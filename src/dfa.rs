// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bit_set::BitSet;
use char_map::{CharMap, CharSet, CharRange};
use error;
use memchr::memchr;
use nfa::Nfa;
use std;
use std::collections::{HashSet, HashMap};
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::result::Result;
use transition::Accept;

trait PopArbitrary<T> {
    /// Removes and returns an arbitrary member of this collection.
    ///
    /// If the collection is empty, this panics.
    fn pop_arbitrary(&mut self) -> T;
}

impl<T: Eq + Clone + Hash> PopArbitrary<T> for HashSet<T> {
    fn pop_arbitrary(&mut self) -> T {
        let elt = self.iter().next().unwrap().clone();
        self.remove(&elt);
        elt
    }
}

#[derive(PartialEq, Debug)]
pub struct DfaState {
    pub transitions: CharMap<usize>,
    pub accept: Accept,
}

impl DfaState {
    pub fn new(accept: Accept) -> DfaState {
        DfaState {
            transitions: CharMap::new(),
            accept: accept.clone(),
        }
    }
}

/// Our `Dfa`s are unanchored, in the sense that by default they can match something in the middle
/// of the input string. However, we allow the initial state of the `Dfa` to depend on where we
/// start matching.
#[derive(PartialEq)]
pub struct Dfa {
    states: Vec<DfaState>,

    /// This is the initial state if we start trying to match at the beginning of the string.
    pub initial_at_start: Option<usize>,

    /// This gives the initial state if we start trying to match in the middle of the string:
    /// if the previous char in the string matches one of the ranges, we start at the corresponding
    /// state.
    pub initial_after_char: CharMap<usize>,

    /// This is the initial state in all other situations.
    pub initial_otherwise: Option<usize>
}

impl Dfa {
    /// Returns a `Dfa` with no states.
    pub fn new() -> Dfa {
        Dfa {
            states: Vec::new(),
            initial_at_start: None,
            initial_after_char: CharMap::new(),
            initial_otherwise: None,
        }
    }

    /// Returns the number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    pub fn from_regex(re: &str) -> Result<Dfa, error::Error> {
        let mut nfa = try!(Nfa::from_regex(re));
        nfa.remove_predicates();
        Ok(nfa.determinize().minimize())
    }

    pub fn add_state(&mut self, accept: Accept) {
        self.states.push(DfaState::new(accept));
    }

    pub fn add_transition(&mut self, from: usize, to: usize, range: CharRange) {
        self.states[from].transitions.push(range, &to);
    }

    pub fn sort_transitions(&mut self) {
        for st in &mut self.states {
            st.transitions.sort();
        }
    }

    /* TODO
    /// If the beginning of this DFA matches a literal string, return it.
    pub fn prefix(&self) -> String {
        let mut ret = String::new();
        let mut state = self.initial;

        let accepts_one_char = |st| {
            self.states[st].transitions.len() == 1
                && self.states[st].transitions.
        };

        loop {

        }
    }
    */

    /// Tests if the given state is accepting, assuming that `next` is the next char.
    fn accepting(&self, state: usize, next: Option<char>) -> bool {
        use transition::Accept::*;
        match self.states[state].accept {
            Never => false,
            Always => true,
            Conditionally { at_eoi, ref at_char } => {
                match next {
                    None => at_eoi,
                    Some(c) => at_char.contains(c as u32),
                }
            }
        }
    }

    /// If we match some prefix of the string, returns the index after the endpoint of the longest
    /// match.
    fn longest_match_after<Iter>(&self, iter: Iter, last: Option<(usize, char)>) -> Option<usize>
    where Iter: Iterator<Item=(usize, char)> + Clone {
        match last {
            None => {
                if let Some(s) = self.initial_at_start {
                    self.longest_match_from(iter, s, 0)
                } else {
                    None
                }
            }
            Some((idx, ch)) => {
                if let Some(&s) = self.initial_after_char.get(ch as u32) {
                    self.longest_match_from(iter, s, idx + ch.len_utf8())
                } else if let Some(s) = self.initial_otherwise {
                    self.longest_match_from(iter, s, idx + ch.len_utf8())
                } else {
                    None
                }
            }
        }
    }

    /// Beginning at the given initial state, if we match some prefix of the string, returns the
    /// index after the endpoint of the longest match.
    ///
    /// `idx` is the value we should return if the initial state is accepting.
    fn longest_match_from<Iter>(&self, iter: Iter, mut state: usize, idx: usize) -> Option<usize>
    where Iter: Iterator<Item=(usize, char)> {
        let mut iter = iter.peekable();
        let mut last_match = if self.accepting(state, iter.peek().map(|&(_, x)| x)) {
            Some(idx)
        } else {
            None
        };

        loop {
            let cur_state = &self.states[state];
            match iter.next() {
                None => return last_match,
                Some((idx, ch)) => {
                    match cur_state.transitions.get(ch as u32) {
                        Some(&next_state) => {
                            state = next_state;
                            let next_ch = iter.peek().map(|&(_, x)| x);
                            if self.accepting(state, next_ch) {
                                last_match = Some(idx + ch.len_utf8());
                            }
                        },
                        None => return last_match,
                    }
                }
            }
        }
    }

    /// Returns the index range of the first longest match, if there is a match. The indices
    /// returned are byte indices of the string. The first index is inclusive; the second is
    /// exclusive, and a little more subtle -- see the crate documentation.
    pub fn longest_match(&self, s: &str) -> Option<(usize, usize)> {
        let mut iter = s.char_indices();

        match self.longest_match_after(iter.clone(), None) {
            None => (),
            Some(n) => return Some((0, n)),
        }
        loop {
            match iter.next() {
                None => return None,
                Some((m, ch)) => {
                    let next_idx = m + ch.len_utf8();
                    match self.longest_match_after(iter.clone(), Some((next_idx, ch))) {
                        None => (),
                        Some(n) => return Some((next_idx, n)),
                    }
                }
            }
        }
    }

    fn shortest_match_from<Iter>(&self, iter: Iter, mut state: usize, idx: usize) -> Option<usize>
    where Iter: Iterator<Item=(usize, char)> {
        let mut iter = iter.peekable();
        let mut cur_idx = idx;
        loop {
            if self.accepting(state, iter.peek().map(|x| x.1)) {
                return Some(cur_idx);
            }
            if let Some((idx, ch)) = iter.next() {
                if let Some(&next_state) = self.states[state].transitions.get(ch as u32) {
                    state = next_state;
                    cur_idx = idx + ch.len_utf8();
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
    }

    /// Checks whether we match the string `s`.
    pub fn is_match(&self, s: &str) -> bool {
        self.shortest_match(s).is_some()
    }

    /// Returns the index range of the first shortest match, if there is a match. The indices
    /// returned are byte indices of the string. The first index is inclusive; the second is
    /// exclusive, and a little more subtle -- see the crate documentation.
    pub fn shortest_match(&self, s: &str) -> Option<(usize, usize)> {
        if let Some(state) = self.initial_at_start {
            if let Some(end) = self.shortest_match_from(s.char_indices(), state, 0) {
                return Some((0, end));
            }
        }
        if self.initial_otherwise.is_none() && self.initial_after_char.is_empty() {
            return None;
        }

        let mut iter = s.char_indices();
        while let Some((idx, ch)) = iter.next() {
            let next_idx = idx + ch.len_utf8();
            if let Some(state) = self.state_after(ch as u32) {
                if let Some(end) = self.shortest_match_from(iter.clone(), state, next_idx) {
                    return Some((next_idx, end));
                }
            }
        }
        return None;
    }

    fn state_after(&self, ch: u32) -> Option<usize> {
        if let Some(&state) = self.initial_after_char.get(ch as u32) {
            Some(state)
        } else if let Some(state) = self.initial_otherwise {
            Some(state)
        } else {
            None
        }
    }

    /// Returns an equivalent DFA with a minimal number of states.
    ///
    /// Uses Hopcroft's algorithm.
    fn minimize(&self) -> Dfa {
        let (never_states, acc_state_partition) = self.accept_partition();
        let mut partition = HashSet::<BitSet>::new();
        let mut distinguishers = HashSet::<BitSet>::new();
        let reversed = self.reversed();

        for state_set in acc_state_partition {
            partition.insert(state_set.clone());
            distinguishers.insert(state_set);
        }
        if !never_states.is_empty() {
            partition.insert(never_states);
        }

        while distinguishers.len() > 0 {
            let dist = distinguishers.pop_arbitrary();
            let sets: Vec<BitSet> = reversed.transitions(&dist)
                                            .into_iter()
                                            .map(|(_, x)| x)
                                            .collect();

            // For each set in our partition so far, split it if
            // some element of `sets` reveals it to contain more than
            // one equivalence class.
            for s in &sets {
                let mut next_partition = HashSet::<BitSet>::new();

                for y in partition.iter() {
                    let y0: BitSet = y.intersection(s).collect();
                    let y1: BitSet = y.difference(s).collect();

                    if y0.is_empty() || y1.is_empty() {
                        next_partition.insert(y.clone());
                    } else {
                        if distinguishers.contains(y) {
                            distinguishers.remove(y);
                            distinguishers.insert(y0.clone());
                            distinguishers.insert(y1.clone());
                        } else if y0.len() < y1.len() {
                            distinguishers.insert(y0.clone());
                        } else {
                            distinguishers.insert(y1.clone());
                        }

                        next_partition.insert(y0);
                        next_partition.insert(y1);
                    }
                }

                partition = next_partition;
            }
        }

        let mut ret = Dfa::new();

        // We need to re-index the states: build a map that maps old indices to
        // new indices.
        let mut old_state_to_new = vec![0; self.states.len()];
        for part in partition.iter() {
            let rep_idx = part.iter().next().unwrap();
            let rep = &self.states[rep_idx];
            ret.states.push(DfaState::new(rep.accept.clone()));

            for state in part.iter() {
                old_state_to_new[state] = ret.states.len() - 1;
            }
        }

        // Fix the indices in all transitions to refer to the new state numbering.
        for part in partition.iter() {
            let old_src_idx = part.iter().next().unwrap();
            let new_src_idx = old_state_to_new[old_src_idx];

            for &(ref range, old_tgt_idx) in self.states[old_src_idx].transitions.iter() {
                let new_tgt_idx = old_state_to_new[old_tgt_idx];
                ret.add_transition(new_src_idx, new_tgt_idx, *range);
            }
        }

        // Fix the initial states to refer to the new numbering.
        if let Some(s) = self.initial_at_start {
            ret.initial_at_start = Some(old_state_to_new[s])
        }
        if let Some(s) = self.initial_otherwise {
            ret.initial_otherwise = Some(old_state_to_new[s])
        }
        for &(ref range, state) in self.initial_after_char.iter() {
            ret.initial_after_char.push(range.clone(), &old_state_to_new[state]);
        }

        ret.normalize_transitions();
        ret
    }

    fn normalize_transitions(&mut self) {
        for st in &mut self.states {
            st.transitions.normalize();
        }
    }

    /// Returns a partition of states according to their accept value. The first tuple element is
    /// the set of states that never accept; the other element is a partition of the remaining
    /// states.
    fn accept_partition(&self) -> (BitSet, Vec<BitSet>) {
        let mut partition = HashMap::<&Accept, BitSet>::new();
        for (idx, st) in self.states.iter().enumerate() {
            partition.entry(&st.accept).or_insert(BitSet::new()).insert(idx);
        }
        let nevers = partition.get(&Accept::Never)
                              .map(|x| x.clone())
                              .unwrap_or_else(|| BitSet::new());
        let others = partition.into_iter()
                              .filter(|&(key, _)| key != &Accept::Never)
                              .map(|(_, val)| val)
                              .collect();
        (nevers, others)
    }

    /// Returns the automaton with all its transitions reversed.  Its states will have the same
    /// indices as those of the original automaton.
    ///
    /// Warning: this does not preserve any ending predicates; it's only for reversing the
    /// input-consuming transitions.
    fn reversed(&self) -> Nfa {
        let mut ret = Nfa::with_capacity(self.states.len());

        for st in self.states.iter() {
            ret.add_state(st.accept.clone());
        }

        for (idx, st) in self.states.iter().enumerate() {
            for &(ref range, target) in st.transitions.iter() {
                ret.add_transition(target, idx, *range);
            }
        }

        ret
    }

    fn first_byte(&self) -> Option<u8> {
        if let Some(state) = self.initial_at_start {
            if self.initial_otherwise == Some(state) && self.initial_after_char.is_empty() {
                if let Some(ch) = Dfa::single_char(self.states[state].transitions.iter()) {
                    if let Some(c) = std::char::from_u32(ch) {
                        if c.len_utf8() == 1 {
                            return Some(ch as u8);
                        }
                    }
                }
            }
        }
        None
    }

    pub fn to_program(&self) -> Program {
        let (mut chains, state_map, lengths) = self.chains();
        let map_state = |s| lengths[*state_map.get(&s).unwrap()];

        // Fix up the indices to refer to the new instructions. Note that only the last instruction
        // in each chain can be a Branch, so we only need to look at those.
        for ch in &mut chains {
            if let Some(inst) = ch.last_mut() {
                if let &mut Inst::Branch(ref mut cm) = inst {
                    cm.map_values(&map_state);
                }
            }
        }

        let insts = chains.into_iter().flat_map(|c| c.into_iter()).collect::<Vec<_>>();
        let mut ret = Program::new();
        ret.insts = insts;
        ret.initial_after_char = self.initial_after_char.clone();
        ret.initial_after_char.map_values(&map_state);
        ret.initial_at_start = self.initial_at_start.map(&map_state);
        ret.initial_otherwise = self.initial_otherwise.map(&map_state);
        ret.first_byte = self.first_byte();
        ret
    }

    /// Looks for transitions that only have one possible target state and groups them.
    /// The second return value is a map from the old state index to the element in the first
    /// return value that represents the same state. The third return value is the accumulated
    /// lengths of the chains.
    fn chains(&self) -> (Vec<Vec<Inst>>, HashMap<usize, usize>, Vec<usize>) {
        let mut chains = Vec::<Vec<Inst>>::new();
        let mut map = HashMap::<usize, usize>::new();
        let mut lengths = Vec::new();
        let mut cur_length = 0;
        let rev = self.reversed();

        for st_idx in 0..self.states.len() {
            if self.is_chain_head(st_idx, &rev) {
                let new_chain = self.build_chain(st_idx, &rev);
                map.insert(st_idx, chains.len());
                lengths.push(cur_length);
                cur_length += new_chain.len();
                chains.push(new_chain);
            }
        }

        (chains, map, lengths)
    }

    fn single_target<'a, Iter>(mut iter: Iter) -> Option<usize>
    where Iter: Iterator<Item = &'a (CharRange, usize)> {
        if let Some(&(_, target)) = iter.next() {
            while let Some(&(_, next_target)) = iter.next() {
                if target != next_target {
                    return None;
                }
            }
            Some(target)
        } else {
            None
        }
    }

    fn single_char<'a, Iter>(mut iter: Iter) -> Option<u32>
    where Iter: Iterator<Item = &'a (CharRange, usize)> {
        if let Some(&(range, _)) = iter.next() {
            if range.start == range.end && iter.next().is_none() {
                Some(range.start)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Returns true if this state has only one target state, and that target state's only source
    /// state is this state.
    fn is_chain_link(&self, st_idx: usize, reversed: &Nfa) -> bool {
        if let Some(tgt) = Dfa::single_target(self.states[st_idx].transitions.iter()) {
            Dfa::single_target(reversed.transitions_from(tgt).iter()).is_some()
        } else {
            false
        }
    }

    fn is_chain_head(&self, st_idx: usize, rev: &Nfa) -> bool {
        // We're at the head of a chain if either we don't have a parent that is a chain link, or
        // if we are a starting state.
        let has_p = if let Some(p) = Dfa::single_target(rev.transitions_from(st_idx).iter()) {
            self.is_chain_link(p, rev)
        } else {
            false
        };
        self.is_starting(st_idx) || !has_p
    }

    fn is_starting(&self, st_idx: usize) -> bool {
        self.initial_at_start == Some(st_idx)
            || self.initial_otherwise == Some(st_idx)
            || (&self.initial_after_char).into_iter().any(|x| x.1 == st_idx)
    }

    fn build_chain(&self, mut st_idx: usize, rev: &Nfa) -> Vec<Inst> {
        let mut ret = Vec::new();
        let mut lit_in_progress = String::new();
        while self.is_chain_link(st_idx, rev) {
            let st = &self.states[st_idx];
            if st.accept != Accept::Never {
                ret.push(Inst::Acc(st.accept.clone()));
            }
            if let Some(ch) = Dfa::single_char(st.transitions.iter()) {
                lit_in_progress.push(std::char::from_u32(ch).unwrap());
            } else {
                if !lit_in_progress.is_empty() {
                    ret.push(Inst::Literal(lit_in_progress));
                    lit_in_progress = String::new();
                }
                ret.push(Inst::Char(st.transitions.to_char_set()));
            }

            // This unwrap is OK because self.is_chain_link(st_idx, rev).
            st_idx = Dfa::single_target(self.states[st_idx].transitions.iter()).unwrap();
        }

        if !lit_in_progress.is_empty() {
            ret.push(Inst::Literal(lit_in_progress));
        }

        let st = &self.states[st_idx];
        if st.accept != Accept::Never {
            ret.push(Inst::Acc(st.accept.clone()));
        }
        if !st.transitions.is_empty() {
            ret.push(Inst::Branch(st.transitions.clone()));
        } else if ret.last() != Some(&Inst::Acc(Accept::Always)) {
            ret.push(Inst::Reject);
        }

        ret
    }
}

impl Debug for Dfa {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        try!(f.write_fmt(format_args!("Dfa ({} states):\n", self.states.len())));

        try!(f.write_fmt(format_args!("Initial_at_start: {:?}\n", self.initial_at_start)));
        try!(f.write_fmt(format_args!("Initial_after_char: {:?}\n", self.initial_after_char)));
        try!(f.write_fmt(format_args!("Initial_otherwise: {:?}\n", self.initial_otherwise)));

        for (st_idx, st) in self.states.iter().enumerate() {
            try!(f.write_fmt(format_args!("\tState {} (accepting: {:?}):\n", st_idx, st.accept)));

            if !st.transitions.is_empty() {
                try!(f.write_str("\t\tTransitions:\n"));
                for &(range, target) in st.transitions.iter() {
                    try!(f.write_fmt(format_args!("\t\t\t{} -- {} => {}\n",
                                                  range.start, range.end, target)));
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Inst {
    Literal(String),
    Char(CharSet),
    Acc(Accept),
    Branch(CharMap<usize>),
    Reject,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    insts: Vec<Inst>,
    initial_at_start: Option<usize>,
    initial_after_char: CharMap<usize>,
    initial_otherwise: Option<usize>,

    /// If this is `Some` then initial_after_char must be empty and initial_at_start must
    /// be the same as initial_otherwise.
    first_byte: Option<u8>,
}

impl Program {
    pub fn new() -> Program {
        Program {
            insts: Vec::new(),
            initial_at_start: None,
            initial_after_char: CharMap::new(),
            initial_otherwise: None,
            first_byte: None,
        }
    }

    fn shortest_match_from(&self, mut s: &str, mut state: usize, idx: usize) -> Option<usize> {
        use dfa::Inst::*;

        let mut cur_idx = idx;
        loop {
            match self.insts[state] {
                Reject => { return None; },
                Acc(Accept::Always) => { return Some(cur_idx); }
                Acc(Accept::Never) => {},
                Acc(Accept::Conditionally { at_eoi, ref at_char }) => {
                    if at_eoi && s.is_empty() {
                        return Some(cur_idx);
                    } else if let Some(next_ch) = s.chars().next() {
                        if at_char.contains(next_ch as u32) {
                            return Some(cur_idx);
                        }
                    }
                    state += 1;
                },
                Char(ref cs) => {
                    if let Some((next_ch, rest)) = s.slice_shift_char() {
                        if cs.contains(next_ch as u32) {
                            state += 1;
                            cur_idx += next_ch.len_utf8();
                            s = rest;
                            continue;
                        }
                    }
                    return None;
                },
                Literal(ref lit) => {
                    if s.starts_with(lit) {
                        state += 1;
                        cur_idx += lit.len();
                        s = &s[lit.len()..];
                    } else {
                        return None;
                    }
                },
                Branch(ref cm) => {
                    if let Some((next_ch, rest)) = s.slice_shift_char() {
                        if let Some(&next_state) = cm.get(next_ch as u32) {
                            state = next_state;
                            cur_idx += next_ch.len_utf8();
                            s = rest;
                            continue;
                        }
                    }
                    return None;
                },
            }
        }
    }

    // A fast path, using memchr to find the candidates for matching.
    fn shortest_match_memchr(&self, mut s: &str, first_ch: u8, state: usize)
    -> Option<(usize, usize)> {
        while let Some(pos) = memchr(first_ch, s.as_bytes()) {
            s = &s[pos..];
            if let Some(end) = self.shortest_match_from(s, state, pos) {
                return Some((pos, end));
            }
            if let Some((_, rest)) = s.slice_shift_char() {
                s = rest;
            }
        }
        return None;
    }

    pub fn shortest_match(&self, mut s: &str) -> Option<(usize, usize)> {
        if let Some(first) = self.first_byte {
            return self.shortest_match_memchr(s, first, self.initial_otherwise.unwrap());
        }

        if let Some(state) = self.initial_at_start {
            if let Some(end) = self.shortest_match_from(s, state, 0) {
                return Some((0, end));
            }
        }

        // Skip looping through the string if we know that the match has to start
        // at the beginning.
        if self.initial_otherwise.is_none() && self.initial_after_char.is_empty() {
            return None;
        }

        let mut idx = 0;
        while let Some((ch, rest)) = s.slice_shift_char() {
            s = rest;
            idx += ch.len_utf8();

            if let Some(&state) = self.initial_after_char.get(ch as u32) {
                if let Some(end) = self.shortest_match_from(s, state, idx) {
                    return Some((idx, end));
                }
            } else if let Some(state) = self.initial_otherwise {
                if let Some(end) = self.shortest_match_from(s, state, idx) {
                    return Some((idx, end));
                }
            }
        }

        None
    }

    pub fn is_match(&self, s: &str) -> bool {
        self.shortest_match(s).is_some()
    }
}

#[cfg(test)]
mod tests {
    use builder;
    use char_map::{CharMap, CharRange, CharSet};
    use dfa::Dfa;
    use nfa::Nfa;
    use regex_syntax;
    use std::iter;
    use transition::Accept;

    fn make_dfa(re: &str) -> Dfa {
        let expr = regex_syntax::Expr::parse(re).unwrap();
        let mut nfa = builder::NfaBuilder::from_expr(&expr).to_automaton();
        nfa.remove_predicates();
        nfa.determinize()
    }

    // Returns an automaton that accepts strings with an even number of 'b's.
    fn even_bs_dfa() -> Dfa {
        let mut ret = Dfa::new();

        ret.initial_at_start = Some(0);
        ret.add_state(Accept::Always);
        ret.add_state(Accept::Never);
        ret.add_transition(0, 0, CharRange::single('a' as u32));
        ret.add_transition(0, 1, CharRange::single('b' as u32));
        ret.add_transition(1, 1, CharRange::single('a' as u32));
        ret.add_transition(1, 0, CharRange::single('b' as u32));
        ret
    }

    fn odd_bs_dfa() -> Dfa {
        let mut ret = even_bs_dfa();
        ret.initial_at_start = Some(1);
        ret
    }

    #[test]
    fn test_reverse() {
        let dfa = even_bs_dfa();

        let mut rev = Nfa::new();
        rev.add_state(Accept::Always);
        rev.add_state(Accept::Never);
        rev.add_transition(0, 0, CharRange::single('a' as u32));
        rev.add_transition(0, 1, CharRange::single('b' as u32));
        rev.add_transition(1, 0, CharRange::single('b' as u32));
        rev.add_transition(1, 1, CharRange::single('a' as u32));

        assert_eq!(rev, dfa.reversed());
    }

    #[test]
    fn test_accept_at_end() {
        // Make a DFA that accepts strings with an even number of b's, or strings
        // whose last character is a b.
        let mut dfa = Dfa::new();
        dfa.initial_at_start = Some(0);
        dfa.add_state(Accept::Always);
        dfa.add_state(Accept::Never);
        dfa.add_state(Accept::Conditionally { at_eoi: true, at_char: CharSet::new() });
        dfa.add_transition(0, 0, CharRange::single('a' as u32));
        dfa.add_transition(0, 2, CharRange::single('b' as u32));
        dfa.add_transition(1, 1, CharRange::single('a' as u32));
        dfa.add_transition(1, 0, CharRange::single('b' as u32));
        dfa.add_transition(2, 1, CharRange::single('a' as u32));
        dfa.add_transition(2, 0, CharRange::single('b' as u32));

        assert_eq!(dfa.longest_match("aaaaaa"), Some((0, 6)));
        assert_eq!(dfa.longest_match("aaaaaba"), Some((0, 5)));
        assert_eq!(dfa.longest_match("aaaaaab"), Some((0, 7)));
        assert_eq!(dfa.longest_match("baabaaaa"), Some((0, 8)));
        assert_eq!(dfa.longest_match("baabaaaab"), Some((0, 9)));
        assert_eq!(dfa.longest_match("bbbba"), Some((0, 5)));
    }

    #[test]
    fn test_accept_after_char() {
        // Make a DFA that accepts strings with an even number of b's, or whose next character
        // is a c.
        let mut dfa = even_bs_dfa();
        dfa.states[1].accept = Accept::Conditionally { at_eoi: false,
                                                       at_char: CharSet::single('c' as u32) };
        assert_eq!(dfa.longest_match("aaaaaa"), Some((0, 6)));
        assert_eq!(dfa.longest_match("aaaaaba"), Some((0, 5)));
        assert_eq!(dfa.longest_match("aaaaaab"), Some((0, 6)));
        assert_eq!(dfa.longest_match("baaaaaa"), Some((0, 0)));
        assert_eq!(dfa.longest_match("baaaaca"), Some((0, 5)));
        assert_eq!(dfa.longest_match("c"), Some((0, 0)));
        assert_eq!(dfa.longest_match("cbb"), Some((0, 0)));
    }

    #[test]
    fn test_unanchored_start() {
        let mut dfa = odd_bs_dfa();
        dfa.initial_at_start = None;
        dfa.initial_otherwise = Some(1);

        assert_eq!(dfa.longest_match("cacbc"), Some((3, 4)));
        assert_eq!(dfa.longest_match("cacababc"), Some((3, 6)));
        assert_eq!(dfa.longest_match("ab"), Some((1, 2)));
        assert_eq!(dfa.longest_match("cacaaca"), None);
    }

    #[test]
    fn test_start_after() {
        let mut dfa = odd_bs_dfa();
        dfa.initial_at_start = None;
        dfa.initial_after_char = CharMap::from_vec(vec![(CharRange::single('c' as u32), 1)]);

        assert_eq!(dfa.longest_match("baabbababaa"), None);
        assert_eq!(dfa.longest_match("baabbacbabaa"), Some((7, 9)));
        assert_eq!(dfa.longest_match("cbaabbababaa"), Some((1, 12)));
    }

    #[test]
    fn test_minimize() {
        let auto1 = make_dfa("a*b*");
        let auto2 = auto1.minimize();

        let test_strings = vec!["aaabbbbbbb", "bbbb", "a", "", "ba", "aba"];
        for s in test_strings {
            assert_eq!(auto1.longest_match(s), auto2.longest_match(s));
        }
        assert_eq!(auto2.states.len(), 2);

        let auto1 = make_dfa(r"^a").minimize();
        assert_eq!(auto1.states.len(), 2);
    }

    #[test]
    fn test_longest_match() {
        let auto = make_dfa("a+b*");
        assert_eq!(auto.longest_match("cdacd"), Some((2, 3)));
        assert_eq!(auto.longest_match("cdaabbcd"), Some((2, 6)));
        assert_eq!(auto.longest_match("aabbcd"), Some((0, 4)));
        assert_eq!(auto.longest_match("cdb"), None);
        assert_eq!(auto.longest_match("ab"), Some((0, 2)));

        // If the pattern matches the empty string, it will always be found
        // at the beginning.
        let auto = make_dfa("a*b*");

        assert_eq!(auto.longest_match("cdacd"), Some((0, 0)));
        assert_eq!(auto.longest_match("cdaabbcd"), Some((0, 0)));
        assert_eq!(auto.longest_match("aabbcd"), Some((0, 4)));
        assert_eq!(auto.longest_match("cdb"), Some((0, 0)));
        assert_eq!(auto.longest_match("ab"), Some((0, 2)));
    }

    #[test]
    fn test_make_anchored() {
        let dfa = make_dfa("^a").minimize();

        assert_eq!(dfa.longest_match("abc"), Some((0, 1)));
        assert_eq!(dfa.longest_match("bac"), None);
        assert_eq!(dfa.states.len(), 2);

        let dfa = make_dfa("^a$").minimize();
        assert_eq!(dfa.longest_match("abc"), None);
        assert_eq!(dfa.longest_match("bca"), None);
        assert_eq!(dfa.longest_match("a"), Some((0, 1)));
        assert_eq!(dfa.states.len(), 2);
    }

    #[test]
    fn test_not_literal() {
        let re = make_dfa(".y").minimize();
        let text = format!("{}y", iter::repeat("x").take(50).collect::<String>());
        assert!(re.is_match(&text));
    }

    #[test]
    fn test_anchored_literal_short_match() {
        let re = Dfa::from_regex("^.bc(d|e)").unwrap();
        let text = "abcdefghijklmnopqrstuvwxyz";
        assert!(re.is_match(text));
    }

    #[test]
    fn test_anchored_literal_long_match() {
        let re = Dfa::from_regex("^.bc(d|e)").unwrap();
        let text: String = iter::repeat("abcdefghijklmnopqrstuvwxyz").take(15).collect();
        assert!(re.is_match(&text));
    }

    #[test]
    fn test_to_program() {
        let re = Dfa::from_regex("^.bc(d|e)").unwrap();
        let prog = re.to_program();
        let text: String = iter::repeat("abcdefghijklmnopqrstuvwxyz").take(15).collect();
        assert_eq!(prog.shortest_match(&text), Some((0, 4)));
    }

   #[test]
    fn test_class_normalized() {
        let re = Dfa::from_regex("[abcdw]").unwrap();
        assert_eq!(re.states.len(), 2);
        // The order of the states is arbitrary, but one should have two transitions and
        // the other should have zero.
        assert_eq!(re.states[0].transitions.len() + re.states[1].transitions.len(), 2);
    }
}

