// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bit_set::BitSet;
use char_map::{CharMap, CharMultiMap, CharRange};
use error;
use nfa::Nfa;
use program::{InitStates, Inst, Program};
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

trait SplitSet: Sized {
    /// If this set has a non-trivial intersection with the other set, returns the intersetion and
    /// the difference.
    fn split(&self, other: &Self) -> Option<(Self, Self)>;
}

impl SplitSet for BitSet {
    fn split(&self, other: &BitSet) -> Option<(BitSet, BitSet)> {
        if !self.is_disjoint(other) && !self.is_subset(other) {
            Some((self.intersection(other).collect(), self.difference(other).collect()))
        } else {
            None
        }
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
    pub init_at_start: Option<usize>,

    /// This gives the initial state if we start trying to match in the middle of the string:
    /// if the previous char in the string matches one of the ranges, we start at the corresponding
    /// state.
    pub init_after_char: CharMap<usize>,

    /// This is the initial state in all other situations.
    pub init_otherwise: Option<usize>
}

impl Dfa {
    /// Returns a `Dfa` with no states.
    pub fn new() -> Dfa {
        Dfa {
            states: Vec::new(),
            init_at_start: None,
            init_after_char: CharMap::new(),
            init_otherwise: None,
        }
    }

    /// Returns the number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Creates a `Dfa` from a regex string, bailing out if more than `max_states` states were
    /// required.
    pub fn from_regex_bounded(re: &str, max_states: usize) -> Result<Dfa, error::Error> {
        let mut nfa = try!(Nfa::from_regex(re));
        try!(nfa.remove_predicates(max_states));
        let dfa = try!(nfa.determinize(max_states));
        Ok(dfa.minimize())
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

    /// Partitions the given states according to what characters they accept.
    fn reject_partition(&self, states: &BitSet) -> Vec<BitSet> {
        if states.is_empty() {
            // Return the empty partition instead of a partition consisting of the empty set.
            return Vec::new();
        }

        // Gets the set of chars rejected from a given state.
        let rejects = |idx: usize| -> CharMap<usize> {
            self.states[idx].transitions.to_char_set().negated().to_char_map(idx)
        };

        // If state `i` rejects char `c` then this will map `c` to `i`.
        let all_rejects = CharMultiMap::from_vec(
            states.iter()
                .flat_map(|idx| rejects(idx).into_iter())
                .collect()
        );

        // This is the collection of sets whose refinement forms the partition we're looking for.
        let sets = all_rejects.group().into_iter().map(|x| x.1);

        // Now build the refinement.
        let mut ret = vec![states.clone()];
        for s in sets {
            let mut next_ret = Vec::new();
            for part in ret {
                if let Some((p1, p2)) = part.split(&s) {
                    next_ret.push(p1);
                    next_ret.push(p2);
                } else {
                    next_ret.push(part);
                }
            }
            ret = next_ret;
        }

        ret
    }

    /// Returns an equivalent DFA with a minimal number of states.
    ///
    /// Uses Hopcroft's algorithm.
    fn minimize(&self) -> Dfa {
        let (never_states, acc_state_partition) = self.accept_partition();
        let reject_partition = self.reject_partition(&never_states);
        let mut partition = Vec::<BitSet>::new();
        let mut distinguishers = HashSet::<BitSet>::new();
        let reversed = self.reversed();

        // This is a little conservative -- we don't actually have to add everything to the set of
        // distinguishers.  But it won't affect the running time much, since the extra
        // distinguishers will just cause a few more no-op loops.
        for state_set in acc_state_partition.into_iter().chain(reject_partition.into_iter()) {
            partition.push(state_set.clone());
            distinguishers.insert(state_set);
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
                let mut next_partition = Vec::<BitSet>::new();

                for y in partition.iter() {
                    if let Some((y0, y1)) = y.split(s) {
                        if distinguishers.contains(y) {
                            distinguishers.remove(y);
                            distinguishers.insert(y0.clone());
                            distinguishers.insert(y1.clone());
                        } else if y0.len() < y1.len() {
                            distinguishers.insert(y0.clone());
                        } else {
                            distinguishers.insert(y1.clone());
                        }

                        next_partition.push(y0);
                        next_partition.push(y1);
                    } else {
                        next_partition.push(y.clone());
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
            // This unwrap is safe because we don't allow any empty sets into the partition.
            let rep_idx = part.iter().next().unwrap();
            let rep = &self.states[rep_idx];
            ret.states.push(DfaState::new(rep.accept.clone()));

            for state in part.iter() {
                old_state_to_new[state] = ret.states.len() - 1;
            }
        }

        // Fix the indices in all transitions to refer to the new state numbering.
        for part in partition.iter() {
            // This unwrap is safe because we don't allow any empty sets into the partition.
            let old_src_idx = part.iter().next().unwrap();
            let new_src_idx = old_state_to_new[old_src_idx];

            for &(ref range, old_tgt_idx) in self.states[old_src_idx].transitions.iter() {
                let new_tgt_idx = old_state_to_new[old_tgt_idx];
                ret.add_transition(new_src_idx, new_tgt_idx, *range);
            }
        }

        // Fix the initial states to refer to the new numbering.
        if let Some(s) = self.init_at_start {
            ret.init_at_start = Some(old_state_to_new[s])
        }
        if let Some(s) = self.init_otherwise {
            ret.init_otherwise = Some(old_state_to_new[s])
        }
        for &(ref range, state) in self.init_after_char.iter() {
            ret.init_after_char.push(range.clone(), &old_state_to_new[state]);
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
        let nevers = partition.get(&Accept::never())
                              .map(|x| x.clone())
                              .unwrap_or_else(|| BitSet::new());
        let others = partition.into_iter()
                              .filter(|&(key, _)| !key.is_never())
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
        // TODO: put this logic in InitStates
        let mut init = InitStates {
            init_after_char: self.init_after_char.clone(),
            init_at_start: self.init_at_start.map(&map_state),
            init_otherwise: self.init_otherwise.map(&map_state),
        };
        init.init_after_char.map_values(&map_state);
        Program {
            init: init,
            insts: insts,
        }
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

    /// Returns true if this state can be merged into its only target.
    ///
    /// For this to be true, first this state must have only one target state (and that target
    /// cannot be this state itself). Moreover, the target cannot be a starting state, and it must
    /// have only one source state.
    fn is_chain_link(&self, st_idx: usize, reversed: &Nfa) -> bool {
        if let Some(tgt) = Dfa::single_target(self.states[st_idx].transitions.iter()) {
            tgt != st_idx
                && !self.is_starting(tgt)
                && Dfa::single_target(reversed.transitions_from(tgt).iter()).is_some()
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
        self.init_at_start == Some(st_idx)
            || self.init_otherwise == Some(st_idx)
            || (&self.init_after_char).into_iter().any(|x| x.1 == st_idx)
    }

    fn build_chain(&self, mut st_idx: usize, rev: &Nfa) -> Vec<Inst> {
        let mut ret = Vec::new();
        while self.is_chain_link(st_idx, rev) {
            let st = &self.states[st_idx];
            let single_char = Dfa::single_char(st.transitions.iter());

            if !st.accept.is_never() {
                ret.push(Inst::Acc(st.accept.clone()));
            }
            if let Some(ch) = single_char {
                ret.push(Inst::Char(std::char::from_u32(ch).unwrap()));
            } else {
                ret.push(Inst::CharSet(st.transitions.to_char_set()));
            }

            // This unwrap is OK because self.is_chain_link(st_idx, rev).
            st_idx = Dfa::single_target(self.states[st_idx].transitions.iter()).unwrap();
        }

        let st = &self.states[st_idx];
        if !st.accept.is_never() {
            ret.push(Inst::Acc(st.accept.clone()));
        }

        // Even if there are no transitions, add an empty branch (which is basically just an
        // unconditional reject) if this is the last instruction in the chain.
        ret.push(Inst::Branch(st.transitions.clone()));
        ret
    }
}

impl Debug for Dfa {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        try!(f.write_fmt(format_args!("Dfa ({} states):\n", self.states.len())));

        try!(f.write_fmt(format_args!("Initial_at_start: {:?}\n", self.init_at_start)));
        try!(f.write_fmt(format_args!("Initial_after_char: {:?}\n", self.init_after_char)));
        try!(f.write_fmt(format_args!("Initial_otherwise: {:?}\n", self.init_otherwise)));

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

#[cfg(test)]
mod tests {
    use dfa::*;
    use nfa::Nfa;
    use program::Program;
    use std::usize;

    // Like Dfa::from_regex, but doesn't minimize.
    fn make_dfa(re: &str) -> Dfa {
        let mut nfa = Nfa::from_regex(re).unwrap();
        nfa.remove_predicates(usize::MAX);
        nfa.determinize(usize::MAX).unwrap()
    }

    #[test]
    fn test_minimize() {
        let auto = make_dfa("a*b*").minimize();
        assert_eq!(auto.states.len(), 2);

        let auto = make_dfa(r"^a").minimize();
        assert_eq!(auto.states.len(), 2);

        let mut auto = make_dfa("[cgt]gggtaaa|tttaccc[acg]");
        // Since `minimize` is non-deterministic (involving random hashes), run this a bunch of
        // times.
        for _ in 0..100 {
            auto = auto.minimize();
            assert_eq!(auto.states.len(), 16);
        }
    }

   #[test]
    fn test_class_normalized() {
        let re = make_dfa("[abcdw]");
        assert_eq!(re.states.len(), 2);
        // The order of the states is arbitrary, but one should have two transitions and
        // the other should have zero.
        assert_eq!(re.states[0].transitions.len() + re.states[1].transitions.len(), 2);
    }

    #[test]
    fn test_max_states() {
        assert!(Program::from_regex_bounded("foo", 3).is_err());
        assert!(Program::from_regex_bounded("foo", 4).is_ok());
    }

    #[test]
    fn test_adjacent_predicates() {
        assert!(Dfa::from_regex_bounded(r"\btest\b\B", 100).unwrap().states.is_empty());
        assert!(Dfa::from_regex_bounded(r"\btest\B\b", 100).unwrap().states.is_empty());
        assert!(Dfa::from_regex_bounded(r"test1\b\Btest2", 100).unwrap().states.is_empty());
    }

    #[test]
    fn test_syntax_error() {
        assert!(Dfa::from_regex_bounded("(abc", 10).is_err());
    }

    #[test]
    fn test_bug() {
        use regex::Regex;
        let re = Regex::new(r"\xff").unwrap();
        assert_eq!(re.shortest_match("\u{ff}"), Some((0, 2)));
    }
}

