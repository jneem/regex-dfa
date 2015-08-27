// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bit_set::BitSet;
use char_map::{CharMap, CharRange, CharSet};
use error;
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
        let nfa = try!(Nfa::from_regex(re));
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

    /// If the beginning of this DFA matches a literal string, return it.
    /* TODO
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
    pub fn accepting(&self, state: usize, next: Option<char>) -> bool {
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
    pub fn longest_match<Iter>(&self, iter: Iter, last_char: Option<char>) -> Option<usize>
    where Iter: Iterator<Item=(usize, char)> + Clone {
        match last_char {
            None => {
                if let Some(s) = self.initial_at_start {
                    self.longest_match_from(iter, s)
                } else {
                    None
                }
            }
            Some(ch) => {
                if let Some(&s) = self.initial_after_char.get(ch as u32) {
                    self.longest_match_from(iter.clone(), s)
                } else if let Some(s) = self.initial_otherwise {
                    self.longest_match_from(iter, s)
                } else {
                    None
                }
            }
        }
    }

    /// Beginning at the given initial state, if we match some prefix of the string, returns the
    /// index after the endpoint of the longest match.
    pub fn longest_match_from<Iter>(&self, iter: Iter, mut state: usize) -> Option<usize>
    where Iter: Iterator<Item=(usize, char)> {
        let mut iter = iter.peekable();
        let mut last_match = if self.accepting(state, iter.peek().map(|&(_, x)| x)) {
            Some(0)
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

    /// Returns the index range of the match, if found.
    // TODO: would prefer to take an iterator, but it seems hard to
    // produce something of type Iterator<Item=(usize, u32)> + Clone.
    pub fn search(&self, s: &str) -> Option<(usize, usize)> {
    // where Iter: Iterator<Item=(usize, u32)> + Clone {
        let mut iter = s.char_indices();

        match self.longest_match(iter.clone(), None) {
            None => (),
            Some(n) => return Some((0, n)),
        }
        loop {
            match iter.next() {
                None => return None,
                Some((m, ch)) => {
                    match self.longest_match(iter.clone(), Some(ch)) {
                        None => (),
                        Some(n) => return Some((m + ch.len_utf8(), n)),
                    }
                }
            }
        }
    }

    /// Returns an equivalent DFA with a minimal number of states.
    ///
    /// Uses Hopcroft's algorithm.
    pub fn minimize(&self) -> Dfa {
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

        ret
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
}

impl Debug for Dfa {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        try!(f.write_fmt(format_args!("Dfa ({} states):\n", self.states.len())));

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
    use builder;
    use char_map::{CharMap, CharRange, CharSet};
    use dfa::Dfa;
    use nfa::Nfa;
    use regex_syntax;
    use transition::Accept;

    fn make_dfa(re: &str) -> Dfa {
        let expr = regex_syntax::Expr::parse(re).unwrap();
        builder::NfaBuilder::from_expr(&expr).to_automaton().determinize()
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

        assert_eq!(dfa.longest_match("aaaaaa".char_indices(), None), Some(6));
        assert_eq!(dfa.longest_match("aaaaaba".char_indices(), None), Some(5));
        assert_eq!(dfa.longest_match("aaaaaab".char_indices(), None), Some(7));
        assert_eq!(dfa.longest_match("baabaaaa".char_indices(), None), Some(8));
        assert_eq!(dfa.longest_match("baabaaaab".char_indices(), None), Some(9));
        assert_eq!(dfa.longest_match("bbbba".char_indices(), None), Some(5));
    }

    #[test]
    fn test_accept_after_char() {
        // Make a DFA that accepts strings with an even number of b's, or whose next character
        // is a c.
        let mut dfa = even_bs_dfa();
        dfa.states[1].accept = Accept::Conditionally { at_eoi: false,
                                                       at_char: CharSet::single('c' as u32) };
        assert_eq!(dfa.longest_match("aaaaaa".char_indices(), None), Some(6));
        assert_eq!(dfa.longest_match("aaaaaba".char_indices(), None), Some(5));
        assert_eq!(dfa.longest_match("aaaaaab".char_indices(), None), Some(6));
        assert_eq!(dfa.longest_match("baaaaaa".char_indices(), None), Some(0));
        assert_eq!(dfa.longest_match("baaaaca".char_indices(), None), Some(5));
        assert_eq!(dfa.longest_match("c".char_indices(), None), Some(0));
        assert_eq!(dfa.longest_match("cbb".char_indices(), None), Some(0));
    }

    #[test]
    fn test_unanchored_start() {
        let mut dfa = odd_bs_dfa();
        dfa.initial_at_start = None;
        dfa.initial_otherwise = Some(1);

        assert_eq!(dfa.search("cacbc"), Some((3, 4)));
        assert_eq!(dfa.search("cacababc"), Some((3, 6)));
        assert_eq!(dfa.search("ab"), Some((1, 2)));
        assert_eq!(dfa.search("cacaaca"), None);
    }

    #[test]
    fn test_start_after() {
        let mut dfa = odd_bs_dfa();
        dfa.initial_at_start = None;
        dfa.initial_after_char = CharMap::from_vec(vec![(CharRange::single('c' as u32), 1)]);

        assert_eq!(dfa.search("baabbababaa"), None);
        assert_eq!(dfa.search("baabbacbabaa"), Some((7, 9)));
        assert_eq!(dfa.search("cbaabbababaa"), Some((1, 12)));
    }

    #[test]
    fn test_minimize() {
        let auto1 = make_dfa("a*b*").minimize();
        let auto2 = auto1.minimize();

        let test_strings = vec!["aaabbbbbbb", "bbbb", "a", "", "ba", "aba"];
        for s in test_strings {
            assert_eq!(auto1.search(s), auto2.search(s));
        }
        assert_eq!(auto2.states.len(), 2);
    }

    #[test]
    fn test_longest_match() {
        let auto = make_dfa("a*b*");

        assert_eq!(auto.longest_match("aba".char_indices(), None), Some(2));
        assert_eq!(auto.longest_match("baba".char_indices(), None), Some(1));
        assert_eq!(auto.longest_match("ac".char_indices(), None), Some(1));
        assert_eq!(auto.longest_match("ab".char_indices(), None), Some(2));
        assert_eq!(auto.longest_match("bc".char_indices(), None), Some(1));
        assert_eq!(auto.longest_match("b".char_indices(), None), Some(1));

        let auto = make_dfa("a+b*");

        assert_eq!(auto.longest_match("aba".char_indices(), None), Some(2));
        assert_eq!(auto.longest_match("baba".char_indices(), None), None);
        assert_eq!(auto.longest_match("ac".char_indices(), None), Some(1));
        assert_eq!(auto.longest_match("ab".char_indices(), None), Some(2));
        assert_eq!(auto.longest_match("bc".char_indices(), None), None);
        assert_eq!(auto.longest_match("b".char_indices(), None), None);
    }

    #[test]
    fn test_search() {
        let auto = make_dfa("a+b*");
        assert_eq!(auto.search("cdacd"), Some((2, 3)));
        assert_eq!(auto.search("cdaabbcd"), Some((2, 6)));
        assert_eq!(auto.search("aabbcd"), Some((0, 4)));
        assert_eq!(auto.search("cdb"), None);
        assert_eq!(auto.search("ab"), Some((0, 2)));

        // If the pattern matches the empty string, it will always be found
        // at the beginning.
        let auto = make_dfa("a*b*");

        assert_eq!(auto.search("cdacd"), Some((0, 0)));
        assert_eq!(auto.search("cdaabbcd"), Some((0, 0)));
        assert_eq!(auto.search("aabbcd"), Some((0, 4)));
        assert_eq!(auto.search("cdb"), Some((0, 0)));
        assert_eq!(auto.search("ab"), Some((0, 2)));
    }

    // Benches copied from regex. Everything is anchored so far,
    // since we don't have any optimizations for non-anchored benchmarks.
    use test::Bencher;
    use regex::Regex;
    use std::iter::repeat;
    #[bench]
    fn anchored_literal_short_non_match(b: &mut Bencher) {
        let re = Regex::new("^zbc(d|e)").unwrap();
        let text = "abcdefghijklmnopqrstuvwxyz";
        b.iter(|| re.is_match(text));
    }

    #[bench]
    fn anchored_literal_short_non_match_dfa(b: &mut Bencher) {
        let auto = make_dfa("^zbc(d|e)").minimize();
        let text = "abcdefghijklmnopqrstuvwxyz";
        b.iter(|| auto.search(text));
    }

    #[bench]
    fn anchored_literal_long_non_match(b: &mut Bencher) {
        let re = Regex::new("^zbc(d|e)").unwrap();
        let text: String = repeat("abcdefghijklmnopqrstuvwxyz").take(15).collect();
        b.iter(|| re.is_match(&text));
    }

    #[bench]
    fn anchored_literal_short_match(b: &mut Bencher) {
        let re = Regex::new("^.bc(d|e)").unwrap();
        let text = "abcdefghijklmnopqrstuvwxyz";
        b.iter(|| re.is_match(text));
    }

    #[bench]
    fn anchored_literal_short_match_dfa(b: &mut Bencher) {
        let auto = make_dfa("^.bc(d|e)").minimize();
        let text = "abcdefghijklmnopqrstuvwxyz";
        b.iter(|| auto.search(text));
    }

    #[bench]
    fn anchored_literal_long_match(b: &mut Bencher) {
        let re = Regex::new("^.bc(d|e)").unwrap();
        let text: String = repeat("abcdefghijklmnopqrstuvwxyz").take(15).collect();
        b.iter(|| re.is_match(&text));
    }

    #[bench]
    fn anchored_literal_long_match_dfa(b: &mut Bencher) {
        let auto = make_dfa("^.bc(d|e)").minimize();
        let text: String = repeat("abcdefghijklmnopqrstuvwxyz").take(15).collect();
        b.iter(|| auto.search(&text));
    }

}

