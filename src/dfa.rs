// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bit_set::BitSet;
use error;
use nfa::Nfa;
use std;
use std::collections::{HashSet, HashMap};
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::result::Result;
use transition::{DfaTransitions, NfaTransitions, SymbRange};


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
    pub transitions: DfaTransitions,
    pub accepting: bool,
}

impl DfaState {
    pub fn new(accepting: bool) -> DfaState {
        DfaState {
            transitions: DfaTransitions::new(),
            accepting: accepting,
        }
    }
}

pub struct Dfa {
    states: Vec<DfaState>,
    initial: usize,
}

impl Dfa {
    /// Returns a `Dfa` with no states.
    pub fn new() -> Dfa {
        Dfa {
            states: Vec::new(),
            initial: 0,
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

    pub fn add_state(&mut self, accepting: bool) {
        self.states.push(DfaState::new(accepting));
    }

    pub fn add_transition(&mut self, from: usize, to: usize, range: SymbRange) {
        self.states[from].transitions.add(range, to);
    }

    pub fn sort_transitions(&mut self) {
        for st in &mut self.states {
            st.transitions.sort();
        }
    }

    pub fn execute<Iter: Iterator<Item=u32>>(&self, mut iter: Iter) -> bool {
        let mut state = self.initial;

        loop {
            let cur_state = &self.states[state];
            match iter.next() {
                None => return cur_state.accepting,
                Some(ch) => {
                    match cur_state.transitions.find_transition(ch) {
                        Some(next_state) => state = next_state,
                        None => return false,
                    }
                }
            }
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

    /// If we match some prefix of the string, returns the index after
    /// the endpoint of the longest match.
    pub fn longest_match<Iter>(&self, mut iter: Iter) -> Option<usize>
    where Iter: Iterator<Item=(usize, char)> {
        let mut state = self.initial;
        let mut last_match = if self.states[state].accepting { Some(0) } else { None };

        loop {
            let cur_state = &self.states[state];
            match iter.next() {
                None => return last_match,
                Some((idx, ch)) => {
                    match cur_state.transitions.find_transition(ch as u32) {
                        Some(next_state) => {
                            state = next_state;
                            if self.states[state].accepting {
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

        match self.longest_match(iter.clone()) {
            None => (),
            Some(n) => return Some((0, n)),
        }
        loop {
            match iter.next() {
                None => return None,
                Some((m, ch)) => {
                    match self.longest_match(iter.clone()) {
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
        let acc_states = self.accepting_states();
        let non_acc_states = self.non_accepting_states();
        let mut partition = HashSet::<BitSet>::new();
        let mut distinguishers = HashSet::<BitSet>::new();
        let reversed = self.reversed();

        partition.insert(acc_states.clone());
        if !non_acc_states.is_empty() {
            partition.insert(non_acc_states.clone());
        }
        distinguishers.insert(acc_states.clone());

        while distinguishers.len() > 0 {
            let dist = distinguishers.pop_arbitrary();

            // Find all transitions leading into dist.
            let mut trans = NfaTransitions::new();
            for state in dist.iter() {
                trans.ranges.extend(reversed.transitions_from(state).iter());
            }

            let sets = trans.collect_transitions();

            // For each set in our partition so far, split it if
            // some element of `sets` reveals it to contain more than
            // one equivalence class.
            for s in sets.iter() {
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
        let mut old_state_to_new = HashMap::<usize, usize>::new();
        for part in partition.iter() {
            let rep_idx = part.iter().next().unwrap();
            let rep = &self.states[rep_idx];
            ret.states.push(DfaState::new(rep.accepting));

            for state in part.iter() {
                old_state_to_new.insert(state, ret.states.len() - 1);
            }
        }

        // Fix the indices in all transitions to refer to the new state numbering.
        for part in partition.iter() {
            let old_src_idx = part.iter().next().unwrap();
            let new_src_idx = old_state_to_new.get(&old_src_idx).unwrap();

            for &(ref range, old_tgt_idx) in self.states[old_src_idx].transitions.iter() {
                let new_tgt_idx = old_state_to_new.get(&old_tgt_idx).unwrap();
                ret.states[*new_src_idx].transitions.add(range.clone(), *new_tgt_idx);
            }

            if part.contains(&0) {
                ret.initial = *new_src_idx;
            }
        }

        ret
    }

    fn accepting_states(&self) -> BitSet {
        let mut ret = BitSet::with_capacity(self.states.len());

        for (idx, state) in self.states.iter().enumerate() {
            if state.accepting {
                ret.insert(idx);
            }
        }

        ret
    }

    fn non_accepting_states(&self) -> BitSet {
        let mut ret = BitSet::with_capacity(self.states.len());

        for (idx, state) in self.states.iter().enumerate() {
            if !state.accepting {
                ret.insert(idx);
            }
        }

        ret
    }

    /// Returns the automaton with all its transitions reversed.
    /// Its states will have the same indices as those of the original automaton.
    fn reversed(&self) -> Nfa {
        let mut ret = Nfa::with_capacity(self.states.len());

        for st in self.states.iter() {
            ret.add_state(st.accepting);
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
            try!(f.write_fmt(format_args!("\tState {} (accepting: {}):\n", st_idx, st.accepting)));

            if !st.transitions.is_empty() {
                try!(f.write_str("\t\tTransitions:\n"));
                for &(range, target) in st.transitions.iter() {
                    try!(f.write_fmt(format_args!("\t\t\t{} -- {} => {}\n",
                                                  range.from, range.to, target)));
                }
            }
        }
        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use dfa::Dfa;
    use nfa::Nfa;
    use builder;
    use regex_syntax;
    use transition::SymbRange;

    fn make_dfa(re: &str) -> Dfa {
        let expr = regex_syntax::Expr::parse(re).unwrap();
        builder::NfaBuilder::from_expr(&expr).to_automaton().determinize()
    }

    fn u32str<'a>(s: &'a str) -> Box<Iterator<Item=u32> + 'a> {
        Box::new(s.chars().map(|c| c as u32))
    }

    // Returns an automaton that accepts strings with an even number of 'b's.
    fn even_bs_nfa() -> Nfa {
        let mut ret = Nfa::new();

        ret.add_state(true);
        ret.add_state(false);
        ret.add_transition(0, 0, SymbRange::single('a' as u32));
        ret.add_transition(0, 1, SymbRange::single('b' as u32));
        ret.add_transition(1, 1, SymbRange::single('a' as u32));
        ret.add_transition(1, 0, SymbRange::single('b' as u32));
        ret
    }

    fn even_bs_dfa() -> Dfa {
        even_bs_nfa().determinize()
    }

    #[test]
    fn test_execute() {
        let auto = even_bs_dfa();

        assert_eq!(auto.execute(u32str("aaaaaaa")), true);
        assert_eq!(auto.execute(u32str("aabaaaaa")), false);
        assert_eq!(auto.execute(u32str("aabaaaaab")), true);
        assert_eq!(auto.execute(u32str("aabaaaaaba")), true);
        assert_eq!(auto.execute(u32str("aabaabaaba")), false);
        assert_eq!(auto.execute(u32str("aabbabaaba")), true);
    }

    #[test]
    fn test_reverse() {
        let dfa = even_bs_dfa();

        let mut rev = Nfa::new();
        rev.add_state(true);
        rev.add_state(false);
        rev.add_transition(0, 0, SymbRange::single('a' as u32));
        rev.add_transition(0, 1, SymbRange::single('b' as u32));
        rev.add_transition(1, 0, SymbRange::single('b' as u32));
        rev.add_transition(1, 1, SymbRange::single('a' as u32));

        assert_eq!(rev, dfa.reversed());
    }

    #[test]
    fn test_minimize() {
        let auto = make_dfa("a*b*").minimize();

        assert_eq!(auto.execute(u32str("aaabbbbbb")), true);
        assert_eq!(auto.execute(u32str("bbbb")), true);
        assert_eq!(auto.execute(u32str("a")), true);
        assert_eq!(auto.execute(u32str("")), true);
        assert_eq!(auto.execute(u32str("ba")), false);
        assert_eq!(auto.execute(u32str("aba")), false);

        assert_eq!(auto.states.len(), 2);
    }

    #[test]
    fn test_dfa() {
        let auto = make_dfa("a*b*");

        assert_eq!(auto.execute(u32str("aaabbbbbb")), true);
        assert_eq!(auto.execute(u32str("bbbb")), true);
        assert_eq!(auto.execute(u32str("a")), true);
        assert_eq!(auto.execute(u32str("")), true);
        assert_eq!(auto.execute(u32str("ba")), false);
        assert_eq!(auto.execute(u32str("aba")), false);
    }

    #[test]
    fn test_longest_match() {
        let auto = make_dfa("a*b*");

        assert_eq!(auto.longest_match("aba".char_indices()), Some(2));
        assert_eq!(auto.longest_match("baba".char_indices()), Some(1));
        assert_eq!(auto.longest_match("ac".char_indices()), Some(1));
        assert_eq!(auto.longest_match("ab".char_indices()), Some(2));
        assert_eq!(auto.longest_match("bc".char_indices()), Some(1));
        assert_eq!(auto.longest_match("b".char_indices()), Some(1));

        let auto = make_dfa("a+b*");

        assert_eq!(auto.longest_match("aba".char_indices()), Some(2));
        assert_eq!(auto.longest_match("baba".char_indices()), None);
        assert_eq!(auto.longest_match("ac".char_indices()), Some(1));
        assert_eq!(auto.longest_match("ab".char_indices()), Some(2));
        assert_eq!(auto.longest_match("bc".char_indices()), None);
        assert_eq!(auto.longest_match("b".char_indices()), None);
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
        let auto = make_dfa("zbc(d|e)").minimize();
        let text = "abcdefghijklmnopqrstuvwxyz";
        b.iter(|| auto.execute(u32str(text)));
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
        let auto = make_dfa(".bc(d|e)").minimize();
        let text = "abcdefghijklmnopqrstuvwxyz";
        b.iter(|| auto.execute(u32str(text)));
    }

    #[bench]
    fn anchored_literal_long_match(b: &mut Bencher) {
        let re = Regex::new("^.bc(d|e)").unwrap();
        let text: String = repeat("abcdefghijklmnopqrstuvwxyz").take(15).collect();
        b.iter(|| re.is_match(&text));
    }

    #[bench]
    fn anchored_literal_long_match_dfa(b: &mut Bencher) {
        let auto = make_dfa(".bc(d|e)").minimize();
        let text: String = repeat("abcdefghijklmnopqrstuvwxyz").take(15).collect();
        b.iter(|| auto.execute(u32str(&text)));
    }

}

