use bit_set::BitSet;
use std;
use std::collections::{HashSet, HashMap};
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::mem;
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
pub struct NfaState {
    pub transitions: NfaTransitions,
    pub accepting: bool,
}

impl NfaState {
    pub fn new(accepting: bool) -> NfaState {
        NfaState {
            transitions: NfaTransitions::new(),
            accepting: accepting,
        }
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


#[derive(PartialEq)]
pub struct Nfa {
    // TODO: make this private once builder has been transitioned away from
    // using Nfa.
    pub states: Vec<NfaState>,
}

pub struct Dfa {
    states: Vec<DfaState>,
    initial: usize,
}

fn singleton(i: usize) -> BitSet {
    let mut ret = BitSet::with_capacity(i+1);
    ret.insert(i);
    ret
}

impl Debug for Nfa {
    fn fmt(&self, f: &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
        try!(f.write_fmt(format_args!("Nfa ({} states):\n", self.states.len())));

        for (st_idx, st) in self.states.iter().enumerate() {
            try!(f.write_fmt(format_args!("\tState {} (accepting: {}):\n", st_idx, st.accepting)));

            if !st.transitions.ranges.is_empty() {
                try!(f.write_str("\t\tTransitions:\n"));
                for &(range, target) in &st.transitions.ranges {
                    try!(f.write_fmt(format_args!("\t\t\t{} -- {} => {}\n",
                                                  range.from, range.to, target)));
                }
            }

            if !st.transitions.eps.is_empty() {
                try!(f.write_fmt(format_args!("\t\tEps-transitions: {:?}\n", &st.transitions.eps)));
            }
        }
        Ok(())
    }
}

impl Nfa {
    pub fn new() -> Nfa {
        Nfa {
            states: Vec::new(),
        }
    }

    pub fn with_capacity(n: usize) -> Nfa {
        Nfa {
            states: Vec::with_capacity(n),
        }
    }

    pub fn add_transition(&mut self, from: usize, to: usize, r: SymbRange) {
        self.states[from].transitions.ranges.push((r, to));
    }

    pub fn add_eps(&mut self, from: usize, to: usize) {
        self.states[from].transitions.eps.push(to);
    }

    /// Creates a deterministic automaton given a non-deterministic one.
    pub fn determinize(&self) -> Dfa {
        let mut ret = Dfa::new();
        let mut state_map = HashMap::<BitSet, usize>::new();
        let mut active_states = Vec::<BitSet>::new();
        let start_state = self.eps_closure(&singleton(0));

        ret.add_state(self.accepting(&start_state));
        active_states.push(start_state.clone());
        state_map.insert(start_state, 0);

        while active_states.len() > 0 {
            let state = active_states.pop().unwrap();
            let state_idx = *state_map.get(&state).unwrap();
            let trans = self.transitions(&state);
            for (range, target) in trans.into_iter() {
                let target_idx = if state_map.contains_key(&target) {
                        *state_map.get(&target).unwrap()
                    } else {
                        ret.add_state(self.accepting(&target));
                        active_states.push(target.clone());
                        state_map.insert(target, ret.states.len() - 1);
                        ret.states.len() - 1
                    };
                ret.add_transition(state_idx, target_idx, range);
            }
        }

        ret.sort_transitions();
        ret
    }

    fn eps_closure(&self, states: &BitSet) -> BitSet {
        let mut ret = states.clone();
        let mut new_states = states.clone();
        let mut next_states = BitSet::with_capacity(self.states.len());
        loop {
            for s in &new_states {
                for &t in &self.states[s].transitions.eps {
                    next_states.insert(t);
                }
            }

            if next_states.is_subset(&ret) {
                return ret;
            } else {
                next_states.difference_with(&ret);
                ret.union_with(&next_states);
                mem::swap(&mut next_states, &mut new_states);
                next_states.clear();
            }
        }
    }

    fn accepting(&self, states: &BitSet) -> bool {
        states.iter().any(|s| { self.states[s].accepting })
    }

    /// Finds all the transitions out of the given set of states.
    ///
    /// Only transitions that consume output are returned. In particular, you
    /// probably want `states` to already be eps-closed.
    fn transitions(&self, states: &BitSet) -> Vec<(SymbRange, BitSet)> {
        let trans = states.iter()
                          .flat_map(|s| self.states[s].transitions.ranges.iter().map(|&i| i))
                          .collect();
        let trans = NfaTransitions::from_vec(trans).collect_transition_pairs();

        trans.into_iter().map(|x| (x.0, self.eps_closure(&x.1))).collect()
    }
}

impl Dfa {
    fn new() -> Dfa {
        Dfa {
            states: Vec::new(),
            initial: 0,
        }
    }

    fn add_state(&mut self, accepting: bool) {
        self.states.push(DfaState::new(accepting));
    }

    fn add_transition(&mut self, from: usize, to: usize, range: SymbRange) {
        self.states[from].transitions.add(range, to);
    }

    fn sort_transitions(&mut self) {
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
                trans.ranges.extend(reversed.states[state].transitions.ranges.iter());
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
            ret.states.push(NfaState::new(st.accepting));
        }

        for (idx, st) in self.states.iter().enumerate() {
            for &(ref range, target) in st.transitions.iter() {
                ret.states[target].transitions.ranges.push((*range, idx));
            }
        }

        ret
    }
}

impl Debug for Dfa {
    fn fmt(&self, f: &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
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
    use automaton::{Nfa, NfaState};
    use builder;
    use regex_syntax;
    use transition::SymbRange;

    fn parse(re: &str) -> Nfa {
        let expr = regex_syntax::Expr::parse(re).unwrap();
        builder::NfaBuilder::from_expr(&expr).to_automaton()
    }

    fn u32str<'a>(s: &'a str) -> Box<Iterator<Item=u32> + 'a> {
        Box::new(s.chars().map(|c| c as u32))
    }

    fn u32istr<'a>(s: &'a str) -> Box<Iterator<Item=(usize, u32)> + 'a> {
        Box::new(s.char_indices().map(|(i, c)| (i, c as u32)))
    }

    /// Returns an automaton that accepts strings with an even number of 'b's.
    fn even_bs_auto() -> Nfa {
        let mut auto = Nfa::new();

        auto.states.push(NfaState::new(true));
        auto.states.push(NfaState::new(false));

        auto.states[0].transitions.ranges.push((SymbRange::single('a' as u32), 0));
        auto.states[0].transitions.ranges.push((SymbRange::single('b' as u32), 1));
        auto.states[1].transitions.ranges.push((SymbRange::single('a' as u32), 1));
        auto.states[1].transitions.ranges.push((SymbRange::single('b' as u32), 0));

        auto
    }

    #[test]
    fn test_execute() {
        let auto = even_bs_auto().determinize();

        assert_eq!(auto.execute(u32str("aaaaaaa")), true);
        assert_eq!(auto.execute(u32str("aabaaaaa")), false);
        assert_eq!(auto.execute(u32str("aabaaaaab")), true);
        assert_eq!(auto.execute(u32str("aabaaaaaba")), true);
        assert_eq!(auto.execute(u32str("aabaabaaba")), false);
        assert_eq!(auto.execute(u32str("aabbabaaba")), true);
    }

    #[test]
    fn test_reverse() {
        // TODO: test something non-palindromic
        let auto = even_bs_auto().determinize();

        let mut rev = Nfa::new();

        rev.states.push(NfaState::new(true));
        rev.states.push(NfaState::new(false));

        rev.states[0].transitions.ranges.push((SymbRange::single('a' as u32), 0));
        rev.states[0].transitions.ranges.push((SymbRange::single('b' as u32), 1));
        rev.states[1].transitions.ranges.push((SymbRange::single('b' as u32), 0));
        rev.states[1].transitions.ranges.push((SymbRange::single('a' as u32), 1));

        assert_eq!(rev, auto.reversed());
    }

    #[test]
    fn test_minimize() {
        let auto = parse("a*b*").determinize().minimize();

        assert_eq!(auto.execute(u32str("aaabbbbbb")), true);
        assert_eq!(auto.execute(u32str("bbbb")), true);
        assert_eq!(auto.execute(u32str("a")), true);
        assert_eq!(auto.execute(u32str("")), true);
        assert_eq!(auto.execute(u32str("ba")), false);
        assert_eq!(auto.execute(u32str("aba")), false);

        assert_eq!(auto.states.len(), 2);
    }

    #[test]
    fn test_determinize() {
        let auto = parse("a*b*").determinize();

        assert_eq!(auto.execute(u32str("aaabbbbbb")), true);
        assert_eq!(auto.execute(u32str("bbbb")), true);
        assert_eq!(auto.execute(u32str("a")), true);
        assert_eq!(auto.execute(u32str("")), true);
        assert_eq!(auto.execute(u32str("ba")), false);
        assert_eq!(auto.execute(u32str("aba")), false);
    }

    #[test]
    fn test_longest_match() {
        let auto = parse("a*b*").determinize();

        assert_eq!(auto.longest_match("aba".char_indices()), Some(2));
        assert_eq!(auto.longest_match("baba".char_indices()), Some(1));
        assert_eq!(auto.longest_match("ac".char_indices()), Some(1));
        assert_eq!(auto.longest_match("ab".char_indices()), Some(2));
        assert_eq!(auto.longest_match("bc".char_indices()), Some(1));
        assert_eq!(auto.longest_match("b".char_indices()), Some(1));

        let auto = parse("a+b*").determinize();

        assert_eq!(auto.longest_match("aba".char_indices()), Some(2));
        assert_eq!(auto.longest_match("baba".char_indices()), None);
        assert_eq!(auto.longest_match("ac".char_indices()), Some(1));
        assert_eq!(auto.longest_match("ab".char_indices()), Some(2));
        assert_eq!(auto.longest_match("bc".char_indices()), None);
        assert_eq!(auto.longest_match("b".char_indices()), None);
    }

    #[test]
    fn test_search() {
        let auto = parse("a+b*").determinize();

        assert_eq!(auto.search("cdacd"), Some((2, 3)));
        assert_eq!(auto.search("cdaabbcd"), Some((2, 6)));
        assert_eq!(auto.search("aabbcd"), Some((0, 4)));
        assert_eq!(auto.search("cdb"), None);
        assert_eq!(auto.search("ab"), Some((0, 2)));

        // If the pattern matches the empty string, it will always be found
        // at the beginning.
        let auto = parse("a*b*").determinize();

        assert_eq!(auto.search("cdacd"), Some((0, 0)));
        assert_eq!(auto.search("cdaabbcd"), Some((0, 0)));
        assert_eq!(auto.search("aabbcd"), Some((0, 4)));
        assert_eq!(auto.search("cdb"), Some((0, 0)));
        assert_eq!(auto.search("ab"), Some((0, 2)));
    }
}

