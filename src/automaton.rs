use std;
use std::collections::{BitSet, HashSet, HashMap};
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use nfa::Nfa;
use transition::{SymbRange, TransList};

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
pub struct State {
    pub transitions: TransList,
    pub accepting: bool,
}

impl State {
    pub fn new(accepting: bool) -> State {
        State {
            transitions: TransList::new(),
            accepting: accepting,
        }
    }
}

#[derive(PartialEq)]
pub struct Automaton {
    // TODO: after stabilizing the appropriate accessor/modifiers, make this private.
    pub states: Vec<State>,
}

fn singleton(i: usize) -> BitSet {
    let mut ret = BitSet::with_capacity(i+1);
    ret.insert(i);
    ret
}

impl Debug for Automaton {
    fn fmt(&self, f: &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
        try!(f.write_fmt(format_args!("Automaton ({} states):\n", self.states.len())));

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

impl Automaton {
    pub fn new() -> Automaton {
        Automaton {
            states: Vec::new(),
        }
    }

    pub fn with_capacity(n: usize) -> Automaton {
        Automaton {
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
    pub fn from_nfa<T: Nfa>(nfa: &T) -> Automaton {
        let mut ret = Automaton::new();
        let mut state_map = HashMap::<BitSet, usize>::new();
        let mut active_states = Vec::<BitSet>::new();
        let start_state = nfa.eps_closure(&singleton(0));

        ret.states.push(State::new(nfa.accepting(&start_state)));
        active_states.push(start_state.clone());
        state_map.insert(start_state, 0);

        while active_states.len() > 0 {
            let state = active_states.pop().unwrap();
            let state_idx = *state_map.get(&state).unwrap();
            let trans = nfa.transitions(&state);
            for (range, target) in trans.into_iter() {
                let target_idx = if state_map.contains_key(&target) {
                        *state_map.get(&target).unwrap()
                    } else {
                        ret.states.push(State::new(nfa.accepting(&target)));
                        active_states.push(target.clone());
                        state_map.insert(target, ret.states.len() - 1);
                        ret.states.len() - 1
                    };
                ret.states[state_idx].transitions.ranges.push((range, target_idx));
            }
        }

        ret
    }

    pub fn execute<Iter: Iterator<Item=u32>>(&self, mut iter: Iter) -> bool {
        let mut state = 0usize;

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
    ///
    /// This may be a non-deterministic automaton. Its states
    /// will have the same indices as those of the original automaton.
    fn reversed(&self) -> Automaton {
        let mut ret = Automaton::with_capacity(self.states.len());

        for st in self.states.iter() {
            ret.states.push(State::new(st.accepting));
        }

        for (idx, st) in self.states.iter().enumerate() {
            for &(ref range, target) in st.transitions.ranges.iter() {
                ret.states[target].transitions.ranges.push((*range, idx));
            }
        }

        ret
    }

    /// Returns an equivalent DFA with a minimal number of states.
    ///
    /// Uses Hopcroft's algorithm.
    pub fn minimize(&self) -> Automaton {
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
            let mut trans = TransList::new();
            for state in dist.iter() {
                trans.ranges.push_all(&reversed.states[state].transitions.ranges[..]);
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

        let mut ret = Automaton::new();

        // Build a map that associates a state with the partition element it
        // belongs to.
        let mut state_to_partition = HashMap::<usize, &BitSet>::new();
        for part in partition.iter() {
            for state in part.iter() {
                state_to_partition.insert(state, part);
            }
        }

        let mut old_state_to_new = HashMap::<usize, usize>::new();
        for part in partition.iter() {
            let rep_idx = part.iter().next().unwrap();
            let rep = &self.states[rep_idx];
            ret.states.push(State::new(rep.accepting));

            for state in part.iter() {
                old_state_to_new.insert(state, ret.states.len() - 1);
            }
        }

        for part in partition.iter() {
            let old_src_idx = part.iter().next().unwrap();
            let new_src_idx = old_state_to_new.get(&old_src_idx).unwrap();

            for &(ref range, old_tgt_idx) in self.states[old_src_idx].transitions.ranges.iter() {
                let new_tgt_idx = old_state_to_new.get(&old_tgt_idx).unwrap();
                ret.states[*new_src_idx].transitions.ranges.push((range.clone(), *new_tgt_idx));
            }
        }

        ret
    }
}

#[cfg(never)]
mod test {
    use automaton;
    use automaton::{Automaton, State, SymbRange, TransList};
    use std::collections::{BitVec, BitSet};
    use regex;
    use regex::Regex;

    /// FIXME: this is C&P from ::nfa. Refactor it somewhere.
    fn prog(re_str: &str) -> regex::native::Program {
        let re = Regex::new(re_str).ok().unwrap();
        match re {
            Regex::Dynamic(dyn) => dyn.prog,
            _ => { panic!("failed to compile re") }
        }
    }

    // FIXME: there should be a better way to implement
    // Automaton::execute that doesn't require this convenience function
    fn u32str(s: &str) -> Vec<u32> {
        s.chars().map(|c| c as u32).collect()
    }

    /// Returns an automaton that accepts strings with an even number of 'b's.
    fn even_bs_auto() -> Automaton {
        let mut auto = Automaton {
            states: vec![],
        };

        auto.states.push(State::new(true));
        auto.states.push(State::new(false));

        auto.states[0].transitions.ranges.push((SymbRange::single('a' as u32), 0));
        auto.states[0].transitions.ranges.push((SymbRange::single('b' as u32), 1));
        auto.states[1].transitions.ranges.push((SymbRange::single('a' as u32), 1));
        auto.states[1].transitions.ranges.push((SymbRange::single('b' as u32), 0));

        auto
    }

    #[test]
    fn test_execute() {
        let auto = even_bs_auto();

        assert_eq!(auto.execute("aaaaaaa".as_bytes().iter()), true);
        assert_eq!(auto.execute("aabaaaaa".as_bytes().iter()), false);
        assert_eq!(auto.execute("aabaaaaab".as_bytes().iter()), true);
        assert_eq!(auto.execute("aabaaaaaba".as_bytes().iter()), true);
        assert_eq!(auto.execute("aabaabaaba".as_bytes().iter()), false);
        assert_eq!(auto.execute("aabbabaaba".as_bytes().iter()), true);
    }

    #[test]
    fn test_split_transitions() {
        let trans = TransList::from_vec(vec![
            (SymbRange::new(0, 5), 0),
            (SymbRange::new(2, 7), 1),
        ]);

        let trans = trans.split_transitions();
        assert_eq!(trans.ranges, vec![
            (SymbRange::new(0, 1), 0),
            (SymbRange::new(2, 5), 0),
            (SymbRange::new(2, 5), 1),
            (SymbRange::new(6, 7), 1),
        ]);
    }

    #[test]
    fn test_reverse() {
        let mut auto = even_bs_auto();
        auto.states[0].transitions.ranges.push((SymbRange::single('c' as u8), 1));

        let mut rev = Automaton {
            states: vec![],
        };

        rev.states.push(State::new(true));
        rev.states.push(State::new(false));

        rev.states[0].transitions.ranges.push((SymbRange::single('a' as u32), 0));
        rev.states[0].transitions.ranges.push((SymbRange::single('b' as u32), 1));
        rev.states[1].transitions.ranges.push((SymbRange::single('b' as u32), 0));
        rev.states[1].transitions.ranges.push((SymbRange::single('c' as u32), 0));
        rev.states[1].transitions.ranges.push((SymbRange::single('a' as u32), 1));

        assert_eq!(rev, auto.reversed());
    }

    #[test]
    fn test_collect_transitions() {
        let trans = TransList::<u8>::from_vec(vec![
            (SymbRange::new(0, 2), 0),
            (SymbRange::new(4, 5), 2),
            (SymbRange::new(0, 2), 2),
            (SymbRange::new(3, 3), 1),
            (SymbRange::new(4, 5), 1),
        ]);
        let mut sets = trans.collect_transitions();
        sets.sort();

        assert_eq!(sets, vec![
            BitSet::from_bitv(BitVec::from_bytes(&[0b01000000])),
            BitSet::from_bitv(BitVec::from_bytes(&[0b10100000])),
            BitSet::from_bitv(BitVec::from_bytes(&[0b01100000])),
        ]);
    }

    #[test]
    fn test_minimize() {
        let auto = Automaton::from_nfa(&prog("a*b*")).minimize();

        assert_eq!(auto.execute(u32str("aaabbbbbb").iter()), true);
        assert_eq!(auto.execute(u32str("bbbb").iter()), true);
        assert_eq!(auto.execute(u32str("a").iter()), true);
        assert_eq!(auto.execute(u32str("").iter()), true);
        assert_eq!(auto.execute(u32str("ba").iter()), false);
        assert_eq!(auto.execute(u32str("aba").iter()), false);

        assert_eq!(auto.minimize(), auto);
    }

    #[test]
    fn test_from_nfa() {
        let auto = Automaton::from_nfa(&prog("a*b*"));

        assert_eq!(auto.execute(u32str("aaabbbbbb").iter()), true);
        assert_eq!(auto.execute(u32str("bbbb").iter()), true);
        assert_eq!(auto.execute(u32str("a").iter()), true);
        assert_eq!(auto.execute(u32str("").iter()), true);
        assert_eq!(auto.execute(u32str("ba").iter()), false);
        assert_eq!(auto.execute(u32str("aba").iter()), false);
    }
}

