use std::num::Int;
use std::collections::{BitvSet, HashSet, HashMap};
use std::hash::Hash;
use std::fmt::Show;
use nfa::NFA;
use regex::native::{Program, OneChar, CharClass, Any, Save, Jump, Split, FLAG_NEGATED};

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


/// A range of symbols.
///
/// Includes the endpoints.
#[deriving(PartialEq, Show, Copy, Clone, Hash)]
pub struct SymbRange<Symb> {
    from: Symb,
    to: Symb,
}

impl<Symb: Int> Eq for SymbRange<Symb> {}

impl<Symb: Int + Hash> SymbRange<Symb> {
    pub fn new(from: Symb, to: Symb) -> SymbRange<Symb> {
        SymbRange {
            from: from,
            to: to,
        }
    }

    pub fn single(symb: Symb) -> SymbRange<Symb> {
        SymbRange::new(symb, symb)
    }
}

impl<Symb: Int> PartialOrd for SymbRange<Symb> {
    fn partial_cmp(&self, other: &SymbRange<Symb>) -> Option<Ordering> {
        if self.from < other.from {
            Some(Ordering::Less)
        } else if self.from > other.from {
            Some(Ordering::Greater)
        } else {
            self.to.partial_cmp(&other.to)
        }
    }
}

#[deriving(PartialEq, Show)]
pub struct TransList<Symb> {
    pub ranges: Vec<(SymbRange<Symb>, uint)>
}

impl<Symb: Int + Hash> TransList<Symb> {
    pub fn new() -> TransList<Symb> {
        TransList { ranges: Vec::new() }
    }

    pub fn from_vec(vec: Vec<(SymbRange<Symb>, uint)>) -> TransList<Symb> {
        TransList { ranges: vec }
    }

    pub fn find_transition(&self, ch: Symb) -> Option<uint> {
        // TODO: ensure that the transitions are sorted, and use binary search
        for &(ref range, state) in self.ranges.iter() {
            if range.from <= ch && ch <= range.to {
                return Some(state)
            }
        }
        return None
    }

    /// Collects transitions with the same symbol range.
    ///
    /// For every unique SymbRange that appears in `trans`, adds an extra
    /// element to the returned vector. That element is a pair whose first
    /// component is the SymbRange and whose second component
    /// is a set containing all the indices of states associated with
    /// that SymbRange.
    pub fn collect_transition_pairs(self) -> Vec<(SymbRange<Symb>, BitvSet)> {
        let mut map = HashMap::<SymbRange<Symb>, BitvSet>::new();

        for (range, state) in self.split_transitions().ranges.into_iter() {
            if map.contains_key(&range) {
                map[range].insert(state);
            } else {
                let mut new_set = BitvSet::new();
                new_set.insert(state);
                map.insert(range, new_set);
            }
        }

        map.into_iter().collect()
    }

    /// Like collect_transition_pairs, but without the SymbRanges.
    pub fn collect_transitions(self) -> Vec<BitvSet> {
        self.collect_transition_pairs().into_iter().map(|x| x.1).collect()
    }

    /// Splits a set of transitions into equal or disjoint transitions.
    ///
    /// The output is a list of transitions in which every pair of transitions
    /// either have identical SymbRanges or disjoint SymbRanges.
    fn split_transitions(&self) -> TransList<Symb> {
        let mut ret = TransList::new();
        let mut start_symbs = Vec::new();

        for &(ref range, _) in self.ranges.iter() {
            start_symbs.push(range.from);
            if range.to < Int::max_value() {
                start_symbs.push(range.to + Int::one());
            }
        }

        start_symbs.sort();
        start_symbs.dedup();

        for &(ref range, ref state) in self.ranges.iter() {
            let mut idx = match start_symbs.binary_search(&range.from) {
                Ok(i) => i+1,
                Err(i) => i,
            };
            let mut last = range.from;
            loop {
                if idx >= start_symbs.len() || start_symbs[idx] > range.to {
                    ret.ranges.push((SymbRange::new(last, range.to), *state));
                    break;
                } else {
                    ret.ranges.push((SymbRange::new(last, start_symbs[idx] - Int::one()), *state));
                    last = start_symbs[idx];
                    idx += 1;
                }
            }
        }

        ret
    }

    /// Returns the complement of this transition list.
    ///
    /// This assumes that the transition list is sorted and that
    /// every range has the same target state.
    fn negated(&self) -> TransList<Symb> {
        let mut ret = TransList::new();
        let state = self.ranges[0].1;
        let mut last = Int::min_value();

        for &(ref range, _) in self.ranges.iter() {
            if range.from > last {
                ret.ranges.push((SymbRange::new(last, range.from - Int::one()), state));
            }
            last = range.to + Int::one();
        }
        if last < Int::max_value() {
            ret.ranges.push((SymbRange::new(last, Int::max_value()), state));
        }

        ret
    }
}

impl TransList<u32> {
    // TODO: support case insensitivity
    pub fn from_char_class(ranges: &Vec<(char, char)>,
                           flags: u8,
                           state: uint) -> TransList<u32> {
        let mut ret = TransList::new();

        for &(from, to) in ranges.iter() {
            ret.ranges.push((SymbRange::new(from as u32, to as u32), state));
        }
        if flags & FLAG_NEGATED > 0 {
            ret.negated()
        } else {
            ret
        }
    }
}

#[deriving(PartialEq, Show)]
pub struct State<Symb> {
    transitions: TransList<Symb>,
    accepting: bool,
}

impl<Symb: Int + Hash> State<Symb> {
    pub fn new(accepting: bool) -> State<Symb> {
        State {
            transitions: TransList::new(),
            accepting: accepting,
        }
    }
}

#[deriving(PartialEq, Show)]
pub struct Automaton<Symb> {
    states: Vec<State<Symb>>,
}

fn singleton(i: uint) -> BitvSet {
    let mut ret = BitvSet::with_capacity(i+1);
    ret.insert(i);
    ret
}

impl Automaton<u32> {
    /// Creates a deterministic automaton given a non-deterministic one.
    pub fn from_nfa(nfa: &Program) -> Automaton<u32> {
        let mut ret = Automaton { states: Vec::new() };
        let mut state_map = HashMap::<BitvSet, uint>::new();
        let mut active_states = Vec::<BitvSet>::new();
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
}

impl<Symb: Int + Hash + Show + 'static> Automaton<Symb> {
    pub fn execute<'a, Iter: Iterator<&'a Symb>>(&self, mut iter: Iter) -> bool {
        let mut state = 0u;

        loop {
            let cur_state = &self.states[state];
            match iter.next() {
                None => return cur_state.accepting,
                Some(ch) => {
                    match cur_state.transitions.find_transition(*ch) {
                        Some(next_state) => state = next_state,
                        None => return false,
                    }
                }
            }
        }
    }

    fn accepting_states(&self) -> BitvSet {
        let mut ret = BitvSet::with_capacity(self.states.len());

        for (idx, state) in self.states.iter().enumerate() {
            if state.accepting {
                ret.insert(idx);
            }
        }

        ret
    }

    fn non_accepting_states(&self) -> BitvSet {
        let mut ret = BitvSet::with_capacity(self.states.len());

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
    fn reversed(&self) -> Automaton<Symb> {
        let mut ret = Automaton {
            states: Vec::with_capacity(self.states.len()),
        };

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
    pub fn minimize(&self) -> Automaton<Symb> {
        let acc_states = self.accepting_states();
        let non_acc_states = self.non_accepting_states();
        let mut partition = HashSet::<BitvSet>::new();
        let mut distinguishers = HashSet::<BitvSet>::new();
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
                trans.ranges.push_all(reversed.states[state].transitions.ranges.as_slice());
            }

            let sets = trans.collect_transitions();

            // For each set in our partition so far, split it if
            // some element of `sets` reveals it to contain more than
            // one equivalence class.
            for s in sets.iter() {
                let mut next_partition = HashSet::<BitvSet>::new();

                for y in partition.iter() {
                    let y0: BitvSet = y.intersection(s).collect();
                    let y1: BitvSet = y.difference(s).collect();

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

        let mut ret = Automaton {
            states: vec![],
        };

        // Build a map that associates a state with the partition element it
        // belongs to.
        let mut state_to_partition = HashMap::<uint, &BitvSet>::new();
        for part in partition.iter() {
            for state in part.iter() {
                state_to_partition.insert(state, part);
            }
        }

        let mut old_state_to_new = HashMap::<uint, uint>::new();
        for part in partition.iter() {
            let rep_idx = part.iter().next().unwrap();
            let rep = &self.states[rep_idx];
            ret.states.push(State::<Symb>::new(rep.accepting));

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

#[cfg(test)]
mod test {
    use automaton;
    use automaton::{Automaton, State, SymbRange, TransList};
    use std::collections::{Bitv, BitvSet};
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
    fn even_bs_auto() -> Automaton<u8> {
        let mut auto = Automaton::<u8> {
            states: vec![],
        };

        auto.states.push(State::new(true));
        auto.states.push(State::new(false));

        auto.states[0].transitions.ranges.push((SymbRange::single('a' as u8), 0));
        auto.states[0].transitions.ranges.push((SymbRange::single('b' as u8), 1));
        auto.states[1].transitions.ranges.push((SymbRange::single('a' as u8), 1));
        auto.states[1].transitions.ranges.push((SymbRange::single('b' as u8), 0));

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
        let trans = TransList::<u8>::from_vec(vec![
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

        let mut rev = Automaton::<u8> {
            states: vec![],
        };

        rev.states.push(State::new(true));
        rev.states.push(State::new(false));

        rev.states[0].transitions.ranges.push((SymbRange::single('a' as u8), 0));
        rev.states[0].transitions.ranges.push((SymbRange::single('b' as u8), 1));
        rev.states[1].transitions.ranges.push((SymbRange::single('b' as u8), 0));
        rev.states[1].transitions.ranges.push((SymbRange::single('c' as u8), 0));
        rev.states[1].transitions.ranges.push((SymbRange::single('a' as u8), 1));

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
            BitvSet::from_bitv(Bitv::from_bytes(&[0b01000000])),
            BitvSet::from_bitv(Bitv::from_bytes(&[0b10100000])),
            BitvSet::from_bitv(Bitv::from_bytes(&[0b01100000])),
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

