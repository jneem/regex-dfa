use automaton::Automaton;
use std::mem;
use std::collections::BitSet;
use transition::{SymbRange, TransList};

pub trait Nfa {
    /// Returns the epsilon-closure of the given set of states.
    ///
    /// That is, the set of all states that can be reached from a state in the given
    /// set without consuming any input.
    fn eps_closure(&self, states: &BitSet) -> BitSet;

    /// Checks whether the given set of states contains an accepting state.
    fn accepting(&self, states: &BitSet) -> bool;

    /// Returns the set of all transitions leaving one of the given states.
    fn transitions(&self, states: &BitSet) -> Vec<(SymbRange, BitSet)>;
}

impl Nfa for Automaton {
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
        let trans = TransList::from_vec(trans).collect_transition_pairs();

        trans.into_iter().map(|x| (x.0, self.eps_closure(&x.1))).collect()
    }
}

#[cfg(never)]
mod test {
    use nfa;
    use nfa::Nfa;
    use regex;
    use regex::Regex;
    use std::collections::{BitSet, BitVec};

    fn set(elts: &[usize]) -> BitSet {
        let mut ret = BitSet::new();
        for e in elts.iter() {
            ret.insert(*e);
        }
        ret
    }

    fn prog(re_str: &str) -> regex::native::Program {
        let re = Regex::new(re_str).ok().unwrap();
        match re {
            Regex::Dynamic(dyn) => dyn.prog,
            _ => { panic!("failed to compile re") }
        }
    }

    #[test]
    fn test_eps_closure() {
        let prog = prog("a*b*");
        // The compiled version should be:
        // [Save(0), Split(2, 4), OneChar(a, 0), Jump(1), Split(5, 7), OneChar(b, 0), Jump(4), Save(1), Match]
        assert_eq!(prog.eps_closure(&set(&[0])), set(&[0, 1, 2, 4, 5, 7, 8]));
        assert_eq!(prog.eps_closure(&set(&[1])), set(&[1, 2, 4, 5, 7, 8]));
        assert_eq!(prog.eps_closure(&set(&[2])), set(&[2]));
        assert_eq!(prog.eps_closure(&set(&[3])), set(&[1, 2, 3, 4, 5, 7, 8]));
        assert_eq!(prog.eps_closure(&set(&[4])), set(&[4, 5, 7, 8]));
        assert_eq!(prog.eps_closure(&set(&[5])), set(&[5]));
        assert_eq!(prog.eps_closure(&set(&[6])), set(&[4, 5, 6, 7, 8]));
        assert_eq!(prog.eps_closure(&set(&[7])), set(&[7, 8]));
        assert_eq!(prog.eps_closure(&set(&[8])), set(&[8]));
    }

    #[test]
    fn test_accepting() {
        let prog = prog("a*b*");
        assert_eq!(prog.accepting(&set(&[0, 3, 8])), true);
        assert_eq!(prog.accepting(&set(&[0, 1, 3, 7])), false);
    }
}

