use std::mem;
use std::num::Int;
use std::collections::BitvSet;
use regex::native::{Program, Save, Jump, Split, Match, OneChar, Any, CharClass,
    FLAG_DOTNL};
use automaton::{TransList, SymbRange};

pub trait NFA {
    /// Returns the epsilon-closure of the given set of states.
    ///
    /// That is, the set of all states that can be reached from a state in the given
    /// set without consuming any input.
    fn eps_closure(&self, states: &BitvSet) -> BitvSet;

    /// Checks whether the given set of states contains an accepting state.
    fn accepting(&self, states: &BitvSet) -> bool;

    /// Returns the set of all transitions leaving one of the given states.
    fn transitions(&self, states: &BitvSet) -> Vec<(SymbRange<u32>, BitvSet)>;
}

impl NFA for Program {
    fn eps_closure(&self, states: &BitvSet) -> BitvSet {
        let mut ret = states.clone();
        let mut new_states = states.clone();
        let mut next_states = BitvSet::with_capacity(self.insts.len());
        loop {
            for s in new_states.iter() {
                match self.insts[s] {
                    Jump(t) => { next_states.insert(t); },
                    Split(t, u) => { next_states.insert(t); next_states.insert(u); },
                    Save(_) => { next_states.insert(s+1); },
                    _ => {},
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

    fn accepting(&self, states: &BitvSet) -> bool {
        for s in states.iter() {
            match self.insts[s] {
                Match => { return true; },
                _ => {},
            }
        }
        return false;
    }

    /// Finds all the transitions out of the given set of states.
    ///
    /// Only transitions that consume output are returned. In particular, you
    /// probably want `states` to already be eps-closed.
    fn transitions(&self, states: &BitvSet) -> Vec<(SymbRange<u32>, BitvSet)> {
        let mut ret = TransList::new();

        for s in states.iter() {
            match self.insts[s] {
                Any(flags) => {
                    if flags & FLAG_DOTNL > 0 {
                        ret.ranges.push((SymbRange::new(0, Int::max_value()), s+1));
                    } else {
                        let nl = '\n' as u32;
                        ret.ranges.push((SymbRange::new(0, nl - 1), s+1));
                        ret.ranges.push((SymbRange::new(nl + 1, Int::max_value()), s+1));
                    }
                },
                // TODO: support case insensitivity
                OneChar(ch, flags) => {
                    ret.ranges.push((SymbRange::single(ch as u32), s+1));
                },
                CharClass(ref ranges, flags) => {
                    let transitions = TransList::from_char_class(ranges, flags, s+1);
                    ret.ranges.push_all(transitions.ranges.as_slice());
                },
                _ => {},
            }
        }

        let trans = ret.collect_transition_pairs();
        trans.into_iter().map(|x| (x.0, self.eps_closure(&x.1))).collect()
    }
}

#[cfg(test)]
mod test {
    use nfa;
    use nfa::NFA;
    use regex;
    use regex::Regex;
    use std::collections::{BitvSet, Bitv};

    fn set(elts: &[uint]) -> BitvSet {
        let mut ret = BitvSet::new();
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

