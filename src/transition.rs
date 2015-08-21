// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bit_set::BitSet;
use char_map::{CharMap, CharMultiMap, CharSet, CharRange};

/// A predicate is a transition that doesn't consume any input, but that can only be traversed if
/// the previous char and the next char satisfy some condition.
#[derive(PartialEq, Debug, Clone)]
pub enum Predicate {
    /// This predicate succeeeds if the previous character is in the first class and the next
    /// character is in the second class.
    InClasses(CharSet, CharSet),
    /// This succeeds if we are currently at the beginning of the input.
    Beginning,
    /// This succeeds if we are currently at the end of the input.
    End,
}

impl Predicate {
    /// Returns a predicate representing the intersection of this one and another one.
    ///
    /// If the intersection is empty, returns None.
    pub fn intersect(&self, other: &Predicate) -> Option<Predicate> {
        use transition::Predicate::*;

        match self {
            &InClasses(ref my_in, ref my_out) => {
                if let &InClasses(ref other_in, ref other_out) = other {
                    let in_ranges = my_in.intersect(other_in);
                    let out_ranges = my_out.intersect(other_out);
                    if !in_ranges.is_empty() && !out_ranges.is_empty() {
                        Some(InClasses(in_ranges, out_ranges))
                    } else {
                        None
                    }
                } else {
                    None
                }
            },
            _ => if self.eq(other) { Some(self.clone()) } else { None }
        }
    }

    pub fn filter_transitions(&self,
                              in_trans: &CharMultiMap<BitSet>,
                              out_trans: &CharMultiMap<BitSet>)
    -> (CharMultiMap<BitSet>, CharMultiMap<BitSet>) {
        use transition::Predicate::*;
        if let &InClasses(ref my_in, ref my_out) = self {
            (in_trans.intersect(my_in), out_trans.intersect(my_out))
        } else {
            (CharMultiMap::new(), CharMultiMap::new())
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct NfaTransitions {
    /// Transitions that consume input.
    pub consuming: CharMultiMap<usize>,
    /// Unconditional transitions that don't consume any input.
    pub eps: Vec<usize>,
    /// Conditional transitions that don't consume any input.
    pub predicates: Vec<(Predicate, usize)>,
}

impl NfaTransitions {
    pub fn new() -> NfaTransitions {
        NfaTransitions {
            consuming: CharMultiMap::new(),
            eps: Vec::new(),
            predicates: Vec::new(),
        }
    }

    pub fn from_vec(vec: Vec<(CharRange, usize)>) -> NfaTransitions {
        NfaTransitions {
            consuming: CharMultiMap::from_vec(vec),
            eps: Vec::new(),
            predicates: Vec::new(),
        }
    }

    /// Groups and sorts the consuming transitions.
    ///
    /// If we map `ch` to `state` then the return value of this method will map `ch` to a set
    /// containing `state`.
    pub fn group_consuming(&self) -> CharMap<BitSet> {
        self.consuming.collect()
    }

    /// Like `group_consuming`, but only returns the groups.
    pub fn groups(&self) -> Vec<BitSet> {
        self.group_consuming().into_iter().map(|x| x.1).collect()
    }
}

#[cfg(test)]
mod tests {
    use bit_set::BitSet;
    use char_map::CharRange;
    use transition::*;

    #[test]
    fn test_groups() {
        let trans = NfaTransitions::from_vec(vec![
            (CharRange::new(0, 2), 0),
            (CharRange::new(4, 5), 2),
            (CharRange::new(0, 2), 2),
            (CharRange::new(3, 3), 1),
            (CharRange::new(4, 5), 1),
        ]);
        let mut sets = trans.groups();
        sets.sort();

        assert_eq!(sets, vec![
            BitSet::from_bytes(&[0b10100000]),
            BitSet::from_bytes(&[0b01000000]),
            BitSet::from_bytes(&[0b01100000]),
        ]);
    }

    /*
    #[test]
    fn test_only_valid_char() {
        let t1 = from_vec(vec![(CharRange::new(5, 5), 7)]);
        let t2 = from_vec(vec![(CharRange::new(5, 6), 7)]);
        let t3 = from_vec(vec![(CharRange::new(5, 5), 7), (CharRange::new(6, 6), 8)]);
        assert_eq!(t1.only_valid_char(), Some((5, 7)));
        assert_eq!(t2.only_valid_char(), None);
        assert_eq!(t3.only_valid_char(), None);
    }
    */
}

