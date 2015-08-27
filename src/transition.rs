// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bit_set::BitSet;
use char_map::{CharMap, CharMultiMap, CharSet, CharRange};
use std;

/// A predicate is a transition that doesn't consume any input, but that can only be traversed if
/// the previous char and the next char satisfy some condition.
#[derive(PartialEq, Debug, Clone)]
pub struct Predicate(pub PredicatePart, pub PredicatePart);

#[derive(PartialEq, Debug, Clone)]
pub struct PredicatePart {
    /// If this part is the first of the pair, `at_boundary == true` means that we can match the
    /// beginning of the input; otherwise, `at_boundary == true` means that we can match the end of
    /// the input.
    pub at_boundary: bool,

    /// The set of allowed chars (which will be applied to either the previous char or the next
    /// char, depending on whether we are the first or second in the pair).
    pub chars: CharSet,
}

impl PredicatePart {
    /// Returns a `PredicatePart` representing the intersection of this one and another one.
    pub fn intersect(&self, other: &PredicatePart) -> PredicatePart {
        PredicatePart {
            chars: self.chars.intersect(&other.chars),
            at_boundary: self.at_boundary && other.at_boundary,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.chars.is_empty() && !self.at_boundary
    }

    pub fn single_char(ch: char) -> PredicatePart {
        PredicatePart {
            chars: CharSet::single(ch as u32),
            at_boundary: false,
        }
    }

    pub fn or_at_boundary(self) -> PredicatePart {
        PredicatePart {
            chars: self.chars,
            at_boundary: true,
        }
    }

    pub fn full() -> PredicatePart {
        PredicatePart {
            chars: CharSet::full(),
            at_boundary: true,
        }
    }

    pub fn at_boundary() -> PredicatePart {
        PredicatePart {
            chars: CharSet::new(),
            at_boundary: true,
        }
    }

    // TODO: support unicode.
    // Probably the best way is to make `mod unicode` in regex::syntax public.
    fn word_chars() -> CharSet {
        let mut ret = CharSet::new();
        ret.push(CharRange::new('0' as u32, '9' as u32));
        ret.push(CharRange::new('A' as u32, 'Z' as u32));
        ret.push(CharRange::new('_' as u32, '_' as u32));
        ret.push(CharRange::new('a' as u32, 'z' as u32));
        ret
    }

    fn not_word_chars() -> CharSet {
        let mut ret = CharSet::new();
        ret.push(CharRange::new(0, '/' as u32));
        ret.push(CharRange::new(':' as u32, '@' as u32));
        ret.push(CharRange::new('[' as u32, '^' as u32));
        ret.push(CharRange::new('`' as u32, '`' as u32));
        ret.push(CharRange::new('{' as u32, std::u32::MAX));
        ret
    }

    pub fn word_char() -> PredicatePart {
        PredicatePart {
            chars: PredicatePart::word_chars(),
            at_boundary: false,
        }
    }

    pub fn not_word_char() -> PredicatePart {
        PredicatePart {
            chars: PredicatePart::not_word_chars(),
            at_boundary: true,
        }
    }
}

impl Predicate {
    /// Returns a predicate representing the intersection of this one and another one.
    ///
    /// If the intersection is empty, returns None.
    pub fn intersect(&self, other: &Predicate) -> Option<Predicate> {
        let first = self.0.intersect(&other.0);
        let second = self.1.intersect(&other.1);
        if first.is_empty() || second.is_empty() {
            None
        } else {
            Some(Predicate(first, second))
        }
    }

    pub fn filter_transitions(&self, in_trans: &CharMap<BitSet>, out_trans: &CharMap<BitSet>)
    -> (CharMap<BitSet>, CharMap<BitSet>) {
        let &Predicate(ref in_pred, ref out_pred) = self;
        (in_trans.intersect(&in_pred.chars), out_trans.intersect(&out_pred.chars))
    }

    /// Imagine that `self` is a predicate leading to a state with acceptance condition `acc`.
    /// Returns the effective acceptance condition of the predicate.
    pub fn filter_accept(&self, acc: Accept) -> Accept {
        let &Predicate(_, ref out_pred) = self;
        match acc {
            Accept::Always =>
                Accept::Conditionally {
                    at_eoi: out_pred.at_boundary,
                    at_char: out_pred.chars.clone(),
                },
            Accept::Never => Accept::Never,
            Accept::Conditionally { at_eoi, ref at_char } =>
                Accept::Conditionally {
                    at_eoi: out_pred.at_boundary && at_eoi,
                    at_char: out_pred.chars.intersect(at_char),
                }
        }
    }
}

/// We extend the "CS 101" automata by allowing the decision of whether a state accepts to depend
/// on what the next character is: we can either require the next character to be the end of the
/// input, or we can require it to belong to a specific set.
#[derive(Clone, Debug, Hash, PartialEq)]
pub enum Accept {
    Never,
    Always,
    Conditionally { at_eoi: bool, at_char: CharSet },
}

impl Eq for Accept {}

impl Accept {
    pub fn at_eoi() -> Accept {
        Accept::Conditionally {
            at_eoi: true,
            at_char: CharSet::new(),
        }
    }

    pub fn at_char(char_set: CharSet) -> Accept {
        Accept::Conditionally {
            at_eoi: false,
            at_char: char_set,
        }
    }

    pub fn accept_at_eoi(&self) -> bool {
        match self {
            &Accept::Always => { true },
            &Accept::Never => { false },
            &Accept::Conditionally { at_eoi, at_char: _ } => { at_eoi },
        }
    }

    /// Returns an `Accept` value that will accept if either `self` or `other` does.
    pub fn union(&self, other: &Accept) -> Accept {
        use transition::Accept::*;

        match self {
            &Never => { other.clone() },
            &Always => { Always },
            &Conditionally { at_eoi, ref at_char } => {
                match other {
                    &Never => { self.clone() },
                    &Always => { Always },
                    &Conditionally { at_eoi: other_at_eoi, at_char: ref other_at_char } => {
                        Conditionally {
                            at_eoi: at_eoi || other_at_eoi,
                            at_char: at_char.union(other_at_char),
                        }
                    }
                }
            }
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
        self.consuming.group()
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

