// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bit_set::BitSet;
use char_map::{CharMap, CharMultiMap, CharSet, CharRange};
use std::fmt::Debug;
use unicode::PERLW;

/// A predicate is a transition that doesn't consume any input, but that can only be traversed if
/// the previous char and the next char satisfy some condition.
#[derive(PartialEq, Debug, Clone)]
pub struct Predicate(pub PredicatePart, pub PredicatePart);

/// Half of a `Predicate`.
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

    /// Returns true if this `PredicatePart` always fails.
    pub fn is_empty(&self) -> bool {
        self.chars.is_empty() && !self.at_boundary
    }

    /// Creates a `PredicatePart` that matches a single char.
    pub fn single_char(ch: char) -> PredicatePart {
        PredicatePart {
            chars: CharSet::single(ch as u32),
            at_boundary: false,
        }
    }

    /// Returns a new `PredicatePart` that matches the same characters as this one, and always
    /// matches the beginning or end of input.
    pub fn or_at_boundary(self) -> PredicatePart {
        PredicatePart {
            chars: self.chars,
            at_boundary: true,
        }
    }

    /// Returns a new `PredicatePart` that always matches.
    pub fn full() -> PredicatePart {
        PredicatePart {
            chars: CharSet::full(),
            at_boundary: true,
        }
    }

    /// Returns a new `PredicatePart` that matches at the beginning or end of input.
    pub fn at_boundary() -> PredicatePart {
        PredicatePart {
            chars: CharSet::new(),
            at_boundary: true,
        }
    }

    /// Returns a new `CharSet` containing all word characters.
    fn word_chars() -> CharSet {
        let mut ret = CharSet::new();
        for &(start, end) in PERLW {
            ret.push(CharRange::new(start as u32, end as u32));
        }
        ret
    }

    /// Returns a new `CharSet` containing all non-word characters.
    fn not_word_chars() -> CharSet {
        let mut ret = CharSet::new();
        for &(start, end) in PERLW {
            ret.push(CharRange::new(start as u32, end as u32));
        }
        ret.negated()
    }

    /// Returns a new `PredicatePart` that matches all word characters.
    pub fn word_char() -> PredicatePart {
        PredicatePart {
            chars: PredicatePart::word_chars(),
            at_boundary: false,
        }
    }

    /// Returns a new `PredicatePart` that matches all non-word characters (or the boundary).
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

    /// Given transitions into and out of a state, return only those transitions satisfying this
    /// predicate.
    pub fn filter_transitions<T: Debug + PartialEq + Clone>
            (&self, in_trans: &CharMap<T>, out_trans: &CharMap<T>)
            -> (CharMap<T>, CharMap<T>)
    {
        let &Predicate(ref in_pred, ref out_pred) = self;
        (in_trans.intersect(&in_pred.chars), out_trans.intersect(&out_pred.chars))
    }

    /// Imagine that `self` is a predicate leading to a state with acceptance condition `acc`.
    /// Returns the effective acceptance condition of the predicate.
    pub fn filter_accept(&self, acc: &Accept) -> Accept {
        let out_pred = &self.1;
        let ret = match acc {
            &Accept::Always =>
                Accept::Conditionally {
                    at_eoi: out_pred.at_boundary,
                    at_char: out_pred.chars.clone(),
                },
            &Accept::Never => Accept::Never,
            &Accept::Conditionally { at_eoi, ref at_char } =>
                Accept::Conditionally {
                    at_eoi: out_pred.at_boundary && at_eoi,
                    at_char: out_pred.chars.intersect(at_char),
                }
        };
        ret.normalize()
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

    pub fn normalize(self) -> Accept {
        if let Accept::Conditionally { at_eoi, ref at_char } = self {
            if !at_eoi && at_char.is_empty() {
                return Accept::Never;
            } else if at_eoi && at_char.is_full(){
                return Accept::Always;
            }
        }
        self
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
    use char_map::*;
    use transition::*;

    #[test]
    fn test_predicate_part_intersect() {
        let wc = PredicatePart::word_char();
        let nwc = PredicatePart::not_word_char();
        let bdy = PredicatePart::at_boundary();
        let full = PredicatePart::full();
        let a = PredicatePart::single_char('a');
        let empty = PredicatePart {
            at_boundary: false,
            chars: CharSet::new(),
        };

        let check = |a: &PredicatePart, b: &PredicatePart, res: &PredicatePart| {
            assert_eq!(a.intersect(b), *res);
            assert_eq!(b.intersect(a), *res);
        };
        check(&wc, &nwc, &empty);
        check(&wc, &bdy, &empty);
        check(&nwc, &bdy, &bdy);
        check(&a, &bdy, &empty);
        check(&wc, &a, &a);
        check(&nwc, &a, &empty);
        check(&wc, &full, &wc);
        check(&nwc, &full, &nwc);
        check(&bdy, &full, &bdy);
        check(&wc.or_at_boundary(), &bdy, &bdy);
    }

    #[test]
    fn test_filter_transitions() {
        let wc = PredicatePart::word_char();
        let nwc = PredicatePart::not_word_char();
        let bdy = PredicatePart::at_boundary();
        let full = PredicatePart::full();
        let a = PredicatePart::single_char('a');
        let empty = PredicatePart {
            at_boundary: false,
            chars: CharSet::new(),
        };

        let cm_empty = CharMap::new();
        let cm_az = CharMap::from_vec(vec![(CharRange::new('a' as u32, 'z' as u32), 1usize)]);
        let cm_a = CharMap::from_vec(vec![(CharRange::new('a' as u32, 'a' as u32), 1usize)]);

        let check = |a: &PredicatePart, b: &CharMap<usize>, res: &CharMap<usize>| {
            assert_eq!(Predicate(a.clone(), a.clone()).filter_transitions(b, b),
                (res.clone(), res.clone()));
        };
        check(&wc, &cm_empty, &cm_empty);
        check(&wc, &cm_az, &cm_az);
        check(&nwc, &cm_empty, &cm_empty);
        check(&nwc, &cm_az, &cm_empty);
        check(&bdy, &cm_empty, &cm_empty);
        check(&bdy, &cm_az, &cm_empty);
        check(&empty, &cm_empty, &cm_empty);
        check(&empty, &cm_az, &cm_empty);
        check(&full, &cm_empty, &cm_empty);
        check(&full, &cm_az, &cm_az);
        check(&a, &cm_empty, &cm_empty);
        check(&a, &cm_az, &cm_a);
    }

    #[test]
    fn test_filter_accept() {
        let e = PredicatePart {
            at_boundary: false,
            chars: CharSet::new(),
        };
        let a = PredicatePart::single_char('a');
        let full = PredicatePart::full();
        let bdy = PredicatePart::at_boundary();

        let acc_eoi = Accept::at_eoi();
        let acc_a = Accept::at_char(CharSet::single('a' as u32));

        assert_eq!(Predicate(e.clone(), e.clone()).filter_accept(&acc_eoi), Accept::Never);
        assert_eq!(Predicate(e.clone(), e.clone()).filter_accept(&acc_a), Accept::Never);
        assert_eq!(Predicate(e.clone(), e.clone()).filter_accept(&Accept::Never), Accept::Never);
        assert_eq!(Predicate(e.clone(), e.clone()).filter_accept(&Accept::Always), Accept::Never);

        assert_eq!(Predicate(e.clone(), a.clone()).filter_accept(&acc_eoi), Accept::Never);
        assert_eq!(Predicate(e.clone(), a.clone()).filter_accept(&acc_a), acc_a);
        assert_eq!(Predicate(e.clone(), a.clone()).filter_accept(&Accept::Never), Accept::Never);
        assert_eq!(Predicate(e.clone(), a.clone()).filter_accept(&Accept::Always), acc_a);

        assert_eq!(Predicate(e.clone(), full.clone()).filter_accept(&acc_eoi), acc_eoi);
        assert_eq!(Predicate(e.clone(), full.clone()).filter_accept(&acc_a), acc_a);
        assert_eq!(Predicate(e.clone(), full.clone()).filter_accept(&Accept::Never),
            Accept::Never);
        assert_eq!(Predicate(e.clone(), full.clone()).filter_accept(&Accept::Always),
            Accept::Always);

        assert_eq!(Predicate(e.clone(), bdy.clone()).filter_accept(&acc_eoi), acc_eoi);
        assert_eq!(Predicate(e.clone(), bdy.clone()).filter_accept(&acc_a), Accept::Never);
        assert_eq!(Predicate(e.clone(), bdy.clone()).filter_accept(&Accept::Never), Accept::Never);
        assert_eq!(Predicate(e.clone(), bdy.clone()).filter_accept(&Accept::Always), acc_eoi);
    }

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
}

