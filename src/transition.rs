// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use range_map::{Range, RangeMap, RangeMultiMap, RangeSet};
use std::fmt::Debug;
use unicode::PERLW;

/// How we represent a set of states. The two important criteria are:
///
/// - it should be reasonably fast even when there are thousands of states (this knocks out
///   BitSet), and
/// - it should be hashable (this knocks out HashSet).
///
/// Note that efficient insertion and O(1) queries are not important. Therefore, we use a sorted
/// Vec. (But be careful to keep it sorted!)
pub type StateSet = Vec<usize>;

pub trait SetOps {
    fn union_with(&mut self, other: &Self);
    fn intersect_with(&mut self, other: &Self);
    fn is_disjoint(&self, other: &Self) -> bool;
}

impl SetOps for StateSet {
    fn union_with(&mut self, other: &StateSet) {
        self.extend(other);
        self.sort();
    }

    fn intersect_with(&mut self, other: &Self) {
        let mut write_idx = 0;
        let mut read_idx = 0;

        for &x in other {
            while read_idx < self.len() && self[read_idx] < x {
                read_idx += 1;
            }
            if read_idx < self.len() && self[read_idx] == x {
                self[write_idx] = self[read_idx];
                write_idx += 1;
                read_idx += 1;
            }
        }

        self.truncate(write_idx);
    }

    fn is_disjoint(&self, other: &StateSet) -> bool {
        let mut my_iter = self.iter().peekable();
        let mut other_iter = other.iter();

        while let Some(&x) = other_iter.next() {
            while let Some(&&y) = my_iter.peek() {
                if y == x {
                    return false;
                } else if y > x {
                    break;
                }
                my_iter.next();
            }
        }
        true
    }
}

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
    pub chars: RangeSet<u32>,
}

impl PredicatePart {
    /// Returns a `PredicatePart` representing the intersection of this one and another one.
    pub fn intersect(&self, other: &PredicatePart) -> PredicatePart {
        PredicatePart {
            chars: self.chars.intersection(&other.chars),
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
            chars: RangeSet::single(ch as u32),
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
            chars: RangeSet::full(),
            at_boundary: true,
        }
    }

    /// Returns a new `PredicatePart` that matches at the beginning or end of input.
    pub fn at_boundary() -> PredicatePart {
        PredicatePart {
            chars: RangeSet::new(),
            at_boundary: true,
        }
    }

    /// Returns a new `RangeSet` containing all word characters.
    fn word_chars() -> RangeSet<u32> {
        PERLW.iter().map(|pair| Range::new(pair.0 as u32, pair.1 as u32)).collect()
    }

    /// Returns a new `RangeSet` containing all non-word characters.
    fn not_word_chars() -> RangeSet<u32> {
        PredicatePart::word_chars().negated()
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
    pub fn filter_transitions<T: Debug + Eq + Clone>
            (&self, in_trans: &RangeMap<u32, T>, out_trans: &RangeMap<u32, T>)
            -> (RangeMap<u32, T>, RangeMap<u32, T>)
    {
        let &Predicate(ref in_pred, ref out_pred) = self;
        (in_trans.intersection(&in_pred.chars), out_trans.intersection(&out_pred.chars))
    }

    /// Imagine that `self` is a predicate leading to a state with acceptance condition `acc`.
    /// Returns the effective acceptance condition of the predicate.
    pub fn filter_accept(&self, acc: &Accept) -> Accept {
        Accept {
            at_eoi: self.1.at_boundary && acc.at_eoi,
            at_char: self.1.chars.intersection(&acc.at_char),
        }
    }
}

/// We extend the "CS 101" automata by allowing the decision of whether a state accepts to depend
/// on what the next character is: we can either require the next character to be the end of the
/// input, or we can require it to belong to a specific set.
#[derive(Clone, Debug, Hash, PartialEq)]
pub struct Accept {
    pub at_eoi: bool,
    pub at_char: RangeSet<u32>,
}

impl Eq for Accept {}

impl Accept {
    /// Returns a new `Accept` that always accepts.
    pub fn always() -> Accept {
        Accept {
            at_eoi: true,
            at_char: RangeSet::full(),
        }
    }

    /// Returns a new `Accept` that never accepts.
    pub fn never() -> Accept {
        Accept {
            at_eoi: false,
            at_char: RangeSet::new(),
        }
    }

    /// Returns true if this never accepts.
    pub fn is_never(&self) -> bool {
        !self.at_eoi && self.at_char.is_empty()
    }

    /// Returns true if this always accepts.
    pub fn is_always(&self) -> bool {
        self.at_eoi && self.at_char.is_full()
    }

    /// Returns an `Accept` value that will accept if either `self` or `other` does.
    pub fn union(&self, other: &Accept) -> Accept {
        Accept {
            at_eoi: self.at_eoi || other.at_eoi,
            at_char: self.at_char.union(&other.at_char),
        }
    }
}


#[derive(Clone, PartialEq, Debug)]
pub struct NfaTransitions {
    /// Transitions that consume input.
    pub consuming: RangeMultiMap<u32, usize>,
    /// Unconditional transitions that don't consume any input.
    pub eps: Vec<usize>,
    /// Conditional transitions that don't consume any input.
    pub predicates: Vec<(Predicate, usize)>,
}

impl NfaTransitions {
    pub fn new() -> NfaTransitions {
        NfaTransitions {
            consuming: RangeMultiMap::new(),
            eps: Vec::new(),
            predicates: Vec::new(),
        }
    }

    pub fn map_targets<F>(&mut self, mut f: F) where F: FnMut(usize) -> usize {
        fn map_vec<T, F>(v: &mut Vec<T>, mut f: F) where F: FnMut(&mut T) {
            for i in 0..v.len() {
                f(&mut v[i]);
            }
        }

        map_vec(&mut self.predicates, |x| { x.1 = f(x.1); });
        map_vec(&mut self.eps, |x| { *x = f(*x); });
        self.consuming.map_values(|x| f(*x));
    }

    pub fn retain_targets<F>(&mut self, mut f: F) where F: FnMut(usize) -> bool {
        self.predicates.retain(|x| f(x.1));
        self.eps.retain(|x| f(*x));
        self.consuming.retain_values(|x| f(*x));
    }

    pub fn filter_map_targets<F>(&mut self, mut f: F) where F: FnMut(usize) -> Option<usize> {
        self.retain_targets(|x| f(x).is_some());
        self.map_targets(|x| f(x).unwrap());
    }
}

#[cfg(test)]
mod tests {
    use range_map::{Range, RangeMap, RangeSet};
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
            chars: RangeSet::new(),
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
            chars: RangeSet::new(),
        };

        let cm_empty = RangeMap::new();
        let cm_az: RangeMap<u32, usize> =
            [(Range::new('a' as u32, 'z' as u32), 1usize)].iter().cloned().collect();
        let cm_a: RangeMap<u32, usize> =
            [(Range::new('a' as u32, 'a' as u32), 1usize)].iter().cloned().collect();

        let check = |a: &PredicatePart, b: &RangeMap<u32, usize>, res: &RangeMap<u32, usize>| {
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
            chars: RangeSet::new(),
        };
        let a = PredicatePart::single_char('a');
        let full = PredicatePart::full();
        let bdy = PredicatePart::at_boundary();

        let acc_eoi = Accept { at_eoi: true, at_char: RangeSet::new() };
        let acc_a = Accept { at_eoi: false, at_char: RangeSet::single('a' as u32) };
        let always = Accept::always();
        let never = Accept::never();

        assert_eq!(Predicate(e.clone(), e.clone()).filter_accept(&acc_eoi), never);
        assert_eq!(Predicate(e.clone(), e.clone()).filter_accept(&acc_a), never);
        assert_eq!(Predicate(e.clone(), e.clone()).filter_accept(&never), never);
        assert_eq!(Predicate(e.clone(), e.clone()).filter_accept(&always), never);

        assert_eq!(Predicate(e.clone(), a.clone()).filter_accept(&acc_eoi), never);
        assert_eq!(Predicate(e.clone(), a.clone()).filter_accept(&acc_a), acc_a);
        assert_eq!(Predicate(e.clone(), a.clone()).filter_accept(&never), never);
        assert_eq!(Predicate(e.clone(), a.clone()).filter_accept(&always), acc_a);

        assert_eq!(Predicate(e.clone(), full.clone()).filter_accept(&acc_eoi), acc_eoi);
        assert_eq!(Predicate(e.clone(), full.clone()).filter_accept(&acc_a), acc_a);
        assert_eq!(Predicate(e.clone(), full.clone()).filter_accept(&never), never);
        assert_eq!(Predicate(e.clone(), full.clone()).filter_accept(&always), always);

        assert_eq!(Predicate(e.clone(), bdy.clone()).filter_accept(&acc_eoi), acc_eoi);
        assert_eq!(Predicate(e.clone(), bdy.clone()).filter_accept(&acc_a), never);
        assert_eq!(Predicate(e.clone(), bdy.clone()).filter_accept(&never), never);
        assert_eq!(Predicate(e.clone(), bdy.clone()).filter_accept(&always), acc_eoi);
    }

    #[test]
    fn test_union() {
        let acc_eoi = Accept { at_eoi: true, at_char: RangeSet::new() };
        let always = Accept::always();
        let never = Accept::never();

        assert_eq!(Accept::never().union(&always), always);
        assert_eq!(Accept::never().union(&never), never);
        assert_eq!(Accept::never().union(&acc_eoi), acc_eoi);
        assert_eq!(Accept::always().union(&acc_eoi), always);

        let acc_a = Accept { at_eoi: false, at_char: RangeSet::single('a' as u32) };
        let acc_b = Accept { at_eoi: false, at_char: RangeSet::single('b' as u32) };
        let acc_ab = Accept {
            at_eoi: false,
            at_char: [Range::new('a' as u32, 'b' as u32)].iter().cloned().collect(),
        };
        assert_eq!(acc_a.union(&acc_b), acc_ab);
        assert_eq!(acc_a.union(&Accept::never()), acc_a);
        assert_eq!(acc_a.union(&Accept::always()), always);
    }
}

