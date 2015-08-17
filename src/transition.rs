// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bit_set::BitSet;
use std;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::ops::Deref;
use std::u32;

/// A range of symbols, including the endpoints.
///
/// If `from` is strictly larger than `to` then this represents an empty range.
#[derive(PartialEq, Debug, Copy, Clone, Hash)]
pub struct SymbRange {
    pub from: u32,
    pub to: u32,
}

impl Eq for SymbRange {}

impl SymbRange {
    pub fn new(from: u32, to: u32) -> SymbRange {
        SymbRange {
            from: from,
            to: to,
        }
    }

    pub fn single(symb: u32) -> SymbRange {
        SymbRange::new(symb, symb)
    }

    pub fn contains(&self, symb: u32) -> bool {
        self.from <= symb && symb <= self.to
    }

    pub fn intersection(&self, other: &SymbRange) -> SymbRange {
        SymbRange::new(std::cmp::max(self.from, other.from), std::cmp::min(self.to, other.to))
    }
}

impl PartialOrd for SymbRange {
    fn partial_cmp(&self, other: &SymbRange) -> Option<Ordering> {
        if self.from < other.from {
            Some(Ordering::Less)
        } else if self.from > other.from {
            Some(Ordering::Greater)
        } else {
            self.to.partial_cmp(&other.to)
        }
    }
}

// Assumes the two ranges are sorted and non-overlapping.
// TODO: there are a lot of utility functions for SymbRange -- collect them in a newtype somewhere.
fn symb_ranges_intersect(rs: &Vec<SymbRange>, ss: &Vec<SymbRange>) -> Vec<SymbRange> {
    use std::cmp::{max, min};

    let mut ret = Vec::new();
    let mut ss_slice: &[SymbRange] = &ss;

    for &r in rs {
        while !ss_slice.is_empty() {
            let (s, ss_tail) = ss_slice.split_first().unwrap();
            if s.to >= r.from && s.from <= r.to {
                ret.push(SymbRange::new(max(s.from, r.from), min(s.to, r.to)));
            }
            if s.to >= r.to {
                break;
            } else {
                ss_slice = ss_tail;
            }
        }
    }

    ret
}

/// A predicate is a transition that doesn't consume any input, but that can only be traversed if
/// the previous char and the next char satisfy some condition.
#[derive(PartialEq, Debug, Clone)]
pub enum Predicate {
    /// This predicate succeeeds if the previous character is in the first class and the next
    /// character is in the second class.
    InClasses(Vec<SymbRange>, Vec<SymbRange>),
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
                    let in_ranges = symb_ranges_intersect(my_in, other_in);
                    let out_ranges = symb_ranges_intersect(my_out, other_out);
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

    // mine is sorted, other is not necessarily.
    fn filter_one<T: Clone>(mine: &Vec<SymbRange>, other: &Vec<(SymbRange, T)>)
        -> Vec<(SymbRange, T)> {

        let mut ret = Vec::new();
        for &(ref his_range, ref target) in other {
            // TODO: use binary search to get the starting range.
            for my_range in mine {
                if my_range.from > his_range.to {
                    break;
                } else if my_range.to >= his_range.from {
                    ret.push((SymbRange::intersection(my_range, his_range), target.clone()));
                }
            }
        }
        ret
    }

    pub fn filter_transitions<T: Clone>(&self,
                              in_trans: &Vec<(SymbRange, T)>,
                              out_trans: &Vec<(SymbRange, T)>)
        -> (Vec<(SymbRange, T)>, Vec<(SymbRange, T)>) {

        use transition::Predicate::*;
        if let &InClasses(ref my_in, ref my_out) = self {
            (Predicate::filter_one(my_in, in_trans), Predicate::filter_one(my_out, out_trans))
        } else {
            (vec![], vec![])
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct NfaTransitions {
    /// Transitions that consume input.
    pub ranges: Vec<(SymbRange, usize)>,
    /// Unconditional transitions that don't consume any input.
    pub eps: Vec<usize>,
    /// Conditional transitions that don't consume any input.
    pub predicates: Vec<(Predicate, usize)>,
}

impl NfaTransitions {
    pub fn new() -> NfaTransitions {
        NfaTransitions {
            ranges: Vec::new(),
            eps: Vec::new(),
            predicates: Vec::new(),
        }
    }

    pub fn from_vec(vec: Vec<(SymbRange, usize)>) -> NfaTransitions {
        NfaTransitions {
            ranges: vec,
            eps: Vec::new(),
            predicates: Vec::new(),
        }
    }

    /// Collects transitions with the same symbol range.
    ///
    /// For every unique SymbRange that appears in `trans`, adds an extra
    /// element to the returned vector. That element is a pair whose first
    /// component is the SymbRange and whose second component
    /// is a set containing all the indices of states associated with
    /// that SymbRange.
    pub fn collect_transition_pairs(self) -> Vec<(SymbRange, BitSet)> {
        let mut map = HashMap::<SymbRange, BitSet>::new();
        for (range, state) in self.split_transitions().ranges.into_iter() {
            map.entry(range).or_insert(BitSet::new()).insert(state);
        }

        map.into_iter().collect()
    }

    /// Like collect_transition_pairs, but without the SymbRanges.
    pub fn collect_transitions(self) -> Vec<BitSet> {
        self.collect_transition_pairs().into_iter().map(|x| x.1).collect()
    }

    /// Splits a set of transitions into equal or disjoint transitions.
    ///
    /// The output is a list of transitions in which every pair of transitions
    /// either have identical SymbRanges or disjoint SymbRanges.
    fn split_transitions(&self) -> NfaTransitions {
        let mut ret = NfaTransitions::new();
        let mut start_symbs = Vec::new();

        for &(ref range, _) in self.ranges.iter() {
            start_symbs.push(range.from);
            if range.to < u32::MAX {
                start_symbs.push(range.to + 1u32);
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
                    ret.ranges.push((SymbRange::new(last, start_symbs[idx] - 1u32), *state));
                    last = start_symbs[idx];
                    idx += 1;
                }
            }
        }

        ret
    }

    /* TODO: needed?
    /// Returns the complement of this transition list.
    ///
    /// This assumes that the transition list is sorted and that
    /// every range has the same target state.
    pub fn negated(&self) -> NfaTransitions {
        let mut ret = NfaTransitions::new();
        let state = self.ranges[0].1;
        let mut last = 0u32;

        for &(ref range, _) in self.ranges.iter() {
            if range.from > last {
                ret.ranges.push((SymbRange::new(last, range.from - 1u32), state));
            }
            last = range.to + 1u32;
        }
        if last < u32::MAX {
            ret.ranges.push((SymbRange::new(last, u32::MAX), state));
        }

        ret
    }
    */
}

#[derive(PartialEq, Debug)]
pub struct DfaTransitions {
    ranges: Vec<(SymbRange, usize)>,
}

impl DfaTransitions {
    pub fn new() -> DfaTransitions {
        DfaTransitions {
            ranges: Vec::new(),
        }
    }

    pub fn sort(&mut self) {
        self.ranges.sort_by(|&(r1, _), &(r2, _)| r1.from.cmp(&r2.from));
    }

    pub fn add(&mut self, range: SymbRange, tgt: usize) {
        self.ranges.push((range, tgt));
    }

    /// If this transition accepts only a single char, return it
    /// and the target state.
    pub fn only_valid_char(&self) -> Option<(u32, usize)> {
        if self.ranges.len() == 1 {
            let r = self.ranges[0].0;
            if r.from == r.to {
                Some((r.from, self.ranges[0].1))
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn find_transition(&self, ch: u32) -> Option<usize> {
        match self.ranges[..].binary_search_by(|&(r, _)| r.from.cmp(&ch)) {
            Ok(idx) => { Some(self.ranges[idx].1) },
            Err(idx) => {
                if idx > 0 && self.ranges[idx-1].0.contains(ch) {
                    Some(self.ranges[idx - 1].1)
                } else {
                    None
                }
            },
        }

    }
}

impl Deref for DfaTransitions {
    type Target = Vec<(SymbRange, usize)>;

    fn deref(&self) -> &Vec<(SymbRange, usize)> { &self.ranges }
}

#[cfg(test)]
mod tests {
    use bit_set::BitSet;
    use transition::*;

    #[test]
    fn test_collect_transitions() {
        let trans = NfaTransitions::from_vec(vec![
            (SymbRange::new(0, 2), 0),
            (SymbRange::new(4, 5), 2),
            (SymbRange::new(0, 2), 2),
            (SymbRange::new(3, 3), 1),
            (SymbRange::new(4, 5), 1),
        ]);
        let mut sets = trans.collect_transitions();
        sets.sort();

        assert_eq!(sets, vec![
            BitSet::from_bytes(&[0b10100000]),
            BitSet::from_bytes(&[0b01000000]),
            BitSet::from_bytes(&[0b01100000]),
        ]);
    }

    #[test]
    fn test_split_transitions() {
        let trans = NfaTransitions::from_vec(vec![
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

    fn from_vec(vec: Vec<(SymbRange, usize)>) -> DfaTransitions {
        DfaTransitions {
            ranges: vec,
        }
    }

    #[test]
    fn test_find_transition() {
        let trans = from_vec(vec![
            (SymbRange::new(1, 1), 10),
            (SymbRange::new(3, 3), 11),
            (SymbRange::new(5, 7), 12),
            (SymbRange::new(9, 9), 13),
        ]);
        assert_eq!(trans.find_transition(1), Some(10));
        assert_eq!(trans.find_transition(3), Some(11));
        assert_eq!(trans.find_transition(5), Some(12));
        assert_eq!(trans.find_transition(6), Some(12));
        assert_eq!(trans.find_transition(9), Some(13));
        assert_eq!(trans.find_transition(0), None);
        assert_eq!(trans.find_transition(2), None);
        assert_eq!(trans.find_transition(4), None);
        assert_eq!(trans.find_transition(77), None);
    }

    #[test]
    fn test_only_valid_char() {
        let t1 = from_vec(vec![(SymbRange::new(5, 5), 7)]);
        let t2 = from_vec(vec![(SymbRange::new(5, 6), 7)]);
        let t3 = from_vec(vec![(SymbRange::new(5, 5), 7), (SymbRange::new(6, 6), 8)]);
        assert_eq!(t1.only_valid_char(), Some((5, 7)));
        assert_eq!(t2.only_valid_char(), None);
        assert_eq!(t3.only_valid_char(), None);
    }
}

