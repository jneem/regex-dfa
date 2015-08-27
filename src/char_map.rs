// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bit_set::BitSet;
use regex_syntax;
use std;
use std::collections::HashMap;
use std::cmp::Ordering;
use std::hash::Hash;
use std::fmt::Debug;
use std::ops::Deref;

/// A range of code points, including the endpoints.
///
/// If `from` is strictly larger than `to` then this represents an empty range.
#[derive(PartialEq, Debug, Copy, Clone, Hash)]
pub struct CharRange {
    pub start: u32,
    pub end: u32,
}

impl Eq for CharRange {}

impl CharRange {
    pub fn new(start: u32, end: u32) -> CharRange {
        CharRange { start: start, end: end }
    }

    pub fn single(ch: u32) -> CharRange {
        CharRange::new(ch, ch)
    }

    pub fn contains(&self, ch: u32) -> bool {
        self.start <= ch && ch <= self.end
    }

    pub fn intersection(&self, other: &CharRange) -> CharRange {
        CharRange::new(std::cmp::max(self.start, other.start), std::cmp::min(self.end, other.end))
    }

    pub fn is_empty(&self) -> bool {
        self.start > self.end
    }
}

impl PartialOrd for CharRange {
    fn partial_cmp(&self, other: &CharRange) -> Option<Ordering> {
        if self.start < other.start {
            Some(Ordering::Less)
        } else if self.start > other.start {
            Some(Ordering::Greater)
        } else {
            self.end.partial_cmp(&other.end)
        }
    }
}

/// A set of characters. Optionally, each character in the set may be associated with some data.
#[derive(PartialEq, Debug, Clone, Hash)]
pub struct CharMap<T: Clone + Debug + PartialEq> {
    elts: Vec<(CharRange, T)>,
    sorted: bool,
}

impl<T: Clone + Debug + PartialEq> IntoIterator for CharMap<T> {
    type Item = (CharRange, T);
    type IntoIter = std::vec::IntoIter<(CharRange, T)>;
    fn into_iter(self) -> Self::IntoIter {
        self.elts.into_iter()
    }
}

impl<T: Clone + Debug + PartialEq> CharMap<T> {
    pub fn new() -> CharMap<T> {
        CharMap {
            elts: Vec::new(),
            sorted: true,
        }
    }

    /// Creates a `CharMap` from a `Vec`, which is assumed to contain non-overlapping ranges in
    /// ascending order.
    pub fn from_vec(vec: Vec<(CharRange, T)>) -> CharMap<T> {
        CharMap {
            elts: vec,
            sorted: true,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.elts.is_empty()
    }

    /// Maps the given range of characters to to the given value.
    ///
    /// Panics if the range is empty.
    pub fn push(&mut self, range: CharRange, t: &T) {
        if range.is_empty() {
            panic!("ranges must be non-empty");
        }
        if let Some(&(ref last_range, _)) = self.elts.last() {
            if last_range.end >= range.start {
                self.sorted = false;
            }
        }
        self.elts.push((range, t.clone()));
    }

    /// Sorts the ranges. Panics if any ranges overlap.
    pub fn sort(&mut self) {
        self.elts.sort_by(|&(r1, _), &(r2, _)| r1.start.cmp(&r2.start));
        self.sorted = true;
        for win in self.elts.windows(2) {
            if win[0].0.end >= win[1].0.start {
                panic!("overlapping ranges");
            }
        }
    }

    /// Returns the data corresponding to a char. This `CharMap` must be sorted before calling
    /// `get`.
    ///
    /// Panics if we are not sorted.
    pub fn get(&self, ch: u32) -> Option<&T> {
        if !self.sorted {
            panic!("tried to get something from an unsorted CharMap");
        }
        match self.elts[..].binary_search_by(|&(r, _)| r.start.cmp(&ch)) {
            Ok(idx) => { Some(&self.elts[idx].1) },
            Err(idx) => {
                if idx > 0 && self.elts[idx-1].0.contains(ch) {
                    Some(&self.elts[idx - 1].1)
                } else {
                    None
                }
            },
        }
    }

    pub fn intersect(&self, other: &CharSet) -> CharMap<T> {
        use std::cmp::{max, min};
        let mut ret = Vec::new();
        let mut other: &[(CharRange, ())] = &other.map.elts;

        for &(ref r, ref data) in &self.elts {
            while !other.is_empty() {
                let (&(ref s, _), tail) = other.split_first().unwrap();
                if s.end >= r.start && s.start <= r.end {
                    let new_range = CharRange::new(max(s.start, r.start), min(s.end, r.end));
                    ret.push((new_range, data.clone()));
                }
                if s.end >= r.end {
                    break;
                } else {
                    other = tail;
                }
            }
        }

        CharMap::from_vec(ret)
    }
}

impl<T: Copy + Debug + PartialEq + 'static> CharMap<T> {
    pub fn extend<'a, I>(&mut self, iter: I) where I: IntoIterator<Item=&'a (CharRange, T)> {
        self.elts.extend(iter)
    }
}

impl<T: Clone + Debug + PartialEq> Deref for CharMap<T> {
    type Target = Vec<(CharRange, T)>;
    fn deref(&self) -> &Self::Target {
        &self.elts
    }
}

#[derive(PartialEq, Debug, Clone, Hash)]
pub struct CharSet {
    map: CharMap<()>,
}

impl<'a> IntoIterator for &'a CharSet {
    type Item = &'a CharRange;

    // TODO: change this, if we get abstract return types
    type IntoIter = Box<std::iter::Iterator<Item=&'a CharRange> + 'a>;
    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.map.elts.iter().map(|x| &x.0))
    }
}

impl CharSet {
    pub fn new() -> CharSet {
        CharSet { map: CharMap::new() }
    }

    pub fn sort(&mut self) {
        self.map.sort();
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    fn from_vec(vec: Vec<(CharRange, ())>) -> CharSet {
        let mut ret = CharSet { map: CharMap { elts: vec, sorted: false } };
        ret.sort();
        ret
    }

    /// Coverts a `regex_syntax::CharClass` into a `CharSet`.
    pub fn from_char_class(cc: &regex_syntax::CharClass) -> CharSet {
        let mut ret = Vec::with_capacity(cc.len());
        for range in cc {
            ret.push((CharRange::new(range.start as u32, range.end as u32), ()))
        }
        CharSet::from_vec(ret)
    }

    /// Creates a `CharSet` containing every codepoint.
    pub fn full() -> CharSet {
        CharSet::from_vec(vec![(CharRange::new(0, std::u32::MAX), ())])
    }

    /// Creates a `CharSet` containing a single codepoint.
    pub fn single(ch: u32) -> CharSet {
        CharSet::from_vec(vec![(CharRange::single(ch), ())])
    }

    /// Creates a `CharSet` containing all codepoints except the given ones.
    ///
    /// Panics if `chars` is not sorted or not unique.
    pub fn except(chars: &str) -> CharSet {
        let mut ret = Vec::with_capacity(chars.len());
        let mut next_allowed = 0u32;
        for c in chars.chars() {
            let n = c as u32;
            if n > next_allowed {
                ret.push((CharRange::new(next_allowed, n - 1), ()));
            } else if n < next_allowed {
                panic!("input to CharSet::except must be sorted");
            }
            next_allowed = n + 1;
        }

        CharSet::from_vec(ret)
    }

    pub fn intersect(&self, other: &CharSet) -> CharSet {
        CharSet { map: self.map.intersect(other) }
    }

    /// Checks if the given character is contained in this set.
    pub fn contains(&self, ch: u32) -> bool {
        self.map.get(ch) == Some(&())
    }

    /// Adds the given range of characters to this set. The range must be non-empty.
    ///
    /// Panics if the range is empty.
    pub fn push(&mut self, r: CharRange) {
        self.map.push(r, &());
    }
}

#[derive(Debug, Hash, PartialEq)]
pub struct CharMultiMap<T: Clone + Debug + Hash + PartialEq> {
    elts: Vec<(CharRange, T)>,
}

impl<T: Clone + Debug + Hash + PartialEq> IntoIterator for CharMultiMap<T> {
    type Item = (CharRange, T);
    type IntoIter = std::vec::IntoIter<(CharRange, T)>;
    fn into_iter(self) -> Self::IntoIter {
        self.elts.into_iter()
    }
}

impl<T: Clone + Debug + Hash + PartialEq> CharMultiMap<T> {
    pub fn new() -> CharMultiMap<T> {
        CharMultiMap { elts: Vec::new() }
    }

    pub fn add(&mut self, range: CharRange, data: &T) {
        self.elts.push((range, data.clone()));
    }

    pub fn from_vec(vec: Vec<(CharRange, T)>) -> CharMultiMap<T> {
        CharMultiMap { elts: vec }
    }

    /// Returns a new `CharMultiMap` containing only the mappings for chars that belong to the
    /// given set.
    pub fn intersect(&self, other: &CharSet) -> CharMultiMap<T> {
        let mut ret = Vec::new();
        for &(ref my_range, ref data) in &self.elts {
            // TODO: use binary search to get the starting range.
            for &(ref other_range, _) in &other.map.elts {
                if my_range.start > other_range.end {
                    break;
                } else if my_range.end >= other_range.start {
                    ret.push((CharRange::intersection(my_range, other_range), data.clone()));
                }
            }
        }
        CharMultiMap { elts: ret }
    }

    /// Splits the set of ranges into equal or disjoint ranges.
    ///
    /// The output is a `CharMultiMap` list of transitions in which every pair of `CharRange`s
    /// are either identical or disjoint.
    fn split(&self) -> CharMultiMap<T> {
        let mut ret = CharMultiMap::new();
        let mut start_chars = Vec::new();

        for &(ref range, _) in self.elts.iter() {
            start_chars.push(range.start);
            if range.end < std::u32::MAX {
                start_chars.push(range.end + 1u32);
            }
        }

        start_chars.sort();
        start_chars.dedup();

        for &(range, ref state) in self.elts.iter() {
            let mut idx = match start_chars.binary_search(&range.start) {
                Ok(i) => i+1,
                Err(i) => i,
            };
            let mut last = range.start;
            loop {
                if idx >= start_chars.len() || start_chars[idx] > range.end {
                    ret.elts.push((CharRange::new(last, range.end), state.clone()));
                    break;
                } else {
                    ret.elts.push((CharRange::new(last, start_chars[idx] - 1u32), state.clone()));
                    last = start_chars[idx];
                    idx += 1;
                }
            }
        }

        ret
    }
}

impl CharMultiMap<usize> {
    /// Makes the ranges sorted and non-overlapping. The data associated with each range will
    /// be a set of `usize`s instead of a single `usize`.
    pub fn group(&self) -> CharMap<BitSet> {
        let mut map = HashMap::<CharRange, BitSet>::new();
        for (range, state) in self.split().elts.into_iter() {
            map.entry(range).or_insert(BitSet::new()).insert(state);
        }

        let mut vec: Vec<(CharRange, BitSet)> = map.into_iter().collect();
        vec.sort_by(|&(r1, _), &(r2, _)| r1.start.cmp(&r2.start));
        CharMap { elts: vec, sorted: true }
    }
}

impl<T: Clone + Debug + Hash + PartialEq> Deref for CharMultiMap<T> {
    type Target = Vec<(CharRange, T)>;
    fn deref(&self) -> &Self::Target {
        &self.elts
    }
}

impl<T: Copy + Debug + Hash + PartialEq + 'static> CharMultiMap<T> {
    pub fn extend<'a, I>(&mut self, iter: I) where I: IntoIterator<Item=&'a (CharRange, T)> {
        self.elts.extend(iter)
    }
}

#[cfg(test)]
mod tests {
    use char_map::*;

    #[test]
    fn test_get() {
        let mut cm = CharMap::new();
        cm.push(CharRange::single(1), &10);
        cm.push(CharRange::single(3), &11);
        cm.push(CharRange::new(5, 7), &12);
        cm.push(CharRange::single(9), &13);
        assert_eq!(cm.get(1), Some(&10));
        assert_eq!(cm.get(3), Some(&11));
        assert_eq!(cm.get(5), Some(&12));
        assert_eq!(cm.get(6), Some(&12));
        assert_eq!(cm.get(9), Some(&13));
        assert_eq!(cm.get(0), None);
        assert_eq!(cm.get(2), None);
        assert_eq!(cm.get(4), None);
        assert_eq!(cm.get(77), None);
    }

    #[test]
    fn test_contains() {
        let mut cs = CharSet::new();
        cs.push(CharRange::single(1));
        cs.push(CharRange::new(5, 7));
        assert!(cs.contains(1));
        assert!(cs.contains(5));
        assert!(cs.contains(6));
        assert!(cs.contains(7));
        assert!(!cs.contains(0));
        assert!(!cs.contains(4));
        assert!(!cs.contains(8));
    }

    #[test]
    fn test_intersect() {
        let mut cs1 = CharSet::new();
        let mut cs2 = CharSet::new();
        let mut result = CharSet::new();

        cs1.push(CharRange::new(1, 20));
        cs2.push(CharRange::new(2, 4));
        result.push(CharRange::new(2, 4));
        assert_eq!(result, cs1.intersect(&cs2));
        assert_eq!(result, cs2.intersect(&cs1));

        cs2.push(CharRange::new(7, 8));
        result.push(CharRange::new(7, 8));
        assert_eq!(result, cs1.intersect(&cs2));
        assert_eq!(result, cs2.intersect(&cs1));

        cs2.push(CharRange::new(15, 25));
        result.push(CharRange::new(15, 20));
        assert_eq!(result, cs1.intersect(&cs2));
        assert_eq!(result, cs2.intersect(&cs1));
    }

    #[test]
    fn test_split() {
        let trans = CharMultiMap::<usize>::from_vec(vec![
            (CharRange::new(0, 5), 0),
            (CharRange::new(2, 7), 1),
        ]);

        let trans = trans.split();
        assert_eq!(trans.elts, vec![
            (CharRange::new(0, 1), 0),
            (CharRange::new(2, 5), 0),
            (CharRange::new(2, 5), 1),
            (CharRange::new(6, 7), 1),
        ]);
    }
}

