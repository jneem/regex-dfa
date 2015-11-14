// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use regex_syntax;
use std;
use std::char;
use std::cmp::{max, min, Ordering};
use std::collections::HashMap;
use std::hash::Hash;
use std::iter::RangeInclusive;
use std::fmt::{Debug, Formatter};
use std::ops::Deref;
use transition::StateSet;

const DISPLAY_LIMIT: usize = 10;

/// A range of code points, including the endpoints.
///
/// If `start` is strictly larger than `end` then this represents an empty range.
#[derive(PartialEq, Debug, Copy, Clone, Hash)]
pub struct CharRange {
    pub start: u32,
    pub end: u32,
}

impl Eq for CharRange {}

impl CharRange {
    /// Creates a new `CharRange` with the given start and endpoints (inclusive).
    pub fn new(start: u32, end: u32) -> CharRange {
        CharRange { start: start, end: end }
    }

    /// Creates a new `CharRange` containing all characters.
    pub fn full() -> CharRange {
        CharRange { start: 0, end: std::u32::MAX }
    }

    /// Creates a new `CharRange` containing a single character.
    pub fn single(ch: u32) -> CharRange {
        CharRange::new(ch, ch)
    }

    /// Tests whether a given char belongs to this range.
    pub fn contains(&self, ch: u32) -> bool {
        self.start <= ch && ch <= self.end
    }

    /// Computes the intersection between two ranges.
    pub fn intersection(&self, other: &CharRange) -> CharRange {
        CharRange::new(max(self.start, other.start), min(self.end, other.end))
    }

    /// Tests whether this range is empty.
    ///
    /// TODO: can we just forbid ranges from being empty?
    pub fn is_empty(&self) -> bool {
        self.start > self.end
    }

    /// Returns the smallest range that covers `self` and `other`.
    pub fn cover(&self, other: &CharRange) -> CharRange {
        if self.is_empty() {
            other.clone()
        } else if other.is_empty() {
            self.clone()
        } else {
            CharRange::new(min(self.start, other.start), max(self.end, other.end))
        }
    }

    /// Returns an iterator over chars in this range.
    pub fn iter(&self) -> RangeInclusive<u32> {
        std::iter::range_inclusive(self.start, self.end)
    }

    /// Returns this range as a pair of chars, or none if this is an empty range.
    pub fn to_char_pair(&self) -> Option<(char, char)> {
        // Round up self.start to the nearest legal codepoint.
        let start = if self.start > 0xD7FF && self.start < 0xE000 {
            0xE000
        } else {
            self.start
        };

        // Round down self.end.
        let end = if self.end > 0x10FFFF {
            0x10FFFF
        } else if self.end < 0xE000 && self.end > 0xD7FF {
            0xD7FF
        } else {
            self.end
        };

        if start > end {
            None
        } else {
            Some((char::from_u32(start).unwrap(), char::from_u32(end).unwrap()))
        }
    }
}

impl PartialEq<u32> for CharRange {
    fn eq(&self, ch: &u32) -> bool {
        self.contains(*ch)
    }
}

impl PartialOrd<u32> for CharRange {
    fn partial_cmp(&self, ch: &u32) -> Option<Ordering> {
        if self.end < *ch {
            Some(Ordering::Less)
        } else if self.start > *ch {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

/// A set of characters. Optionally, each character in the set may be associated with some data.
#[derive(PartialEq, Clone, Hash)]
pub struct CharMap<T: Clone + Debug + PartialEq> {
    elts: Vec<(CharRange, T)>,
}

impl<T: Clone + Debug + PartialEq + Eq> Eq for CharMap<T> {}

impl<T: Clone + Debug + PartialEq> IntoIterator for CharMap<T> {
    type Item = (CharRange, T);
    type IntoIter = std::vec::IntoIter<(CharRange, T)>;
    fn into_iter(self) -> Self::IntoIter {
        self.elts.into_iter()
    }
}

impl<'a, T: Clone + Debug + PartialEq> IntoIterator for &'a CharMap<T> {
    type Item = &'a (CharRange, T);
    type IntoIter = std::slice::Iter<'a, (CharRange, T)>;
    fn into_iter(self) -> Self::IntoIter {
        self.elts.iter()
    }
}

impl<T: Clone + Debug + PartialEq> Debug for CharMap<T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        let s = self.iter()
            .take(DISPLAY_LIMIT)
            .map(|x| format!("{} - {} => {:?}", x.0.start, x.0.end, x.1))
            .collect::<Vec<String>>()
            .join(", ");
        if self.elts.len() > DISPLAY_LIMIT {
            try!(f.write_fmt(format_args!("CharMap ({}...)", s)));
        } else {
            try!(f.write_fmt(format_args!("CharMap ({})", s)));
        }
        Ok(())
    }
}

impl<T: Clone + Debug + PartialEq> CharMap<T> {
    /// Creates a new empty `CharMap`.
    pub fn new() -> CharMap<T> {
        CharMap {
            elts: Vec::new(),
        }
    }

    /// Creates a new empty `CharMap` for which `push` can be called `n` times without
    /// reallocation.
    pub fn with_capacity(n: usize) -> CharMap<T> {
        CharMap {
            elts: Vec::with_capacity(n),
        }
    }

    /// Creates a `CharMap` from a `Vec`, which is assumed to contain non-overlapping ranges in
    /// ascending order.
    pub fn from_vec(vec: Vec<(CharRange, T)>) -> CharMap<T> {
        CharMap {
            elts: vec,
        }
    }

    /// Returns the number of intervals in this `CharMap`.
    ///
    /// Note that this is not usually the same as the number of mapped characters.
    pub fn len(&self) -> usize {
        self.elts.len()
    }

    /// Tests whether this `CharMap` is empty.
    pub fn is_empty(&self) -> bool {
        self.elts.is_empty()
    }

    /// Tests whether this `CharMap` maps every value.
    ///
    /// Assumes the `CharMap` is `normalize()`ed.
    pub fn is_full(&self) -> bool {
        self.elts.len() == 1 && self.elts[0].0 == CharRange::new(0, std::u32::MAX)
    }

    /// Iterates over all the mapped ranges and values.
    pub fn iter<'a>(&'a self) -> std::slice::Iter<'a, (CharRange, T)> {
        self.elts.iter()
    }

    /// Returns a `Vec` of pairs of mapped chars and their values.
    // Probably this should return an iterator, but I was having trouble with lifetimes...
    pub fn pairs(&self) -> Vec<(u32, T)> {
        let tmp: Vec<Vec<(u32, T)>> =
            self.elts.iter()
                .map(|x| x.0.iter().map(|c| (c, x.1.clone())).collect()).collect();
        tmp.into_iter().flat_map(|v| v.into_iter()).collect()
    }

    /// Minimizes the number of ranges in this `CharMap`.
    ///
    /// If there are any adjacent ranges that map to the same data, merges them.
    pub fn normalize(&mut self) {
        let mut vec = Vec::with_capacity(self.elts.len());
        if let Some((head, rest)) = self.elts.split_first() {
            vec.push((head.0, head.1.clone()));
            for elt in rest {
                if elt.0.start == vec.last().unwrap().0.end + 1
                        && elt.1 == vec.last().unwrap().1 {
                    vec.last_mut().unwrap().0.end = elt.0.end;
                } else {
                    vec.push((elt.0, elt.1.clone()));
                }
            }
        }
        self.elts = vec;
    }

    /// Maps the given range of characters to to the given value.
    ///
    /// This function must maintain an (unenforced) invariant: all the ranges must be
    /// non-overlapping. Moreover, if they are added in any order other than increasing order, then
    /// `sort()` must be called before any other methods are.
    ///
    /// # Panics
    ///  - if the range is empty.
    pub fn push(&mut self, range: CharRange, t: &T) {
        if range.is_empty() {
            panic!("ranges must be non-empty");
        }
        self.elts.push((range, t.clone()));
    }

    /// Sorts the ranges.
    ///
    /// If you have `push()`ed ranges out of order, then you must call this method before doing
    /// anything else.
    ///
    /// # Panics
    ///  - if there are any overlapping ranges.
    pub fn sort(&mut self) {
        self.elts.sort_by(|&(r1, _), &(r2, _)| r1.start.cmp(&r2.start));
        for win in self.elts.windows(2) {
            if win[0].0.end >= win[1].0.start {
                panic!("overlapping ranges");
            }
        }
    }

    /// Intersects this map with another set of characters.
    pub fn intersect(&self, other: &CharSet) -> CharMap<T> {
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

    /// Counts the number of mapped chars.
    ///
    /// This saturates at u32::MAX, even if the map is full. Note that this is not guaranteed to
    /// reflect the actual number of valid codepoints mapped, since we might be mapping some
    /// invalid codepoints also.
    pub fn char_count(&self) -> u32 {
        self.iter().fold(0, |acc, range| {
            acc.saturating_add((range.0.end - range.0.start).saturating_add(1))
        })
    }

    /// Returns the set of mapped chars, forgetting what they are mapped to.
    pub fn to_char_set(&self) -> CharSet {
        CharSet::from_vec(self.elts.iter().map(|x| (x.0, ())).collect())
    }

    /// Modifies the values in place.
    pub fn map_values<F>(&mut self, mut f: F) where F: FnMut(T) -> T {
        for &mut (_, ref mut data) in &mut self.elts {
            *data = f(data.clone());
        }
    }

    /// Returns a new `CharMap`, containing only those mappings with values `v` satisfying `f(v)`.
    pub fn filter_values<F>(&self, mut f: F) -> CharMap<T> where F: FnMut(&T) -> bool {
        CharMap {
            elts: self.elts.iter().cloned().filter(|x| f(&x.1)).collect()
        }
    }
}

/// A set of characters, implemented as a sorted list of (inclusive) ranges.
#[derive(PartialEq, Clone, Hash)]
pub struct CharSet {
    map: CharMap<()>,
}

impl Eq for CharSet {}

impl<'a> IntoIterator for &'a CharSet {
    type Item = &'a CharRange;

    type IntoIter = Box<std::iter::Iterator<Item=&'a CharRange> + 'a>;
    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.map.elts.iter().map(|x| &x.0))
    }
}

impl Debug for CharSet {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        let s = self.into_iter()
            .take(DISPLAY_LIMIT)
            .map(|x| format!("{} - {}", x.start, x.end))
            .collect::<Vec<String>>()
            .join(", ");
        if self.map.elts.len() > DISPLAY_LIMIT {
            try!(f.write_fmt(format_args!("CharSet ({}...)", s)));
        } else {
            try!(f.write_fmt(format_args!("CharSet ({})", s)));
        }
        Ok(())
    }
}

impl CharSet {
    /// Creates a new empty `CharSet`.
    pub fn new() -> CharSet {
        CharSet { map: CharMap::new() }
    }

    /// Creates a new empty `CharSet` for which `push` can be called `n` times without
    /// reallocation.
    pub fn with_capacity(n: usize) -> CharSet {
        CharSet { map: CharMap::with_capacity(n) }
    }

    /// Sorts the ranges in this set. See `CharMap::sort` for more details.
    ///
    /// # Panics
    ///  - if any ranges overlap.
    pub fn sort(&mut self) {
        self.map.sort();
    }

    /// Tests if this set is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Tests whether this `CharSet` contains every char.
    pub fn is_full(&self) -> bool {
        self.map.is_full()
    }

    fn from_vec(vec: Vec<(CharRange, ())>) -> CharSet {
        let mut ret = CharSet { map: CharMap { elts: vec } };
        ret.sort();
        ret
    }

    /// Returns the union between `self` and `other`.
    pub fn union(&self, other: &CharSet) -> CharSet {
        if self.is_empty() {
            return other.clone();
        } else if other.is_empty() {
            return self.clone();
        }

        let mut ret = Vec::with_capacity(self.map.elts.len() + other.map.elts.len());
        let mut it1 = self.map.elts.iter();
        let mut it2 = other.map.elts.iter();
        let mut r1 = it1.next();
        let mut r2 = it2.next();
        let mut cur_range = CharRange::new(1, 0);

        while r1.is_some() || r2.is_some() {
            let r1_start = if let Some(&(r, _)) = r1 { r.start } else { std::u32::MAX };
            let r2_start = if let Some(&(r, _)) = r2 { r.start } else { std::u32::MAX };
            if !cur_range.is_empty() && min(r1_start, r2_start) > cur_range.end.saturating_add(1) {
                ret.push((cur_range, ()));
                cur_range = CharRange::new(1, 0);
            }

            if r1_start < r2_start || r2.is_none() {
                cur_range = cur_range.cover(&r1.unwrap().0);
                r1 = it1.next();
            } else {
                cur_range = cur_range.cover(&r2.unwrap().0);
                r2 = it2.next();
            }
        }

        if !cur_range.is_empty() {
            ret.push((cur_range, ()));
        }

        CharSet::from_vec(ret)
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
        CharSet::from_vec(vec![(CharRange::full(), ())])
    }

    /// Creates a `CharSet` containing a single codepoint.
    pub fn single(ch: u32) -> CharSet {
        CharSet::from_vec(vec![(CharRange::single(ch), ())])
    }

    /// Creates a `CharSet` containing all codepoints except the given ones.
    ///
    /// # Panics
    ///  - if `chars` is not sorted or not unique.
    pub fn except(chars: &str) -> CharSet {
        if chars.is_empty() {
            return CharSet::full();
        }

        let mut ret = Vec::with_capacity(chars.len());
        let mut next_allowed = 0u32;
        let mut n = 0u32;
        for c in chars.chars() {
            n = c as u32;
            if n > next_allowed {
                ret.push((CharRange::new(next_allowed, n - 1), ()));
            } else if n < next_allowed {
                panic!("input to CharSet::except must be sorted");
            }

            if n < std::u32::MAX {
                next_allowed = n + 1;
            } else {
                break;
            }
        }

        if n < std::u32::MAX {
            ret.push((CharRange::new(n + 1, std::u32::MAX), ()));
        }
        CharSet::from_vec(ret)
    }

    /// Finds the intersection between this set and `other`.
    pub fn intersect(&self, other: &CharSet) -> CharSet {
        CharSet { map: self.map.intersect(other) }
    }

    /// Adds the given range of characters to this set. The range must be non-empty.
    ///
    /// See `CharMap::push` for more details.
    ///
    /// # Panics
    ///  - if the range is empty.
    pub fn push(&mut self, r: CharRange) {
        self.map.push(r, &());
    }

    /// Returns the set of all characters that are not in this set.
    pub fn negated(&self) -> CharSet {
        let mut ret = CharSet::with_capacity(self.map.len() + 1);
        let mut last_end = 0u32;

        for range in self {
            if range.start > last_end {
                ret.push(CharRange::new(last_end, range.start - 1u32));
            }
            last_end = range.end.saturating_add(1u32);
        }
        if last_end < std::u32::MAX {
            ret.push(CharRange::new(last_end, std::u32::MAX));
        }

        ret
    }
}

/// A multi-valued mapping from chars to other data.
#[derive(Clone, Hash, PartialEq)]
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

impl<T: Clone + Debug + Hash + PartialEq> Debug for CharMultiMap<T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        let s = self.elts.iter()
            .take(DISPLAY_LIMIT)
            .map(|x| format!("{} - {} => {:?}", x.0.start, x.0.end, x.1))
            .collect::<Vec<String>>()
            .join(", ");
        if self.elts.len() > DISPLAY_LIMIT {
            try!(f.write_fmt(format_args!("CharMultiMap ({}...)", s)));
        } else {
            try!(f.write_fmt(format_args!("CharMultiMap ({})", s)));
        }
        Ok(())
    }
}

impl<T: Clone + Debug + Hash + PartialEq> CharMultiMap<T> {
    /// Creates a new empty `CharMultiMap`.
    pub fn new() -> CharMultiMap<T> {
        CharMultiMap { elts: Vec::new() }
    }

    /// Adds a new mapping from a range of characters to `data`.
    pub fn push(&mut self, range: CharRange, data: &T) {
        self.elts.push((range, data.clone()));
    }

    /// Creates a `CharMultiMap` from a vector of pairs.
    pub fn from_vec(vec: Vec<(CharRange, T)>) -> CharMultiMap<T> {
        CharMultiMap { elts: vec }
    }

    /// Returns a new `CharMultiMap` containing only the mappings for chars that belong to the
    /// given set.
    pub fn intersect(&self, other: &CharSet) -> CharMultiMap<T> {
        let mut ret = Vec::new();
        for &(ref my_range, ref data) in &self.elts {
            let start_idx = other.map.elts
                .binary_search_by(|r| r.0.end.cmp(&my_range.start))
                .unwrap_or_else(|x| x);
            for &(ref other_range, _) in &other.map.elts[start_idx..] {
                if my_range.start > other_range.end {
                    break;
                } else if my_range.end >= other_range.start {
                    ret.push((CharRange::intersection(my_range, other_range), data.clone()));
                }
            }
        }
        CharMultiMap { elts: ret }
    }

    /// Returns a new `CharMultiMap`, containing only those mappings with values `v` satisfying
    /// `f(v)`.
    pub fn filter_values<F>(&self, mut f: F) -> CharMultiMap<T> where F: FnMut(&T) -> bool {
        CharMultiMap::from_vec(self.elts.iter().filter(|x| f(&x.1)).cloned().collect())
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

    pub fn into_vec(self) -> Vec<(CharRange, T)> {
        self.elts
    }

    pub fn vec_ref_mut(&mut self) -> &mut Vec<(CharRange, T)> {
        &mut self.elts
    }
}

impl CharMultiMap<usize> {
    /// Makes the ranges sorted and non-overlapping. The data associated with each range will
    /// be a set of `usize`s instead of a single `usize`.
    pub fn group(&self) -> CharMap<StateSet> {
        let mut map = HashMap::<CharRange, StateSet>::new();
        for (range, state) in self.split().elts.into_iter() {
            map.entry(range).or_insert(StateSet::new()).push(state);
        }

        let mut vec: Vec<(CharRange, StateSet)> = map.into_iter().collect();
        for &mut (_, ref mut set) in &mut vec {
            set.sort();
            set.dedup();
        }
        vec.sort_by(|&(r1, _), &(r2, _)| r1.start.cmp(&r2.start));
        CharMap { elts: vec }
    }
}

impl<T: Clone + Debug + Hash + PartialEq> Deref for CharMultiMap<T> {
    type Target = Vec<(CharRange, T)>;
    fn deref(&self) -> &Self::Target {
        &self.elts
    }
}

#[cfg(test)]
mod tests {
    use char_map::*;
    use std::u32::MAX;

    #[test]
    fn test_except() {
        assert_eq!(CharSet::except(""), CharSet::full());
        assert_eq!(CharSet::except("\0"), CharSet::from_vec(vec![(CharRange::new(1, MAX), ())]));

        let mut cs = CharSet::new();
        cs.push(CharRange::new(0, 9));
        cs.push(CharRange::new(11, 12));
        cs.push(CharRange::new(14, MAX));
        assert_eq!(CharSet::except("\n\r"), cs);
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
    fn test_union() {
        let mut cs1 = CharSet::new();
        let mut cs2 = CharSet::new();
        let mut result = CharSet::new();
        assert_eq!(result, cs1.union(&cs2));

        cs1.push(CharRange::new(1, 3));
        result.push(CharRange::new(1, 3));
        assert_eq!(result, cs1.union(&cs2));
        assert_eq!(result, cs2.union(&cs1));

        cs2.push(CharRange::new(5, 6));
        result.push(CharRange::new(5, 6));
        assert_eq!(result, cs1.union(&cs2));
        assert_eq!(result, cs2.union(&cs1));

        cs1.push(CharRange::new(6, 8));
        result.map.elts[1].0.end = 8;
        assert_eq!(result, cs1.union(&cs2));
        assert_eq!(result, cs2.union(&cs1));

        cs1.push(CharRange::new(7, 10));
        result.map.elts[1].0.end = 10;
        assert_eq!(result, cs1.union(&cs2));
        assert_eq!(result, cs2.union(&cs1));

        cs1.push(CharRange::new(15, 20));
        result.push(CharRange::new(15, 20));
        assert_eq!(result, cs1.union(&cs2));
        assert_eq!(result, cs2.union(&cs1));
    }

    #[test]
    fn test_normalize() {
        let mut map = CharMap::from_vec(vec![
            (CharRange::new(0, 3), 0),
            (CharRange::new(5, 6), 0),
            (CharRange::new(7, 9), 0),
            (CharRange::new(15, 16), 0),
            (CharRange::new(17, 20), 1),
            (CharRange::new(21, 23), 1),
        ]);
        let target = CharMap::from_vec(vec![
            (CharRange::new(0, 3), 0),
            (CharRange::new(5, 9), 0),
            (CharRange::new(15, 16), 0),
            (CharRange::new(17, 23), 1),
        ]);
        map.normalize();
        assert_eq!(map, target);
    }

    fn make_mm(xs: &[(u32, u32, usize)]) -> CharMultiMap<usize> {
        CharMultiMap::from_vec(xs.iter().map(|x| (CharRange::new(x.0, x.1), x.2)).collect())
    }

    #[test]
    fn test_multimap_intersect() {
        let mm = make_mm(&[
            (1, 5, 1),
            (2, 6, 2),
            (3, 6, 3),
            (7, 10, 1),
            (4, 9, 4),
        ]);
        let mut cs = CharSet::new();

        assert_eq!(mm.intersect(&cs), CharMultiMap::new());
        cs.push(CharRange::new(11, 100));
        assert_eq!(mm.intersect(&cs), CharMultiMap::new());
        cs.push(CharRange::new(7, 8));
        cs.sort();
        assert_eq!(mm.intersect(&cs), make_mm(&[(7, 8, 1), (7, 8, 4)]));
        cs.push(CharRange::new(2, 3));
        cs.sort();
        assert_eq!(mm.intersect(&cs),
            make_mm(&[(2, 3, 1), (2, 3, 2), (3, 3, 3), (7, 8, 1), (7, 8, 4)]));
        cs.push(CharRange::new(0, 1));
        cs.sort();
        assert_eq!(mm.intersect(&cs),
            make_mm(&[(1, 1, 1), (2, 3, 1), (2, 3, 2), (3, 3, 3), (7, 8, 1), (7, 8, 4)]));
    }


    #[test]
    fn test_split() {
        assert_eq!(
            make_mm(&[(1, 5, 1), (6, 8, 2), (9, 10, 3)]).split(),
            make_mm(&[(1, 5, 1), (6, 8, 2), (9, 10, 3)]));
        assert_eq!(
            make_mm(&[(1, 5, 1), (3, 4, 2)]).split(),
            make_mm(&[(1, 2, 1), (3, 4, 1), (5, 5, 1), (3, 4, 2)]));
        assert_eq!(
            make_mm(&[(1, 5, 1), (3, 4, 2), (0, 1, 3)]).split(),
            make_mm(&[(1, 1, 1), (2, 2, 1), (3, 4, 1), (5, 5, 1), (3, 4, 2), (0, 0, 3), (1, 1, 3)]));
    }
}

