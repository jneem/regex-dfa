use regex_syntax::CharClass;
use std::cmp::Ordering;
use std::collections::{BitSet, HashMap};
use std::u32;

/// A range of symbols.
///
/// Includes the endpoints.
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

#[derive(PartialEq, Debug)]
pub struct TransList {
    pub ranges: Vec<(SymbRange, usize)>,
    pub eps: Vec<usize>, // Transitions that don't consume any input.
}

impl TransList {
    pub fn new() -> TransList {
        TransList {
            ranges: Vec::new(),
            eps: Vec::new(),
        }
    }

    pub fn from_vec(vec: Vec<(SymbRange, usize)>) -> TransList {
        TransList {
            ranges: vec,
            eps: Vec::new(),
        }
    }

    pub fn from_char_class(c: &CharClass, target: usize) -> TransList {
        let mut ret = TransList::new();
        for range in c {
            ret.ranges.push((SymbRange::new(range.start as u32, range.end as u32), target))
        }
        ret
    }

    pub fn find_transition(&self, ch: u32) -> Option<usize> {
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
    fn split_transitions(&self) -> TransList {
        let mut ret = TransList::new();
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

    /// Returns the complement of this transition list.
    ///
    /// This assumes that the transition list is sorted and that
    /// every range has the same target state.
    fn negated(&self) -> TransList {
        let mut ret = TransList::new();
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
}

impl TransList {
    // TODO: support case insensitivity
        /* FIXME
    pub fn from_char_class(ranges: &Vec<(char, char)>,
                           flags: u8,
                           state: usize) -> TransList {
        let mut ret = TransList::new();

        for &(from, to) in ranges.iter() {
            ret.ranges.push((SymbRange::new(from as u32, to as u32), state));
        }
        if flags & FLAG_NEGATED > 0 {
            ret.negated()
        } else {
            ret
        }
        ret
    }
        */
}


