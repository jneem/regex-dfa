// Copyright 2015-2016 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use aho_corasick::{Automaton, AcAutomaton, FullAcAutomaton, MatchesOverlapping};
use memchr::memchr;
use memmem::{Searcher, TwoWaySearcher};

/// A `Prefix` is the first part of a DFA. Anything matching the DFA should start with
/// something matching the `Prefix`.
///
/// The purpose of a `Prefix` is that scanning through the input looking for the `Prefix` should be
/// much faster than running the DFA naively.
#[derive(Clone, Debug)]
pub enum Prefix {
    // Matches every position.
    Empty,
    // Matches a single byte in a particular set.
    ByteSet(Vec<bool>),
    // Matches one specific byte.
    Byte(u8),
    // Matches a specific sequence of bytes.
    Lit(Vec<u8>),
    // Matches one of several sequences of bytes. The sequences are contained in the
    // `FullAcAutomaton`. The `Vec<usize>` tells us which state the DFA should start in after
    // matching each sequence. That is, `vec[i] == s` if after finding sequence `i` we should
    // start in state `s`.
    Ac(FullAcAutomaton<Vec<u8>>, Vec<usize>),
}

/// The result of scanning through the input for a `Prefix`.
///
/// The semi-open interval `[start_pos, end_pos)` is the part of the interval that was consumed by
/// the `Prefix`. The state `end_state` is the DFA state at which we should start to continue
/// matching; that is, the DFA should begin at position `end_pos` in state `end_state`.
///
/// Note that some `Prefix`es return empty intervals (`start_pos == end_pos`). This doesn't mean
/// necessarily that the `Prefix` didn't match any input, only that it's simpler (and fast) just
/// to have the DFA re-match from the beginning.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrefixResult {
    pub start_pos: usize,
    pub end_pos: usize,
    pub end_state: usize,
}

/// Encapsulates the `Prefix` and the input string, and allows iteration over all matches.
pub trait PrefixSearcher {
    /// Moves the "cursor" to the given position in the input.
    fn skip_to(&mut self, pos: usize);
    /// From the current position in the input, finds the next substring matching the `Prefix`
    /// and advances the "cursor" past that point.
    fn search(&mut self) -> Option<PrefixResult>;
}

impl Prefix {
    /// Converts a set of `(string, state)` pairs into a `Prefix` that matches any of the strings.
    ///
    /// The `state` part of each `(string, state)` pair is the DFA state that we would be in after
    /// matching the `string`.
    pub fn from_strings<P: AsRef<[u8]>, I: Iterator<Item=(P, usize)>>(it: I) -> Prefix {
        let strings: Vec<(Vec<u8>, usize)> = it
            .filter(|x| !x.0.as_ref().is_empty())
            .map(|(s, x)| (s.as_ref().to_vec(), x))
            .collect();

        if strings.is_empty() {
            Prefix::Empty
        } else if strings.len() == 1 {
            if strings[0].0.len() == 1 {
                Prefix::Byte(strings[0].0[0])
            } else {
                Prefix::Lit(strings.into_iter().next().unwrap().0)
            }
        } else if strings.iter().map(|x| x.0.len()).min() == Some(1) {
            let mut bs = vec![false; 256];
            for (s, _) in strings.into_iter() {
                bs[s[0] as usize] = true;
            }
            Prefix::ByteSet(bs)
        } else {
            let state_map: Vec<_> = strings.iter().map(|x| x.1).collect();
            let ac = FullAcAutomaton::new(AcAutomaton::new(strings.into_iter().map(|x| x.0)));
            Prefix::Ac(ac, state_map)
        }
    }

    /// Takes an input string and prepares for quickly finding matches in it.
    pub fn make_searcher<'a>(&'a self, input: &'a [u8]) -> Box<PrefixSearcher + 'a> {
        use runner::prefix::Prefix::*;

        match self {
            &Empty => Box::new(SimpleSearcher::new((), input)),
            &ByteSet(ref bs) => Box::new(SimpleSearcher::new(&bs[..], input)),
            &Byte(b) => Box::new(SimpleSearcher::new(b, input)),
            &Lit(ref l) => Box::new(lit_searcher(l, input)),
            &Ac(ref ac, ref map) => Box::new(AcSearcher::new(ac, map, input)),
        }
    }
}

// TODO: profile to see if this really helps
macro_rules! run_with_searcher {
    ($prefix:expr, $input:expr, $callback:expr) => {
        match $prefix {
            Prefix::Empty => $callback(SimpleSearcher::new((), $input)),
            Prefix::ByteSet(ref bs) => $callback(SimpleSearcher::new(&bs[..], $input)),
            Prefix::Byte(b) => $callback(SimpleSearcher::new(b, $input)),
            Prefix::Lit(ref l) => $callback(lit_searcher(l, $input)),
            Prefix::Ac(ref ac, ref map) => $callback(AcSearcher::new(ac, map, $input)),
        }
    };
}

pub trait SkipFn {
    fn skip(&self, input: &[u8]) -> Option<(usize, usize)>;
}

pub trait SimpleSkipFn {
    fn simple_skip(&self, input: &[u8]) -> Option<usize>;
}

impl<Sk: SimpleSkipFn> SkipFn for Sk {
    fn skip(&self, input: &[u8]) -> Option<(usize, usize)> {
        self.simple_skip(input).map(|x| (x, x))
    }
}

impl SimpleSkipFn for () {
    #[inline(always)]
    fn simple_skip(&self, _: &[u8]) -> Option<usize> { Some(0) }
}

impl SimpleSkipFn for u8 {
    #[inline(always)]
    fn simple_skip(&self, input: &[u8]) -> Option<usize> { memchr(*self, input) }
}

impl<'a> SimpleSkipFn for TwoWaySearcher<'a> {
    fn simple_skip(&self, input: &[u8]) -> Option<usize> { self.search_in(input) }
}

impl<'a> SimpleSkipFn for &'a [bool] {
    #[inline(always)]
    fn simple_skip(&self, input: &[u8]) -> Option<usize> {
        input.iter().position(|c| self[*c as usize])
    }
}

pub struct SimpleSearcher<'a, Skip: SkipFn> {
    skip_fn: Skip,
    input: &'a [u8],
    pos: usize,
}

impl<'a, Sk: SkipFn> SimpleSearcher<'a, Sk> {
    pub fn new(skip_fn: Sk, input: &'a [u8]) -> SimpleSearcher<'a, Sk> {
        SimpleSearcher {
            skip_fn: skip_fn,
            input: input,
            pos: 0,
        }
    }
}

pub fn lit_searcher<'i, 'lit>(lit: &'lit [u8], input: &'i [u8])
-> SimpleSearcher<'i, TwoWaySearcher<'lit>> {
    SimpleSearcher {
        skip_fn: TwoWaySearcher::new(lit),
        input: input,
        pos: 0,
    }
}

impl<'a, Sk: SkipFn> PrefixSearcher for SimpleSearcher<'a, Sk> {
    fn search(&mut self) -> Option<PrefixResult> {
        if self.pos > self.input.len() {
            None
        } else if let Some((start_off, end_off)) = self.skip_fn.skip(&self.input[self.pos..]) {
            let start = self.pos + start_off;
            let end = self.pos + end_off;
            self.pos += end_off + 1;

            Some(PrefixResult {
                start_pos: start,
                end_pos: end,
                end_state: 0,
            })
        } else {
            None
        }
    }

    fn skip_to(&mut self, pos: usize) { self.pos = pos; }
}

pub struct AcSearcher<'ac, 'i, 'st> {
    ac: &'ac FullAcAutomaton<Vec<u8>>,
    state_map: &'st [usize],
    input: &'i [u8],
    pos: usize,
    iter: MatchesOverlapping<'ac, 'i, Vec<u8>, FullAcAutomaton<Vec<u8>>>,
}

impl<'ac, 'i, 'st> AcSearcher<'ac, 'i, 'st> {
    pub fn new(ac: &'ac FullAcAutomaton<Vec<u8>>, state_map: &'st [usize], input: &'i [u8])
    -> AcSearcher<'ac, 'i, 'st> {
        AcSearcher {
            ac: ac,
            state_map: state_map,
            input: input,
            pos: 0,
            iter: ac.find_overlapping(input),
        }
    }
}

impl<'ac, 'i, 'st> PrefixSearcher for AcSearcher<'ac, 'i, 'st> {
    fn skip_to(&mut self, pos: usize) {
        self.pos = pos;
        let input: &'i [u8] = if pos > self.input.len() {
            &[]
        } else {
            &self.input[self.pos..]
        };
        self.iter = self.ac.find_overlapping(input);
    }

    fn search(&mut self) -> Option<PrefixResult> {
        self.iter.next().map(|mat| PrefixResult {
            start_pos: mat.start + self.pos,
            end_pos: mat.end + self.pos,
            end_state: self.state_map[mat.pati],
        })
    }
}

#[cfg(test)]
mod tests {
    use runner::prefix::*;

    impl<'a> Iterator for Box<PrefixSearcher + 'a> {
        type Item = PrefixResult;
        fn next(&mut self) -> Option<PrefixResult> {
            self.search()
        }
    }

    fn search(pref: Prefix, input: &str) -> Vec<PrefixResult> {
        pref.make_searcher(input.as_bytes()).collect::<Vec<_>>()
    }

    fn result(pos: usize) -> PrefixResult {
        PrefixResult {
            start_pos: pos,
            end_pos: pos,
            end_state: 0,
        }
    }

    fn results(posns: Vec<usize>) -> Vec<PrefixResult> {
        posns.into_iter().map(result).collect()
    }

    #[test]
    fn test_empty_search() {
        assert_eq!(search(Prefix::Empty, "blah"), results(vec![0, 1, 2, 3, 4]));
        assert_eq!(search(Prefix::Empty, ""), results(vec![0]));
    }

    #[test]
    fn test_byte_search() {
        assert_eq!(search(Prefix::Byte(b'a'), "abracadabra"), results(vec![0, 3, 5, 7, 10]));
        assert_eq!(search(Prefix::Byte(b'a'), "abracadabr"), results(vec![0, 3, 5, 7]));
        assert_eq!(search(Prefix::Byte(b'a'), ""), vec![]);
    }

    #[test]
    fn test_str_search() {
        fn lit_pref(s: &str) -> Prefix {
            Prefix::Lit(s.as_bytes().to_vec())
        }
        assert_eq!(search(lit_pref("aa"), "baa baa black sheep aa"), results(vec![1, 5, 20]));
        assert_eq!(search(lit_pref("aa"), "aaa baaa black sheep"), results(vec![0, 1, 5, 6]));
        assert_eq!(search(lit_pref("aa"), ""), vec![]);
    }

    #[test]
    fn test_byteset_search() {
        fn bs_pref(s: &str) -> Prefix {
            let mut bytes = vec![false; 256];
            for &b in s.as_bytes().iter() {
                bytes[b as usize] = true;
            }
            Prefix::ByteSet(bytes)
        }
        assert_eq!(search(bs_pref("aeiou"), "quick brown"), results(vec![1, 2, 8]));
        assert_eq!(search(bs_pref("aeiou"), "aabaa"), results(vec![0, 1, 3, 4]));
        assert_eq!(search(bs_pref("aeiou"), ""), vec![]);
    }

    #[test]
    fn test_ac_search() {
        fn ac_pref(strs: Vec<&str>) -> Prefix {
            let len = strs.len();
            let pref = Prefix::from_strings(strs.into_iter().zip(0..len));
            assert!(matches!(pref, Prefix::Ac(_, _)));
            pref
        }

        assert_eq!(search(ac_pref(vec!["baa", "aa"]), "baa aaa black sheep"),
            vec![
                PrefixResult { start_pos: 0, end_pos: 3, end_state: 0 },
                PrefixResult { start_pos: 1, end_pos: 3, end_state: 1 },
                PrefixResult { start_pos: 4, end_pos: 6, end_state: 1 },
                PrefixResult { start_pos: 5, end_pos: 7, end_state: 1 },
            ]);
        assert_eq!(search(ac_pref(vec!["baa", "aa"]), ""), vec![]);
    }

    #[test]
    fn test_prefix_choice() {
        use runner::prefix::Prefix::*;

        fn pref(strs: Vec<&str>) -> Prefix {
            let len = strs.len();
            Prefix::from_strings(strs.into_iter().zip(0..len))
        }

        assert!(matches!(pref(vec![]), Empty));
        assert!(matches!(pref(vec![""]), Empty));
        assert!(matches!(pref(vec!["a"]), Byte(_)));
        assert!(matches!(pref(vec!["", "a", ""]), Byte(_)));
        assert!(matches!(pref(vec!["abc"]), Lit(_)));
        assert!(matches!(pref(vec!["abc", ""]), Lit(_)));
        assert!(matches!(pref(vec!["a", "b", "c"]), ByteSet(_)));
        assert!(matches!(pref(vec!["a", "b", "", "c"]), ByteSet(_)));
        assert!(matches!(pref(vec!["a", "baa", "", "c"]), ByteSet(_)));
        assert!(matches!(pref(vec!["ab", "baa", "", "cb"]), Ac(_, _)));
    }

    // TODO: test skipping
}

