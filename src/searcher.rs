// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
This module provides functions for quickly skipping through the haystack, looking for places that
might conceivably be the start of a match. Just about everything in this module is an iterator over
`(usize, usize, usize)` triples.

  - The first `usize` is the index where the match begun. If this does turn out to be a match, the
    DFA should report the match as beginning here. This should always be at a character boundary.
  - The second `usize` is the index that the DFA should begin matching from. This could be
    different from the first index because we might already know what state the DFA would be in
    if it encountered the prefix we found. In that case, there is no need for the DFA to go back
    and re-examine the prefix. This should always be at a character boundary.
  - The third `usize` is the state that the DFA should start in.
 */

use aho_corasick::{Automaton, FullAcAutomaton};
use bytes::ByteSet;
use memchr::memchr;
use memmem::{Searcher, TwoWaySearcher};
use program::InitStates;
use std;

pub trait Skipper {
    fn skip(&self, s: &[u8], pos: usize) -> Option<(usize, usize, usize)>;
}

/* TODO: see whether specialization gives better performance than boxing. If it doesn't
 * go back to this implementation instead of the one in threaded.
impl Skipper {
    pub fn from_prefix<'a, 'b>(p: &'a Prefix, init: &'b InitStates) -> Box<Skipper + 'a + 'b> {
        use prefix::Prefix::*;

        match *p {
            Empty => Box::new(NoSkipper(init)),
            AsciiChar(ref set, _) => Box::new(SkipToAsciiSet(set.clone(), state)),
            Byte(b, _) => Box::new(SkipToByte(b)),
            Lit(ref s, _) => Box::new(SkipToStr(&s)),
            Ac(ref ac, _) => Box::new(AcSkipper(ac)),
            LoopUntil(ref set, _) => Box::new(LoopSkipper(set.clone())),
        }
    }
}
*/

/// An iterator that searchest for a given byte. The second position is position of the byte.
pub struct ByteIter<'a> {
    input: &'a [u8],
    byte: u8,
    pos: usize,
    state: usize,
}

impl<'a> ByteIter<'a> {
    pub fn new(s: &'a [u8], b: u8, state: usize) -> ByteIter<'a> {
        ByteIter {
            input: s,
            byte: b,
            pos: 0,
            state: state,
        }
    }
}

impl<'a> Iterator for ByteIter<'a> {
    type Item = (usize, usize, usize);

    fn next(&mut self) -> Option<(usize, usize, usize)> {
        let ret =
        memchr(self.byte, &self.input[self.pos..])
            .map(|pos| {
                self.pos += pos + 1;
                (self.pos - 1, self.pos - 1, self.state)
            });
        ret
    }
}

/// An iterator over (possibly overlapping) matches of a string. The second position is the one
/// at the start of the match.
pub struct StrIter<'hay, 'needle> {
    input: &'hay [u8],
    searcher: TwoWaySearcher<'needle>,
    pos: usize,
    state: usize,
}

impl<'hay, 'needle> StrIter<'hay, 'needle> {
    pub fn new(hay: &'hay [u8], needle: &'needle [u8], state: usize) -> StrIter<'hay, 'needle> {
        StrIter {
            input: hay,
            searcher: TwoWaySearcher::new(needle),
            pos: 0,
            state: state,
        }
    }
}

impl<'hay, 'needle> Iterator for StrIter<'hay, 'needle> {
    type Item = (usize, usize, usize);

    fn next(&mut self) -> Option<(usize, usize, usize)> {
        if let Some(pos) = self.searcher.search_in(&self.input[self.pos..]) {
            let ret = Some((self.pos + pos, self.pos + pos, self.state));
            self.pos += pos + 1;
            ret
        } else {
            None
        }
    }
}

/// An iterator over all non-overlapping (but possibly empty) strings of chars belonging to a given
/// set. The second position is the one after the end of the match.
pub struct LoopIter<'a, 'b> {
    input: &'a [u8],
    bytes: &'b ByteSet,
    pos: usize,
    state: usize,
}

impl<'a, 'b> LoopIter<'a, 'b> {
    pub fn new(input: &'a [u8], bytes: &'b ByteSet, state: usize) -> LoopIter<'a, 'b> {
        LoopIter {
            input: input,
            bytes: bytes,
            pos: 0,
            state: state,
        }
    }
}

impl<'a, 'b> Iterator for LoopIter<'a, 'b> {
    type Item = (usize, usize, usize);

    fn next(&mut self) -> Option<(usize, usize, usize)> {
        if let Some(pos) = self.input[self.pos..].iter()
                .position(|c| !self.bytes.0[*c as usize]) {
            let ret = Some((self.pos, self.pos + pos, self.state));
            self.pos += pos + 1;
            ret
        } else {
            None
        }
    }
}

/// An iterator over all characters belonging to a certain set of bytes. The second position is the
/// position of the match.
pub struct ByteSetIter<'a, 'b> {
    input: &'a [u8],
    bytes: &'b ByteSet,
    pos: usize,
    state: usize,
}

impl<'a, 'b> ByteSetIter<'a, 'b> {
    pub fn new(input: &'a [u8], bytes: &'b ByteSet, state: usize) -> ByteSetIter<'a, 'b> {
        ByteSetIter {
            input: input,
            bytes: bytes,
            pos: 0,
            state: state,
        }
    }
}

impl<'a, 'b> Iterator for ByteSetIter<'a, 'b> {
    type Item = (usize, usize, usize);

    fn next(&mut self) -> Option<(usize, usize, usize)> {
        if let Some(pos) = self.input[self.pos..].iter()
                .position(|c| self.bytes.0[*c as usize]) {
            self.pos += pos + 1;
            Some((self.pos - 1, self.pos - 1, self.state))
        } else {
            None
        }
    }
}

pub struct NoSkipper<'a>(pub &'a InitStates);
impl<'a> Skipper for NoSkipper<'a> {
    fn skip(&self, s: &[u8], pos: usize) -> Option<(usize, usize, usize)> {
        for pos in pos..s.len() {
            if let Some(state) = self.0.state_at_pos(s, pos) {
                return Some((pos, pos, state));
            }
        }
        None
    }
}

pub struct SkipToByte(pub u8, pub usize);
impl Skipper for SkipToByte {
    fn skip(&self, s: &[u8], pos: usize) -> Option<(usize, usize, usize)> {
        if let Some(offset) = memchr(self.0, &s[pos..]) {
            Some((pos + offset, pos + offset, self.1))
        } else {
            None
        }
    }
}

pub struct SkipToStr<'a>(pub TwoWaySearcher<'a>, pub usize);
impl<'a> SkipToStr<'a> {
    pub fn new(needle: &'a [u8], state: usize) -> SkipToStr<'a> {
        SkipToStr(TwoWaySearcher::new(needle), state)
    }
}
impl<'a> Skipper for SkipToStr<'a> {
    fn skip(&self, hay: &[u8], pos: usize) -> Option<(usize, usize, usize)> {
        if let Some(offset) = self.0.search_in(&hay[pos..]) {
            Some((pos + offset, pos + offset, self.1))
        } else {
            None
        }
    }
}

pub struct SkipToByteSet<'a>(pub &'a ByteSet, pub usize);
impl<'a> Skipper for SkipToByteSet<'a> {
    fn skip(&self, s: &[u8], pos: usize) -> Option<(usize, usize, usize)> {
        if let Some(offset) = s[pos..].iter().position(|c| (self.0).0[*c as usize]) {
            Some((pos + offset, pos + offset, self.1))
        } else {
            None
        }
    }
}

pub struct LoopSkipper<'a>(pub &'a ByteSet, pub usize);
impl<'a> Skipper for LoopSkipper<'a> {
    fn skip(&self, s: &[u8], pos: usize) -> Option<(usize, usize, usize)> {
        if let Some(offset) = s[pos..].iter().position(|c| !(self.0).0[*c as usize]) {
            Some((pos, pos + offset, self.1))
        } else {
            None
        }
    }
}

pub struct AcSkipper<'a>(pub &'a FullAcAutomaton<Vec<u8>>, pub usize);
impl<'a> Skipper for AcSkipper<'a> {
    fn skip(&self, s: &[u8], pos: usize) -> Option<(usize, usize, usize)> {
        let ac_input = unsafe { std::str::from_utf8_unchecked(&s[pos..]) };
        if let Some(mat) = self.0.find(ac_input).next() {
            Some((pos + mat.start, pos + mat.start, self.1))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    //use prefix::ExtAsciiSet;

    #[test]
    fn test_byte_iter() {
        let bi = ByteIter::new("abcaba".as_bytes(), 'a' as u8, 5);
        assert_eq!(bi.collect::<Vec<_>>(),
            vec![(0, 0, 5), (3, 3, 5), (5, 5, 5)]);
    }

    /*
    #[test]
    fn test_str_iter() {
        let si = StrIter::new("abcaba", "ab", 5);
        assert_eq!(si.collect::<Vec<_>>(),
            vec![(0, 0, 5), (3, 3, 5)]);

        let si = StrIter::new("aaaa", "aa", 5);
        assert_eq!(si.collect::<Vec<_>>(),
            vec![(0, 0, 5), (1, 1, 5), (2, 2, 5)]);
    }

    #[test]
    fn test_loop_iter() {
        let cs = ExtAsciiSet {
            set: AsciiSet::from_chars("b".chars()),
            contains_non_ascii: false,
        };
        let li = LoopIter::new("baaababaa", cs, 5);
        assert_eq!(li.collect::<Vec<_>>(),
            vec![(0, 0, 5), (1, 4, 5), (5, 6, 5)]);
    }

    #[test]
    fn test_ascii_set_iter() {
        let cs = AsciiSet::from_chars("ac".chars());
        let asi = AsciiSetIter::new("abcba", cs, 5);
        assert_eq!(asi.collect::<Vec<_>>(),
            vec![(0, 0, 5), (2, 2, 5), (4, 4, 5)]);
    }
    */
}
