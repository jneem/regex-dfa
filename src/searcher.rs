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
use ascii_set::AsciiSet;
use memchr::memchr;
use prefix::ExtAsciiSet;
use program::InitStates;

pub trait Skipper {
    fn skip(&self, s: &str, pos: usize, last_char: Option<char>) -> Option<(usize, usize, usize)>;
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
    input: &'a str,
    byte: u8,
    pos: usize,
    state: usize,
}

impl<'a> ByteIter<'a> {
    pub fn new(s: &'a str, b: u8, state: usize) -> ByteIter<'a> {
        if b >= 128 {
            panic!("can only use ASCII bytes");
        } else {
            ByteIter {
                input: s,
                byte: b,
                pos: 0,
                state: state,
            }
        }
    }
}

impl<'a> Iterator for ByteIter<'a> {
    type Item = (usize, usize, usize);

    fn next(&mut self) -> Option<(usize, usize, usize)> {
        let ret =
        memchr(self.byte, &self.input.as_bytes()[self.pos..])
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
    input: &'hay str,
    needle: &'needle str,
    pos: usize,
    state: usize,
}

impl<'hay, 'needle> StrIter<'hay, 'needle> {
    pub fn new(hay: &'hay str, needle: &'needle str, state: usize) -> StrIter<'hay, 'needle> {
        StrIter {
            input: hay,
            needle: needle,
            pos: 0,
            state: state,
        }
    }
}

impl<'hay, 'needle> Iterator for StrIter<'hay, 'needle> {
    type Item = (usize, usize, usize);

    fn next(&mut self) -> Option<(usize, usize, usize)> {
        if let Some(pos) = self.input[self.pos..].find(self.needle) {
            self.pos += pos;
            let ret = Some((self.pos, self.pos, self.state));
            self.pos += self.input.char_at(pos).len_utf8();
            ret
        } else {
            None
        }
    }
}

/// An iterator over all non-overlapping (but possibly empty) strings of chars belonging to a given
/// set. The second position is the one after the end of the match.
pub struct LoopIter<'a> {
    chars: ExtAsciiSet,
    input: &'a str,
    pos: usize,
    state: usize,
}

impl<'a> LoopIter<'a> {
    pub fn new(input: &'a str, chars: ExtAsciiSet, state: usize) -> LoopIter<'a> {
        LoopIter {
            chars: chars,
            input: input,
            pos: 0,
            state: state,
        }
    }
}

impl<'a> Iterator for LoopIter<'a> {
    type Item = (usize, usize, usize);

    fn next(&mut self) -> Option<(usize, usize, usize)> {
        if let Some(pos) = self.input.as_bytes()[self.pos..].iter()
                .position(|c| self.chars.contains_byte(*c)) {
            let ret = Some((self.pos, self.pos + pos, self.state));
            self.pos += pos + self.input.char_at(pos).len_utf8();
            ret
        } else {
            None
        }
    }
}

/// An iterator over all characters belonging to a certain ASCII set. The second position is the
/// position of the match.
pub struct AsciiSetIter<'a> {
    chars: AsciiSet,
    input: &'a str,
    pos: usize,
    state: usize,
}

impl<'a> AsciiSetIter<'a> {
    pub fn new(input: &'a str, chars: AsciiSet, state: usize) -> AsciiSetIter<'a> {
        AsciiSetIter {
            chars: chars,
            input: input,
            pos: 0,
            state: state,
        }
    }
}

impl<'a> Iterator for AsciiSetIter<'a> {
    type Item = (usize, usize, usize);

    fn next(&mut self) -> Option<(usize, usize, usize)> {
        if let Some(pos) = self.input.as_bytes()[self.pos..].iter()
                .position(|c| self.chars.contains_byte(*c)) {
            self.pos += pos + 1;
            Some((self.pos - 1, self.pos - 1, self.state))
        } else {
            None
        }
    }
}

pub struct NoSkipper<'a>(pub &'a InitStates);
impl<'a> Skipper for NoSkipper<'a> {
    fn skip(&self, s: &str, pos: usize, ch: Option<char>) -> Option<(usize, usize, usize)> {
        if let Some(state) = self.0.state_after(ch) {
            return Some((pos, pos, state));
        }
        for (offset, ch) in s[pos..].char_indices() {
            if let Some(state) = self.0.state_after(Some(ch)) {
                let ret_pos = pos + offset + ch.len_utf8();
                return Some((ret_pos, ret_pos, state));
            }
        }
        None
    }
}

pub struct SkipToByte(pub u8, pub usize);
impl Skipper for SkipToByte {
    fn skip(&self, s: &str, pos: usize, _: Option<char>) -> Option<(usize, usize, usize)> {
        if let Some(offset) = memchr(self.0, &s.as_bytes()[pos..]) {
            Some((pos + offset, pos + offset, self.1))
        } else {
            None
        }
    }
}

pub struct SkipToStr<'a>(pub &'a str, pub usize);
impl<'a> Skipper for SkipToStr<'a> {
    fn skip(&self, s: &str, pos: usize, _: Option<char>) -> Option<(usize, usize, usize)> {
        if let Some(offset) = s[pos..].find(self.0) {
            Some((pos + offset, pos + offset, self.1))
        } else {
            None
        }
    }
}

pub struct SkipToAsciiSet(pub AsciiSet, pub usize);
impl Skipper for SkipToAsciiSet {
    fn skip(&self, s: &str, pos: usize, _: Option<char>) -> Option<(usize, usize, usize)> {
        if let Some(offset) = s[pos..].as_bytes().iter().position(|c| self.0.contains_byte(*c)) {
            Some((pos + offset, pos + offset, self.1))
        } else {
            None
        }
    }
}

pub struct LoopSkipper(pub ExtAsciiSet, pub usize);
impl Skipper for LoopSkipper {
    fn skip(&self, s: &str, pos: usize, _: Option<char>) -> Option<(usize, usize, usize)> {
        if let Some(offset) = s[pos..].as_bytes().iter().position(|c| self.0.contains_byte(*c)) {
            Some((pos, pos + offset, self.1))
        } else {
            None
        }
    }
}

pub struct AcSkipper<'a>(pub &'a FullAcAutomaton<String>, pub usize);
impl<'a> Skipper for AcSkipper<'a> {
    fn skip(&self, s: &str, pos: usize, _: Option<char>) -> Option<(usize, usize, usize)> {
        if let Some(mat) = self.0.find(&s[pos..]).next() {
            Some((pos + mat.start, pos + mat.start, self.1))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ascii_set::AsciiSet;
    use prefix::ExtAsciiSet;

    #[test]
    fn test_byte_iter() {
        let bi = ByteIter::new("abcaba", 'a' as u8, 5);
        assert_eq!(bi.collect::<Vec<_>>(),
            vec![(0, 0, 5), (3, 3, 5), (5, 5, 5)]);
    }

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
}
