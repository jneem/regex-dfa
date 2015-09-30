use aho_corasick::FullAcAutomaton;
use ascii_set::AsciiSet;
use memchr::memchr;

/// A set of chars that either is entirely ASCII or else contains every non-ASCII char.
#[derive(Clone, Debug, PartialEq)]
pub struct ExtAsciiSet {
    pub set: AsciiSet,
    pub contains_non_ascii: bool,
}

impl ExtAsciiSet {
    pub fn contains_byte(&self, b: u8) -> bool {
        if self.contains_non_ascii {
            b >= 128 || self.set.contains_byte(b)
        } else {
            self.set.contains_byte(b)
        }
    }

    pub fn complement(&self) -> ExtAsciiSet {
        ExtAsciiSet {
            set: self.set.complement(),
            contains_non_ascii: !self.contains_non_ascii,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Search {
    Empty,
    AsciiChar(AsciiSet, usize),
    Byte(u8, usize),
    Lit(String, usize),
    Ac(FullAcAutomaton<String>, Vec<usize>),
    LoopUntil(ExtAsciiSet, usize),
}

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
        memchr(self.byte, &self.input.as_bytes()[self.pos..])
            .map(|pos| {
                self.pos = pos + 1;
                (pos, pos + 1, self.state)
            })
    }
}

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
            let ret = Some((self.pos, self.pos + self.needle.len(), self.state));
            self.pos += self.input.char_at(pos).len_utf8();
            ret
        } else {
            None
        }
    }
}

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
            let ret = Some((pos, pos, self.state));
            self.pos += pos + 1;
            ret
        } else {
            None
        }
    }
}

