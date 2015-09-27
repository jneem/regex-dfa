use ascii_set::AsciiSet;
use memchr::memchr;

pub trait Searcher: Sized {
    fn search(&self, &str) -> Option<(usize, usize)>;

    fn iter<'a, 'b>(&'a self, input: &'b str) -> Iter<'a, 'b, Self> {
        Iter {
            searcher: self,
            input: input,
            pos: 0,
            overlapping: true,
        }
    }
}

pub trait Matcher {
    fn matches(&self, &str) -> Option<usize>;
}

#[derive(Clone, Debug)]
pub struct Iter<'a, 'b, S: Searcher + 'a> {
    searcher: &'a S,
    input: &'b str,
    pos: usize,
    overlapping: bool,
}

impl<'a, 'b, S: Searcher> Iterator for Iter<'a, 'b, S> {
    type Item = (usize, usize);
    fn next(&mut self) -> Option<(usize, usize)> {
        if self.pos <= self.input.len() {
            if let Some((start, end)) = self.searcher.search(&self.input[self.pos..]) {
                let ret = Some((self.pos + start, self.pos + end));

                // Advance the input. We always advance it by at least one byte. If it is currently
                // empty then we set it to None.
                self.pos += if self.overlapping || end == 0 {
                    if let &Some(ch) = &self.input[self.pos..].chars().next() {
                        ch.len_utf8()
                    } else {
                        1
                    }
                } else {
                    end
                };

                return ret;
            }
        }
        None
    }
}

#[derive(Clone, Debug)]
pub struct StrSearcher(pub String);

impl Searcher for StrSearcher {
    fn search(&self, s: &str) -> Option<(usize, usize)> {
        s.find(&self.0).map(|x| (x, x + self.0.len()))
    }
}

#[derive(Clone, Debug)]
pub struct ByteSearcher(pub u8);

impl Searcher for ByteSearcher {
    fn search(&self, s: &str) -> Option<(usize, usize)> {
        memchr(self.0, s.as_bytes()).map(|x| (x, x+1))
    }
}

/// Searchers for (non-overlapping) intervals that don't match `S`.
#[derive(Clone, Debug)]
pub struct RepeatUntil<S: Searcher>(pub S);

impl<S: Searcher> Searcher for RepeatUntil<S> {
    fn search(&self, s: &str) -> Option<(usize, usize)> {
        if let Some((start, _)) = self.0.search(s) {
            Some((0, start))
        } else {
            Some((0, s.len()))
        }
    }

    fn iter<'a, 'b>(&'a self, input: &'b str) -> Iter<'a, 'b, Self> {
        Iter {
            searcher: self,
            input: input,
            pos: 0,
            overlapping: false,
        }
    }
}

impl Matcher for AsciiSet {
    fn matches(&self, s: &str) -> Option<usize> {
        s.as_bytes()
            .first()
            .and_then(|b| if self.contains_byte(*b) { Some(1) } else { None })
    }
}

impl Searcher for AsciiSet {
    fn search(&self, s: &str) -> Option<(usize, usize)> {
        s.as_bytes().iter().position(|b| self.contains_byte(*b)).map(|x| (x, x+1))
    }
}

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

impl Matcher for ExtAsciiSet {
    fn matches(&self, s: &str) -> Option<usize> {
        s.as_bytes()
            .first()
            .and_then(|b| if self.contains_byte(*b) { Some(s.char_at(0).len_utf8()) } else { None })
    }
}

impl Searcher for ExtAsciiSet {
    fn search(&self, s: &str) -> Option<(usize, usize)> {
        s.as_bytes().iter()
            .position(|b| self.contains_byte(*b))
            .map(|x| (x, x + s.char_at(x).len_utf8()))
    }
}

#[derive(Clone, Debug)]
pub struct SearchThenMatch<S: Searcher, M: Matcher>(pub S, pub M);

impl<S: Searcher, M: Matcher> Searcher for SearchThenMatch<S, M> {
    fn search(&self, s: &str) -> Option<(usize, usize)> {
        let mut cur_pos = 0;
        while let Some((start, end_s)) = self.0.search(&s[cur_pos..]) {
            if let Some(end_m) = self.1.matches(&s[(cur_pos + end_s)..]) {
                return Some((cur_pos + start, cur_pos + end_m))
            }
            cur_pos += end_s;
        }
        None
    }
}

