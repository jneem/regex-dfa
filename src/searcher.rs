use memchr::memchr;

pub trait Searcher: Sized {
    fn search(&mut self, &str) -> Option<usize>;

    fn iter_str<'a>(self, input: &'a str) -> Iter<'a, Self> {
        Iter {
            searcher: self,
            input: input,
        }
    }
}

pub struct Iter<'a, S: Searcher> {
    searcher: S,
    input: &'a str,
}

impl<'a, S: Searcher> Iterator for Iter<'a, S> {
    type Item = &'a str;
    fn next(&mut self) -> Option<&'a str> {
        if let Some(pos) = self.searcher.search(self.input) {
            let ret = &self.input[pos..];

            // Move the input to point to the character after the matched one.
            if let Some((_, rest)) = ret.slice_shift_char() {
                self.input = rest;
            }
            Some(ret)
        } else {
            None
        }
    }
}

impl<F> Searcher for F where F: Fn(&str) -> Option<usize> {
    fn search(&mut self, s: &str) -> Option<usize> {
        self(s)
    }
}

pub struct MemchrSearcher {
    pub byte: u8,
}

impl Searcher for MemchrSearcher {
    fn search(&mut self, s: &str) -> Option<usize> {
        memchr(self.byte, s.as_bytes())
    }
}

pub struct AsciiTableSearcher {
    pub table: [bool; 256],
}

impl Searcher for AsciiTableSearcher {
    fn search(&mut self, s: &str) -> Option<usize> {
        s.as_bytes().iter().position(|b| self.table[*b as usize])
    }
}

pub struct MemchrAsciiTableSearcher {
    pub byte: u8,
    pub table: [bool; 256],
}

impl Searcher for MemchrAsciiTableSearcher {
    fn search(&mut self, mut s: &str) -> Option<usize> {
        let start_pos = s.as_bytes().as_ptr() as usize;
        while let Some(offset) = memchr(self.byte, s.as_bytes()) {
            if offset + 1 < s.len() {
                if self.table[s.as_bytes()[offset + 1] as usize] {
                    let match_pos = s.as_bytes().as_ptr() as usize + offset;
                    return Some(match_pos - start_pos);
                }
                s = &s[(offset + 1)..];
            } else {
                return None;
            }
        }
        None
    }
}

