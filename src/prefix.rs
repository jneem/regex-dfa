// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use aho_corasick::{Automaton, AcAutomaton, FullAcAutomaton};
use bytes::{ByteMap, ByteSet};
use program::Program;
use std::cmp::Ordering;
use std::collections::BinaryHeap;

// TODO: these limits are pretty arbitrary (just copied from the regex crate).
const NUM_PREFIX_LIMIT: usize = 30;
const PREFIX_LEN_LIMIT: usize = 15;

#[derive(Clone, Debug)]
pub enum Prefix {
    Empty,
    ByteSet(ByteSet, usize),
    Byte(u8, usize),
    //Lit(String, usize),
    Ac(FullAcAutomaton<Vec<u8>>, Vec<usize>),
    LoopWhile(ByteSet, usize),
}

impl Prefix {
    // TODO: extract from the Dfa instead of the Program.
    pub fn extract(prog: &Program) -> Prefix {
        use program::Inst::*;

        if let Some(state) = prog.init.constant() {
            let mut prefixes = PrefixSearcher::new(NUM_PREFIX_LIMIT, PREFIX_LEN_LIMIT);
            prefixes.search(prog, state);
            if let Some(lit) = prefixes.to_lit() {
                if lit.len() == 1 {
                    return Prefix::Byte(lit[0], state);
                }
            }
            if let Some((ac, state_map)) = prefixes.to_ac() {
                return Prefix::Ac(ac, state_map);
            }

            match prog.insts[state] {
                ByteSet(ref bs) => {
                    return Prefix::ByteSet(bs.clone(), state);
                },
                Branch(ref bm) => {
                    if let Some(bs) = loop_optimization(bm, state) {
                        return Prefix::LoopWhile(bs, state);
                    }
                    if bm.len() == 1 {
                        let (b, state) = bm.into_iter().next().unwrap();
                        return Prefix::Byte(b, state as usize);
                    }
                    return Prefix::ByteSet(bm.to_set(), state);
                },
                _ => {},
            }
        }

        Prefix::Empty
    }
}

/// A pair of a `String` and the index of the state that we are in after encountering that string.
///
/// Prefixes are ordered by the decreasing length of their string.
#[derive(Debug, Clone)]
struct PrefixPart(pub Vec<u8>, pub usize);
impl PartialOrd for PrefixPart {
    fn partial_cmp(&self, other: &PrefixPart) -> Option<Ordering> {
        self.0.len().partial_cmp(&other.0.len()).map(|x| x.reverse())
    }
}

impl Ord for PrefixPart {
    fn cmp(&self, other: &PrefixPart) -> Ordering {
        self.partial_cmp(&other).unwrap().reverse()
    }
}

impl PartialEq for PrefixPart {
    fn eq(&self, other: &PrefixPart) -> bool {
        self.0.len().eq(&other.0.len())
    }
}

impl Eq for PrefixPart { }


struct PrefixSearcher {
    active: BinaryHeap<PrefixPart>,
    current: PrefixPart,
    finished: Vec<PrefixPart>,

    // The set of prefixes is complete if:
    //  - we're done with active prefixes before we go over any of our limits, and
    //  - we didn't encounter any conditional accept statements.
    complete: bool,

    max_prefixes: usize,
    max_len: usize,
}

impl PrefixSearcher {
    fn new(max_prefixes: usize, max_len: usize) -> PrefixSearcher {
        PrefixSearcher {
            active: BinaryHeap::new(),
            current: PrefixPart(Vec::new(), 0),
            finished: Vec::new(),
            complete: true,
            max_prefixes: max_prefixes,
            max_len: max_len,
        }
    }

    fn bail_out(&mut self) {
        self.finished.extend(self.active.iter().cloned());
        self.finished.push(self.current.clone());
        self.complete = false;
    }

    // Returns true if we bailed out.
    fn add(&mut self, new_prefs: Vec<PrefixPart>) -> bool {
        if new_prefs.len() + self.active.len() + self.finished.len() > self.max_prefixes {
            self.bail_out();
            true
        } else {
            for p in new_prefs.into_iter() {
                if p.0.len() >= self.max_len {
                    self.finished.push(p);
                } else {
                    self.active.push(p);
                }
            }
            false
        }
    }

    fn too_many(&mut self, more: usize) -> bool {
        if self.active.len() + self.finished.len() + more > self.max_prefixes {
            self.bail_out();
            true
        } else {
            false
        }
    }

    fn search(&mut self, prog: &Program, state: usize) {
        use program::Inst::*;

        self.active.push(PrefixPart(Vec::new(), state));
        while !self.active.is_empty() {
            self.current = self.active.pop().unwrap();
            match prog.insts[self.current.1] {
                Byte(b) => {
                    let mut next_pref = self.current.0.clone();
                    next_pref.push(b);
                    let next_pref = PrefixPart(next_pref, self.current.1 + 1);
                    if self.add(vec![next_pref]) {
                        break;
                    }
                },
                ByteSet(ref bs) => {
                    if self.too_many(bs.len()) {
                        break;
                    }
                    let next_prefs = bs.into_iter()
                        .map(|b| {
                            let mut next_str = self.current.0.clone();
                            next_str.push(b);
                            PrefixPart(next_str, self.current.1 + 1)
                        }).collect();
                    if self.add(next_prefs) {
                        break;
                    }
                },
                Acc(_) => {
                    self.finished.push(self.current.clone());
                },
                Branch(ref bm) => {
                    if self.too_many(bm.len()) {
                        break;
                    }
                    let next_prefs = bm.into_iter()
                        .map(|(b, tgt)| {
                            let mut next_str = self.current.0.clone();
                            next_str.push(b);
                            PrefixPart(next_str, tgt as usize)
                        }).collect();
                    if self.add(next_prefs) {
                        break;
                    }
                },
            }
        }
    }

    fn to_ac(&self) -> Option<(FullAcAutomaton<Vec<u8>>, Vec<usize>)> {
        if self.finished.is_empty()
                || self.finished.iter().any(|s| s.0.is_empty())
                || self.finished.iter().all(|s| s.0.len() <= 1) {
            None
        } else {
            let strings: Vec<Vec<u8>> = self.finished.iter().map(|x| x.0.clone()).collect();
            let auto = FullAcAutomaton::new(AcAutomaton::new(strings));
            let map: Vec<usize> = self.finished.iter().map(|x| x.1).collect();
            Some((auto, map))
        }
    }

    fn to_lit(&self) -> Option<Vec<u8>> {
        if self.finished.len() == 1 {
            Some(self.finished[0].0.clone())
        } else {
            None
        }
    }

}

// Given the transitions at state index `st_idx`, checks to see if we should insert a loop
// searcher. If so, returns the set of characters that are part of the loop.
fn loop_optimization(bm: &ByteMap, st_idx: usize) -> Option<ByteSet> {
    if bm.into_iter().any(|x| x.1 as usize == st_idx) {
        Some(bm.filter_values(|s| s as usize == st_idx))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use dfa::Dfa;
    use prefix::{Prefix, PrefixSearcher};

    #[test]
    fn test_search_choice() {
        fn regex_prefix(s: &str) -> Prefix {
            let prog = Dfa::from_regex_bounded(s, 100).unwrap().to_program();
            println!("{:?}", prog);
            Prefix::extract(&prog)
        }

        fn is_byte(p: &Prefix) -> bool {
            if let &Prefix::Byte(_, _) = p { true } else { false }
        }
        /*
        fn is_lit(p: &Prefix) -> bool {
            if let &Prefix::Lit(_, _) = p { true } else { false }
        }
        */
        fn is_loop(p: &Prefix) -> bool {
            if let &Prefix::LoopWhile(_, _) = p { true } else { false }
        }
        fn is_ac(p: &Prefix) -> bool {
            if let &Prefix::Ac(_, _) = p { true } else { false }
        }
        fn is_set(p: &Prefix) -> bool {
            if let &Prefix::ByteSet(_, _) = p { true } else { false }
        }

        assert!(is_byte(&regex_prefix("a.*b")));
        assert!(is_ac(&regex_prefix("abc.*b")));
        assert!(is_loop(&regex_prefix(".*abc")));
        assert!(is_ac(&regex_prefix("[XYZ]ABCDEFGHIJKLMNOPQRSTUVWXYZ$")));
        assert!(is_set(&regex_prefix("[ab].*cd")));
        assert!(is_set(&regex_prefix("(f.*f|b.*b)")));
    }

    #[test]
    fn test_prefixes() {
        fn test_prefix(re_str: &str, answer: Vec<&str>, max_num: usize, max_len: usize) {
            let re = Dfa::from_regex_bounded(re_str, 100).unwrap().to_program();
            let mut pref = PrefixSearcher::new(max_num, max_len);
            pref.search(&re, re.init.init_otherwise.unwrap());
            let mut prefs = pref.finished.into_iter().map(|x| x.0).collect::<Vec<_>>();
            prefs.sort();

            let answer: Vec<Vec<u8>> =
                answer
                    .iter()
                    .map(|s| s.as_bytes().to_owned())
                    .collect();
            assert_eq!(prefs, answer);
        }

        test_prefix("[XYZ]ABCDEFGHIJKLMNOPQRSTUVWXYZ",
            vec!["XABCDEFGHIJKLMNOPQRSTUVWXYZ",
               "YABCDEFGHIJKLMNOPQRSTUVWXYZ",
               "ZABCDEFGHIJKLMNOPQRSTUVWXYZ",],
            3, 30);

        test_prefix("(?i)abc[a-z]",
            vec!["ABC", "ABc", "AbC", "Abc", "aBC", "aBc", "abC", "abc"],
            30, 5);
    }
}

