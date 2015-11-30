// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use aho_corasick::{Automaton, AcAutomaton, FullAcAutomaton};
use bytes::ByteSet;
use dfa::Dfa;
use range_map::RangeMap;
use std::collections::VecDeque;

// TODO: these limits are pretty arbitrary (just copied from the regex crate).
const NUM_PREFIX_LIMIT: usize = 30;
const PREFIX_LEN_LIMIT: usize = 15;

#[derive(Clone, Debug)]
pub enum Prefix {
    Empty,
    ByteSet(ByteSet, usize),
    Byte(u8, usize),
    Lit(Vec<u8>, usize),
    Ac(FullAcAutomaton<Vec<u8>>, Vec<usize>),
    LoopWhile(ByteSet, usize),
}

impl Prefix {
    pub fn extract(dfa: &Dfa) -> Prefix {
        if let Some(state) = dfa.simple_init() {
            let mut prefixes = PrefixSearcher::new(NUM_PREFIX_LIMIT, PREFIX_LEN_LIMIT);
            prefixes.search(dfa, state);
            if let Some(lit) = prefixes.to_lit() {
                if lit.len() == 1 {
                    return Prefix::Byte(lit[0], state);
                } else {
                    return Prefix::Lit(lit, state);
                }
            }
            if let Some((ac, state_map)) = prefixes.to_ac() {
                return Prefix::Ac(ac, state_map);
            }

            let first_trans = dfa.transitions(state);

            if dfa.accept(state).is_never() {
                if let Some(bs) = loop_optimization(first_trans, state) {
                    return Prefix::LoopWhile(bs, state);
                }
            }
            if first_trans.num_keys() > 1 {
                return Prefix::ByteSet(ByteSet::from_range_set(&first_trans.to_range_set()), state);
            }
        }

        Prefix::Empty
    }

    pub fn map_states<F>(&mut self, mut f: F) where F: FnMut(usize) -> usize {
        use prefix::Prefix::*;

        match *self {
            Empty => {},
            ByteSet(_, ref mut st) => *st = f(*st),
            Byte(_, ref mut st) => *st = f(*st),
            Lit(_, ref mut st) => *st = f(*st),
            LoopWhile(_, ref mut st) => *st = f(*st),
            Ac(_, ref mut sts) => {
                for st in sts {
                    *st = f(*st);
                }
            },
        }
    }
}

/// A pair of a byte sequence and the index of the state that we are in after encountering that
/// sequence.
#[derive(Debug, Clone)]
struct PrefixPart(pub Vec<u8>, pub usize);

struct PrefixSearcher {
    active: VecDeque<PrefixPart>,
    current: PrefixPart,
    finished: Vec<PrefixPart>,

    // The set of prefixes is complete if:
    //  - we're done with active prefixes before we go over any of our limits, and
    //  - we didn't encounter any states that accept conditionally.
    complete: bool,

    max_prefixes: usize,
    max_len: usize,
}

impl PrefixSearcher {
    fn new(max_prefixes: usize, max_len: usize) -> PrefixSearcher {
        PrefixSearcher {
            active: VecDeque::new(),
            current: PrefixPart(Vec::new(), 0),
            finished: Vec::new(),
            complete: true,
            max_prefixes: max_prefixes,
            max_len: max_len,
        }
    }

    fn bail_out(&mut self) {
        // TODO: unnecessary clones
        self.finished.extend(self.active.iter().cloned());
        self.finished.push(self.current.clone());
        self.complete = false;
    }

    fn add(&mut self, new_prefs: Vec<PrefixPart>) {
        debug_assert!(new_prefs.len() + self.active.len() + self.finished.len() <= self.max_prefixes);

        for p in new_prefs.into_iter() {
            if p.0.len() >= self.max_len {
                self.finished.push(p);
            } else {
                self.active.push_back(p);
            }
        }
    }

    fn too_many(&mut self, more: usize) -> bool {
        self.active.len() + self.finished.len() + more > self.max_prefixes
    }

    fn search(&mut self, dfa: &Dfa, state: usize) {
        self.active.push_back(PrefixPart(Vec::new(), state));
        while !self.active.is_empty() {
            self.current = self.active.pop_front().unwrap();
            let trans = dfa.transitions(self.current.1);

            // Stop searching if we have too many prefixes already, or if we've run into an accept
            // state. In principle, we could continue expanding the other prefixes even after we
            // run into an accept state, but there doesn't seem much point in having some short
            // prefixes and other long prefixes.
            if self.too_many(trans.num_keys() as usize) || !dfa.accept(self.current.1).is_never() {
                self.bail_out();
                break;
            }

            let mut next_prefs = Vec::new();
            for (ch, next_state) in trans.keys_values() {
                let mut next_pref = self.current.0.clone();
                next_pref.push(ch);
                next_prefs.push(PrefixPart(next_pref, *next_state));
            }

            self.add(next_prefs);
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
        if self.finished.len() == 1 && !self.finished[0].0.is_empty() {
            Some(self.finished[0].0.clone())
        } else {
            None
        }
    }

}

// Given the transitions at state index `st_idx`, checks to see if we should insert a loop
// searcher. If so, returns the set of bytes that are part of the loop.
//
// Note that the set of bytes we return is guaranteed to contain all or none of the non-ascii
// bytes. Thus, if we start searching at a character boundary then we are guaranteed to stop
// at a character boundary also.
fn loop_optimization(map: &RangeMap<u8, usize>, st_idx: usize) -> Option<ByteSet> {
    if map.ranges_values().any(|x| x.1 == st_idx) {
        let mut loop_chars = map.clone();
        loop_chars.retain_values(|s| *s == st_idx);
        let loop_chars = loop_chars.to_range_set();
        Some(ByteSet::from_range_set(&loop_chars))
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
            let dfa = Dfa::from_regex_bounded(s, 100).unwrap();
            println!("{:?}", dfa);
            let ret = Prefix::extract(&dfa);
            println!("{:?}", ret);
            ret
        }

        fn is_byte(p: &Prefix) -> bool {
            if let &Prefix::Byte(_, _) = p { true } else { false }
        }
        fn is_lit(p: &Prefix) -> bool {
            if let &Prefix::Lit(_, _) = p { true } else { false }
        }
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
        assert!(is_lit(&regex_prefix("abc.*b")));
        assert!(is_loop(&regex_prefix(".*abc")));
        assert!(is_ac(&regex_prefix("[XYZ]ABCDEFGHIJKLMNOPQRSTUVWXYZ$")));
        assert!(is_set(&regex_prefix("[ab].*cd")));
        assert!(is_set(&regex_prefix("(f.*f|b.*b)")));
    }

    #[test]
    fn test_prefixes() {
        fn test_prefix(re_str: &str, answer: Vec<&str>, max_num: usize, max_len: usize) {
            let dfa = Dfa::from_regex_bounded(re_str, 100).unwrap();
            let mut pref = PrefixSearcher::new(max_num, max_len);
            pref.search(&dfa, dfa.simple_init().unwrap());
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

