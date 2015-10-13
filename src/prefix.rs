// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use aho_corasick::{Automaton, AcAutomaton, FullAcAutomaton};
use ascii_set::AsciiSet;
use char_map::CharMap;
use program::Program;
use std;
use std::cmp::Ordering;
use std::collections::BinaryHeap;

// TODO: these limits are pretty arbitrary (just copied from the regex crate).
const NUM_PREFIX_LIMIT: usize = 30;
const PREFIX_LEN_LIMIT: usize = 15;

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
pub enum Prefix {
    Empty,
    AsciiChar(AsciiSet, usize),
    Byte(u8, usize),
    Lit(String, usize),
    Ac(FullAcAutomaton<String>, Vec<usize>),
    LoopUntil(ExtAsciiSet, usize),
}

impl Prefix {
    pub fn extract(prog: &Program) -> Prefix {
        use program::Inst::*;

        if let Some(state) = prog.init.constant() {
            let mut prefixes = PrefixSearcher::new(NUM_PREFIX_LIMIT, PREFIX_LEN_LIMIT);
            prefixes.search(prog, state);
            if let Some(lit) = prefixes.to_lit() {
                if lit.len() == 1 {
                    return Prefix::Byte(lit.as_bytes()[0], state);
                } else if lit.len() >= 2 {
                    return Prefix::Lit(lit.clone(), state);
                }
            } else if let Some((ac, state_map)) = prefixes.to_ac() {
                return Prefix::Ac(ac, state_map);
            }

            match prog.insts[state] {
                CharSet(ref cs) => {
                    if cs.is_ascii() {
                        return Prefix::AsciiChar(cs.to_ascii_set(), state);
                    }
                },
                Branch(ref cm) => {
                    if let Some(cs) = loop_optimization(cm, state) {
                        return Prefix::LoopUntil(cs.complement(), state);
                    }
                    let cs = cm.to_char_set();
                    if cs.is_ascii() {
                        if cs.char_count() == 1 {
                            let &(range, state) = cm.iter().next().unwrap();
                            return Prefix::Byte(range.start as u8, state);
                        }
                        return Prefix::AsciiChar(cs.to_ascii_set(), state);
                    }
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
struct PrefixPart(pub String, pub usize);
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
            current: PrefixPart(String::new(), 0),
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

        self.active.push(PrefixPart(String::new(), state));
        while !self.active.is_empty() {
            self.current = self.active.pop().unwrap();
            match prog.insts[self.current.1] {
                Char(c) => {
                    let mut next_pref = self.current.0.clone();
                    next_pref.push(c);
                    let next_pref = PrefixPart(next_pref, self.current.1 + 1);
                    if self.add(vec![next_pref]) {
                        break;
                    }
                },
                CharSet(ref cs) => {
                    if self.too_many(cs.char_count() as usize) {
                        break;
                    }
                    let next_prefs = cs.chars()
                        .filter_map(std::char::from_u32)
                        .map(|c| {
                            let mut next_str = self.current.0.clone();
                            next_str.push(c);
                            PrefixPart(next_str, self.current.1 + 1)
                        }).collect();
                    if self.add(next_prefs) {
                        break;
                    }
                },
                Acc(ref acc) => {
                    self.finished.push(self.current.clone());
                    if !acc.is_always() {
                        self.complete = false;
                    }
                },
                Branch(ref cm) => {
                    if self.too_many(cm.to_char_set().char_count() as usize) {
                        break;
                    }
                    let next_prefs = cm.pairs().into_iter()
                        .filter_map(|x| std::char::from_u32(x.0).map(|c| (c, x.1)))
                        .map(|(c, tgt)| {
                            let mut next_str = self.current.0.clone();
                            next_str.push(c);
                            PrefixPart(next_str, tgt)
                        }).collect();
                    if self.add(next_prefs) {
                        break;
                    }
                },
            }
        }
    }

    fn to_ac(&self) -> Option<(FullAcAutomaton<String>, Vec<usize>)> {
        if self.finished.len() <= 1
                || self.finished.iter().any(|s| s.0.is_empty())
                || self.finished.iter().all(|s| s.0.len() <= 1) {
            None
        } else {
            let strings: Vec<String> = self.finished.iter().map(|x| x.0.clone()).collect();
            let auto = FullAcAutomaton::new(AcAutomaton::new(strings));
            let map: Vec<usize> = self.finished.iter().map(|x| x.1).collect();
            Some((auto, map))
        }
    }

    fn to_lit(&self) -> Option<String> {
        if self.finished.len() == 1 {
            Some(self.finished[0].0.clone())
        } else {
            None
        }
    }

}

// Given the transitions at state index `st_idx`, checks to see if we should insert a loop
// searcher. If so, returns the lookup table and also the remaining transitions.
fn loop_optimization(cm: &CharMap<usize>, st_idx: usize) -> Option<ExtAsciiSet> {
    let loop_cs = cm.filter_values(|st| *st == st_idx).to_char_set();
    if !loop_cs.is_empty() && (loop_cs.is_ascii() || loop_cs.contains_non_ascii()) {
        let set = loop_cs.to_ascii_set();
        let set = ExtAsciiSet { set: set, contains_non_ascii: loop_cs.contains_non_ascii() };
        Some(set)
    } else {
        None
    }
}


