// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use aho_corasick::Automaton;
use engine::Engine;
use prefix::Prefix;
use program::Program;
// TODO: rename to skipper
use searcher::{AsciiSetIter, ByteIter, LoopIter, StrIter};

#[derive(Clone, Debug)]
pub struct BacktrackingEngine {
    prog: Program,
    prefix: Prefix,
}

impl BacktrackingEngine {
    pub fn new(prog: Program) -> BacktrackingEngine {
        let pref = Prefix::extract(&prog);
        BacktrackingEngine {
            prog: prog,
            prefix: pref,
        }
    }

    fn shortest_match_from<'a>(&self, s: &'a str, mut state: usize) -> Option<usize> {
        let mut chars = s.char_indices().peekable();
        let mut next = chars.next();
        while let Some((pos, ch)) = next {
            let (next_state, accepted, retry) = self.prog.step(state, ch);
            if accepted {
                return Some(pos);
            } else if let Some(next_state) = next_state {
                state = next_state;
                if !retry {
                    next = chars.next();
                }
            } else {
                return None;
            }
        }

        if self.prog.check_eoi(state) {
            Some(s.len())
        } else {
            None
        }
    }

    /// `positions` iterates over `(prefix_start, prog_start, state)`
    fn shortest_match_from_iter<I>(&self, input: &str, positions: I) -> Option<(usize, usize)>
        where I: Iterator<Item=(usize, usize, usize)>
    {
        for (pref_start, prog_start, state) in positions {
            if let Some(end) = self.shortest_match_from(&input[prog_start..], state) {
                return Some((pref_start, prog_start + end));
            }
        }
        None
    }


    fn shortest_match_slow(&self, s: &str) -> Option<(usize, usize)> {
        if let Some(state) = self.prog.init.init_at_start {
            if let Some(end) = self.shortest_match_from(s, state) {
                return Some((0, end))
            }
        }

        // Skip looping through the string if we know that the match has to start
        // at the beginning.
        if self.prog.init.init_otherwise.is_none() && self.prog.init.init_after_char.is_empty() {
            return None;
        }

        let mut pos: usize = 0;
        for ch in s.chars() {
            pos += ch.len_utf8();

            if let Some(state) = self.prog.init.state_after(Some(ch)) {
                if let Some(end) = self.shortest_match_from(&s[pos..], state) {
                    return Some((pos, pos + end));
                }
            }
        }

        None
    }
}

impl Engine for BacktrackingEngine {
    fn shortest_match(&self, s: &str) -> Option<(usize, usize)> {
        if self.prog.insts.is_empty() {
            return None;
        }

        match self.prefix {
            Prefix::AsciiChar(ref cs, state) =>
                self.shortest_match_from_iter(s, AsciiSetIter::new(s, cs.clone(), state)),
            Prefix::Byte(b, state) =>
                self.shortest_match_from_iter(s, ByteIter::new(s, b, state)),
            Prefix::Lit(ref lit, state) =>
                self.shortest_match_from_iter(s, StrIter::new(s, lit, state)),
            Prefix::Ac(ref ac, ref state_table) => {
                let iter = ac.find_overlapping(s).map(|m| (m.start, m.end, state_table[m.pati]));
                self.shortest_match_from_iter(s, iter)
            },
            Prefix::LoopUntil(ref cs, state) =>
                self.shortest_match_from_iter(s, LoopIter::new(s, cs.clone(), state)),
            Prefix::Empty => self.shortest_match_slow(s),
        }
    }

    fn clone_box(&self) -> Box<Engine> {
        Box::new(self.clone())
    }
}
