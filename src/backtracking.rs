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
use searcher::{ByteSetIter, ByteIter, LoopIter, StrIter};
use std;

#[derive(Clone, Debug)]
pub struct BacktrackingEngine<Prog: Program> {
    prog: Prog,
    prefix: Prefix,
}

impl<Prog: Program> BacktrackingEngine<Prog> {
    pub fn new(prog: Prog, pref: Prefix) -> BacktrackingEngine<Prog> {
        BacktrackingEngine {
            prog: prog,
            prefix: pref,
        }
    }

    fn shortest_match_from<'a>(&self, input: &[u8], pos: usize, mut state: usize)
    -> Option<usize> {
        for pos in pos..input.len() {
            let (next_state, accepted) = self.prog.step(state, &input[pos..]);
            if let Some(bytes_ago) = accepted {
                // We need to use saturating_sub here because Nfa::determinize_for_shortest_match
                // makes it so that bytes_ago can be positive even when start_idx == 0.
                return Some(pos.saturating_sub(bytes_ago as usize));
            } else if let Some(next_state) = next_state {
                state = next_state;
            } else {
                return None;
            }
        }

        self.prog.check_eoi(state, input.len())
    }

    /// `positions` iterates over `(prefix_start, prog_start, state)`
    fn shortest_match_from_iter<I>(&self, input: &[u8], positions: I) -> Option<(usize, usize)>
        where I: Iterator<Item=(usize, usize, usize)>
    {
        for (pref_start, prog_start, state) in positions {
            if let Some(end) = self.shortest_match_from(input, prog_start, state) {
                return Some((pref_start, end));
            }
        }

        self.prog.check_empty_match_at_end(input)
    }

    fn shortest_match_slow(&self, s: &[u8]) -> Option<(usize, usize)> {
        for pos in std::iter::range_inclusive(0, s.len()) {
            if let Some(state) = self.prog.init().state_at_pos(s, pos) {
                if let Some(end) = self.shortest_match_from(s, pos, state) {
                    return Some((pos, end));
                }
            }
        }

        None
    }
}

impl<P: Program + 'static> Engine for BacktrackingEngine<P> {
    fn shortest_match(&self, s: &str) -> Option<(usize, usize)> {
        let input = s.as_bytes();
        if self.prog.num_states() == 0 {
            return None;
        } else if let Some(state) = self.prog.init().anchored() {
            return self.shortest_match_from(input, 0, state).map(|x| (0, x));
        }

        match self.prefix {
            Prefix::ByteSet(ref bs, state) =>
                self.shortest_match_from_iter(input, ByteSetIter::new(input, bs, state)),
            Prefix::Byte(b, state) =>
                self.shortest_match_from_iter(input, ByteIter::new(input, b, state)),
            Prefix::Lit(ref lit, state) =>
                self.shortest_match_from_iter(input, StrIter::new(input, &lit, state)),
            Prefix::Ac(ref ac, ref state_table) => {
                let iter =
                    ac.find_overlapping(input)
                        .map(|m| (m.start, m.end, state_table[m.pati]));
                self.shortest_match_from_iter(input, iter)
            },
            Prefix::LoopWhile(ref bs, state) =>
                self.shortest_match_from_iter(input, LoopIter::new(input, bs, state)),
            Prefix::Empty => self.shortest_match_slow(input),
        }
    }

    fn clone_box(&self) -> Box<Engine> {
        Box::new(self.clone())
    }
}
