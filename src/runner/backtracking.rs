// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use aho_corasick::Automaton;
use std::fmt::Debug;
use runner::Engine;
use runner::prefix::{Prefix, PrefixSearcher};
use runner::program::{Instructions, Program};

#[derive(Clone, Debug)]
pub struct BacktrackingEngine<Insts: Instructions> {
    prog: Program<Insts>,
    prefix: Prefix,
}

impl<Insts: Instructions> BacktrackingEngine<Insts> {
    pub fn new(prog: Program<Insts>, pref: Prefix) -> BacktrackingEngine<Insts> {
        BacktrackingEngine {
            prog: prog,
            prefix: pref,
        }
    }

    fn shortest_match_from_searcher(&self, input: &[u8], search: &mut PrefixSearcher)
    -> Option<(usize, usize, Insts::Ret)> {
        while let Some(res) = search.search() {
            if let Ok(end) = self.prog.shortest_match_from(input, res.end_pos, res.end_state) {
                return Some((res.start_pos, end.0, end.1));
            }
        }

        None
    }
}

impl<I: Instructions + 'static> Engine<I::Ret> for BacktrackingEngine<I>
where I::Ret: Debug {
    fn shortest_match(&self, s: &str) -> Option<(usize, usize, I::Ret)> {
        let input = s.as_bytes();
        if self.prog.is_empty() {
            return None;
        } else if self.prog.is_anchored {
            if let Ok(end) = self.prog.shortest_match_from(input, 0, 0) {
                return Some((0, end.0, end.1));
            } else {
                return None;
            }
        }

        let mut searcher = self.prefix.make_searcher(input);
        self.shortest_match_from_searcher(input, &mut *searcher)
    }

    fn clone_box(&self) -> Box<Engine<I::Ret>> {
        Box::new(self.clone())
    }
}
