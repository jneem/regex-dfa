// Copyright 2015-2016 Joe Neeman.
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
use runner::program::TableInsts;

#[derive(Clone, Debug)]
pub struct BacktrackingEngine<Ret> {
    prog: TableInsts<Ret>,
    prefix: Prefix,
}

impl<Ret: Copy + Debug> BacktrackingEngine<Ret> {
    pub fn new(prog: TableInsts<Ret>, pref: Prefix) -> BacktrackingEngine<Ret> {
        BacktrackingEngine {
            prog: prog,
            prefix: pref,
        }
    }

    fn shortest_match_from_searcher(&self, input: &[u8], search: &mut PrefixSearcher)
    -> Option<(usize, usize, Ret)> {
        while let Some(res) = search.search() {
            if let Ok(end) = self.prog.shortest_match_from(input, res.end_pos, res.end_state) {
                return Some((res.start_pos, end.0, end.1));
            }
        }

        None
    }
}

impl<Ret: Copy + Debug + 'static> Engine<Ret> for BacktrackingEngine<Ret> {
    fn shortest_match(&self, s: &str) -> Option<(usize, usize, Ret)> {
        let input = s.as_bytes();
        if self.prog.is_empty() {
            return None;
        } else if self.prog.is_anchored() {
            if let Ok(end) = self.prog.shortest_match_from(input, 0, 0) {
                return Some((0, end.0, end.1));
            } else {
                return None;
            }
        }

        let mut searcher = self.prefix.make_searcher(input);
        self.shortest_match_from_searcher(input, &mut *searcher)
    }

    fn clone_box(&self) -> Box<Engine<Ret>> {
        Box::new(self.clone())
    }
}
