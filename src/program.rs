// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use char_map::{CharMap, CharSet};
use searcher::Search;
use transition::Accept;

pub trait RegexSearcher {
    fn shortest_match(&self, haystack: &str) -> Option<(usize, usize)>;
}

#[derive(Clone, Debug, PartialEq)]
pub struct InitStates {
    init_at_start: Option<usize>,
    init_after_char: CharMap<usize>,
    init_otherwise: Option<usize>,
}

impl InitStates {
    /// If we can start only at the beginning of the input, return the start state.
    pub fn anchored(&self) -> Option<usize> {
        if self.init_after_char.is_empty() && self.init_otherwise.is_none() {
            self.init_at_start
        } else {
            None
        }
    }

    /// If the start state is always the same, return it.
    pub fn constant(&self) -> Option<usize> {
        if self.init_after_char.is_empty() && self.init_otherwise == self.init_at_start {
            self.init_at_start
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Inst {
    Char(char),
    CharSet(CharSet),
    Acc(Accept),
    Branch(CharMap<usize>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    pub insts: Vec<Inst>,
    pub init: InitStates,
}

impl Program {
    /// Returns (next_state, accept, retry), where
    ///   - next_state is the next state to try
    ///   - if accept is true then we should accept before consuming `ch`
    ///   - if retry is true then we should call `step` again before advancing the input past `ch`.
    ///
    /// It would be a little cleaner for `step` to advance the input on its own instead of
    /// asking its caller to advance, but if `step` is recursive then it can't be inlined (which
    /// is very important for performance).
    #[inline(always)]
    pub fn step(&self, state: usize, ch: char) -> (Option<usize>, bool, bool) {
        use program::Inst::*;
        match self.insts[state] {
            Acc(ref a) => {
                return (Some(state + 1), a.accepts(Some(ch as u32)), true);
            },
            Char(c) => {
                if ch == c {
                    return (Some(state + 1), false, false);
                }
            },
            CharSet(ref cs) => {
                if cs.contains(ch as u32) {
                    return (Some(state + 1), false, false);
                }
            },
            Branch(ref cm) => {
                if let Some(&next_state) = cm.get(ch as u32) {
                    return (Some(next_state), false, false);
                }
            },
        }
        (None, false, false)
    }

    /// Returns true if the program should accept at the end of input in state `state`.
    pub fn check_eoi(&self, state: usize) -> bool {
        if let Inst::Acc(ref acc) = self.insts[state] {
            acc.at_eoi
        } else {
            false
        }
    }

}

