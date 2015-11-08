// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bytes::{ByteSet, ByteMap};
use char_map::CharMap;
use std;
use std::fmt::{Debug, Formatter, Error as FmtError};
use std::{u8, u32};

pub trait RegexSearcher {
    fn shortest_match(&self, haystack: &str) -> Option<(usize, usize)>;
}

// TODO: replace init_after_char with a backwards-running table-based machine.
#[derive(Clone, Debug, PartialEq)]
pub struct InitStates {
    pub init_at_start: Option<usize>,
    pub init_after_char: CharMap<usize>,
    pub init_otherwise: Option<usize>,
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

    /// Returns the starting state if we are at the given pos in the input.
    pub fn state_at_pos(&self, input: &[u8], pos: usize) -> Option<usize> {
        if pos == 0 {
            self.init_at_start
        } else {
            let s = unsafe { std::str::from_utf8_unchecked(input) };
            if s.is_char_boundary(pos) {
                let ch = s.char_at_reverse(pos);
                self.init_after_char.get(ch as u32).cloned().or(self.init_otherwise)
            } else {
                None
            }
        }
    }
}

// TODO: write a better debug impl that doesn't print usize::MAX millions of times.
#[derive(Clone, Debug, PartialEq)]
pub enum Inst {
    Byte(u8),
    ByteSet(ByteSet),
    Acc(u8),
    Branch(ByteMap),
}

pub trait Program: Clone + Debug {
    /// Returns (next_state, accept), where
    ///   - next_state is the next state to try
    ///   - accept says how many bytes ago we should have accepted.
    fn step(&self, state: usize, input: &[u8]) -> (Option<usize>, Option<u8>);

    /// If the program should accept at the end of input in state `state`, returns the index of the
    /// end of the match.
    fn check_eoi(&self, state: usize, pos: usize) -> Option<usize>;

    /// If this program matches an empty match at the end of the input, return it.
    fn check_empty_match_at_end(&self, input: &[u8]) -> Option<(usize, usize)>;

    /// The number of states in this program.
    fn num_states(&self) -> usize;

    /// The initial state when starting the program.
    fn init(&self) -> &InitStates;
}

#[derive(Clone, PartialEq)]
pub struct VmProgram {
    pub insts: Vec<Inst>,
    pub init: InitStates,
    pub accept_at_eoi: Vec<u8>,
}

impl Program for VmProgram {
    #[inline(always)]
    fn step(&self, state: usize, input: &[u8]) -> (Option<usize>, Option<u8>) {
        use program::Inst::*;
        match self.insts[state] {
            Acc(a) => {
                return (Some(state + 1), Some(a));
            },
            Byte(b) => {
                if b == input[0] {
                    return (Some(state + 1), None);
                }
            },
            ByteSet(ref bs) => {
                if bs.0[input[0] as usize] {
                    return (Some(state + 1), None);
                }
            },
            Branch(ref table) => {
                let next_state = table.0[input[0] as usize];
                if next_state != u32::MAX {
                    return (Some(next_state as usize), None);
                }
            },
        }
        (None, None)
    }

    fn check_eoi(&self, state: usize, pos: usize) -> Option<usize> {
        if self.accept_at_eoi[state] != u8::MAX {
            Some(pos.saturating_sub(self.accept_at_eoi[state] as usize))
        } else {
            None
        }
    }

    fn check_empty_match_at_end(&self, input: &[u8]) -> Option<(usize, usize)> {
        let pos = input.len();
        if let Some(state) = self.init.state_at_pos(input, pos) {
            if self.accept_at_eoi[state] != u8::MAX {
                return Some((pos, pos));
            }
        }
        None
    }

    fn num_states(&self) -> usize {
        self.insts.len()
    }

    fn init(&self) -> &InitStates {
        &self.init
    }
}


impl Debug for VmProgram {
    fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
        try!(f.write_fmt(format_args!("Program ({} instructions):\n", self.insts.len())));

        try!(f.write_fmt(format_args!("Initial_at_start: {:?}\n", self.init.init_at_start)));
        try!(f.write_fmt(format_args!("Initial_after_char: {:?}\n", self.init.init_after_char)));
        try!(f.write_fmt(format_args!("Initial_otherwise: {:?}\n", self.init.init_otherwise)));
        try!(f.write_fmt(format_args!("Accept_at_eoi: {:?}\n", self.accept_at_eoi)));

        for (idx, inst) in self.insts.iter().enumerate() {
            try!(f.write_fmt(format_args!("\tInst {}: {:?}\n", idx, inst)));
        }
        Ok(())
    }
}

pub type TableStateIdx = u32;

/// A DFA program implemented as a lookup table.
#[derive(Clone, Debug)]
pub struct TableProgram {
    /// A `256 x num_instructions`-long table.
    pub table: Vec<TableStateIdx>,
    /// If `accept[st]` is not `u8::MAX`, then it gives the number of bytes ago that we should have
    /// matched the input when we're in state `st`.
    pub accept: Vec<u8>,
    /// Similar to `accept`, but only applies when we're at the end of the input.
    pub accept_at_eoi: Vec<u8>,
    /// Tells us which state to start in.
    pub init: InitStates,
}

impl Program for TableProgram {
    #[inline(always)]
    fn step(&self, state: usize, input: &[u8]) -> (Option<usize>, Option<u8>) {
        let accept = self.accept[state];
        let next_state = self.table[state * 256 + input[0] as usize];

        let accept = if accept != u8::MAX { Some(accept) } else { None };
        let next_state = if next_state != u32::MAX { Some(next_state as usize) } else { None };

        (next_state, accept)
    }

    fn check_eoi(&self, state: usize, pos: usize) -> Option<usize> {
        if self.accept_at_eoi[state] != u8::MAX {
            Some(pos.saturating_sub(self.accept_at_eoi[state] as usize))
        } else {
            None
        }
    }

    fn check_empty_match_at_end(&self, input: &[u8]) -> Option<(usize, usize)> {
        let pos = input.len();
        if let Some(state) = self.init.state_at_pos(input, pos) {
            if self.accept_at_eoi[state] != u8::MAX {
                return Some((pos, pos));
            }
        }
        None
    }

    fn num_states(&self) -> usize {
        self.accept.len()
    }

    fn init(&self) -> &InitStates {
        &self.init
    }
}

