// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::fmt::{Debug, Formatter, Error as FmtError};
use std::u32;

pub trait RegexSearcher {
    fn shortest_match(&self, haystack: &str) -> Option<(usize, usize)>;
}

#[derive(Clone, Debug, PartialEq)]
pub enum Inst<Ret> {
    Byte(u8),
    ByteSet(usize),
    Acc(Ret),
    Branch(usize),
}

pub trait Instructions: Clone + Debug {
    type Ret: Clone + Debug;

    /// Returns (next_state, accept), where
    ///   - next_state is the next state to try
    ///   - accept gives some data associated with the acceptance.
    fn step(&self, state: usize, input: u8) -> (Option<usize>, Option<Self::Ret>);

    /// The number of states in this program.
    fn num_states(&self) -> usize;
}

#[derive(Clone, Debug)]
pub struct Program<Insts: Instructions> {
    pub accept_at_eoi: Vec<Option<Insts::Ret>>,
    pub instructions: Insts,
    pub is_anchored: bool,
}

impl<Insts: Instructions> Program<Insts> {
    /// If the program should accept at the end of input in state `state`, returns the data
    /// associated with the match.
    pub fn check_eoi(&self, state: usize) -> Option<Insts::Ret> {
        self.accept_at_eoi[state].clone()
    }

    /// If a match is found, returns the ending position and the returned value. Otherwise,
    /// returns the position at which we failed.
    pub fn shortest_match_from(&self, input: &[u8], pos: usize, mut state: usize)
    -> Result<(usize, Insts::Ret), usize> {
        for pos in pos..input.len() {
            let (next_state, accepted) = self.instructions.step(state, input[pos]);
            if let Some(ret) = accepted {
                return Ok((pos, ret));
            } else if let Some(next_state) = next_state {
                state = next_state;
            } else {
                return Err(pos);
            }
        }

        if let Some(ret) = self.check_eoi(state) {
            Ok((input.len(), ret))
        } else {
            Err(input.len())
        }
    }

    /// If a match is found, returns the ending position and the returned value.
    pub fn longest_backward_match_from(&self, input: &[u8], pos: usize, mut state: usize)
    -> Option<(usize, Insts::Ret)> {
        let mut ret = None;
        for pos in (0..pos).rev() {
            let (next_state, accepted) = self.instructions.step(state, input[pos]);
            if let Some(next_ret) = accepted {
                ret = Some((pos + 1, next_ret));
            }
            if let Some(next_state) = next_state {
                state = next_state;
            } else {
                return ret;
            }
        }

        if let Some(end_ret) = self.check_eoi(state) {
            Some((0, end_ret))
        } else {
            ret
        }
    }

    pub fn is_empty(&self) -> bool {
        self.instructions.num_states() == 0
    }
}

#[derive(Clone, PartialEq)]
pub struct VmInsts<Ret> {
    pub byte_sets: Vec<bool>,
    pub branch_table: Vec<u32>,
    pub insts: Vec<Inst<Ret>>,
}

impl<Ret: Copy + Debug> Instructions for VmInsts<Ret> {
    type Ret = Ret;

    #[inline(always)]
    fn step(&self, mut state: usize, input: u8) -> (Option<usize>, Option<Ret>) {
        use runner::program::Inst::*;
        let mut acc = None;
        loop {
            match self.insts[state] {
                Acc(a) => {
                    acc = Some(a);
                    state += 1;
                },
                Byte(b) => {
                    if b == input {
                        return (Some(state + 1), acc);
                    }
                    break;
                },
                ByteSet(bs_idx) => {
                    if self.byte_sets[bs_idx * 256 + input as usize] {
                        return (Some(state + 1), acc);
                    }
                    break;
                },
                Branch(table_idx) => {
                    let next_state = self.branch_table[table_idx * 256 + input as usize];
                    if next_state != u32::MAX {
                        return (Some(next_state as usize), acc);
                    }
                    break;
                },
            }
        }
        (None, acc)
    }

    fn num_states(&self) -> usize {
        self.insts.len()
    }
}

fn fmt_byte_map(f: &mut Formatter, map: &[u32]) -> Result<(), FmtError> {
    try!(f.debug_map()
         .entries(map.iter().cloned().enumerate()
                  .filter(|pair| pair.1 != u32::MAX))
         .finish());
    Ok(())
}

fn fmt_byte_set(f: &mut Formatter, set: &[bool]) -> Result<(), FmtError> {
    try!(f.debug_set()
         .entries(set.iter().cloned().enumerate()
                  .filter(|pair| pair.1)
                  .map(|pair| pair.0))
         .finish());
    Ok(())
}

impl<Ret: Debug> Debug for VmInsts<Ret> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
        try!(f.write_fmt(format_args!("VmInsts ({} instructions):\n", self.insts.len())));

        for (idx, inst) in self.insts.iter().enumerate() {
            try!(f.write_fmt(format_args!("\tInst {}: {:?}\n", idx, inst)));
        }

        for i in 0..(self.branch_table.len() / 256) {
            try!(f.write_fmt(format_args!("\tBranch {}: ", i)));
            try!(fmt_byte_map(f, &self.branch_table[i*256 .. (i+1)*256]));
            try!(f.write_str("\n"));
        }
        for i in 0..(self.byte_sets.len() / 256) {
            try!(f.write_fmt(format_args!("\tSet {}: ", i)));
            try!(fmt_byte_set(f, &self.byte_sets[i*256 .. (i+1)*256]));
            try!(f.write_str("\n"));
        }
        Ok(())
    }
}

pub type TableStateIdx = u32;

/// A DFA program implemented as a lookup table.
#[derive(Clone)]
pub struct TableInsts<Ret> {
    /// A `256 x num_instructions`-long table.
    pub table: Vec<TableStateIdx>,
    /// If `accept[st]` is not `None` then `st` is accepting, and `accept[st]` is the data
    /// to return.
    pub accept: Vec<Option<Ret>>,
}

impl<Ret: Debug> Debug for TableInsts<Ret> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
        try!(f.write_fmt(format_args!("TableInsts ({} instructions):\n", self.accept.len())));

        for idx in 0..self.accept.len() {
            try!(f.write_fmt(format_args!("State {}:\n", idx)));
            try!(f.debug_map()
                .entries((0usize..255)
                    .map(|c| (c, self.table[idx * 256 + c]))
                    .filter(|x| x.1 != u32::MAX))
                .finish());
            try!(f.write_str("\n"));
        }

        try!(f.write_str("Accept: "));
        for idx in 0..self.accept.len() {
            if let Some(ref ret) = self.accept[idx] {
                try!(f.write_fmt(format_args!("{} -> {:?}, ", idx, ret)));
            }
        }
        Ok(())
    }
}


impl<Ret: Copy + Debug> Instructions for TableInsts<Ret> {
    type Ret = Ret;

    #[inline(always)]
    fn step(&self, state: usize, input: u8) -> (Option<usize>, Option<Ret>) {
        let accept = self.accept[state];
        let next_state = self.table[state * 256 + input as usize];

        let next_state = if next_state != u32::MAX { Some(next_state as usize) } else { None };

        (next_state, accept)
    }

    fn num_states(&self) -> usize {
        self.accept.len()
    }
}

