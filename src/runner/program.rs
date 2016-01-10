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

    /// If `state` is an accepting state, return the associated value.
    fn check_accept(&self, state: usize) -> Option<Self::Ret>;

    /// If `state` is an accepting state at the end of the input, return the associated value.
    fn check_accept_at_eoi(&self, state: usize) -> Option<Self::Ret>;

    /// Returns the next state after consuming `input`.
    fn next_state(&self, state: usize, input: u8) -> Option<usize>;

    /// The number of states in this program.
    fn num_states(&self) -> usize;

    fn is_anchored(&self) -> bool;

    fn shortest_match_from(&self, input: &[u8], pos: usize, mut state: usize)
    -> Result<(usize, Self::Ret), usize> {
        for pos in pos..input.len() {
            if let Some(ret) = self.check_accept(state) {
                return Ok((pos, ret));
            } else if let Some(next_state) = self.next_state(state, input[pos]) {
                state = next_state;
            } else {
                return Err(pos);
            }
        }

        if let Some(ret) = self.check_accept_at_eoi(state) {
            Ok((input.len(), ret))
        } else {
            Err(input.len())
        }
    }

    /// If a match is found, returns the ending position and the returned value.
    fn longest_backward_match_from(&self, input: &[u8], pos: usize, mut state: usize)
    -> Option<(usize, Self::Ret)> {
        let mut ret = None;
        for pos in (0..pos).rev() {
            if let Some(next_ret) = self.check_accept(state) {
                ret = Some((pos + 1, next_ret));
            }
            if let Some(next_state) = self.next_state(state, input[pos]) {
                state = next_state;
            } else {
                return ret;
            }
        }

        if let Some(end_ret) = self.check_accept_at_eoi(state) {
            Some((0, end_ret))
        } else {
            ret
        }
    }

    fn is_empty(&self) -> bool {
        self.num_states() == 0
    }
}

#[derive(Clone, PartialEq)]
pub struct VmInsts<Ret> {
    pub byte_sets: Vec<bool>,
    pub branch_table: Vec<u32>,
    pub insts: Vec<Inst<Ret>>,
    pub accept_at_eoi: Vec<Option<Ret>>,
    pub is_anchored: bool,
}

impl<Ret: Copy + Debug> Instructions for VmInsts<Ret> {
    type Ret = Ret;

    fn check_accept(&self, state: usize) -> Option<Ret> {
        match self.insts[state] {
            Inst::Acc(a) => Some(a),
            _ => None,
        }
    }

    fn check_accept_at_eoi(&self, state: usize) -> Option<Ret> {
        self.accept_at_eoi[state]
    }

    fn is_anchored(&self) -> bool {
        self.is_anchored
    }

    fn next_state(&self, mut state: usize, input: u8) -> Option<usize> {
        use self::Inst::*;
        // Recursion might be more natural here, but it prevents us from being inlined.
        loop {
            match self.insts[state] {
                Acc(_) => {
                    state += 1;
                },
                Byte(b) => {
                    return if b == input { Some(state + 1) } else { None };
                },
                ByteSet(bs_idx) => {
                    return if self.byte_sets[bs_idx * 256 + input as usize] {
                        Some(state + 1)
                    } else {
                        None
                    };
                },
                Branch(table_idx) => {
                    let next_state = self.branch_table[table_idx * 256 + input as usize];
                    return if next_state != u32::MAX {
                        Some(next_state as usize)
                    } else {
                        None
                    };
                },
            }
        }
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
    /// Same as `accept`, but applies only at the end of the input.
    pub accept_at_eoi: Vec<Option<Ret>>,
    /// If true, this program should only be used at the start of the input.
    pub is_anchored: bool,
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

        try!(f.write_str("Accept_at_eoi: "));
        for idx in 0..self.accept_at_eoi.len() {
            if let Some(ref ret) = self.accept_at_eoi[idx] {
                try!(f.write_fmt(format_args!("{} -> {:?}, ", idx, ret)));
            }
        }
        Ok(())
    }
}


impl<Ret: Copy + Debug> Instructions for TableInsts<Ret> {
    type Ret = Ret;

    fn check_accept(&self, state: usize) -> Option<Ret> {
        self.accept[state]
    }

    fn check_accept_at_eoi(&self, state: usize) -> Option<Ret> {
        self.accept_at_eoi[state]
    }

    fn is_anchored(&self) -> bool {
        self.is_anchored
    }

    fn next_state(&self, state: usize, input: u8) -> Option<usize> {
        let next_state = self.table[state * 256 + input as usize];
        if next_state != u32::MAX {
            Some(next_state as usize)
        } else {
            None
        }
    }

    fn num_states(&self) -> usize {
        self.accept.len()
    }

    // This is copy & paste from the blanket implementation in Instructions, with check_accept
    // and next_state manually inlined. For some reason, doing this increases speeds substantially
    // (but adding #[inline(always)] to check_accept and next_state doesn't).
    fn shortest_match_from(&self, input: &[u8], pos: usize, mut state: usize)
    -> Result<(usize, Self::Ret), usize> {
        for pos in pos..input.len() {
            if let Some(ret) = self.accept[state] {
                return Ok((pos, ret));
            }

            let next_state = self.table[state * 256 + input[pos] as usize];
            if next_state != u32::MAX {
                state = next_state as usize;
            } else {
                return Err(pos);
            }
        }

        if let Some(ret) = self.check_accept_at_eoi(state) {
            Ok((input.len(), ret))
        } else {
            Err(input.len())
        }
    }
}

