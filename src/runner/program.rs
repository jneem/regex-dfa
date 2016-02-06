// Copyright 2015-2016 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::fmt::{Debug, Formatter, Error as FmtError};
use std::u32;

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
        try!(f.write_fmt(format_args!("TableInsts ({} instructions):\n",
                                      self.accept.len())));

        for idx in 0..self.accept.len() {
            try!(f.write_fmt(format_args!("State {}:\n", idx)));
            try!(f.debug_map()
                .entries((0usize..256)
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

impl<Ret: Copy + Debug> TableInsts<Ret> {
    pub fn is_anchored(&self) -> bool {
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

    pub fn num_states(&self) -> usize {
        self.accept.len()
    }

    pub fn shortest_match_from(&self, input: &[u8], pos: usize, state: usize)
    -> Result<(usize, Ret), usize> {
        let mut state = state as u32;

        for pos in pos..input.len() {
            if let Some(ret) = self.accept[state as usize] {
                return Ok((pos, ret));
            }

            // We've manually inlined next_state here, for better performance (measurably better
            // than using #[inline(always)]).
            state = self.table[(state * 256) as usize + input[pos] as usize];
            if state == u32::MAX {
                return Err(pos);
            }
        }

        if let Some(ret) = self.accept_at_eoi[state as usize] {
            Ok((input.len(), ret))
        } else {
            Err(input.len())
        }
    }

    pub fn longest_backward_match_from(&self, input: &[u8], pos: usize, mut state: usize)
    -> Option<(usize, Ret)> {
        let mut ret = None;
        for pos in (0..pos).rev() {
            if let Some(next_ret) = self.accept[state] {
                ret = Some((pos + 1, next_ret));
            }
            if let Some(next_state) = self.next_state(state, input[pos]) {
                state = next_state;
            } else {
                return ret;
            }
        }

        if let Some(end_ret) = self.accept_at_eoi[state] {
            Some((0, end_ret))
        } else {
            ret
        }
    }

    pub fn is_empty(&self) -> bool {
        self.num_states() == 0
    }
}

