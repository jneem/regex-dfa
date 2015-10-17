// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use backtracking::BacktrackingEngine;
use char_map::{CharMap, CharSet};
use dfa::Dfa;
use engine::Engine;
use error;
use std::fmt::{Debug, Formatter, Error as FmtError};
use threaded::ThreadedEngine;
use transition::Accept;

pub trait RegexSearcher {
    fn shortest_match(&self, haystack: &str) -> Option<(usize, usize)>;
}

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

    /// Returns the state if the previous char was `ch`.
    pub fn state_after(&self, ch: Option<char>) -> Option<usize> {
        if let Some(ch) = ch {
            self.init_after_char.get(ch as u32).cloned().or(self.init_otherwise)
        } else {
            self.init_at_start
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

#[derive(Clone, PartialEq)]
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

    pub fn from_regex_bounded(re: &str, max_states: usize) -> Result<Program, error::Error> {
        let dfa = try!(Dfa::from_regex_bounded(re, max_states));
        Ok(dfa.to_program())
    }

    /// Returns an engine for executing this program.
    pub fn to_engine(self) -> Box<Engine> {
        if self.init.anchored().is_some() || !self.has_cycles() {
            Box::new(BacktrackingEngine::new(self))
        } else {
            Box::new(ThreadedEngine::new(self))
        }
    }

    /// Checks whether the execution graph of this program has any cycles.
    ///
    /// If not, it's a good candidate for the backtracking engine.
    pub fn has_cycles(&self) -> bool {
        use self::Inst::*;

        if self.insts.is_empty() {
            return false;
        }

        // Pairs of (state, child_idx) where child_idx is the index of the next child to explore.
        let mut stack: Vec<(usize, usize)> = Vec::with_capacity(self.insts.len());
        let mut visiting: Vec<bool> = vec![false; self.insts.len()];
        let mut done: Vec<bool> = vec![false; self.insts.len()];

        macro_rules! push {
            ($state:expr) => {
                if visiting[$state] {
                    return true;
                } else if !done[$state] {
                    stack.push(($state, 0));
                    visiting[$state] = true;
                }
            };
        }

        macro_rules! pop {
            ($state:expr) => {
                visiting[$state] = false;
                done[$state] = true;
                stack.pop();
            };
        }

        for start in 0..self.insts.len() {
            if !done[start] {
                stack.push((start, 0));

                while !stack.is_empty() {
                    let &(cur, child_idx) = stack.last().unwrap();
                    stack.last_mut().unwrap().1 += 1;

                    match self.insts[cur] {
                        Acc(ref a) => if !a.is_always() && child_idx == 0 {
                            push!(cur + 1);
                        } else {
                            pop!(cur);
                        },
                        Branch(ref cm) => if child_idx < cm.len() {
                            push!(cm.nth(child_idx).1);
                        } else {
                            pop!(cur);
                        },
                        _ => if child_idx > 0 { pop!(cur); } else { push!(cur + 1); },
                    }
                }
            }
        }
        false
    }
}


impl Debug for Program {
    fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
        try!(f.write_fmt(format_args!("Program ({} instructions):\n", self.insts.len())));

        try!(f.write_fmt(format_args!("Initial_at_start: {:?}\n", self.init.init_at_start)));
        try!(f.write_fmt(format_args!("Initial_after_char: {:?}\n", self.init.init_after_char)));
        try!(f.write_fmt(format_args!("Initial_otherwise: {:?}\n", self.init.init_otherwise)));

        for (idx, inst) in self.insts.iter().enumerate() {
            try!(f.write_fmt(format_args!("\tInst {}: {:?}\n", idx, inst)));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std;
    use super::*;

    #[test]
    fn cycles() {
        macro_rules! cyc {
            ($re:expr, $res:expr) => {
                {
                    let prog = Program::from_regex_bounded($re, std::usize::MAX).unwrap();
                    println!("{:?}", prog);
                    assert_eq!($res, prog.has_cycles());
                }
            };
        }

        cyc!("abcde", false);
        cyc!("ab*d", true);
        cyc!("ab*", false);
        cyc!("ab*$", true);
        cyc!("ab+", false);
        cyc!("ab+$", true);
        cyc!("(ab*|cde)", false);
        cyc!("(ab*|cde)f", true);
        cyc!("(abc)*", false);
        cyc!("(abc)*def", true);
    }
}

