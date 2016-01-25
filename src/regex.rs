// Copyright 2015-2016 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use dfa::CompileTarget;
use error::Error;
use graph::Graph;
use nfa::{Nfa, NoLooks};
use runner::forward_backward::ForwardBackwardEngine;
use runner::backtracking::BacktrackingEngine;
use runner::prefix::Prefix;
use runner::program::{Instructions, TableInsts};
use runner::Engine;
use std;
use std::fmt::Debug;

#[derive(Debug)]
pub struct Regex {
    engine: Box<Engine<u8>>,
}

// An engine that doesn't match anything.
#[derive(Clone, Debug)]
struct EmptyEngine;

impl<Ret: Debug> Engine<Ret> for EmptyEngine {
    fn shortest_match(&self, _: &str) -> Option<(usize, usize, Ret)> { None }
    fn clone_box(&self) -> Box<Engine<Ret>> { Box::new(EmptyEngine) }
}

/// An enum listing the different kinds of supported regex engines.
#[derive(Clone, Copy, Debug)]
pub enum EngineType {
    /// The backtracking engine will attempt to match the regex starting from offset zero,
    /// then it will try again from offset one, and so on. Although it is quite fast in practice,
    /// it has a poor worst-case behavior. For example, in attempting to match the regex
    /// `"aaaaaaaaaaab"` against the string `"aaaaaaaaaaaaaaaaaaaaaaaaaaa"`, it will look at
    /// each character in the input many times.
    Backtracking,
    /// The forward-backward engine is guaranteed to look at each input character at most twice.
    ForwardBackward,
}

/// An enum listing the different ways for representing the regex program.
#[derive(Clone, Copy, Debug)]
pub enum ProgramType {
    /// A `Table` program is the classical table-based implementation of a DFA.
    Table,
}

impl Clone for Regex {
    fn clone(&self) -> Regex {
        Regex {
            engine: self.engine.clone_box(),
        }
    }
}

impl Regex {
    /// Creates a new `Regex` from a regular expression string.
    pub fn new(re: &str) -> ::Result<Regex> {
        Regex::new_bounded(re, std::usize::MAX)
    }

    /// Creates a new `Regex` from a regular expression string, but only if it doesn't require too
    /// many states.
    pub fn new_bounded(re: &str, max_states: usize) -> ::Result<Regex> {
        Regex::make_regex(re, max_states, None, None)
    }

    /// Creates a new `Regex` from a regular expression string, with some additional knobs to
    /// tweak.
    ///
    /// - `engine` - specifies the search algorithm to use while executing the regex.
    /// - `program` - specifies the representation of the regex program.
    pub fn new_advanced(re: &str, max_states: usize, engine: EngineType, program: ProgramType)
    -> ::Result<Regex>
    {
        Regex::make_regex(re, max_states, Some(engine), Some(program))
    }

    fn make_backtracking<I>(nfa: Nfa<u32, NoLooks>, max_states: usize)
    -> ::Result<BacktrackingEngine<I>>
    where I: Instructions<Ret=u8> + CompileTarget<u8> {
        if nfa.has_look_behind() {
            return Err(Error::InvalidEngine("look-behind rules out the backtracking engine"));
        }

        let nfa = try!(nfa.byte_me(max_states));
        let dfa = try!(nfa.determinize_shortest(max_states))
            .optimize_for_shortest_match()
            .map_ret(|(_, bytes)| bytes);
        let prog = dfa.compile::<I>();
        let prefix = if dfa.is_anchored() {
            Prefix::Empty
        } else {
            Prefix::for_slow_engine(dfa.prefix_strings())
        };

        Ok(BacktrackingEngine::new(prog, prefix))
    }

    fn make_forward_backward<FI, BI>(nfa: Nfa<u32, NoLooks>, max_states: usize)
    -> ::Result<ForwardBackwardEngine<FI, BI>> where
    FI: Instructions<Ret=(usize, u8)> + CompileTarget<(usize, u8)>,
    BI: Instructions<Ret=u8> + CompileTarget<u8> {
        if nfa.is_anchored() {
            return Err(Error::InvalidEngine("anchors rule out the forward-backward engine"));
        }

        let f_nfa = try!(try!(nfa.clone().byte_me(max_states)).anchor(max_states));
        let b_nfa = try!(try!(nfa.byte_me(max_states)).reverse(max_states));

        let f_dfa = try!(f_nfa.determinize_shortest(max_states)).optimize_for_shortest_match();
        let b_dfa = try!(b_nfa.determinize_longest(max_states))
            .optimize();
        let b_dfa = b_dfa.map_ret(|(_, bytes)| bytes);

        let b_prog = b_dfa.compile::<BI>();
        let f_dfa = f_dfa.map_ret(|(look, bytes)| {
            let b_dfa_state = b_dfa.init[look.as_usize()].expect("BUG: back dfa must have this init");
            (b_dfa_state, bytes)
        });

        let mut f_prog = f_dfa.compile::<FI>();
        let prefix = Prefix::for_fast_engine(f_dfa.pruned_prefix_strings());
        match prefix {
            Prefix::Empty => {},
            _ => {
                // If there is a non-trivial prefix, we can usually speed up matching by deleting
                // transitions that return to the start state. That way, instead of returning to
                // the start state, we will just fail to match. Then we get to search for the
                // prefix before trying to match again.
                let f_dfa = f_dfa.cut_loop_to_init().optimize_for_shortest_match();
                f_prog = f_dfa.compile::<FI>();
            },
        }

        Ok(ForwardBackwardEngine::new(f_prog, prefix, b_prog))
    }

    // Make a forward-backward engine, but if that uses too many states and fallback is true then try
    // making a backtracking engine instead.
    fn make_boxed_forward_backward<FI, BI>(nfa: Nfa<u32, NoLooks>, max_states: usize, fallback: bool)
    -> ::Result<Box<Engine<u8>>> where
    FI: Instructions<Ret=(usize, u8)> + CompileTarget<(usize, u8)> + 'static,
    BI: Instructions<Ret=u8> + CompileTarget<u8> + 'static,
    {
        let fb = Regex::make_forward_backward::<FI, BI>(nfa.clone(), max_states)
            .map(|x| Box::new(x) as Box<Engine<u8>>);
        // TODO: we can allow cycles as long as the shortest match happens before the cycle.
        if fallback && !nfa.has_cycles() {
            fb.or_else(|_| {
                let b = try!(Regex::make_backtracking::<BI>(nfa, max_states));
                Ok(Box::new(b) as Box<Engine<u8>>)
            })
        } else {
            fb
        }
    }

    fn make_regex(re: &str,
                  max_states: usize,
                  maybe_eng: Option<EngineType>,
                  maybe_prog: Option<ProgramType>)
    -> ::Result<Regex> {
        let nfa = try!(Nfa::from_regex(re));
        let nfa = nfa.remove_looks();

        if nfa.is_empty() {
            return Ok(Regex { engine: Box::new(EmptyEngine) });
        }

        // If the engine and program weren't specified, choose them automatically based on nfa.
        let eng = maybe_eng.unwrap_or(if nfa.is_anchored() {
            EngineType::Backtracking
        } else {
            EngineType::ForwardBackward
        });
        let prog = maybe_prog.unwrap_or(ProgramType::Table);

        let eng: Box<Engine<u8>> = match eng {
            EngineType::Backtracking => {
                match prog {
                    ProgramType::Table =>
                        Box::new(try!(Regex::make_backtracking::<TableInsts<_>>(nfa, max_states))),
                }
            }
            EngineType::ForwardBackward => {
                match prog {
                    ProgramType::Table =>
                        try!(Regex::make_boxed_forward_backward::<TableInsts<_>, TableInsts<_>>(
                                nfa,
                                max_states,
                                maybe_eng.is_none())),
                }
            }
        };

        Ok(Regex { engine: eng })
    }

    /// Returns the index range of the first shortest match, if there is a match. The indices
    /// returned are byte indices of the string. The first index is inclusive; the second is
    /// exclusive, and a little more subtle -- see the crate documentation.
    pub fn shortest_match(&self, s: &str) -> Option<(usize, usize)> {
        if let Some((start, end, look_behind)) = self.engine.shortest_match(s) {
            Some((start + look_behind as usize, end))
        } else {
            None
        }
    }

    pub fn is_match(&self, s: &str) -> bool {
        self.shortest_match(s).is_some()
    }
}

#[cfg(test)]
mod tests {
    use regex::*;

    #[test]
    fn size_fallback() {
        // This regex takes a huge number of states if you anchor it by adding '.*' in front.
        let re = "a[ab]{100}c";
        assert!(Regex::new_bounded(re, 2000).is_ok());
        assert!(Regex::new_advanced(re, 2000, EngineType::Backtracking, ProgramType::Table).is_ok());
        assert!(Regex::new_advanced(re, 2000, EngineType::ForwardBackward, ProgramType::Table).is_err());
    }

    #[test]
    fn fallback_cycles() {
        // This regex has cycles, so it shouldn't automatically fall back to backtracking.
        let re = "a[ab]{100}c+";
        assert!(Regex::new_bounded(re, 2000).is_err());
        assert!(Regex::new_advanced(re, 2000, EngineType::ForwardBackward, ProgramType::Table).is_err());

        // If they specifically ask for backtracking, then ok.
        assert!(Regex::new_advanced(re, 2000, EngineType::Backtracking, ProgramType::Table).is_ok());
    }
}

