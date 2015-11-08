// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use backtracking::BacktrackingEngine;
use dfa::Dfa;
use engine;
use error;
use std;
use threaded::ThreadedEngine;

#[derive(Debug)]
pub struct Regex {
    engine: Box<engine::Engine>,
}

/// An enum listing the different kinds of supported regex engines.
pub enum Engine {
    /// The backtracking engine will attempt to match the regex starting from offset zero,
    /// then it will try again from offset one, and so on. Although it is quite fast in practice,
    /// it has a poor worst-case behavior. For example, in attempting to match the regex
    /// `"aaaaaaaaaaab"` against the string `"aaaaaaaaaaaaaaaaaaaaaaaaaaa"`, it will look at
    /// each character in the input many times.
    Backtracking,
    /// The threaded engine is guaranteed to look at each input character exactly once, and its
    /// worst-case performance is `O(m * n)`, where `m` is the number of states in the DFA
    /// and `n` is the length of the input.
    Threaded,
}

/// An enum listing the different ways for representing the regex program.
pub enum Program {
    /// A `Vm` program represents a regex as a list of instructions. It is a fairly
    /// memory-efficient representation, particularly when the regex contains lots of string
    /// literals.
    Vm,
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
    pub fn new(re: &str) -> Result<Regex, error::Error> {
        Regex::new_bounded(re, std::usize::MAX)
    }

    /// Creates a new `Regex` from a regular expression string, but only if it doesn't require too
    /// many states.
    pub fn new_bounded(re: &str, max_states: usize) -> Result<Regex, error::Error> {
        Regex::make_regex(re, max_states, None, None)
    }

    /// Creates a new `Regex` from a regular expression string, with some additional knobs to
    /// tweak.
    ///
    /// - `engine` - specifies the search algorithm to use while executing the regex.
    /// - `program` - specifies the representation of the regex program.
    pub fn new_advanced(re: &str, max_states: usize, engine: Engine, program: Program)
    -> Result<Regex, error::Error>
    {
        Regex::make_regex(re, max_states, Some(engine), Some(program))
    }

    fn make_regex(re: &str, max_states: usize, eng: Option<Engine>, prog: Option<Program>)
    -> Result<Regex, error::Error>
    {
        let dfa = try!(Dfa::from_regex_bounded(re, max_states));
        let default_eng = if dfa.is_anchored() || !dfa.has_cycles() {
            Engine::Backtracking
        } else {
            Engine::Threaded
        };
        let eng = eng.unwrap_or(default_eng);
        let prog = prog.unwrap_or(Program::Table);

        let engine: Box<engine::Engine> = match prog {
            Program::Table => {
                let (prog, pref) = dfa.to_table_program();
                match eng {
                    Engine::Backtracking => Box::new(BacktrackingEngine::new(prog, pref)),
                    Engine::Threaded => Box::new(ThreadedEngine::new(prog, pref)),
                }
            },
            Program::Vm => {
                let (prog, pref) = dfa.to_vm_program();
                match eng {
                    Engine::Backtracking => Box::new(BacktrackingEngine::new(prog, pref)),
                    Engine::Threaded => Box::new(ThreadedEngine::new(prog, pref)),
                }
            },
        };

        Ok(Regex { engine: engine })
    }

    /// Returns the index range of the first shortest match, if there is a match. The indices
    /// returned are byte indices of the string. The first index is inclusive; the second is
    /// exclusive, and a little more subtle -- see the crate documentation.
    pub fn shortest_match(&self, s: &str) -> Option<(usize, usize)> {
        self.engine.shortest_match(s)
    }

    pub fn is_match(&self, s: &str) -> bool {
        self.shortest_match(s).is_some()
    }
}
