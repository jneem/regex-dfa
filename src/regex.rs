// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use backtracking::BacktrackingEngine;
use dfa::Dfa;
use engine::Engine;
use error;
use std;
use threaded::ThreadedEngine;

#[derive(Debug)]
pub struct Regex {
    engine: Box<Engine>,
}

impl Clone for Regex {
    fn clone(&self) -> Regex {
        Regex {
            engine: self.engine.clone_box(),
        }
    }
}

impl Regex {
    pub fn new(re: &str) -> Result<Regex, error::Error> {
        Regex::new_bounded(re, std::usize::MAX)
    }

    pub fn new_bounded(re: &str, max_states: usize) -> Result<Regex, error::Error> {
        let dfa = try!(Dfa::from_regex_bounded(re, max_states));
        let (prog, pref) = dfa.to_vm_program();

        let engine: Box<Engine> = if prog.init.anchored().is_some() || !dfa.has_cycles() {
            Box::new(BacktrackingEngine::new(prog, pref))
        } else {
            Box::new(ThreadedEngine::new(prog, pref))
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
