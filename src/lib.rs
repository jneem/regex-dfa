// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
This crate provides tools for creating, manipulating, and executing deterministic finite automata
(DFAs). The main type is therefore `Dfa`. There is also `Nfa`, which is for representing and
analyzing non-deterministic finite automata (NFAs). However, there is no support for
executing NFAs; they are only used for constructing DFAs.

# Example: creating and running a `Dfa`

```rust
use automaton::Dfa;
let dfa = Dfa::from_regex(r"\d{4}-\d{2}-\d{2}").unwrap();
assert_eq!(dfa.search("My birthday is 1986-08-22!"), Some((15, 25)));
```
*/

#![feature(slice_splits, test)]

extern crate bit_set;
extern crate regex;
extern crate regex_syntax;
extern crate test;

mod automaton;
mod builder;
mod error;
mod transition;

pub use automaton::{Dfa, Nfa};

pub use error::Error;
