// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
This crate provides tools for converting regular expressions into deterministic finite automata
(DFAs). The most interesting type is `Program`, which is a DFA represented as a sequence of
instructions for a virtual machine.

# Example: creating and running a `Program`

```rust
use regex_dfa::Program;
let dfa = Program::from_regex(r"\d{4}-\d{2}-\d{2}").unwrap();
assert_eq!(dfa.shortest_match("My birthday is 1986-08-22!"), Some((15, 25)));
```

# Caveats

The most useful function in this crate is `Program::shortest_match`, which looks for substrings of
the given string that match the language of the DFA. The first index of the return value is fairly
self-explanatory but the second index should be used with caution because it is only a bound on the
ending index you will get from running a standard regex engine. This is because a regex specifies
not only a language, but also a preferred execution order (for example, by specifying lazy or
greedy repetition operators). This information is lost when moving to a DFA, so we cannot
necessarily find the exact same match that a standard regex engine will.
*/

#![feature(slice_splits, str_char, test)]

extern crate ascii_set;
extern crate bit_set;
extern crate memchr;
extern crate regex;
extern crate regex_syntax;
extern crate test;

mod builder;
mod char_map;
mod dfa;
mod error;
mod nfa;
mod searcher;
mod transition;
mod unicode;

pub use dfa::Program;
pub use error::Error;

