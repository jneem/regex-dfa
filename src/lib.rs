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
use regex_dfa::Dfa;
let dfa = Dfa::from_regex(r"\d{4}-\d{2}-\d{2}").unwrap();
assert_eq!(dfa.shortest_match("My birthday is 1986-08-22!"), Some((15, 25)));
```

# Caveats

The main useful functions in this crate are `Dfa::shortest_match` and `Dfa::longest_match`, which
look for substrings of the given string that match the language of the `Dfa`. For both of these
functions, the starting index of the return value is fairly self-explanatory but the ending index
should be used with caution because it is only a bound on the ending index you will get from
running a standard regex engine based on an NFA. This is because a regex specifies not only a
language, but also a preferred execution order (for example, by specifying lazy or greedy
repetition operators). This information is lost when moving to a DFA, so we cannot necessarily find
the exact same match that a standard regex engine will.
*/

#![feature(slice_splits, str_char, test)]
#![allow(dead_code)]

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
mod transition;

pub use dfa::{Dfa, Program};
pub use nfa::Nfa;

pub use error::Error;

