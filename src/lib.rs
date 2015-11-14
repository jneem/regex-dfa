// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
This crate provides tools for converting regular expressions into deterministic finite automata
(DFAs). The most interesting type is `Regex`, which is a virtual machine for executing a DFA.

# Example: creating and running a `Regex`

```rust
use regex_dfa::Regex;
let re = Regex::new(r"\d{4}-\d{2}-\d{2}").unwrap();
assert_eq!(re.shortest_match("My birthday is 1986-08-22!"), Some((15, 25)));
```

# Caveats

The most useful function in this crate is `Regex::shortest_match`, which looks for substrings of
the given string that match the language of the DFA. The first index of the return value is fairly
self-explanatory but the second index should be used with caution because it is only a bound on the
ending index you will get from running a standard regex engine. This is because a regex specifies
not only a language, but also a preferred execution order (for example, by specifying lazy or
greedy repetition operators). This information is lost when moving to a DFA, so we cannot
necessarily find the exact same match that a standard regex engine will.
*/

#![feature(iter_arith, range_inclusive, slice_splits, test)]

extern crate aho_corasick;
extern crate itertools;
extern crate memchr;
extern crate memmem;
extern crate regex_syntax;
extern crate test;
extern crate utf8_ranges;

mod backtracking;
mod backwards_char_map;
mod builder;
mod bytes;
mod char_map;
mod dfa;
mod engine;
mod error;
mod nfa;
mod prefix;
mod program;
mod regex;
mod searcher;
mod threaded;
mod transition;
mod unicode;

pub use error::Error;
pub use regex::{Engine, Program, Regex};

