// Copyright 2015-2016 Joe Neeman.
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
necessarily find the exact same match that a standard regex engine will. Having said that, see the
next example.

# Example: scanning with `regex_dfa` and then matching with `regex`

Probably the most useful way to use this crate is as a preprocessor for a real regex engine. The
idea is to use `regex_dfa` for finding the start of a match, and then to use another engine for
doing the rest (e.g. replacing text, finding capture groups, etc.).

```rust
# extern crate regex;
# extern crate regex_dfa;

use regex::Regex;
use regex_dfa::{Regex as RegexDfa};

# fn main() {
let digits_dfa = RegexDfa::new("[0-9]+").unwrap();
let digits = Regex::new("^[0-9]+").unwrap(); // Note the '^'!

let find_digits = |s: &str| {
    // First, quickly find the beginning of a match.
    if let Some((start, _)) = digits_dfa.shortest_match(s) {
        // Now use the real regex engine to do the rest.
        digits.find(&s[start..]).map(|(x, y)| (x + start, y + start))
    } else {
        None
    }
};
# }
```
*/

#![cfg_attr(test, feature(test))]
#[cfg(test)]
extern crate quickcheck;

#[cfg(test)]
#[macro_use]
extern crate matches;

#[cfg(test)]
extern crate test;

extern crate itertools;
extern crate memchr;
extern crate num;
extern crate range_map;
extern crate refinery;
extern crate regex_syntax;
extern crate utf8_ranges;

#[macro_use]
extern crate lazy_static;

mod dfa;
mod error;
mod look;
mod graph;
mod nfa;
mod regex;
mod runner;
mod unicode;

pub use error::Error;
pub use regex::Regex;
pub type Result<T> = ::std::result::Result<T, Error>;

