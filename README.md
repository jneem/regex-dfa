regex_dfa
=========

A crate for compiling regular expressions down to deterministic finite
automata.

[![Build status](https://travis-ci.org/jneem/regex-dfa.svg)](https://travis-ci.org/jneem/regex-dfa)
[![Coverage Status](https://coveralls.io/repos/jneem/regex-dfa/badge.svg?branch=master&service=github)](https://coveralls.io/github/jneem/regex-dfa?branch=master)

[Documentation](http://jneem.github.io/regex-dfa/regex_dfa/index.html)

# Why?

Some regular expression implementations (e.g. [rust's regex
library](http://github.com/rust-lang/regex)) are based on simulating
non-deterministic finite automata (NFAs). By turning NFAs into DFAs, we can
get a speed boost, at the cost of some compilation time.
[Preliminary benchmarks](https://github.com/jneem/regex) show a substantial
speed improvement (for some examples) over rust's default `regex` crate.

# Limitations

Some regex features don't map well to DFAs. Specifically, this crate does not
support (nor does it plan to support) lazy repetition or subgroup captures.
But even if these features are needed, a DFA can be used to accelerate a more
fully-featured regex implementation: run a DFA to find the beginning of a match,
and then run the full engine to either refine the match or extract the capture
groups. My experimental [fork](https://github.com/jneem/regex) of the `regex` crate
takes this approach.

`regex_dfa` currently only works on nightly rust.

# Status/TODO

- Implement a compiler plugin, and see if it improves performance.

# License

`regex_dfa` is distributed under the MIT license and the Apache license (version 2.0).
See LICENSE-APACHE and LICENSE-MIT for details.

