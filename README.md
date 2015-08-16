automaton
=========

A crate for creating and manipulating deterministic finite automata (DFAs).
Currently, the implementation is somewhat biased towards building DFAs from
regular expressions.

# Why

Regular expression implementations (e.g. [rust's regex
library](http://github.com/rust-lang/regex)) are usually based on
non-deterministic finite automata (NFAs). By turning NFAs into DFAs, we can
sometimes get a speed boost, at the cost of some compilation time. Preliminary
benchmarks show that we can get a 5x improvement over rust's built-in regular
expressions for very simple regexes.

# Limitations

Some regex features don't map well to DFAs. Specifically, this crate does not
support (nor does it plan to support) lazy repetition or subgroup captures.
There are also some whose support is planned, but not implemented (e.g. word
boundaries).

# License

`automaton` is distributed under the MIT license and the Apache license (version 2.0).
See LICENSE-APACHE and LICENSE-MIT for details.

