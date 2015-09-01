regex_dfa
=========

A crate for creating and manipulating deterministic finite automata (DFAs).
Currently, the implementation is somewhat biased towards building DFAs from
regular expressions.

[![Build status](https://travis-ci.org/jneem/regex-dfa.svg)](https://travis-ci.org/jneem/regex-dfa)

[Documentation](http://jneem.github.io/regex-dfa/regex_dfa/index.html)

# Why

Regular expression implementations (e.g. [rust's regex
library](http://github.com/rust-lang/regex)) are usually based on
non-deterministic finite automata (NFAs). By turning NFAs into DFAs, we can
sometimes get a speed boost, at the cost of some compilation time. Preliminary
benchmarks show that we can get a 5x improvement over rust's built-in regular
expressions for very simple regexes.

For a favorable example, compare the results of `regex_dfa::Dfa`:
```
test bench::anchored_literal_long_match      ... bench:          51 ns/iter (+/- 2)
test bench::anchored_literal_long_non_match  ... bench:          31 ns/iter (+/- 1)
test bench::anchored_literal_short_match     ... bench:          51 ns/iter (+/- 1)
test bench::anchored_literal_short_non_match ... bench:          31 ns/iter (+/- 1)
```
to the same results for `regex::Regex`:
```
test bench::anchored_literal_long_match      ... bench:         353 ns/iter (+/- 7)
test bench::anchored_literal_long_non_match  ... bench:         230 ns/iter (+/- 13)
test bench::anchored_literal_short_match     ... bench:         329 ns/iter (+/- 24)
test bench::anchored_literal_short_non_match ... bench:         206 ns/iter (+/- 9)
```

There are also less favorable examples, however: `bench::medium_1K` has a throughput of
38 MB/s with `regex_dfa`, but 325 MB/s with `regex`.

# Limitations

Some regex features don't map well to DFAs. Specifically, this crate does not
support (nor does it plan to support) lazy repetition or subgroup captures.

`regex_dfa` is not universally faster than the implementation in the `regex` crate.
For example, the character matching code is faster in `regex` than `regex_dfa`
(see `bench::match_class_unicode`) for an example. The various throughput benchmarks are
also (currently) substantially faster in `regex`.

`regex_dfa` currently only works on nightly rust.

# License

`regex_dfa` is distributed under the MIT license and the Apache license (version 2.0).
See LICENSE-APACHE and LICENSE-MIT for details.

