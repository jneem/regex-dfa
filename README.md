regex_dfa
=========

A crate for creating and manipulating deterministic finite automata (DFAs).
Currently, the implementation is somewhat biased towards building DFAs from
regular expressions.

[![Build status](https://travis-ci.org/jneem/regex-dfa.svg)](https://travis-ci.org/jneem/regex-dfa)
[![Coverage Status](https://coveralls.io/repos/jneem/regex-dfa/badge.svg?branch=master&service=github)](https://coveralls.io/github/jneem/regex-dfa?branch=master)

[Documentation](http://jneem.github.io/regex-dfa/regex_dfa/index.html)

# Why

Some regular expression implementations (e.g. [rust's regex
library](http://github.com/rust-lang/regex)) are based on
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
271 MB/s with `regex_dfa`, but 325 MB/s with `regex`.

# Limitations

Some regex features don't map well to DFAs. Specifically, this crate does not
support (nor does it plan to support) lazy repetition or subgroup captures.

`regex_dfa` is not universally faster than the implementation in the `regex`
crate. For example, the character matching code is faster in `regex` than
`regex_dfa` (see `bench::match_class_unicode`) for an example. Moreover,
`regex` has a much more sophisticated optimization for regexes that begin with
one of a small set of strings (e.g. the regex-dna benchmark in the benchmark
shootout game).

`regex_dfa` currently only works on nightly rust.

# Status/TODO

- The internals have more-or-less converged, but need to be documented and more
  thoroughly tested.
- For good regex performance, it is very important to quickly scan the text for
  plausible starting points. We currently have a fairly half-hearted
  implementation of this, which overlaps somewhat with the implementation in
  the `regex` crate. We should split off a better implementation into a
  separate crate.
- Evaluate the usefulness of this crate as part of a full regex implementation
  (e.g. using `regex-dfa` to find matches and then running `regex` on those
  matches in order to extract groups).
- Implement a compiler plugin, and see if it improves performance.

# License

`regex_dfa` is distributed under the MIT license and the Apache license (version 2.0).
See LICENSE-APACHE and LICENSE-MIT for details.

