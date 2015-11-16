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
[Preliminary benchmarks](http://bl.ocks.org/jneem/raw/3f08ade195796358d027/?data=%5B%7B%22x%22%3A%2032096469%2C%20%22y%22%3A%2069727258%2C%20%22ratio%22%3A%200.46031451573787685%2C%20%22bench%22%3A%20%22%5Ba-zA-Z%5D%2Bing%22%7D%2C%20%7B%22x%22%3A%201580349%2C%20%22y%22%3A%201714298%2C%20%22ratio%22%3A%200.9218636433105563%2C%20%22bench%22%3A%20%22Huck%5Ba-zA-Z%5D%2B%7CSaw%5Ba-zA-Z%5D%2B%22%7D%2C%20%7B%22x%22%3A%201669853%2C%20%22y%22%3A%201775481%2C%20%22ratio%22%3A%200.9405073892652188%2C%20%22bench%22%3A%20%22%5Ba-z%5Dshing%22%7D%2C%20%7B%22x%22%3A%2031479482%2C%20%22y%22%3A%20309943101%2C%20%22ratio%22%3A%200.10156535795904036%2C%20%22bench%22%3A%20%22.%7B2%2C4%7D%28Tom%7CSawyer%7CHuckleberry%7CFinn%29%22%7D%2C%20%7B%22x%22%3A%2024915540%2C%20%22y%22%3A%2094765990%2C%20%22ratio%22%3A%200.2629164745706767%2C%20%22bench%22%3A%20%22%5C%5Cb%5C%5Cw%2Bnn%5C%5Cb%22%7D%2C%20%7B%22x%22%3A%201946649%2C%20%22y%22%3A%20137852308%2C%20%22ratio%22%3A%200.01412126520217565%2C%20%22bench%22%3A%20%22%28%3Fi%29Tom%7CSawyer%7CHuckleberry%7CFinn%22%7D%2C%20%7B%22x%22%3A%201539498%2C%20%22y%22%3A%207550793%2C%20%22ratio%22%3A%200.20388560512783227%2C%20%22bench%22%3A%20%22%5B%5C%22%27%5D%5B%5E%5C%22%27%5D%7B0%2C30%7D%5B%3F%21%5C%5C.%5D%5B%5C%22%27%5D%22%7D%2C%20%7B%22x%22%3A%20103928%2C%20%22y%22%3A%20110762%2C%20%22ratio%22%3A%200.9383001390368538%2C%20%22bench%22%3A%20%22Twain%22%7D%2C%20%7B%22x%22%3A%201583691%2C%20%22y%22%3A%201729199%2C%20%22ratio%22%3A%200.9158523686400466%2C%20%22bench%22%3A%20%22Tom.%7B10%2C25%7Driver%7Criver.%7B10%2C25%7DTom%22%7D%2C%20%7B%22x%22%3A%201634767%2C%20%22y%22%3A%201658690%2C%20%22ratio%22%3A%200.985577172346852%2C%20%22bench%22%3A%20%22Tom%7CSawyer%7CHuckleberry%7CFinn%22%7D%2C%20%7B%22x%22%3A%2011521511%2C%20%22y%22%3A%2057281209%2C%20%22ratio%22%3A%200.20113945220674376%2C%20%22bench%22%3A%20%22%5C%5CbF%5C%5Cw%2Bn%5C%5Cb%22%7D%2C%20%7B%22x%22%3A%2021489493%2C%20%22y%22%3A%20247434316%2C%20%22ratio%22%3A%200.08684928326594764%2C%20%22bench%22%3A%20%22.%7B0%2C2%7D%28Tom%7CSawyer%7CHuckleberry%7CFinn%29%22%7D%2C%20%7B%22x%22%3A%201593109%2C%20%22y%22%3A%201735606%2C%20%22ratio%22%3A%200.917897840869414%2C%20%22bench%22%3A%20%22%28%3Fi%29Twain%22%7D%2C%20%7B%22x%22%3A%2016153708%2C%20%22y%22%3A%20128001818%2C%20%22ratio%22%3A%200.1261990513290991%2C%20%22bench%22%3A%20%22%28%5BA-Za-z%5Dawyer%7C%5BA-Za-z%5Dinn%29%5C%5Cs%22%7D%2C%20%7B%22x%22%3A%2012675293%2C%20%22y%22%3A%2083113461%2C%20%22ratio%22%3A%200.15250589793150354%2C%20%22bench%22%3A%20%22%5C%5Cs%5Ba-zA-Z%5D%7B0%2C12%7Ding%5C%5Cs%22%7D%2C%20%7B%22x%22%3A%2035508394%2C%20%22y%22%3A%20132126239%2C%20%22ratio%22%3A%200.268745968013212%2C%20%22bench%22%3A%20%22%5Ba-q%5D%5B%5Eu-z%5D%7B13%7Dx%22%7D%5D) show a substantial
speed improvement (for some examples) over rust's default `regex` crate.

# Limitations

Some regex features don't map well to DFAs. Specifically, this crate does not
support (nor does it plan to support) lazy repetition or subgroup captures.
But even if those features are needed, a DFA can be used to accelerate a more
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

