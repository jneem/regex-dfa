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
[Preliminary benchmarks](http://bl.ocks.org/jneem/raw/3f08ade195796358d027/?data=%5B%7B%22y%22%3A%20295351074%2C%20%22ratio%22%3A%200.008334599792245889%2C%20%22bench%22%3A%20%22.%7B2%2C4%7D%28Tom%7CSawyer%7CHuckleberry%7CFinn%29%22%2C%20%22x%22%3A%202461633%7D%2C%20%7B%22y%22%3A%20125978857%2C%20%22ratio%22%3A%200.12771945533685863%2C%20%22bench%22%3A%20%22%5Ba-q%5D%5B%5Eu-z%5D%7B13%7Dx%22%2C%20%22x%22%3A%2016089951%7D%2C%20%7B%22y%22%3A%201631615%2C%20%22ratio%22%3A%200.9981981043322107%2C%20%22bench%22%3A%20%22Tom%7CSawyer%7CHuckleberry%7CFinn%22%2C%20%22x%22%3A%201628675%7D%2C%20%7B%22y%22%3A%20137662852%2C%20%22ratio%22%3A%200.014245985547357395%2C%20%22bench%22%3A%20%22%28%3Fi%29Tom%7CSawyer%7CHuckleberry%7CFinn%22%2C%20%22x%22%3A%201961143%7D%2C%20%7B%22y%22%3A%201724976%2C%20%22ratio%22%3A%200.920081206926937%2C%20%22bench%22%3A%20%22Tom.%7B10%2C25%7Driver%7Criver.%7B10%2C25%7DTom%22%2C%20%22x%22%3A%201587118%7D%2C%20%7B%22y%22%3A%201620677%2C%20%22ratio%22%3A%200.9712465839892835%2C%20%22bench%22%3A%20%22Huck%5Ba-zA-Z%5D%2B%7CSaw%5Ba-zA-Z%5D%2B%22%2C%20%22x%22%3A%201574077%7D%2C%20%7B%22y%22%3A%2084880712%2C%20%22ratio%22%3A%200.0620566425031873%2C%20%22bench%22%3A%20%22%5C%5Cs%5Ba-zA-Z%5D%7B0%2C12%7Ding%5C%5Cs%22%2C%20%22x%22%3A%205267412%7D%2C%20%7B%22y%22%3A%201646883%2C%20%22ratio%22%3A%200.96746763431282%2C%20%22bench%22%3A%20%22%28%3Fi%29Twain%22%2C%20%22x%22%3A%201593306%7D%2C%20%7B%22y%22%3A%2099739%2C%20%22ratio%22%3A%201.0025065420748154%2C%20%22bench%22%3A%20%22Twain%22%2C%20%22x%22%3A%2099989%7D%2C%20%7B%22y%22%3A%2062666721%2C%20%22ratio%22%3A%200.06938462601226575%2C%20%22bench%22%3A%20%22%5C%5CbF%5C%5Cw%2Bn%5C%5Cb%22%2C%20%22x%22%3A%204348107%7D%2C%20%7B%22y%22%3A%2071127171%2C%20%22ratio%22%3A%200.10740621189615428%2C%20%22bench%22%3A%20%22%5Ba-zA-Z%5D%2Bing%22%2C%20%22x%22%3A%207639500%7D%2C%20%7B%22y%22%3A%201664874%2C%20%22ratio%22%3A%200.9960153140718156%2C%20%22bench%22%3A%20%22%5Ba-z%5Dshing%22%2C%20%22x%22%3A%201658240%7D%2C%20%7B%22y%22%3A%207366270%2C%20%22ratio%22%3A%200.1817939065497192%2C%20%22bench%22%3A%20%22%5B%5C%22%27%5D%5B%5E%5C%22%27%5D%7B0%2C30%7D%5B%3F%21%5C%5C.%5D%5B%5C%22%27%5D%22%2C%20%22x%22%3A%201339143%7D%2C%20%7B%22y%22%3A%20243419316%2C%20%22ratio%22%3A%200.01944975065166973%2C%20%22bench%22%3A%20%22.%7B0%2C2%7D%28Tom%7CSawyer%7CHuckleberry%7CFinn%29%22%2C%20%22x%22%3A%204734445%7D%2C%20%7B%22y%22%3A%2094501284%2C%20%22ratio%22%3A%200.04505000164865485%2C%20%22bench%22%3A%20%22%5C%5Cb%5C%5Cw%2Bnn%5C%5Cb%22%2C%20%22x%22%3A%204257283%7D%2C%20%7B%22y%22%3A%20131818244%2C%20%22ratio%22%3A%200.0326143094426292%2C%20%22bench%22%3A%20%22%28%5BA-Za-z%5Dawyer%7C%5BA-Za-z%5Dinn%29%5C%5Cs%22%2C%20%22x%22%3A%204299161%7D%5D)
show a substantial speed improvement over rust's default `regex` crate.

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

