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
[Preliminary benchmarks](http://bl.ocks.org/jneem/raw/3f08ade195796358d027/?data=%5B%7B%22x%22%3A%205561115%2C%20%22y%22%3A%2094501284%2C%20%22ratio%22%3A%200.05884697820613739%2C%20%22bench%22%3A%20%22%5C%5Cb%5C%5Cw%2Bnn%5C%5Cb%22%7D%2C%20%7B%22x%22%3A%201657080%2C%20%22y%22%3A%201664874%2C%20%22ratio%22%3A%200.9953185646481355%2C%20%22bench%22%3A%20%22%5Ba-z%5Dshing%22%7D%2C%20%7B%22x%22%3A%206471113%2C%20%22y%22%3A%20243419316%2C%20%22ratio%22%3A%200.026584221442804482%2C%20%22bench%22%3A%20%22.%7B0%2C2%7D%28Tom%7CSawyer%7CHuckleberry%7CFinn%29%22%7D%2C%20%7B%22x%22%3A%2028486373%2C%20%22y%22%3A%20125978857%2C%20%22ratio%22%3A%200.2261202687368405%2C%20%22bench%22%3A%20%22%5Ba-q%5D%5B%5Eu-z%5D%7B13%7Dx%22%7D%2C%20%7B%22x%22%3A%203560469%2C%20%22y%22%3A%20295351074%2C%20%22ratio%22%3A%200.012055039962373728%2C%20%22bench%22%3A%20%22.%7B2%2C4%7D%28Tom%7CSawyer%7CHuckleberry%7CFinn%29%22%7D%2C%20%7B%22x%22%3A%205585521%2C%20%22y%22%3A%20131818244%2C%20%22ratio%22%3A%200.04237289794271573%2C%20%22bench%22%3A%20%22%28%5BA-Za-z%5Dawyer%7C%5BA-Za-z%5Dinn%29%5C%5Cs%22%7D%2C%20%7B%22x%22%3A%206779240%2C%20%22y%22%3A%2084880712%2C%20%22ratio%22%3A%200.07986785030738197%2C%20%22bench%22%3A%20%22%5C%5Cs%5Ba-zA-Z%5D%7B0%2C12%7Ding%5C%5Cs%22%7D%2C%20%7B%22x%22%3A%201575178%2C%20%22y%22%3A%201620677%2C%20%22ratio%22%3A%200.9719259297194938%2C%20%22bench%22%3A%20%22Huck%5Ba-zA-Z%5D%2B%7CSaw%5Ba-zA-Z%5D%2B%22%7D%2C%20%7B%22x%22%3A%201450277%2C%20%22y%22%3A%207366270%2C%20%22ratio%22%3A%200.1968807822683665%2C%20%22bench%22%3A%20%22%5B%5C%22%27%5D%5B%5E%5C%22%27%5D%7B0%2C30%7D%5B%3F%21%5C%5C.%5D%5B%5C%22%27%5D%22%7D%2C%20%7B%22x%22%3A%201594032%2C%20%22y%22%3A%201646883%2C%20%22ratio%22%3A%200.9679084670860043%2C%20%22bench%22%3A%20%22%28%3Fi%29Twain%22%7D%2C%20%7B%22x%22%3A%209042835%2C%20%22y%22%3A%2071127171%2C%20%22ratio%22%3A%200.12713615448026183%2C%20%22bench%22%3A%20%22%5Ba-zA-Z%5D%2Bing%22%7D%2C%20%7B%22x%22%3A%201631573%2C%20%22y%22%3A%201631615%2C%20%22ratio%22%3A%200.9999742586333173%2C%20%22bench%22%3A%20%22Tom%7CSawyer%7CHuckleberry%7CFinn%22%7D%2C%20%7B%22x%22%3A%205627696%2C%20%22y%22%3A%2062666721%2C%20%22ratio%22%3A%200.08980358171285202%2C%20%22bench%22%3A%20%22%5C%5CbF%5C%5Cw%2Bn%5C%5Cb%22%7D%2C%20%7B%22x%22%3A%201589366%2C%20%22y%22%3A%201724976%2C%20%22ratio%22%3A%200.9213844134643032%2C%20%22bench%22%3A%20%22Tom.%7B10%2C25%7Driver%7Criver.%7B10%2C25%7DTom%22%7D%2C%20%7B%22x%22%3A%201969851%2C%20%22y%22%3A%20137662852%2C%20%22ratio%22%3A%200.014309241537433787%2C%20%22bench%22%3A%20%22%28%3Fi%29Tom%7CSawyer%7CHuckleberry%7CFinn%22%7D%2C%20%7B%22x%22%3A%20103867%2C%20%22y%22%3A%2099739%2C%20%22ratio%22%3A%201.0413880227393497%2C%20%22bench%22%3A%20%22Twain%22%7D%5D)
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

