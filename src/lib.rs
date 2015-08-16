// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(slice_splits, test)]

extern crate bit_set;
extern crate regex;
extern crate regex_syntax;
extern crate test;

pub mod automaton;
mod builder;
mod error;
pub mod transition;

pub use error::Error;
