#![feature(bitset, bitvec, iter_arith)]
#![allow(dead_code)]

extern crate regex;
extern crate regex_syntax;

pub mod automaton;
pub mod builder;
mod error;
pub mod transition;

pub use error::Error;
