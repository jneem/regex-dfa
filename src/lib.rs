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
