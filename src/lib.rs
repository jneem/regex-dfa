#![feature(collections, core)]
#![allow(dead_code)]

extern crate regex;
extern crate regex_syntax;

pub mod automaton;
pub mod builder;
mod error;
pub mod nfa;
pub mod transition;

pub use error::Error;
