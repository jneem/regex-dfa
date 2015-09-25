// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use regex_syntax;
use std::error;
use std::fmt;

#[derive(Debug)]
pub enum Error {
    RegexSyntax(regex_syntax::Error),
    TooManyStates,
}

use error::Error::*;
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RegexSyntax(ref e) => write!(f, "Regex syntax error: {}", e),
            TooManyStates => write!(f, "State overflow"),
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match *self {
            RegexSyntax(ref e) => e.description(),
            TooManyStates => "This NFA required too many states to represent as a DFA.",
        }
    }
}

impl From<regex_syntax::Error> for Error {
    fn from(e: regex_syntax::Error) -> Error {
        RegexSyntax(e)
    }
}

