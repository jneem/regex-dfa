use regex_syntax;
use std::error;
use std::fmt;

#[derive(Debug)]
pub enum Error {
    RegexSyntax(regex_syntax::Error),
    Unimplemented(&'static str),
}

use error::Error::*;
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RegexSyntax(ref e) => write!(f, "Regex syntax error: {}", e),
            Unimplemented(s) => write!(f, "Unimplemented: {}", s),
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match *self {
            RegexSyntax(ref e) => e.description(),
            Unimplemented(_) => "You found a regex that's unimplemented",
        }
    }
}

impl From<regex_syntax::Error> for Error {
    fn from(e: regex_syntax::Error) -> Error {
        RegexSyntax(e)
    }
}

