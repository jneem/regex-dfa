// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use char_map::{CharMap, CharSet};
use std::fmt;
use std::u32;

#[derive(Clone, PartialEq)]
pub struct ByteSet(pub Box<[bool]>);

impl ByteSet {
    /// Converts from `CharSet` to `ByteSet`. The values in the `CharSet` are interpreted as
    /// bytes, not codepoints.
    ///
    /// # Panics
    ///  - if `cs` contains any elements bigger than `255`.
    pub fn from_char_set(cs: &CharSet) -> ByteSet {
        let mut ret = Box::new([false; 256]);
        for range in cs {
            for b in range.iter() {
                if b > 256 {
                    panic!("tried to convert a non-byte CharSet into a ByteSet");
                }
                ret[b as usize] = true;
            }
        }

        ByteSet(ret)
    }
}

impl<'a> IntoIterator for &'a ByteSet {
    type IntoIter = Box<Iterator<Item=u8> + 'a>;
    type Item = u8;
    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.0.iter().enumerate().filter(|x| *x.1).map(|x| x.0 as u8))
    }
}

impl fmt::Debug for ByteSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let s = self.into_iter()
            .map(|x| format!("{}", x))
            .collect::<Vec<_>>()
            .join(", ");
        try!(f.write_fmt(format_args!("ByteSet ({})", s)));
        Ok(())
    }
}


#[derive(Clone, PartialEq)]
pub struct ByteMap(pub Box<[u32]>);

impl ByteMap {
    pub fn from_char_map(cm: &CharMap<usize>) -> ByteMap {
        let mut ret = Box::new([u32::MAX; 256]);

        for &(range, state) in cm {
            for b in range.iter() {
                if b > 256 {
                    panic!("tried to convert a non-byte CharMap into a ByteMap");
                }
                ret[b as usize] = state as u32;
            }
        }

        ByteMap(ret)
    }

    pub fn map_values<F: FnMut(usize) -> usize>(&mut self, mut f: F) {
        for i in 0..256 {
            if self.0[i] != u32::MAX {
                self.0[i] = f(self.0[i] as usize) as u32;
            }
        }
    }
}

impl<'a> IntoIterator for &'a ByteMap {
    type IntoIter = Box<Iterator<Item=(u8, u32)> + 'a>;
    type Item = (u8, u32);
    fn into_iter(self) -> Self::IntoIter {
        Box::new(
            self.0.iter()
                .enumerate()
                .filter(|x| *x.1 != u32::MAX)
                .map(|(a, &b)| (a as u8, b)))
    }
}

impl fmt::Debug for ByteMap {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let s = self.into_iter()
            .map(|x| format!("{} -> {}", x.0, x.1))
            .collect::<Vec<_>>()
            .join(", ");
        try!(f.write_fmt(format_args!("ByteMap ({})", s)));
        Ok(())
    }
}

