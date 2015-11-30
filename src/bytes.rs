// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use range_map::{RangeMap, RangeSet};
use std::fmt;
use std::u32;

#[derive(Clone, PartialEq)]
pub struct ByteSet(pub Box<[bool]>);

impl ByteSet {
    /// Converts from `RangeSet` to `ByteSet`.
    pub fn from_range_set(set: &RangeSet<u8>) -> ByteSet {
        let mut ret = Box::new([false; 256]);
        for b in set.elements() {
            ret[b as usize] = true;
        }

        ByteSet(ret)
    }
}

impl fmt::Debug for ByteSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        try!(f.debug_set()
            .entries(self.0.iter().enumerate().filter(|x| *x.1).map(|x| x.0))
            .finish());
        Ok(())
    }
}

#[derive(Clone, PartialEq)]
pub struct ByteMap(pub Box<[u32]>);

impl ByteMap {
    pub fn from_range_map(map: &RangeMap<u8, usize>) -> ByteMap {
        let mut ret = Box::new([u32::MAX; 256]);

        for (b, &state) in map.keys_values() {
            ret[b as usize] = state as u32;
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

impl fmt::Debug for ByteMap {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        try!(f.debug_map()
            .entries(self.0.iter().enumerate().filter(|x| *x.1 != u32::MAX))
            .finish());
        Ok(())
    }
}


