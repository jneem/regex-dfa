// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use char_map::CharMap;
use std::u32;

#[derive(Clone, Debug, PartialEq)]
pub struct ByteSet(pub Box<[bool]>);

impl ByteSet {
    pub fn len(&self) -> usize {
        self.into_iter().count()
    }
}

impl<'a> IntoIterator for &'a ByteSet {
    type IntoIter = Box<Iterator<Item=u8> + 'a>;
    type Item = u8;
    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.0.iter().enumerate().filter(|x| *x.1).map(|x| x.0 as u8))
    }
}

#[derive(Clone, Debug, PartialEq)]
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

    pub fn len(&self) -> usize {
        self.into_iter().count()
    }

    pub fn to_set(&self) -> ByteSet {
        self.filter_values(|x| x != u32::MAX)
    }

    pub fn filter_values<F: FnMut(u32) -> bool>(&self, mut f: F) -> ByteSet {
        let mut ret = Box::new([false; 256]);
        for (i, &state) in self.0.iter().enumerate() {
            if f(state) {
                ret[i] = true;
            }
        }
        ByteSet(ret)
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

