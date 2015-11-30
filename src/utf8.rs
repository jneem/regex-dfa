// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use itertools::Itertools;
use range_map::Range;
use std::char;
use utf8_ranges::{Utf8Range, Utf8Sequence, Utf8Sequences};

/// This provides a more compact way of representing UTF-8 sequences.
///
/// A sequence of bytes belongs to this set if its first byte is in `head[0]`, its second byte is
/// in `head[1]`, etc., and its last byte belongs to one of the ranges in `last_byte`.
///
/// This representation is handy for making NFAs because compared to the representation in
/// `Utf8Sequences`, it adds many fewer states. Basically, we are doing some crude minimization
/// before creating the states.
pub struct MergedUtf8Sequences {
    pub head: Vec<Utf8Range>,
    pub last_byte: Vec<Utf8Range>,
}

// Returns this range as a pair of chars, or none if this is an empty range.
fn to_char_pair(r: Range<u32>) -> Option<(char, char)> {
    // Round up self.start to the nearest legal codepoint.
    let start = if r.start > 0xD7FF && r.start < 0xE000 {
        0xE000
    } else {
        r.start
    };

    // Round down self.end.
    let end = if r.end > 0x10FFFF {
        0x10FFFF
    } else if r.end < 0xE000 && r.end > 0xD7FF {
        0xD7FF
    } else {
        r.end
    };

    if start > end {
        None
    } else {
        Some((char::from_u32(start).unwrap(), char::from_u32(end).unwrap()))
    }
}

impl MergedUtf8Sequences {
    // Panics if not all the input sequences have the same leading byte ranges.
    fn merge<I>(iter: I) -> MergedUtf8Sequences where I: Iterator<Item=Utf8Sequence> {
        let mut head = Vec::new();
        let mut last_byte = Vec::new();

        for seq in iter {
            let len = seq.len();
            let h = &seq.as_slice()[..len-1];
            if head.is_empty() {
                head.extend(h);
            } else if &head[..] != h {
                panic!("invalid sequences to merge");
            }

            last_byte.push(seq.as_slice()[len-1]);
        }

        MergedUtf8Sequences {
            head: head,
            last_byte: last_byte,
        }
    }

    fn from_sequences<'a, I>(iter: I) -> Box<Iterator<Item=MergedUtf8Sequences> + 'a>
    where I: Iterator<Item=Utf8Sequence> + 'a {
        fn head(u: &Utf8Sequence) -> Vec<Utf8Range> {
            let len = u.len();
            u.as_slice()[..len-1].to_owned()
        }

        Box::new(iter
            .group_by(head)
            .into_iter()
            .map(|(_, seqs)| MergedUtf8Sequences::merge(seqs.into_iter())))
    }

    pub fn from_ranges<'a, I>(iter: I) -> Box<Iterator<Item=MergedUtf8Sequences> + 'a>
    where I: Iterator<Item=Range<u32>> + 'a {
        MergedUtf8Sequences::from_sequences(
            iter.filter_map(to_char_pair)
                .flat_map(|r| Utf8Sequences::new(r.0, r.1)))
    }
}

