// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::fmt::Debug;
use runner::Engine;
use runner::prefix::{Prefix, AcSearcher, PrefixSearcher, lit_searcher, SimpleSearcher};
use runner::program::Instructions;

#[derive(Clone, Debug)]
pub struct ForwardBackwardEngine<FInsts: Instructions<Ret=(usize, u8)>, BInsts: Instructions> {
    forward: FInsts,
    backward: BInsts,
    prefix: Prefix,
}

impl<FI, BI> ForwardBackwardEngine<FI, BI> where
FI: Instructions<Ret=(usize, u8)>,
BI: Instructions,
BI::Ret: Debug {
    pub fn new(forward: FI, prefix: Prefix, backward: BI) -> Self {
        ForwardBackwardEngine {
            forward: forward,
            backward: backward,
            prefix: prefix,
        }
    }

    fn shortest_match_from_searcher<P: PrefixSearcher>(&self, input: &[u8], mut search: P)
    //fn shortest_match_from_searcher(&self, input: &[u8], search: &mut PrefixSearcher)
    -> Option<(usize, usize, BI::Ret)> {
        while let Some(start) = search.search() {
            match self.forward.shortest_match_from(input, start.end_pos, start.end_state) {
                Ok((end, (rev_state, look_ahead))) => {
                    let rev_pos = end.saturating_sub(look_ahead as usize);
                    let (start_pos, ret) = self.backward
                        .longest_backward_match_from(input, rev_pos, rev_state)
                        .expect("BUG: matched forward but failed to match backward");
                    return Some((start_pos, rev_pos, ret));

                },
                Err(end) => {
                    search.skip_to(end + 1);
                },
            }
        }

        None
    }
}

impl<FI, BI> Engine<BI::Ret> for ForwardBackwardEngine<FI, BI> where
FI: Instructions<Ret=(usize, u8)> + 'static,
BI: Instructions + 'static,
BI::Ret: Debug {
    fn shortest_match(&self, s: &str) -> Option<(usize, usize, BI::Ret)> {
        let input = s.as_bytes();
        if self.forward.is_empty() {
            return None;
        }

        //let mut s = self.prefix.make_searcher(input);
        //self.shortest_match_from_searcher(input, &mut *s)
        run_with_searcher!(self.prefix, input, |s| self.shortest_match_from_searcher(input, s))
    }

    fn clone_box(&self) -> Box<Engine<BI::Ret>> {
        Box::new(self.clone())
    }
}

