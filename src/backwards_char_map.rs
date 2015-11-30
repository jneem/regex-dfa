// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use dfa::{Dfa, DfaAccept};
use itertools::Itertools;
use nfa::Nfa;
use program::TableInsts;
use range_map::{Range, RangeMap};
use transition::Accept;
use std::usize;
use utf8::MergedUtf8Sequences;

#[derive(Clone, Debug)]
pub struct BackCharMap {
    insts: TableInsts,
    state_at_eoi: Option<usize>,
    fallback_state: Option<usize>,
}

impl BackCharMap {
    pub fn from_range_map(map: &RangeMap<u32, usize>) -> BackCharMap {
        let mut nfa = Nfa::new();
        nfa.add_state(Accept::never());
        nfa.add_init_at_start_state(0);

        let mut map_copy: Vec<_> = map.ranges_values().collect();
        map_copy.sort_by(|x, y| x.1.cmp(&y.1)); // Sort by the target state.
        let grouped = map_copy.into_iter().group_by_lazy(|pair| pair.1);

        // Iterator over (state, Iterator over Range<u32>)
        let states_ranges = grouped.into_iter().map(|(v, rv)| (v, rv.map(|x| x.0)));

        for (state, ranges) in states_ranges {
            for seq in MergedUtf8Sequences::from_ranges(ranges) {
                let mut last = 0usize;

                for range in seq.head.iter() {
                    nfa.add_state(Accept::never());
                    let new_idx = nfa.num_states() - 1;
                    let range = Range::new(range.start as u32, range.end as u32);
                    nfa.add_transition(last, new_idx, range);
                    last = new_idx;
                }

                for range in seq.last_byte.iter() {
                    nfa.add_dfa_state(DfaAccept::accept(state));
                    let new_idx = nfa.num_states() - 1;
                    let range = Range::new(range.start as u32, range.end as u32);
                    nfa.add_transition(last, new_idx, range);
                }
            }
        }

        // This unwrap is ok because the only failure in `from_nfa_bounded` is if we overrun the
        // maximum number of states.
        let dfa = Dfa::from_nfa_bounded(&nfa, usize::MAX).unwrap();
        let bcm = BackCharMap {
            insts: dfa.to_table_insts(),
            state_at_eoi: None,
            fallback_state: None,
        };

        bcm
    }

    pub fn set_fallback(&mut self, state: usize) {
        self.fallback_state = Some(state);
    }

    pub fn set_eoi(&mut self, state: usize) {
        self.state_at_eoi = Some(state);
    }

    pub fn run(&self, input: &[u8], mut pos: usize) -> Option<usize> {
        if pos == 0 {
            return self.state_at_eoi;
        }

        let mut state = 0;
        let len = self.insts.accept.len();
        while state < len {
            if self.insts.accept[state] != usize::MAX {
                return Some(self.insts.accept[state]);
            }

            if pos == 0 {
                break;
            } else {
                pos -= 1;
                state = self.insts.table[state * 256 + input[pos] as usize] as usize;
            }
        }

        self.fallback_state
    }
}

