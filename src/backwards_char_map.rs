// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use char_map::{CharMap, CharRange};
use dfa::{Dfa, DfaAccept};
use nfa::Nfa;
use program::TableInsts;
use transition::Accept;
use std::usize;
use utf8_ranges::Utf8Sequences;

#[derive(Clone, Debug)]
pub struct BackCharMap {
    insts: TableInsts,
    state_at_eoi: Option<usize>,
    fallback_state: Option<usize>,
}

impl BackCharMap {
    pub fn from_char_map(cm: &CharMap<usize>) -> BackCharMap {
        let mut nfa = Nfa::new();
        nfa.add_state(Accept::never());
        nfa.add_init_at_start_state(0);

        for &(range, state) in cm {
            if let Some((start, end)) = range.to_char_pair() {
                for seq in Utf8Sequences::new(start, end) {
                    let mut last = 0usize;
                    for byte_range in seq.into_iter().rev() {
                        nfa.add_state(Accept::never());

                        let target = nfa.num_states() - 1;
                        let range = CharRange::new(byte_range.start as u32, byte_range.end as u32);
                        nfa.add_transition(last, target, range);
                        last = target;
                    }
                    let target = nfa.num_states() - 1;
                    nfa.set_byte_accept(target, DfaAccept::accept(state));
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

