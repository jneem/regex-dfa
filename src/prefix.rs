// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use dfa::{Dfa, RetTrait};
use nfa::Accept;
use std::collections::VecDeque;
use std::mem::swap;
use trie::Trie;

// TODO: These limits are pretty arbitrary (copied from the regex crate).
const NUM_PREFIX_LIMIT: usize = 30;
const PREFIX_LEN_LIMIT: usize = 15;

/// A pair of a byte sequence and the index of the state that we are in after encountering that
/// sequence.
#[derive(Debug, Clone)]
pub struct PrefixPart(pub Vec<u8>, pub usize);

pub struct PrefixSearcher {
    active: VecDeque<PrefixPart>,
    current: PrefixPart,
    suffixes: Trie,
    prune_suffixes: bool,
    pub finished: Vec<PrefixPart>,

    // The set of prefixes is complete if:
    //  - we're done with active prefixes before we go over any of our limits, and
    //  - we didn't encounter any states that accept conditionally.
    complete: bool,

    max_prefixes: usize,
    max_len: usize,
}

impl PrefixSearcher {
    pub fn new(prune: bool) -> PrefixSearcher {
        PrefixSearcher {
            active: VecDeque::new(),
            current: PrefixPart(Vec::new(), 0),
            suffixes: Trie::new(),
            prune_suffixes: prune,
            finished: Vec::new(),
            complete: true,
            max_prefixes: NUM_PREFIX_LIMIT,
            max_len: PREFIX_LEN_LIMIT,
        }
    }

    fn bail_out(&mut self) {
        let mut current = PrefixPart(Vec::new(), 0);
        let mut active = VecDeque::new();
        swap(&mut current, &mut self.current);
        swap(&mut active, &mut self.active);

        self.finished.extend(active.into_iter());
        self.finished.push(current);
        self.complete = false;
    }

    fn add(&mut self, new_prefs: Vec<PrefixPart>) {
        debug_assert!(new_prefs.len() + self.active.len() + self.finished.len() <= self.max_prefixes);

        for p in new_prefs.into_iter() {
            if p.0.len() >= self.max_len {
                self.finished.push(p);
            } else {
                self.active.push_back(p);
            }
        }
    }

    fn too_many(&mut self, more: usize) -> bool {
        self.active.len() + self.finished.len() + more > self.max_prefixes
    }

    pub fn search<T: RetTrait>(&mut self, dfa: &Dfa<T>, state: usize) {
        self.active.push_back(PrefixPart(Vec::new(), state));
        self.suffixes.insert(vec![].into_iter(), state);
        while !self.active.is_empty() {
            self.current = self.active.pop_front().unwrap();

            let trans = dfa.transitions(self.current.1);
            let mut next_prefs = Vec::new();
            for (ch, next_state) in trans.keys_values() {
                let mut next_pref = self.current.0.clone();
                next_pref.push(ch);
                next_prefs.push(PrefixPart(next_pref, *next_state));
            }

            // If we're asked to prune, discard any new prefix that is the suffix of some existing
            // prefix.
            if self.prune_suffixes {
                next_prefs.retain(|pref| {
                    let rev_bytes = pref.0.iter().cloned().rev();
                    !self.suffixes
                        .prefixes(rev_bytes)
                        .any(|s| s == pref.1)
                });
                for pref in &next_prefs {
                    self.suffixes.insert(pref.0.iter().cloned().rev(), pref.1);
                }
            }

            // Stop searching if we have too many prefixes already, or if we've run into an accept
            // state. In principle, we could continue expanding the other prefixes even after we
            // run into an accept state, but there doesn't seem much point in having some short
            // prefixes and other long prefixes.
            if self.too_many(next_prefs.len())
                || *dfa.accept(self.current.1) != Accept::Never {
                self.bail_out();
                break;
            }


            self.add(next_prefs);
        }
    }

    pub fn map_states<F: FnMut(usize) -> usize>(&mut self, mut f: F) {
        for part in &mut self.finished {
            part.1 = f(part.1);
        }
    }
}


#[cfg(test)]
mod tests {
    use dfa;
    use look::Look;
    use prefix::*;

    macro_rules! test_prefix {
        ($name:ident, $pruned:expr, $re_str:expr, $answer:expr, $max_num:expr, $max_len:expr) => {
            #[test]
            fn $name() {
                let dfa = dfa::tests::make_dfa($re_str).unwrap();
                let mut pref = PrefixSearcher::new($pruned);
                pref.max_prefixes = $max_num;
                pref.max_len = $max_len;
                pref.search(&dfa, dfa.init_state(Look::Boundary).unwrap());
                let mut prefs = pref.finished.into_iter().map(|x| x.0).collect::<Vec<_>>();
                prefs.sort();

                let answer: Vec<Vec<u8>> = $answer.iter()
                    .map(|s| s.as_bytes().to_owned())
                    .collect();
                assert_eq!(prefs, answer);
            }
        };
    }

    test_prefix!(long, false,
        "[XYZ]ABCDEFGHIJKLMNOPQRSTUVWXYZ",
        vec!["XABCDEFGHIJKLMNOPQRSTUVWXYZ",
           "YABCDEFGHIJKLMNOPQRSTUVWXYZ",
           "ZABCDEFGHIJKLMNOPQRSTUVWXYZ",],
        3, 30);

    test_prefix!(case_insensitive, false,
        "(?i)abc[a-z]",
        vec!["ABC", "ABc", "AbC", "Abc", "aBC", "aBc", "abC", "abc"],
        30, 5);

    test_prefix!(byte_set, false,
        "[ac]",
        vec!["a", "c"],
        30, 5);

    test_prefix!(unpruned_repetition, false,
        "a+bc",
        vec!["aaaa", "aaab", "aabc", "abc"],
        10, 10);

    test_prefix!(pruned_repetition, true,
        "a+bc",
        vec!["abc"],
        10, 10);
    test_prefix!(pruned_empty_repetition, true,
        "[a-zA-Z]*bc",
        vec!["bc"],
        10, 10);
}

