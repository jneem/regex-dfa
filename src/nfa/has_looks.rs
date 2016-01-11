// Copyright 2015-2016 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use look::Look;
use nfa::{Accept, HasLooks, LookPair, Nfa, NoLooks};
use nfa::builder::NfaBuilder;
use std::cmp::max;
use std::collections::HashSet;
use std::mem::swap;
use regex_syntax;

impl Nfa<u32, HasLooks> {
    pub fn from_regex(re: &str) -> ::Result<Nfa<u32, HasLooks>> {
        let expr = try!(regex_syntax::Expr::parse(re));
        Ok(NfaBuilder::from_expr(&expr).to_automaton())
    }

    pub fn add_look(&mut self, source: usize, target: usize, behind: Look, ahead: Look) {
        let look = LookPair {
            behind: behind,
            ahead: ahead,
            target_state: target,
        };
        self.states[source].looking.push(look);
    }

    // Removes all the look transitions.
    pub fn remove_looks(mut self) -> Nfa<u32, NoLooks> {
        if self.states.is_empty() {
            return Nfa::with_capacity(0);
        }

        let all_closures: Vec<_> = (0..self.states.len()).map(|s| self.closure(s)).collect();
        let mut new_states: Vec<(usize, Look, usize)> = Vec::new();
        for (state_idx, looks) in all_closures.iter().enumerate() {
            for &look in looks {
                if let Some(new_state) = self.add_state_and_out_trans(state_idx, look) {
                    new_states.push((state_idx, look.behind, new_state));
                }
            }
            self.states[state_idx].looking.clear();
        }

        let rev = self.reversed_transitions();
        for (old_state, look, new_state) in new_states {
            for &(range, src) in rev[old_state].intersection(look.as_set()).ranges_values() {
                self.add_transition(src, new_state, range);
            }
        }

        // We push 0 here because it used to be the implicit start state.
        self.init_mut(Look::Full).push(0);
        self.init_mut(Look::Boundary).push(0);
        for vec in &mut self.init {
            vec.sort();
            vec.dedup();
        }

        let mut ret: Nfa<u32, NoLooks> = self.transmuted();
        ret.trim_unreachable();
        ret
    }

    // Adds a new state for a LookPair and creates all the transitions out of it.
    //
    // Returns the index of the new state (which may not actually be new, for example if look is
    // just a pair of Fulls).
    fn add_state_and_out_trans(&mut self, source_state: usize, look: LookPair) -> Option<usize> {
        let target_state = look.target_state;
        let out_consuming = self.states[target_state].consuming.intersection(look.ahead.as_set());

        // If there is some non-trivial look-behind, we need to create a new state to handle it.
        // Otherwise, we can just add out transitions to source_state.
        let new_state = {
            if look.behind.is_full() {
                source_state
            } else {
                self.add_state(Accept::Never)
            }
        };

        let out_filtered = out_consuming.intersection(look.ahead.as_set());
        for &(range, target) in out_filtered.ranges_values() {
            self.add_transition(new_state, target, range);
        }

        // Set the accept status of the new state. If the look-ahead is full, just copy the accept
        // status of the target state.
        if look.ahead.is_full() {
            self.states[new_state].accept =
                max(self.states[new_state].accept, self.states[target_state].accept);
        } else {
            // If the target states accepts at end of input and the look allows eoi, then the new
            // state must also accept at eoi.
            if self.states[target_state].accept != Accept::Never && look.ahead.allows_eoi() {
                self.states[new_state].accept = Accept::AtEoi;
                self.states[new_state].accept_look = Look::Boundary;
            }

            // If the target state of the look is accepting, add a new look-ahead accepting state.
            if self.states[target_state].accept == Accept::Always {
                let acc_state = self.add_look_ahead_state(look.ahead, 1, new_state);
                for range in look.ahead.as_set().ranges() {
                    self.add_transition(new_state, acc_state, range);
                }
            }
        }

        // Make the new state an initial state, if necessary. Note that we don't need to do this if
        // the look-behind was trivial, since in that case state zero will have the necessary
        // consuming transitions.
        if source_state == 0 && !look.behind.is_full() {
            if look.behind != Look::Boundary {
                self.init[look.behind.as_usize()].push(new_state);
            }
            if look.behind.allows_eoi() {
                self.init[Look::Boundary.as_usize()].push(new_state);
            }
        }

        if look.behind.is_full() { None } else { Some(new_state) }
    }

    // Finds (transitively) the set of all non-consuming transitions that can be make starting
    // from `state`.
    fn closure(&self, state: usize) -> Vec<LookPair> {
        let mut ret: HashSet<LookPair> = self.states[state].looking.iter().cloned().collect();
        let mut new_looks = ret.clone();
        let mut next_looks = HashSet::new();

        while !new_looks.is_empty() {
            for last_look in &new_looks {
                for next_look in &self.states[last_look.target_state].looking {
                    let int = next_look.intersection(last_look);
                    if !int.is_empty() && !ret.contains(&int) {
                        next_looks.insert(int);
                        ret.insert(int);
                    }
                }
            }

            swap(&mut next_looks, &mut new_looks);
            next_looks.clear();
        }

        // Sorting isn't strictly necessary, but it makes this method deterministic which is useful
        // for testing.
        let mut ret: Vec<_> = ret.into_iter().collect();
        ret.sort();
        ret
    }
}

#[cfg(test)]
mod tests {
    use look::Look;
    use nfa::{Accept, NoLooks, Nfa};
    use nfa::tests::{re_nfa, trans_nfa};

    // Creates an Nfa with the given transitions, with initial state zero, and with the final
    // state the only accepting state.
    fn trans_nfa_extra(size: usize, transitions: &[(usize, usize, char)]) -> Nfa<u32, NoLooks> {
        let mut ret: Nfa<u32, NoLooks> = trans_nfa(size, transitions);

        ret.states[size-1].accept = Accept::Always;
        ret.init_mut(Look::Full).push(0);
        ret.init_mut(Look::Boundary).push(0);
        ret
     }

    #[test]
    fn single() {
        let nfa = re_nfa("a");
        let target = trans_nfa_extra(2, &[(0, 1, 'a')]);

        assert_eq!(nfa, target);
    }

    #[test]
    fn alternate() {
        let nfa = re_nfa("a|b");
        let mut target = trans_nfa_extra(3, &[(0, 1, 'a'), (0, 2, 'b')]);
        target.states[1].accept = Accept::Always;

        assert_eq!(nfa, target);
    }

    #[test]
    fn sequence() {
        let nfa = re_nfa("ab");
        let target = trans_nfa_extra(3, &[(0, 1, 'a'), (1, 2, 'b')]);

        assert_eq!(nfa, target);
    }

    #[test]
    fn anchored_start() {
        let nfa = re_nfa("^a");
        let mut target = trans_nfa(2, &[(1, 0, 'a')]);
        target.init_mut(Look::Boundary).push(1);
        target.states[0].accept = Accept::Always;

        assert_eq!(nfa, target);
    }

    #[test]
    fn anchored_end() {
        let nfa = re_nfa("a$");
        let mut target = trans_nfa_extra(2, &[(0, 1, 'a')]);
        target.states[1].accept = Accept::AtEoi;
        target.states[1].accept_look = Look::Boundary;
        target.states[1].accept_state = 1;

        assert_eq!(nfa, target);
    }

    #[test]
    fn word_boundary_start() {
        let nfa = re_nfa(r"\ba");
        let mut target = trans_nfa(2, &[(1, 0, 'a')]);
        target.init_mut(Look::NotWordChar).push(1);
        target.init_mut(Look::Boundary).push(1);
        target.states[0].accept = Accept::Always;

        assert_eq!(nfa, target);
    }

    #[test]
    fn word_boundary_end() {
        let nfa = re_nfa(r"a\b");
        let mut target = trans_nfa_extra(3, &[(0, 1, 'a')]);
        for range in Look::NotWordChar.as_set().ranges() {
            target.add_transition(1, 2, range);
        }
        target.states[1].accept = Accept::AtEoi;
        target.states[1].accept_look = Look::Boundary;
        target.states[1].accept_state = 1;
        target.states[2].accept = Accept::Always;
        target.states[2].accept_look = Look::NotWordChar;
        target.states[2].accept_state = 1;
        target.states[2].accept_tokens = 1;

        assert_eq!(nfa, target);
    }

    #[test]
    fn word_boundary_ambiguous() {
        let nfa = re_nfa(r"\b(a| )");
        let mut target = trans_nfa(4, &[(2, 1, ' '), (3, 0, 'a')]);
        target.states[0].accept = Accept::Always;
        target.states[1].accept = Accept::Always;
        target.init_mut(Look::Boundary).push(3);
        target.init_mut(Look::WordChar).push(2);
        target.init_mut(Look::NotWordChar).push(3);

        assert_eq!(nfa, target);
    }

    #[test]
    fn empty() {
        assert_eq!(re_nfa(""), trans_nfa(0, &[]));
    }
}

