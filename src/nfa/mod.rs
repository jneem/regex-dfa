// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use itertools::Itertools;
use look::Look;
use num::traits::PrimInt;
use range_map::{Range, RangeMap, RangeMultiMap};
use std::fmt::{self, Debug, Formatter};
use std::marker::PhantomData;

mod builder;
mod has_looks;
mod no_looks;

/// How we represent a set of states. The two important criteria are:
///
/// - it should be reasonably fast even when there are thousands of states (this knocks out
///   BitSet), and
/// - it should be hashable (this knocks out HashSet).
///
/// Note that efficient insertion and O(1) queries are not important. Therefore, we use a sorted
/// Vec. (But be careful to keep it sorted!)
pub type StateSet = Vec<usize>;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct LookPair {
    pub behind: Look,
    pub ahead: Look,
    pub target_state: usize,
}

impl LookPair {
    pub fn is_empty(&self) -> bool {
        self.behind == Look::Empty || self.ahead == Look::Empty
    }

    pub fn intersection(&self, other: &LookPair) -> LookPair {
        LookPair {
            behind: self.behind.intersection(&other.behind),
            ahead: self.ahead.intersection(&other.ahead),
            target_state: self.target_state,
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Accept {
    Never,
    AtEoi,
    Always,
}

#[derive(Clone, Eq, PartialEq)]
pub struct State<Tok> {
    accept: Accept,
    // If accept == Always and accept_tokens > 0, then we had to do some look-ahead in order to
    // determine that we have a match. In that case, accept_state is the index of the state that
    // should have accepted.
    accept_state: usize,
    // In the case that we had some look-ahead, `accept_look` says what kind of char was involved
    // in the look-ahead, and `accept_tokens` says how many input tokens were consumed while
    // looking ahead. There are some restrictions on these values:
    // - if accept is Never then accept_look is Full and accept_tokens is zero
    // - if accept is AtEoi then accept_look is Boundary and accept_tokens is zero
    // - accept_look is never Empty
    // - if accept is Always then accept_look is neither empty nor Boundary
    // - if Tok is u32 then accept_tokens is either 0 or 1
    // - if Tok is u8 then accept_tokens is at most 4.
    accept_look: Look,
    accept_tokens: u8,

    consuming: RangeMultiMap<Tok, usize>,
    looking: Vec<LookPair>,
}

#[derive(Clone, Eq, PartialEq)]
pub struct Nfa<Tok, Variant> {
    states: Vec<State<Tok>>,
    init: Vec<StateSet>,
    phantom: PhantomData<Variant>,
}

pub trait Lookability {}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct HasLooks;
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct NoLooks;

impl Lookability for HasLooks {}
impl Lookability for NoLooks {}

impl<Tok: Debug + PrimInt, L: Lookability> Nfa<Tok, L> {
    pub fn with_capacity(n: usize) -> Nfa<Tok, L> {
        Nfa {
            states: Vec::with_capacity(n),
            init: vec![StateSet::new(); Look::num()],
            phantom: PhantomData,
        }
    }

    pub fn reversed_transitions(&self) -> Vec<RangeMultiMap<Tok, usize>> {
        let mut ret = vec![RangeMultiMap::new(); self.states.len()];

        for (source_idx, st) in self.states.iter().enumerate() {
            for &(range, target_idx) in st.consuming.ranges_values() {
                ret[target_idx].insert(range, source_idx);
            }
        }
        ret
    }

    /// Adds a new state and returns its index.
    pub fn add_state(&mut self, accept: Accept) -> usize {
        let state_idx = self.states.len();
        self.states.push(State {
            accept: accept,
            accept_state: state_idx,
            accept_look: if accept == Accept::AtEoi { Look::Boundary } else { Look::Full },
            accept_tokens: 0,
            consuming: RangeMultiMap::new(),
            looking: Vec::new(),
        });
        state_idx
    }

    pub fn add_look_ahead_state(&mut self, look: Look, tokens: u8, accept_state: usize)
    -> usize {
        let accept = if look == Look::Boundary { Accept::AtEoi } else { Accept::Always };
        let state_idx = self.states.len();
        self.states.push(State {
            accept: accept,
            accept_state: accept_state,
            accept_look: look,
            accept_tokens: tokens,
            consuming: RangeMultiMap::new(),
            looking: Vec::new(),
        });
        state_idx
    }

    /// Adds a transition that moves from `source` to `target` on consuming a token in `range`.
    pub fn add_transition(&mut self, source: usize, target: usize, range: Range<Tok>) {
        self.states[source].consuming.insert(range, target);
    }

    pub fn add_look(&mut self, source: usize, target: usize, behind: Look, ahead: Look) {
        let look = LookPair {
            behind: behind,
            ahead: ahead,
            target_state: target,
        };
        self.states[source].looking.push(look);
    }

    // You've just done some operation that has changed state indices (probably by deleting
    // un-needed states). Now re-label the existing transitions according to the new state indices.
    fn map_states<F>(&mut self, map: F) where F: Fn(usize) -> Option<usize> {
        for st in &mut self.states {
            st.consuming.retain_values(|x| map(*x).is_some());
            // The unwrap is ok because we've just filtered all the `None`s (and `map` is Fn, not
            // FnMut).
            st.consuming.map_values(|x| map(*x).unwrap());

            st.looking = st.looking.iter()
                .filter(|look| map(look.target_state).is_some())
                // The unwrap is ok because we've just filtered all the `None`s.
                .map(|look| LookPair { target_state: map(look.target_state).unwrap(), .. *look })
                .collect();

            st.accept_state = map(st.accept_state).expect("bug in map_states");
        }

        for vec in &mut self.init {
            *vec = vec.iter().filter_map(|x| map(*x)).collect();
            vec.sort();
            vec.dedup();
        }
    }

    // Returns all possible initial states.
    fn initial_states(&self) -> StateSet {
        let mut init_states = Vec::new();
        for s in &self.init {
            init_states.extend(s);
        }
        init_states.sort();
        init_states.dedup();
        init_states
    }

    // Returns all possible final states.
    fn final_states(&self) -> StateSet {
        let mut final_states = StateSet::new();
        for (idx, s) in self.states.iter().enumerate() {
            if s.accept != Accept::Never {
                final_states.push(idx);
            }
        }
        final_states.sort();
        final_states.dedup();
        final_states
    }

    fn transmuted<NewL: Lookability>(self) -> Nfa<Tok, NewL> {
        Nfa {
            states: self.states,
            init: self.init,
            phantom: PhantomData,
        }
    }

    fn init_mut(&mut self, look: Look) -> &mut StateSet {
        &mut self.init[look.as_usize()]
    }

    // Finds the transitions out of the given set of states, as a RangeMap.
    fn transition_map(&self, states: &StateSet) -> RangeMap<Tok, StateSet> {
        let trans = states.into_iter()
            .flat_map(|s| self.states[*s].consuming.ranges_values().cloned())
            .collect();
        RangeMultiMap::from_vec(trans).group()
    }

    pub fn has_look_behind(&self) -> bool {
        Look::all().iter().any(|&look|
            look != Look::Full
            && look != Look::Boundary
            && !self.init[look.as_usize()].is_empty()
        )
    }

    /// Returns true if this Nfa only matches things at the beginning of the input.
    pub fn is_anchored(&self) -> bool {
        !self.init[Look::Boundary.as_usize()].is_empty()
            && self.init.iter().filter(|x| !x.is_empty()).count() == 1
    }

    /// Returns true if this Nfa never matches anything.
    pub fn is_empty(&self) -> bool {
        self.states.is_empty()
    }
}

impl<Tok: Debug + PrimInt, L: Lookability> Debug for Nfa<Tok, L> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        try!(f.write_fmt(format_args!("Nfa ({} states):\n", self.states.len())));

        try!(f.write_fmt(format_args!("Init: {:?}\n", self.init)));

        for (st_idx, st) in self.states.iter().enumerate().take(40) {
            try!(f.write_fmt(format_args!("\tState {} ({:?}):\n", st_idx, st.accept)));

            if st.accept != Accept::Never {
                try!(f.write_fmt(format_args!("\t\tlook {:?}, tokens {:?}, state {:?}\n",
                                              st.accept_look, st.accept_tokens, st.accept_state)));
            }
            if !st.consuming.is_empty() {
                try!(f.write_str("\t\tConsuming:\n"));
                // Cap it at 5 transitions, since it gets unreadable otherwise.
                for &(range, target) in st.consuming.ranges_values().take(5) {
                    try!(f.write_fmt(format_args!("\t\t\t{:?} -- {:?} => {}\n",
                                                  range.start, range.end, target)));
                }
                if st.consuming.num_ranges() > 5 {
                    try!(f.write_str("\t\t\t...\n"));
                }
            }
            if !st.looking.is_empty() {
                try!(f.write_str("\t\tLooking:\n"));
                for look in &st.looking {
                    try!(f.write_fmt(format_args!("\t\t\t({:?},{:?}) => {}\n",
                        look.behind, look.ahead, look.target_state)));
                }
            }
        }
        if self.states.len() > 40 {
            try!(f.write_fmt(format_args!("\t... ({} more states)\n", self.states.len() - 40)));
        }
        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use nfa::{Accept, NoLooks, Nfa};
    use num::traits::PrimInt;
    use range_map::Range;
    use std::fmt::Debug;

    pub fn re_nfa(re: &str) -> Nfa<u32, NoLooks> {
        Nfa::from_regex(re).unwrap().remove_looks()
    }

    pub fn trans_range_nfa<Tok>(size: usize, transitions: &[(usize, usize, Range<Tok>)])
    -> Nfa<Tok, NoLooks>
    where Tok: Debug + PrimInt {
        let mut ret: Nfa<Tok, NoLooks> = Nfa::with_capacity(size);
        for _ in 0..size {
            ret.add_state(Accept::Never);
        }
        for &(src, tgt, range) in transitions {
            ret.add_transition(src, tgt, range);
        }
        ret
    }

    // Creates an Nfa with the given transitions.
    pub fn trans_nfa<Tok>(size: usize, transitions: &[(usize, usize, char)])
    -> Nfa<Tok, NoLooks>
    where Tok: Debug + PrimInt {
        let tok = |x: char| -> Tok { Tok::from(x as u32).unwrap() };
        let range_trans: Vec<_> = transitions.iter()
            .map(|x| (x.0, x.1, Range::new(tok(x.2), tok(x.2))))
            .collect();
        trans_range_nfa(size, &range_trans)
    }
}

