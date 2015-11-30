// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use builder::NfaBuilder;
use dfa::{Dfa, DfaAccept};
use error;
use itertools::Itertools;
use range_map::{Range, RangeMap, RangeMultiMap};
use regex_syntax;
use std;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter};
use std::mem;
use std::result::Result;
use transition::{Accept, NfaTransitions, Predicate, SetOps, StateSet};
use utf8::MergedUtf8Sequences;

// Variations of `Nfa`:
//  - it can have predicate transitions or not
//  - it can have start state depending on the preceding char (lookbehind)
//  - it can have accept state depending on the following char (lookahead). If not, it stores
//    bytes_ago.
//  - it can be byte-based or char-based
//
// Transformations:
//  - remove_predicates takes a machine that has predicate transitions but no lookbehind and turns
//    it into a machine without predicated transitions, but with lookbehind and lookahead.
//  - remove_lookbehind (potential name) takes a machine with lookbehind and gets rid of it (but it
//    also loses information about the start of the match)
//  - remove_lookahead (potential name) takes a machine with lookahead and gets rid of it
//  - byte_me takes a char machine and turns it into a byte machine
//
// Differences in storing these variations:
//  - the transitions might need predicates
//  - the accept struct might change
//  - we might have to store a table of prev_char -> start_state
//  - the transitions might be indexed by different things (bytes vs chars)

#[derive(Clone, PartialEq, Debug)]
pub struct NfaState {
    pub transitions: NfaTransitions,
    /// Before calling `byte_me()`, this determines whether we accept or not.
    pub accept: Accept,
    /// After calling `byte_me()`, this determines whether we accept or not.
    pub dfa_accept: DfaAccept,
}

impl NfaState {
    pub fn new(accept: Accept) -> NfaState {
        NfaState {
            transitions: NfaTransitions::new(),
            accept: accept,
            dfa_accept: DfaAccept::never(),
        }
    }
}

/// `Nfa` represents a non-deterministic finite automaton. We do not provide any support for
/// actually executing the automaton directly; its main purpose is to turn into a `Dfa`.
///
/// By default, `Nfa` represents an "unanchored" automaton, meaning that if we were to execute
/// it on some input then it could match any subset of the input, not just the part starting at
/// the beginning. In terms of regexes, it's like having an implicit ".*" at the start.
///
/// The initial state of an `Nfa` always includes state zero, but see also the documentation for
/// `init_at_start` and `init_after_char`.
#[derive(Clone, PartialEq)]
pub struct Nfa {
    states: Vec<NfaState>,

    /// The set of initial states.
    init: StateSet,

    /// Sometimes we want to only match at the beginning of the text; we can represent this
    /// using `init_at_start`, which is a set of states that are all valid as starting states,
    /// but only if we start matching at the beginning of the input.
    ///
    /// Note that `transition::Predicate` provides another, higher-level, way to represent the same
    /// information. Before turning this `Nfa` into a `Dfa`, we will lower the
    /// `transition::Predicate` representation into this one.
    init_at_start: StateSet,

    /// Sometimes we want to begin in a particular state only if the char before the substring we
    /// are trying to match is in a particular class. (For example, this is used to implement word
    /// boundaries.) This is represented by `init_after_char`: if the char before the current
    /// position (call it `ch`) is in `init_after_char` then we start in all the states in
    /// `init_after_char.get(ch)`.
    init_after_char: RangeMap<u32, StateSet>,
}

impl Debug for Nfa {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        try!(f.write_fmt(format_args!("Nfa ({} states):\n", self.states.len())));
        try!(f.write_fmt(format_args!("Initial: {:?}\n", self.init)));
        if !self.init_at_start.is_empty() {
            try!(f.write_fmt(format_args!("Initial_at_start: {:?}\n", self.init_at_start)));
        }

        if !self.init_after_char.is_empty() {
            try!(f.write_fmt(format_args!("Initial_after_char: {:?}\n", self.init_after_char)));
        }

        for (st_idx, st) in self.states.iter().enumerate() {
            try!(f.write_fmt(format_args!("\tState {}:\n", st_idx)));
            try!(f.write_fmt(format_args!("\t\tAccept: {:?}\n", st.accept)));
            try!(f.write_fmt(format_args!("\t\tDfa_accept: {:?}\n", st.dfa_accept)));

            if !st.transitions.consuming.is_empty() {
                try!(f.write_fmt(format_args!("\t\tTransitions: {:?}\n", st.transitions.consuming)));
            }

            if !st.transitions.eps.is_empty() {
                try!(f.write_fmt(format_args!("\t\tEps-transitions: {:?}\n", &st.transitions.eps)));
            }

            if !st.transitions.predicates.is_empty() {
                try!(f.write_fmt(format_args!("\t\tPredicates: {:?}\n", &st.transitions.predicates)));
            }
        }
        Ok(())
    }
}

impl Nfa {
    pub fn from_regex(re: &str) -> Result<Nfa, error::Error> {
        let expr = try!(regex_syntax::Expr::parse(re));
        Ok(NfaBuilder::from_expr(&expr).to_automaton())
    }

    pub fn new() -> Nfa {
        Nfa::with_capacity(0)
    }

    pub fn with_capacity(n: usize) -> Nfa {
        Nfa {
            states: Vec::with_capacity(n),
            init: StateSet::new(),
            init_at_start: StateSet::new(),
            init_after_char: RangeMap::new(),
        }
    }

    pub fn add_init_state(&mut self, st: usize) {
        if st > self.states.len() - 1 {
            panic!("invalid initial state");
        }
        self.init.push(st);
        self.init.sort();
    }

    pub fn add_init_at_start_state(&mut self, st: usize) {
        if st > self.states.len() - 1 {
            panic!("invalid initial state");
        }
        self.init_at_start.push(st);
        self.init_at_start.sort();
    }

    pub fn add_transition(&mut self, from: usize, to: usize, r: Range<u32>) {
        self.states[from].transitions.consuming.insert(r, to);
    }

    pub fn add_state(&mut self, accept: Accept) {
        self.states.push(NfaState::new(accept));
    }

    pub fn add_eps(&mut self, from: usize, to: usize) {
        self.states[from].transitions.eps.push(to);
    }

    pub fn add_predicate(&mut self, from: usize, to: usize, pred: Predicate) {
        self.states[from].transitions.predicates.push((pred, to));
    }

    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    pub fn add_dfa_state(&mut self, accept: DfaAccept) {
        self.states.push(NfaState::new(Accept::never()));
        self.states.last_mut().unwrap().dfa_accept = accept;
    }

    /// Adds a path from `start_state` to `end_state` for all byte sequences matching `seq`.
    ///
    /// If `end_state` is None, then the last state becomes an accepting state that rewinds
    /// to the beginning of the sequence.
    ///
    /// All the transitions in this path are byte transitions, not char transitions.
    fn add_utf8_sequence(
        &mut self,
        start_state: usize,
        end_state: Option<usize>,
        seq: MergedUtf8Sequences
    ) {
        let mut last_state = start_state;
        for range in &seq.head {
            self.add_state(Accept::never());
            let cur_state = self.states.len() - 1;
            let range = Range::new(range.start as u32, range.end as u32);

            self.add_transition(last_state, cur_state, range);
            last_state = cur_state;
        }

        let end_state = if let Some(e) = end_state {
            e
        } else {
            self.add_state(Accept::never());
            let e = self.states.len() - 1;
            self.states[e].dfa_accept = DfaAccept::accept(seq.head.len() + 1);
            e
        };

        for range in &seq.last_byte {
            let range = Range::new(range.start as u32, range.end as u32);
            self.add_transition(last_state, end_state, range);
        }
    }

    fn add_utf8_sequences<I>(
        &mut self,
        start_state: usize,
        ranges: I,
        target: Option<usize>,
        max_states: usize)
    -> Result<(), error::Error>
    where I: Iterator<Item=Range<u32>> {
        for m in MergedUtf8Sequences::from_ranges(ranges) {
            self.add_utf8_sequence(start_state, target, m);
            if self.states.len() > max_states {
                return Err(error::Error::TooManyStates);
            }
        }
        Ok(())
    }

    /// Converts all the transitions in this automaton into byte transitions.
    ///
    /// This doesn't do anything to predicates, so you probably want to `remove_predicates()`
    /// first.
    fn byte_me(&mut self, max_states: usize) -> Result<(), error::Error> {
        for i in 0..self.states.len() {
            let mut trans = RangeMultiMap::new();
            mem::swap(&mut trans, &mut self.states[i].transitions.consuming);

            // Group transitions by the target state, and add them in batches. Most of the time, we
            // can merge a bunch of Utf8Sequences before adding them, which saves a bunch of
            // states.
            let mut trans = trans.into_vec();
            trans.sort_by(|x, y| x.1.cmp(&y.1));
            for (tgt, transitions) in trans.into_iter().group_by(|x| x.1) {
                try!(self.add_utf8_sequences(
                        i,
                        transitions.into_iter().map(|x| x.0),
                        Some(tgt),
                        max_states));
            }
        }
        Ok(())
    }

    /// Convert from using Accept to DfaAccept.
    fn byte_accept(&mut self, max_states: usize) -> Result<(), error::Error> {
        for i in 0..self.states.len() {
            self.states[i].dfa_accept.at_eoi = self.states[i].accept.at_eoi;
            if self.states[i].accept.at_char.is_full() {
                debug_assert!(self.states[i].accept.at_eoi);
                self.states[i].dfa_accept.otherwise = true;
            } else if !self.states[i].accept.at_char.is_empty() {
                let ranges = self.states[i].accept.at_char.clone();
                try!(self.add_utf8_sequences(
                        i,
                        ranges.ranges(),
                        None,
                        max_states));
            }
        }
        Ok(())
    }

    /// Modifies this automaton to remove all transition predicates.
    ///
    /// Note that this clobbers `init_at_start` and `init_after_char`, so you probably don't want
    /// to call this if those are already set. In particular, calling `remove_predicates()` twice
    /// on the same `Nfa` is probably a bad idea.
    fn remove_predicates(&mut self) {
        self.init_at_start = self.init.clone();

        // Sometimes an InClasses predicate is attached to the initial state. This map keeps track
        // of such predicates: if `initial_preds` contains the map 'a' -> 3, for example, then if
        // we just saw the character 'a' we should start in the state 3.
        let mut initial_preds = RangeMultiMap::<u32, usize>::new();

        let mut changed = self.remove_predicates_once(&mut initial_preds);
        while changed {
            changed = self.remove_predicates_once(&mut initial_preds);
        }
        self.init_after_char = initial_preds.group();
    }

    // This is the algorithm for removing predicates, which we run repeatedly until
    // we reach a fixed point.
    //  for every predicate {
    //      suppose the predicate goes from state a to state b
    //      make a new state
    //      for every transition or predicate leading into a {
    //          make a copy of that transition leading into the new state
    //      }
    //      for every transition or predicate leading out of b {
    //          make a copy of that transition leading out of the new state
    //      }
    //  }
    // Above, when we say "leading into" or "leading out of," that includes eps-closures.
    //
    // TODO: this function is pretty generous about adding extra states. We could be much more
    // stingy about extra states, e.g. at predicates only matching the beginning or end of input.
    // (Although this is rather less crucial now that we are trimming unreachable states.)
    fn remove_predicates_once(&mut self, initial_preds: &mut RangeMultiMap<u32, usize>) -> bool {
        let orig_len = self.states.len();
        let mut reversed = self.reversed();

        for idx in 0..self.states.len() {
            let preds = self.states[idx].transitions.predicates.clone();
            self.states[idx].transitions.predicates.clear();
            // Also remove the preds from our reversed copy.
            for (_, &(_, target)) in preds.iter().enumerate() {
                reversed.states[target].transitions.predicates.retain(|&(_, s)| s != idx);
            }

            for &(ref pred, pred_target_idx) in &preds {
                let in_states = reversed.eps_closure_single(idx);
                let out_states = self.eps_closure_single(pred_target_idx);
                let (in_trans, out_trans) =
                    pred.filter_transitions(&reversed.transitions(&in_states),
                                            &self.transitions(&out_states));

                let acc = self.predicate_accept(pred, &out_states);
                self.states.push(NfaState::new(acc));
                // We only keep `reversed` around for its transitions and predicates, so it doesn't
                // matter what we pass for `accept` here.
                reversed.states.push(NfaState::new(Accept::never()));
                let new_idx = self.states.len() - 1;

                // If the `in_states` were a possible starting state at the beginning
                // of the input, maybe make the new state also a starting state.
                if pred.0.at_boundary && !in_states.is_disjoint(&self.init_at_start) {
                    self.init_at_start.push(new_idx);
                    // No need to re-sort, since the new one is the largest index in the whole
                    // Nfa.
                }

                // If the `in_states` are a possible starting state in the middle of the input,
                // maybe make the new state a conditional starting state.
                let mut init_chars = initial_preds.clone();
                init_chars.retain_values(|x| in_states.contains(x));
                if !in_states.is_disjoint(&self.init) {
                    init_chars.insert(Range::full(), 0); // FIXME: why 0 here and not the new state?
                }
                init_chars = init_chars.intersection(&pred.0.chars);
                for &(range, _) in init_chars.ranges_values() {
                    initial_preds.insert(range, new_idx);
                }

                for &(range, ref sources) in in_trans.ranges_values() {
                    for &source in sources {
                        self.add_transition(source, new_idx, range);
                        reversed.add_transition(new_idx, source, range);
                    }
                }
                for (other_pred, source) in reversed.predicates(&in_states) {
                    if let Some(p) = pred.intersect(&other_pred) {
                        self.add_predicate(source, new_idx, p.clone());
                        reversed.add_predicate(new_idx, source, p);
                    }
                }
                for &(range, ref targets) in out_trans.ranges_values() {
                    for &target in targets {
                        self.add_transition(new_idx, target, range);
                        reversed.add_transition(target, new_idx, range);
                    }
                }
                for (other_pred, target) in self.predicates(&out_states) {
                    if let Some(p) = pred.intersect(&other_pred) {
                        self.add_predicate(new_idx, target, p.clone());
                        reversed.add_predicate(target, new_idx, p);
                    }
                }
            }
        }

        self.states.len() > orig_len
    }

    // We've just created a new state for the predicate `pred`, and `states` is the eps-closure of
    // its target state. Under what conditions should the new state accept?
    fn predicate_accept(&self, pred: &Predicate, states: &StateSet) -> Accept {
        pred.filter_accept(&self.accept(states))
    }

    /// Deletes all transitions following an unconditional accept.
    fn optimize_for_shortest_match(&mut self) {
        for st_idx in 0..self.states.len() {
            let eps_closure = self.eps_closure_single(st_idx);
            if self.accept(&eps_closure).is_always() {
                self.states[st_idx].transitions.predicates.clear();
                self.states[st_idx].transitions.consuming = RangeMultiMap::new();
            }
        }

        for st in &mut self.states {
            if st.accept.is_always() {
                st.transitions.eps.clear();
            }
        }

        self.trim_unreachable();
    }

    fn trim_unreachable(&mut self) {
        let reachable = self.reachable_states();

        let mut old_states = Vec::new();
        mem::swap(&mut self.states, &mut old_states);

        let (new_to_old, new_states): (Vec<_>, Vec<NfaState>) = old_states.into_iter()
            .enumerate()
            .filter(|&(i, _)| reachable.contains(&i))
            .unzip();
        self.states = new_states;
        let old_to_new: HashMap<usize, usize> = new_to_old.iter()
            .enumerate()
            .map(|(x, y)| (*y, x))
            .collect();
        let map_state = |x: usize| -> Option<usize> { old_to_new.get(&x).cloned() };
        let map_state_set = |x: &StateSet| -> StateSet {
            x.iter().cloned().filter_map(&map_state).collect()
        };

        for i in 0..self.states.len() {
            self.states[i].transitions.filter_map_targets(&map_state);
        }
        self.init = self.init.iter().filter_map(|x| map_state(*x)).collect();
        self.init_at_start = self.init_at_start.iter().filter_map(|x| map_state(*x)).collect();
        self.init_after_char.map_values(&map_state_set);
    }

    /// Returns a copy with all transitions reversed.
    ///
    /// Its states will have the same indices as those of the original.
    fn reversed(&self) -> Nfa {
        let mut ret = Nfa::with_capacity(self.states.len());

        for st in self.states.iter() {
            ret.states.push(NfaState::new(st.accept.clone()));
        }

        for (idx, st) in self.states.iter().enumerate() {
            for &(ref range, target) in st.transitions.consuming.ranges_values() {
                ret.add_transition(target, idx, *range);
            }
            for &target in st.transitions.eps.iter() {
                ret.add_eps(target, idx);
            }
            for &(ref pred, target) in st.transitions.predicates.iter() {
                ret.add_predicate(target, idx, pred.clone());
            }
        }

        ret
    }

    /// Returns the set of all states that can be reached from some initial state.
    fn reachable_from(&self, states: &StateSet) -> StateSet {
        let mut active: HashSet<usize> = states.iter().cloned().collect();
        let mut next_active: HashSet<usize> = HashSet::new();
        let mut ret = active.clone();

        while !active.is_empty() {
            for &s in &active {
                for &t in &self.states[s].transitions.eps {
                    if !ret.contains(&t) {
                        ret.insert(t);
                        next_active.insert(t);
                    }
                }
                for &(_, t) in self.states[s].transitions.consuming.ranges_values() {
                    if !ret.contains(&t) {
                        ret.insert(t);
                        next_active.insert(t);
                    }
                }

                for &(_, t) in self.states[s].transitions.predicates.iter() {
                    if !ret.contains(&t) {
                        ret.insert(t);
                        next_active.insert(t);
                    }
                }
            }
            mem::swap(&mut active, &mut next_active);
            next_active.clear();
        }

        let mut ret: Vec<_> = ret.into_iter().collect();
        ret.sort();
        ret
    }

    /// Returns the set of all states that can be reached from an initial state and that can reach
    /// some accepting state.
    pub fn reachable_states(&self) -> StateSet {
        let mut init_states = self.init.clone();
        init_states.extend(&self.init_at_start);
        for &(_, ref s) in self.init_after_char.ranges_values() {
            init_states.extend(s);
        }
        init_states.sort();

        let mut final_states = StateSet::new();
        for (idx, s) in self.states.iter().enumerate() {
            if !s.accept.is_never() {
                final_states.push(idx);
            }
        }

        let mut forward = self.reachable_from(&init_states);
        let backward = self.reversed().reachable_from(&final_states);
        forward.intersect_with(&backward);
        forward
    }

    /// Converts this char-based automaton into a byte-based one that can be used to find the
    /// shortest strings matching this language.
    pub fn convert_to_byte_automaton(&mut self, max_states: usize)
    -> Result<(), error::Error> {
        // Technically, we only need to optimize_for_shortest_match once at the end. But
        // doing it more times is cheap, and it can help prevent remove_predicates and byte_me
        // from unnecessarily adding many states.
        self.optimize_for_shortest_match();
        self.remove_predicates();
        self.optimize_for_shortest_match();
        try!(self.byte_me(max_states));
        try!(self.byte_accept(max_states));

        Ok(())
    }

    /// Creates a deterministic automaton representing the same language.
    ///
    /// This assumes that we have no transition predicates -- if there are any, you must call
    /// `remove_predicates` before calling `determinize`.
    pub fn determinize(&self, max_states: usize) -> Result<Dfa, error::Error> {
        if self.states.is_empty() {
            return Ok(Dfa::new());
        }

        let mut ret = Dfa::new();
        let mut state_map = HashMap::<StateSet, usize>::new();
        let mut active_states = Vec::<StateSet>::new();

        let add_state = |s: StateSet, dfa: &mut Dfa, active: &mut Vec<_>, map: &mut HashMap<_,_>|
        -> Result<usize, error::Error> {
            if map.contains_key(&s) {
                Ok(*map.get(&s).unwrap())
            } else if dfa.num_states() >= max_states {
                Err(error::Error::TooManyStates)
            } else {
                dfa.add_state(self.dfa_accept(&s));
                active.push(s.clone());
                map.insert(s, dfa.num_states() - 1);
                Ok(dfa.num_states() - 1)
            }
        };

        let init_other = self.eps_closure(&self.init);
        if !init_other.is_empty() {
            let idx =
                try!(add_state(init_other.clone(), &mut ret, &mut active_states, &mut state_map));
            ret.init_otherwise = Some(idx);
        }

        let init_at_start = self.eps_closure(&self.init_at_start);
        if !init_at_start.is_empty() {
            let idx =
                try!(add_state(init_at_start, &mut ret, &mut active_states, &mut state_map));
            ret.init_at_start = Some(idx);
        }

        let mut ret_init_after = Vec::new();
        for &(range, ref states) in self.init_after_char.ranges_values() {
            let mut init = self.eps_closure(states);
            init.union_with(&init_other);
            if !init.is_empty() {
                let idx = try!(add_state(init, &mut ret, &mut active_states, &mut state_map));
                ret_init_after.push((range, idx));
            }
        }
        ret.init_after_char = ret_init_after.into_iter().collect();

        while active_states.len() > 0 {
            let state = active_states.pop().unwrap();
            let state_idx = *state_map.get(&state).unwrap();
            let trans = self.transitions(&state);

            let mut dfa_trans = Vec::new();
            for &(range, ref target) in trans.ranges_values() {
                let target_idx =
                    try!(add_state(target.clone(), &mut ret, &mut active_states, &mut state_map));

                assert!(range.start < 256 && range.end < 256);
                let range = Range::new(range.start as u8, range.end as u8);
                dfa_trans.push((range, target_idx));
            }
            ret.set_transitions(state_idx, dfa_trans.into_iter().collect());
        }
        Ok(ret)
    }

    fn eps_closure(&self, states: &StateSet) -> StateSet {
        let mut ret: HashSet<usize> = states.iter().cloned().collect();
        let mut new_states = ret.clone();
        let mut next_states = HashSet::new();

        while !new_states.is_empty() {
            for &s in &new_states {
                for &t in &self.states[s].transitions.eps {
                    if !ret.contains(&t) {
                        next_states.insert(t);
                        ret.insert(t);
                    }
                }
            }

            mem::swap(&mut next_states, &mut new_states);
            next_states.clear();
        }

        let mut ret: Vec<_> = ret.into_iter().collect();
        ret.sort();
        ret
    }

    fn eps_closure_single(&self, state: usize) -> StateSet {
        let mut set = StateSet::new();
        set.push(state);
        self.eps_closure(&set)
    }

    fn accept(&self, states: &StateSet) -> Accept {
        states.iter().fold(Accept::never(), |a, b| a.union(&self.states[*b].accept))
    }

    fn dfa_accept(&self, states: &StateSet) -> DfaAccept {
        let ret = states.iter()
            .fold(
                DfaAccept::never(),
                |a, b| a.union_shortest(&self.states[*b].dfa_accept));
        ret
    }

    /// Finds all the transitions out of the given set of states.
    ///
    /// Only transitions that consume output are returned. In particular, you
    /// probably want `states` to already be eps-closed.
    pub fn transitions<'a, I>(&self, states: I) -> RangeMap<u32, StateSet>
    where I: IntoIterator<Item=&'a usize> {
        let trans = states.into_iter()
            .flat_map(|s| self.states[*s].transitions.consuming.ranges_values().cloned())
            .collect();
        let trans = RangeMultiMap::from_vec(trans).group();

        trans.ranges_values().map(|x| (x.0, self.eps_closure(&x.1))).collect()
    }

    /// Finds all predicates transitioning out of the given set of states.
    fn predicates(&self, states: &StateSet) -> Vec<(Predicate, usize)> {
        states.iter()
              .flat_map(|s| self.states[*s].transitions.predicates.iter().cloned())
              .collect()
    }
}

#[cfg(test)]
mod tests {
    use nfa::Nfa;
    use range_map::{Range, RangeMap, RangeSet};
    use transition::{Accept, PredicatePart, StateSet};

    #[test]
    fn test_predicate_beginning() {
        let mut nfa = Nfa::from_regex("^a").unwrap();
        // There should be a beginning predicate between states 0 and 4, an eps transition from 1
        // to 2, and 'a' transitions from 2 to 3 and 4 to 3.
        assert_eq!(nfa.states.len(), 4);
        nfa.remove_predicates();
        assert_eq!(nfa.states.len(), 5);

        let mut target = Nfa::with_capacity(6);
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::always());
        target.add_state(Accept::never());
        target.add_transition(2, 3, Range::single('a' as u32));
        target.add_transition(4, 3, Range::single('a' as u32));
        target.add_eps(1, 2);
        target.init.push(0);
        target.init_at_start.push(0);
        target.init_at_start.push(4);
        assert_eq!(nfa, target)
    }

    fn word_chars() -> RangeSet<u32> { PredicatePart::word_char().chars }
    fn not_word_chars() -> RangeSet<u32> { PredicatePart::not_word_char().chars }

    fn word_char_map(word_state: usize, non_word_state: usize) -> RangeMap<u32, StateSet> {
        let mut ret = Vec::new();
        let mut word_states = StateSet::new();
        word_states.push(word_state);
        let mut non_word_states = StateSet::new();
        non_word_states.push(non_word_state);

        let chs = word_chars();
        for range in chs.ranges() {
            ret.push((range, word_states.clone()));
        }
        let chs = not_word_chars();
        for range in chs.ranges() {
            ret.push((range, non_word_states.clone()));
        }
        ret.sort();
        ret.into_iter().collect()
    }

    #[test]
    fn test_word_boundary_beginning() {
        let mut nfa = Nfa::from_regex(r"\ba").unwrap();
        // There should be a word boundary predicate between states 0 and 5, an eps transition from
        // 1 to 2, and 'a' transitions from 2 to 3 and 5 to 3. There will also be a useless state
        // 4.
        assert_eq!(nfa.states.len(), 4);
        nfa.remove_predicates();
        assert_eq!(nfa.states.len(), 6);

        let mut target = Nfa::with_capacity(6);
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::always());
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_transition(2, 3, Range::single('a' as u32));
        target.add_transition(5, 3, Range::single('a' as u32));
        target.add_eps(1, 2);
        target.init.push(0);
        target.init_at_start.push(0);
        target.init_at_start.push(5);
        target.init_after_char = word_char_map(4, 5);
        assert_eq!(nfa, target)
    }

    #[test]
    fn test_word_boundary_end() {
        let mut nfa = Nfa::from_regex(r"a\b").unwrap();
        assert_eq!(nfa.states.len(), 4);
        nfa.remove_predicates();
        assert_eq!(nfa.states.len(), 6);

        let mut target = Nfa::with_capacity(6);
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::always());
        target.add_state(Accept { at_eoi: true, at_char: not_word_chars() });
        target.add_state(Accept { at_eoi: false, at_char: word_chars() });
        target.add_transition(0, 1, Range::single('a' as u32));
        target.add_transition(0, 4, Range::single('a' as u32));
        target.add_eps(1, 2);
        target.init.push(0);
        target.init_at_start.push(0);
        assert_eq!(nfa, target)
    }

    #[test]
    fn test_max_size() {
        let nfa = Nfa::from_regex(r"a[0-9]b").unwrap();
        assert!(nfa.clone().byte_me(10).is_ok());
        assert!(nfa.clone().byte_me(5).is_err());

        let mut nfa = Nfa::from_regex(r"\ba\b").unwrap();
        nfa.remove_predicates();
        assert!(nfa.clone().byte_me(10).is_ok());
        assert!(nfa.clone().byte_me(5).is_err());
        assert!(nfa.clone().byte_accept(4000).is_ok());
        assert!(nfa.clone().byte_accept(500).is_err());

        let mut nfa = Nfa::from_regex(r"blah.*\ba\b.*blah").unwrap();
        nfa.remove_predicates();
        assert!(nfa.clone().byte_me(10000).is_ok());
        assert!(nfa.clone().byte_me(8000).is_err());
    }
}

