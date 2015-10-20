// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bit_set::BitSet;
use builder::NfaBuilder;
use char_map::{CharMap, CharMultiMap, CharRange};
use dfa::Dfa;
use error;
use regex_syntax;
use std;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::mem;
use std::ops::Deref;
use std::result::Result;
use transition::{Accept, NfaTransitions, Predicate};


#[derive(PartialEq, Debug)]
pub struct NfaState {
    pub transitions: NfaTransitions,
    pub accept: Accept,
}

impl NfaState {
    pub fn new(accept: Accept) -> NfaState {
        NfaState {
            transitions: NfaTransitions::new(),
            accept: accept,
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
#[derive(PartialEq)]
pub struct Nfa {
    states: Vec<NfaState>,

    /// Sometimes we want to only match at the beginning of the text; we can represent this
    /// using `init_at_start`, which is a set of states that are all valid as starting states,
    /// but only if we start matching at the beginning of the input.
    ///
    /// Note that `transition::Predicate` provides another, higher-level, way to represent the same
    /// information. Before turning this `Nfa` into a `Dfa`, we will lower the
    /// `transition::Predicate` representation into this one.
    init_at_start: BitSet,

    /// Sometimes we want to begin in a particular state only if the char before the substring we
    /// are trying to match is in a particular class. (For example, this is used to implement word
    /// boundaries.) This is represented by `init_after_char`: if the char before the current
    /// position (call it `ch`) is in `init_after_char` then we start in all the states in
    /// `init_after_char.get(ch)`.
    init_after_char: CharMap<BitSet>,
}

impl Debug for Nfa {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        try!(f.write_fmt(format_args!("Nfa ({} states):\n", self.states.len())));
        if !self.init_at_start.is_empty() {
            try!(f.write_fmt(format_args!("Initial_at_start: {:?}\n", self.init_at_start)));
        }

        if !self.init_after_char.is_empty() {
            try!(f.write_fmt(format_args!("Initial_after_char: {:?}\n", self.init_after_char)));
        }

        for (st_idx, st) in self.states.iter().enumerate() {
            try!(f.write_fmt(format_args!("\tState {} (accept: {:?}):\n", st_idx, st.accept)));

            if !st.transitions.consuming.is_empty() {
                try!(f.write_str("\t\tTransitions:\n"));
                for &(range, target) in st.transitions.consuming.iter() {
                    try!(f.write_fmt(format_args!("\t\t\t{} -- {} => {}\n",
                                                  range.start, range.end, target)));
                }
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

    pub fn with_capacity(n: usize) -> Nfa {
        Nfa {
            states: Vec::with_capacity(n),
            init_at_start: BitSet::with_capacity(n),
            init_after_char: CharMap::new(),
        }
    }

    pub fn add_transition(&mut self, from: usize, to: usize, r: CharRange) {
        self.states[from].transitions.consuming.push(r, &to);
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

    /// Returns the list of all input-consuming transitions from the given state.
    ///
    /// TODO: this would be a prime candidate for using abstract return types, if that ever lands.
    pub fn transitions_from(&self, from: usize) -> &Vec<(CharRange, usize)> {
        self.states[from].transitions.consuming.deref()
    }

    /// Modifies this automaton to remove all transition predicates.
    ///
    /// Note that this clobbers `init_at_start` and `init_after_char`, so you probably don't want
    /// to call this if those are already set. In particular, calling `remove_predicates()` twice
    /// on the same `Nfa` is probably a bad idea.
    pub fn remove_predicates(&mut self, max_states: usize) -> Result<(), error::Error> {
        self.init_at_start.clear();
        self.init_at_start.insert(0);

        // Sometimes an InClasses predicate is attached to the initial state. This map keeps track
        // of such predicates: if `initial_preds` contains the map 'a' -> 3, for example, then if
        // we just saw the character 'a' we should start in the state 3.
        let mut initial_preds = CharMultiMap::<usize>::new();

        let mut changed = self.remove_predicates_once(&mut initial_preds);
        while changed {
            if self.states.len() > max_states {
                return Err(error::Error::TooManyStates);
            }
            changed = self.remove_predicates_once(&mut initial_preds);
        }
        self.init_after_char = initial_preds.group();
        Ok(())
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
    fn remove_predicates_once(&mut self, initial_preds: &mut CharMultiMap<usize>) -> bool {
        let orig_len = self.states.len();
        let mut reversed = self.reversed();

        for idx in 0..orig_len {
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
                    self.init_at_start.insert(new_idx);
                }

                // If the `in_states` are a possible starting state in the middle of the input,
                // maybe make the new state a conditional starting state.
                let mut init_chars = initial_preds.filter_values(|x| in_states.contains(&x));
                if in_states.contains(&0) {
                    init_chars.push(CharRange::full(), &0);
                }
                init_chars = init_chars.intersect(&pred.0.chars);
                for (range, _) in init_chars {
                    initial_preds.push(range, &new_idx);
                }

                for (range, ref sources) in in_trans.into_iter() {
                    for source in sources {
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
                for (range, ref targets) in out_trans.into_iter() {
                    for target in targets {
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
    fn predicate_accept(&self, pred: &Predicate, states: &BitSet) -> Accept {
        pred.filter_accept(&self.accept(states))
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
            for &(ref range, target) in st.transitions.consuming.iter() {
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

    /// Returns the set of all states that can be reached from some initial state.  Predicates must
    /// be removed before calling this.
    fn reachable_from(&self, states: &BitSet) -> BitSet {
        let mut active = states.clone();
        let mut next_active = BitSet::with_capacity(self.states.len());
        let mut ret = active.clone();

        while !active.is_empty() {
            for s in &active {
                for &t in &self.states[s].transitions.eps {
                    if !ret.contains(&t) {
                        ret.insert(t);
                        next_active.insert(t);
                    }
                }
                for &(_, t) in self.states[s].transitions.consuming.iter() {
                    if !ret.contains(&t) {
                        ret.insert(t);
                        next_active.insert(t);
                    }
                }
            }
            mem::swap(&mut active, &mut next_active);
            next_active.clear();
        }

        ret
    }

    /// Returns the set of all states that can be reached from an initial state and that can reach
    /// some accepting state.
    pub fn reachable_states(&self) -> BitSet {
        let mut init_states = BitSet::with_capacity(self.states.len());
        init_states.insert(0);
        init_states.union_with(&self.init_at_start);
        for &(_, ref s) in &self.init_after_char {
            init_states.union_with(s);
        }

        let mut final_states = BitSet::with_capacity(self.states.len());
        for (idx, s) in self.states.iter().enumerate() {
            if !s.accept.is_never() {
                final_states.insert(idx);
            }
        }

        let mut forward = self.reachable_from(&init_states);
        let backward = self.reversed().reachable_from(&final_states);
        forward.intersect_with(&backward);
        forward
    }

    /// Creates a deterministic automaton representing the same language.
    ///
    /// This assumes that we have no transition predicates -- if there are any, you must call
    /// `remove_predicates` before calling `determinize`.
    pub fn determinize(&self, max_states: usize) -> Result<Dfa, error::Error> {
        if self.states.is_empty() {
            // FIXME: figure out what to do for empty automata
            return Err(error::Error::TooManyStates);
        }

        let mut ret = Dfa::new();
        let mut state_map = HashMap::<BitSet, usize>::new();
        let mut active_states = Vec::<BitSet>::new();
        let reachable = self.reachable_states();

        let add_state = |s: BitSet, dfa: &mut Dfa, active: &mut Vec<_>, map: &mut HashMap<_,_>|
        -> Result<usize, error::Error> {
            if map.contains_key(&s) {
                Ok(*map.get(&s).unwrap())
            } else if dfa.num_states() >= max_states {
                Err(error::Error::TooManyStates)
            } else {
                dfa.add_state(self.accept(&s));
                active.push(s.clone());
                map.insert(s, dfa.num_states() - 1);
                Ok(dfa.num_states() - 1)
            }
        };

        let mut init_other = self.eps_closure_single(0);
        init_other.intersect_with(&reachable);
        if !init_other.is_empty() {
            let idx =
                try!(add_state(init_other.clone(), &mut ret, &mut active_states, &mut state_map));
            ret.init_otherwise = Some(idx);
        }

        let mut init_at_start = self.eps_closure(&self.init_at_start);
        init_at_start.intersect_with(&reachable);
        if !init_at_start.is_empty() {
            let idx =
                try!(add_state(init_at_start, &mut ret, &mut active_states, &mut state_map));
            ret.init_at_start = Some(idx);
        }

        for &(range, ref states) in &self.init_after_char {
            let mut init = self.eps_closure(states);
            init.union_with(&init_other);
            init.intersect_with(&reachable);
            if !init.is_empty() {
                let idx = try!(add_state(init, &mut ret, &mut active_states, &mut state_map));
                ret.init_after_char.push(range, &idx);
            }
        }

        while active_states.len() > 0 {
            let state = active_states.pop().unwrap();
            let state_idx = *state_map.get(&state).unwrap();
            let trans = self.transitions(&state);
            for (range, target) in trans.into_iter() {
                let target_idx =
                    try!(add_state(target.clone(), &mut ret, &mut active_states, &mut state_map));
                ret.add_transition(state_idx, target_idx, range);
            }
        }

        ret.sort_transitions();
        Ok(ret)
    }

    fn eps_closure(&self, states: &BitSet) -> BitSet {
        let mut ret = states.clone();
        let mut new_states = states.clone();
        let mut next_states = BitSet::with_capacity(self.states.len());

        while !new_states.is_empty() {
            for s in &new_states {
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

        ret
    }

    fn eps_closure_single(&self, state: usize) -> BitSet {
        let mut set = BitSet::with_capacity(self.states.len());
        set.insert(state);
        self.eps_closure(&set)
    }

    fn accept(&self, states: &BitSet) -> Accept {
        states.iter().fold(Accept::never(), |a, b| a.union(&self.states[b].accept))
    }

    /// Finds all the transitions out of the given set of states.
    ///
    /// Only transitions that consume output are returned. In particular, you
    /// probably want `states` to already be eps-closed.
    pub fn transitions(&self, states: &BitSet) -> CharMap<BitSet> {
        let trans = states.iter()
                          .flat_map(|s| self.states[s].transitions.consuming.iter().cloned())
                          .collect();
        let trans = CharMultiMap::from_vec(trans).group();

        CharMap::from_vec(trans.into_iter().map(|x| (x.0, self.eps_closure(&x.1))).collect())
    }

    /// Finds all predicates transitioning out of the given set of states.
    fn predicates(&self, states: &BitSet) -> Vec<(Predicate, usize)> {
        states.iter()
              .flat_map(|s| self.states[s].transitions.predicates.iter().cloned())
              .collect()
    }
}

#[cfg(test)]
mod tests {
    use bit_set::BitSet;
    use nfa::Nfa;
    use char_map::{CharMap, CharRange, CharSet};
    use std::usize;
    use transition::{Accept, PredicatePart};

    #[test]
    fn test_predicate_beginning() {
        let mut nfa = Nfa::from_regex("^a").unwrap();
        // There should be a beginning predicate between states 0 and 4, an eps transition from 1
        // to 2, and 'a' transitions from 2 to 3 and 4 to 3.
        assert_eq!(nfa.states.len(), 4);
        nfa.remove_predicates(usize::MAX);
        assert_eq!(nfa.states.len(), 5);

        let mut target = Nfa::with_capacity(6);
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::always());
        target.add_state(Accept::never());
        target.add_transition(2, 3, CharRange::single('a' as u32));
        target.add_transition(4, 3, CharRange::single('a' as u32));
        target.add_eps(1, 2);
        target.init_at_start.insert(0);
        target.init_at_start.insert(4);
        assert_eq!(nfa, target)
    }

    fn word_chars() -> CharSet { PredicatePart::word_char().chars }
    fn not_word_chars() -> CharSet { PredicatePart::not_word_char().chars }

    fn word_char_map(word_state: usize, non_word_state: usize) -> CharMap<BitSet> {
        let mut ret = CharMap::new();
        let mut word_states = BitSet::new();
        word_states.insert(word_state);
        let mut non_word_states = BitSet::new();
        non_word_states.insert(non_word_state);

        let chs = word_chars();
        for &range in &chs {
            ret.push(range, &word_states);
        }
        let chs = not_word_chars();
        for &range in &chs {
            ret.push(range, &non_word_states);
        }
        ret.sort();
        ret
    }

    #[test]
    fn test_word_boundary_beginning() {
        let mut nfa = Nfa::from_regex(r"\ba").unwrap();
        // There should be a word boundary predicate between states 0 and 5, an eps transition from
        // 1 to 2, and 'a' transitions from 2 to 3 and 5 to 3. There will also be a useless state
        // 4.
        assert_eq!(nfa.states.len(), 4);
        nfa.remove_predicates(usize::MAX);
        assert_eq!(nfa.states.len(), 6);

        let mut target = Nfa::with_capacity(6);
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::always());
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_transition(2, 3, CharRange::single('a' as u32));
        target.add_transition(5, 3, CharRange::single('a' as u32));
        target.add_eps(1, 2);
        target.init_at_start.insert(0);
        target.init_at_start.insert(5);
        target.init_after_char = word_char_map(4, 5);
        assert_eq!(nfa, target)
    }

    #[test]
    fn test_word_boundary_end() {
        let mut nfa = Nfa::from_regex(r"a\b").unwrap();
        assert_eq!(nfa.states.len(), 4);
        nfa.remove_predicates(usize::MAX);
        assert_eq!(nfa.states.len(), 6);

        let mut target = Nfa::with_capacity(6);
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::never());
        target.add_state(Accept::always());
        target.add_state(Accept { at_eoi: true, at_char: not_word_chars() });
        target.add_state(Accept { at_eoi: false, at_char: word_chars() });
        target.add_transition(0, 1, CharRange::single('a' as u32));
        target.add_transition(0, 4, CharRange::single('a' as u32));
        target.add_eps(1, 2);
        target.init_at_start.insert(0);
        assert_eq!(nfa, target)
    }
}

