// Copyright 2015-2016 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use look::Look;
use nfa::{Accept, HasLooks, Nfa};
use range_map::{Range, RangeSet};
use regex_syntax::{CharClass, ClassRange, Expr, Repeater};
use std::ops::Deref;

/// When constructing an Nfa from a regex, the states have special structure: if the transition
/// accepts any input or matches a predicate, then it always moves to the next state. Therefore,
/// there is no need to store the target state of a transition or predicate.  Also, the last state
/// is always the accepting state, so there is no need to store whether a state is accepting.
#[derive(Debug, PartialEq)]
struct State {
    chars: RangeSet<u32>,
    looks: Vec<(Look, Look)>,
    eps: Vec<usize>,
}

impl State {
    fn new() -> State {
        State {
            chars: RangeSet::new(),
            eps: Vec::new(),
            looks: Vec::new(),
        }
    }

    fn from_chars(chars: RangeSet<u32>) -> State {
        State {
            chars: chars,
            eps: Vec::new(),
            looks: Vec::new(),
        }
    }
}

// Converts a `CharClass` into a `RangeSet`
fn class_to_set(cc: &CharClass) -> RangeSet<u32> {
    cc.iter().map(|r| Range::new(r.start as u32, r.end as u32)).collect()
}

/// Builds an `Nfa` from a `regex_syntax::Expr`.
#[derive(Debug, PartialEq)]
pub struct NfaBuilder {
    states: Vec<State>,
}

impl NfaBuilder {
    /// Returns the number of states.
    pub fn len(&self) -> usize {
        self.states.len()
    }

    /// Converts this `NfaBuilder` into an `Nfa`.
    pub fn to_automaton(&self) -> Nfa<u32, HasLooks> {
        let mut ret = Nfa::with_capacity(self.len());
        let mut ret_len: usize = 0;
        for s in &self.states {
            ret_len += 1;
            ret.add_state(if ret_len == self.len() { Accept::Always } else { Accept::Never });

            for range in s.chars.ranges() {
                ret.add_transition(ret_len - 1, ret_len, range);
            }
            for eps in &s.eps {
                ret.add_look(ret_len - 1, *eps, Look::Full, Look::Full);
            }
            for look in &s.looks {
                ret.add_look(ret_len - 1, ret_len, look.0, look.1);
            }
        }

        ret
    }

    /// Creates an `NfaBuilder` from an `Expr`.
    pub fn from_expr(expr: &Expr) -> NfaBuilder {
        let mut ret = NfaBuilder { states: Vec::new() };
        ret.add_expr(expr);
        ret
    }

    /// Adds an eps transition between the given states.
    fn add_eps(&mut self, from: usize, to: usize) {
        self.states[from].eps.push(to);
    }

    /// Appends two states, with a given transition between them.
    fn add_single_transition(&mut self, chars: RangeSet<u32>) {
        self.states.push(State::from_chars(chars));
        self.states.push(State::new());
     }

    /// Appends a sequence of states that recognizes a literal.
    fn add_literal<C, I>(&mut self, chars: I, case_insensitive: bool)
        where C: Deref<Target=char>,
              I: Iterator<Item=C>
    {
        for ch in chars {
            let ranges = if case_insensitive {
                let cc = CharClass::new(vec![ClassRange { start: *ch, end: *ch }]);
                class_to_set(&cc.case_fold())
            } else {
                RangeSet::single(*ch as u32)
            };
            self.states.push(State::from_chars(ranges));
        }
        self.states.push(State::new());
    }

    /// Appends a sequence of states that recognizes the concatenation of `exprs`.
    fn add_concat_exprs(&mut self, exprs: &Vec<Expr>) {
        if let Some((expr, rest)) = exprs.split_first() {
            self.add_expr(expr);

            for expr in rest {
                let cur_len = self.states.len();
                self.add_eps(cur_len - 1, cur_len);
                self.add_expr(expr);
            }
        }
    }

    /// Appends a sequence of states that recognizes one of the expressions in `alts`.
    fn add_alternate_exprs(&mut self, alts: &Vec<Expr>) {
        // Add the new initial state that feeds into the alternate.
        let init_idx = self.states.len();
        self.states.push(State::new());

        let mut expr_end_indices = Vec::<usize>::new();
        for expr in alts {
            let expr_init_idx = self.states.len();
            self.add_eps(init_idx, expr_init_idx);
            self.add_expr(expr);
            expr_end_indices.push(self.states.len() - 1);
        }

        // Make the final state of each alternative point to our new final state.
        self.states.push(State::new());
        let final_idx = self.states.len() - 1;
        for idx in expr_end_indices {
            self.add_eps(idx, final_idx);
        }
    }

    /// Appends new states, representing multiple copies of `expr`.
    fn add_repeat(&mut self, expr: &Expr, rep: Repeater) {
        match rep {
            Repeater::ZeroOrOne => {
                self.add_repeat_min_max(expr, 0, Some(1));
            },
            Repeater::ZeroOrMore => {
                self.add_repeat_min_max(expr, 0, None);
            },
            Repeater::OneOrMore => {
                self.add_repeat_min_max(expr, 1, None);
            },
            Repeater::Range{ min, max } => {
                self.add_repeat_min_max(expr, min, max);
            }
        }
    }

    /// Appends new states, representing multiple copies of `expr`.
    ///
    /// The new states represent a language that accepts at least `min` and at most `maybe_max`
    /// copies of `expr`. (If `maybe_max` is `None`, there is no upper bound.)
    fn add_repeat_min_max(&mut self, expr: &Expr, min: u32, maybe_max: Option<u32>) {
        if min == 0 && maybe_max == Some(0) {
            // We add a state anyway, in order to maintain the convention that every expr should
            // add at least one state (otherwise keeping track of indices becomes much more
            // tedious).
            self.states.push(State::new());
            return;
        }

        // The starting index of the repetition that we are currently working on.
        let mut cur_init_idx = self.states.len();
        if min > 0 {
            self.add_expr(expr);
            for _ in 1..min {
                cur_init_idx = self.states.len();
                self.add_expr(expr);
                self.add_eps(cur_init_idx - 1, cur_init_idx);
            }
        }

        if let Some(max) = maybe_max {
            let mut init_indices = Vec::<usize>::with_capacity((max - min) as usize);
            for i in 0..(max - min) {
                cur_init_idx = self.states.len();
                self.add_expr(expr);
                init_indices.push(cur_init_idx);

                if i > 0 || min > 0 {
                    self.add_eps(cur_init_idx - 1, cur_init_idx);
                }
            }
            let final_idx = self.states.len() - 1;
            for idx in init_indices {
                self.add_eps(idx, final_idx);
            }
        } else {
            if min == 0 {
                cur_init_idx = self.states.len();
                self.add_expr(expr);
                let final_idx = self.states.len() - 1;
                self.add_eps(cur_init_idx, final_idx);
            }

            let final_idx = self.states.len() - 1;
            self.add_eps(final_idx, cur_init_idx);
        }
    }

    /// Adds two new states, with a look connecting them.
    fn add_look(&mut self, behind: Look, ahead: Look) {
        self.states.push(State::new());
        self.states.last_mut().unwrap().looks.push((behind, ahead));
        self.states.push(State::new());
    }

    /// Adds an extra predicate between the last two states (there must be at least two states).
    fn extra_look(&mut self, behind: Look, ahead: Look) {
        let len = self.states.len();
        self.states[len-2].looks.push((behind, ahead));
    }

    /// Appends a bunch of new states, representing `expr`.
    fn add_expr(&mut self, expr: &Expr) {
        use regex_syntax::Expr::*;

        match expr {
            &Empty => {},
            &Class(ref c) => self.add_single_transition(class_to_set(c)),
            &AnyChar => self.add_single_transition(RangeSet::full()),
            &AnyCharNoNL => {
                let nls = b"\n\r".into_iter().map(|b| *b as u32);
                self.add_single_transition(RangeSet::except(nls))
            },
            &Concat(ref es) => self.add_concat_exprs(es),
            &Alternate(ref es) => self.add_alternate_exprs(es),
            &Literal { ref chars, casei } => self.add_literal(chars.iter(), casei),
            &StartLine => self.add_look(Look::NewLine, Look::Full),
            &StartText => self.add_look(Look::Boundary, Look::Full),
            &EndLine => self.add_look(Look::Full, Look::NewLine),
            &EndText => self.add_look(Look::Full, Look::Boundary),
            &WordBoundary => {
                self.add_look(Look::WordChar, Look::NotWordChar);
                self.extra_look(Look::NotWordChar, Look::WordChar);
            },
            &NotWordBoundary => {
                self.add_look(Look::WordChar, Look::WordChar);
                self.extra_look(Look::NotWordChar, Look::NotWordChar);
            },

            // We don't support capture groups, so there is no need to keep track of
            // the group name or number.
            &Group { ref e, .. } => self.add_expr(e),

            // We don't support greedy vs. lazy matching, because I don't know
            // if it can be expressed in a DFA.
            &Repeat { ref e, r, .. } => self.add_repeat(e, r),
        }
    }
}

    #[cfg(test)]
mod tests {
    use nfa::builder::{NfaBuilder, State};
    use range_map::{Range, RangeSet};
    use regex_syntax;

    fn parse(s: &str) -> regex_syntax::Result<NfaBuilder> {
        let expr = try!(regex_syntax::Expr::parse(s));
        Ok(NfaBuilder::from_expr(&expr))
    }

    fn make_builder(n_states: usize) -> NfaBuilder {
        let mut ret = NfaBuilder { states: Vec::new() };
        for _ in 0..n_states {
            ret.states.push(State::new());
        }
        ret
    }

    fn set(ranges: &[(char, char)]) -> RangeSet<u32> {
        ranges.iter().map(|r| Range::new(r.0 as u32, r.1 as u32)).collect()
    }

    #[test]
    fn test_char_class() {
        let builder = parse("[a-z][A-Z]").unwrap();
        let mut target = make_builder(4);
        target.states[0].chars = set(&[('a', 'z')]);
        target.add_eps(1, 2);
        target.states[2].chars = set(&[('A', 'Z')]);

        assert_eq!(builder, target);
    }

    #[test]
    fn test_literal() {
        let builder = parse("aZ").unwrap();
        let mut target = make_builder(3);
        target.states[0].chars = RangeSet::single('a' as u32);
        target.states[1].chars = RangeSet::single('Z' as u32);

        assert_eq!(builder, target);
    }

    #[test]
    fn test_repeat_zero_or_more() {
        let builder = parse("ab*z").unwrap();
        let builder2 = parse("ab{0,}z").unwrap();
        let mut target = make_builder(6);
        target.states[0].chars = RangeSet::single('a' as u32);
        target.states[2].chars = RangeSet::single('b' as u32);
        target.states[4].chars = RangeSet::single('z' as u32);
        target.add_eps(1, 2);
        target.add_eps(2, 3);
        target.add_eps(3, 2);
        target.add_eps(3, 4);

        assert_eq!(builder, target);
        assert_eq!(builder2, target);
    }

    #[test]
    fn test_repeat_one_or_more() {
        let builder = parse("ab+z").unwrap();
        let builder2 = parse("ab{1,}z").unwrap();
        let mut target = make_builder(6);
        target.states[0].chars = RangeSet::single('a' as u32);
        target.states[2].chars = RangeSet::single('b' as u32);
        target.states[4].chars = RangeSet::single('z' as u32);
        target.add_eps(1, 2);
        target.add_eps(3, 2);
        target.add_eps(3, 4);

        assert_eq!(builder, target);
        assert_eq!(builder2, target);
    }

    #[test]
    fn test_repeat_zero_or_one() {
        let builder = parse("ab?z").unwrap();
        let builder2 = parse("ab{0,1}z").unwrap();
        let mut target = make_builder(6);
        target.states[0].chars = RangeSet::single('a' as u32);
        target.states[2].chars = RangeSet::single('b' as u32);
        target.states[4].chars = RangeSet::single('z' as u32);
        target.add_eps(1, 2);
        target.add_eps(2, 3);
        target.add_eps(3, 4);

        assert_eq!(builder, target);
        assert_eq!(builder2, target);
    }

    #[test]
    fn test_repeat_exact() {
        let builder = parse("ab{3}z").unwrap();
        let mut target = make_builder(10);
        target.states[0].chars = RangeSet::single('a' as u32);
        target.states[2].chars = RangeSet::single('b' as u32);
        target.states[4].chars = RangeSet::single('b' as u32);
        target.states[6].chars = RangeSet::single('b' as u32);
        target.states[8].chars = RangeSet::single('z' as u32);
        target.add_eps(1, 2);
        target.add_eps(3, 4);
        target.add_eps(5, 6);
        target.add_eps(7, 8);

        assert_eq!(builder, target);
    }

    #[test]
    fn test_repeat_between() {
        let builder = parse("a{2,4}z").unwrap();
        let mut target = parse("a{4}z").unwrap();
        target.add_eps(4, 7);
        target.add_eps(6, 7);

        assert_eq!(builder, target);

        let builder = parse("a{0,2}z").unwrap();
        let mut target = parse("a{2}z").unwrap();
        target.add_eps(0, 3);
        target.add_eps(2, 3);

        assert_eq!(builder, target);
    }

    #[test]
    fn test_alternate() {
        let builder = parse("a|z").unwrap();
        let mut target = make_builder(6);
        target.states[1].chars = RangeSet::single('a' as u32);
        target.states[3].chars = RangeSet::single('z' as u32);
        target.add_eps(0, 1);
        target.add_eps(2, 5);
        target.add_eps(0, 3);
        target.add_eps(4, 5);

        assert_eq!(builder, target);
    }

    #[test]
    fn test_case_insensitive() {
        let builder = parse("(?i)ab").unwrap();
        let mut target = make_builder(3);
        target.states[0].chars = set(&[('a', 'a'), ('A', 'A')]);
        target.states[1].chars = set(&[('b', 'b'), ('B', 'B')]);

        assert_eq!(builder, target);
    }
}

