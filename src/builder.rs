// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use char_map::CharSet;
use nfa::Nfa;
use transition::{Accept, Predicate, PredicatePart};
use regex_syntax::{CharClass, ClassRange, Expr, Repeater};
use std::ops::Deref;

// When constructing an Nfa from a regex, the states have special structure: if the transition
// accepts any input or matches a predicate, then it always moves to the next state. Therefore,
// there is no need to store the target state of a transition or predicate.  Also, the last state
// is always the accepting state, so there is no need to store whether a state is accepting.
#[derive(Debug, PartialEq)]
struct BuilderState {
    chars: CharSet,
    eps: Vec<usize>,
    predicates: Vec<Predicate>
}

impl BuilderState {
    fn new() -> BuilderState {
        BuilderState {
            chars: CharSet::new(),
            eps: Vec::new(),
            predicates: Vec::new(),
        }
    }

    fn from_chars(chars: CharSet) -> BuilderState {
        BuilderState {
            chars: chars,
            eps: Vec::new(),
            predicates: Vec::new(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct NfaBuilder {
    states: Vec<BuilderState>,
}

impl NfaBuilder {
    pub fn len(&self) -> usize {
        self.states.len()
    }

    pub fn to_automaton(&self) -> Nfa {
        let mut ret = Nfa::with_capacity(self.len());
        let mut ret_len: usize = 0;
        for s in &self.states {
            ret_len += 1;
            ret.add_state(if ret_len == self.len() { Accept::Always } else { Accept::Never });

            for ch in &s.chars {
                ret.add_transition(ret_len - 1, ret_len, *ch);
            }
            for eps in &s.eps {
                ret.add_eps(ret_len - 1, *eps);
            }
            for p in &s.predicates {
                ret.add_predicate(ret_len - 1, ret_len, p.clone());
            }
        }

        ret
    }

    pub fn from_expr(expr: &Expr) -> NfaBuilder {
        let mut ret = NfaBuilder { states: Vec::new() };
        ret.add_expr(expr);
        ret
    }

    fn add_eps(&mut self, from: usize, to: usize) {
        self.states[from].eps.push(to);
    }

    // Appends two states, with a given transition between them.
    fn add_single_transition(&mut self, chars: CharSet) {
        self.states.push(BuilderState::from_chars(chars));
        self.states.push(BuilderState::new());
     }

    // Adds a sequence of states, and a sequence of transitions between them.
    fn add_literal<C, I>(&mut self, chars: I, case_insensitive: bool)
        where C: Deref<Target=char>,
              I: Iterator<Item=C>
    {
        for ch in chars {
            let ranges = if case_insensitive {
                // NOTE: it isn't really necessary to create a new CharClass here, but
                // regex_syntax doesn't expose case_fold (or new) on ClassRange.
                let cc = CharClass::new(vec![ClassRange { start: *ch, end: *ch }]);
                CharSet::from_char_class(&cc.case_fold())
            } else {
                CharSet::single(*ch as u32)
            };
            self.states.push(BuilderState::from_chars(ranges));
        }
        self.states.push(BuilderState::new());
    }

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

    fn add_alternate_exprs(&mut self, alts: &Vec<Expr>) {
        // Add the new initial state that feeds into the alternate.
        let init_idx = self.states.len();
        self.states.push(BuilderState::new());

        let mut expr_end_indices = Vec::<usize>::new();
        for expr in alts {
            let expr_init_idx = self.states.len();
            self.add_eps(init_idx, expr_init_idx);
            self.add_expr(expr);
            expr_end_indices.push(self.states.len() - 1);
        }

        // Make the final state of each alternative point to our new final state.
        self.states.push(BuilderState::new());
        let final_idx = self.states.len() - 1;
        for idx in expr_end_indices {
            self.add_eps(idx, final_idx);
        }
    }

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

    fn add_repeat_min_max(&mut self, expr: &Expr, min: u32, maybe_max: Option<u32>) {
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

    fn add_predicate(&mut self, part1: PredicatePart, part2: PredicatePart) {
        self.states.push(BuilderState::new());
        self.states.last_mut().unwrap().predicates.push(Predicate(part1, part2));
        self.states.push(BuilderState::new());
    }

    // Adds an extra predicate between the last two states (there must be at least two states).
    fn extra_predicate(&mut self, part1: PredicatePart, part2: PredicatePart) {
        let len = self.states.len();
        self.states[len-2].predicates.push(Predicate(part1, part2));
    }

    fn add_expr(&mut self, expr: &Expr) {
        use regex_syntax::Expr::*;

        match expr {
            &Empty => {},
            &Class(ref c) => self.add_single_transition(CharSet::from_char_class(c)),
            &AnyChar => self.add_single_transition(CharSet::full()),
            &AnyCharNoNL => self.add_single_transition(CharSet::except("\n\r")),
            &Concat(ref es) => self.add_concat_exprs(es),
            &Alternate(ref es) => self.add_alternate_exprs(es),
            &Literal { ref chars, casei } => self.add_literal(chars.iter(), casei),
            &StartLine => {
                self.add_predicate(PredicatePart::single_char('\n').or_at_boundary(),
                                   PredicatePart::full());
            },
            &StartText => {
                self.add_predicate(PredicatePart::at_boundary(), PredicatePart::full());
            }
            &EndLine => {
                self.add_predicate(PredicatePart::full(),
                                   PredicatePart::single_char('\n').or_at_boundary());
            },
            &EndText => {
                self.add_predicate(PredicatePart::full(), PredicatePart::at_boundary());
            }
            &WordBoundary => {
                self.add_predicate(PredicatePart::word_char(), PredicatePart::not_word_char());
                self.extra_predicate(PredicatePart::not_word_char(), PredicatePart::word_char());
            },
            &NotWordBoundary => {
                self.add_predicate(PredicatePart::word_char(), PredicatePart::word_char());
                self.extra_predicate(PredicatePart::not_word_char(), PredicatePart::word_char());
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
    use builder::{NfaBuilder, BuilderState};
    use char_map::CharRange;
    use regex_syntax;

    fn parse(s: &str) -> regex_syntax::Result<NfaBuilder> {
        let expr = try!(regex_syntax::Expr::parse(s));
        Ok(NfaBuilder::from_expr(&expr))
    }

    fn make_builder(n_states: usize) -> NfaBuilder {
        let mut ret = NfaBuilder { states: Vec::new() };
        for _ in 0..n_states {
            ret.states.push(BuilderState::new());
        }
        ret
    }

    #[test]
    fn test_char_class() {
        let builder = parse("[a-z][A-Z]").unwrap();
        let mut target = make_builder(4);
        target.states[0].chars.push(CharRange::new('a' as u32, 'z' as u32));
        target.add_eps(1, 2);
        target.states[2].chars.push(CharRange::new('A' as u32, 'Z' as u32));

        assert_eq!(builder, target);
    }

    #[test]
    fn test_literal() {
        let builder = parse("aZ").unwrap();
        let mut target = make_builder(3);
        target.states[0].chars.push(CharRange::single('a' as u32));
        target.states[1].chars.push(CharRange::single('Z' as u32));

        assert_eq!(builder, target);
    }

    #[test]
    fn test_repeat_zero_or_more() {
        let builder = parse("a*z").unwrap();
        let builder2 = parse("a{0,}z").unwrap();
        let mut target = make_builder(4);
        target.states[0].chars.push(CharRange::single('a' as u32));
        target.states[2].chars.push(CharRange::single('z' as u32));
        target.add_eps(0, 1);
        target.add_eps(1, 0);
        target.add_eps(1, 2);

        assert_eq!(builder, target);
        assert_eq!(builder2, target);
    }

    #[test]
    fn test_repeat_one_or_more() {
        let builder = parse("a+z").unwrap();
        let builder2 = parse("a{1,}z").unwrap();
        let mut target = make_builder(4);
        target.states[0].chars.push(CharRange::single('a' as u32));
        target.states[2].chars.push(CharRange::single('z' as u32));
        target.add_eps(1, 0);
        target.add_eps(1, 2);

        assert_eq!(builder, target);
        assert_eq!(builder2, target);
    }

    #[test]
    fn test_repeat_zero_or_one() {
        let builder = parse("a?z").unwrap();
        let builder2 = parse("a{0,1}z").unwrap();
        let mut target = make_builder(4);
        target.states[0].chars.push(CharRange::single('a' as u32));
        target.states[2].chars.push(CharRange::single('z' as u32));
        target.add_eps(0, 1);
        target.add_eps(1, 2);

        assert_eq!(builder, target);
        assert_eq!(builder2, target);
    }

    #[test]
    fn test_repeat_exact() {
        let builder = parse("a{3}z").unwrap();
        let mut target = make_builder(8);
        target.states[0].chars.push(CharRange::single('a' as u32));
        target.states[2].chars.push(CharRange::single('a' as u32));
        target.states[4].chars.push(CharRange::single('a' as u32));
        target.states[6].chars.push(CharRange::single('z' as u32));
        target.add_eps(1, 2);
        target.add_eps(3, 4);
        target.add_eps(5, 6);

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
        target.states[1].chars.push(CharRange::single('a' as u32));
        target.states[3].chars.push(CharRange::single('z' as u32));
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
        target.states[0].chars.push(CharRange::single('A' as u32));
        target.states[0].chars.push(CharRange::single('a' as u32));
        target.states[1].chars.push(CharRange::single('B' as u32));
        target.states[1].chars.push(CharRange::single('b' as u32));

        assert_eq!(builder, target);
    }
}

