// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use automaton::Nfa;
use transition::SymbRange;
use regex_syntax::{CharClass, ClassRange, Expr, Repeater};
use std;
use std::ops::Deref;

// Utility functions for constructing Vec<SymbRange>

fn symb_ranges_from_char_class(c: &CharClass) -> Vec<SymbRange> {
    let mut ret = Vec::with_capacity(c.len());
    for range in c {
        ret.push(SymbRange::new(range.start as u32, range.end as u32))
    }
    ret
}

fn symb_ranges_from_any_char() -> Vec<SymbRange> {
    let mut ret = Vec::with_capacity(1);
    ret.push(SymbRange::new(0, std::u32::MAX));
    ret
}

fn symb_ranges_from_any_char_except(chars: &str) -> Vec<SymbRange> {
    let mut ret = Vec::with_capacity(chars.len());
    let mut next_allowed = 0u32;
    for c in chars.chars() {
        let n = c as u32;
        if n > next_allowed {
            ret.push(SymbRange::new(next_allowed, n - 1));
        }
        next_allowed = n + 1;
    }
    ret
}

// When constructing an Nfa from a regex, the states have special structure: if the transition
// accepts any input, then it always moves to the next state. Therefore, there is no need to store
// the target state of a transition.
// Also, the last state is always the accepting state, so there is no need to store whether
// a state is accepting.
#[derive(Debug, PartialEq)]
struct BuilderState {
    ranges: Vec<SymbRange>,
    eps: Vec<usize>,
}

impl BuilderState {
    fn new() -> BuilderState {
        BuilderState {
            ranges: Vec::new(),
            eps: Vec::new(),
        }
    }

    fn from_ranges(rs: Vec<SymbRange>) -> BuilderState {
        BuilderState {
            ranges: rs,
            eps: Vec::new(),
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
            ret.add_state(ret_len == self.len());

            for ch in &s.ranges {
                ret.add_transition(ret_len-1, ret_len, *ch);
            }
            for eps in &s.eps {
                ret.add_eps(ret_len-1, *eps);
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
    fn add_single_transition(&mut self, ranges: Vec<SymbRange>) {
        self.states.push(BuilderState::from_ranges(ranges));
        self.states.push(BuilderState::new());
     }

    // Adds a sequence of states, and a sequence of transitions between them.
    pub fn add_literal<C, I>(&mut self, chars: I, case_insensitive: bool)
        where C: Deref<Target=char>,
              I: Iterator<Item=C>
    {
        for ch in chars {
            let ranges = if case_insensitive {
                // NOTE: it isn't really necessary to create a new CharClass here, but
                // regex_syntax doesn't expose case_fold (or new) on ClassRange.
                let cc = CharClass::new(vec![ClassRange { start: *ch, end: *ch }]);
                symb_ranges_from_char_class(&cc.case_fold())
            } else {
                vec![SymbRange::single(*ch as u32)]
            };
            self.states.push(BuilderState::from_ranges(ranges));
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
        let init_idx = self.len();
        self.add_expr(expr);
        let final_idx = self.len() - 1;

        match rep {
            Repeater::ZeroOrOne => {
                self.add_eps(init_idx, final_idx);
            },
            Repeater::ZeroOrMore => {
                self.add_eps(init_idx, final_idx);
                self.add_eps(final_idx, init_idx);
            },
            Repeater::OneOrMore => {
                self.add_eps(final_idx, init_idx);
            },
            Repeater::Range{..} => {
                panic!("range not supported yet");
            }
        }
    }

    fn add_expr(&mut self, expr: &Expr) {
        use regex_syntax::Expr::*;

        match expr {
            &Class(ref c) => self.add_single_transition(symb_ranges_from_char_class(c)),
            &AnyChar => self.add_single_transition(symb_ranges_from_any_char()),
            &AnyCharNoNL => self.add_single_transition(symb_ranges_from_any_char_except("\n\r")),
            &Concat(ref es) => self.add_concat_exprs(es),
            &Alternate(ref es) => self.add_alternate_exprs(es),
            &Literal { ref chars, casei } => self.add_literal(chars.iter(), casei),

            // We don't support capture groups, so there is no need to keep track of
            // the group name or number.
            &Group { ref e, .. } => self.add_expr(e),

            // We don't support greedy vs. lazy matching, because I don't know
            // if it can be expressed in a DFA.
            &Repeat { ref e, r, .. } => self.add_repeat(e, r),
            _ => { panic!("unsupported expr: {:?}", expr) }
        }
    }
}

#[cfg(test)]
mod tests {
    use builder::{NfaBuilder, BuilderState};
    use transition::SymbRange;
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
        target.states[0].ranges.push(SymbRange::new('a' as u32, 'z' as u32));
        target.add_eps(1, 2);
        target.states[2].ranges.push(SymbRange::new('A' as u32, 'Z' as u32));

        assert_eq!(builder, target);
    }

    #[test]
    fn test_literal() {
        let builder = parse("aZ").unwrap();
        let mut target = make_builder(3);
        target.states[0].ranges.push(SymbRange::single('a' as u32));
        target.states[1].ranges.push(SymbRange::single('Z' as u32));

        assert_eq!(builder, target);
    }

    #[test]
    fn test_repeat_zero_or_more() {
        let builder = parse("a*z").unwrap();
        let mut target = make_builder(4);
        target.states[0].ranges.push(SymbRange::single('a' as u32));
        target.states[2].ranges.push(SymbRange::single('z' as u32));
        target.add_eps(0, 1);
        target.add_eps(1, 0);
        target.add_eps(1, 2);

        assert_eq!(builder, target);
    }

    #[test]
    fn test_repeat_one_or_more() {
        let builder = parse("a+z").unwrap();
        let mut target = make_builder(4);
        target.states[0].ranges.push(SymbRange::single('a' as u32));
        target.states[2].ranges.push(SymbRange::single('z' as u32));
        target.add_eps(1, 0);
        target.add_eps(1, 2);

        assert_eq!(builder, target);
    }

    #[test]
    fn test_repeat_zero_or_one() {
        let builder = parse("a?z").unwrap();
        let mut target = make_builder(4);
        target.states[0].ranges.push(SymbRange::single('a' as u32));
        target.states[2].ranges.push(SymbRange::single('z' as u32));
        target.add_eps(0, 1);
        target.add_eps(1, 2);

        assert_eq!(builder, target);
    }

    #[test]
    fn test_alternate() {
        let builder = parse("a|z").unwrap();
        let mut target = make_builder(6);
        target.states[1].ranges.push(SymbRange::single('a' as u32));
        target.states[3].ranges.push(SymbRange::single('z' as u32));
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
        target.states[0].ranges.push(SymbRange::single('A' as u32));
        target.states[0].ranges.push(SymbRange::single('a' as u32));
        target.states[1].ranges.push(SymbRange::single('B' as u32));
        target.states[1].ranges.push(SymbRange::single('b' as u32));

        assert_eq!(builder, target);
    }
}

