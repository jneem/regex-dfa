use automaton::{Automaton, State};
use transition::{SymbRange, TransList};
use regex_syntax::{CharClass, Expr, Repeater};
use std::ops::Deref;

// The automaton here is non-deterministic, and guaranteed to have exactly
// one accepting state: the last one. In fact, we don't even mark that state
// as accepting, but we implicitly know that it is.
// TODO: test some optimizations:
//  - avoid fixing up indices by using relative instead of absolute offsets
//  - avoid reallocation and copying by using linked lists instead of vectors
pub struct AutomatonBuilder {
    auto: Automaton,
}

impl AutomatonBuilder {
    // Private, because the return value doesn't satisfy the invariants:
    // accept is not the index of a valid state.
    fn with_capacity(n: usize) -> AutomatonBuilder {
        AutomatonBuilder {
            auto: Automaton::with_capacity(n),
        }
    }

    // Adds an increment to all state indices in this automaton.
    fn fix_indices(&mut self, increment: usize) {
        for s in &mut self.auto.states {
            for &mut(_, ref mut target) in &mut s.transitions.ranges {
                *target += increment;
            }
            for target in &mut s.transitions.eps {
                *target += increment;
            }
        }
    }

    pub fn len(&self) -> usize {
        self.auto.states.len()
    }
    
    pub fn to_automaton(mut self) -> Automaton {
        let len = self.len();
        self.auto.states[len-1].accepting = true;
        self.auto
    }

    // Builds an automaton that recognizes a language consisting of a single character.
    pub fn char(c: &CharClass) -> AutomatonBuilder {
        let mut ret = AutomatonBuilder::with_capacity(2);

        ret.auto.states.push(State::new(false));
        ret.auto.states.push(State::new(false));
        ret.auto.states[0].transitions = TransList::from_char_class(c, 1);
        ret
    }

    pub fn literal<C, I>(chars: I) -> AutomatonBuilder
        where C: Deref<Target=char>,
              I: Iterator<Item=C>
    {
        let len = chars.size_hint().0 + 1;
        let mut ret = AutomatonBuilder::with_capacity(len);
        ret.auto.states.push(State::new(false));

        for (i, ch) in chars.enumerate() {
            ret.auto.states.push(State::new(false));
            ret.auto.add_transition(i, i+1, SymbRange::single(*ch as u32));
        }

        ret
    }

    fn append(&mut self, mut other: AutomatonBuilder) {
        let len = self.len();

        other.fix_indices(len);
        self.auto.states.extend(other.auto.states);

        if len > 0 {
            self.auto.add_eps(len-1, len);
        }
    }

    pub fn concat(autos: Vec<AutomatonBuilder>) -> AutomatonBuilder {
        let new_len = autos.iter().map(|a| a.len()).sum::<usize>();
        let mut ret = AutomatonBuilder::with_capacity(new_len);

        for auto in autos {
            ret.append(auto);
        }
        ret
    }

    pub fn alternate(alts: Vec<AutomatonBuilder>) -> AutomatonBuilder {
        // The new length is 2 more than the sum of existing lengths: 1 for the
        // new initial state and 1 for the new final state.
        let new_len = alts.iter().map(|a| a.len()).sum::<usize>() + 2;
        let mut ret = AutomatonBuilder::with_capacity(new_len);

        ret.auto.states.push(State::new(false));

        for mut alt in alts {
            let cur_len = ret.len();
            ret.auto.add_eps(0, cur_len);

            let this_len = alt.len();
            alt.fix_indices(cur_len);
            ret.auto.states.extend(alt.auto.states);
            ret.auto.add_eps(cur_len + this_len - 1, new_len - 1);
        }
        ret.auto.states.push(State::new(true));
        ret
    }

    pub fn repeat(mut self, rep: Repeater) -> AutomatonBuilder {
        let last = self.len() - 1;
        match rep {
            Repeater::ZeroOrOne => {
                self.auto.add_eps(0, last);
            },
            Repeater::ZeroOrMore => {
                self.auto.add_eps(0, last);
                self.auto.add_eps(last, 0);
            },
            Repeater::OneOrMore => {
                self.auto.add_eps(last, 0);
            },
            Repeater::Range{..} => {
                panic!("range not supported yet");
            }
        }
        self
    }

    pub fn from_expr(e: &Expr) -> AutomatonBuilder {
        use regex_syntax::Expr::*;

        fn from_exprs(es: &Vec<Expr>) -> Vec<AutomatonBuilder> {
            es.iter().map(AutomatonBuilder::from_expr).collect()
        }

        match e {
            &Class(ref c) => AutomatonBuilder::char(c),
            &Concat(ref es) => AutomatonBuilder::concat(from_exprs(es)),
            &Alternate(ref es) => AutomatonBuilder::alternate(from_exprs(es)),
            &Literal { ref chars, .. } => AutomatonBuilder::literal(chars.iter()),
            &Group { ref e, .. } => AutomatonBuilder::from_expr(&e),
            &Repeat { ref e, r, .. } => AutomatonBuilder::repeat(AutomatonBuilder::from_expr(e), r),
            _ => { panic!("unsupported expr") }
        }
    }
}

#[cfg(test)]
mod tests {
    use ::builder::AutomatonBuilder;
    use ::automaton::{Automaton, State};
    use ::transition::SymbRange;
    use regex_syntax;

    fn parse(s: &str) -> regex_syntax::Result<Automaton> {
        let expr = try!(regex_syntax::Expr::parse(s));
        Ok(AutomatonBuilder::from_expr(&expr).to_automaton())
    }

    fn make_auto(n_states: usize) -> Automaton {
        let mut ret = Automaton::with_capacity(n_states);

        if n_states > 0 {
            for _ in 0..(n_states-1) {
                ret.states.push(State::new(false));
            }
            ret.states.push(State::new(true));
        }
        ret
    }

    #[test]
    fn test_char_class() {
        let auto = parse("[a-z][A-Z]").unwrap();
        let mut target = make_auto(4);
        target.add_transition(0, 1, SymbRange::new('a' as u32, 'z' as u32));
        target.add_eps(1, 2);
        target.add_transition(2, 3, SymbRange::new('A' as u32, 'Z' as u32));

        assert_eq!(auto, target);
    }

    #[test]
    fn test_literal() {
        let auto = parse("aZ").unwrap();
        let mut target = make_auto(3);
        target.add_transition(0, 1, SymbRange::single('a' as u32));
        target.add_transition(1, 2, SymbRange::single('Z' as u32));

        assert_eq!(auto, target);
    }

    #[test]
    fn test_repeat() {
        let auto = parse("a*z").unwrap();
        let mut target = make_auto(4);
        target.add_transition(0, 1, SymbRange::single('a' as u32));
        target.add_eps(0, 1);
        target.add_eps(1, 0);
        target.add_eps(1, 2);
        target.add_transition(2, 3, SymbRange::single('z' as u32));

        assert_eq!(auto, target);
    }

    #[test]
    fn test_alternate() {
        let auto = parse("a|z").unwrap();
        let mut target = make_auto(6);
        target.add_eps(0, 1);
        target.add_transition(1, 2, SymbRange::single('a' as u32));
        target.add_eps(2, 5);

        target.add_eps(0, 3);
        target.add_transition(3, 4, SymbRange::single('z' as u32));
        target.add_eps(4, 5);

        assert_eq!(auto, target);
    }
}

