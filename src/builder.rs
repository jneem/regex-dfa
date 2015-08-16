use automaton::{Nfa, NfaState};
use transition::{SymbRange, NfaTransitions};
use regex_syntax::{CharClass, Expr, Repeater};
use std::ops::Deref;

// The automaton here is non-deterministic, and guaranteed to have exactly
// one accepting state: the last one. In fact, we don't even mark that state
// as accepting, but we implicitly know that it is.
// TODO: test some optimizations:
//  - avoid fixing up indices by using relative instead of absolute offsets
//  - avoid reallocation and copying by using linked lists instead of vectors
pub struct NfaBuilder {
    auto: Nfa,
}

impl NfaBuilder {
    pub fn with_capacity(n: usize) -> NfaBuilder {
        NfaBuilder {
            auto: Nfa::with_capacity(n),
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
    
    pub fn to_automaton(mut self) -> Nfa {
        let len = self.len();
        self.auto.states[len-1].accepting = true;
        self.auto
    }

    // Given a transition list, constructs the automaton with two
    // states and that transition list. The target state of all transitions
    // in the list should be `1'.
    fn single_transition(trans: NfaTransitions) -> NfaBuilder {
        let mut ret = NfaBuilder::with_capacity(2);

        ret.auto.states.push(NfaState::new(false));
        ret.auto.states.push(NfaState::new(false));
        ret.auto.states[0].transitions = trans;

        ret
     }

    /// Builds an automaton that recognizes a language consisting of a single character from a
    /// specific class.
    pub fn char(c: &CharClass) -> NfaBuilder {
        NfaBuilder::single_transition(NfaTransitions::from_char_class(c, 1))
    }

    /// Builds an automaton that recognizes the language consisting of any single character.
    pub fn any_char() -> NfaBuilder {
        NfaBuilder::single_transition(NfaTransitions::any_char(1))
    }

    /// Builds an automaton that recognizes the language consisting of a single character belonging
    /// to the given string. The string must be sorted.
    pub fn any_char_except(chars: &str) -> NfaBuilder {
        NfaBuilder::single_transition(NfaTransitions::any_char_except(chars, 1))
    }

    pub fn literal<C, I>(chars: I) -> NfaBuilder
        where C: Deref<Target=char>,
              I: Iterator<Item=C>
    {
        let len = chars.size_hint().0 + 1;
        let mut ret = NfaBuilder::with_capacity(len);
        ret.auto.states.push(NfaState::new(false));

        for (i, ch) in chars.enumerate() {
            ret.auto.states.push(NfaState::new(false));
            ret.auto.add_transition(i, i+1, SymbRange::single(*ch as u32));
        }

        ret
    }

    fn append(&mut self, mut other: NfaBuilder) {
        let len = self.len();

        other.fix_indices(len);
        self.auto.states.extend(other.auto.states);

        if len > 0 {
            self.auto.add_eps(len-1, len);
        }
    }

    pub fn concat(autos: Vec<NfaBuilder>) -> NfaBuilder {
        let new_len = autos.iter().map(|a| a.len()).sum::<usize>();
        let mut ret = NfaBuilder::with_capacity(new_len);

        for auto in autos {
            ret.append(auto);
        }
        ret
    }

    pub fn alternate(alts: Vec<NfaBuilder>) -> NfaBuilder {
        // The new length is 2 more than the sum of existing lengths: 1 for the
        // new initial state and 1 for the new final state.
        let new_len = alts.iter().map(|a| a.len()).sum::<usize>() + 2;
        let mut ret = NfaBuilder::with_capacity(new_len);

        ret.auto.states.push(NfaState::new(false));

        for mut alt in alts {
            let cur_len = ret.len();
            ret.auto.add_eps(0, cur_len);

            let this_len = alt.len();
            alt.fix_indices(cur_len);
            ret.auto.states.extend(alt.auto.states);
            ret.auto.add_eps(cur_len + this_len - 1, new_len - 1);
        }
        ret.auto.states.push(NfaState::new(true));
        ret
    }

    pub fn repeat(mut self, rep: Repeater) -> NfaBuilder {
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

    pub fn from_expr(e: &Expr) -> NfaBuilder {
        use regex_syntax::Expr::*;

        fn from_exprs(es: &Vec<Expr>) -> Vec<NfaBuilder> {
            es.iter().map(NfaBuilder::from_expr).collect()
        }

        match e {
            &Class(ref c) => NfaBuilder::char(c),
            &Concat(ref es) => NfaBuilder::concat(from_exprs(es)),
            &Alternate(ref es) => NfaBuilder::alternate(from_exprs(es)),
            &Literal { ref chars, .. } => NfaBuilder::literal(chars.iter()),
            &Group { ref e, .. } => NfaBuilder::from_expr(&e),
            &Repeat { ref e, r, .. } => NfaBuilder::repeat(NfaBuilder::from_expr(e), r),
            &AnyChar => NfaBuilder::any_char(),
            &AnyCharNoNL => NfaBuilder::any_char_except("\n\r"),
            _ => { panic!("unsupported expr: {:?}", e) }
        }
    }
}

#[cfg(test)]
mod tests {
    use builder::NfaBuilder;
    use automaton::{Nfa, NfaState};
    use transition::SymbRange;
    use regex_syntax;

    fn parse(s: &str) -> regex_syntax::Result<Nfa> {
        let expr = try!(regex_syntax::Expr::parse(s));
        Ok(NfaBuilder::from_expr(&expr).to_automaton())
    }

    fn make_auto(n_states: usize) -> Nfa {
        let mut ret = Nfa::with_capacity(n_states);

        if n_states > 0 {
            for _ in 0..(n_states-1) {
                ret.states.push(NfaState::new(false));
            }
            ret.states.push(NfaState::new(true));
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

