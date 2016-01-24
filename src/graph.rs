// Copyright 2016 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use dfa::{Dfa, RetTrait};
use nfa::{Nfa, NoLooks, StateIdx};

#[derive(Clone, Copy, Debug)]
pub enum DfsInstruction {
    Continue,
    TurnBack,
    Stop,
}

pub trait Graph {
    fn num_states(&self) -> usize;

    fn neighbors<'a>(&'a self, i: StateIdx) -> Box<Iterator<Item=StateIdx> + 'a>;

    /// Does a depth-first search of this graph.
    ///
    /// Every time the search visits a new state, `visit` will be called. Every time the search
    /// detects a loop, `cycle` will be called. These return value of these callbacks tell the
    /// search how to proceed:
    /// - on `Continue`, the search will proceed normally
    /// - on `TurnBack`, the search will stop searching the current branch
    /// - on `Stop`, the search will terminate early.
    fn dfs<Inits, Visit, Cycle>(&self, init: Inits, mut visit: Visit, mut cycle: Cycle)
    where
    Visit: FnMut(StateIdx) -> DfsInstruction,
    Cycle: FnMut(&[StateIdx]) -> DfsInstruction,
    Inits: Iterator<Item=StateIdx>,
    {
        // Pairs of (state, children_left_to_explore).
        let mut stack: Vec<(StateIdx, Box<Iterator<Item=StateIdx>>)>
            = Vec::with_capacity(self.num_states());
        let mut visiting: Vec<bool> = vec![false; self.num_states()];
        let mut done: Vec<bool> = vec![false; self.num_states()];

        // For nodes that we are currently visiting, this is their position on the stack.
        let mut stack_pos: Vec<usize> = vec![0; self.num_states()];

        let start_states: Vec<StateIdx> = init.collect();

        for &start_idx in &start_states {
            if !done[start_idx] {
                match visit(start_idx) {
                    DfsInstruction::Continue => {},
                    DfsInstruction::TurnBack => {
                        done[start_idx] = true;
                        continue;
                    },
                    DfsInstruction::Stop => { return; },
                }

                visiting[start_idx] = true;
                stack.push((start_idx, self.neighbors(start_idx)));
                stack_pos[start_idx] = 0;

                while !stack.is_empty() {
                    let (cur, next_child) = {
                        let &mut (cur, ref mut children) = stack.last_mut().unwrap();
                        (cur, children.next())
                    };

                    if let Some(child) = next_child {
                        if visiting[child] {
                            // We found a cycle: report it (and maybe terminate early).
                            let cyc: Vec<_> = stack[stack_pos[child]..].iter()
                                .map(|x| x.0)
                                .collect();

                            match cycle(&cyc) {
                                DfsInstruction::Stop => { return; },
                                // Since we turn back on finding a cycle anyway, we treat Continue
                                // and TurnBack the same.
                                _ => {},
                            }
                        } else if !done[child] {
                            // This is a new state: report it and push it onto the stack.
                            match visit(child) {
                                DfsInstruction::Stop => { return; },
                                DfsInstruction::TurnBack => {
                                    done[child] = true;
                                },
                                DfsInstruction::Continue => {
                                    stack.push((child, self.neighbors(child)));
                                    visiting[child] = true;
                                    stack_pos[child] = stack.len() - 1;
                                },
                            }
                        }
                        continue;
                    }

                    // If we got this far, the current node is out of children. Pop it from the
                    // stack.
                    visiting[cur] = false;
                    done[cur] = true;
                    stack.pop();
                }
            }
        }
    }

    /// Returns a list of states, visited in depth-first order.
    fn dfs_order<I: Iterator<Item=StateIdx>>(&self, init: I) -> Vec<StateIdx> {
        use self::DfsInstruction::*;

        let mut ret: Vec<StateIdx> = Vec::new();
        self.dfs(init, |st| { ret.push(st); Continue }, |_| Continue);
        ret
    }

    /// Checks whether this graph has any cycles.
    #[allow(unused)]
    fn has_cycles(&self) -> bool {
        use self::DfsInstruction::*;

        let mut found = false;
        self.dfs(0..self.num_states(), |_| Continue, |_| { found = true; Stop });
        found
    }
}

impl<T: RetTrait> Graph for Dfa<T> {
    fn num_states(&self) -> usize {
        Dfa::num_states(self)
    }

    fn neighbors<'a>(&'a self, i: StateIdx) -> Box<Iterator<Item=StateIdx> + 'a> {
        Box::new(self.transitions(i).ranges_values().map(|x| x.1))
    }
}

impl Graph for Nfa<u8, NoLooks> {
    fn num_states(&self) -> usize {
        Nfa::num_states(self)
    }

    fn neighbors<'a>(&'a self, i: usize) -> Box<Iterator<Item=usize> + 'a> {
        Box::new(self.consuming(i).ranges_values().map(|x| x.1))
    }
}

#[cfg(test)]
mod tests {
    use dfa::tests::make_dfa;
    use graph::Graph;

    #[test]
    fn cycles() {
        macro_rules! cyc {
            ($re:expr, $res:expr) => {
                {
                    let dfa = make_dfa($re).unwrap();
                    println!("{:?}", dfa);
                    assert_eq!(dfa.has_cycles(), $res);
                }
            };
        }

        cyc!("abcde", false);
        cyc!("ab*d", true);
        cyc!("ab*", false);
        cyc!("ab*$", true);
        cyc!("ab+", false);
        cyc!("ab+$", true);
        cyc!("(ab*|cde)", false);
        cyc!("(ab*|cde)f", true);
        cyc!("(abc)*", false);
        cyc!("(abc)*def", true);
    }
}

