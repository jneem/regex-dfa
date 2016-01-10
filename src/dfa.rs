// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use look::Look;
use nfa::{Accept, StateSet};
use prefix::PrefixSearcher;
use range_map::{Range, RangeMap, RangeMultiMap, RangeSet};
use refinery::Partition;
use runner::prefix::Prefix;
use runner::program::{Inst, TableInsts, VmInsts};
use std;
use std::collections::{HashSet, HashMap};
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::mem;
use std::u32;

#[derive(Clone, PartialEq, Debug)]
pub struct State<Ret> {
    pub transitions: RangeMap<u8, usize>,
    pub accept: Accept,
    pub ret: Option<Ret>,
}

impl<Ret> State<Ret> {
    pub fn new(accept: Accept, ret: Option<Ret>) -> State<Ret> {
        State {
            transitions: RangeMap::new(),
            accept: accept,
            ret: ret,
        }
    }
}

pub trait RetTrait: Clone + Copy + Debug + Eq + Hash {}
impl<T: Clone + Copy + Debug + Eq + Hash> RetTrait for T {}

#[derive(PartialEq)]
pub struct Dfa<Ret: 'static> {
    states: Vec<State<Ret>>,

    /// This is a vector of length `Look::num()` containing all possible starting positions.
    ///
    /// `init[Look::Boundary]` is the starting position if we are at the beginning of the
    /// input.
    ///
    /// `init[Look::Full]` is the default starting position.
    ///
    /// All other positions in `init` are only used if we are specifically asked to start
    /// there; this is mainly useful in the forward-backward engine.
    pub init: Vec<Option<usize>>,
}

impl<Ret: RetTrait> Dfa<Ret> {
    /// Returns a `Dfa` with no states.
    pub fn new() -> Dfa<Ret> {
        Dfa {
            states: Vec::new(),
            init: vec![None; Look::num()],
        }
    }

    /// Returns the number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    pub fn add_state(&mut self, accept: Accept, ret: Option<Ret>) -> usize {
        self.states.push(State::new(accept, ret));
        self.states.len() - 1
    }

    pub fn set_transitions(&mut self, from: usize, transitions: RangeMap<u8, usize>) {
        self.states[from].transitions = transitions;
    }

    pub fn init_state(&self, look: Look) -> Option<usize> {
        self.init[look.as_usize()]
    }

    pub fn init_at_start(&self) -> Option<usize> {
        self.init_state(Look::Boundary)
    }

    pub fn init_otherwise(&self) -> Option<usize> {
        self.init_state(Look::Full)
    }

    /// Returns true if this `Dfa` only matches things at the beginning of the input.
    pub fn is_anchored(&self) -> bool {
        self.init_otherwise().is_none() && self.init_at_start().is_some()
    }

    /// Get transitions from a given state.
    pub fn transitions(&self, state: usize) -> &RangeMap<u8, usize> {
        &self.states[state].transitions
    }

    /// Returns the conditions under which the given state accepts.
    pub fn accept(&self, state: usize) -> &Accept {
        &self.states[state].accept
    }

    /// The value that will be returned if we accept in state `state`.
    pub fn ret(&self, state: usize) -> Option<&Ret> {
        self.states[state].ret.as_ref()
    }

    /// Changes the return value.
    pub fn map_ret<T: RetTrait, F: FnMut(Ret) -> T>(self, mut f: F) -> Dfa<T> {
        let mut ret: Dfa<T> = Dfa::new();
        ret.init = self.init;

        for st in self.states {
            let new_st = State {
                transitions: st.transitions,
                accept: st.accept,
                ret: st.ret.map(&mut f),
            };
            ret.states.push(new_st);
        }
        ret
    }

    /// Returns an equivalent DFA with a minimal number of states.
    ///
    /// Uses Hopcroft's algorithm.
    fn minimize(&self) -> Dfa<Ret> {
        let mut min = Minimizer::new(self);
        min.minimize()
    }

    /// Returns the transitions of this automaton, reversed.
    fn reversed_transitions(&self) -> Vec<RangeMultiMap<u8, usize>> {
        let mut ret = vec![RangeMultiMap::new(); self.states.len()];

        for (source, st) in self.states.iter().enumerate() {
            for &(range, target) in st.transitions.ranges_values() {
                ret[target].insert(range, source);
            }
        }

        ret
    }

    fn make_prefix(&self, state_map: &[usize], prune_suffixes: bool) -> Prefix {
        let mut searcher = PrefixSearcher::new(prune_suffixes);
        // It might seem silly to look for prefixes starting at the anchored state, but it's useful
        // for forward-backward matching. In cases where the regex is honestly anchored, we won't
        // ask to make a prefix anyway.
        if let Some(state) = self.init_state(Look::Boundary) {
            searcher.search(self, state);
        }
        searcher.map_states(|x| state_map[x]);
        Prefix::from_strings(searcher.finished.into_iter().map(|x| (x.0, x.1)))
    }

    /// Creates a prefix that can search quickly for potential match starts.
    ///
    /// `state_map` gives a mapping between the `Dfa` states and the states that the prefix
    /// should report.
    pub fn prefix(&self, state_map: &[usize]) -> Prefix {
        self.make_prefix(state_map, false)
    }

    /// Creates a prefix that can search quickly for potential match starts. Unlike the prefix
    /// returned by `prefix()`, this prefix doesn't necessarily have the same starting position as
    /// the whole match.
    ///
    /// `state_map` gives a mapping between the `Dfa` states and the states that the prefix
    /// should report.
    pub fn pruned_prefix(&self, state_map: &[usize]) -> Prefix {
        self.make_prefix(state_map, true)
    }

    /// Compiles this `Dfa` into instructions for execution.
    ///
    /// Returns the new instructions, along with a map from the dfa states to the instructions.
    pub fn compile<P: CompileTarget<Ret>>(&self) -> (P, Vec<usize>) {
        P::from_dfa(self)
    }

    // TODO: should trim unreachable here -- match_python_281 is an example where it will help
    pub fn optimize_for_shortest_match(self) -> Dfa<Ret> {
        // Repeatedly `minimize` and `optimize_once_for_shortest_match` until we reach a fixed
        // point.
        let mut ret = self.minimize();
        loop {
            if !ret.optimize_once_for_shortest_match() {
                break;
            }
            let last_len = ret.num_states();
            ret = ret.minimize();
            if ret.num_states() == last_len {
                break;
            }
        }
        ret.sort_states();
        ret
    }

    pub fn optimize(self) -> Dfa<Ret> {
        let mut ret = self.minimize();
        ret.sort_states();
        ret
    }

    /// Deletes any transitions that return to the initial state.
    ///
    /// This results in a new Dfa with the following properties:
    /// - if the original Dfa has a match then the new Dfa also has a match that ends in the same
    ///   position (and vice versa), and
    /// - the new Dfa doesn't need to backtrack to find matches: if it fails then it can be
    ///   restarted at the same position it failed in.
    ///
    /// The reason for this method is that it makes prefixes more effective: where the original Dfa
    /// would just loop back to the start state, the new Dfa will signal a failure. Then we can use
    /// a `Prefix` to scan ahead for a good place to resume matching.
    ///
    /// # Panics
    /// - if `self` is not anchored.
    pub fn cut_loop_to_init(mut self) -> Dfa<Ret> {
        if !self.is_anchored() {
            panic!("only anchored Dfas can be cut");
        }

        // The unwrap is safe because we just checked that we are anchored.
        let init = self.init_at_start().unwrap();
        for st in &mut self.states {
            st.transitions.retain_values(|x| *x != init);
        }
        self
    }

    /// Deletes any transitions after a match. Returns true if anything changed.
    fn optimize_once_for_shortest_match(&mut self) -> bool {
        let mut changed = false;
        for st in &mut self.states {
            if st.accept == Accept::Always {
                changed |= !st.transitions.is_empty();
                st.transitions = RangeMap::new();
            }
        }
        changed
    }

    /// Does a depth-first search of this `Dfa`.
    ///
    /// Every time the search visits a new state, `visit` will be called. Every time the search
    /// detects a loop, `cycle` will be called. If either of these calls returns `false`, the
    /// search will terminate early.
    fn dfs<Visit, Cycle>(&self, mut visit: Visit, mut cycle: Cycle)
    where Visit: FnMut(usize) -> bool, Cycle: FnMut(&[usize]) -> bool {
        if self.states.is_empty() {
            return;
        }

        // Pairs of (state, children_left_to_explore).
        let mut stack: Vec<(usize, std::slice::Iter<_>)> = Vec::with_capacity(self.states.len());
        let mut visiting: Vec<bool> = vec![false; self.states.len()];
        let mut done: Vec<bool> = vec![false; self.states.len()];

        // For nodes that we are currently visiting, this is their position on the stack.
        let mut stack_pos: Vec<usize> = vec![0; self.states.len()];

        let start_states: Vec<usize> = self.init.iter().filter_map(|x| *x).collect();

        for &start_idx in &start_states {
            if !done[start_idx] {
                if !visit(start_idx) { return; }
                stack.push((start_idx, self.states[start_idx].transitions.ranges_values()));
                visiting[start_idx] = true;
                stack_pos[start_idx] = 0;

                while !stack.is_empty() {
                    let (cur, next_child) = {
                        let &mut (cur, ref mut children) = stack.last_mut().unwrap();
                        (cur, children.next())
                    };

                    if let Some(&(_, child)) = next_child {
                        if visiting[child] {
                            // We found a cycle: report it (and maybe terminate early).
                            let cyc: Vec<_> = stack[stack_pos[child]..].iter()
                                .map(|x| x.0)
                                .collect();

                            if !cycle(&cyc) { return; }
                        } else if !done[child] {
                            // This is a new state: report it and push it onto the stack (and maybe
                            // terminate early).
                            if !visit(child) { return; }

                            stack.push((child, self.states[child].transitions.ranges_values()));
                            visiting[child] = true;
                            stack_pos[child] = stack.len() - 1;
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
    fn dfs_order(&self) -> Vec<usize> {
        let mut ret: Vec<usize> = Vec::new();
        self.dfs(|st| { ret.push(st); true }, |_| true);
        ret
    }

    fn map_states<F: FnMut(usize) -> usize>(&mut self, mut map: F) {
        for st in &mut self.states {
            st.transitions.map_values(|x| map(*x));
        }
        let init: Vec<_> = self.init.iter().map(|x| x.map(|y| map(y))).collect();
        self.init = init;
    }

    /// Sorts states in depth-first alphabetical order.
    ///
    /// This has the following advantages:
    /// - the construction of a `Dfa` becomes deterministic: without sorting, the states aren't in
    ///   deterministic order because `minimize` using hashing.
    /// - better locality: after sorting, many transitions just go straight to the next state.
    /// - we prune unreachable states.
    fn sort_states(&mut self) {
        let sorted = self.dfs_order();

        // Not every old state will necessary get mapped to a new one (unreachable states won't).
        let mut state_map: Vec<Option<usize>> = vec![None; self.states.len()];
        let mut old_states = vec![State::new(Accept::Never, None); self.states.len()];
        mem::swap(&mut old_states, &mut self.states);

        for (new_idx, old_idx) in sorted.into_iter().enumerate() {
            state_map[old_idx] = Some(new_idx);
            mem::swap(&mut old_states[old_idx], &mut self.states[new_idx]);
        }

        // Fix the transitions and initialization to point to the new states. The `unwrap` here is
        // basically the assertion that all reachable states should be mapped to new states.
        self.map_states(|s| state_map[s].unwrap());
    }

    /// Checks whether this DFA has any cycles.
    ///
    /// If not, it's a good candidate for the backtracking engine.
    #[allow(unused)]
    // TODO: test for cycles in the nfa, rather than the dfa
    pub fn has_cycles(&self) -> bool {
        let mut found = false;
        self.dfs(|_| true, |_| { found = true; false });
        found
    }
}

impl<Ret: Debug> Debug for Dfa<Ret> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        try!(f.write_fmt(format_args!("Dfa ({} states):\n", self.states.len())));

        try!(f.write_fmt(format_args!("Init: {:?}\n", self.init)));

        for (st_idx, st) in self.states.iter().enumerate().take(40) {
            try!(f.write_fmt(format_args!("\tState {} (accepting: {:?}):\n", st_idx, st.accept)));
            if let Some(ref ret) = st.ret {
                try!(f.write_fmt(format_args!("\t\t{:?}\n", ret)));
            }

            if !st.transitions.is_empty() {
                try!(f.write_str("\t\tTransitions:\n"));
                // Cap it at 5 transitions, since it gets unreadable otherwise.
                for &(range, target) in st.transitions.ranges_values().take(5) {
                    try!(f.write_fmt(format_args!("\t\t\t{} -- {} => {}\n",
                                                  range.start, range.end, target)));
                }
                if st.transitions.num_ranges() > 5 {
                    try!(f.write_str("\t\t\t...\n"));
                }
            }
        }
        if self.states.len() > 40 {
            try!(f.write_fmt(format_args!("\t...({} more states)\n", self.states.len() - 40)));
        }
        Ok(())
    }
}

pub trait CompileTarget<Ret> {
    fn from_dfa(dfa: &Dfa<Ret>) -> (Self, Vec<usize>);
}

impl<Ret: RetTrait> CompileTarget<Ret> for VmInsts<Ret> {
    fn from_dfa(dfa: &Dfa<Ret>) -> (Self, Vec<usize>) {
        let mut cmp = VmCompiler::new(dfa);
        cmp.compile(dfa);
        (cmp.insts, cmp.state_map)
    }
}

impl<Ret: RetTrait> CompileTarget<Ret> for TableInsts<Ret> {
    fn from_dfa(dfa: &Dfa<Ret>) -> (Self, Vec<usize>) {
        let mut table = vec![u32::MAX; 256 * dfa.num_states()];
        let accept: Vec<Option<Ret>> = dfa.states.iter()
            .map(|st| if st.accept == Accept::Always { st.ret } else { None })
            .collect();
        let accept_at_eoi: Vec<Option<Ret>> = dfa.states.iter()
            .map(|st| if st.accept != Accept::Never { st.ret } else { None })
            .collect();

        for (idx, st) in dfa.states.iter().enumerate() {
            for (ch, &tgt_state) in st.transitions.keys_values() {
                table[idx * 256 + ch as usize] = tgt_state as u32;
            }
        }

        let insts = TableInsts {
            accept: accept,
            accept_at_eoi: accept_at_eoi,
            table: table,
            is_anchored: dfa.is_anchored(),
        };

        (insts, (0..dfa.num_states()).collect())
    }
}

struct VmCompiler<Ret: 'static> {
    state_map: Vec<usize>,
    insts: VmInsts<Ret>,
}

impl<Ret: RetTrait> VmCompiler<Ret> {
    fn new(dfa: &Dfa<Ret>) -> VmCompiler<Ret> {
        let mut state_map = vec![0; dfa.states.len()];
        let mut next_inst_idx = 0usize;

        // The VM states are almost the same as the Dfa states, except that accept instructions
        // take an extra state.
        for (i, st) in dfa.states.iter().enumerate() {
            state_map[i] = next_inst_idx;
            if st.accept == Accept::Always {
                next_inst_idx += 1;
            }
            next_inst_idx += 1;
        }

        VmCompiler {
            state_map: state_map,
            insts: VmInsts {
                byte_sets: Vec::new(),
                branch_table: Vec::new(),
                insts: Vec::with_capacity(next_inst_idx),
                accept_at_eoi: vec![None; next_inst_idx],
                is_anchored: dfa.is_anchored(),
            }
        }
    }

    fn add_byte_set(&mut self, set: &RangeSet<u8>) -> usize {
        // TODO: we could check for duplicated sets here.
        let offset = self.insts.byte_sets.len();
        self.insts.byte_sets.extend([false; 256].into_iter());
        for b in set.elements() {
            self.insts.byte_sets[offset + b as usize] = true;
        }

        debug_assert!(self.insts.byte_sets.len() % 256 == 0);
        (self.insts.byte_sets.len() / 256) - 1
    }

    fn add_byte_map(&mut self, map: &RangeMap<u8, usize>) -> usize {
        let offset = self.insts.branch_table.len();
        self.insts.branch_table.extend([u32::MAX; 256].into_iter());
        for (b, &state) in map.keys_values() {
            self.insts.branch_table[offset + b as usize] = state as u32;
        }

        debug_assert!(self.insts.branch_table.len() % 256 == 0);
        (self.insts.branch_table.len() / 256) - 1
    }

    fn single_target<'a, Iter>(mut iter: Iter) -> Option<usize>
    where Iter: Iterator<Item = &'a (Range<u8>, usize)> {
        if let Some(&(_, target)) = iter.next() {
            while let Some(&(_, next_target)) = iter.next() {
                if target != next_target {
                    return None;
                }
            }
            Some(target)
        } else {
            None
        }
    }

    fn single_char<'a, Iter>(mut iter: Iter) -> Option<u8>
    where Iter: Iterator<Item = &'a (Range<u8>, usize)> {
        if let Some(&(range, _)) = iter.next() {
            if range.start == range.end && iter.next().is_none() {
                Some(range.start)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn compile(&mut self, dfa: &Dfa<Ret>) {
        for st in &dfa.states {
            if st.accept != Accept::Never {
                self.insts.accept_at_eoi[self.insts.insts.len()] = st.ret;
            }
            if st.accept == Accept::Always {
                // This unwrap is asserting that accepting states must have return values.
                self.insts.insts.push(Inst::Acc(st.ret.unwrap()));
                // Mark the next state (which will consume) as accepting at eoi also.
                self.insts.accept_at_eoi[self.insts.insts.len()] = st.ret;
            }
            if let Some(tgt) = Self::single_target(st.transitions.ranges_values()) {
                if self.state_map[tgt] == self.insts.insts.len() + 1 {
                    // The target state is just immediately after this state -- we don't need a
                    // branch instruction.
                    let inst =
                        if let Some(ch) = Self::single_char(st.transitions.ranges_values()) {
                            Inst::Byte(ch)
                        } else {
                            Inst::ByteSet(self.add_byte_set(&st.transitions.to_range_set()))
                        };
                    self.insts.insts.push(inst);
                    continue;
                }
            }

            // If we're still here, we didn't add a Byte or ByteSet instruction, so add a Branch.
            let mut bm = st.transitions.clone();
            bm.map_values(|x| self.state_map[*x]);
            let inst = Inst::Branch(self.add_byte_map(&bm));
            self.insts.insts.push(inst);
        }
    }
}

struct Minimizer<'a, Ret: 'static> {
    partition: Partition,
    distinguishers: HashSet<usize>,
    dfa: &'a Dfa<Ret>,
    // The reversed transitions of the dfa.
    rev: Vec<RangeMultiMap<u8, usize>>,
}

impl<'a, Ret: RetTrait> Minimizer<'a, Ret> {
    fn initial_partition(dfa: &'a Dfa<Ret>) -> Vec<Vec<usize>> {
        let mut part: HashMap<(Accept, Option<&Ret>, RangeSet<u8>), Vec<usize>> = HashMap::new();
        for (idx, st) in dfa.states.iter().enumerate() {
            let chars = st.transitions.to_range_set();
            part.entry((st.accept, dfa.ret(idx), chars)).or_insert(Vec::new()).push(idx);
        }
        part.into_iter().map(|x| x.1).collect()
    }

    // Refine the current partition based on the fact that everything in `splitter` is distinct
    // from everything not in it.
    fn refine(&mut self, splitter: &[usize]) {
        let dists = &mut self.distinguishers;

        self.partition.refine_with_callback(splitter, |p, int_idx, diff_idx| {
            if dists.contains(&int_idx) || p.part(diff_idx).len() < p.part(int_idx).len() {
                dists.insert(diff_idx);
            } else {
                dists.insert(int_idx);
            }
        });
    }

    fn next_distinguisher(&mut self) -> Option<usize> {
        let maybe_elt = self.distinguishers.iter().next().cloned();
        if let Some(elt) = maybe_elt {
            self.distinguishers.remove(&elt);
        }
        maybe_elt
    }

    fn get_input_sets(&mut self, part_idx: usize) -> Vec<StateSet> {
        let inputs: Vec<_> = self.partition.part(part_idx)
                .iter()
                .flat_map(|s| self.rev[*s].ranges_values().cloned())
                .collect();
        if inputs.is_empty() {
            return Vec::new();
        }

        let inputs = RangeMultiMap::from_vec(inputs);
        let mut sets: Vec<StateSet> = inputs.group()
            .ranges_values()
            .map(|&(_, ref x)| x.clone())
            .collect();
        for set in &mut sets {
            set.sort();
        }
        sets.sort();
        sets.dedup();
        sets
    }

    fn compute_partition(&mut self) {
        while let Some(dist) = self.next_distinguisher() {
            let sets = self.get_input_sets(dist);

            for set in &sets {
                self.refine(set);
            }
        }
    }

    fn minimize(&mut self) -> Dfa<Ret> {
        self.compute_partition();

        let mut ret = Dfa::new();

        // We need to re-index the states: build a map that maps old indices to
        // new indices.
        let mut old_state_to_new = vec![0; self.dfa.num_states()];
        for part in self.partition.iter() {
            // This unwrap is safe because we don't allow any empty sets into the partition.
            let rep_idx = *part.iter().next().unwrap();
            ret.states.push(self.dfa.states[rep_idx].clone());

            for &state in part.iter() {
                old_state_to_new[state] = ret.states.len() - 1;
            }
        }

        ret.map_states(|s: usize| old_state_to_new[s]);
        ret.init = self.dfa.init.iter()
            .map(|x| x.map(|s: usize| old_state_to_new[s]))
            .collect();
        ret
    }

    fn new(dfa: &'a Dfa<Ret>) -> Minimizer<'a, Ret> {
        let init = Minimizer::initial_partition(dfa);
        let part = Partition::new(init.into_iter().map(|set| set.into_iter()), dfa.num_states());

        // According to Hopkins' algorithm, we're allowed to leave out one of the distinguishers
        // (at least, as long as it isn't a set of accepting states). Choose the one with the
        // most states to leave out.
        let mut dists: HashSet<usize> = (0..part.num_parts()).collect();
        let worst = (0..dists.len())
            .filter(|i| dfa.states[part.part(*i)[0]].accept == Accept::Never)
            .max_by_key(|i| part.part(*i).len());
        if let Some(worst) = worst {
            dists.remove(&worst);
        }

        Minimizer {
            partition: part,
            distinguishers: dists,
            dfa: dfa,
            rev: dfa.reversed_transitions(),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use dfa::*;
    use itertools::Itertools;
    use look::Look;
    use nfa::{Accept, Nfa};
    use range_map::{Range, RangeMap};
    use runner::prefix::Prefix;
    use std::usize;

    // Creates a non-backtracking dfa from a regex string.
    pub fn make_dfa_bounded(re: &str, max_states: usize) -> ::Result<Dfa<(Look, u8)>> {
        let nfa = try!(Nfa::from_regex(re));
        let nfa = nfa.remove_looks();
        let nfa = try!(nfa.byte_me(max_states));

        let dfa = try!(nfa.determinize_shortest(max_states));
        Ok(dfa.optimize_for_shortest_match())
    }

    pub fn make_dfa(re: &str) -> ::Result<Dfa<(Look, u8)>> {
        make_dfa_bounded(re, usize::MAX)
    }

    pub fn make_anchored(re: &str) -> Dfa<(Look, u8)> {
        let nfa = Nfa::from_regex(re).unwrap()
            .remove_looks()
            .byte_me(usize::MAX).unwrap()
            .anchor_look_behind(usize::MAX).unwrap();

        nfa.determinize_shortest(usize::MAX).unwrap()
            .optimize_for_shortest_match()
            .cut_loop_to_init()
            .optimize_for_shortest_match()
    }

    pub fn trans_dfa_anchored(size: usize, trans: &[(usize, usize, Range<u8>)])
    -> Dfa<(Look, u8)> {
        let mut ret = Dfa::new();
        for _ in 0..size {
            ret.add_state(Accept::Never, None);
        }
        for (src, trans) in trans.iter().group_by(|x| x.0) {
            let rm: RangeMap<u8, usize> = trans.into_iter()
                .map(|x| (x.2, x.1))
                .collect();
            ret.set_transitions(src, rm);
        }
        ret
    }

    #[test]
    fn test_anchored_dfa_simple() {
        let dfa = make_anchored("a");
        let mut tgt = trans_dfa_anchored(2, &[(0, 1, Range::new(b'a', b'a'))]);
        tgt.init[Look::Boundary.as_usize()] = Some(0);
        tgt.states[1].accept = Accept::Always;
        tgt.states[1].ret = Some((Look::Full, 0));

        assert_eq!(dfa, tgt);
    }

    #[test]
    fn test_forward_backward_simple() {
        // TODO
    }

    #[test]
    fn test_anchored_dfa_anchored_end() {
        let dfa = make_anchored("a$");
        let mut tgt = trans_dfa_anchored(2, &[(0, 1, Range::new(b'a', b'a')),
                                              (1, 1, Range::new(b'a', b'a'))]);
        tgt.init[Look::Boundary.as_usize()] = Some(0);
        tgt.states[1].accept = Accept::AtEoi;
        tgt.states[1].ret = Some((Look::Boundary, 0));

        assert_eq!(dfa, tgt);
    }

    #[test]
    fn test_anchored_dfa_literal_prefix() {
        let dfa = make_anchored("abc[A-z]");
        let state_map: Vec<_> = (0..dfa.num_states()).collect();
        let pref = dfa.pruned_prefix(&state_map);
        println!("{:?}", pref);
        match pref {
            Prefix::Lit(ref v) => assert_eq!(*v, "abc".as_bytes().to_vec()),
            _ => panic!("expected Lit"),
        }
    }

    #[test]
    fn test_minimize() {
        let auto = make_dfa("a*b*").unwrap();
        // 1, because optimizing for shortest match means we match empty strings.
        assert_eq!(auto.states.len(), 1);

        let auto = make_dfa(r"^a").unwrap();
        assert_eq!(auto.states.len(), 2);

        let mut auto = make_dfa("[cgt]gggtaaa|tttaccc[acg]").unwrap();
        // Since `minimize` is non-deterministic (involving random hashes), run this a bunch of
        // times.
        for _ in 0..100 {
            auto = auto.optimize();
            assert_eq!(auto.states.len(), 16);
        }
    }

   #[test]
    fn test_class_normalized() {
        let mut re = make_dfa("[abcdw]").unwrap();
        re.sort_states();
        assert_eq!(re.states.len(), 2);
        assert_eq!(re.states[0].transitions.num_ranges(), 2)
    }

    #[test]
    fn test_max_states() {
        assert!(make_dfa_bounded("foo", 3).is_err());
        assert!(make_dfa_bounded("foo", 4).is_ok());
    }

    #[test]
    fn test_adjacent_predicates() {
        assert!(make_dfa_bounded(r"\btest\b\B", 100).unwrap().states.is_empty());
        assert!(make_dfa_bounded(r"\btest\B\b", 100).unwrap().states.is_empty());
        assert!(make_dfa_bounded(r"test1\b\Btest2", 100).unwrap().states.is_empty());
    }

    #[test]
    fn test_syntax_error() {
        assert!(make_dfa_bounded("(abc", 10).is_err());
    }

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

    #[test]
    fn optimize_for_shortest_match() {
        macro_rules! eq {
            ($re1:expr, $re2:expr) => {
                {
                    let dfa1 = make_dfa($re1).unwrap();
                    let dfa2 = make_dfa($re2).unwrap();
                    assert_eq!(dfa1, dfa2);
                }
            };
        }
        eq!("(a|aa)", "a");
        //eq!("a*", ""); // TODO: figure out how empty regexes should behave
        eq!("abcb*", "abc");
    }

    // TODO: add a test checking that minimize() doesn't clobber return values.
}
