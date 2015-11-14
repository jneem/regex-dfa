// Copyright 2015 Joe Neeman.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use engine::Engine;
use prefix::Prefix;
use program::{Program, InitStates, Instructions};
use searcher::{Skipper, SkipToByteSet, SkipToByte, SkipToStr, AcSkipper, LoopSkipper, NoSkipper};
use std::mem;
use std::cell::RefCell;
use std::ops::DerefMut;

#[derive(Clone, Debug, PartialEq)]
struct Thread {
    state: usize,
    start_idx: usize,
}

#[derive(Clone, Debug, PartialEq)]
struct Threads {
    threads: Vec<Thread>,
    states: Vec<u8>,
}

impl Threads {
    fn with_capacity(n: usize) -> Threads {
        Threads {
            threads: Vec::with_capacity(n),
            states: vec![0; n],
        }
    }

    fn add(&mut self, state: usize, start_idx: usize) {
        if self.states[state] == 0 {
            self.states[state] = 1;
            self.threads.push(Thread { state: state, start_idx: start_idx });
        }
    }

    fn starts_after(&self, start_idx: usize) -> bool {
        self.threads.is_empty() || self.threads[0].start_idx >= start_idx
    }
}

#[derive(Clone, Debug, PartialEq)]
struct ProgThreads {
    cur: Threads,
    next: Threads,
}

impl ProgThreads {
    fn with_capacity(n: usize) -> ProgThreads {
        ProgThreads {
            cur: Threads::with_capacity(n),
            next: Threads::with_capacity(n),
        }
    }

    fn swap(&mut self) {
        mem::swap(&mut self.cur, &mut self.next);
        self.next.threads.clear();
    }

    fn clear(&mut self) {
        self.cur.threads.clear();
        self.next.threads.clear();

        for s in &mut self.cur.states {
            *s = 0;
        }
        for s in &mut self.next.states {
            *s = 0;
        }
    }
}

#[derive(Clone, Debug)]
pub struct ThreadedEngine<Insts: Instructions> {
    prog: Program<Insts>,
    threads: RefCell<ProgThreads>,
    prefix: Prefix,
}

impl<Insts: Instructions> ThreadedEngine<Insts> {
    pub fn new(prog: Program<Insts>, pref: Prefix) -> ThreadedEngine<Insts> {
        let len = prog.num_states();
        ThreadedEngine {
            prog: prog,
            threads: RefCell::new(ProgThreads::with_capacity(len)),
            prefix: pref,
        }
    }

    fn advance_thread(&self,
            threads: &mut ProgThreads,
            acc: &mut Option<(usize, usize)>,
            i: usize,
            input: &[u8],
            pos: usize) {
        let state = threads.cur.threads[i].state;
        let start_idx = threads.cur.threads[i].start_idx;
        threads.cur.states[state] = 0;

        let (next_state, accept) = self.prog.step(state, &input[pos..]);
        if let Some(bytes_ago) = accept {
            // We need to use saturating_sub here because Nfa::determinize_for_shortest_match
            // makes it so that bytes_ago can be positive even when start_idx == 0.
            let acc_idx = start_idx.saturating_sub(bytes_ago as usize);
            if acc.is_none() || acc_idx < acc.unwrap().0 {
                *acc = Some((acc_idx, pos));
            }
        }
        if let Some(next_state) = next_state {
            threads.next.add(next_state, start_idx);
        }
    }

    fn shortest_match_<'a, Skip>(&'a self, s: &[u8], skip: Skip, init: &InitStates)
    -> Option<(usize, usize)>
    where Skip: Skipper + 'a
    {
        let mut acc: Option<(usize, usize)> = None;
        let (first_start_pos, mut pos, start_state) = match skip.skip(s, 0) {
            Some(x) => x,
            None => return None,
        };
        let mut threads_guard = self.threads.borrow_mut();
        let threads = threads_guard.deref_mut();

        threads.clear();
        threads.cur.threads.push(Thread { state: start_state, start_idx: first_start_pos });
        while pos < s.len() {
            for i in 0..threads.cur.threads.len() {
                self.advance_thread(threads, &mut acc, i, s, pos);
            }
            threads.swap();

            // If one of our threads accepted and it started sooner than any of our active
            // threads, we can stop early.
            if acc.is_some() && threads.cur.starts_after(acc.unwrap().0) {
                return acc;
            }

            // If we're out of threads, skip ahead to the next good position (but be sure to
            // always advance the input by at least one char).
            pos += 1;
            if threads.cur.threads.is_empty() {
                if let Some((next_start_pos, next_pos, state)) = skip.skip(s, pos) {
                    pos = next_pos;
                    threads.cur.add(state, next_start_pos);
                } else {
                    return None
                }
            } else if let Some(state) = init.state_at_pos(s, pos) {
                threads.cur.add(state, pos);
            }
        }

        for th in &threads.cur.threads {
            if let Some(bytes_ago) = self.prog.check_eoi(th.state) {
                return Some((th.start_idx, s.len().saturating_sub(bytes_ago)));
            }
        }
        None
    }

}

impl<I: Instructions + 'static> Engine for ThreadedEngine<I> {
    fn shortest_match(&self, s: &str) -> Option<(usize, usize)> {
        if self.prog.num_states() == 0 {
            return None;
        }

        let s = s.as_bytes();
        let ret = match self.prefix {
                Prefix::ByteSet(ref bs, state) =>
                    self.shortest_match_(s, SkipToByteSet(bs, state), self.prog.init()),
                Prefix::Byte(b, state) =>
                    self.shortest_match_(s, SkipToByte(b, state), self.prog.init()),
                Prefix::Lit(ref lit, state) =>
                    self.shortest_match_(s, SkipToStr::new(&lit, state), self.prog.init()),
                Prefix::Ac(ref ac, _) =>
                    self.shortest_match_(
                        s,
                        AcSkipper(ac, self.prog.init()),
                        self.prog.init()),
                Prefix::LoopWhile(ref bs, state) =>
                    self.shortest_match_(s, LoopSkipper(bs, state), self.prog.init()),
                Prefix::Empty =>
                    self.shortest_match_(s, NoSkipper(self.prog.init()), self.prog.init()),
        };

        if ret.is_none() {
            self.prog.check_empty_match_at_end(s)
        } else {
            ret
        }
    }

    fn clone_box(&self) -> Box<Engine> {
        Box::new(self.clone())
    }
}

