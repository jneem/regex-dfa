use std::fmt::Debug;

pub trait Engine<Ret: Debug>: Debug {
    fn shortest_match(&self, s: &str) -> Option<(usize, usize, Ret)>;
    fn clone_box(&self) -> Box<Engine<Ret>>;
}

#[macro_use]
pub mod prefix;

pub mod backtracking;
pub mod forward_backward;
pub mod program;
