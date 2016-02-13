use std::fmt::Debug;

pub trait Engine<Ret: Debug>: Debug {
    fn shortest_match(&self, s: &str) -> Option<(usize, usize, Ret)>;
    fn clone_box(&self) -> Box<Engine<Ret>>;
}

pub mod anchored;
pub mod forward_backward;
pub mod program;
