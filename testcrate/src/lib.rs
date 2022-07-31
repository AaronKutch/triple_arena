use triple_arena::prelude::*;
use triple_arena_render::*;

pub struct MyNode<P: Ptr> {
    pub sources: Vec<(P, String)>,
    pub center: Vec<String>,
    pub sinks: Vec<(P, String)>,
}

impl<P: Ptr> MyNode<P> {
    pub fn new(sources: Vec<(P, String)>, center: Vec<String>, sinks: Vec<(P, String)>) -> Self {
        Self {
            sources,
            center,
            sinks,
        }
    }
}

impl<P: Ptr> DebugNodeTrait<P> for MyNode<P> {
    fn debug_node(this: &Self) -> DebugNode<P> {
        DebugNode {
            sources: this.sources.clone(),
            center: this.center.clone(),
            sinks: this.sinks.clone(),
        }
    }
}

ptr_struct!(P0[core::primitive::usize](core::num::NonZeroU64));
ptr_struct!(P1[core::primitive::usize]());
ptr_struct!(P2[core::primitive::usize]);
ptr_struct!(P3(core::num::NonZeroU64));
ptr_struct!(P4());
ptr_struct!(P5);
