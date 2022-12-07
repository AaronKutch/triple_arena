use triple_arena::{ptr_struct, Ptr};
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
    fn debug_node(_p_this: P, this: &Self) -> DebugNode<P> {
        DebugNode {
            sources: this.sources.clone(),
            center: this.center.clone(),
            sinks: this.sinks.clone(),
        }
    }
}

ptr_struct!(P0);
