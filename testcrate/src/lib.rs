use triple_arena::prelude::*;
use triple_arena_render::*;

pub struct MyNode<P: PtrTrait> {
    pub sources: Vec<(Ptr<P>, String)>,
    pub center: Vec<String>,
    pub sinks: Vec<(Ptr<P>, String)>,
}

impl<P: PtrTrait> MyNode<P> {
    pub fn new(
        sources: Vec<(Ptr<P>, String)>,
        center: Vec<String>,
        sinks: Vec<(Ptr<P>, String)>,
    ) -> Self {
        Self {
            sources,
            center,
            sinks,
        }
    }
}

impl<P: PtrTrait> DebugNodeTrait<P> for MyNode<P> {
    fn debug_node(this: &Self) -> DebugNode<P> {
        DebugNode {
            sources: this.sources.clone(),
            center: this.center.clone(),
            sinks: this.sinks.clone(),
        }
    }
}

ptr_trait_struct_with_gen!(P0);
