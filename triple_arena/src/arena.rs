pub mod arena_iterators;
mod base_arena;
//mod nonzero_inx_vec;
mod arena_backing;
mod reference_heap_backing;
mod stack_backing;

pub use arena_backing::{ArenaBacking, HeapBacking, StackBacking};
pub use base_arena::{Arena, InternalEntry};
pub use heap_backing::NonZeroInxVec;
use reference_heap_backing as heap_backing;
pub use stack_backing::NonZeroInxArray;
