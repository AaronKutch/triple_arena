mod arena_backing;
pub mod arena_iterators;
mod base_arena;
#[cfg(feature = "alloc")]
mod heap_backing;
#[cfg(feature = "alloc")]
mod limited_heap_backing;
mod stack_backing;

pub use arena_backing::{ArenaBacking, StackBacking};
#[cfg(feature = "alloc")]
pub use arena_backing::{HeapBacking, LimitedHeapBacking};
pub use base_arena::{Arena, InternalEntry};
#[cfg(feature = "alloc")]
pub use heap_backing::NonZeroInxVec;
#[cfg(feature = "alloc")]
pub use limited_heap_backing::NonZeroInxLimitedVec;
pub use stack_backing::NonZeroInxArray;
