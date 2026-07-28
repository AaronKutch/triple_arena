mod arena_backing;
pub mod arena_iterators;
mod base_arena;
#[cfg(feature = "alloc")]
mod fixed_heap_backing;
#[cfg(feature = "alloc")]
mod heap_backing;
mod impl_arena_trait;
#[cfg(feature = "alloc")]
mod limited_heap_backing;
mod stack_backing;

pub use arena_backing::{ArenaBacking, StackBacking};
#[cfg(feature = "alloc")]
pub use arena_backing::{FixedHeapBacking, HeapBacking, LimitedHeapBacking};
pub use base_arena::{Arena, InternalSlot};
#[cfg(feature = "alloc")]
pub use fixed_heap_backing::{NonZeroInxBoxedSlice, NonZeroInxBoxedSlicePushEntry};
#[cfg(feature = "alloc")]
pub use heap_backing::{NonZeroInxVec, NonZeroInxVecPushEntry};
pub use impl_arena_trait::ArenaInsertEntry;
#[cfg(feature = "alloc")]
pub use limited_heap_backing::{NonZeroInxLimitedVec, NonZeroInxLimitedVecPushEntry};
pub use stack_backing::{NonZeroInxArray, NonZeroInxArrayPushEntry};
