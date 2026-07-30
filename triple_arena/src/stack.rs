mod arena_backing;
#[cfg(feature = "alloc")]
mod fixed_heap_backing;
#[cfg(feature = "alloc")]
mod heap_backing;
#[cfg(feature = "alloc")]
mod limited_heap_backing;
mod nonzero_inx_generic_stack;
mod stack_backing;

pub use arena_backing::{ArenaBacking, StackBacking};
#[cfg(feature = "alloc")]
pub use arena_backing::{FixedHeapBacking, HeapBacking, LimitedHeapBacking};
#[cfg(feature = "alloc")]
pub use fixed_heap_backing::{NonZeroInxBoxedSlice, NonZeroInxBoxedSlicePushEntry};
#[cfg(feature = "alloc")]
pub use heap_backing::{NonZeroInxVec, NonZeroInxVecPushEntry};
#[cfg(feature = "alloc")]
pub use limited_heap_backing::{NonZeroInxLimitedVec, NonZeroInxLimitedVecPushEntry};
pub use nonzero_inx_generic_stack::{
    NonZeroInxGenericStack, NonZeroInxGenericStackPushEntryTrait, SetMaxCapacity,
};
pub use stack_backing::{NonZeroInxArray, NonZeroInxArrayPushEntry};
