mod advancer;
mod arena_traits;
mod extra;
mod nonzero_inx_generic_stack;
#[cfg(not(feature = "serde_support"))]
mod ptr;
#[cfg(feature = "serde_support")]
mod ptr_serde;
#[cfg(feature = "serde_support")]
pub mod serde;
#[cfg(feature = "serde_support")]
pub mod serde_docs;

pub use advancer::Advancer;
pub use arena_traits::{
    ArenaCloneFromWith, ArenaDirectInsertTrait, ArenaInsertEntryTrait, ArenaInsertTrait,
    ArenaTrait, ChainArenaTrait, InvalidationOption, InvalidationResult, LinkInsertKind,
    SingularGenerationArena,
};
pub use extra::{
    AllocError, ChainInsertionError, DirectInsertionError, IntoNonZeroUsizeIterator,
    MaxCapacityReductionError, NotWithinCapacityError, ReallocationError, nzusize_iter,
};
pub use nonzero_inx_generic_stack::{
    NonZeroInxGenericStack, NonZeroInxGenericStackPushEntryTrait, SetMaxCapacity,
};
#[cfg(not(feature = "serde_support"))]
pub use ptr::{Ptr, PtrGen, PtrInx, PtrNoGen};
#[cfg(feature = "serde_support")]
pub use ptr_serde::{Ptr, PtrGen, PtrInx, PtrNoGen};
