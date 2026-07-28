//! Note: there are "alloc" (enabled by default), "std", and "serde_support"
//! feature flags. When the default "alloc" feature is enabled, the arenas have
//! a defaulted `B: ArenaBacking = triple_arena::utils::HeapBacking` parameter,
//! but when the alloc feature is optional, the parameter should always be
//! specified.

#![no_std]
#![allow(clippy::type_complexity)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod arena;
mod chain;
mod ord;
// this would have directly been the `traits` module, but things had to be so
// selective that we synthesize the `utils` and `traits` modules instead
mod fundamental;
mod surject;

// reexport for the macros to use
pub use arena::{Arena, arena_iterators};
pub use chain::{ChainArena, Link, chain_iterators};
/// Documentation on arenas and serialization
#[cfg(feature = "serde_support")]
pub use fundamental::serde_docs;
pub use fundamental::{
    AllocError, DirectInsertionError, InvalidationOption, InvalidationResult,
    MaxCapacityReductionError, NotWithinCapacityError, ReallocationError,
};
pub use ord::{OrdArena, ord_iterators};
pub use surject::{SurjectArena, surject_iterators};

pub use crate::arena::StackBacking;
#[cfg(feature = "alloc")]
pub use crate::arena::{FixedHeapBacking, HeapBacking, LimitedHeapBacking};

/// Special utilities for advanced usage
pub mod utils {
    #[cfg(feature = "alloc")]
    pub use crate::arena::{
        NonZeroInxBoxedSlice, NonZeroInxBoxedSlicePushEntry, NonZeroInxLimitedVec,
        NonZeroInxLimitedVecPushEntry, NonZeroInxVec, NonZeroInxVecPushEntry,
    };
    // FIXME rename? or put in another module, do the same with InternalSlot
    pub use crate::ord::Node;
    pub use crate::{
        arena::{InternalSlot, NonZeroInxArray, NonZeroInxArrayPushEntry},
        chain::{ChainNoGenArena, LinkNoGen, chain_no_gen_iterators},
        fundamental::PtrNoGen,
    };
    /// A reexport used by the macros
    #[cfg(feature = "serde_support")]
    pub mod serde {
        pub use serde::{Deserialize, Deserializer, Serialize, Serializer};
    }

    // `ArenaBacking` is rarely referenced directly so we put it in here

    /// Traits for [crate::utils]
    pub mod traits {
        pub use crate::{
            arena::ArenaBacking,
            chain::{ChainNoGenArena, LinkNoGen, chain_no_gen_iterators},
            fundamental::{
                NonZeroInxGenericStack, NonZeroInxGenericStackPushEntryTrait, PtrGen, PtrInx,
                SetMaxCapacity,
            },
        };
    }
}

/// All the main traits, this can be glob imported
pub mod traits {
    pub use recasting::{Recast, Recaster};

    pub use crate::fundamental::{
        Advancer, ArenaCloneFromWith, ArenaDirectInsertTrait, ArenaInsertEntryTrait,
        ArenaInsertTrait, ArenaTrait, ChainArenaTrait, Ptr, SetMaxCapacity,
        SingularGenerationArena,
    };
}
