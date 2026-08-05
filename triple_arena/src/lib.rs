//! Note: there are "alloc" (enabled by default), "std", and "serde_support"
//! feature flags. When the default "alloc" feature is enabled, the arenas have
//! a defaulted `B: ArenaBacking = triple_arena::utils::HeapBacking` parameter,
//! but when the alloc feature is optional, the parameter should always be
//! specified.

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::type_complexity)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod arena;
mod chain;
mod ord;
mod stack;
// this would have directly been the `traits` module, but things had to be so
// selective that we synthesize the `utils` and `traits` modules instead
mod fundamental;
mod surject;

// reexport for the macros to use
pub use arena::{Arena, DirectArena, arena_iterators, direct_arena_iterators};
pub(crate) use chain::LinkInsertInxKind;
pub use chain::{ChainArena, Link, LinkInsertKind, LinkNoGen, chain_iterators};
/// Documentation on arenas and serialization
#[cfg(feature = "serde_support")]
pub use fundamental::serde_docs;
pub use fundamental::{InvalidationOption, InvalidationResult, errors};
pub use ord::{OrdInsertKind, SimpleOrdArena, SimpleOrdItem, ord_iterators};
pub use surject::{SurjectArena, surject_iterators};

#[cfg(feature = "alloc")]
pub use crate::stack::{FixedHeapBacking, HeapBacking, LimitedHeapBacking};
pub use crate::{ord::OrdPair, stack::StackBacking};

/// Special utilities for advanced usage
pub mod utils {
    pub(crate) use crate::arena::{from_checked_ptr, from_checked_raw};
    #[cfg(feature = "alloc")]
    pub use crate::stack::{
        NonZeroInxBoxedSlice, NonZeroInxBoxedSlicePushEntry, NonZeroInxLimitedVec,
        NonZeroInxLimitedVecPushEntry, NonZeroInxVec, NonZeroInxVecPushEntry,
    };
    pub use crate::{
        arena::{ArenaInsertEntry, ArenaSlot, DirectSlot},
        chain::{ChainArena, chain_iterators},
        fundamental::PtrNoGen,
        ord::{Node, SimpleOrdArenaInsertEntry},
        stack::{NonZeroInxArray, NonZeroInxArrayPushEntry},
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
            fundamental::{PtrGen, PtrInx},
            stack::{
                ArenaBacking, NonZeroInxGenericStack, NonZeroInxGenericStackPushEntryTrait,
                SetMaxCapacity,
            },
        };
    }
}

/// All the main traits, this can be glob imported
pub mod traits {
    pub use recasting::{Recast, Recaster};

    pub use crate::{
        arena::{
            ArenaCloneFromWith, ArenaDirectInsertEntryTrait, ArenaDirectInsertTrait,
            ArenaInsertEntryTrait, ArenaInsertTrait, ArenaTrait, SingularGenerationArena,
        },
        chain::ChainArenaTrait,
        fundamental::{Advancer, Ptr},
        stack::SetMaxCapacity,
    };
}
