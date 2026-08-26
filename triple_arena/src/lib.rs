//! Provides multiple very flexible and ideal arena types. All support non-Clone
//! entry insertion and deletion. All are indexable with a `P: Ptr` generic,
//! which contains an optional generation counter to check for invalidity (zero
//! cost when omitted). `no_std` and even `no_alloc` compatible.
//!
//! - [Arena]`<P, T>` is the basic unassociated and nonhereditary arena type
//! - [ChainArena]`<P, T>` allows associating entries together into multiple
//!   linear or cyclic chains, representing an idealized doubly linked list
//!   stored on an arena
//! - [SurjectArena]`<P, T, S>` is a special kind of union-find data structure
//!   that can associate `T` element entries into nonhereditary sets, which we
//!   call surjects as a shorthand. Each surject has a common `S` shared value.
//! - [SimpleOrdArena]`<P, T>` is a fusion between an ordered balanced tree and
//!   an arena. Entries can be a uniform combined value and key to be ordered
//!   by. Hereditary and nonhereditary insertion is supported. Unlike most
//!   `BTreeMap`s and `HashMap`s, the `P: Ptr` references to entries are stable,
//!   and can be trivially reused for `O(1)` operations.
//! - [DirectArena]`<P, T>` is a freelist-less arena with alternate "direct
//!   insertion" methods
//!
//! Note: most of the functionality is on the traits in [traits], which can be
//! glob imported.
//!
//! Note: there are "alloc" (enabled by default), "std", and "serde_support"
//! feature flags. When the default "alloc" feature is enabled, the arenas have
//! a defaulted `B: ArenaBacking = triple_arena::utils::HeapBacking` parameter,
//! but when the alloc feature is optional, the parameter should always be
//! specified.

// Disclaimer: there is some LLM generated code, but besides some localized fixes, I have kept any
// plain vibe coding to the tests folder and extraneous things. See all commits mentioning "LLM".

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::type_complexity)]
#![deny(clippy::cast_possible_truncation)]
#![deny(clippy::cast_possible_wrap)]
#![deny(clippy::indexing_slicing)]
#![deny(clippy::cast_lossless)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(rustdoc::private_intra_doc_links)]

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
// this renders a crate level doc correctly
#[cfg(feature = "serde_support")]
pub use fundamental::serde_docs;
pub use fundamental::{InvalidationOption, InvalidationResult, errors};
pub use ord::{OrdEntryKind, OrdInsertKind, SimpleOrdArena, ord_iterators};
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
        arena::{ArenaDirectInsertEntry, ArenaInsertEntry, ArenaSlot, DirectSlot},
        chain::ChainArenaInsertEntry,
        fundamental::{IntoNonZeroUsizeIterator, NonZeroUsizeIterator, PtrNoGen, nzusize_iter},
        ord::{SimpleOrdArenaInsertEntry, SimpleOrdArenaNode},
        stack::{NonZeroInxArray, NonZeroInxArrayPushEntry},
        surject::{SurjectElement, SurjectShared},
    };
    /// A reexport used by the macros
    #[cfg(feature = "serde_support")]
    pub mod serde {
        pub use serde::{Deserialize, Deserializer, Serialize, Serializer};
    }

    // `ArenaBacking` is rarely referenced directly so we put it in here

    /// Traits for [utils](crate::utils)
    pub mod traits {
        pub use crate::{
            fundamental::{PtrGen, PtrInx},
            ord::SimpleOrdItem,
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
            ArenaInsertEntryTrait, ArenaInsertTrait, ArenaTrait, CompactArenaTrait,
            DisjointableArenaTrait,
        },
        chain::ChainArenaTrait,
        fundamental::{Advancer, Ptr},
        stack::SetMaxCapacity,
    };
}
