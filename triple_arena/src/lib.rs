//! Note: there are "alloc" (enabled by default), "std", "serde_support", and
//! "expose_internal_utils" feature flags. When the default "alloc" feature is
//! enabled, the arenas have a defaulted
//! `B: ArenaBacking = triple_arena::utils::HeapBacking` parameter, but when
//! disabled the parameter must be specified.

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
pub use fundamental::InvalidationResult;
// always keep this for the serde documentation
#[cfg(feature = "serde_support")]
pub use fundamental::serde_docs;
pub use ord::{OrdArena, ord_iterators};
pub use surject::{SurjectArena, surject_iterators};

/// Special utilities for advanced usage
pub mod utils {
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::arena::{InternalEntry, NonZeroInxArray};
    #[cfg(all(feature = "alloc", feature = "expose_internal_utils"))]
    pub use crate::arena::{NonZeroInxLimitedVec, NonZeroInxVec};
    // only intended for size_of tests and such
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::ord::Node;
    pub use crate::{
        chain::{ChainNoGenArena, LinkNoGen, chain_no_gen_iterators},
        fundamental::{PtrGen, PtrInx, PtrNoGen},
    };
    /// A reexport used by the macros
    #[cfg(feature = "serde_support")]
    pub mod serde {
        pub use serde::{Deserialize, Deserializer, Serialize, Serializer};
    }

    #[cfg(feature = "alloc")]
    pub use crate::arena::{HeapBacking, LimitedHeapBacking};
    pub use crate::{
        arena::{ArenaBacking, StackBacking},
        fundamental::{
            AllocError, NonZeroInxGenericStack, NonZeroInxGenericStackFallible, SetMaxCapacity,
            ptrinx_unchecked,
        },
    };
}

/// All the main traits, this can be glob imported
pub mod traits {
    pub use recasting::{Recast, Recaster};

    pub use crate::fundamental::{Advancer, ArenaTrait, Ptr,ArenaTraitFallible};
}
