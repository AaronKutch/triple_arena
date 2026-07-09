//! Note: there are "std" and "serde_support" feature flags

#![no_std]
#![allow(clippy::type_complexity)]

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
// always keep this for the serde documentation
#[cfg(feature = "serde_support")]
pub use fundamental::serde_docs;
pub use ord::{OrdArena, ord_iterators};
pub use surject::{SurjectArena, surject_iterators};

/// Special utilities for advanced usage
pub mod utils {
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::arena::{InternalEntry, NonZeroInxArray, NonZeroInxLimitedVec, NonZeroInxVec};
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

    pub use crate::{
        arena::{ArenaBacking, HeapBacking, LimitedHeapBacking, StackBacking},
        fundamental::{
            AllocError, NonZeroInxGenericStack, SettableCapacityLimit, ptrinx_unchecked,
        },
    };
}

/// All the main traits, this can be glob imported
pub mod traits {
    pub use recasting::{Recast, Recaster};

    pub use crate::fundamental::{Advancer, Ptr};
}
