//! Note: there are "std" and "serde_support" feature flags

#![no_std]

mod arena;
pub use arena::arena_iterators;
mod chain;
mod ord;
mod traits;
pub use chain::{ChainArena, Link, chain_iterators};
// always keep this for the serde documentation
#[cfg(feature = "serde_support")]
pub use traits::serde;
pub use traits::{Advancer, ArenaTrait, Ptr};
mod surject;
// reexport for the macros to use
pub use arena::Arena;
pub use ord::{OrdArena, ord_iterators};
pub use recasting::{Recast, Recaster};
pub use surject::{SurjectArena, surject_iterators};
/// Special utilities for advanced usage
pub mod utils {
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::arena::InternalEntry;
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::arena::NonZeroInxVec;
    #[cfg(not(feature = "expose_internal_utils"))]
    pub(crate) use crate::arena::NonZeroInxVec;
    // only intended for size_of tests and such
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::ord::Node;
    pub(crate) use crate::traits::ptrinx_unchecked;
    pub use crate::{
        chain::{ChainNoGenArena, LinkNoGen, chain_no_gen_iterators},
        traits::{PtrGen, PtrInx, PtrNoGen},
    };
    /// A reexport used by the macros
    #[cfg(feature = "serde_support")]
    pub mod serde {
        pub use serde::{Deserialize, Deserializer, Serialize, Serializer};
    }
}

extern crate alloc;
