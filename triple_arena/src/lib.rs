#![no_std]
// false positives
#![allow(clippy::while_let_on_iterator)]
#![allow(clippy::comparison_chain)]

// TODO all places where we have an internal .get_..().unwrap() need to have
// .get_inx_unwrap() (removes both the return and generation input wastage) do
// this after OrdArena is settled
// check all `get_inx_mut_unwrap` to see if we can replace with the _t variant

mod arena;
pub use arena::arena_iterators;
mod chain;
mod ord;
mod traits;
pub use chain::{ChainArena, Link};
pub use traits::{Advancer, ArenaTrait, Ptr};
mod surject;
// reexport for the macros to use
pub use arena::Arena;
pub use chain::chain_iterators;
pub use ord::{ord_iterators, OrdArena};
pub use recasting::{Recast, Recaster};
pub use surject::{surject_iterators, SurjectArena};
/// Special utilities for advanced usage
pub mod utils {
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::arena::InternalEntry;
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::arena::NonZeroInxVec;
    #[cfg(not(feature = "expose_internal_utils"))]
    pub(crate) use crate::nonzero_inx_vec::NonZeroInxVec;
    // only intended for size_of tests and such
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::ord::Node;
    pub use crate::traits::{PtrGen, PtrInx, PtrNoGen};
    pub(crate) use crate::{arena::nzusize_unchecked, traits::ptrinx_unchecked};
}

extern crate alloc;
