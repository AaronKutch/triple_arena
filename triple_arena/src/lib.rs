#![no_std]
// false positives
#![allow(clippy::while_let_on_iterator)]

// TODO all places where we have an internal .get_..().unwrap() need to have
// .get_inx_unwrap() (removes both the return and generation input wastage) do
// this after OrdArena is settled
// check all `get_inx_mut_unwrap` to see if we can replace with the _t variant

mod arena;
pub mod arena_iterators;
mod arena_trait;
mod chain;
mod nonzero_inx_vec;
mod ord_arena;
mod traits;
pub use arena_trait::ArenaTrait;
pub use chain::{ChainArena, Link};
pub use traits::{Advancer, Ptr};
//mod safe_nonzero_inx_vec;
//use safe_nonzero_inx_vec as nonzero_inx_vec;
mod surject;
pub use surject::SurjectArena;
pub mod chain_iterators;
pub mod surject_iterators;
pub use arena::Arena;
pub use ord_arena::{ord_iterators, OrdArena};
/// Special utilities for advanced usage
pub mod utils {
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::arena::InternalEntry;
    #[cfg(not(feature = "expose_internal_utils"))]
    pub(crate) use crate::nonzero_inx_vec::NonZeroInxVec;
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::nonzero_inx_vec::NonZeroInxVec;
    // only intended for size_of tests and such
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::ord_arena::Node;
    pub use crate::traits::{PtrGen, PtrInx, PtrNoGen};
    pub(crate) use crate::{nonzero_inx_vec::nzusize_unchecked, traits::ptrinx_unchecked};
}

extern crate alloc;
