#![no_std]
// false positives
#![allow(clippy::while_let_on_iterator)]

// TODO all places where we have an internal .get_..().unwrap() need to have
// .get_inx_unwrap() (removes both the return and generation input wastage) do
// this after OrdArena is settled
// check all `get_inx_mut_unwrap` to see if we can replace with the _t variant

mod advancer;
mod arena;
mod arena_trait;
mod chain;
pub mod iterators;
mod nonzero_inx_vec;
mod ord_arena;
mod ptr;
pub use advancer::Advancer;
pub use arena_trait::ArenaTrait;
pub use chain::{ChainArena, Link};
pub use ptr::Ptr;
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
    pub(crate) use crate::nonzero_inx_vec::{nzusize_unchecked, NonZeroInxVec};
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::nonzero_inx_vec::{nzusize_unchecked, NonZeroInxVec};
    // only intended for size_of tests and such
    #[cfg(feature = "expose_internal_utils")]
    pub use crate::ord_arena::Node;
    pub use crate::ptr::{ptrinx_unchecked, PtrGen, PtrInx, PtrNoGen};
}

extern crate alloc;
