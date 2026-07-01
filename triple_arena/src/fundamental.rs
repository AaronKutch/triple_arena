mod advancer;
mod extra;
mod nonzero_inx_generic_stack;
// FIXME delete
mod old_arena_trait;
#[cfg(not(feature = "serde_support"))]
mod ptr;
#[cfg(feature = "serde_support")]
mod ptr_serde;
#[cfg(feature = "serde_support")]
pub mod serde;
#[cfg(feature = "serde_support")]
pub mod serde_docs;

pub use advancer::Advancer;
pub use extra::{AllocError, GetDisjointMutError, ptrinx_unchecked};
pub use nonzero_inx_generic_stack::NonZeroInxGenericStack;
pub use old_arena_trait::ArenaTrait;
#[cfg(not(feature = "serde_support"))]
pub use ptr::{Ptr, PtrGen, PtrInx, PtrNoGen};
#[cfg(feature = "serde_support")]
pub use ptr_serde::{Ptr, PtrGen, PtrInx, PtrNoGen};
