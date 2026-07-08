mod advancer;
mod extra;
mod nonzero_inx_generic_stack;
#[cfg(not(feature = "serde_support"))]
mod ptr;
#[cfg(feature = "serde_support")]
mod ptr_serde;
#[cfg(feature = "serde_support")]
pub mod serde;
#[cfg(feature = "serde_support")]
pub mod serde_docs;

pub use advancer::Advancer;
pub use extra::{AllocError, IntoNonZeroUsizeIterator, nzusize_iter, ptrinx_unchecked};
pub use nonzero_inx_generic_stack::NonZeroInxGenericStack;
#[cfg(not(feature = "serde_support"))]
pub use ptr::{Ptr, PtrGen, PtrInx, PtrNoGen};
#[cfg(feature = "serde_support")]
pub use ptr_serde::{Ptr, PtrGen, PtrInx, PtrNoGen};
