mod advancer;
pub mod errors;
mod extra;
#[cfg(not(feature = "serde_support"))]
mod ptr;
#[cfg(feature = "serde_support")]
mod ptr_serde;
#[cfg(feature = "serde_support")]
pub mod serde;
#[cfg(feature = "serde_support")]
pub mod serde_docs;

pub use advancer::Advancer;
pub use extra::{IntoNonZeroUsizeIterator, InvalidationOption, InvalidationResult, nzusize_iter};
#[cfg(not(feature = "serde_support"))]
pub use ptr::{Ptr, PtrGen, PtrInx, PtrNoGen};
#[cfg(feature = "serde_support")]
pub use ptr_serde::{Ptr, PtrGen, PtrInx, PtrNoGen};
