mod advancer;
mod arena_trait;
#[cfg(not(feature = "serde_support"))]
mod ptr;
#[cfg(feature = "serde_support")]
mod ptr_serde;
#[cfg(feature = "serde_support")]
pub mod serde;

pub use advancer::Advancer;
pub use arena_trait::ArenaTrait;
#[cfg(not(feature = "serde_support"))]
pub use ptr::{ptrinx_unchecked, Ptr, PtrGen, PtrInx, PtrNoGen};
#[cfg(feature = "serde_support")]
pub use ptr_serde::{ptrinx_unchecked, Ptr, PtrGen, PtrInx, PtrNoGen};
