mod advancer;
// FIXME delete
mod nz_inx_backing;
mod old_arena_trait;
#[cfg(not(feature = "serde_support"))]
mod ptr;
#[cfg(feature = "serde_support")]
mod ptr_serde;
#[cfg(feature = "serde_support")]
pub mod serde;

pub use advancer::Advancer;
pub use old_arena_trait::ArenaTrait;
#[cfg(not(feature = "serde_support"))]
pub use ptr::{Ptr, PtrGen, PtrInx, PtrNoGen, ptrinx_unchecked};
#[cfg(feature = "serde_support")]
pub use ptr_serde::{Ptr, PtrGen, PtrInx, PtrNoGen, ptrinx_unchecked};
