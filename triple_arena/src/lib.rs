#![no_std]
// because `Ptr` is based on user-controlled code we will not use unsafe code
// for the foreseeable future
#![deny(unsafe_code)]
// false positives
#![allow(clippy::while_let_on_iterator)]

// TODO all places where we have an internal .get_..().unwrap() need to have
// .get_inx_unwrap() (removes both the return and generation input wastage) do
// this after OrdArena is settled
// check all `get_inx_mut_unwrap` to see if we can replace with the _t variant

mod arena;
mod chain;
mod entry;
pub mod iterators;
mod ord;
mod ptr;
pub use chain::{ChainArena, Link};
pub(crate) use entry::InternalEntry;
pub use ptr::{Ptr, PtrGen, PtrInx, PtrNoGen};
mod surject;
pub use surject::SurjectArena;
pub mod chain_iterators;
pub mod surject_iterators;
pub use ord::OrdArena;
pub mod ord_iterators;
pub use arena::Arena;

extern crate alloc;
