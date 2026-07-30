pub mod arena_iterators;
mod arena_traits;
mod base_arena;
mod impl_arena_trait;

pub(crate) use arena_traits::handle_reallocation;
pub use arena_traits::{
    ArenaCloneFromWith, ArenaDirectInsertTrait, ArenaInsertEntryTrait, ArenaInsertTrait,
    ArenaTrait, SingularGenerationArena,
};
pub use base_arena::{Arena, InternalSlot};
pub(crate) use base_arena::{from_checked_ptr, from_checked_raw};
pub use impl_arena_trait::ArenaInsertEntry;
