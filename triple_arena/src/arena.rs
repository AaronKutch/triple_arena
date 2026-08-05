pub mod arena_iterators;
mod arena_traits;
mod base_arena;
pub mod direct_arena_iterators;
mod direct_insertion_arena;
mod impl_arena_trait;
mod impl_direct_arena_trait;

pub(crate) use arena_traits::handle_reallocation;
pub use arena_traits::{
    ArenaCloneFromWith, ArenaDirectInsertEntryTrait, ArenaDirectInsertTrait, ArenaInsertEntryTrait,
    ArenaInsertTrait, ArenaTrait, SingularGenerationArena,
};
pub use base_arena::{Arena, ArenaSlot};
pub(crate) use base_arena::{from_checked_ptr, from_checked_raw};
pub use direct_insertion_arena::{DirectArena, DirectSlot};
pub use impl_arena_trait::ArenaInsertEntry;
