#![allow(clippy::type_complexity)]
#![allow(clippy::new_without_default)]
#![allow(clippy::too_many_arguments)]

pub mod basic_arena;
pub mod cdgen;
pub mod chain_arena;
pub mod direct_arena;
pub mod misc;
pub mod nonzero_inx_generic_stack;
// TODO cleanup
pub mod old_helpers;
mod ptrs;
pub mod simple_ord_arena;
pub mod surject_arena;

pub use old_helpers::*;
pub use ptrs::*;
