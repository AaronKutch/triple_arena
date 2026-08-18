//! Documentation on arenas and serialization.
//!
//! It is rarely a good idea to directly serialize an arena (and in fact we
//! deliberately do not implement serialization on the arena types, even though
//! we implement serialization for building blocks like `Ptr`s and
//! `LinkNoGen`s). The proper way to serialize a `triple_arena` arena-like
//! structure, in practice, has to be completely tailored to each use case, and
//! the user should use advancers or iterators and helper structs as
//! intermediates in serialization. There are a few different things that should
//! be considered:
//!
//! - Whether compression and recasting should be used (highly preferred, note
//!   that `reset_generation` options should be set when possible, see the
//!   example on [compress_with](crate::traits::ArenaTrait::compress_with)).
//!   Note for the more complex arenas, however, that the in-place compress
//!   functions without maps (needed to build a recaster) cannot fully
//!   canonicalize the arena (which is favorable for better cache locality). The
//!   _canonical_ transfer functions like
//!   [transfer_canonical_reallocating](crate::ChainArena::transfer_canonical_reallocating)
//!   (see the example there) should be used instead.
//! - If [ArenaDirectInsertTrait](crate::traits::ArenaDirectInsertTrait)-based
//!   arenas should be used
//! - If generation counters should be omitted
//! - If indexes can be implicit. After compression on a simple arena, the
//!   entries have no gaps between them, and the entries could be simply read
//!   out in a simple list. Then when deserializing, they can be inserted in
//!   order and will pick up the correct indexes (again, at least in simple
//!   arenas).

// TODO more examples
