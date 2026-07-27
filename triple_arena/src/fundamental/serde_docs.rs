//! It is rarely a good idea to directly serialize an arena (and in fact we
//! deliberately do not implement serialization on the arena types even though
//! we implement serialization for some things like `Ptr`s). The proper way to
//! serialize a `triple_arena` arena-like structure is different depending on
//! the problem, and in each case the user should use advancers or iterators and
//! helper structs as intermediates in serialization. There are a few different
//! things that should be considered:
//!
//! - Whether compression and recasting should be used (highly preferred)
//!
//! In many cases, you should be using [Recast] and [ArenaTrait::]
//!
//! There are about 3 cases. First, you will often want to avoid directly
//! serializing arenas in the first case, because any
//! In many cases, you will first want to use
//! Serialization drops generation counters and deserialization sets them to
//! 2. It is highly recommended to run [Arena::compress_and_shrink] or
//! [Arena::compress_and_shrink_recaster] and use the [recasting::Recast]
//! trait before serializing the arena, or else excess capacity may be
//! forced upon the deserializer.
//!
//! Note that `OrdArena` requires that it is compressed before being serialized.
