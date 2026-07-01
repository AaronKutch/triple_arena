//! Documentation on the serialization of arenas
//!
//! Serialization drops generation counters and deserialization sets them to
//! 2. It is highly recommended to run [Arena::compress_and_shrink] or
//! [Arena::compress_and_shrink_recaster] and use the [recasting::Recast]
//! trait before serializing the arena, or else excess capacity may be
//! forced upon the deserializer.
//!
//! Note that `OrdArena` requires that it is compressed before being serialized.
//!
//! ```
//! // Example using the `ron` crate
//! use ron::{from_str, to_string};
//! use triple_arena::{Arena, Recast, Recaster, ptr_struct};
//!
//! ptr_struct!(P0);
//!
//! type Example = Arena<P0, (u64, Option<P0>)>;
//!
//! impl Recast<P0> for (u64, Option<P0>) {
//!     fn recast<R: Recaster<Item = P0>>(
//!         &mut self,
//!         recaster: &R,
//!     ) -> Result<(), <R as Recaster>::Item> {
//!         self.1.recast(recaster)?;
//!         Ok(())
//!     }
//! }
//!
//! let mut a: Example = Arena::new();
//!
//! // stimulating a generation increase
//! a.clear();
//! let p0 = a.insert((0, None));
//! let p42 = a.insert((42, None));
//! let p1 = a.insert((1, None));
//! a.insert((1337, Some(p42)));
//! // make some internal arena entries unallocated
//! a.remove(p0).unwrap();
//! a.remove(p1).unwrap();
//!
//! assert_eq!(
//!     &format!("{a:?}"),
//!     "{P0[2](3): (42, None), P0[4](3): (1337, Some(P0[2](3)))}"
//! );
//!
//! let serialized = to_string(&a).unwrap();
//! assert_eq!(serialized, "{2:(42,None),4:(1337,Some(2))}");
//!
//! let mut a: Example = from_str(&serialized).unwrap();
//! // note how everything is the same except that all `Ptr`s have
//! // had their generations set to an initial 2 (because the
//! // generation is dropped for the serialized form)
//! assert_eq!(
//!     &format!("{a:?}"),
//!     "{P0[2](2): (42, None), P0[4](2): (1337, Some(P0[2](2)))}"
//! );
//!
//! // However, there is one big problem that users should be aware of.
//! // If there is unused capacity that consists of `Ptr` indexes less
//! // than the largest existing index (in this case `P0[1]` and `P0[2]`
//! // are not allocated entries in the arena), then that capacity is
//! // forced to be inherited by the deserialized arena. If the `Arena`
//! // is part of some long lived state that gets repeatedly serialized
//! // to a file and then read back and deserialized, it may retain the
//! // largest capacity it has had forever, regardless of `a.len()`.
//! assert_eq!(a.len(), 2);
//! assert!(a.capacity() >= 4);
//!
//! // This is what the `Recast` trait is for. We call this before
//! // serialization. This fixes both the indexes of the `Ptr` keys
//! // and the indexes inside the values of the arena, so that
//! // relations are preserved.
//! let recaster = a.compress_and_shrink_recaster();
//! a.recast(&recaster).unwrap();
//!
//! assert_eq!(
//!     &format!("{a:?}"),
//!     "{P0[1](3): (42, None), P0[2](3): (1337, Some(P0[1](3)))}"
//! );
//! let serialized = to_string(&a).unwrap();
//! assert_eq!(serialized, "{1:(42,None),2:(1337,Some(1))}");
//! let mut a: Example = from_str(&serialized).unwrap();
//! assert_eq!(
//!     &format!("{a:?}"),
//!     "{P0[1](2): (42, None), P0[2](2): (1337, Some(P0[1](2)))}"
//! );
//! assert!(a.capacity() >= 2);
//! ```
