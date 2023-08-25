//! Documentation on the serialization of arenas
//!
//! Serialization drops generation counters and deserialization sets them to
//! 2. It is highly recommended to run [Arena::compress_and_shrink] or
//! [Arena::compress_and_shrink_recaster] and use the [recasting::Recast]
//! trait before serializing the arena, or else excess capacity may be
//! forced upon the deserializer.
//!
//! ```
//! // Example using the `ron` crate
//! use ron::{from_str, to_string};
//! use triple_arena::{ptr_struct, Arena, Recast, Recaster};
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

use alloc::fmt;
use core::{marker::PhantomData, num::NonZeroUsize};

use serde::{
    de::{Error, MapAccess, Visitor},
    ser::SerializeMap,
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::{
    arena::InternalEntry,
    utils::{PtrGen, PtrInx},
    Arena, Ptr,
};

impl<P: Ptr, T: Serialize> Serialize for Arena<P, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_map(Some(self.len()))?;
        for (p, t) in self {
            s.serialize_entry(&p.inx(), t)?;
        }
        s.end()
    }
}

struct ArenaVisitor<P: Ptr, T>(PhantomData<fn() -> (P, T)>);

impl<'de, P: Ptr, T> Visitor<'de> for ArenaVisitor<P, T>
where
    T: Deserialize<'de>,
{
    type Value = Arena<P, T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a `triple_arena` arena")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'de>,
    {
        let mut a = Arena::new();
        if let Some(hint) = access.size_hint() {
            a.m.reserve(hint);
        }

        while let Some((p, t)) = access.next_entry::<P::Inx, T>()? {
            let i = PtrInx::get(p).get();
            if i > a.capacity() {
                for _ in 0..(i.wrapping_sub(a.capacity())) {
                    a.m.push(InternalEntry::Free(PtrInx::new(
                        NonZeroUsize::new(1).unwrap(),
                    )))
                }
            }
            let entry = a.m_get_mut(p).unwrap();
            match entry {
                InternalEntry::Free(_) => {
                    entry.replace_free_with_allocated(PtrGen::two(), t).unwrap();
                    let len = a.len;
                    a.len = len.wrapping_add(1);
                }
                InternalEntry::Allocated(..) => {
                    return Err(Error::custom(
                        "when deserializing a `triple_arena` arena, encountered duplicate pointer \
                         index keys",
                    ))
                }
            }
        }

        // fix the freelist
        let mut last_free = None;
        for i in a.m.nziter() {
            if let InternalEntry::Free(p) = a.m_get_mut(PtrInx::new(i)).unwrap() {
                if let Some(ref mut last_free) = last_free {
                    *p = PtrInx::new(*last_free);
                    *last_free = i;
                } else {
                    // points to itself
                    *p = PtrInx::new(i);
                    last_free = Some(i);
                }
            }
        }
        if let Some(last_free) = last_free {
            a.freelist_root = Some(PtrInx::new(last_free));
        } else {
            a.freelist_root = None;
        }

        Ok(a)
    }
}

impl<'de, P: Ptr, T> Deserialize<'de> for Arena<P, T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(ArenaVisitor(PhantomData))
    }
}