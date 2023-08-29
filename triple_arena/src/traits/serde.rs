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

#![allow(clippy::type_complexity)]

use alloc::fmt;
use core::{marker::PhantomData, num::NonZeroUsize};

use serde::{
    de::{Error, MapAccess, Visitor},
    ser::{SerializeMap, SerializeTuple},
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::{
    arena::InternalEntry,
    ord::Node,
    surject::{Key, Val},
    utils::{ChainNoGenArena, LinkNoGen, PtrGen, PtrInx, PtrNoGen},
    Arena, ChainArena, Link, OrdArena, Ptr, SurjectArena,
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

impl<P: Ptr, T: Serialize> Serialize for Link<P, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_tuple(3)?;
        s.serialize_element(&self.prev())?;
        s.serialize_element(&self.next())?;
        s.serialize_element(&self.t)?;
        s.end()
    }
}

impl<P: Ptr, T: Serialize> Serialize for ChainArena<P, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.a.serialize(serializer)
    }
}

impl<P: Ptr, T: Serialize> Serialize for LinkNoGen<P, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_tuple(3)?;
        s.serialize_element(&self.prev())?;
        s.serialize_element(&self.next())?;
        s.serialize_element(&self.t)?;
        s.end()
    }
}

impl<P: Ptr, T: Serialize> Serialize for ChainNoGenArena<P, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.a.serialize(serializer)
    }
}

impl<P: Ptr, K: Serialize> Serialize for Key<P, K> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_tuple(2)?;
        s.serialize_element(&self.k)?;
        s.serialize_element(&self.p_val)?;
        s.end()
    }
}

impl<V: Serialize> Serialize for Val<V> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_tuple(2)?;
        s.serialize_element(&self.v)?;
        s.serialize_element(&self.key_count)?;
        s.end()
    }
}

impl<P: Ptr, K: Serialize, V: Serialize> Serialize for SurjectArena<P, K, V> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_tuple(2)?;
        s.serialize_element(&self.keys)?;
        s.serialize_element(&self.vals)?;
        s.end()
    }
}

impl<P: Ptr, K: Serialize, V: Serialize> Serialize for OrdArena<P, K, V> {
    /// The `OrdArena` must be compressed or else an error will be returned (use
    /// one of the `compress_and_shrink_*` functions).
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_map(Some(self.len()))?;
        let mut last = None;
        for (p, k, v) in self {
            let err = if let Some(last) = last {
                PtrInx::get(last).get().saturating_add(1) != PtrInx::get(p.inx()).get()
            } else {
                PtrInx::get(p.inx()).get() != 1
            };
            if err {
                return Err(serde::ser::Error::custom(
                    "Tried to serialize an uncompressed `OrdArena` (use one of the \
                     `compress_and_shrink_*` functions)",
                ))
            }
            s.serialize_entry(k, v)?;
            last = Some(p.inx());
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
    /// This function returns an error in case of duplicate `Ptr` keys
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(ArenaVisitor(PhantomData))
    }
}

impl<'de, P: Ptr, T> Deserialize<'de> for Link<P, T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (prev, next, t): (Option<P>, Option<P>, T) = Deserialize::deserialize(deserializer)?;
        Ok(Link::new((prev, next), t))
    }
}

impl<'de, P: Ptr, T> Deserialize<'de> for ChainArena<P, T>
where
    T: Deserialize<'de>,
{
    /// This function returns an error in case of a broken interlink structure
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let a: Arena<P, Link<P, T>> = Deserialize::deserialize(deserializer)?;
        match ChainArena::from_arena(a) {
            Ok(res) => Ok(res),
            Err(e) => Err(Error::custom(e)),
        }
    }
}

impl<'de, P: Ptr, T> Deserialize<'de> for LinkNoGen<P, T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (prev, next, t): (Option<P::Inx>, Option<P::Inx>, T) =
            Deserialize::deserialize(deserializer)?;
        Ok(LinkNoGen::new((prev, next), t))
    }
}

impl<'de, P: Ptr, T> Deserialize<'de> for ChainNoGenArena<P, T>
where
    T: Deserialize<'de>,
{
    /// This function returns an error in case of a broken interlink structure
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let a: Arena<P, LinkNoGen<P, T>> = Deserialize::deserialize(deserializer)?;
        match ChainNoGenArena::from_arena(a) {
            Ok(res) => Ok(res),
            Err(e) => Err(Error::custom(e)),
        }
    }
}

impl<'de, P: Ptr, K> Deserialize<'de> for Key<P, K>
where
    K: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (k, p_val): (K, PtrNoGen<P>) = Deserialize::deserialize(deserializer)?;
        Ok(Key { k, p_val })
    }
}

impl<'de, V> Deserialize<'de> for Val<V>
where
    V: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (v, key_count): (V, NonZeroUsize) = Deserialize::deserialize(deserializer)?;
        Ok(Val { v, key_count })
    }
}

impl<'de, P: Ptr, K, V> Deserialize<'de> for SurjectArena<P, K, V>
where
    K: Deserialize<'de>,
    V: Deserialize<'de>,
{
    /// This function returns an error in case of a broken surject structure
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (keys, vals): (ChainNoGenArena<P, Key<P, K>>, Arena<PtrNoGen<P>, Val<V>>) =
            Deserialize::deserialize(deserializer)?;
        let res = SurjectArena { keys, vals };
        if let Err(e) = SurjectArena::_check_surjects(&res) {
            Err(Error::custom(e))
        } else {
            Ok(res)
        }
    }
}

struct OrdArenaVisitor<P: Ptr, K, V>(PhantomData<fn() -> (P, K, V)>);

impl<'de, P: Ptr, K, V> Visitor<'de> for OrdArenaVisitor<P, K, V>
where
    K: Deserialize<'de>,
    V: Deserialize<'de>,
{
    type Value = OrdArena<P, K, V>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a `triple_arena` arena")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'de>,
    {
        let mut a: Arena<P, LinkNoGen<P, Node<P, K, V>>> = Arena::new();
        if let Some(hint) = access.size_hint() {
            a.m.reserve(hint);
        }

        let mut i = 1usize;
        let mut last = None;
        while let Some((k, v)) = access.next_entry::<K, V>()? {
            let p = PtrInx::new(NonZeroUsize::new(i).unwrap());
            if let Some(last) = last {
                a.get_inx_mut_unwrap(last).prev_next.1 = Some(p);
            }
            let t = LinkNoGen::new((last, None), Node {
                k,
                v,
                p_back: None,
                p_tree0: None,
                p_tree1: None,
                rank: 0,
            });
            a.m.push(InternalEntry::Allocated(PtrGen::two(), t));
            i = i.wrapping_add(1);
            last = Some(p);
        }

        a.freelist_root = None;
        a.len = a.m.len();

        let a = ChainNoGenArena { a };
        let tmp = P::invalid().inx();
        let mut res = OrdArena {
            a,
            root: tmp,
            first: tmp,
            last: tmp,
        };
        res.raw_rebalance_assuming_compressed();
        Ok(res)
    }
}

impl<'de, P: Ptr, K, V> Deserialize<'de> for OrdArena<P, K, V>
where
    K: Deserialize<'de>,
    V: Deserialize<'de>,
{
    /// This does not check the ordering of keys.
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(OrdArenaVisitor(PhantomData))
    }
}
