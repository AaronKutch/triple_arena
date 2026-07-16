#![allow(clippy::type_complexity)]

use core::{fmt, marker::PhantomData, num::NonZeroUsize};

use serde::{
    Deserialize, Deserializer, Serialize, Serializer,
    de::{Error, MapAccess, Visitor},
    ser::{SerializeMap, SerializeTuple},
};

use crate::{
    Arena, ChainArena, Link, OrdArena, SurjectArena,
    arena::InternalSlot,
    ord::Node,
    surject::{Key, Val},
    traits::Ptr,
    utils::{
        ArenaBacking, ChainNoGenArena, LinkNoGen, NonZeroInxGenericStack, PtrGen, PtrInx, PtrNoGen,
    },
};

impl<P: Ptr, T: Serialize, B: ArenaBacking> Serialize for Arena<P, T, B> {
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

impl<P: Ptr, T: Serialize, B: ArenaBacking> Serialize for ChainArena<P, T, B> {
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

impl<P: Ptr, T: Serialize, B: ArenaBacking> Serialize for ChainNoGenArena<P, T, B> {
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

impl<P: Ptr, K: Serialize, V: Serialize, B: ArenaBacking> Serialize for SurjectArena<P, K, V, B> {
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

impl<P: Ptr, K: Serialize, V: Serialize, B: ArenaBacking> Serialize for OrdArena<P, K, V, B> {
    /// The `OrdArena` must be compressed or else an error will be returned (use
    /// one of the `compress_and_shrink_*` functions).
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_map(Some(self.len()))?;
        let mut last = None;
        for (p, k, v) in self {
            // FIXME
            let err = if let Some(last) = last {
                PtrInx::try_into_usize(last)
                    .unwrap()
                    .get()
                    .saturating_add(1)
                    != PtrInx::try_into_usize(p.inx()).unwrap().get()
            } else {
                PtrInx::try_into_usize(p.inx()).unwrap().get() != 1
            };
            if err {
                return Err(serde::ser::Error::custom(
                    "Tried to serialize an uncompressed `OrdArena` (use one of the \
                     `compress_and_shrink_*` functions)",
                ));
            }
            s.serialize_entry(k, v)?;
            last = Some(p.inx());
        }
        s.end()
    }
}

struct ArenaVisitor<P: Ptr, T, B: ArenaBacking>(PhantomData<fn() -> (P, T, B)>);

impl<'de, P: Ptr, T, B: ArenaBacking> Visitor<'de> for ArenaVisitor<P, T, B>
where
    T: Deserialize<'de>,
{
    type Value = Arena<P, T, B>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a `triple_arena` arena")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'de>,
    {
        let mut a = Arena::<P, T, B>::new();
        if let Some(hint) = access.size_hint() {
            let _ = a.m.reallocate_min_capacity(hint);
        }

        while let Some((p, t)) = access.next_entry::<P::Inx, T>()? {
            let i = PtrInx::try_into_usize(p).unwrap().get();
            if i > a.capacity() {
                for _ in 0..(i.wrapping_sub(a.capacity())) {
                    // the freelist is fixed later

                    // FIXME
                    a.m.push_reallocating(InternalSlot::Free(
                        PtrInx::try_from_usize(NonZeroUsize::new(1).unwrap()).unwrap(),
                    ))
                    .map_err(|_| {
                        Error::custom(
                            "when deserializing a `triple_arena` arena, ran into allocation error",
                        )
                    })?;
                }
            }
            let entry = a.m_get_mut(p).unwrap();
            match entry {
                InternalSlot::Free(_) => {
                    entry.replace_free_with_allocated(PtrGen::two(), t).unwrap();
                    let len = a.len;
                    a.len = len.wrapping_add(1);
                }
                InternalSlot::Allocated(..) => {
                    return Err(Error::custom(
                        "when deserializing a `triple_arena` arena, encountered duplicate pointer \
                         index keys",
                    ));
                }
            }
        }

        // fix the freelist
        let mut last_free = None;
        for i in a.nziter() {
            // FIXME
            if let InternalSlot::Free(p) = a.m_get_mut(PtrInx::try_from_usize(i).unwrap()).unwrap()
            {
                if let Some(ref mut last_free) = last_free {
                    *p = PtrInx::try_from_usize(*last_free).unwrap();
                    *last_free = i;
                } else {
                    // points to itself
                    *p = PtrInx::try_from_usize(i).unwrap();
                    last_free = Some(i);
                }
            }
        }
        if let Some(last_free) = last_free {
            // FIXME
            a.freelist_root = Some(PtrInx::try_from_usize(last_free).unwrap());
        } else {
            a.freelist_root = None;
        }

        Ok(a)
    }
}

impl<'de, P: Ptr, T, B: ArenaBacking> Deserialize<'de> for Arena<P, T, B>
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

impl<'de, P: Ptr, T, B: ArenaBacking> Deserialize<'de> for ChainArena<P, T, B>
where
    T: Deserialize<'de>,
{
    /// This function returns an error in case of a broken interlink structure
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let a: Arena<P, Link<P, T>, B> = Deserialize::deserialize(deserializer)?;
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

impl<'de, P: Ptr, T, B: ArenaBacking> Deserialize<'de> for ChainNoGenArena<P, T, B>
where
    T: Deserialize<'de>,
{
    /// This function returns an error in case of a broken interlink structure
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let a: Arena<P, LinkNoGen<P, T>, B> = Deserialize::deserialize(deserializer)?;
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

impl<'de, P: Ptr, K, V, B: ArenaBacking> Deserialize<'de> for SurjectArena<P, K, V, B>
where
    K: Deserialize<'de>,
    V: Deserialize<'de>,
{
    /// This function returns an error in case of a broken surject structure
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (keys, vals): (
            ChainNoGenArena<P, Key<P, K>, B>,
            Arena<PtrNoGen<P>, Val<V>, B>,
        ) = Deserialize::deserialize(deserializer)?;
        let res = SurjectArena { keys, vals };
        if let Err(e) = SurjectArena::_check_surjects(&res) {
            Err(Error::custom(e))
        } else {
            Ok(res)
        }
    }
}

struct OrdArenaVisitor<P: Ptr, K, V, B: ArenaBacking>(PhantomData<fn() -> (P, K, V, B)>);

impl<'de, P: Ptr, K, V, B: ArenaBacking> Visitor<'de> for OrdArenaVisitor<P, K, V, B>
where
    K: Deserialize<'de>,
    V: Deserialize<'de>,
{
    type Value = OrdArena<P, K, V, B>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a `triple_arena` arena")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'de>,
    {
        let mut a: Arena<P, LinkNoGen<P, Node<P, K, V>>, B> = Arena::new();
        if let Some(hint) = access.size_hint() {
            let _ = a.m.reallocate_min_capacity(hint);
        }

        let mut i = 1usize;
        let mut last = None;
        while let Some((k, v)) = access.next_entry::<K, V>()? {
            // FIXME
            let p = PtrInx::try_from_usize(NonZeroUsize::new(i).unwrap()).unwrap();
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
            a.m.push_reallocating(InternalSlot::Allocated(PtrGen::two(), t))
                .map_err(|_| {
                    Error::custom(
                        "when deserializing a `triple_arena` arena, ran into allocation error",
                    )
                })?;
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

impl<'de, P: Ptr, K, V, B: ArenaBacking> Deserialize<'de> for OrdArena<P, K, V, B>
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
