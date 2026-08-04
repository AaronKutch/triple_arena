use core::fmt;

use recasting::{Recast, Recaster};

/// This should be implemented for an item that has a stable ordering with
/// respect to [SimpleOrdItem::key]. Unlike [OrdPair] and the future `OrdArena`
/// which implicitly require keys and values to be separate structs, the item
/// implementing this can project part of its internal structure as the key.
pub trait SimpleOrdItem {
    type Key<'a>: Ord
    where
        Self: 'a;

    /// Returns the key
    fn key(&self) -> Self::Key<'_>;

    /// Shortens the lifetime of a key. Any sensible `Key` is covariant over
    /// its lifetime, but the compiler treats generic associated types as
    /// invariant, so this witness is needed in order to use a long lived key
    /// within a shorter borrow of the arena. Implementations should just have
    /// the body `{ k }`.
    fn shorten_key<'long: 'short, 'short>(k: Self::Key<'long>) -> Self::Key<'short>
    where
        Self: 'long;
}

// We almost implemented this for all `T: Ord`, but blanket impls have a bad
// habit of causing conflicts and will probably mess with type checking
// protection in this case. Also `OrdPair<K, ()>` or an explicit equivalent is
// desired to prevent changing the key accidentally. It is easy to implement
// this for single structs if they are intended as keys.

/// An implementor of [SimpleOrdItem] that has a key `K: Ord` and associated
/// value `V`. `&K` is used as the key. Note that this does not provide a
/// `k_mut` function in order to guard against accidentally modifying the key of
/// an &mut OrdPair<...> reference from a [SimpleOrdArena].
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct OrdPair<K, V> {
    k: K,
    v: V,
}

impl<K: Ord, V> SimpleOrdItem for OrdPair<K, V> {
    type Key<'a>
        = &'a K
    where
        Self: 'a;

    fn key(&self) -> Self::Key<'_> {
        &self.k
    }

    fn shorten_key<'long: 'short, 'short>(k: Self::Key<'long>) -> Self::Key<'short>
    where
        Self: 'long,
    {
        k
    }
}

impl<K: Ord + fmt::Debug, V: fmt::Debug> fmt::Debug for OrdPair<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("").field(self.k()).field(self.v()).finish()
    }
}

impl<K, V> OrdPair<K, V> {
    /// Creates a new `OrdPair` from the key `k` and value `v`
    pub fn new(k: K, v: V) -> Self {
        Self { k, v }
    }

    pub fn k(&self) -> &K {
        &self.k
    }

    pub fn v(&self) -> &V {
        &self.v
    }

    pub fn v_mut(&mut self) -> &mut V {
        &mut self.v
    }

    pub fn k_v(&self) -> (&K, &V) {
        (&self.k, &self.v)
    }

    pub fn k_v_mut(&mut self) -> (&K, &mut V) {
        (&self.k, &mut self.v)
    }

    pub fn into_k_v(self) -> (K, V) {
        (self.k, self.v)
    }
}

/// Recasts only the `V`
impl<K, I, V: Recast<I>> Recast<I> for OrdPair<K, V> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        self.v_mut().recast(recaster)?;
        Ok(())
    }
}

// TODO future OrdArena-specific trait goes here
