/// This should be implemented for an item that has a stable ordering with
/// respect to [SimpleOrdItem::key]. Unlike [OrdPair] and [OrdArena] which
/// implicitly require keys and values to be separate structs, the item
/// implementing this can project part of its internal structure as the key.
pub trait SimpleOrdItem {
    type Key<'a>: Ord
    where
        Self: 'a;

    /// Returns the key
    fn key(&self) -> Self::Key<'_>;
}

/// An implementor of [SimpleOrdItem] that has a key `K: Ord` and associated
/// value `V`. `&K` is used as the key.
pub struct OrdPair<K, V> {
    pub k: K,
    pub v: V,
}

impl<K: Ord, V> SimpleOrdItem for OrdPair<K, V> {
    type Key<'a>
        = &'a K
    where
        Self: 'a;

    fn key(&self) -> Self::Key<'_> {
        &self.k
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

    pub fn k_mut(&mut self) -> &mut K {
        &mut self.k
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

    pub fn k_v_mut(&mut self) -> (&mut K, &mut V) {
        (&mut self.k, &mut self.v)
    }

    pub fn into_k_v(self) -> (K, V) {
        (self.k, self.v)
    }
}

// TODO future OrdArena-specific trait goes here
