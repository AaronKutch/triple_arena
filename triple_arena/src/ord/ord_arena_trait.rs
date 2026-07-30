/// This should be implemented for an item that has a stable ordering with
/// respect to [SimpleOrdItem::key]. Unlike [OrdPair] and [OrdArena] which
/// implicitly require keys and values to be separate structs, the item
/// implementing this can project part of its internal structure as the key.
pub trait SimpleOrdItem {
    /// Returns the key
    fn key(&self) -> impl Ord;
}

/// An implementor of [SimpleOrdItem] that has a key `K: Ord` and associated
/// value `V`. `&K` is used as the key.
pub struct OrdPair<K: Ord, V> {
    pub k: K,
    pub v: V,
}

impl<K: Ord, V> SimpleOrdItem for OrdPair<K, V> {
    fn key(&self) -> impl Ord {
        &self.k
    }
}
