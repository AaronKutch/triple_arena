//! Iterators for `OrdArena`

use crate::{OrdArena, Ptr};

/// All the iterators here can return values in arbitrary order
impl<P: Ptr, K: Ord, V> OrdArena<P, K, V> {
    // TODO make all iterators go in order
    /*
    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> Ptrs<P, K> {
        Ptrs {
            iter: self.a.ptrs(),
        }
    }

    /// Iteration over `&K`
    pub fn keys(&self) -> Keys<P, K> {
        Keys {
            iter: self.keys.vals(),
        }
    }

    /// Iteration over `&V`
    pub fn vals(&self) -> Vals<P, V> {
        Vals {
            iter: self.vals.vals(),
        }
    }

    /// Mutable iteration over `&mut K`
    pub fn keys_mut(&mut self) -> KeysMut<P, K> {
        KeysMut {
            iter_mut: self.keys.vals_mut(),
        }
    }

    /// Mutable iteration over `&mut V`
    pub fn vals_mut(&mut self) -> ValsMut<P, V> {
        ValsMut {
            iter_mut: self.vals.vals_mut(),
        }
    }

    /// Iteration over `(P, &K, &V)` tuples. For each surject with multiple `P`
    /// pointing to the same `V`, the same reference to the `V` is returned
    /// multiple times
    pub fn iter(&self) -> Iter<P, K, V> {
        Iter {
            iter: self.keys.iter(),
            vals: &self.vals,
        }
    }*/
}
