//! Iterators for `OrdArena`

use crate::{Link, OrdArena, Ptr};

/// An iterator over the valid `P`s of an `OrdArena`
pub struct Ptrs<'a, P: Ptr, K: Ord, V> {
    arena: &'a OrdArena<P, K, V>,
    p: Option<P>,
}

impl<'a, P: Ptr, K: Ord, V> Iterator for Ptrs<'a, P, K, V> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        let p_res = self.p;
        self.arena.next_ptr(&mut self.p);
        p_res
    }
}

/// All the iterators here iterate in order from the least key to the greatest
/// key
impl<P: Ptr, K: Ord, V> OrdArena<P, K, V> {
    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> Ptrs<P, K, V> {
        Ptrs {
            arena: self,
            p: self.min(),
        }
    }

    /*
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

    /// Similar to [crate::ChainArena::next_chain_ptr] except it iterates over
    /// pointers in order of the keys. In order to iterate over all pointers:
    ///
    /// ```text
    /// let mut p = arena.min();
    /// loop {
    ///     if let Some(p) = p {
    ///         // use `p` here, but be aware that the removal or insertion of
    ///         // elements within this loop is not supported
    ///     } else {
    ///         break
    ///     }
    ///     arena.next_ptr(&mut p);
    /// }
    /// ```
    #[inline]
    pub fn next_ptr(&self, p: &mut Option<P>) {
        if let Some(inner) = p {
            if let Some(link) = self.a.get(*inner) {
                if let Some(next) = Link::next(link) {
                    *p = Some(next);
                }
            }
            *p = None;
        }
        // else `p` is already `None`
    }
}
