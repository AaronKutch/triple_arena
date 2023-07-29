//! Iterators for `OrdArena`

use crate::{OrdArena, Ptr};

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

/// An iterator over `&K` in an `OrdArena`
pub struct Keys<'a, P: Ptr, K: Ord, V> {
    arena: &'a OrdArena<P, K, V>,
    p: Option<P>,
}

impl<'a, P: Ptr, K: Ord, V> Iterator for Keys<'a, P, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        let p_res = self.p;
        self.arena.next_ptr(&mut self.p);
        p_res.map(|p| self.arena.get_key(p).unwrap())
    }
}

/// An iterator over `&V` in an `OrdArena`
pub struct Vals<'a, P: Ptr, K: Ord, V> {
    arena: &'a OrdArena<P, K, V>,
    p: Option<P>,
}

impl<'a, P: Ptr, K: Ord, V> Iterator for Vals<'a, P, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        let p_res = self.p;
        self.arena.next_ptr(&mut self.p);
        p_res.map(|p| self.arena.get_val(p).unwrap())
    }
}

/*
/// A mutable iterator over `&mut V` in an `OrdArena`
pub struct ValsMut<'a, P: Ptr, K: Ord, V> {
    arena: &'a mut OrdArena<P, K, V>,
    p: Option<P>,
}

impl<'a, P: Ptr, K: Ord, V> Iterator for ValsMut<'a, P, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        let p_res = self.p;
        self.arena.next_ptr(&mut self.p);
        p_res.map(|p| self.arena.get_val_mut(p).unwrap())
    }
}
*/

/// An iterator over `(P, &K, &V)` in an `OrdArena`
pub struct Iter<'a, P: Ptr, K: Ord, V> {
    arena: &'a OrdArena<P, K, V>,
    p: Option<P>,
}

impl<'a, P: Ptr, K: Ord, V> Iterator for Iter<'a, P, K, V> {
    type Item = (P, &'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let p_res = self.p;
        self.arena.next_ptr(&mut self.p);
        p_res.map(|p| {
            let tmp = self.arena.get(p).unwrap();
            (p, tmp.0, tmp.1)
        })
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

    /// Iteration over `&K`
    pub fn keys(&self) -> Keys<P, K, V> {
        Keys {
            arena: self,
            p: self.min(),
        }
    }

    /// Iteration over `&V`
    pub fn vals(&self) -> Vals<P, K, V> {
        Vals {
            arena: self,
            p: self.min(),
        }
    }

    /*
    /// Mutable iteration over `&mut V`
    pub fn vals_mut(&mut self) -> ValsMut<P, V> {
        ValsMut {
            iter_mut: self.vals.vals_mut(),
        }
    }
    */

    /// Iteration over `(P, &K, &V)` tuples
    pub fn iter(&self) -> Iter<P, K, V> {
        Iter {
            arena: self,
            p: self.min(),
        }
    }

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
            if let Some(link) = self.a.get_link(*inner) {
                if let Some(next) = link.next() {
                    *p = Some(next);
                    return
                }
            }
            *p = None;
        }
        // else `p` is already `None`
    }
}
