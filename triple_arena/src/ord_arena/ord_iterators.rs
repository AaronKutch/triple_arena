//! Iterators for `OrdArena`

use core::marker::PhantomData;

use crate::{Advancer, OrdArena, Ptr};

/// An advancer over the valid `P`s of an `OrdArena`
pub struct PtrAdvancer<P: Ptr, K: Ord, V> {
    // same as for `ChainPtrAdvancer` except we get to assume the chain is acyclical and we start
    // from the beginning
    ptr: Option<P>,
    _boo: PhantomData<(K, V)>,
}

impl<P: Ptr, K: Ord, V> Advancer for PtrAdvancer<P, K, V> {
    type Collection = OrdArena<P, K, V>;
    type Item = P;

    fn advance(&mut self, collection: &Self::Collection) -> Option<Self::Item> {
        if let Some(ptr) = self.ptr {
            if let Some(link) = collection.a.get_link(ptr) {
                if let Some(next) = link.next() {
                    self.ptr = Some(next);
                } else {
                    // could be unreachable under invalidation
                    self.ptr = None;
                }
                Some(ptr)
            } else {
                self.ptr = None;
                None
            }
        } else {
            None
        }
    }
}

/// An iterator over the valid `P`s of an `OrdArena`
pub struct Ptrs<'a, P: Ptr, K: Ord, V> {
    arena: &'a OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<'a, P: Ptr, K: Ord, V> Iterator for Ptrs<'a, P, K, V> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv.advance(self.arena)
    }
}

/// An iterator over `&K` in an `OrdArena`
pub struct Keys<'a, P: Ptr, K: Ord, V> {
    arena: &'a OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<'a, P: Ptr, K: Ord, V> Iterator for Keys<'a, P, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| self.arena.get_key(p).unwrap())
    }
}

/// An iterator over `&V` in an `OrdArena`
pub struct Vals<'a, P: Ptr, K: Ord, V> {
    arena: &'a OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<'a, P: Ptr, K: Ord, V> Iterator for Vals<'a, P, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| self.arena.get_val(p).unwrap())
    }
}

/*
/// A mutable iterator over `&mut V` in an `OrdArena`
pub struct ValsMut<'a, P: Ptr, K: Ord, V> {
    arena: &'a mut OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<'a, P: Ptr, K: Ord, V> Iterator for ValsMut<'a, P, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
    }
}
*/

/// An iterator over `(P, &K, &V)` in an `OrdArena`
pub struct Iter<'a, P: Ptr, K: Ord, V> {
    arena: &'a OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<'a, P: Ptr, K: Ord, V> Iterator for Iter<'a, P, K, V> {
    type Item = (P, &'a (K, V));

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| (p, self.arena.get(p).unwrap()))
    }
}

/// All the iterators here iterate in order from the least key to the greatest
/// key
impl<P: Ptr, K: Ord, V> OrdArena<P, K, V> {
    /// Advances over every valid `Ptr` in `self`. Invalidating the next greater
    /// entry is _not_ supported during each advancement.
    pub fn advancer(&self) -> PtrAdvancer<P, K, V> {
        PtrAdvancer {
            ptr: self.min(),
            _boo: PhantomData,
        }
    }

    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> Ptrs<P, K, V> {
        Ptrs {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// Iteration over `&K`
    pub fn keys(&self) -> Keys<P, K, V> {
        Keys {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// Iteration over `&V`
    pub fn vals(&self) -> Vals<P, K, V> {
        Vals {
            arena: self,
            adv: self.advancer(),
        }
    }

    /*
    /// Mutable iteration over `&mut V`
    pub fn vals_mut(&mut self) -> ValsMut<P, V> {
    }
    */

    /// Iteration over `(P, &K, &V)` tuples
    pub fn iter(&self) -> Iter<P, K, V> {
        Iter {
            arena: self,
            adv: self.advancer(),
        }
    }
}
