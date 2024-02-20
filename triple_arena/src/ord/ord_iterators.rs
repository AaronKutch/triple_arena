//! Iterators for `OrdArena`

use core::marker::PhantomData;

use recasting::{Recast, Recaster};

use crate::{Advancer, OrdArena, Ptr};

/// An advancer over the valid `P`s of an `OrdArena`
pub struct PtrAdvancer<P: Ptr, K, V> {
    // same as for `ChainPtrAdvancer` except we get to assume the chain is acyclical and we start
    // from the beginning
    ptr: Option<P::Inx>,
    _boo: PhantomData<fn() -> (K, V)>,
}

impl<P: Ptr, K, V> Advancer for PtrAdvancer<P, K, V> {
    type Collection = OrdArena<P, K, V>;
    type Item = P;

    fn advance(&mut self, collection: &Self::Collection) -> Option<Self::Item> {
        if let Some(ptr) = self.ptr {
            if let Some((gen, link)) = collection.a.get_no_gen(ptr) {
                if let Some(next) = link.next() {
                    self.ptr = Some(next);
                } else {
                    // could be unreachable under invalidation
                    self.ptr = None;
                }
                Some(Ptr::_from_raw(ptr, gen))
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
pub struct Ptrs<'a, P: Ptr, K, V> {
    arena: &'a OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<'a, P: Ptr, K, V> Iterator for Ptrs<'a, P, K, V> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv.advance(self.arena)
    }
}

/// An iterator over `&K` in an `OrdArena`
pub struct Keys<'a, P: Ptr, K, V> {
    arena: &'a OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<'a, P: Ptr, K, V> Iterator for Keys<'a, P, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| self.arena.get_key(p).unwrap())
    }
}

/// An iterator over `&V` in an `OrdArena`
pub struct Vals<'a, P: Ptr, K, V> {
    arena: &'a OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<'a, P: Ptr, K, V> Iterator for Vals<'a, P, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| self.arena.get_val(p).unwrap())
    }
}

/// A mutable iterator over `&mut V` in an `OrdArena`
pub struct ValsMut<'a, P: Ptr, K, V> {
    arena: &'a mut OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<'a, P: Ptr, K, V> Iterator for ValsMut<'a, P, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.adv.advance(self.arena) {
            let tmp = self.arena.get_val_mut(p).unwrap();
            // safety: subsequent calls to `next` will not access the same data
            unsafe { Some(&mut *(tmp as *mut V)) }
        } else {
            None
        }
    }
}

/// An iterator over `(P, &K, &V)` in an `OrdArena`
pub struct Iter<'a, P: Ptr, K, V> {
    arena: &'a OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<'a, P: Ptr, K, V> Iterator for Iter<'a, P, K, V> {
    type Item = (P, &'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.adv.advance(self.arena).map(|p| {
            let tmp = self.arena.get(p).unwrap();
            (p, tmp.0, tmp.1)
        })
    }
}

/// A draining iterator over `(P, K, V)` in an `OrdArena`
pub struct Drain<'a, P: Ptr, K, V> {
    arena: &'a mut OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<'a, P: Ptr, K, V> Drop for Drain<'a, P, K, V> {
    fn drop(&mut self) {
        if !self.arena.is_empty() {
            self.arena.clear();
        }
        // else normal operation
    }
}

impl<'a, P: Ptr, K, V> Iterator for Drain<'a, P, K, V> {
    type Item = (P, K, V);

    fn next(&mut self) -> Option<Self::Item> {
        // TODO can we do this more efficiently by ignoring the tree structure but deal
        // with leaking also?
        self.adv.advance(self.arena).map(|p| {
            let res = self.arena.remove(p).unwrap();
            (p, res.0, res.1)
        })
    }
}

/// A capacity draining iterator over `(P, T)` in an `Arena`
pub struct CapacityDrain<P: Ptr, K, V> {
    arena: OrdArena<P, K, V>,
    adv: PtrAdvancer<P, K, V>,
}

impl<P: Ptr, K, V> Iterator for CapacityDrain<P, K, V> {
    type Item = (P, K, V);

    fn next(&mut self) -> Option<Self::Item> {
        // TODO we can definitely do this more efficiently
        self.adv.advance(&self.arena).map(|p| {
            let res = self.arena.remove(p).unwrap();
            (p, res.0, res.1)
        })
    }
}

impl<P: Ptr, K, V> IntoIterator for OrdArena<P, K, V> {
    type IntoIter = CapacityDrain<P, K, V>;
    type Item = (P, K, V);

    fn into_iter(self) -> Self::IntoIter {
        self.capacity_drain()
    }
}

impl<'a, P: Ptr, K, V> IntoIterator for &'a OrdArena<P, K, V> {
    type IntoIter = Iter<'a, P, K, V>;
    type Item = (P, &'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<P: Ptr, K: Ord, V> FromIterator<(K, V)> for OrdArena<P, K, V> {
    /// Uses `insert` and lets it replace identical keys
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut a = OrdArena::new();
        for (k, v) in iter {
            let _ = a.insert(k, v);
        }
        a
    }
}

/// All the iterators here iterate in order from the least key to the greatest
/// key
impl<P: Ptr, K, V> OrdArena<P, K, V> {
    /// Advances over every valid `Ptr` in `self`. Invalidating the next greater
    /// entry is _not_ supported during each advancement.
    pub fn advancer(&self) -> PtrAdvancer<P, K, V> {
        PtrAdvancer {
            ptr: self.first().map(|p| p.inx()),
            _boo: PhantomData,
        }
    }

    /// Advances over valid `Ptr`s in `self` starting from `p_start`. If
    /// `p_start` is invalid the advancer will return only `None`s. Invalidating
    /// the next greater entry is _not_ supported during each advancement.
    pub fn advancer_starting_from(&self, p_start: P) -> PtrAdvancer<P, K, V> {
        PtrAdvancer {
            ptr: Some(p_start.inx()),
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

    /// Mutable iteration over `&mut V`
    pub fn vals_mut(&mut self) -> ValsMut<P, K, V> {
        let adv = self.advancer();
        ValsMut { arena: self, adv }
    }

    /// Iteration over `(P, &K, &V)` tuples
    pub fn iter(&self) -> Iter<P, K, V> {
        Iter {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// By-entry iteration over `(P, K, V)` tuples. Consumes all entries in
    /// `self`, but retains capacity.
    ///
    /// Note: When the `Drain` struct is dropped, any remaining iterations will
    /// be consumed and dropped like normal. If the `Drain` struct is leaked
    /// (such as with [core::mem::forget]), unspecified behavior will result.
    pub fn drain(&mut self) -> Drain<P, K, V> {
        // NOTE: I have not thought fully about how our new invariants interact with
        // leaking the `Drain` struct, just use a normal advancer

        let adv = self.advancer();
        Drain { arena: self, adv }
    }

    /// By-entry iteration with `(P, K, V)` tuples. Consumes all entries and
    /// capacity.
    pub fn capacity_drain(self) -> CapacityDrain<P, K, V> {
        let adv = self.advancer();
        CapacityDrain { arena: self, adv }
    }

    /// Performs [OrdArena::compress_and_shrink] and returns an `Arena<P, P>`
    /// that can be used for [Recast]ing
    pub fn compress_and_shrink_recaster(&mut self) -> crate::Arena<P, P> {
        let mut res = crate::Arena::<P, P>::new();
        self.clone_to_arena(&mut res, |_, _, _| P::invalid());
        self.compress_and_shrink_with(|p, _, _, q| *res.get_mut(p).unwrap() = q);
        res
    }
}

impl<P: Ptr, I, K, V: Recast<I>> Recast<I> for OrdArena<P, K, V> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for val in self.vals_mut() {
            val.recast(recaster)?;
        }
        Ok(())
    }
}
