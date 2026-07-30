//! Iterators for `OrdArena`

use recasting::{Recast, Recaster};

use crate::{
    SimpleOrdArena,
    traits::{Advancer, ArenaTrait, Ptr},
    utils::traits::ArenaBacking,
};

/// An advancer over the valid `P`s of an `OrdArena`
pub struct PtrAdvancer<P: Ptr> {
    // same as for `ChainPtrAdvancer` except we get to assume the chain is acyclical and we start
    // from the beginning
    pub(in crate::ord) inx: Option<P::Inx>,
    // if in reverse
    pub(in crate::ord) rev: bool,
}

impl<P: Ptr, T, B: ArenaBacking> Advancer<SimpleOrdArena<P, T, B>> for PtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &SimpleOrdArena<P, T, B>) -> Option<Self::Item> {
        let inx = self.inx?;
        if let Some((generation, link)) = collection.a.a.get_inx(inx) {
            if self.rev {
                self.inx = link.prev();
            } else {
                self.inx = link.next();
            }
            Some(Ptr::_from_raw(inx, generation))
        } else {
            self.inx = None;
            None
        }
    }

    fn empty() -> Self {
        Self {
            inx: None,
            rev: false,
        }
    }
}

/*
/// An iterator over the valid `P`s of an `OrdArena`
pub struct Ptrs<'a, P: Ptr, K, V, B: ArenaBacking> {
    arena: &'a OrdArena<P, K, V, B>,
    adv: PtrAdvancer<P>,
}

impl<P: Ptr, K, V, B: ArenaBacking> Iterator for Ptrs<'_, P, K, V, B> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv.advance(self.arena)
    }
}

/// An iterator over `&K` in an `OrdArena`
pub struct Keys<'a, P: Ptr, K, V, B: ArenaBacking> {
    arena: &'a OrdArena<P, K, V, B>,
    adv: PtrAdvancer<P>,
}

impl<'a, P: Ptr, K, V, B: ArenaBacking> Iterator for Keys<'a, P, K, V, B> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| self.arena.get_key(p).unwrap())
    }
}

/// An iterator over `&V` in an `OrdArena`
pub struct Vals<'a, P: Ptr, K, V, B: ArenaBacking> {
    arena: &'a OrdArena<P, K, V, B>,
    adv: PtrAdvancer<P>,
}

impl<'a, P: Ptr, K, V, B: ArenaBacking> Iterator for Vals<'a, P, K, V, B> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| self.arena.get_val(p).unwrap())
    }
}

/// A mutable iterator over `&mut V` in an `OrdArena`
pub struct ValsMut<'a, P: Ptr, K, V, B: ArenaBacking> {
    arena: &'a mut OrdArena<P, K, V, B>,
    adv: PtrAdvancer<P>,
}

impl<'a, P: Ptr, K, V, B: ArenaBacking> Iterator for ValsMut<'a, P, K, V, B> {
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
pub struct Iter<'a, P: Ptr, K, V, B: ArenaBacking> {
    arena: &'a OrdArena<P, K, V, B>,
    adv: PtrAdvancer<P>,
}

impl<'a, P: Ptr, K, V, B: ArenaBacking> Iterator for Iter<'a, P, K, V, B> {
    type Item = (P, &'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.adv.advance(self.arena).map(|p| {
            let tmp = self.arena.get(p).unwrap();
            (p, tmp.0, tmp.1)
        })
    }
}

/// A draining iterator over `(P, K, V)` in an `OrdArena`
pub struct Drain<'a, P: Ptr, K, V, B: ArenaBacking> {
    arena: &'a mut OrdArena<P, K, V, B>,
    adv: PtrAdvancer<P>,
}

impl<P: Ptr, K, V, B: ArenaBacking> Drop for Drain<'_, P, K, V, B> {
    fn drop(&mut self) {
        if !self.arena.is_empty() {
            self.arena.clear();
        }
        // else normal operation
    }
}

impl<P: Ptr, K, V, B: ArenaBacking> Iterator for Drain<'_, P, K, V, B> {
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
pub struct CapacityDrain<P: Ptr, K, V, B: ArenaBacking> {
    arena: OrdArena<P, K, V, B>,
    adv: PtrAdvancer<P>,
}

impl<P: Ptr, K, V, B: ArenaBacking> Iterator for CapacityDrain<P, K, V, B> {
    type Item = (P, K, V);

    fn next(&mut self) -> Option<Self::Item> {
        // TODO we can definitely do this more efficiently
        self.adv.advance(&self.arena).map(|p| {
            let res = self.arena.remove(p).unwrap();
            (p, res.0, res.1)
        })
    }
}

impl<P: Ptr, K, V, B: ArenaBacking> IntoIterator for OrdArena<P, K, V, B> {
    type IntoIter = CapacityDrain<P, K, V, B>;
    type Item = (P, K, V);

    fn into_iter(self) -> Self::IntoIter {
        self.capacity_drain()
    }
}

impl<'a, P: Ptr, K, V, B: ArenaBacking> IntoIterator for &'a OrdArena<P, K, V, B> {
    type IntoIter = Iter<'a, P, K, V, B>;
    type Item = (P, &'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<P: Ptr, K: Ord, V, B: ArenaBacking> FromIterator<(K, V)> for OrdArena<P, K, V, B> {
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
impl<P: Ptr, K, V, B: ArenaBacking> OrdArena<P, K, V, B> {
    /// Advances over every valid `Ptr` in `self`. Invalidating the next greater
    /// entry is _not_ supported during each advancement.
    pub fn advancer(&self) -> PtrAdvancer<P> {
        PtrAdvancer {
            ptr: self.first().map(|p| p.inx()),
        }
    }

    /// Advances over valid `Ptr`s in `self` starting from `p_start`. If
    /// `p_start` is invalid the advancer will return only `None`s. Invalidating
    /// the next greater entry is _not_ supported during each advancement.
    pub fn advancer_starting_from(&self, p_start: P) -> PtrAdvancer<P> {
        PtrAdvancer {
            ptr: Some(p_start.inx()),
        }
    }

    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> Ptrs<'_, P, K, V, B> {
        Ptrs {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// Iteration over `&K`
    pub fn keys(&self) -> Keys<'_, P, K, V, B> {
        Keys {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// Iteration over `&V`
    pub fn vals(&self) -> Vals<'_, P, K, V, B> {
        Vals {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// Mutable iteration over `&mut V`
    pub fn vals_mut(&mut self) -> ValsMut<'_, P, K, V, B> {
        let adv = self.advancer();
        ValsMut { arena: self, adv }
    }

    /// Iteration over `(P, &K, &V)` tuples
    pub fn iter(&self) -> Iter<'_, P, K, V, B> {
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
    pub fn drain(&mut self) -> Drain<'_, P, K, V, B> {
        // NOTE: I have not thought fully about how our new invariants interact with
        // leaking the `Drain` struct, just use a normal advancer

        let adv = self.advancer();
        Drain { arena: self, adv }
    }

    /// By-entry iteration with `(P, K, V)` tuples. Consumes all entries and
    /// capacity.
    pub fn capacity_drain(self) -> CapacityDrain<P, K, V, B> {
        let adv = self.advancer();
        CapacityDrain { arena: self, adv }
    }

    /// Performs [OrdArena::compress_and_shrink] and returns an `Arena<P, P>`
    /// that can be used for [Recast]ing
    pub fn compress_and_shrink_recaster(&mut self) -> crate::Arena<P, P, B> {
        let mut res = crate::Arena::<P, P, B>::new();
        self.clone_to_arena(&mut res, |_, _, _| P::invalid());
        self.compress_and_shrink_with(|p, _, _, q| *res.get_mut(p).unwrap() = q);
        res
    }
}

impl<P: Ptr, I, K, V: Recast<I>, B: ArenaBacking> Recast<I> for OrdArena<P, K, V, B> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for val in self.vals_mut() {
            val.recast(recaster)?;
        }
        Ok(())
    }
}
*/
