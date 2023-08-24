//! Iterators for `Arena`

use core::{marker::PhantomData, num::NonZeroUsize};

use recasting::{Recast, Recaster};
use InternalEntry::*;

use crate::{
    arena::InternalEntry,
    utils::{nzusize_unchecked, PtrInx},
    Advancer, Arena, Ptr,
};

/// An advancer over the valid `P`s of an `Arena`
pub struct PtrAdvancer<P: Ptr, T> {
    // If we used `P::Inx`, we would be widening and truncating on every advance, and running into
    // needing a boolean to tell if we advanced past the last entry where `P::Inx::max` is a valid
    // entry
    inx: NonZeroUsize,
    _boo: PhantomData<fn() -> (P, T)>,
}

impl<P: Ptr, T> Advancer for PtrAdvancer<P, T> {
    type Collection = Arena<P, T>;
    type Item = P;

    fn advance(&mut self, collection: &Self::Collection) -> Option<Self::Item> {
        loop {
            let old_inx = self.inx;
            if let Some(allocation) = collection.m.get(old_inx) {
                unsafe {
                    self.inx = nzusize_unchecked(old_inx.get().wrapping_add(1));
                }
                if let Allocated(g, _) = allocation {
                    return Some(P::_from_raw(P::Inx::new(old_inx), *g))
                }
            } else {
                return None
            }
        }
    }
}

/// An iterator over the valid `P`s of an `Arena`
pub struct Ptrs<'a, P: Ptr, T> {
    arena: &'a Arena<P, T>,
    adv: PtrAdvancer<P, T>,
}

impl<'a, P: Ptr, T> Iterator for Ptrs<'a, P, T> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv.advance(self.arena)
    }
}

/// An iterator over `&T` in an `Arena`
pub struct Vals<'a, P: Ptr, T> {
    arena: &'a Arena<P, T>,
    adv: PtrAdvancer<P, T>,
}

impl<'a, P: Ptr, T> Iterator for Vals<'a, P, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| self.arena.get(p).unwrap())
    }
}

/// A mutable iterator over `&mut T` in an `Arena`
pub struct ValsMut<'a, P: Ptr, T> {
    arena: &'a mut Arena<P, T>,
    adv: PtrAdvancer<P, T>,
}

impl<'a, P: Ptr, T> Iterator for ValsMut<'a, P, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.adv.advance(self.arena) {
            let tmp = self.arena.get_mut(p).unwrap();
            // safety: subsequent calls to `next` will not access the same data
            unsafe { Some(&mut *(tmp as *mut T)) }
        } else {
            None
        }
    }
}

/// An iterator over `(P, &T)` in an `Arena`
pub struct Iter<'a, P: Ptr, T> {
    arena: &'a Arena<P, T>,
    adv: PtrAdvancer<P, T>,
}

impl<'a, P: Ptr, T> Iterator for Iter<'a, P, T> {
    type Item = (P, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| (p, self.arena.get(p).unwrap()))
    }
}

/// A mutable iterator over `(P, &mut T)` in an `Arena`
pub struct IterMut<'a, P: Ptr, T> {
    arena: &'a mut Arena<P, T>,
    adv: PtrAdvancer<P, T>,
}

impl<'a, P: Ptr, T> Iterator for IterMut<'a, P, T> {
    type Item = (P, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.adv.advance(self.arena) {
            let tmp = self.arena.get_mut(p).unwrap();
            // safety: subsequent calls to `next` will not access the same data
            unsafe { Some((p, &mut *(tmp as *mut T))) }
        } else {
            None
        }
    }
}

/// A draining iterator over `(P, T)` in an `Arena`
pub struct Drain<'a, P: Ptr, T> {
    arena: &'a mut Arena<P, T>,
    adv: PtrAdvancer<P, T>,
}

impl<'a, P: Ptr, T> Drop for Drain<'a, P, T> {
    fn drop(&mut self) {
        if !self.arena.is_empty() {
            self.arena.clear();
        }
        // else normal operation
    }
}

impl<'a, P: Ptr, T> Iterator for Drain<'a, P, T> {
    type Item = (P, T);

    fn next(&mut self) -> Option<Self::Item> {
        // NOTE: I have not thought fully about how our new invariants interact with
        // leaking the `Drain` struct, just use a normal advancer
        self.adv
            .advance(self.arena)
            .map(|p| (p, self.arena.remove_internal_inx_unwrap(p.inx(), false)))
    }
}

/// A capacity draining iterator over `(P, T)` in an `Arena`
pub struct CapacityDrain<P: Ptr, T> {
    arena: Arena<P, T>,
    adv: PtrAdvancer<P, T>,
}

impl<P: Ptr, T> Iterator for CapacityDrain<P, T> {
    type Item = (P, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(&self.arena)
            .map(|p| (p, self.arena.remove(p).unwrap()))
    }
}

impl<P: Ptr, T> IntoIterator for Arena<P, T> {
    type IntoIter = CapacityDrain<P, T>;
    type Item = (P, T);

    fn into_iter(self) -> Self::IntoIter {
        self.capacity_drain()
    }
}

impl<'a, P: Ptr, T> IntoIterator for &'a Arena<P, T> {
    type IntoIter = Iter<'a, P, T>;
    type Item = (P, &'a T);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, P: Ptr, T> IntoIterator for &'a mut Arena<P, T> {
    type IntoIter = IterMut<'a, P, T>;
    type Item = (P, &'a mut T);

    /// This returns an `IterMut`. Use `Arena::drain` for by-value consumption.
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<P: Ptr, T> FromIterator<T> for Arena<P, T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut a = Arena::new();
        for t in iter {
            a.insert(t);
        }
        a
    }
}

/// All the iterators here can return values in arbitrary order
impl<P: Ptr, T> Arena<P, T> {
    /// Advances over every valid `Ptr` in `self`.
    ///
    /// When using the correct loop structure, every `Ptr` valid from before the
    /// loop began will be witnessed as long as it is kept valid during the
    /// loop. The `Ptr`s of insertions that occur during the loop can both be
    /// witnessed or not witnessed before the loop terminates.
    pub fn advancer(&self) -> PtrAdvancer<P, T> {
        PtrAdvancer {
            inx: NonZeroUsize::new(1).unwrap(),
            _boo: PhantomData,
        }
    }

    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> Ptrs<P, T> {
        Ptrs {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// Iteration over `&T`
    pub fn vals(&self) -> Vals<P, T> {
        Vals {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// Mutable iteration over `&mut T`
    pub fn vals_mut(&mut self) -> ValsMut<P, T> {
        let adv = self.advancer();
        ValsMut { arena: self, adv }
    }

    /// Iteration over `(P, &T)` tuples
    pub fn iter(&self) -> Iter<P, T> {
        Iter {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// Mutable iteration over `(P, &mut T)` tuples
    pub fn iter_mut(&mut self) -> IterMut<P, T> {
        let adv = self.advancer();
        IterMut { arena: self, adv }
    }

    /// By-value iteration over `(P, T)` tuples. Consumes all `T` in
    /// `self`, but retains capacity.
    ///
    /// Note: When the `Drain` struct is dropped, any remaining iterations will
    /// be consumed and dropped like normal. If the `Drain` struct is leaked
    /// (such as with [core::mem::forget]), unspecified behavior will result.
    pub fn drain(&mut self) -> Drain<P, T> {
        // NOTE: I have not thought fully about how our new invariants interact with
        // leaking the `Drain` struct, just use a normal advancer

        self.inc_gen();
        let adv = self.advancer();
        Drain { arena: self, adv }
    }

    // This is needed for the `impl IntoIterator for Arena<T, P>` trait

    /// By-value iteration with `(P, T)` tuples. Consumes all `T` and
    /// capacity.
    pub fn capacity_drain(self) -> CapacityDrain<P, T> {
        let adv = self.advancer();
        CapacityDrain { arena: self, adv }
    }

    /// Performs [Arena::compress_and_shrink] and returns an `Arena<P, P>` that
    /// can be used for [Recast]ing
    pub fn compress_and_shrink_recaster(&mut self) -> Arena<P, P> {
        let mut res = Arena::<P, P>::new();
        res.clone_from_with(self, |_, _| P::invalid());
        self.compress_and_shrink_with(|p, _, q| *res.get_mut(p).unwrap() = q);
        res
    }
}

impl<P: Ptr> Recaster for Arena<P, P> {
    type Item = P;

    fn recast_item(&self, item: &mut Self::Item) -> Result<(), Self::Item> {
        if let Some(res) = self.get(*item) {
            *item = *res;
            Ok(())
        } else {
            Err(*item)
        }
    }
}

impl<P: Ptr, I, T: Recast<I>> Recast<I> for Arena<P, T> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for val in self.vals_mut() {
            val.recast(recaster)?;
        }
        Ok(())
    }
}
