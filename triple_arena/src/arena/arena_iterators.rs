//! Iterators for `Arena`

use core::num::NonZeroUsize;

use InternalSlot::*;
use recasting::{Recast, Recaster};

use crate::{
    Arena, InvalidationOption, InvalidationResult,
    arena::{ArenaBacking, InternalSlot},
    traits::{Advancer, ArenaTrait, Ptr},
    utils::traits::{NonZeroInxGenericStack, PtrInx},
};

/// An advancer over the valid `P`s of an `Arena`
pub struct PtrAdvancer<P: Ptr> {
    pub(in crate::arena) inx: Option<P::Inx>,
    // if in reverse
    pub(in crate::arena) rev: bool,
}

impl<P: Ptr, T, B: ArenaBacking> Advancer<Arena<P, T, B>> for PtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &Arena<P, T, B>) -> Option<Self::Item> {
        loop {
            let inx = self.inx?;
            // If the `Ptr` is not linear then this will always return `None` and the
            // advancer will be empty like it should
            let raw_inx = P::Inx::try_into_usize(inx)?;
            // update before other fallible points
            if self.rev {
                self.inx = NonZeroUsize::new(raw_inx.get() - 1).and_then(P::Inx::try_from_usize);
            } else {
                self.inx = raw_inx.checked_add(1).and_then(P::Inx::try_from_usize);
            }
            let allocation = collection.m.get(raw_inx)?;
            if let Allocated(g, _) = allocation {
                return Some(P::_from_raw(inx, *g));
            }
        }
    }

    fn empty() -> Self {
        Self {
            inx: None,
            rev: false,
        }
    }
}

/// An iterator over the valid `P`s of an `Arena`
pub struct Ptrs<'a, P: Ptr, T, B: ArenaBacking> {
    arena: &'a Arena<P, T, B>,
    adv: PtrAdvancer<P>,
}

impl<P: Ptr, T, B: ArenaBacking> Iterator for Ptrs<'_, P, T, B> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv.advance(self.arena)
    }
}

/// An iterator over `&T` in an `Arena`
pub struct Vals<'a, P: Ptr, T, B: ArenaBacking> {
    arena: &'a Arena<P, T, B>,
    adv: PtrAdvancer<P>,
}

impl<'a, P: Ptr, T, B: ArenaBacking> Iterator for Vals<'a, P, T, B> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| self.arena.get(p).unwrap())
    }
}

/// A mutable iterator over `&mut T` in an `Arena`
pub struct ValsMut<'a, P: Ptr, T, B: ArenaBacking> {
    arena: &'a mut Arena<P, T, B>,
    adv: PtrAdvancer<P>,
}

impl<'a, P: Ptr, T, B: ArenaBacking> Iterator for ValsMut<'a, P, T, B> {
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
pub struct Iter<'a, P: Ptr, T, B: ArenaBacking> {
    arena: &'a Arena<P, T, B>,
    adv: PtrAdvancer<P>,
}

impl<'a, P: Ptr, T, B: ArenaBacking> Iterator for Iter<'a, P, T, B> {
    type Item = (P, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| (p, self.arena.get(p).unwrap()))
    }
}

/// A mutable iterator over `(P, &mut T)` in an `Arena`
pub struct IterMut<'a, P: Ptr, T, B: ArenaBacking> {
    pub(in crate::arena) arena: &'a mut Arena<P, T, B>,
    pub(in crate::arena) adv: PtrAdvancer<P>,
}

impl<'a, P: Ptr, T, B: ArenaBacking> Iterator for IterMut<'a, P, T, B> {
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
pub struct Drain<'a, P: Ptr, T, B: ArenaBacking> {
    pub(crate) arena: &'a mut Arena<P, T, B>,
    pub(crate) adv: PtrAdvancer<P>,
}

impl<P: Ptr, T, B: ArenaBacking> Drop for Drain<'_, P, T, B> {
    fn drop(&mut self) {
        self.arena.clear().ok();
    }
}

impl<P: Ptr, T, B: ArenaBacking> Iterator for Drain<'_, P, T, B> {
    type Item = InvalidationOption<(P, T)>;

    fn next(&mut self) -> Option<Self::Item> {
        let p = self.adv.advance(self.arena)?;
        // for global generation arenas, just do this for simplicity and so that the
        // invalidation is associated with a particular element

        //  FIXME
        match ArenaTrait::remove(self.arena, p) {
            InvalidationResult::Success(t) => Some(InvalidationOption::Success((p, t))),
            InvalidationResult::GenerationOverflow(t) => {
                Some(InvalidationOption::GenerationOverflow((p, t)))
            }
            InvalidationResult::InvalidPtr => None,
        }
    }
}

/*
/// A draining iterator over `(P, T)` in an `Arena`
pub struct Drain<'a, P: Ptr, T, B: ArenaBacking> {
    arena: &'a mut Arena<P, T, B>,
    adv: PtrAdvancer<P>,
}

impl<P: Ptr, T, B: ArenaBacking> Drop for Drain<'_, P, T, B> {
    fn drop(&mut self) {
        if !self.arena.is_empty() {
            self.arena.clear();
        }
        // else normal operation
    }
}

impl<P: Ptr, T, B: ArenaBacking> Iterator for Drain<'_, P, T, B> {
    type Item = (P, T);

    fn next(&mut self) -> Option<Self::Item> {
        // NOTE: I have not thought fully about how our new invariants interact with
        // leaking the `Drain` struct, just use a normal advancer
        self.adv
            .advance(self.arena)
            .map(|p| (p, self.arena.remove_internal_inx_unwrap(p.inx(), false)))
    }
}*/

/// A capacity draining iterator over `(P, T)` in an `Arena`
pub struct CapacityDrain<P: Ptr, T, B: ArenaBacking> {
    arena: Arena<P, T, B>,
    adv: PtrAdvancer<P>,
}

impl<P: Ptr, T, B: ArenaBacking> Iterator for CapacityDrain<P, T, B> {
    type Item = (P, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(&self.arena)
            .map(|p| (p, self.arena.remove(p).unwrap()))
    }
}

impl<P: Ptr, T, B: ArenaBacking> IntoIterator for Arena<P, T, B> {
    type IntoIter = CapacityDrain<P, T, B>;
    type Item = (P, T);

    fn into_iter(self) -> Self::IntoIter {
        let adv = self.advancer();
        CapacityDrain { arena: self, adv }
    }
}

impl<'a, P: Ptr, T, B: ArenaBacking> IntoIterator for &'a Arena<P, T, B> {
    type IntoIter = Iter<'a, P, T, B>;
    type Item = (P, &'a T);

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            arena: self,
            adv: self.advancer(),
        }
    }
}

impl<'a, P: Ptr, T, B: ArenaBacking> IntoIterator for &'a mut Arena<P, T, B> {
    type IntoIter = IterMut<'a, P, T, B>;
    type Item = (P, &'a mut T);

    /// This returns an `IterMut`. Use `Arena::drain` for by-value consumption.
    fn into_iter(self) -> Self::IntoIter {
        let adv = self.advancer();
        IterMut { arena: self, adv }
    }
}

/// All the iterators here can return values in arbitrary order
impl<P: Ptr, T, B: ArenaBacking> Arena<P, T, B> {
    /// Advances over every valid `Ptr` in `self`.
    ///
    /// When using the correct loop structure, every `Ptr` valid from before the
    /// loop began will be witnessed as long as it is kept valid during the
    /// loop. The `Ptr`s of insertions that occur during the loop can both be
    /// witnessed or not witnessed before the loop terminates.
    pub fn old_advancer(&self) -> PtrAdvancer<P> {
        PtrAdvancer {
            // FIXME remove we fixed this in the trait
            inx: Some(P::Inx::try_from_usize(NonZeroUsize::new(1).unwrap()).unwrap()),
            rev: false,
        }
    }

    /// Iteration over all valid `P` in the arena
    pub fn old_ptrs(&self) -> Ptrs<'_, P, T, B> {
        Ptrs {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// Iteration over `&T`
    pub fn old_vals(&self) -> Vals<'_, P, T, B> {
        Vals {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// Mutable iteration over `&mut T`
    pub fn old_vals_mut(&mut self) -> ValsMut<'_, P, T, B> {
        let adv = self.advancer();
        ValsMut { arena: self, adv }
    }

    /// Iteration over `(P, &T)` tuples
    pub fn old_iter(&self) -> Iter<'_, P, T, B> {
        Iter {
            arena: self,
            adv: self.advancer(),
        }
    }

    /// Mutable iteration over `(P, &mut T)` tuples
    pub fn old_iter_mut(&mut self) -> IterMut<'_, P, T, B> {
        let adv = self.advancer();
        IterMut { arena: self, adv }
    }

    /// By-value iteration over `(P, T)` tuples. Consumes all `T` in
    /// `self`, but retains capacity.
    ///
    /// Note: When the `Drain` struct is dropped, any remaining iterations will
    /// be consumed and dropped like normal. If the `Drain` struct is leaked
    /// (such as with [core::mem::forget]), unspecified behavior will result.
    pub fn old_drain(&mut self) -> Drain<'_, P, T, B> {
        // NOTE: I have not thought fully about how our new invariants interact with
        // leaking the `Drain` struct, just use a normal advancer

        self.inc_generation().ok();
        let adv = self.advancer();
        Drain { arena: self, adv }
    }

    /// Performs [Arena::compress_and_shrink] and returns an `Arena<P, P>` that
    /// can be used for [Recast]ing
    pub fn compress_and_shrink_recaster(&mut self) -> Arena<P, P, B> {
        let mut res = Arena::<P, P, B>::new();
        res.clone_from_with(self, |_, _| P::invalid());
        self.compress_and_shrink_with(|p, _, q| *res.get_mut(p).unwrap() = q);
        res
    }
}

impl<P: Ptr, B: ArenaBacking> Recaster for Arena<P, P, B> {
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

impl<P: Ptr, B: ArenaBacking, I, T: Recast<I>> Recast<I> for Arena<P, T, B> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for val in self.vals_mut() {
            val.recast(recaster)?;
        }
        Ok(())
    }
}
