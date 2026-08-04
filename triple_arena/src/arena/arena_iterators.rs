//! Iterators for `Arena`

use core::num::NonZeroUsize;

use InternalSlot::*;
use recasting::{Recast, Recaster};

use crate::{
    Arena, InvalidationOption, InvalidationResult,
    traits::{Advancer, ArenaTrait, Ptr},
    utils::{
        InternalSlot,
        traits::{ArenaBacking, NonZeroInxGenericStack, PtrInx},
    },
};

/// An advancer over the valid `P`s of an `Arena`
pub struct PtrAdvancer<P: Ptr> {
    inx: Option<P::Inx>,
    // if in reverse
    rev: bool,
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

/*
REF(mutable_iterator_soundness)
We have to be very careful or else the mutable iterator implementation will be unsound due to `PtrInx` being a safe trait (we would rather not make it unsafe for various reasons). We can rely on the backing stack since `NonZeroInxGenericStack` is unsafe and strict. As long as we directly use and only increment or decrement a NonZeroUsize and don't roundtrip `P::Inx` after initialization, it is safe. But other iterators want to use `P::Inx` because it is more compact in some cases. We only need to special case `IterMut` and anything else mutable can safely inherit from it
*/

/// A mutable iterator over `(P, &mut T)` in an `Arena`
pub struct IterMut<'a, P: Ptr, T, B: ArenaBacking> {
    arena: &'a mut Arena<P, T, B>,
    inx: Option<NonZeroUsize>,
}

// FIXME this is unsound, make `PtrInx` in particular unsafe
impl<'a, P: Ptr, T, B: ArenaBacking> Iterator for IterMut<'a, P, T, B> {
    type Item = (P, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let inx = self.inx?;
            // If the `Ptr` is not linear then this will always return `None` and the
            // iterator will be empty like it should
            let p_inx = P::Inx::try_from_usize(inx)?;
            // before other fallible points
            self.inx = inx.checked_add(1);
            let allocation = self.arena.m.get_mut(inx)?;
            if let Allocated(g, t) = allocation {
                let p = P::_from_raw(p_inx, *g);
                // safety: subsequent calls to `next` will not access the same data
                return unsafe { Some((p, &mut *(t as *mut T))) };
            }
        }
    }
}

/// A draining iterator over `(P, T)` in an `Arena`
pub struct Drain<'a, P: Ptr, T, B: ArenaBacking> {
    arena: &'a mut Arena<P, T, B>,
    adv: PtrAdvancer<P>,
}

impl<P: Ptr, T, B: ArenaBacking> Drop for Drain<'_, P, T, B> {
    fn drop(&mut self) {
        self.arena.clear().allow();
    }
}

impl<P: Ptr, T, B: ArenaBacking> Iterator for Drain<'_, P, T, B> {
    type Item = InvalidationOption<(P, T)>;

    fn next(&mut self) -> Option<Self::Item> {
        let p = self.adv.advance(self.arena)?;
        // for global generation arenas, just do this for simplicity and so that the
        // invalidation is associated with a particular element

        match self.arena.remove(p) {
            InvalidationResult::Success(t) => Some(InvalidationOption::Success((p, t))),
            InvalidationResult::GenerationOverflow(t) => {
                Some(InvalidationOption::GenerationOverflow((p, t)))
            }
            InvalidationResult::InvalidPtr => None,
        }
    }
}

/// A capacity draining iterator over `(P, T)` in an `Arena`
pub struct CapacityDrain<P: Ptr, T, B: ArenaBacking> {
    arena: Arena<P, T, B>,
    adv: PtrAdvancer<P>,
}

impl<P: Ptr, T, B: ArenaBacking> Iterator for CapacityDrain<P, T, B> {
    type Item = (P, T);

    fn next(&mut self) -> Option<Self::Item> {
        // ignore generation overflows
        self.adv
            .advance(&self.arena)
            .map(|p| (p, self.arena.remove(p).allow().unwrap()))
    }
}

// TODO we could remove these in the future with associated `impl` types
impl<P: Ptr, T, B: ArenaBacking> Arena<P, T, B> {
    pub(crate) fn internal_advancer_inx(&self, inx: P::Inx, rev: bool) -> PtrAdvancer<P> {
        PtrAdvancer {
            inx: Some(inx),
            rev,
        }
    }

    pub(crate) fn internal_iter(&self) -> Iter<'_, P, T, B> {
        Iter {
            arena: self,
            adv: self.advancer(),
        }
    }

    pub(crate) fn internal_iter_mut(&mut self) -> IterMut<'_, P, T, B> {
        IterMut {
            arena: self,
            inx: Some(NonZeroUsize::new(1).unwrap()),
        }
    }

    pub(crate) fn internal_drain(&mut self) -> Drain<'_, P, T, B> {
        let adv = self.advancer();
        Drain { arena: self, adv }
    }

    pub(crate) fn internal_capacity_drain(self) -> CapacityDrain<P, T, B> {
        let adv = self.advancer();
        CapacityDrain { arena: self, adv }
    }
}

impl<'a, P: Ptr, T, B: ArenaBacking> IntoIterator for &'a Arena<P, T, B> {
    type IntoIter = Iter<'a, P, T, B>;
    type Item = (P, &'a T);

    fn into_iter(self) -> Self::IntoIter {
        self.internal_iter()
    }
}

impl<'a, P: Ptr, T, B: ArenaBacking> IntoIterator for &'a mut Arena<P, T, B> {
    type IntoIter = IterMut<'a, P, T, B>;
    type Item = (P, &'a mut T);

    /// This returns an `IterMut`. Use `Arena::drain` for by-value consumption.
    fn into_iter(self) -> Self::IntoIter {
        self.internal_iter_mut()
    }
}

impl<P: Ptr, T, B: ArenaBacking> IntoIterator for Arena<P, T, B> {
    type IntoIter = CapacityDrain<P, T, B>;
    type Item = (P, T);

    fn into_iter(self) -> Self::IntoIter {
        self.internal_capacity_drain()
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
