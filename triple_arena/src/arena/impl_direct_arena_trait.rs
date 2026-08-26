use core::{cmp::min, mem, num::NonZeroUsize, slice::GetDisjointMutError};

use crate::{
    DirectArena, InvalidationOption, InvalidationResult, direct_arena_iterators,
    errors::{AllocError, DirectInsertionError, ReallocationError},
    traits::{
        Advancer, ArenaCloneFromWith, ArenaDirectInsertEntryTrait, ArenaDirectInsertTrait,
        ArenaTrait, CompactArenaTrait, DisjointableArenaTrait, Ptr,
    },
    utils::{
        DirectSlot::*,
        from_checked_raw,
        traits::{ArenaBacking, NonZeroInxGenericStack, PtrInx},
    },
};

impl<P: Ptr, T, B: ArenaBacking> ArenaTrait<P, T> for DirectArena<P, T, B> {
    type PtrAdvancer = direct_arena_iterators::PtrAdvancer<P>;

    fn new() -> Self {
        Self {
            len: 0,
            m: NonZeroInxGenericStack::new(),
        }
    }

    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError> {
        Ok(Self {
            len: 0,
            m: NonZeroInxGenericStack::with_min_capacity(min_capacity)?,
        })
    }

    fn capacity(&self) -> usize {
        min(
            self.m.capacity(),
            P::Inx::max_index().map(|i| i.get()).unwrap_or(usize::MAX),
        )
    }

    fn max_capacity(&self) -> Option<usize> {
        self.m.max_capacity()
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), ReallocationError> {
        // so that capacity on the end is not used up by unallocated slots, but only
        // pop off exactly what is needed, so that direct insertion doesn't have to add
        // back in free slots
        let excess = self.m.len().saturating_sub(min_capacity);
        self.pop_free_end_slots(excess);
        // using `max_index` because we are dealing with a plain `usize` and testing for
        // linearity, this equivalently does the check that `P::Inx::try_from_usize`
        // would succeed.
        if let Some(max) = P::Inx::max_index()
            && min_capacity > max.get()
        {
            // this is not a max capacity concern (according to the `max_capacity` kind of
            // maximum)
            return Err(ReallocationError::AllocError);
        }
        self.m.reallocate_min_capacity(min_capacity)
    }

    fn len(&self) -> usize {
        self.len
    }

    fn singular_generation(&self) -> Option<<P as Ptr>::Gen> {
        None
    }

    fn get_inx(&self, p: <P as Ptr>::Inx) -> Option<(<P as Ptr>::Gen, &T)> {
        let Allocated(generation, t) = self.m.get(PtrInx::try_into_usize(p)?)? else {
            return None;
        };
        Some((*generation, t))
    }

    fn get_inx_mut(&mut self, p: <P as Ptr>::Inx) -> Option<(<P as Ptr>::Gen, &mut T)> {
        let Allocated(generation, t) = self.m.get_mut(PtrInx::try_into_usize(p)?)? else {
            return None;
        };
        Some((*generation, t))
    }

    fn find_first_inx_ptr(&self) -> Option<P> {
        for inx in self.nziter() {
            if let Allocated(generation, _) = self.m.get(inx).unwrap() {
                return Some(P::_from_raw(from_checked_raw::<P>(inx), *generation));
            }
        }
        None
    }

    fn find_last_inx_ptr(&self) -> Option<P> {
        for inx in self.nziter().into_iter().rev() {
            if let Allocated(generation, _) = self.m.get(inx).unwrap() {
                return Some(P::_from_raw(from_checked_raw::<P>(inx), *generation));
            }
        }
        None
    }

    fn advancer_inx(&self, inx: <P as Ptr>::Inx, rev: bool) -> Self::PtrAdvancer {
        self.internal_advancer_inx(inx, rev)
    }

    fn invalidate(&mut self, p: P) -> InvalidationResult<P> {
        let Some(inx) = PtrInx::try_into_usize(p.inx()) else {
            return InvalidationResult::InvalidPtr;
        };
        let Some(Allocated(generation, _)) = self.m.get_mut(inx) else {
            return InvalidationResult::InvalidPtr;
        };
        if *generation != p.generation() {
            return InvalidationResult::InvalidPtr;
        }
        // preserve generations
        InvalidationResult::Success(p)
    }

    fn drain(&mut self) -> impl Iterator<Item = InvalidationOption<(P, T)>> {
        self.internal_drain()
    }

    fn remove(&mut self, p: P) -> InvalidationResult<T> {
        match self.remove_internal(p.inx(), Some(p.generation())) {
            Some((_, t)) => InvalidationResult::Success(t),
            None => InvalidationResult::InvalidPtr,
        }
    }

    fn remove_inx(&mut self, p: P::Inx) -> InvalidationResult<(P::Gen, T)> {
        match self.remove_internal(p, None) {
            Some((generation, t)) => InvalidationResult::Success((generation, t)),
            None => InvalidationResult::InvalidPtr,
        }
    }

    fn clear(&mut self) -> InvalidationOption<()> {
        // REF(zero_before_drop)
        self.len = 0;
        self.m.clear();
        InvalidationOption::Success(())
    }

    fn compress_with<F: FnMut(P, &mut T, P)>(
        &mut self,
        _reset_generation: bool,
        mut map: F,
    ) -> InvalidationOption<()> {
        // preserve generations

        // we are moving from `j` to `i`
        let mut i = NonZeroUsize::new(1).unwrap();
        for j in self.nziter() {
            let Allocated(generation, t) = self.m.get_mut(j).unwrap() else {
                continue;
            };
            let generation = *generation;
            // REF(map_before_moving)
            map(
                Ptr::_from_raw(from_checked_raw::<P>(j), generation),
                t,
                Ptr::_from_raw(from_checked_raw::<P>(i), generation),
            );
            if i != j {
                let entry = mem::replace(
                    self.m.get_mut(j).unwrap(),
                    // this will be overwritten or dropped
                    Free,
                );
                // the slot at `i` is always free at this point
                let _ = mem::replace(self.m.get_mut(i).unwrap(), entry);
            }
            i = i.checked_add(1).unwrap();
        }
        // In this case we do actually want to pop off free end slots, because the
        // compression should also occur with direct insertion indexes reducing in size
        // (or at least compression should be rare), and we want to reduce the number of
        // slots that advancers need to traverse
        self.pop_free_end_slots(usize::MAX);
        InvalidationOption::Success(())
    }
}

impl<P: Ptr, T, B: ArenaBacking> DisjointableArenaTrait<P, T> for DirectArena<P, T, B> {
    fn get_disjoint_inx_mut<const N: usize>(
        &mut self,
        indices: [<P as Ptr>::Inx; N],
    ) -> Result<[(<P as Ptr>::Gen, &mut T); N], GetDisjointMutError> {
        // check for PtrInx truncation, this is a no-op in the default case
        for inx in indices {
            if PtrInx::try_into_usize(inx).is_none() {
                return Err(GetDisjointMutError::IndexOutOfBounds);
            }
        }
        let indices = indices.map(|inx| PtrInx::try_into_usize(inx).unwrap());
        match self.m.get_disjoint_mut(indices) {
            Ok(a) => {
                for slot in &a {
                    if matches!(slot, Free) {
                        return Err(GetDisjointMutError::IndexOutOfBounds);
                    }
                }
                Ok(a.map(|slot| {
                    let Allocated(generation, t) = slot else {
                        unreachable!()
                    };
                    (*generation, t)
                }))
            }
            Err(GetDisjointMutError::IndexOutOfBounds) => {
                Err(GetDisjointMutError::IndexOutOfBounds)
            }
            Err(GetDisjointMutError::OverlappingIndices) => {
                Err(GetDisjointMutError::OverlappingIndices)
            }
        }
    }

    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (P, &'a mut T)>
    where
        T: 'a,
    {
        self.internal_iter_mut()
    }
}

impl<P: Ptr, T, B: ArenaBacking> CompactArenaTrait<P, T> for DirectArena<P, T, B> {}

impl<P: Ptr, T, B: ArenaBacking> ArenaCloneFromWith<P, T> for DirectArena<P, T, B> {
    fn clone_from_with<U, A: CompactArenaTrait<P, U>, F: FnMut(P, &U) -> T>(
        &mut self,
        source: &A,
        mut map: F,
    ) -> Result<(), ReallocationError> {
        let Some(last) = source.find_last_inx_ptr() else {
            // no entries

            // same as `clear`
            // REF(zero_before_drop)
            self.len = 0;
            self.m.clear();
            return Ok(());
        };
        // REF(careful_index_checking)
        let Some(raw_last) = P::Inx::try_into_usize(last.inx()) else {
            return Err(ReallocationError::AllocError);
        };
        if raw_last.get() > self.capacity() {
            // max capacity is tested here
            self.reallocate_min_capacity(raw_last.get())?;
        }
        // start modifying after the fallible points that we can reasonably deal with
        // REF(zero_before_drop)
        self.len = 0;
        self.m.clear();
        // maintain invariants even with bad behavior, and increment `len` at the right
        // moment. The last thing pushed is always an allocated slot, so nothing has to
        // be popped off the end afterwards, and a `map` that unwinds can only leave
        // behind free slots that are valid to keep.
        let mut adv = source.advancer();
        while let Some(p) = adv.advance(source) {
            let Some(raw) = P::Inx::try_into_usize(p.inx()) else {
                unreachable!();
            };
            if raw.get() <= self.m.len() {
                // the advancer is out of order
                unreachable!();
            }
            // insert free entries in gaps
            while raw.get() - 1 > self.m.len() {
                if self.m.push_within_capacity(Free).is_err() {
                    unreachable!();
                }
            }
            let Some(u) = source.get(p) else {
                unreachable!();
            };
            let t = map(p, u);
            if self
                .m
                .push_within_capacity(Allocated(p.generation(), t))
                .is_err()
            {
                unreachable!();
            }
            self.len = self.len.wrapping_add(1);
        }
        Ok(())
    }
}

// REF(insertion_idempotency) We rely on cancelling and retrying an insertion
// without doing any mutable things to be idempotent

/// The [ArenaDirectInsertTrait::DirectInsertionEntry] of [DirectArena].
/// Dropping this cancels the insertion.
pub struct ArenaDirectInsertEntry<'a, P: Ptr, T, B: ArenaBacking> {
    this: &'a mut DirectArena<P, T, B>,
    // this either points to a free slot or to free capacity
    raw: NonZeroUsize,
    generation: P::Gen,
}

impl<'a, P: Ptr, T, B: ArenaBacking> ArenaDirectInsertEntryTrait<'a, P, T>
    for ArenaDirectInsertEntry<'a, P, T, B>
{
    fn insert(self, t: T) {
        let this = self.this;
        let raw = self.raw;
        // push up through the allocation that must have been prepared for us
        while this.m.len() < raw.get() {
            this.m.push_within_capacity(Free).ok().unwrap();
        }
        // `Free` has no drop code
        *this.m.get_mut(raw).unwrap() = Allocated(self.generation, t);
        // safe by `isize::MAX` limits, the slots can never be ZSTs
        this.len = this.len.wrapping_add(1);
    }
}

impl<P: Ptr, T, B: ArenaBacking> ArenaDirectInsertTrait<P, T> for DirectArena<P, T, B> {
    type DirectInsertionEntry<'a>
        = ArenaDirectInsertEntry<'a, P, T, B>
    where
        Self: 'a;

    fn direct_insert_within_capacity(
        &mut self,
        p: P,
    ) -> Result<Self::DirectInsertionEntry<'_>, DirectInsertionError> {
        let Some(raw) = PtrInx::try_into_usize(p.inx()) else {
            return Err(DirectInsertionError::NotWithinCapacity);
        };
        if raw.get() > self.capacity() {
            return Err(DirectInsertionError::NotWithinCapacity);
        }
        if let Some(Allocated(..)) = self.m.get(raw) {
            Err(DirectInsertionError::ExistingElementAtIndex)
        } else {
            Ok(ArenaDirectInsertEntry {
                this: self,
                raw,
                generation: p.generation(),
            })
        }
    }
}
