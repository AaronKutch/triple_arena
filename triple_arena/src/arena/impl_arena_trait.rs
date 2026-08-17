use core::{cmp::min, mem, num::NonZeroUsize, slice::GetDisjointMutError};

use crate::{
    Arena, InvalidationOption, InvalidationResult,
    arena::CompactArenaTrait,
    arena_iterators,
    errors::{AllocError, NotWithinCapacityError, ReallocationError},
    traits::{
        Advancer, ArenaCloneFromWith, ArenaInsertEntryTrait, ArenaInsertTrait, ArenaTrait, Ptr,
    },
    utils::{
        ArenaSlot::*,
        from_checked_ptr, from_checked_raw,
        traits::{
            ArenaBacking, NonZeroInxGenericStack, NonZeroInxGenericStackPushEntryTrait, PtrGen,
            PtrInx,
        },
    },
};

impl<P: Ptr, T, B: ArenaBacking> ArenaTrait<P, T> for Arena<P, T, B> {
    type PtrAdvancer = arena_iterators::PtrAdvancer<P>;

    fn new() -> Self {
        Self {
            len: 0,
            m: NonZeroInxGenericStack::new(),
            freelist_root: None,
            generation: PtrGen::two(),
        }
    }

    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError> {
        Ok(Self {
            len: 0,
            m: NonZeroInxGenericStack::with_min_capacity(min_capacity)?,
            freelist_root: None,
            generation: PtrGen::two(),
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
        // so that capacity on the end is not used up by unallocated slots, and just fix
        // up the freelist if this function was called under any circumstance, it is
        // understood that it is a `O(n)` operation anyway.
        self.canonicalize_free_list();
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
        Some(self.generation())
    }

    fn get_inx(&self, p: <P as Ptr>::Inx) -> Option<(<P as Ptr>::Gen, &T)> {
        let Allocated(generation, t) = self.m.get(PtrInx::try_into_usize(p)?)? else {
            return None;
        };
        Some((*generation, t))
    }

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
                    if matches!(slot, Free(_)) {
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

    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (P, &'a mut T)>
    where
        T: 'a,
    {
        self.internal_iter_mut()
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
        let tmp = PtrGen::generational_inc(self.generation);
        self.generation = tmp.0;
        *generation = self.generation;
        let p = P::_from_raw(p.inx(), *generation);
        if tmp.1 {
            InvalidationResult::GenerationOverflow(p)
        } else {
            InvalidationResult::Success(p)
        }
    }

    fn drain(&mut self) -> impl Iterator<Item = InvalidationOption<(P, T)>> {
        self.internal_drain()
    }

    fn remove(&mut self, p: P) -> InvalidationResult<T> {
        self.remove_internal(p.inx(), Some(p.generation()), true)
            .map(|(_, t)| t)
    }

    fn remove_inx(&mut self, p: P::Inx) -> InvalidationResult<(P::Gen, T)> {
        self.remove_internal(p, None, true)
    }

    fn clear(&mut self) -> InvalidationOption<()> {
        let was_empty = self.is_empty();
        // always do these steps to make sure the freelist is clear (make it canonical,
        // may be logically empty but still have a messed up freelist)
        // REF(zero_before_drop)
        self.len = 0;
        self.freelist_root = None;
        self.m.clear();
        if was_empty {
            InvalidationOption::Success(())
        } else {
            // only if there was any element
            self.inc_generation()
        }
    }

    fn compress_with<F: FnMut(P, &mut T, P)>(
        &mut self,
        reset_generation: bool,
        mut map: F,
    ) -> InvalidationOption<()> {
        let res = if reset_generation {
            self.generation = P::Gen::two();
            InvalidationOption::Success(())
        } else {
            // follow what `clear` does, and let the rest of the function canonicalize
            if self.is_empty() {
                InvalidationOption::Success(())
            } else {
                self.inc_generation()
            }
        };
        let new_gen = self.generation;
        // we are moving from `j` to `i`
        let mut i = NonZeroUsize::new(1).unwrap();
        for j in self.nziter() {
            if i == j {
                // optimize for the front part being compressed already
                if let Allocated(old_gen, t) = self.m.get_mut(j).unwrap() {
                    map(
                        Ptr::_from_raw(from_checked_raw::<P>(j), *old_gen),
                        t,
                        Ptr::_from_raw(from_checked_raw::<P>(i), new_gen),
                    );
                    *old_gen = new_gen;
                    i = i.checked_add(1).unwrap();
                }
                continue;
            }
            let entry = mem::replace(
                self.m.get_mut(j).unwrap(),
                // this will be overwritten or dropped
                Free(P::invalid().inx()),
            );
            if let Allocated(old_gen, mut t) = entry {
                map(
                    Ptr::_from_raw(from_checked_raw::<P>(j), old_gen),
                    &mut t,
                    Ptr::_from_raw(from_checked_raw::<P>(i), new_gen),
                );
                let _ = mem::replace(self.m.get_mut(i).unwrap(), Allocated(new_gen, t));
                i = i.checked_add(1).unwrap();
            }
        }
        // remove free slots off the end
        for inx in self.nziter().into_iter().rev() {
            if let Free(_) = self.m.get(inx).unwrap() {
                self.m.pop();
            } else {
                break;
            }
        }
        self.freelist_root = None;
        res
    }
}

impl<P: Ptr, T, B: ArenaBacking> CompactArenaTrait<P, T> for Arena<P, T, B> {}

impl<P: Ptr, T, B: ArenaBacking> ArenaCloneFromWith<P, T> for Arena<P, T, B> {
    fn clone_from_with<U, A: CompactArenaTrait<P, U>, F: FnMut(P, &U) -> T>(
        &mut self,
        source: &A,
        mut map: F,
    ) -> Result<(), ReallocationError> {
        let Some(last) = source.find_last_inx_ptr() else {
            // no entries

            // same as `clear` but the generation is copied over
            // REF(zero_before_drop)
            self.len = 0;
            self.freelist_root = None;
            self.generation = source.singular_generation().unwrap_or(P::Gen::two());
            self.m.clear();
            return Ok(());
        };
        // REF(careful_index_checking) Be aware that `source` may not be linear and the
        // `P`s coming from it can't be relied on. We have to check here because the
        // `reallocate_min_capacity` may not be called to check for us, and `AllocError`
        // is the correct error to returned based on the logic of standard
        // `ArenaTrait::reallocate_min_capacity`.
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
        self.freelist_root = None;
        self.generation = source.singular_generation().unwrap_or(P::Gen::two());
        self.m.clear();
        // maintain invariants even with bad behavior, increment `len` at the right
        // moment and always call `canonicalize_free_list` after this point
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
                if self
                    .m
                    .push_within_capacity(Free(P::invalid().inx()))
                    .is_err()
                {
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
        // has to be done with reverse iteration anyways
        self.canonicalize_free_list();
        Ok(())
    }
}

// REF(insertion_idempotency) We rely on cancelling and retrying an insertion
// without doing any mutable things to be idempotent

pub struct ArenaInsertEntry<'a, P: Ptr, T, B: ArenaBacking> {
    this: &'a mut Arena<P, T, B>,
    // this either points to a free slot or to one past `this.m.len()` where an allocation can be
    // pushed successfully
    p: P,
}

impl<'a, P: Ptr, T, B: ArenaBacking> ArenaInsertEntryTrait<'a, P, T>
    for ArenaInsertEntry<'a, P, T, B>
{
    fn ptr(&self) -> P {
        self.p
    }

    fn insert(self, t: T) {
        let this = self.this;
        let inx = from_checked_ptr::<P>(self.p.inx());
        let generation = self.p.generation();
        if let Some(slot) = this.m.get_mut(inx) {
            let Free(next) = mem::replace(slot, Allocated(generation, t)) else {
                unreachable!()
            };
            if next == self.p.inx() {
                // end of freelist
                this.freelist_root = None;
            } else {
                // move to next node in the freelist
                this.freelist_root = Some(next);
            }
        } else {
            // freelist remains unset
            this.m
                .push_within_capacity(Allocated(this.generation, t))
                .ok()
                .unwrap();
        }
        // safe by `isize::MAX` limits, the slots can never be ZSTs
        this.len = this.len.wrapping_add(1);
    }
}

impl<P: Ptr, T, B: ArenaBacking> ArenaInsertTrait<P, T> for Arena<P, T, B> {
    type InsertionEntry<'a>
        = ArenaInsertEntry<'a, P, T, B>
    where
        Self: 'a;

    fn insert_within_capacity(&mut self, t: T) -> Result<P, NotWithinCapacityError> {
        let generation = self.generation;
        if let Some(inx) = self.freelist_root {
            let slot = self.m.get_mut(from_checked_ptr::<P>(inx)).unwrap();
            let Free(next) = mem::replace(slot, Allocated(generation, t)) else {
                unreachable!()
            };
            if next == inx {
                // end of freelist
                self.freelist_root = None;
            } else {
                // move to next node in the freelist
                self.freelist_root = Some(next);
            }
            // safe by `isize::MAX` limits, the slots can never be ZSTs
            self.len = self.len.wrapping_add(1);
            Ok(P::_from_raw(inx, generation))
        } else {
            // see if capacity for slots remains, freelist remains unset if we push just
            // one thing
            let entry = self.m.entry_push_within_capacity()?;
            let raw_inx = entry.inx();
            if let Some(inx) = P::Inx::try_from_usize(raw_inx) {
                entry.push(Allocated(self.generation, t));
                self.len = self.len.wrapping_add(1);
                Ok(P::_from_raw(inx, generation))
            } else {
                drop(entry);
                Err(NotWithinCapacityError)
            }
        }
    }

    fn entry_insert_within_capacity(
        &mut self,
    ) -> Result<Self::InsertionEntry<'_>, NotWithinCapacityError> {
        let generation = self.generation;
        if let Some(inx) = self.freelist_root {
            Ok(ArenaInsertEntry {
                this: self,
                p: Ptr::_from_raw(inx, generation),
            })
        } else if self.m.len() < self.m.capacity() {
            // `push_within_capacity` would succeed, but check that the P::Inx conversion
            // works
            if let Some(inx) =
                P::Inx::try_from_usize(NonZeroUsize::new(self.m.len().wrapping_add(1)).unwrap())
            {
                Ok(ArenaInsertEntry {
                    this: self,
                    p: Ptr::_from_raw(inx, generation),
                })
            } else {
                Err(NotWithinCapacityError)
            }
        } else {
            Err(NotWithinCapacityError)
        }
    }
}
