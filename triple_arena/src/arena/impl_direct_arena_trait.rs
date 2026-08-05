use core::{mem, num::NonZeroUsize, slice::GetDisjointMutError};

use crate::{
    DirectArena, InvalidationOption, InvalidationResult, direct_arena_iterators,
    errors::{AllocError, DirectInsertionError, ReallocationError},
    traits::{
        Advancer, ArenaCloneFromWith, ArenaDirectInsertEntryTrait, ArenaDirectInsertTrait,
        ArenaTrait, CompactArenaTrait, Ptr,
    },
    utils::{
        DirectSlot::*,
        from_checked_raw,
        traits::{ArenaBacking, NonZeroInxGenericStack, PtrGen, PtrInx},
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
        self.m.capacity()
    }

    fn max_capacity(&self) -> Option<usize> {
        self.m.max_capacity()
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), ReallocationError> {
        // so that capacity on the end is not used up by unallocated slots
        self.canonicalize_free_slots();
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
            Some(x) => InvalidationResult::Success(x),
            None => InvalidationResult::InvalidPtr,
        }
    }

    fn clear(&mut self) -> InvalidationOption<()> {
        self.m.clear();
        self.len = 0;
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
            if i == j {
                // optimize for the front part being compressed already
                if let Allocated(old_gen, t) = self.m.get_mut(j).unwrap() {
                    map(
                        Ptr::_from_raw(from_checked_raw::<P>(j), *old_gen),
                        t,
                        Ptr::_from_raw(from_checked_raw::<P>(i), *old_gen),
                    );
                    i = i.checked_add(1).unwrap();
                }
                continue;
            }
            let entry = mem::replace(
                self.m.get_mut(j).unwrap(),
                // this will be overwritten or dropped
                Free,
            );
            if let Allocated(old_gen, mut t) = entry {
                map(
                    Ptr::_from_raw(from_checked_raw::<P>(j), old_gen),
                    &mut t,
                    Ptr::_from_raw(from_checked_raw::<P>(i), old_gen),
                );
                let _ = mem::replace(self.m.get_mut(i).unwrap(), Allocated(old_gen, t));
                i = i.checked_add(1).unwrap();
            }
        }
        // remove free slots off the end
        self.canonicalize_free_slots();
        InvalidationOption::Success(())
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

            // same as `clear` but the generation is copied over
            self.m.clear();
            self.len = 0;
            return Ok(());
        };
        // REF(careful_general_clone)
        let e = Err(ReallocationError::BeyondMaxCapacity);
        let Some(raw_last) = P::Inx::try_into_usize(last.inx()) else {
            return e;
        };
        if raw_last.get() > self.m.capacity() {
            // max capacity is tested here
            self.reallocate_min_capacity(raw_last.get())?;
        }
        // start modifying after the fallible points that we can reasonably deal with
        self.m.clear();
        self.len = 0;
        // maintain invariants even with bad behavior, increment `len` at the right
        // moment and always call `canonicalize_free_slots` after this point
        let res = 'outer: {
            let mut adv = source.advancer();
            while let Some(p) = adv.advance(source) {
                let Some(raw) = P::Inx::try_into_usize(p.inx()) else {
                    break 'outer e;
                };
                if raw.get() <= self.m.len() {
                    // the advancer is out of order
                    break 'outer e;
                }
                // insert free entries in gaps
                while raw.get() - 1 > self.m.len() {
                    if self.m.push_within_capacity(Free).is_err() {
                        break 'outer e;
                    }
                }
                let Some(u) = source.get(p) else {
                    break 'outer e;
                };
                let t = map(p, u);
                if self
                    .m
                    .push_within_capacity(Allocated(p.generation(), t))
                    .is_err()
                {
                    break 'outer e;
                }
                self.len = self.len.wrapping_add(1);
            }
            Ok(())
        };
        self.canonicalize_free_slots();
        res
    }

    fn clone_general<
        U,
        A: CompactArenaTrait<P, U>,
        Adv: Advancer<A, Item = P>,
        F: FnMut(P, &U, P) -> T,
    >(
        &mut self,
        reset_generation: bool,
        source: &A,
        mut advancer: Adv,
        mut map: F,
    ) -> Result<InvalidationOption<()>, ReallocationError> {
        // need this to follow the `is_empty` generation handling correctly
        if source.is_empty() {
            self.m.clear();
            self.len = 0;
            return Ok(InvalidationOption::Success(()));
        }
        // REF(careful_general_clone)
        let e = Err(ReallocationError::BeyondMaxCapacity);

        // start modifying after the fallible points that we can reasonably deal with
        self.m.clear();
        self.len = 0;

        // we don't have a global generation to set, but we can still select the new
        // slot generations
        let (new_gen, res) = if reset_generation {
            (P::Gen::two(), InvalidationOption::Success(()))
        } else {
            if let Some(next) = source.singular_generation() {
                // not `self.inc_generation()`, need to get the incremented source generation
                let tmp = P::Gen::generational_inc(next);
                if tmp.1 {
                    // this is an absurdly qualified corner case that doesn't happen with any other
                    // operation on `DirectArena`s, but folling the logic naturally leads to this
                    // being the case
                    (tmp.0, InvalidationOption::GenerationOverflow(()))
                } else {
                    (tmp.0, InvalidationOption::Success(()))
                }
            } else {
                (P::Gen::two(), InvalidationOption::Success(()))
            }
        };

        // maintain invariants even with bad behavior, increment `len` at the right
        // moment and always maintain a canonical state with kept invariants
        let mut i = NonZeroUsize::new(1).unwrap();
        while let Some(p) = advancer.advance(source) {
            let Some(inx_new) = P::Inx::try_from_usize(i) else {
                return e;
            };
            let p_new = P::_from_raw(inx_new, new_gen);

            let Some(u) = source.get(p) else {
                return e;
            };
            let t = map(p, u, p_new);

            // We push all Allocated entries as part of this being a compression function.
            // It is safe to return from the function here immediately on error.
            self.m.push_reallocating(Allocated(new_gen, t))?;
            // immediately afterwards
            self.len = self.len.wrapping_add(1);
            i = i.checked_add(1).unwrap();
        }
        Ok(res)
    }
}

// REF(insertion_idempotency) We rely on cancelling and retrying an insertion
// without doing any mutable things to be idempotent

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
        while this.m.len() < raw.get() {
            this.m.push(Free);
        }
        *this.m.get_mut(raw).unwrap() = Allocated(self.generation, t);
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
        if raw.get() > self.m.capacity() {
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
