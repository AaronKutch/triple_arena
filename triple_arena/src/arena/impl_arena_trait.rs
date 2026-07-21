use core::{mem, num::NonZeroUsize, slice::GetDisjointMutError};

use crate::{
    Arena, InvalidationOption, InvalidationResult,
    arena::{
        ArenaBacking,
        InternalSlot::{self, *},
    },
    arena_iterators,
    traits::{Advancer, ArenaInsertTrait, ArenaTrait, Ptr, SingularGenerationArena},
    utils::{AllocError, NonZeroInxGenericStack, PtrGen, PtrInx},
};

impl<P: Ptr, T, B: ArenaBacking> SingularGenerationArena<P> for Arena<P, T, B> {
    fn singular_generation(&self) -> <P as Ptr>::Gen {
        self.generation
    }
}

impl<P: Ptr, T, B: ArenaBacking> ArenaTrait<P, T> for Arena<P, T, B> {
    type PtrAdvancer = arena_iterators::PtrAdvancer<P>;

    fn new() -> Self {
        Self {
            len: 0,
            m: B::Stack::new(),
            freelist_root: None,
            generation: PtrGen::two(),
        }
    }

    fn capacity(&self) -> usize {
        self.m.capacity()
    }

    fn max_capacity(&self) -> Option<usize> {
        self.m.max_capacity()
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), AllocError> {
        // so that capacity on the end is not used up by unallocated slots, and just fix
        // up the freelist if this function was called under any circumstance, it is
        // understood that it is a `O(n)` operation anyway.
        self.canonicalize_free_list();
        self.m.reallocate_min_capacity(min_capacity)
    }

    fn len(&self) -> usize {
        self.len
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

    fn find_first_ptr(&self) -> Option<P> {
        for inx in self.nziter() {
            if let Allocated(generation, _) = self.m.get(inx).unwrap() {
                return Some(P::_from_raw(Self::from_checked(inx), *generation));
            }
        }
        None
    }

    fn find_last_ptr(&self) -> Option<P> {
        for inx in self.nziter().into_iter().rev() {
            if let Allocated(generation, _) = self.m.get(inx).unwrap() {
                return Some(P::_from_raw(Self::from_checked(inx), *generation));
            }
        }
        None
    }

    fn ordered_advancer(&self, inx: <P as Ptr>::Inx, rev: bool) -> Self::PtrAdvancer {
        arena_iterators::PtrAdvancer {
            inx: Some(inx),
            rev,
        }
    }

    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (P, &'a mut T)>
    where
        T: 'a,
    {
        let adv = self.advancer();
        arena_iterators::IterMut { arena: self, adv }
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

    fn remove(&mut self, p: P) -> InvalidationResult<T> {
        self.remove_internal(p.inx(), Some(p.generation()), true)
    }

    fn clear(&mut self) -> InvalidationOption<()> {
        self.m.clear();
        self.len = 0;
        self.freelist_root = None;
        self.inc_generation()
    }

    fn clone_from_with<
        U,
        A: ArenaTrait<P, U> + SingularGenerationArena<P>,
        F: FnMut(P, &U) -> T,
    >(
        &mut self,
        source: &A,
        mut map: F,
    ) -> Result<(), AllocError> {
        let Some(last) = source.find_last_ptr() else {
            // no entries
            self.clear();
            return Ok(());
        };
        // Be aware that `source` may not be linear and the `P`s coming from it can't be
        // relied on, if this happens just return the `AllocError` which is logical
        // anyways
        let Some(raw_last) = P::Inx::try_into_usize(last.inx()) else {
            return Err(AllocError);
        };
        if raw_last.get() > self.capacity() {
            self.reallocate_min_capacity(raw_last.get())?;
        }
        // start modifying after the fallible points that we can reasonably deal with
        self.m.clear();
        self.len = 0;
        self.generation = source.singular_generation();
        // maintain invariants even with bad behavior, increment `len` at the right
        // moment and always call `canonicalize_free_list` after this point
        let res = 'outer: {
            let mut adv = source.advancer();
            while let Some(p) = adv.advance(source) {
                let Some(raw) = P::Inx::try_into_usize(p.inx()) else {
                    break 'outer Err(AllocError);
                };
                if raw.get() <= self.m.len() {
                    // the advancer is out of order
                    break 'outer Err(AllocError);
                }
                // insert free entries in gaps
                while raw.get() - 1 > self.m.len() {
                    if self
                        .m
                        .push_within_capacity(Free(P::invalid().inx()))
                        .is_err()
                    {
                        break 'outer Err(AllocError);
                    }
                }
                let Some(u) = source.get(p) else {
                    break 'outer Err(AllocError);
                };
                let t = map(p, u);
                if self
                    .m
                    .push_within_capacity(Allocated(p.generation(), t))
                    .is_err()
                {
                    break 'outer Err(AllocError);
                }
                self.len = self.len.wrapping_add(1);
            }
            Ok(())
        };
        // has to be done with reverse iteration anyways
        self.canonicalize_free_list();
        res
    }

    fn compress_with<F: FnMut(P, &mut T, P)>(&mut self, mut map: F) -> InvalidationOption<()> {
        let res = self.inc_generation();
        let new_gen = self.generation;
        // we are moving from `j` to `i`
        let mut i = NonZeroUsize::new(1).unwrap();
        for j in self.nziter() {
            let entry = mem::replace(
                self.m.get_mut(j).unwrap(),
                // this will be overwritten or dropped
                Free(P::invalid().inx()),
            );
            if let Allocated(old_gen, mut t) = entry {
                map(
                    Ptr::_from_raw(Self::from_checked(j), old_gen),
                    &mut t,
                    Ptr::_from_raw(Self::from_checked(i), new_gen),
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

impl<P: Ptr, T, B: ArenaBacking> ArenaInsertTrait<P, T> for Arena<P, T, B> {
    fn insert_within_capacity(&mut self, t: T) -> Result<(P, &mut T), T> {
        let generation = self.generation;
        if let Some(inx) = self.freelist_root {
            let slot = self.m.get_mut(Self::into_checked(inx)).unwrap();
            let InternalSlot::Free(next) = mem::replace(slot, Allocated(generation, t)) else {
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
            let InternalSlot::Allocated(_, t) = slot else {
                unreachable!()
            };
            Ok((Ptr::_from_raw(inx, generation), t))
        } else {
            // see if capacity for slots remains, freelist remains unset if we push just
            // one thing
            match self
                .m
                .push_within_capacity(InternalSlot::Allocated(self.generation, t))
            {
                // TODO Polonius cleans this up
                Ok((raw_inx, _)) => {
                    if let Some(inx) = P::Inx::try_from_usize(raw_inx) {
                        let Some(InternalSlot::Allocated(_, t)) = self.m.get_mut(raw_inx) else {
                            unreachable!()
                        };
                        self.len = self.len.wrapping_add(1);
                        Ok((<P as Ptr>::_from_raw(inx, generation), t))
                    } else {
                        // undo
                        let InternalSlot::Allocated(_, t) = self.m.pop().unwrap() else {
                            unreachable!()
                        };
                        Err(t)
                    }
                }
                Err(slot) => {
                    let InternalSlot::Allocated(_, t) = slot else {
                        unreachable!()
                    };
                    Err(t)
                }
            }
        }
    }
}
