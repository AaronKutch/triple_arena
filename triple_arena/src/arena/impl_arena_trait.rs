use core::{mem, slice::GetDisjointMutError};

use crate::{
    Arena, InvalidationResult,
    arena::{
        ArenaBacking,
        InternalSlot::{self, *},
    },
    traits::{ArenaInsertTrait, ArenaTrait, Ptr},
    utils::{AllocError, NonZeroInxGenericStack, PtrGen, PtrInx},
};

impl<P: Ptr, T, B: ArenaBacking> ArenaTrait<P, T> for Arena<P, T, B> {
    fn new() -> Self {
        Self {
            len: 0,
            m: B::Stack::new(),
            freelist_root: None,
            generation: PtrGen::two(),
        }
    }

    fn capacity(&self) -> usize {
        self.m.len()
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

    fn generation(&self) -> <P as Ptr>::Gen {
        self.generation
    }

    fn set_generation(&mut self, new_gen: P::Gen) {
        self.generation = new_gen;
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

    fn clear(&mut self) {
        self.m.clear();
    }

    fn clone_from_with<U, A: ArenaTrait<P, U>, F: FnMut(P, &U) -> T>(
        &mut self,
        source: &A,
        map: F,
    ) -> Result<(), AllocError> {
        //if self.capacity() < sour
        todo!()
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
