use core::slice::GetDisjointMutError;

use crate::{
    Arena, InvalidationResult,
    arena::{ArenaBacking, InternalEntry::*},
    traits::{ArenaTrait, Ptr},
    utils::{NonZeroInxGenericStack, PtrGen, PtrInx},
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

    fn reallocate_min_capacity(
        &mut self,
        min_capacity: usize,
    ) -> Result<(), crate::utils::AllocError> {
        todo!()
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
                for entry in &a {
                    if matches!(entry, Free(_)) {
                        return Err(GetDisjointMutError::IndexOutOfBounds);
                    }
                }
                Ok(a.map(|entry| {
                    let Allocated(generation, t) = entry else {
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

    fn remove(&mut self, p: P) -> Option<T> {
        todo!()
    }

    fn clear(&mut self) {
        todo!()
    }
}
