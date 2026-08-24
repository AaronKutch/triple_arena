use core::slice::GetDisjointMutError;

use crate::{
    Arena, ChainArena, InvalidationOption, InvalidationResult, SurjectArena,
    errors::{AllocError, ReallocationError},
    surject_iterators,
    traits::{ArenaTrait, CompactArenaTrait, DisjointableArenaTrait, Ptr},
    utils::traits::ArenaBacking,
};

impl<P: Ptr, T, S, B: ArenaBacking> ArenaTrait<P, T> for SurjectArena<P, T, S, B> {
    type PtrAdvancer = surject_iterators::PtrAdvancer<P>;

    fn new() -> Self {
        Self {
            keys: ChainArena::new(),
            vals: Arena::new(),
        }
    }

    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError> {
        Self::with_min_capacity_separated(min_capacity, min_capacity)
    }

    fn capacity(&self) -> usize {
        self.keys.capacity()
    }

    fn max_capacity(&self) -> Option<usize> {
        self.keys.max_capacity()
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), ReallocationError> {
        self.vals.reallocate_min_capacity(min_capacity)?;
        self.keys.reallocate_min_capacity(min_capacity)
    }

    fn len(&self) -> usize {
        self.keys.len()
    }

    fn singular_generation(&self) -> Option<<P as Ptr>::Gen> {
        Some(self.generation())
    }

    fn get_inx(&self, p: <P as Ptr>::Inx) -> Option<(<P as Ptr>::Gen, &T)> {
        self.keys
            .get_inx(p)
            .map(|(generation, key)| (generation, &key.k))
    }

    fn get_inx_mut(&mut self, p: <P as Ptr>::Inx) -> Option<(<P as Ptr>::Gen, &mut T)> {
        self.keys
            .get_inx_mut(p)
            .map(|(generation, key)| (generation, &mut key.k))
    }

    fn find_first_inx_ptr(&self) -> Option<P> {
        self.keys.find_first_inx_ptr()
    }

    fn find_last_inx_ptr(&self) -> Option<P> {
        self.keys.find_last_inx_ptr()
    }

    fn advancer_inx(&self, inx: <P as Ptr>::Inx, rev: bool) -> Self::PtrAdvancer {
        self.internal_advancer_inx(inx, rev)
    }

    fn invalidate(&mut self, p: P) -> InvalidationResult<P> {
        self.keys.invalidate(p)
    }

    fn drain(&mut self) -> impl Iterator<Item = InvalidationOption<(P, T)>> {
        self.drain_combined().map(|o| o.map(|(p, t, _)| (p, t)))
    }

    fn remove(&mut self, p: P) -> InvalidationResult<T> {
        self.remove_key(p).map(|(t, _)| t)
    }

    fn remove_inx(&mut self, p: <P as Ptr>::Inx) -> InvalidationResult<(<P as Ptr>::Gen, T)> {
        self.remove_key_inx(p)
            .map(|(generation, t, _)| (generation, t))
    }

    fn clear(&mut self) -> InvalidationOption<()> {
        self.vals.clear().allow();
        self.keys.clear()
    }

    fn compress_with<F: FnMut(P, &mut T, P)>(
        &mut self,
        reset_generation: bool,
        mut map: F,
    ) -> InvalidationOption<()> {
        todo!();
    }
}

impl<P: Ptr, T, S, B: ArenaBacking> DisjointableArenaTrait<P, T> for SurjectArena<P, T, S, B> {
    fn get_disjoint_inx_mut<const N: usize>(
        &mut self,
        indices: [<P as Ptr>::Inx; N],
    ) -> Result<[(<P as Ptr>::Gen, &mut T); N], GetDisjointMutError> {
        self.keys
            .get_disjoint_inx_mut(indices)
            .map(|a| a.map(|(generation, key)| (generation, &mut key.k)))
    }

    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (P, &'a mut T)>
    where
        T: 'a,
    {
        self.keys.iter_mut().map(|(p, key)| (p, &mut key.k))
    }
}

impl<P: Ptr, T, S, B: ArenaBacking> CompactArenaTrait<P, T> for SurjectArena<P, T, S, B> {}
