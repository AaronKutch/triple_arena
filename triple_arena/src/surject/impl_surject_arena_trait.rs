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
            elements: ChainArena::new(),
            shared_vals: Arena::new(),
        }
    }

    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError> {
        Self::with_min_capacity_separated(min_capacity, min_capacity)
    }

    fn capacity(&self) -> usize {
        self.elements.capacity()
    }

    fn max_capacity(&self) -> Option<usize> {
        self.elements.max_capacity()
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), ReallocationError> {
        self.shared_vals.reallocate_min_capacity(min_capacity)?;
        self.elements.reallocate_min_capacity(min_capacity)
    }

    fn len(&self) -> usize {
        self.elements.len()
    }

    /// Note that `self.len() == 0` if and only if `self.len_shared() == 0`
    fn is_empty(&self) -> bool {
        self.shared_vals.len() == 0
    }

    fn singular_generation(&self) -> Option<<P as Ptr>::Gen> {
        Some(self.generation())
    }

    fn get_inx(&self, p: <P as Ptr>::Inx) -> Option<(<P as Ptr>::Gen, &T)> {
        self.elements
            .get_inx(p)
            .map(|(generation, element)| (generation, &element.t))
    }

    fn get_inx_mut(&mut self, p: <P as Ptr>::Inx) -> Option<(<P as Ptr>::Gen, &mut T)> {
        self.elements
            .get_inx_mut(p)
            .map(|(generation, element)| (generation, &mut element.t))
    }

    fn find_first_inx_ptr(&self) -> Option<P> {
        self.elements.find_first_inx_ptr()
    }

    fn find_last_inx_ptr(&self) -> Option<P> {
        self.elements.find_last_inx_ptr()
    }

    fn advancer_inx(&self, inx: <P as Ptr>::Inx, rev: bool) -> Self::PtrAdvancer {
        self.internal_advancer_inx(inx, rev)
    }

    fn invalidate(&mut self, p: P) -> InvalidationResult<P> {
        self.elements.invalidate(p)
    }

    /// Note that this drains one whole surject at a time, see
    /// [drain_combined](SurjectArena::drain_combined)
    fn drain(&mut self) -> impl Iterator<Item = InvalidationOption<(P, T)>> {
        self.drain_combined().map(|o| o.map(|(p, t, _)| (p, t)))
    }

    /// Note that this drops the shared value if `p` was the last element of its
    /// surject, see [remove_element](SurjectArena::remove_element)
    fn remove(&mut self, p: P) -> InvalidationResult<T> {
        self.remove_element(p).map(|(t, _)| t)
    }

    /// Note that this drops the shared value if `p` was the last element of its
    /// surject, see [remove_element_inx](SurjectArena::remove_element_inx)
    fn remove_inx(&mut self, p: <P as Ptr>::Inx) -> InvalidationResult<(<P as Ptr>::Gen, T)> {
        self.remove_element_inx(p)
            .map(|(generation, t, _)| (generation, t))
    }

    fn clear(&mut self) -> InvalidationOption<()> {
        self.shared_vals.clear().allow();
        self.elements.clear()
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
        self.elements
            .get_disjoint_inx_mut(indices)
            .map(|a| a.map(|(generation, element)| (generation, &mut element.t)))
    }

    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (P, &'a mut T)>
    where
        T: 'a,
    {
        self.elements
            .iter_mut()
            .map(|(p, element)| (p, &mut element.t))
    }
}

impl<P: Ptr, T, S, B: ArenaBacking> CompactArenaTrait<P, T> for SurjectArena<P, T, S, B> {}
