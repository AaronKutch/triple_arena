use core::slice::GetDisjointMutError;

use crate::{
    InvalidationOption, InvalidationResult, SimpleOrdArena,
    chain::ChainArena,
    errors::{AllocError, ReallocationError},
    ord_iterators,
    traits::{ArenaTrait, Ptr, SingularGenerationArena},
    utils::traits::ArenaBacking,
};

impl<P: Ptr, T, B: ArenaBacking> ArenaTrait<P, T> for SimpleOrdArena<P, T, B> {
    type PtrAdvancer = ord_iterators::PtrAdvancer<P>;

    fn new() -> Self {
        Self {
            root: P::invalid().inx(),
            first: P::invalid().inx(),
            last: P::invalid().inx(),
            a: ChainArena::new(),
        }
    }

    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError> {
        Ok(Self {
            root: P::invalid().inx(),
            first: P::invalid().inx(),
            last: P::invalid().inx(),
            a: ChainArena::with_min_capacity(min_capacity)?,
        })
    }

    fn capacity(&self) -> usize {
        self.a.capacity()
    }

    fn max_capacity(&self) -> Option<usize> {
        self.a.max_capacity()
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), ReallocationError> {
        self.a.reallocate_min_capacity(min_capacity)
    }

    fn len(&self) -> usize {
        self.a.len()
    }

    fn get_inx(&self, p: <P as Ptr>::Inx) -> Option<(<P as Ptr>::Gen, &T)> {
        self.a
            .get_inx(p)
            .map(|(generation, node)| (generation, &node.t))
    }

    fn get_disjoint_inx_mut<const N: usize>(
        &mut self,
        indices: [<P as Ptr>::Inx; N],
    ) -> Result<[(<P as Ptr>::Gen, &mut T); N], GetDisjointMutError> {
        self.a
            .get_disjoint_inx_mut(indices)
            .map(|a| a.map(|(generation, node)| (generation, &mut node.t)))
    }

    fn find_first_inx_ptr(&self) -> Option<P> {
        self.a.find_first_inx_ptr()
    }

    fn find_last_inx_ptr(&self) -> Option<P> {
        self.a.find_last_inx_ptr()
    }

    fn ordered_advancer(&self, inx: <P as Ptr>::Inx, rev: bool) -> Self::PtrAdvancer {
        ord_iterators::PtrAdvancer {
            inx: Some(inx),
            rev,
        }
    }

    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (P, &'a mut T)>
    where
        T: 'a,
    {
        self.a.iter_mut().map(|(p, link)| (p, &mut link.t.t))
    }

    fn invalidate(&mut self, p: P) -> InvalidationResult<P> {
        self.a.invalidate(p)
    }

    fn drain(&mut self) -> impl Iterator<Item = InvalidationOption<(P, T)>> {
        self.a.drain().map(|o| o.map(|(p, link)| (p, link.t.t)))
    }

    fn remove(&mut self, p: P) -> InvalidationResult<T> {
        if !self.contains(p) {
            return InvalidationResult::InvalidPtr;
        }
        self.internal_remove(p.inx()).map(|(_, t)| t)
    }

    fn remove_inx(&mut self, p: <P as Ptr>::Inx) -> InvalidationResult<(<P as Ptr>::Gen, T)> {
        self.internal_remove(p)
    }

    fn clear(&mut self) -> InvalidationOption<()> {
        self.a.clear()
    }

    fn compress_with<F: FnMut(P, &mut T, P)>(
        &mut self,
        reset_generation: bool,
        mut map: F,
    ) -> InvalidationOption<()> {
        self.a
            .compress_with(reset_generation, |p, node, q| map(p, &mut node.t, q))
        // FIXME need generic rebalancer
    }
}

impl<P: Ptr, T, B: ArenaBacking> SingularGenerationArena<P> for SimpleOrdArena<P, T, B> {
    fn singular_generation(&self) -> <P as Ptr>::Gen {
        self.a.singular_generation()
    }
}
