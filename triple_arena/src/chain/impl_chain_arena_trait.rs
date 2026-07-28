use core::slice::GetDisjointMutError;

use crate::{
    AllocError, Arena, InvalidationOption, InvalidationResult, NotWithinCapacityError,
    ReallocationError,
    arena::ArenaBacking,
    chain::{ChainNoGenArena, LinkNoGen, chain_no_gen_iterators},
    traits::{
        ArenaInsertEntryTrait, ArenaInsertTrait, ArenaTrait, ChainArenaTrait, Ptr,
        SingularGenerationArena,
    },
};

// FIXME unify the chain arenas

impl<P: Ptr, T, B: ArenaBacking> ArenaTrait<P, T> for ChainNoGenArena<P, T, B> {
    type PtrAdvancer = chain_no_gen_iterators::PtrAdvancer<P>;

    fn new() -> Self {
        Self { a: Arena::new() }
    }

    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError> {
        Ok(Self {
            a: Arena::with_min_capacity(min_capacity)?,
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
            .map(|(generation, link)| (generation, &link.t))
    }

    fn get_disjoint_inx_mut<const N: usize>(
        &mut self,
        indices: [<P as Ptr>::Inx; N],
    ) -> Result<[(<P as Ptr>::Gen, &mut T); N], GetDisjointMutError> {
        self.a
            .get_disjoint_inx_mut(indices)
            .map(|a| a.map(|(generation, link)| (generation, &mut link.t)))
    }

    fn find_first_inx_ptr(&self) -> Option<P> {
        self.a.find_first_inx_ptr()
    }

    fn find_last_inx_ptr(&self) -> Option<P> {
        self.a.find_last_inx_ptr()
    }

    fn ordered_advancer(&self, inx: <P as Ptr>::Inx, rev: bool) -> Self::PtrAdvancer {
        chain_no_gen_iterators::PtrAdvancer {
            adv: self.a.ordered_advancer(inx, rev),
        }
    }

    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (P, &'a mut T)>
    where
        T: 'a,
    {
        self.a.iter_mut().map(|(p, link)| (p, &mut link.t))
    }

    fn invalidate(&mut self, p: P) -> InvalidationResult<P> {
        self.a.invalidate(p)
    }

    fn drain(&mut self) -> impl Iterator<Item = InvalidationOption<(P, T)>> {
        self.a.drain().map(|o| o.map(|(p, link)| (p, link.t)))
    }

    fn remove(&mut self, p: P) -> InvalidationResult<T> {
        // FIXME
        self.a.remove(p).map(|link| link.t)
    }

    fn clear(&mut self) -> InvalidationOption<()> {
        self.a.clear()
    }

    fn compress_with<F: FnMut(P, &mut T, P)>(
        &mut self,
        reset_generation: bool,
        mut map: F,
    ) -> InvalidationOption<()> {
        // FIXME
        self.a
            .compress_with(reset_generation, |p, link, q| map(p, &mut link.t, q))
    }
}

impl<P: Ptr, T, B: ArenaBacking> SingularGenerationArena<P> for ChainNoGenArena<P, T, B> {
    fn singular_generation(&self) -> <P as Ptr>::Gen {
        self.a.singular_generation()
    }
}

pub struct ChainArenaInsertEntry<'a, P: Ptr, T, B: ArenaBacking> {
    this: &'a mut ChainNoGenArena<P, T, B>,
    // this either points to a free slot or to one past `this.m.len()` where an allocation can be
    // pushed successfully
    p: P,
    prev_next: (Option<P::Inx>, Option<P::Inx>),
}

impl<'a, P: Ptr, T, B: ArenaBacking> ArenaInsertEntryTrait<'a, P, T>
    for ChainArenaInsertEntry<'a, P, T, B>
{
    fn ptr(&'a self) -> P {
        self.p
    }

    fn insert(self, t: T) {
        let this = self.this;
        this.a.insert(LinkNoGen::new(self.prev_next, t));
    }
}

impl<P: Ptr, T, B: ArenaBacking> ChainArenaTrait<P, T> for ChainNoGenArena<P, T, B> {
    type InsertionEntry<'a>
        = ChainArenaInsertEntry<'a, P, T, B>
    where
        Self: 'a;

    fn get_link_no_gen_inx(&self, p: <P as Ptr>::Inx) -> Option<(P::Gen, &LinkNoGen<P, T>)> {
        self.a.get_inx(p)
    }

    fn entry_insert_within_capacity(
        &mut self,
        prev_next: (Option<P>, Option<P>),
    ) -> Result<Self::InsertionEntry<'_>, NotWithinCapacityError> {
        todo!()
    }
}
