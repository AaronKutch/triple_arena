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
    // note: we drop the entry when constructing this and are relying on idempotency
    a: &'a mut ChainNoGenArena<P, T, B>,
    p: P,
    // this must be filled out if in the middle of a chain
    prev_next: (Option<P::Inx>, Option<P::Inx>),
}

impl<'a, P: Ptr, T, B: ArenaBacking> ArenaInsertEntryTrait<'a, P, T>
    for ChainArenaInsertEntry<'a, P, T, B>
{
    fn ptr(&'a self) -> P {
        self.p
    }

    fn insert(self, t: T) {
        let p = self.p;
        // double check idempotency
        let entry = self.a.a.entry_insert_within_capacity().unwrap();
        assert_eq!(entry.ptr(), p);
        match self.prev_next {
            (None, None) => {
                entry.insert(LinkNoGen::new(self.prev_next, t));
            }
            (None, Some(p1)) => {
                entry.insert(LinkNoGen::new(self.prev_next, t));
                self.a.a.get_inx_mut_unwrap(p1).prev_next.0 = Some(p.inx());
            }
            (Some(p0), None) => {
                entry.insert(LinkNoGen::new(self.prev_next, t));
                self.a.a.get_inx_mut_unwrap(p0).prev_next.1 = Some(p.inx());
            }
            (Some(p0), Some(p1)) => {
                entry.insert(LinkNoGen::new(self.prev_next, t));
                self.a.a.get_inx_mut_unwrap(p0).prev_next.1 = Some(p.inx());
                self.a.a.get_inx_mut_unwrap(p1).prev_next.0 = Some(p.inx());
            }
        }
    }
}

impl<P: Ptr, T, B: ArenaBacking> ChainArenaTrait<P, T> for ChainNoGenArena<P, T, B> {
    type InsertionEntry<'a>
        = ChainArenaInsertEntry<'a, P, T, B>
    where
        Self: 'a;

    fn get_inx_link_no_gen(&self, p: <P as Ptr>::Inx) -> Option<(P::Gen, &LinkNoGen<P, T>)> {
        self.a.get_inx(p)
    }

    fn entry_insert_new_within_capacity(
        &mut self,
        cyclical: bool,
    ) -> Result<Self::InsertionEntry<'_>, NotWithinCapacityError> {
        let entry = self.a.entry_insert_within_capacity()?;
        let p = entry.ptr();
        let prev_next = if cyclical {
            (Some(entry.ptr().inx()), Some(entry.ptr().inx()))
        } else {
            (None, None)
        };
        Ok(ChainArenaInsertEntry {
            a: self,
            p,
            prev_next,
        })
    }

    fn entry_insert_inx_within_capacity(
        &mut self,
        mut prev_next: (Option<P::Inx>, Option<P::Inx>),
    ) -> Option<Result<Self::InsertionEntry<'_>, NotWithinCapacityError>> {
        match prev_next {
            // new chain
            (None, None) => {}
            (None, Some(p1)) => {
                // if there is a failure it cannot result in a node being inserted
                let prev = self.a.get_inx(p1)?.1.prev();
                if let Some(p0) = prev {
                    // inserting into middle of chain
                    prev_next.0 = Some(p0);
                }
            }
            (Some(p0), None) => {
                let next = self.a.get_inx(p0)?.1.next();
                if let Some(p1) = next {
                    // inserting into middle of chain
                    prev_next.1 = Some(p1);
                }
            }
            (Some(p0), Some(p1)) => {
                // check for existence and that the nodes are neighbors
                if !self.are_neighbors_inx(p0, p1) {
                    return None;
                }
            }
        }
        match self.a.entry_insert_within_capacity() {
            Ok(entry) => {
                let p = entry.ptr();
                Some(Ok(ChainArenaInsertEntry {
                    a: self,
                    p,
                    prev_next,
                }))
            }
            Err(e) => Some(Err(e)),
        }
    }

    fn connect(&mut self, p_prev: P, p_next: P) -> Option<()> {
        if self.get_link_no_gen(p_prev)?.next().is_none()
            && self.get_link_no_gen(p_next)?.prev().is_none()
        {
            self.a.get_inx_mut_unwrap(p_prev.inx()).prev_next.1 = Some(p_next.inx());
            self.a.get_inx_mut_unwrap(p_next.inx()).prev_next.0 = Some(p_prev.inx());
            Some(())
        } else {
            None
        }
    }

    fn break_prev(&mut self, p: P) -> Option<()> {
        let prev = self.get_link_no_gen(p)?.prev()?;
        self.a.get_inx_mut_unwrap(prev).prev_next.1 = None;
        self.a.get_inx_mut_unwrap(p.inx()).prev_next.0 = None;
        Some(())
    }

    fn break_next(&mut self, p: P) -> Option<()> {
        let next = self.get_link_no_gen(p)?.next()?;
        self.a.get_inx_mut_unwrap(p.inx()).prev_next.1 = None;
        self.a.get_inx_mut_unwrap(next).prev_next.0 = None;
        Some(())
    }

    fn exchange_next(&mut self, p0: P, p1: P) -> Option<()> {
        if self.contains(p0) && self.contains(p1) {
            // get downstream links
            let d0 = self.a.get_inx_unwrap(p0.inx()).next()?;
            let d1 = self.a.get_inx_unwrap(p1.inx()).next()?;
            self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(d1);
            self.a.get_inx_mut_unwrap(p1.inx()).prev_next.1 = Some(d0);
            self.a.get_inx_mut_unwrap(d0).prev_next.0 = Some(p1.inx());
            self.a.get_inx_mut_unwrap(d1).prev_next.0 = Some(p0.inx());
            Some(())
        } else {
            None
        }
    }

    /*fn drain_chain(&mut self, p: P) -> Option<impl Iterator<Item = InvalidationOption<(P, T)>>> {
        // FIXME fix generic
        let res = match ArenaTrait::remove(self, p) {
            InvalidationResult::Success(_) => InvalidationOption::Success(()),
            InvalidationResult::GenerationOverflow(_) => InvalidationOption::GenerationOverflow(()),
            InvalidationResult::InvalidPtr => return InvalidationResult::InvalidPtr,
        };
        let mut removed = 1;
        let mut tmp = init.next();
        while let Some(next) = tmp {
            if next == p.inx() {
                // cyclical
                return Some(removed);
            }
            tmp = self
                .a
                .remove_internal(next, None, false)
                .allow()
                .unwrap()
                .next();
            removed = removed.wrapping_add(1);
        }
        let mut tmp = init.prev();
        while let Some(prev) = tmp {
            tmp = self
                .a
                .remove_internal(prev, None, false)
                .allow()
                .unwrap()
                .prev();
            removed = removed.wrapping_add(1);
        }
        match res {
            InvalidationOption::Success(()) => InvalidationResult::Success(removed),
            InvalidationOption::GenerationOverflow(()) => InvalidationResult::GenerationOverflow(removed),
        }
    }*/
}
