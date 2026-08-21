use core::slice::GetDisjointMutError;

use crate::{
    Arena, ChainArena, InvalidationOption, InvalidationResult, SurjectArena,
    errors::{AllocError, ReallocationError},
    surject_iterators,
    traits::{ArenaTrait, CompactArenaTrait, DisjointableArenaTrait, Ptr},
    utils::traits::ArenaBacking,
};

impl<P: Ptr, T, B: ArenaBacking> ArenaTrait<P, T> for SurjectArena<P, T, B> {
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
        self.internal_drain()
            .map(|o| o.map(|(p, node)| (p, node.t)))
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

    /// Note that this also completely rebalances the tree, which is `O(n)` and
    /// therefore does not change the complexity of the compression itself.
    ///
    /// # Unwind Safety
    ///
    /// If `map` panics, this follows
    /// [compress_with](ArenaTrait::compress_with) on the base arena, and
    /// additionally the tree is rebalanced over the partially compressed
    /// entries so that `self` is left in a valid state.
    fn compress_with<F: FnMut(P, &mut T, P)>(
        &mut self,
        reset_generation: bool,
        mut map: F,
    ) -> InvalidationOption<()> {
        // REF(ord_rebalance_guard)
        struct Rebalance<'a, P: Ptr, T, B: ArenaBacking>(&'a mut SimpleOrdArena<P, T, B>);
        impl<P: Ptr, T, B: ArenaBacking> Drop for Rebalance<'_, P, T, B> {
            fn drop(&mut self) {
                // this is the precondition for the rebalance, and doing it here rather
                // than in the `map` closure also covers the entries that `map` did not
                // reach
                for node in self.0.a.vals_mut() {
                    node.p_back = None;
                    node.p_tree0 = None;
                    node.p_tree1 = None;
                }
                self.0.raw_rebalance_assuming_prepared();
            }
        }

        let this = Rebalance(self);
        this.0
            .a
            .compress_with(reset_generation, |p, node, q| map(p, &mut node.t, q))
    }
}

impl<P: Ptr, T, B: ArenaBacking> DisjointableArenaTrait<P, T> for SimpleOrdArena<P, T, B> {
    fn get_disjoint_inx_mut<const N: usize>(
        &mut self,
        indices: [<P as Ptr>::Inx; N],
    ) -> Result<[(<P as Ptr>::Gen, &mut T); N], GetDisjointMutError> {
        self.a
            .get_disjoint_inx_mut(indices)
            .map(|a| a.map(|(generation, node)| (generation, &mut node.t)))
    }

    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (P, &'a mut T)>
    where
        T: 'a,
    {
        self.a.iter_mut().map(|(p, node)| (p, &mut node.t))
    }
}

impl<P: Ptr, T, B: ArenaBacking> CompactArenaTrait<P, T> for SimpleOrdArena<P, T, B> {}

// TODO? If this is common enough do this
//struct SimpleOrdArenaRecaster(SimpleOrdArena<R, OrdPair<P, Q>, B>)
//impl ArenaDirectInsertTrait<Q, P> for SimpleOrdArenaRecaster
