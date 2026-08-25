use core::{mem, num::NonZeroUsize, slice::GetDisjointMutError};

use crate::{
    Arena, ChainArena, InvalidationOption, InvalidationResult, SurjectArena,
    arena::{ArenaSlot, from_checked_raw},
    chain::ChainArenaTrait,
    errors::{AllocError, ReallocationError},
    stack::NonZeroInxGenericStack,
    surject::SurjectShared,
    surject_iterators,
    traits::{Advancer, ArenaTrait, CompactArenaTrait, DisjointableArenaTrait, Ptr},
    utils::{PtrNoGen, traits::ArenaBacking},
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
        // Both arenas have to end up cleared, but REF(surject_clear_guard) cannot be
        // used
        struct ClearShared<'a, P: Ptr, S, B: ArenaBacking>(
            &'a mut Arena<PtrNoGen<P>, SurjectShared<S>, B>,
        );
        impl<P: Ptr, S, B: ArenaBacking> Drop for ClearShared<'_, P, S, B> {
            fn drop(&mut self) {
                self.0.clear().allow();
            }
        }
        let _shared = ClearShared(&mut self.shared_vals);
        self.elements.clear()
    }

    /// Note that this signature on `SurjectArena` unfortunately requires
    /// `O(n^2)` complexity. Instead, use
    /// [compress_canonical](SurjectArena::compress_canonical) or
    /// [transfer_canonical_reallocating](SurjectArena::transfer_canonical_reallocating),
    /// which are `O(n)` and improve cache locality as well.
    ///
    /// # Unwind Safety
    ///
    /// If `map` panics, this follows
    /// [compress_with](ArenaTrait::compress_with) on the elements. `map` can
    /// only run during that stage, so the shared values are left untouched and
    /// `self` is left in a valid state.
    fn compress_with<F: FnMut(P, &mut T, P)>(
        &mut self,
        reset_generation: bool,
        mut map: F,
    ) -> InvalidationOption<()> {
        let res = self
            .elements
            .compress_with(reset_generation, |p, element, q| map(p, &mut element.t, q));

        // It is much more important for this to have the same uniform capacity
        // reduction guarantees as the other uniform arenas, than for it to be `O(n)`.
        // Because of the difficulties we are going through already, keep the shared
        // values in their relative order, because that order can be observed through
        // `SurjectArena::shared_vals`. The empty case needs no special handling, every
        // slot is skipped and only the free slot removal below happens.

        // we are moving from `j` to `i`
        let mut i = NonZeroUsize::new(1).unwrap();
        for j in self.shared_vals.nziter() {
            let ArenaSlot::Allocated(..) = self.shared_vals.m.get(j).unwrap() else {
                continue;
            };
            if i != j {
                let entry = mem::replace(
                    self.shared_vals.m.get_mut(j).unwrap(),
                    // this will be overwritten or dropped
                    ArenaSlot::Free(P::invalid().inx()),
                );
                // the slot at `i` is always free at this point
                let _ = mem::replace(self.shared_vals.m.get_mut(i).unwrap(), entry);

                // find any one element of the surject that was pointing at `j`, then
                // repoint all of them at `i`
                let p_shared_j = PtrNoGen::<P>::_from_raw(from_checked_raw::<PtrNoGen<P>>(j), ());
                let p_shared_i = PtrNoGen::<P>::_from_raw(from_checked_raw::<PtrNoGen<P>>(i), ());
                let mut found = false;
                let mut outer_adv = self.elements.advancer();
                while let Some(p_init) = outer_adv.advance(&self.elements) {
                    let element = self.elements.get(p_init).unwrap();
                    if element.p_shared == p_shared_j {
                        let mut adv = self.elements.advancer_chain(p_init).unwrap();
                        while let Some(p) = adv.advance(&self.elements) {
                            // update
                            self.elements.get_mut(p).unwrap().p_shared = p_shared_i;
                        }
                        found = true;
                        break;
                    }
                }
                if !found {
                    // there is always exactly one surject pointing at an allocated
                    // shared value
                    unreachable!()
                }
            }
            i = i.checked_add(1).unwrap();
        }

        self.shared_vals.remove_free_end_slots();
        self.shared_vals.freelist_root = None;
        res
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
