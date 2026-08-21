//! Iterators for `ChainArena`

use recasting::{Recast, Recaster};

pub use crate::arena_iterators::{CapacityDrain, Iter};
use crate::{
    Arena, ChainArena, InvalidationOption, LinkNoGen, arena_iterators,
    traits::{Advancer, ArenaTrait, ChainArenaTrait, DisjointableArenaTrait, Ptr},
    utils::traits::ArenaBacking,
};

/// An advancer over the valid `P`s of a `ChainArena`
pub struct PtrAdvancer<P: Ptr> {
    adv: arena_iterators::PtrAdvancer<P>,
}

impl<P: Ptr, T, B: ArenaBacking> Advancer<ChainArena<P, T, B>> for PtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &ChainArena<P, T, B>) -> Option<Self::Item> {
        self.adv.advance(&collection.a)
    }

    fn empty() -> Self {
        Self {
            adv: <arena_iterators::PtrAdvancer<P> as Advancer<Arena<P, LinkNoGen<P, T>, B>>>::empty(
            ),
        }
    }
}

/// An advancer over the valid `P`s of one chain in a `ChainArena`
pub struct ChainPtrAdvancer<P: Ptr> {
    // the initial `Ptr` for checking if we are in a cycle
    init: P::Inx,
    // we ultimately want this in order to provide the extra guarantee that a removal and insertion
    // into the same spot can't cause the advancer to jump to an unrelated chain
    ptr: Option<P::Inx>,
    // switch to going in the previous direction
    switch: bool,
    // prevents infinite loops in case of various shenanigans
    max_advances: usize,
}

impl<P: Ptr, T, B: ArenaBacking> Advancer<ChainArena<P, T, B>> for ChainPtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &ChainArena<P, T, B>) -> Option<Self::Item> {
        if self.max_advances == 0 {
            return None;
        } else {
            self.max_advances = self.max_advances.wrapping_sub(1);
        }
        if let Some(ptr) = self.ptr {
            if self.switch {
                if let Some((generation, link)) = collection.a.get_inx(ptr) {
                    if let Some(prev) = link.prev() {
                        self.ptr = Some(prev);
                    } else {
                        self.ptr = None;
                    }
                    // note how we also get to implicitly check the validity of the original
                    // `self.ptr` without incurring extra lookups.
                    Some(Ptr::_from_raw(ptr, generation))
                } else {
                    self.ptr = None;
                    None
                }
            } else if let Some((generation, link)) = collection.a.get_inx(ptr) {
                if let Some(next) = link.next() {
                    if next == self.init {
                        // cyclical
                        self.ptr = None;
                    } else {
                        self.ptr = Some(next);
                    }
                } else {
                    self.switch = true;
                    // `init` was done on first iteration, we need to immediately use the
                    // previous node to `init`
                    if let Some((_, link)) = collection.a.get_inx(self.init) {
                        self.ptr = link.prev();
                    } else {
                        self.ptr = None;
                    }
                }
                Some(Ptr::_from_raw(ptr, generation))
            } else {
                self.ptr = None;
                None
            }
        } else {
            None
        }
    }

    fn empty() -> Self {
        // `max_advances: 0` guarantees empty
        Self {
            init: P::invalid().inx(),
            ptr: None,
            switch: false,
            max_advances: 0,
        }
    }
}

/// A draining iterator for a single chain. Drops the rest of the chain when
/// this iterator is dropped.
pub struct ChainDrain<'a, P: Ptr, T, B: ArenaBacking> {
    arena: &'a mut ChainArena<P, T, B>,
    // the `prev` interlink that the chain was started at, which is where we resume from
    // after running out of links in the `next` direction, and which also tells us when a
    // cyclic chain has come all the way back around
    prev_init: Option<P::Inx>,
    target: Option<P::Inx>,
    // switch to going in the previous direction
    go_prev: bool,
}

impl<'a, P: Ptr, T, B: ArenaBacking> Iterator for ChainDrain<'a, P, T, B> {
    type Item = InvalidationOption<(P, LinkNoGen<P, T>)>;

    fn next(&mut self) -> Option<Self::Item> {
        let p = self.target?;
        // TODO when we get the ability to enforce !Forget, optimize so that we don't
        // need to deal with interlinks
        let ((generation, link), o) = self.arena.remove_inx_link_no_gen(p).unwrap().overflowing();

        // REF(chain_drain_ordering) locate the next target first. This mirrors
        // `ChainPtrAdvancer` exactly so that the two produce the same ordering, which
        // `transfer_canonical_reallocating` relies on.
        self.target = if self.go_prev {
            link.prev()
        } else if Some(p) == self.prev_init {
            // cyclic
            None
        } else {
            let next = link.next();
            if next.is_none() {
                // switch directions
                self.go_prev = true;
                // automatically `None` if started at the start
                self.prev_init
            } else {
                next
            }
        };

        let p = P::_from_raw(p, generation);
        if o {
            Some(InvalidationOption::GenerationOverflow((p, link)))
        } else {
            Some(InvalidationOption::Success((p, link)))
        }
    }
}

impl<'a, P: Ptr, T, B: ArenaBacking> Drop for ChainDrain<'a, P, T, B> {
    fn drop(&mut self) {
        while self.next().is_some() {}
    }
}

// we have this because if we returned `&mut LinkNoGen<P, T>` it would allow
// breaking the chain invariants

/// A mutable iterator over `(P, LinkNoGen<P, &mut T>)` in a `ChainArena`
pub struct IterMut<'a, P: Ptr, T, B: ArenaBacking> {
    iter_mut: arena_iterators::IterMut<'a, P, LinkNoGen<P, T>, B>,
}

impl<'a, P: Ptr, T, B: ArenaBacking> Iterator for IterMut<'a, P, T, B> {
    type Item = (P, LinkNoGen<P, &'a mut T>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut
            .next()
            .map(|(p, link)| (p, LinkNoGen::new(link.prev_next(), &mut link.t)))
    }
}

// TODO we could remove these in the future with associated `impl` types

// note that everything here except for `internal_advancer_chain` and
// `internal_drain_chain` goes in increasing internal index order and is
// unrelated to the chain ordering
impl<P: Ptr, T, B: ArenaBacking> ChainArena<P, T, B> {
    pub(crate) fn internal_advancer_inx(&self, inx: P::Inx, rev: bool) -> PtrAdvancer<P> {
        PtrAdvancer {
            adv: self.a.advancer_inx(inx, rev),
        }
    }

    // I would add a mutable ordered iterator but it is not possible to make that
    // sound currently (we would have to rely on `P` conversions unlike the
    // unordered iterator which can rely on directly accessing the internal stack
    // which has strong requirements).

    pub(crate) fn internal_drain_chain(&mut self, p_init: P) -> Option<ChainDrain<'_, P, T, B>> {
        if !self.contains(p_init) {
            return None;
        }
        let p_init = p_init.inx();
        let prev_init = self.a.get_inx_unwrap(p_init).prev();
        Some(ChainDrain {
            arena: self,
            prev_init,
            target: Some(p_init),
            go_prev: false,
        })
    }

    pub(crate) fn internal_advancer_chain(&self, p_init: P) -> Option<ChainPtrAdvancer<P>> {
        if !self.contains(p_init) {
            return None;
        }
        Some(ChainPtrAdvancer {
            init: p_init.inx(),
            ptr: Some(p_init.inx()),
            switch: false,
            max_advances: self.len(),
        })
    }

    pub(crate) fn internal_iter(&self) -> Iter<'_, P, LinkNoGen<P, T>, B> {
        self.a.internal_iter()
    }

    pub(crate) fn internal_iter_mut(&mut self) -> IterMut<'_, P, T, B> {
        IterMut {
            iter_mut: self.a.internal_iter_mut(),
        }
    }
}

impl<'a, P: Ptr, T, B: ArenaBacking> IntoIterator for &'a ChainArena<P, T, B> {
    type IntoIter = Iter<'a, P, LinkNoGen<P, T>, B>;
    type Item = (P, &'a LinkNoGen<P, T>);

    fn into_iter(self) -> Self::IntoIter {
        self.a.internal_iter()
    }
}

impl<'a, P: Ptr, T, B: ArenaBacking> IntoIterator for &'a mut ChainArena<P, T, B> {
    type IntoIter = IterMut<'a, P, T, B>;
    type Item = (P, LinkNoGen<P, &'a mut T>);

    /// This returns an `IterMut`. Use `ChainArena::drain` for by-value
    /// consumption.
    fn into_iter(self) -> Self::IntoIter {
        self.internal_iter_mut()
    }
}

impl<P: Ptr, T, B: ArenaBacking> IntoIterator for ChainArena<P, T, B> {
    type IntoIter = CapacityDrain<P, LinkNoGen<P, T>, B>;
    type Item = (P, LinkNoGen<P, T>);

    fn into_iter(self) -> Self::IntoIter {
        self.a.internal_capacity_drain()
    }
}

impl<P: Ptr, I, T: Recast<I>, B: ArenaBacking> Recast<I> for ChainArena<P, T, B> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        // note that the interlinks are not recast, they are internal to this arena and
        // are always maintained by it
        for val in self.vals_mut() {
            val.recast(recaster)?;
        }
        Ok(())
    }
}
