//! Iterators for [SimpleOrdArena]

use recasting::{Recast, Recaster};

use crate::{
    ChainArena, InvalidationOption, SimpleOrdArena, arena_iterators,
    chain::ChainArenaTrait,
    chain_iterators,
    traits::{Advancer, ArenaTrait, DisjointableArenaTrait, Ptr},
    utils::traits::ArenaBacking,
};

/// An advancer over the valid `P`s of a `SimpleOrdArena`. This is _not_ ordered
/// with respect to keys
pub struct PtrAdvancer<P: Ptr> {
    adv: arena_iterators::PtrAdvancer<P>,
}

impl<P: Ptr, T, B: ArenaBacking> Advancer<SimpleOrdArena<P, T, B>> for PtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &SimpleOrdArena<P, T, B>) -> Option<Self::Item> {
        self.adv.advance(&collection.a.a)
    }

    fn empty() -> Self {
        Self {
            adv: <arena_iterators::PtrAdvancer<P> as Advancer<crate::Arena<P, T, B>>>::empty(),
        }
    }
}

/// An ordered advancer
pub struct OrderedPtrAdvancer<P: Ptr> {
    // same as for `ChainPtrAdvancer` except we get to assume the chain is acyclic and we start
    // from the beginning
    inx: Option<P::Inx>,
    // if in reverse
    rev: bool,
}

impl<P: Ptr, T, B: ArenaBacking> Advancer<SimpleOrdArena<P, T, B>> for OrderedPtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &SimpleOrdArena<P, T, B>) -> Option<Self::Item> {
        let inx = self.inx?;
        if let Some((generation, link)) = collection.a.a.get_inx(inx) {
            if self.rev {
                self.inx = link.prev();
            } else {
                self.inx = link.next();
            }
            Some(Ptr::_from_raw(inx, generation))
        } else {
            self.inx = None;
            None
        }
    }

    fn empty() -> Self {
        Self {
            inx: None,
            rev: false,
        }
    }
}

/// An ordered iterator over `(P, &T)` in a `SimpleOrdArena`
pub struct Iter<'a, P: Ptr, T, B: ArenaBacking> {
    arena: &'a SimpleOrdArena<P, T, B>,
    adv: OrderedPtrAdvancer<P>,
}

impl<'a, P: Ptr, T, B: ArenaBacking> Iterator for Iter<'a, P, T, B> {
    type Item = (P, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        self.adv
            .advance(self.arena)
            .map(|p| (p, self.arena.get(p).unwrap()))
    }
}

/// An ordered draining iterator over `(P, T)` in a `SimpleOrdArena`, produced
/// by [drain_ordered](SimpleOrdArena::drain_ordered)
pub struct OrderedDrain<'a, P: Ptr, T, B: ArenaBacking> {
    arena: &'a mut SimpleOrdArena<P, T, B>,
    adv: OrderedPtrAdvancer<P>,
}

impl<P: Ptr, T, B: ArenaBacking> Drop for OrderedDrain<'_, P, T, B> {
    fn drop(&mut self) {
        self.arena.clear().allow();
    }
}

impl<P: Ptr, T, B: ArenaBacking> Iterator for OrderedDrain<'_, P, T, B> {
    type Item = InvalidationOption<(P, T)>;

    fn next(&mut self) -> Option<Self::Item> {
        // TODO if we can make it !Forget, we can advance over the chain instead of
        // having to use `O(log n)` ops
        let p = self.adv.advance(self.arena)?;
        Some(self.arena.remove(p).map(|t| (p, t)).unwrap())
    }
}

/// An ordered capacity draining iterator over `(P, T)` in a `SimpleOrdArena`,
/// produced by the owning [IntoIterator] impl. Note that until Rust supports
/// !Forget types, this operation is `O(n log n)` because it has to individually
/// remove every element.
pub struct CapacityDrain<P: Ptr, T, B: ArenaBacking> {
    arena: SimpleOrdArena<P, T, B>,
    adv: chain_iterators::ChainPtrAdvancer<P>,
}

impl<P: Ptr, T, B: ArenaBacking> Iterator for CapacityDrain<P, T, B> {
    type Item = (P, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.adv.advance(&self.arena.a).map(|p| {
            // allow generation overflows
            (p, self.arena.remove(p).allow().unwrap())
        })
    }
}

impl<P: Ptr, T, B: ArenaBacking> SimpleOrdArena<P, T, B> {
    pub(crate) fn internal_advancer_inx(&self, inx: P::Inx, rev: bool) -> PtrAdvancer<P> {
        PtrAdvancer {
            adv: self.a.a.advancer_inx(inx, rev),
        }
    }

    /// This advances over all the entries in order with respect to their keys.
    /// Starts from `p` and moves in reverse order if `rev` is set. Returns
    /// `None` if `p` is invalid
    pub fn advancer_ordered(&self, p: P, rev: bool) -> Option<OrderedPtrAdvancer<P>> {
        if !self.contains(p) {
            return None;
        }
        Some(OrderedPtrAdvancer {
            inx: Some(p.inx()),
            rev,
        })
    }

    /// Iterates in order from least to greatest
    pub fn iter_ordered(&self) -> Iter<'_, P, T, B> {
        let inx = if self.is_empty() {
            None
        } else {
            Some(self.first)
        };
        Iter {
            arena: self,
            adv: OrderedPtrAdvancer { inx, rev: false },
        }
    }

    /// Drains all on drop. Note that until Rust supports !Forget types, this
    /// operation is `O(n log n)` because it has to individually remove every
    /// element.
    pub fn drain_ordered(&mut self) -> OrderedDrain<'_, P, T, B> {
        let inx = if self.is_empty() {
            None
        } else {
            Some(self.first)
        };
        OrderedDrain {
            arena: self,
            adv: OrderedPtrAdvancer { inx, rev: false },
        }
    }

    pub(crate) fn internal_drain_capacity_ordered(self) -> CapacityDrain<P, T, B> {
        let adv = if let Some(first) = self.first() {
            self.a.advancer_chain(first).unwrap()
        } else {
            <chain_iterators::ChainPtrAdvancer<P> as Advancer<ChainArena<P, T, B>>>::empty()
        };
        CapacityDrain { arena: self, adv }
    }
}

/// Uses [SimpleOrdArena::iter_ordered]
impl<'a, P: Ptr, T, B: ArenaBacking> IntoIterator for &'a SimpleOrdArena<P, T, B> {
    type IntoIter = Iter<'a, P, T, B>;
    type Item = (P, &'a T);

    fn into_iter(self) -> Self::IntoIter {
        self.iter_ordered()
    }
}

// I would add a mutable iterator since we already allow getting &mut T, but I
// would also want it to be ordered like the other `IntoIterator`s here, and it
// is not possible to make that sound currently (we would have to rely on `P`
// conversions unlike the unordered case which can rely on directly accessing
// the internal stack which has strong requirements)

/// This is ordered from least to greatest.
impl<P: Ptr, T, B: ArenaBacking> IntoIterator for SimpleOrdArena<P, T, B> {
    type IntoIter = CapacityDrain<P, T, B>;
    type Item = (P, T);

    fn into_iter(self) -> Self::IntoIter {
        self.internal_drain_capacity_ordered()
    }
}

/// Be aware that this gives access to the full `T`
impl<P: Ptr, I, T: Recast<I>, B: ArenaBacking> Recast<I> for SimpleOrdArena<P, T, B> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for t in self.vals_mut() {
            t.recast(recaster)?;
        }
        Ok(())
    }
}
