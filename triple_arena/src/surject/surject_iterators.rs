//! Iterators for [SurjectArena]

use recasting::{Recast, Recaster};

use crate::{
    Arena, InvalidationOption, LinkNoGen, SurjectArena, arena_iterators,
    surject::{SurjectElement, SurjectShared},
    traits::{Advancer, ArenaTrait, ChainArenaTrait, DisjointableArenaTrait, Ptr},
    utils::{PtrNoGen, traits::ArenaBacking},
};

/// An advancer over the valid `P`s of a `SurjectArena`
pub struct PtrAdvancer<P: Ptr> {
    adv: arena_iterators::PtrAdvancer<P>,
}

impl<P: Ptr, T, S, B: ArenaBacking> Advancer<SurjectArena<P, T, S, B>> for PtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &SurjectArena<P, T, S, B>) -> Option<Self::Item> {
        self.adv.advance(&collection.elements.a)
    }

    fn empty() -> Self {
        Self {
            adv: <arena_iterators::PtrAdvancer<P> as Advancer<
                Arena<P, LinkNoGen<P, SurjectElement<P, T>>, B>,
            >>::empty(),
        }
    }
}

/// An advancer over the valid `P`s of one surject in a `SurjectArena`
pub struct SurjectPtrAdvancer<P: Ptr> {
    // same as for `ChainPtrAdvancer` except we get to assume the chain is cyclical
    init: P::Inx,
    ptr: Option<P::Inx>,
    // prevent infinite loops
    max_advances: usize,
}

impl<P: Ptr, T, S, B: ArenaBacking> Advancer<SurjectArena<P, T, S, B>> for SurjectPtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &SurjectArena<P, T, S, B>) -> Option<Self::Item> {
        if self.max_advances == 0 {
            return None;
        } else {
            self.max_advances = self.max_advances.wrapping_sub(1);
        }
        if let Some(ptr) = self.ptr {
            if let Some((generation, link)) = collection.elements.get_inx_link_no_gen(ptr) {
                if let Some(next) = link.next() {
                    if next == self.init {
                        self.ptr = None;
                    } else {
                        self.ptr = Some(next);
                    }
                } else {
                    // could be unreachable under invalidation
                    self.ptr = None;
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
            max_advances: 0,
        }
    }
}

/// An iterator over the `(P, &T, &S)` of one surject in a `SurjectArena`
pub struct IterSurject<'a, P: Ptr, T, S, B: ArenaBacking> {
    arena: &'a SurjectArena<P, T, S, B>,
    adv: SurjectPtrAdvancer<P>,
    // the surject is fixed for the whole iteration, so this is looked up only once
    shared: &'a S,
}

impl<'a, P: Ptr, T, S, B: ArenaBacking> Iterator for IterSurject<'a, P, T, S, B> {
    type Item = (P, &'a T, &'a S);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.adv.advance(self.arena) {
            Some((p, self.arena.get(p).unwrap(), self.shared))
        } else {
            None
        }
    }
}

/// An iterator over `(P, &T, &S)` in a `SurjectArena`
pub struct Iter<'a, P: Ptr, T, S, B: ArenaBacking> {
    iter: arena_iterators::Iter<'a, P, LinkNoGen<P, SurjectElement<P, T>>, B>,
    shared_vals: &'a Arena<PtrNoGen<P>, SurjectShared<S>, B>,
}

impl<'a, P: Ptr, T, S, B: ArenaBacking> Iterator for Iter<'a, P, T, S, B> {
    type Item = (P, &'a T, &'a S);

    fn next(&mut self) -> Option<Self::Item> {
        let (p, link) = self.iter.next()?;
        Some((
            p,
            &link.t.t,
            &self.shared_vals.get(link.t.p_shared).unwrap().s,
        ))
    }
}

// TODO this is how we have to do it until !Forget types, I would want the `S`
// to be returned in a tuple with the iterator

/// A draining iterator over the `(P, T, Option<S>)` of one surject in a
/// `SurjectArena`. The last item will return the shared value.
pub struct SurjectDrain<'a, P: Ptr, T, S, B: ArenaBacking> {
    arena: &'a mut SurjectArena<P, T, S, B>,
    adv: SurjectPtrAdvancer<P>,
}

impl<P: Ptr, T, S, B: ArenaBacking> Drop for SurjectDrain<'_, P, T, S, B> {
    fn drop(&mut self) {
        while self.next().is_some() {}
    }
}

impl<P: Ptr, T, S, B: ArenaBacking> Iterator for SurjectDrain<'_, P, T, S, B> {
    type Item = InvalidationOption<(P, T, Option<S>)>;

    fn next(&mut self) -> Option<Self::Item> {
        let p = self.adv.advance(self.arena)?;
        Some(
            self.arena
                .remove_element(p)
                .unwrap()
                .map(|(t, s)| (p, t, s)),
        )
    }
}

/// A draining iterator over all of the `(P, T, Option<S>)` in a `SurjectArena`.
/// Each surject is drained completely before moving onto the next one, so the
/// shared value arrives with the last element of each surject.
pub struct Drain<'a, P: Ptr, T, S, B: ArenaBacking> {
    arena: &'a mut SurjectArena<P, T, S, B>,
    adv0: PtrAdvancer<P>,
    adv1: Option<SurjectPtrAdvancer<P>>,
}

impl<P: Ptr, T, S, B: ArenaBacking> Drop for Drain<'_, P, T, S, B> {
    fn drop(&mut self) {
        self.arena.clear().allow();
    }
}

impl<P: Ptr, T, S, B: ArenaBacking> Iterator for Drain<'_, P, T, S, B> {
    type Item = InvalidationOption<(P, T, Option<S>)>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(adv1) = &mut self.adv1 {
                if let Some(p) = adv1.advance(self.arena) {
                    return Some(
                        self.arena
                            .remove_element(p)
                            .unwrap()
                            .map(|(t, s)| (p, t, s)),
                    );
                } else {
                    self.adv1 = None;
                }
            }
            let p_next_surject = self.adv0.advance(self.arena)?;
            self.adv1 = Some(self.arena.advancer_surject(p_next_surject).unwrap());
        }
    }
}

impl<P: Ptr, T, S, B: ArenaBacking> SurjectArena<P, T, S, B> {
    pub(crate) fn internal_advancer_inx(&self, inx: P::Inx, rev: bool) -> PtrAdvancer<P> {
        PtrAdvancer {
            adv: self.elements.a.advancer_inx(inx, rev),
        }
    }

    // FIXME remove

    /// Advances over every valid `Ptr` in `self`.
    ///
    /// Has the same properties as [crate::Arena::advancer]
    pub fn advancer(&self) -> PtrAdvancer<P> {
        PtrAdvancer {
            adv: self.elements.a.advancer(),
        }
    }

    /// Advances over every valid `Ptr` in the surject that contains `p_init`.
    /// This does _not_ support invalidating `Ptr`s of the surject of `p_init`
    /// during the loop.
    ///
    /// # Note
    ///
    /// If elements of the surject that contains `p_init` are invalidated during
    /// the loop, it can lead to a loop where the same `Ptr` can be returned
    /// multiple times. There is an internal fail safe that prevents
    /// non-termination.
    pub fn advancer_surject(&self, p_init: P) -> Option<SurjectPtrAdvancer<P>> {
        if !self.contains(p_init) {
            return None;
        }
        Some(SurjectPtrAdvancer {
            init: p_init.inx(),
            ptr: Some(p_init.inx()),
            max_advances: self.len(),
        })
    }

    /// Iteration over the `(P, &T, &S)` tuples of the surject that contains
    /// `p_init`. The same `&S` reference is used for all iterations. Returns
    /// `None` if `p_init` is invalid.
    pub fn iter_surject(&self, p_init: P) -> Option<IterSurject<'_, P, T, S, B>> {
        Some(IterSurject {
            arena: self,
            adv: self.advancer_surject(p_init)?,
            // `advancer_surject` has already established that `p_init` is valid
            shared: self.get_shared(p_init).unwrap(),
        })
    }

    pub(crate) fn internal_iter(&self) -> Iter<'_, P, T, S, B> {
        Iter {
            iter: self.elements.internal_iter(),
            shared_vals: &self.shared_vals,
        }
    }

    // TODO until we have a proper trait

    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> impl Iterator<Item = P> {
        self.elements.ptrs()
    }

    /// Iteration over the `&S` of every surject, once each
    pub fn shared_vals<'a>(&'a self) -> impl Iterator<Item = &'a S>
    where
        S: 'a,
    {
        self.shared_vals.vals().map(|shared| &shared.s)
    }

    /// Mutable iteration over the `&mut S` of every surject, once each
    pub fn shared_vals_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut S>
    where
        S: 'a,
    {
        self.shared_vals.iter_mut().map(|(_, shared)| &mut shared.s)
    }

    /// Iteration over `(P, &T, &S)` tuples. For each surject with multiple `P`
    /// pointing to the same `S`, the same reference to the `S` is returned
    /// multiple times
    pub fn iter_combined(&self) -> Iter<'_, P, T, S, B> {
        self.internal_iter()
    }

    /// Draining iteration over the surject that contains `p_init`, returning
    /// `(P, T, Option<S>)` with the shared value arriving with the last
    /// element. Returns `None` if `p_init` is invalid.
    pub fn drain_surject(&mut self, p_init: P) -> Option<SurjectDrain<'_, P, T, S, B>> {
        let adv = self.advancer_surject(p_init)?;
        Some(SurjectDrain { arena: self, adv })
    }

    /// Draining iteration over every element of the arena, returning
    /// `(P, T, Option<S>)` with the shared value of each surject arriving with
    /// the last element of that surject
    pub fn drain_combined(&mut self) -> Drain<'_, P, T, S, B> {
        let adv0 = self.advancer();
        Drain {
            arena: self,
            adv0,
            adv1: None,
        }
    }
}

impl<'a, P: Ptr, T, S, B: ArenaBacking> IntoIterator for &'a SurjectArena<P, T, S, B> {
    type IntoIter = Iter<'a, P, T, S, B>;
    type Item = (P, &'a T, &'a S);

    fn into_iter(self) -> Self::IntoIter {
        self.internal_iter()
    }
}

impl<P: Ptr, I, T: Recast<I>, S: Recast<I>, B: ArenaBacking> Recast<I>
    for SurjectArena<P, T, S, B>
{
    /// Note that this recasts both the elements and the shared values (only the
    /// `Ptr`s are the keyed items from the `Recast` perspective)
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for element in self.vals_mut() {
            element.recast(recaster)?;
        }
        for shared in self.shared_vals_mut() {
            shared.recast(recaster)?;
        }
        Ok(())
    }
}
