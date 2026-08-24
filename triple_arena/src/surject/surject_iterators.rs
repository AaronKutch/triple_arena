//! Iterators for `SurjectArena`

use recasting::{Recast, Recaster};

use crate::{
    Arena, InvalidationOption, LinkNoGen, SurjectArena, arena_iterators,
    surject::{Key, Val},
    traits::{Advancer, ArenaTrait, ChainArenaTrait, DisjointableArenaTrait, Ptr},
    utils::{PtrNoGen, traits::ArenaBacking},
};

/// An advancer over the valid `P`s of a `SurjectArena`
pub struct PtrAdvancer<P: Ptr> {
    adv: arena_iterators::PtrAdvancer<P>,
}

impl<P: Ptr, K, V, B: ArenaBacking> Advancer<SurjectArena<P, K, V, B>> for PtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &SurjectArena<P, K, V, B>) -> Option<Self::Item> {
        self.adv.advance(&collection.keys.a)
    }

    fn empty() -> Self {
        Self {
            adv: <arena_iterators::PtrAdvancer<P> as Advancer<crate::Arena<P, K, B>>>::empty(),
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

impl<P: Ptr, K, V, B: ArenaBacking> Advancer<SurjectArena<P, K, V, B>> for SurjectPtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &SurjectArena<P, K, V, B>) -> Option<Self::Item> {
        if self.max_advances == 0 {
            return None;
        } else {
            self.max_advances = self.max_advances.wrapping_sub(1);
        }
        if let Some(ptr) = self.ptr {
            if let Some((generation, link)) = collection.keys.get_inx_link_no_gen(ptr) {
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

/// An iterator over `(P, &K, &V)` in a `SurjectArena` surject
pub struct IterSurject<'a, P: Ptr, K, V, B: ArenaBacking> {
    arena: &'a SurjectArena<P, K, V, B>,
    adv: SurjectPtrAdvancer<P>,
    surject_val: Option<&'a V>,
}

impl<'a, P: Ptr, K, V, B: ArenaBacking> Iterator for IterSurject<'a, P, K, V, B> {
    type Item = (P, &'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.adv.advance(self.arena) {
            Some((p, self.arena.get_key(p).unwrap(), self.surject_val.unwrap()))
        } else {
            None
        }
    }
}

/// An iterator over `(P, &K, &V)` in a `SurjectArena`
pub struct Iter<'a, P: Ptr, K, V, B: ArenaBacking> {
    iter: arena_iterators::Iter<'a, P, LinkNoGen<P, Key<P, K>>, B>,
    vals: &'a Arena<PtrNoGen<P>, Val<V>, B>,
}

impl<'a, P: Ptr, K, V, B: ArenaBacking> Iterator for Iter<'a, P, K, V, B> {
    type Item = (P, &'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let (p, link) = self.iter.next()?;
        Some((p, &link.t.k, &self.vals.get(link.t.p_val).unwrap().v))
    }
}

// TODO this is how we have to do it until !Forget types, I would want the `V`
// to be returned in a tuple with the iterator

/// A draining iterator over a surject of `(P, K, Option<V>)` in a
/// `SurjectArena`, produced by [drain_surject](SurjectArena::drain_surject).
/// The last item will return the value.
pub struct SurjectDrain<'a, P: Ptr, K, V, B: ArenaBacking> {
    arena: &'a mut SurjectArena<P, K, V, B>,
    adv: SurjectPtrAdvancer<P>,
}

impl<P: Ptr, K, V, B: ArenaBacking> Drop for SurjectDrain<'_, P, K, V, B> {
    fn drop(&mut self) {
        self.arena.clear().allow();
    }
}

impl<P: Ptr, K, V, B: ArenaBacking> Iterator for SurjectDrain<'_, P, K, V, B> {
    type Item = InvalidationOption<(P, K, Option<V>)>;

    fn next(&mut self) -> Option<Self::Item> {
        let p = self.adv.advance(self.arena)?;
        Some(self.arena.remove_key(p).unwrap().map(|(k, v)| (p, k, v)))
    }
}

pub struct Drain<'a, P: Ptr, K, V, B: ArenaBacking> {
    arena: &'a mut SurjectArena<P, K, V, B>,
    adv0: PtrAdvancer<P>,
    adv1: Option<SurjectPtrAdvancer<P>>,
}

impl<P: Ptr, K, V, B: ArenaBacking> Drop for Drain<'_, P, K, V, B> {
    fn drop(&mut self) {
        self.arena.clear().allow();
    }
}

impl<P: Ptr, K, V, B: ArenaBacking> Iterator for Drain<'_, P, K, V, B> {
    type Item = InvalidationOption<(P, K, Option<V>)>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(adv1) = &mut self.adv1 {
                if let Some(p) = adv1.advance(self.arena) {
                    return Some(self.arena.remove_key(p).unwrap().map(|(k, v)| (p, k, v)));
                } else {
                    self.adv1 = None;
                }
            }
            let p_next_set = self.adv0.advance(self.arena)?;
            self.adv1 = Some(self.arena.advancer_surject(p_next_set).unwrap());
        }
    }
}

impl<P: Ptr, K, V, B: ArenaBacking> SurjectArena<P, K, V, B> {
    pub(crate) fn internal_advancer_inx(&self, inx: P::Inx, rev: bool) -> PtrAdvancer<P> {
        PtrAdvancer {
            adv: self.keys.a.advancer_inx(inx, rev),
        }
    }

    // FIXME remove

    /// Advances over every valid `Ptr` in `self`.
    ///
    /// Has the same properties as [crate::Arena::advancer]
    pub fn advancer(&self) -> PtrAdvancer<P> {
        PtrAdvancer {
            adv: self.keys.a.advancer(),
        }
    }

    /// Advances over every valid `Ptr` in the surject that contains `p_init`.
    /// This does _not_ support invalidating `Ptr`s of the surject of `p_init`
    /// during the loop.
    ///
    /// # Note
    ///
    /// If links of the surject that contains `p_init` are invalidated during
    /// the loop, it can lead to loop where the same `Ptr` can be returned
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

    /// Iteration over `(P, &K, &V)` tuples in the surject that contains
    /// `p_init`. The same `&V` reference is used for all iterations.
    pub fn iter_surject(&self, p_init: P) -> Option<IterSurject<'_, P, K, V, B>> {
        Some(IterSurject {
            arena: self,
            adv: self.advancer_surject(p_init)?,
            surject_val: self.get_val(p_init),
        })
    }

    pub(crate) fn internal_iter(&self) -> Iter<'_, P, K, V, B> {
        Iter {
            iter: self.keys.internal_iter(),
            vals: &self.vals,
        }
    }

    // TODO until we have a proper trait

    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> impl Iterator<Item = P> {
        self.keys.ptrs()
    }

    /// Iteration over `&K`
    pub fn keys<'a>(&'a self) -> impl Iterator<Item = &'a K>
    where
        K: 'a,
    {
        self.keys.vals().map(|key| &key.k)
    }

    /// Iteration over `&V`
    pub fn vals<'a>(&'a self) -> impl Iterator<Item = &'a V>
    where
        V: 'a,
    {
        self.vals.vals().map(|val| &val.v)
    }

    /// Mutable iteration over `&mut K`
    pub fn keys_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut K>
    where
        K: 'a,
    {
        self.keys.iter_mut().map(|(_, key)| &mut key.k)
    }

    /// Mutable iteration over `&mut V`
    pub fn vals_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut V>
    where
        V: 'a,
    {
        self.vals.iter_mut().map(|(_, val)| &mut val.v)
    }

    /// Iteration over `(P, &K, &V)` tuples. For each surject with multiple `P`
    /// pointing to the same `V`, the same reference to the `V` is returned
    /// multiple times
    pub fn iter_combined(&self) -> Iter<'_, P, K, V, B> {
        self.internal_iter()
    }

    pub fn drain_surject(&mut self, p_init: P) -> Option<SurjectDrain<'_, P, K, V, B>> {
        let adv = self.advancer_surject(p_init)?;
        Some(SurjectDrain { arena: self, adv })
    }

    pub fn drain_combined(&mut self) -> Drain<'_, P, K, V, B> {
        let adv0 = self.advancer();
        Drain {
            arena: self,
            adv0,
            adv1: None,
        }
    }
}

impl<'a, P: Ptr, K, V, B: ArenaBacking> IntoIterator for &'a SurjectArena<P, K, V, B> {
    type IntoIter = Iter<'a, P, K, V, B>;
    type Item = (P, &'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        self.internal_iter()
    }
}

impl<P: Ptr, I, K: Recast<I>, V: Recast<I>, B: ArenaBacking> Recast<I>
    for SurjectArena<P, K, V, B>
{
    /// Note that this recasts both keys and values (only the `Ptr`s are the
    /// keyed items from the `Recast` perspective)
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for key in self.keys_mut() {
            key.recast(recaster)?;
        }
        for val in self.vals_mut() {
            val.recast(recaster)?;
        }
        Ok(())
    }
}
