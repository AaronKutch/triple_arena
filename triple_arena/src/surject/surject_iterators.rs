//! Iterators for `SurjectArena`

use recasting::{Recast, Recaster};

use crate::{
    Arena, SurjectArena,
    arena_iterators::{self},
    chain::ChainNoGenArena,
    surject::{Key, Val},
    traits::{Advancer, ArenaTrait, Ptr},
    utils::{LinkNoGen, PtrNoGen, chain_no_gen_iterators, traits::ArenaBacking},
};

/// An advancer over the valid `P`s of a `SurjectArena`
pub struct PtrAdvancer<P: Ptr> {
    adv: chain_no_gen_iterators::PtrAdvancer<P>,
}

impl<P: Ptr, K, V, B: ArenaBacking> Advancer<SurjectArena<P, K, V, B>> for PtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &SurjectArena<P, K, V, B>) -> Option<Self::Item> {
        self.adv.advance(&collection.keys)
    }

    fn empty() -> Self {
        Self {
            adv: <chain_no_gen_iterators::PtrAdvancer<P> as Advancer<
                ChainNoGenArena<P, Key<P, K>, B>,
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

impl<P: Ptr, K, V, B: ArenaBacking> Advancer<SurjectArena<P, K, V, B>> for SurjectPtrAdvancer<P> {
    type Item = P;

    fn advance(&mut self, collection: &SurjectArena<P, K, V, B>) -> Option<Self::Item> {
        if self.max_advances == 0 {
            return None;
        } else {
            self.max_advances = self.max_advances.wrapping_sub(1);
        }
        if let Some(ptr) = self.ptr {
            if let Some((generation, link)) = collection.keys.get_no_gen(ptr) {
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

/// An iterator over the valid `P`s of a `SurjectArena`
pub struct Ptrs<'a, P: Ptr, K, B: ArenaBacking> {
    iter: arena_iterators::Ptrs<'a, P, LinkNoGen<P, Key<P, K>>, B>,
}

impl<P: Ptr, K, B: ArenaBacking> Iterator for Ptrs<'_, P, K, B> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

/// An iterator over `&K` in a `SurjectArena`
pub struct Keys<'a, P: Ptr, K, B: ArenaBacking> {
    iter: arena_iterators::Vals<'a, P, LinkNoGen<P, Key<P, K>>, B>,
}

impl<'a, P: Ptr, K, B: ArenaBacking> Iterator for Keys<'a, P, K, B> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|link| &link.t.k)
    }
}

/// An iterator over `&V` in a `SurjectArena`
pub struct Vals<'a, P: Ptr, V, B: ArenaBacking> {
    iter: arena_iterators::Vals<'a, PtrNoGen<P>, Val<V>, B>,
}

impl<'a, P: Ptr, V, B: ArenaBacking> Iterator for Vals<'a, P, V, B> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|v| &v.v)
    }
}

/// A mutable iterator over `&mut K` in a `SurjectArena`
pub struct KeysMut<'a, P: Ptr, K, B: ArenaBacking> {
    iter_mut: chain_no_gen_iterators::ValsLinkMut<'a, P, Key<P, K>, B>,
}

impl<'a, P: Ptr, K, B: ArenaBacking> Iterator for KeysMut<'a, P, K, B> {
    type Item = &'a mut K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut.next().map(|link| &mut link.t.k)
    }
}

/// A mutable iterator over `&mut V` in a `SurjectArena`
pub struct ValsMut<'a, P: Ptr, V, B: ArenaBacking> {
    iter_mut: arena_iterators::ValsMut<'a, PtrNoGen<P>, Val<V>, B>,
}

impl<'a, P: Ptr, V, B: ArenaBacking> Iterator for ValsMut<'a, P, V, B> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut.next().map(|v| &mut v.v)
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

// I don't think it would be safe to implement an `IterMut` because the same
// values would be returned multiple times

impl<'a, P: Ptr, K, V, B: ArenaBacking> IntoIterator for &'a SurjectArena<P, K, V, B> {
    type IntoIter = Iter<'a, P, K, V, B>;
    type Item = (P, &'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// All the iterators here can return values in arbitrary order
impl<P: Ptr, K, V, B: ArenaBacking> SurjectArena<P, K, V, B> {
    /// Advances over every valid `Ptr` in `self`.
    ///
    /// Has the same properties as [crate::Arena::advancer]
    pub fn advancer(&self) -> PtrAdvancer<P> {
        PtrAdvancer {
            adv: self.keys.advancer(),
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
    pub fn advancer_surject(&self, p_init: P) -> SurjectPtrAdvancer<P> {
        SurjectPtrAdvancer {
            init: p_init.inx(),
            ptr: Some(p_init.inx()),
            max_advances: self.len_keys(),
        }
    }

    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> Ptrs<'_, P, K, B> {
        Ptrs {
            iter: self.keys.ptrs(),
        }
    }

    /// Iteration over `&K`
    pub fn keys(&self) -> Keys<'_, P, K, B> {
        Keys {
            iter: self.keys.vals(),
        }
    }

    /// Iteration over `&V`
    pub fn vals(&self) -> Vals<'_, P, V, B> {
        Vals {
            iter: self.vals.old_vals(),
        }
    }

    /// Mutable iteration over `&mut K`
    pub fn keys_mut(&mut self) -> KeysMut<'_, P, K, B> {
        KeysMut {
            iter_mut: self.keys.vals_mut(),
        }
    }

    /// Mutable iteration over `&mut V`
    pub fn vals_mut(&mut self) -> ValsMut<'_, P, V, B> {
        ValsMut {
            iter_mut: self.vals.old_vals_mut(),
        }
    }

    /// Iteration over `(P, &K, &V)` tuples. For each surject with multiple `P`
    /// pointing to the same `V`, the same reference to the `V` is returned
    /// multiple times
    pub fn iter(&self) -> Iter<'_, P, K, V, B> {
        Iter {
            iter: self.keys.iter(),
            vals: &self.vals,
        }
    }

    /// Iteration over `(P, &K, &V)` tuples in the surject that contains
    /// `p_init`. The same `&V` reference is used for all iterations.
    pub fn iter_surject(&self, p_init: P) -> IterSurject<'_, P, K, V, B> {
        IterSurject {
            arena: self,
            adv: self.advancer_surject(p_init),
            surject_val: self.get_val(p_init),
        }
    }

    /// Performs [SurjectArena::compress_and_shrink] and returns an `Arena<P,
    /// P>` that can be used for [Recast]ing
    pub fn compress_and_shrink_recaster(&mut self) -> crate::Arena<P, P, B> {
        let mut res = crate::Arena::<P, P, B>::new();
        self.clone_keys_to_arena(&mut res, |_, _| P::invalid());
        self.compress_and_shrink_with(|p, _, _, q| *res.get_mut(p).unwrap() = q);
        res
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
