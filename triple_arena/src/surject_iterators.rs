//! Iterators for `SurjectArena`

use core::marker::PhantomData;

use recasting::{Recast, Recaster};

use crate::{
    arena_iterators::{self},
    chain_iterators,
    surject::{Key, Val},
    utils::PtrNoGen,
    Advancer, Arena, Link, Ptr, SurjectArena,
};

/// An advancer over the valid `P`s of a `SurjectArena`
pub struct PtrAdvancer<P: Ptr, K, V> {
    adv: chain_iterators::PtrAdvancer<P, Key<P, K>>,
    _boo: PhantomData<V>,
}

impl<P: Ptr, K, V> Advancer for PtrAdvancer<P, K, V> {
    type Collection = SurjectArena<P, K, V>;
    type Item = P;

    fn advance(&mut self, collection: &Self::Collection) -> Option<Self::Item> {
        self.adv.advance(&collection.keys)
    }
}

/// An advancer over the valid `P`s of one surject in a `SurjectArena`
pub struct SurjectPtrAdvancer<P: Ptr, K, V> {
    // same as for `ChainPtrAdvancer` except we get to assume the chain is cyclical
    init: P,
    ptr: Option<P>,
    // prevent infinite loops
    max_advances: usize,
    _boo: PhantomData<(K, V)>,
}

impl<P: Ptr, K, V> Advancer for SurjectPtrAdvancer<P, K, V> {
    type Collection = SurjectArena<P, K, V>;
    type Item = P;

    fn advance(&mut self, collection: &Self::Collection) -> Option<Self::Item> {
        if self.max_advances == 0 {
            return None
        } else {
            self.max_advances = self.max_advances.wrapping_sub(1);
        }
        if let Some(ptr) = self.ptr {
            if let Some(link) = collection.keys.get_link(ptr) {
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
                Some(ptr)
            } else {
                self.ptr = None;
                None
            }
        } else {
            None
        }
    }
}

/// An iterator over the valid `P`s of a `SurjectArena`
pub struct Ptrs<'a, P: Ptr, K> {
    iter: arena_iterators::Ptrs<'a, P, Link<P, Key<P, K>>>,
}

impl<'a, P: Ptr, K> Iterator for Ptrs<'a, P, K> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

/// An iterator over `&K` in a `SurjectArena`
pub struct Keys<'a, P: Ptr, K> {
    iter: arena_iterators::Vals<'a, P, Link<P, Key<P, K>>>,
}

impl<'a, P: Ptr, K> Iterator for Keys<'a, P, K> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|link| &link.t.k)
    }
}

/// An iterator over `&V` in a `SurjectArena`
pub struct Vals<'a, P: Ptr, V> {
    iter: arena_iterators::Vals<'a, PtrNoGen<P>, Val<V>>,
}

impl<'a, P: Ptr, V> Iterator for Vals<'a, P, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|v| &v.v)
    }
}

/// A mutable iterator over `&mut K` in a `SurjectArena`
pub struct KeysMut<'a, P: Ptr, K> {
    iter_mut: chain_iterators::ValsLinkMut<'a, P, Key<P, K>>,
}

impl<'a, P: Ptr, K> Iterator for KeysMut<'a, P, K> {
    type Item = &'a mut K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut.next().map(|link| &mut link.t.k)
    }
}

/// A mutable iterator over `&mut V` in a `SurjectArena`
pub struct ValsMut<'a, P: Ptr, V> {
    iter_mut: arena_iterators::ValsMut<'a, PtrNoGen<P>, Val<V>>,
}

impl<'a, P: Ptr, V> Iterator for ValsMut<'a, P, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut.next().map(|v| &mut v.v)
    }
}

/// An iterator over `(P, &K, &V)` in a `SurjectArena`
pub struct Iter<'a, P: Ptr, K, V> {
    iter: arena_iterators::Iter<'a, P, Link<P, Key<P, K>>>,
    vals: &'a Arena<PtrNoGen<P>, Val<V>>,
}

impl<'a, P: Ptr, K, V> Iterator for Iter<'a, P, K, V> {
    type Item = (P, &'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let (p, link) = self.iter.next()?;
        Some((p, &link.t.k, &self.vals.get(link.t.p_val).unwrap().v))
    }
}

/// An iterator over `(P, &K, &V)` in a `SurjectArena` surject
pub struct IterSurject<'a, P: Ptr, K, V> {
    arena: &'a SurjectArena<P, K, V>,
    adv: SurjectPtrAdvancer<P, K, V>,
    surject_val: Option<&'a V>,
}

impl<'a, P: Ptr, K, V> Iterator for IterSurject<'a, P, K, V> {
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

impl<'a, P: Ptr, K, V> IntoIterator for &'a SurjectArena<P, K, V> {
    type IntoIter = Iter<'a, P, K, V>;
    type Item = (P, &'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// All the iterators here can return values in arbitrary order
impl<P: Ptr, K, V> SurjectArena<P, K, V> {
    /// Advances over every valid `Ptr` in `self`.
    ///
    /// Has the same properties as [crate::Arena::advancer]
    pub fn advancer(&self) -> PtrAdvancer<P, K, V> {
        PtrAdvancer {
            adv: self.keys.advancer(),
            _boo: PhantomData,
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
    pub fn advancer_surject(&self, p_init: P) -> SurjectPtrAdvancer<P, K, V> {
        SurjectPtrAdvancer {
            init: p_init,
            ptr: Some(p_init),
            max_advances: self.len_keys(),
            _boo: PhantomData,
        }
    }

    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> Ptrs<P, K> {
        Ptrs {
            iter: self.keys.ptrs(),
        }
    }

    /// Iteration over `&K`
    pub fn keys(&self) -> Keys<P, K> {
        Keys {
            iter: self.keys.vals(),
        }
    }

    /// Iteration over `&V`
    pub fn vals(&self) -> Vals<P, V> {
        Vals {
            iter: self.vals.vals(),
        }
    }

    /// Mutable iteration over `&mut K`
    pub fn keys_mut(&mut self) -> KeysMut<P, K> {
        KeysMut {
            iter_mut: self.keys.vals_mut(),
        }
    }

    /// Mutable iteration over `&mut V`
    pub fn vals_mut(&mut self) -> ValsMut<P, V> {
        ValsMut {
            iter_mut: self.vals.vals_mut(),
        }
    }

    /// Iteration over `(P, &K, &V)` tuples. For each surject with multiple `P`
    /// pointing to the same `V`, the same reference to the `V` is returned
    /// multiple times
    pub fn iter(&self) -> Iter<P, K, V> {
        Iter {
            iter: self.keys.iter(),
            vals: &self.vals,
        }
    }

    /// Iteration over `(P, &K, &V)` tuples in the surject that contains
    /// `p_init`. The same `&V` reference is used for all iterations.
    pub fn iter_surject(&self, p_init: P) -> IterSurject<P, K, V> {
        IterSurject {
            arena: self,
            adv: self.advancer_surject(p_init),
            surject_val: self.get_val(p_init),
        }
    }

    /// Performs [SurjectArena::compress_and_shrink] and returns an `Arena<P,
    /// P>` that can be used for [Recast]ing
    pub fn compress_and_shrink_recaster(&mut self) -> crate::Arena<P, P> {
        let mut res = crate::Arena::<P, P>::new();
        self.clone_keys_to_arena(&mut res, |_, _| P::invalid());
        self.compress_and_shrink_with(|p, _, _, q| *res.get_mut(p).unwrap() = q);
        res
    }
}

impl<P: Ptr, I, K: Recast<I>, V: Recast<I>> Recast<I> for SurjectArena<P, K, V> {
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
