//! Iterators for `ChainArena`

use recasting::{Recast, Recaster};

pub use crate::arena_iterators::{CapacityDrain, Drain, Iter, IterMut, Ptrs, Vals, ValsMut};
use crate::{
    Arena, ChainArena, Link, arena_iterators,
    traits::{Advancer, Ptr},
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
            adv: <arena_iterators::PtrAdvancer<P> as Advancer<Arena<P, Link<P, T>, B>>>::empty(),
        }
    }
}

/// An advancer over the valid `P`s of one chain in a `ChainArena`
pub struct ChainPtrAdvancer<P: Ptr> {
    // the initial `Ptr` for checking if we are in a cycle
    init: P,
    // we ultimately want this in order to provide the extra guarantee that a removal and insertion
    // into the same spot can't cause the advancer to jump to an unrelated chain
    ptr: Option<P>,
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
                if let Some(link) = collection.a.get(ptr) {
                    if let Some(prev) = link.prev() {
                        self.ptr = Some(prev);
                    } else {
                        self.ptr = None;
                    }
                    // note how we also get to implicitly check the validity of the original
                    // `self.ptr` without incurring extra lookups.
                    Some(ptr)
                } else {
                    self.ptr = None;
                    None
                }
            } else if let Some(link) = collection.a.get(ptr) {
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
                    if let Some(link) = collection.a.get(self.init) {
                        self.ptr = link.prev();
                    } else {
                        self.ptr = None;
                    }
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

    fn empty() -> Self {
        // `max_advances: 0` guarantees empty
        Self {
            init: P::invalid(),
            ptr: None,
            switch: false,
            max_advances: 0,
        }
    }
}

/// An iterator over `Link<P, &mut T>` in a `ChainArena`
pub struct ValsLinkMut<'a, P: Ptr, T, B: ArenaBacking> {
    iter_mut: ValsMut<'a, P, Link<P, T>, B>,
}

impl<'a, P: Ptr, T, B: ArenaBacking> Iterator for ValsLinkMut<'a, P, T, B> {
    type Item = Link<P, &'a mut T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut
            .next()
            .map(|link| Link::new(link.prev_next(), &mut link.t))
    }
}

/// An iterator for links in a chain in a `ChainArena`
pub struct IterChain<'a, P: Ptr, T, B: ArenaBacking> {
    arena: &'a ChainArena<P, T, B>,
    adv: ChainPtrAdvancer<P>,
}

impl<'a, P: Ptr, T, B: ArenaBacking> Iterator for IterChain<'a, P, T, B> {
    type Item = (P, &'a Link<P, T>);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.adv.advance(self.arena) {
            Some((p, self.arena.get_link(p).unwrap()))
        } else {
            None
        }
    }
}

/// A mutable iterator over `(P, Link<P, &mut T>)` in a `ChainArena`
pub struct IterLinkMut<'a, P: Ptr, T, B: ArenaBacking> {
    iter_mut: IterMut<'a, P, Link<P, T>, B>,
}

impl<'a, P: Ptr, T, B: ArenaBacking> Iterator for IterLinkMut<'a, P, T, B> {
    type Item = (P, Link<P, &'a mut T>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut
            .next()
            .map(|(p, link)| (p, Link::new(link.prev_next(), &mut link.t)))
    }
}

impl<P: Ptr, T, B: ArenaBacking> IntoIterator for ChainArena<P, T, B> {
    type IntoIter = CapacityDrain<P, Link<P, T>, B>;
    type Item = (P, Link<P, T>);

    fn into_iter(self) -> Self::IntoIter {
        self.capacity_drain()
    }
}

impl<'a, P: Ptr, T, B: ArenaBacking> IntoIterator for &'a ChainArena<P, T, B> {
    type IntoIter = Iter<'a, P, Link<P, T>, B>;
    type Item = (P, &'a Link<P, T>);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, P: Ptr, T, B: ArenaBacking> IntoIterator for &'a mut ChainArena<P, T, B> {
    type IntoIter = IterLinkMut<'a, P, T, B>;
    type Item = (P, Link<P, &'a mut T>);

    /// This returns an `IterMut`. Use `ChainArena::drain` for by-value
    /// consumption.
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<P: Ptr, T, B: ArenaBacking> FromIterator<T> for ChainArena<P, T, B> {
    /// Inserts as single link chains
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut a = ChainArena::new();
        for t in iter {
            a.insert_new(t);
        }
        a
    }
}

/// All the iterators here can return values in arbitrary order, except for
/// [ChainArena::advancer_chain].
impl<P: Ptr, T, B: ArenaBacking> ChainArena<P, T, B> {
    /// Advances over every valid `Ptr` in `self`.
    ///
    /// Has the same properties as [crate::Arena::advancer]
    pub fn advancer(&self) -> PtrAdvancer<P> {
        PtrAdvancer {
            adv: self.a.advancer(),
        }
    }

    /// Advances over every valid `Ptr` in the chain that contains `p_init`.
    /// This does _not_ support invalidating `Ptr`s or changing the interlinks
    /// of the chain of `p_init` during the loop.
    ///
    /// # Note
    ///
    /// This handles cyclical chains, however if links or interlinks of the
    /// chain that contains `p_init` are invalidated during the loop, or if the
    /// chain starts as noncyclical and is reconnected to become cyclical during
    /// the loop, it can lead to a loop where the same `Ptr` can be returned
    /// multiple times. There is a internal fail safe that prevents
    /// non-termination.
    pub fn advancer_chain(&self, p_init: P) -> ChainPtrAdvancer<P> {
        ChainPtrAdvancer {
            init: p_init,
            ptr: Some(p_init),
            switch: false,
            max_advances: self.len(),
        }
    }

    /// Iteration over all valid `P`s in the arena
    pub fn ptrs(&self) -> Ptrs<'_, P, Link<P, T>, B> {
        self.a.ptrs()
    }

    /// Iteration over `&Link<P, T>`
    pub fn vals(&self) -> Vals<'_, P, Link<P, T>, B> {
        self.a.vals()
    }

    /// Mutable iteration over `Link<P, &mut T>`
    pub fn vals_mut(&mut self) -> ValsLinkMut<'_, P, T, B> {
        ValsLinkMut {
            iter_mut: self.a.vals_mut(),
        }
    }

    /// Iteration over `(P, &Link<P, T>)` tuples
    pub fn iter(&self) -> Iter<'_, P, Link<P, T>, B> {
        self.a.iter()
    }

    /// Iteration over `(P, &Link<P, T>)` tuples corresponding to all
    /// links in the chain that `p_init` is connected to, according to the order
    /// of [ChainArena::advancer_chain]
    pub fn iter_chain(&self, p_init: P) -> IterChain<'_, P, T, B> {
        let adv = self.advancer_chain(p_init);
        IterChain { arena: self, adv }
    }

    /// Mutable iteration over `(P, Link<P, &mut T>)` tuples
    pub fn iter_mut(&mut self) -> IterLinkMut<'_, P, T, B> {
        IterLinkMut {
            iter_mut: self.a.iter_mut(),
        }
    }

    /// Same as [crate::Arena::drain]
    pub fn drain(&mut self) -> Drain<'_, P, Link<P, T>, B> {
        self.a.drain()
    }

    /// Same as [crate::Arena::capacity_drain]
    pub fn capacity_drain(self) -> CapacityDrain<P, Link<P, T>, B> {
        self.a.capacity_drain()
    }

    /// Performs [ChainArena::compress_and_shrink] and returns an `Arena<P, P>`
    /// that can be used for [Recast]ing
    pub fn compress_and_shrink_recaster(&mut self) -> crate::Arena<P, P, B> {
        let mut res = crate::Arena::<P, P, B>::new();
        self.clone_to_arena(&mut res, |_, _| P::invalid());
        self.compress_and_shrink_with(|p, _, q| *res.get_mut(p).unwrap() = q);
        res
    }
}

impl<P: Ptr, I, T: Recast<I>, B: ArenaBacking> Recast<I> for ChainArena<P, T, B> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for val in self.vals_mut() {
            val.t.recast(recaster)?;
        }
        Ok(())
    }
}

impl<P: Ptr, T: Recast<P>> Recast<P> for Link<P, T> {
    /// Recasts both the interlinks and the `T`
    fn recast<R: Recaster<Item = P>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        self.prev_next.recast(recaster)?;
        self.t.recast(recaster)?;
        Ok(())
    }
}
