//! Iterators for `ChainNoGenArena`

use core::marker::PhantomData;

use recasting::{Recast, Recaster};

pub use crate::arena_iterators::{CapacityDrain, Drain, Iter, IterMut, Ptrs, Vals, ValsMut};
use crate::{
    arena_iterators,
    utils::{ChainNoGenArena, LinkNoGen},
    Advancer, Ptr,
};

/// An advancer over the valid `P`s of a `ChainNoGenArena`
pub struct PtrAdvancer<P: Ptr, T> {
    adv: arena_iterators::PtrAdvancer<P, LinkNoGen<P, T>>,
}

impl<P: Ptr, T> Advancer for PtrAdvancer<P, T> {
    type Collection = ChainNoGenArena<P, T>;
    type Item = P;

    fn advance(&mut self, collection: &Self::Collection) -> Option<Self::Item> {
        self.adv.advance(&collection.a)
    }
}

/// An advancer over the valid `P`s of one chain in a `ChainNoGenArena`
pub struct ChainPtrAdvancer<P: Ptr, T> {
    // the initial `Ptr` for checking if we are in a cycle
    init: P::Inx,
    // we ultimately want this in order to provide the extra guarantee that a removal and insertion
    // into the same spot can't cause the advancer to jump to an unrelated chain
    ptr: Option<P::Inx>,
    // switch to going in the previous direction
    switch: bool,
    // prevents infinite loops in case of various shenanigans
    max_advances: usize,
    _boo: PhantomData<(P, T)>,
}

impl<P: Ptr, T> Advancer for ChainPtrAdvancer<P, T> {
    type Collection = ChainNoGenArena<P, T>;
    type Item = P;

    fn advance(&mut self, collection: &Self::Collection) -> Option<Self::Item> {
        if self.max_advances == 0 {
            return None
        } else {
            self.max_advances = self.max_advances.wrapping_sub(1);
        }
        if let Some(ptr) = self.ptr {
            if self.switch {
                if let Some((gen, link)) = collection.a.get_ignore_gen(ptr) {
                    if let Some(prev) = link.prev() {
                        self.ptr = Some(prev);
                    } else {
                        self.ptr = None;
                    }
                    // note how we also get to implicitly check the validity of the original
                    // `self.ptr` without incurring extra lookups.
                    Some(Ptr::_from_raw(ptr, gen))
                } else {
                    self.ptr = None;
                    None
                }
            } else if let Some((gen, link)) = collection.a.get_ignore_gen(ptr) {
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
                    if let Some((_, link)) = collection.a.get_ignore_gen(self.init) {
                        self.ptr = link.prev();
                    } else {
                        self.ptr = None;
                    }
                }
                Some(Ptr::_from_raw(ptr, gen))
            } else {
                self.ptr = None;
                None
            }
        } else {
            None
        }
    }
}

/// An iterator over `LinkNoGen<P, &mut T>` in a `ChainNoGenArena`
pub struct ValsLinkMut<'a, P: Ptr, T> {
    iter_mut: ValsMut<'a, P, LinkNoGen<P, T>>,
}

impl<'a, P: Ptr, T> Iterator for ValsLinkMut<'a, P, T> {
    type Item = LinkNoGen<P, &'a mut T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut
            .next()
            .map(|link| LinkNoGen::new(link.prev_next(), &mut link.t))
    }
}

/// An iterator for links in a chain in a `ChainNoGenArena`
pub struct IterChain<'a, P: Ptr, T> {
    arena: &'a ChainNoGenArena<P, T>,
    adv: ChainPtrAdvancer<P, T>,
}

impl<'a, P: Ptr, T> Iterator for IterChain<'a, P, T> {
    type Item = (P, &'a LinkNoGen<P, T>);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.adv.advance(self.arena) {
            Some((p, self.arena.get_link(p).unwrap()))
        } else {
            None
        }
    }
}

/// A mutable iterator over `(P, LinkNoGen<P, &mut T>)` in a `ChainNoGenArena`
pub struct IterLinkMut<'a, P: Ptr, T> {
    iter_mut: IterMut<'a, P, LinkNoGen<P, T>>,
}

impl<'a, P: Ptr, T> Iterator for IterLinkMut<'a, P, T> {
    type Item = (P, LinkNoGen<P, &'a mut T>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut
            .next()
            .map(|(p, link)| (p, LinkNoGen::new(link.prev_next(), &mut link.t)))
    }
}

impl<P: Ptr, T> IntoIterator for ChainNoGenArena<P, T> {
    type IntoIter = CapacityDrain<P, LinkNoGen<P, T>>;
    type Item = (P, LinkNoGen<P, T>);

    fn into_iter(self) -> Self::IntoIter {
        self.capacity_drain()
    }
}

impl<'a, P: Ptr, T> IntoIterator for &'a ChainNoGenArena<P, T> {
    type IntoIter = Iter<'a, P, LinkNoGen<P, T>>;
    type Item = (P, &'a LinkNoGen<P, T>);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, P: Ptr, T> IntoIterator for &'a mut ChainNoGenArena<P, T> {
    type IntoIter = IterLinkMut<'a, P, T>;
    type Item = (P, LinkNoGen<P, &'a mut T>);

    /// This returns an `IterMut`. Use `ChainNoGenArena::drain` for by-value
    /// consumption.
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<P: Ptr, T> FromIterator<T> for ChainNoGenArena<P, T> {
    /// Inserts as single link chains
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut a = ChainNoGenArena::new();
        for t in iter {
            a.insert_new(t);
        }
        a
    }
}

/// All the iterators here can return values in arbitrary order, except for
/// [ChainNoGenArena::advancer_chain].
impl<P: Ptr, T> ChainNoGenArena<P, T> {
    /// Advances over every valid `Ptr` in `self`.
    ///
    /// Has the same properties as [crate::Arena::advancer]
    pub fn advancer(&self) -> PtrAdvancer<P, T> {
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
    pub fn advancer_chain(&self, p_init: P::Inx) -> ChainPtrAdvancer<P, T> {
        ChainPtrAdvancer {
            init: p_init,
            ptr: Some(p_init),
            switch: false,
            max_advances: self.len(),
            _boo: PhantomData,
        }
    }

    /// Iteration over all valid `P`s in the arena
    pub fn ptrs(&self) -> Ptrs<P, LinkNoGen<P, T>> {
        self.a.ptrs()
    }

    /// Iteration over `&LinkNoGen<P, T>`
    pub fn vals(&self) -> Vals<P, LinkNoGen<P, T>> {
        self.a.vals()
    }

    /// Mutable iteration over `LinkNoGen<P, &mut T>`
    pub fn vals_mut(&mut self) -> ValsLinkMut<P, T> {
        ValsLinkMut {
            iter_mut: self.a.vals_mut(),
        }
    }

    /// Iteration over `(P, &LinkNoGen<P, T>)` tuples
    pub fn iter(&self) -> Iter<P, LinkNoGen<P, T>> {
        self.a.iter()
    }

    /// Iteration over `(P, &LinkNoGen<P, T>)` tuples corresponding to all
    /// links in the chain that `p_init` is connected to, according to the order
    /// of [ChainNoGenArena::advancer_chain]
    pub fn iter_chain(&self, p_init: P::Inx) -> IterChain<P, T> {
        let adv = self.advancer_chain(p_init);
        IterChain { arena: self, adv }
    }

    /// Mutable iteration over `(P, LinkNoGen<P, &mut T>)` tuples
    pub fn iter_mut(&mut self) -> IterLinkMut<P, T> {
        IterLinkMut {
            iter_mut: self.a.iter_mut(),
        }
    }

    /// Same as [crate::Arena::drain]
    pub fn drain(&mut self) -> Drain<P, LinkNoGen<P, T>> {
        self.a.drain()
    }

    /// Same as [crate::Arena::capacity_drain]
    pub fn capacity_drain(self) -> CapacityDrain<P, LinkNoGen<P, T>> {
        self.a.capacity_drain()
    }

    /// Performs [ChainNoGenArena::compress_and_shrink] and returns an `Arena<P,
    /// P>` that can be used for [Recast]ing
    pub fn compress_and_shrink_recaster(&mut self) -> crate::Arena<P, P> {
        let mut res = crate::Arena::<P, P>::new();
        self.clone_to_arena(&mut res, |_, _| P::invalid());
        self.compress_and_shrink_with(|p, _, q| *res.get_mut(p).unwrap() = q);
        res
    }
}

impl<P: Ptr, I, T: Recast<I>> Recast<I> for ChainNoGenArena<P, T> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for val in self.vals_mut() {
            val.t.recast(recaster)?;
        }
        Ok(())
    }
}
