//! Iterators for `ChainArena`

pub use crate::iterators::{CapacityDrain, Drain, Iter, IterMut, Ptrs, Vals, ValsMut};
use crate::{ChainArena, Link, Ptr};

/// An iterator over `Link<P, &mut T>` in a `ChainArena`
pub struct ValsLinkMut<'a, P: Ptr, T> {
    iter_mut: ValsMut<'a, P, Link<P, T>>,
}

impl<'a, P: Ptr, T> Iterator for ValsLinkMut<'a, P, T> {
    type Item = Link<P, &'a mut T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut
            .next()
            .map(|link| Link::new(Link::prev_next(link), &mut link.t))
    }
}

/// An iterator for links in a chain in a `ChainArena`
pub struct IterChain<'a, P: Ptr, T> {
    arena: &'a ChainArena<P, T>,
    init: P,
    p: P,
    switch: bool,
    stop: bool,
}

impl<'a, P: Ptr, T> Iterator for IterChain<'a, P, T> {
    type Item = (P, &'a Link<P, T>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.stop {
            None
        } else {
            let p_res = self.p;
            self.arena
                .next_chain_ptr(self.init, &mut self.p, &mut self.switch, &mut self.stop);
            Some((p_res, self.arena.get(p_res).unwrap()))
        }
    }
}

/// A mutable iterator over `(P, Link<P, &mut T>)` in a `ChainArena`
pub struct IterLinkMut<'a, P: Ptr, T> {
    iter_mut: IterMut<'a, P, Link<P, T>>,
}

impl<'a, P: Ptr, T> Iterator for IterLinkMut<'a, P, T> {
    type Item = (P, Link<P, &'a mut T>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut
            .next()
            .map(|(p, link)| (p, Link::new(Link::prev_next(link), &mut link.t)))
    }
}

impl<'a, P: Ptr, T> IntoIterator for &'a ChainArena<P, T> {
    type IntoIter = Iter<'a, P, Link<P, T>>;
    type Item = (P, &'a Link<P, T>);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, P: Ptr, T> IntoIterator for &'a mut ChainArena<P, T> {
    type IntoIter = IterLinkMut<'a, P, T>;
    type Item = (P, Link<P, &'a mut T>);

    /// This returns an `IterMut`. Use `ChainArena::drain` for by-value
    /// consumption.
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<PLink: Ptr, T> ChainArena<PLink, T> {
    /// Iteration over all valid `PLink`s in the arena
    pub fn ptrs(&self) -> Ptrs<PLink, Link<PLink, T>> {
        self.a.ptrs()
    }

    /// Iteration over `&Link<PLink, T>`
    pub fn vals(&self) -> Vals<PLink, Link<PLink, T>> {
        self.a.vals()
    }

    /// Mutable iteration over `Link<PLink, &mut T>`
    pub fn vals_mut(&mut self) -> ValsLinkMut<PLink, T> {
        ValsLinkMut {
            iter_mut: self.a.vals_mut(),
        }
    }

    /// Iteration over `(PLink, &Link<PLink, T>)` tuples
    pub fn iter(&self) -> Iter<PLink, Link<PLink, T>> {
        self.a.iter()
    }

    /// Iteration over `(PLink, &Link<PLink, T>)` tuples corresponding to all
    /// links in the chain that `p` is connected to. If `p` was invalid, this
    /// iterator returns `None`.
    pub fn iter_chain(&self, p: PLink) -> IterChain<PLink, T> {
        IterChain {
            init: p,
            p,
            switch: false,
            stop: !self.contains(p),
            arena: self,
        }
    }

    /// Mutable iteration over `(PLink, Link<PLink, &mut T>)` tuples
    pub fn iter_mut(&mut self) -> IterLinkMut<PLink, T> {
        IterLinkMut {
            iter_mut: self.a.iter_mut(),
        }
    }

    /// Same as [Arena::drain]
    pub fn drain(&mut self) -> Drain<PLink, Link<PLink, T>> {
        self.a.drain()
    }

    /// Same as [Arena::capacity_drain]
    pub fn capacity_drain(self) -> CapacityDrain<PLink, Link<PLink, T>> {
        self.a.capacity_drain()
    }

    /// Same as [Arena::first_ptr]
    #[must_use]
    pub fn first_ptr(&self) -> (PLink, bool) {
        self.a.first_ptr()
    }

    /// Same as [Arena::next_ptr]
    pub fn next_ptr(&self, p: &mut PLink, b: &mut bool) {
        self.a.next_ptr(p, b);
    }

    /// Same as [Arena::next_ptr] except that this only iterates over elements
    /// of the chain that `p` is connected to. This does _not_ have a
    /// corresponding `first_chain_ptr` function, see the below recommended
    /// structure for calling this.
    ///
    /// ```text
    /// let init = ...;
    /// let mut p = init;
    /// let mut switch = false;
    /// let mut stop = !arena.contains(init);
    /// loop {
    ///     if stop {
    ///         break
    ///     }
    ///
    ///     // use `p` here, but be aware that the removal or insertion of
    ///     // elements within the chain of `init` is not supported
    ///
    ///     arena.next_chain_ptr(init, &mut p, &mut switch, &mut stop);
    /// }
    /// ```
    ///
    /// For the details on how this works (as long as you adhere to the format
    /// above, you do not have to worry about this): On the first iteration of
    /// "use `p` here", `p == init` is used. `next_chain_ptr` will then check
    /// for the next link. If the next link is equal to `init`, then we know we
    /// are in a cyclical chain and `stop` is set. If there is a next link, `p`
    /// is set to that next link and iteration progresses until the end of the
    /// chain. When the end of the chain is reached and there is no next link,
    /// `switch` is set and `p` is set to the link previous to `init` (or sets
    /// `stop` if there is no previous link). When `switch` is set previous
    /// links are similarly followed until the end of the chain, when `stop` is
    /// set.
    ///
    /// If `p` is invalid, `stop` is set, but should only ever be the case if
    /// the initial `init` was invalid.
    pub fn next_chain_ptr(&self, init: PLink, p: &mut PLink, switch: &mut bool, stop: &mut bool) {
        if *switch {
            let prev = if let Some(link) = self.a.get(*p) {
                if let Some(prev) = Link::prev(link) {
                    prev
                } else {
                    *stop = true;
                    return
                }
            } else {
                *stop = true;
                return
            };
            *p = prev;
        } else {
            let next = if let Some(link) = self.a.get(*p) {
                if let Some(next) = Link::next(link) {
                    next
                } else {
                    *switch = true;
                    // `init` was done on first iteration, we need to immediately use the previous
                    // node to `init`
                    if let Some(link) = self.a.get(init) {
                        if let Some(prev) = Link::prev(link) {
                            *p = prev;
                        } else {
                            *stop = true;
                        }
                    } else {
                        *stop = true;
                    }
                    return
                }
            } else {
                *stop = true;
                return
            };
            if next == init {
                // cyclical
                *stop = true;
                return
            }
            *p = next;
        }
    }
}