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

impl<P: Ptr, T> IntoIterator for ChainArena<P, T> {
    type IntoIter = CapacityDrain<P, Link<P, T>>;
    type Item = (P, Link<P, T>);

    fn into_iter(self) -> Self::IntoIter {
        self.capacity_drain()
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

impl<P: Ptr, T> FromIterator<T> for ChainArena<P, T> {
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
/// [ChainArena::next_chain_ptr].
impl<P: Ptr, T> ChainArena<P, T> {
    /// Iteration over all valid `P`s in the arena
    pub fn ptrs(&self) -> Ptrs<P, Link<P, T>> {
        self.a.ptrs()
    }

    /// Iteration over `&Link<P, T>`
    pub fn vals(&self) -> Vals<P, Link<P, T>> {
        self.a.vals()
    }

    /// Mutable iteration over `Link<P, &mut T>`
    pub fn vals_mut(&mut self) -> ValsLinkMut<P, T> {
        ValsLinkMut {
            iter_mut: self.a.vals_mut(),
        }
    }

    /// Iteration over `(P, &Link<P, T>)` tuples
    pub fn iter(&self) -> Iter<P, Link<P, T>> {
        self.a.iter()
    }

    /// Iteration over `(P, &Link<P, T>)` tuples corresponding to all
    /// links in the chain that `p` is connected to. This starts at the link
    /// pointed to by `p` and iterates along the `next` direction until it
    /// reaches the end of the chain (or reaches `p` again if the chain is
    /// cyclical), then it iterates in the reverse direction starting from the
    /// link before `p` if it exists. If `p` was invalid, this
    /// iterator returns `None`.
    pub fn iter_chain(&self, p: P) -> IterChain<P, T> {
        IterChain {
            init: p,
            p,
            switch: false,
            stop: !self.contains(p),
            arena: self,
        }
    }

    /// Mutable iteration over `(P, Link<P, &mut T>)` tuples
    pub fn iter_mut(&mut self) -> IterLinkMut<P, T> {
        IterLinkMut {
            iter_mut: self.a.iter_mut(),
        }
    }

    /// Same as [crate::Arena::drain]
    pub fn drain(&mut self) -> Drain<P, Link<P, T>> {
        self.a.drain()
    }

    /// Same as [crate::Arena::capacity_drain]
    pub fn capacity_drain(self) -> CapacityDrain<P, Link<P, T>> {
        self.a.capacity_drain()
    }

    /// Same as [crate::Arena::first_ptr]
    #[must_use]
    pub fn first_ptr(&self) -> (P, bool) {
        self.a.first_ptr()
    }

    /// Same as [crate::Arena::next_ptr]
    pub fn next_ptr(&self, p: &mut P, b: &mut bool) {
        self.a.next_ptr(p, b);
    }

    /// Same as [crate::Arena::next_ptr] except that this only iterates over
    /// elements of the chain that `p` is connected to. This does _not_ have
    /// a corresponding `first_chain_ptr` function, see the below
    /// recommended structure for calling this.
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
    pub fn next_chain_ptr(&self, init: P, p: &mut P, switch: &mut bool, stop: &mut bool) {
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
