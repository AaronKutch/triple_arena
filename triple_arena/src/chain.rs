use core::{
    borrow::Borrow,
    fmt,
    fmt::{Debug, Display},
    hash::Hash,
    mem,
    ops::{Deref, DerefMut, Index, IndexMut},
};

use crate::{Arena, Ptr};

/// This represents a link in a `ChainArena` that has a public `t: T` field and
/// `Option<Ptr<PLink>>` interlinks to the previous and next links. Note that
/// `Deref` and `DerefMut` are implemented to grant direct access to the
/// methods on `T`. The interlinks are private and only accessible through
/// methods so that the whole `Link` can be returned by indexing the arena
/// without worrying about accidentally breaking the links (preventing a lot of
/// cumbersome code when traversing chains).
pub struct Link<PLink: Ptr, T> {
    // I think the code gen should be overall better if this is done
    prev_next: (Option<PLink>, Option<PLink>),
    pub t: T,
}

impl<PLink: Ptr, T> Link<PLink, T> {
    /// Get a `PLink` to the previous `Link` in the chain before `this`. Returns
    /// `None` if `this` is at the start of the chain.
    pub fn prev(this: &Link<PLink, T>) -> Option<PLink> {
        this.prev_next.0
    }

    /// Get a `PLink` to the next `Link` in the chain after `this`. Returns
    /// `None` if `this` is at the end of the chain.
    pub fn next(this: &Link<PLink, T>) -> Option<PLink> {
        this.prev_next.1
    }

    /// Shorthand for `(Link::prev(this), Link::next(this))`
    pub fn prev_next(this: &Link<PLink, T>) -> (Option<PLink>, Option<PLink>) {
        this.prev_next
    }

    /// Construct a `Link` from its raw components, this is not intended for
    /// general use and can easily break invariants.
    #[doc(hidden)]
    pub fn _from_raw(prev_next: (Option<PLink>, Option<PLink>), t: T) -> Self {
        Self { prev_next, t }
    }
}

impl<PLink: Ptr, T> Deref for Link<PLink, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.t
    }
}

impl<PLink: Ptr, T> DerefMut for Link<PLink, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.t
    }
}

/// This is a specially managed `Arena` for handling usecases involving `O(1)`
/// insertion, deletion, and other functions on linear lists of elements that we
/// call "chains" of "links". The arena supports multiple chains and cyclical
/// chains.
pub struct ChainArena<PLink: Ptr, T> {
    pub(crate) a: Arena<PLink, Link<PLink, T>>,
}

impl<PLink: Ptr, T> ChainArena<PLink, T> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        for (p, link) in &this.a {
            if let Some(prev) = Link::prev(link) {
                if let Some(prev) = this.a.get(prev) {
                    if let Some(next) = Link::next(prev) {
                        if p != next {
                            return Err("interlink does not correspond")
                        }
                    } else {
                        return Err("next node does not exist")
                    }
                } else {
                    return Err("prev node does not exist")
                }
            }
            // there are going to be duplicate checks but this must be done for invariant
            // breaking cases
            if let Some(next) = Link::next(link) {
                if let Some(next) = this.a.get(next) {
                    if let Some(prev) = Link::prev(next) {
                        if p != prev {
                            return Err("interlink does not correspond")
                        }
                    } else {
                        return Err("prev node does not exist")
                    }
                } else {
                    return Err("next node does not exist")
                }
            }
        }
        Ok(())
    }

    pub fn new() -> Self {
        Self { a: Arena::new() }
    }

    /// Returns the number of links in the arena
    pub fn len(&self) -> usize {
        self.a.len()
    }

    /// Returns if the arena is empty
    pub fn is_empty(&self) -> bool {
        self.a.is_empty()
    }

    /// Returns the capacity of the arena.
    pub fn capacity(&self) -> usize {
        self.a.capacity()
    }

    /// Follows [Arena::gen]
    pub fn gen(&self) -> PLink::Gen {
        self.a.gen()
    }

    /// Follows [Arena::reserve]
    pub fn reserve(&mut self, additional: usize) {
        self.a.reserve(additional)
    }

    /// If `prev_next.0.is_none() && prev_next.1.is_none()` then a new chain is
    /// started in the arena. If
    /// `prev_next.0.is_some() || prev_next.1.is_some()` then the link is
    /// inserted in an existing chain and the neighboring interlinks reroute to
    /// the new link. `prev_next.0.is_some() && prev_next.1.is_none()`
    /// and the reverse is allowed even if the link is not at the start or
    /// end of the chain; this function will detect this and derive the
    /// unknown `PLink`, inserting in the middle of the chain as usual. The
    /// `PLink` to the new link is returned.
    ///
    /// # Errors
    ///
    /// If a `PLink` is invalid, or `!self.are_neighbors(prev, next)`, then
    /// ownership of `t` is returned.
    pub fn insert(&mut self, prev_next: (Option<PLink>, Option<PLink>), t: T) -> Result<PLink, T> {
        match prev_next {
            // new chain
            (None, None) => Ok(self.a.insert(Link::_from_raw((None, None), t))),
            (None, Some(p1)) => {
                // if there is a failure it cannot result in a node being inserted
                if let Some(link) = self.a.get_mut(p1) {
                    if let Some(p0) = Link::prev(link) {
                        // insert into middle of chain
                        let res = self.a.insert(Link::_from_raw((Some(p0), Some(p1)), t));
                        self.a.get_mut(p0).unwrap().prev_next.1 = Some(res);
                        self.a.get_mut(p1).unwrap().prev_next.0 = Some(res);
                        Ok(res)
                    } else {
                        let res = self.a.insert(Link::_from_raw((None, Some(p1)), t));
                        self.a.get_mut(p1).unwrap().prev_next.0 = Some(res);
                        Ok(res)
                    }
                } else {
                    Err(t)
                }
            }
            (Some(p0), None) => {
                if let Some(link) = self.a.get_mut(p0) {
                    if let Some(p1) = Link::next(link) {
                        // insert into middle of chain
                        let res = self.a.insert(Link::_from_raw((Some(p0), Some(p1)), t));
                        self.a.get_mut(p0).unwrap().prev_next.1 = Some(res);
                        self.a.get_mut(p1).unwrap().prev_next.0 = Some(res);
                        Ok(res)
                    } else {
                        let res = self.a.insert(Link::_from_raw((Some(p0), None), t));
                        self.a.get_mut(p0).unwrap().prev_next.1 = Some(res);
                        Ok(res)
                    }
                } else {
                    Err(t)
                }
            }
            (Some(p0), Some(p1)) => {
                // check for existence and that the nodes are neighbors
                if !self.are_neighbors(p0, p1) {
                    return Err(t)
                }
                let res = self.a.insert(Link::_from_raw((Some(p0), Some(p1)), t));
                self.a.get_mut(p0).unwrap().prev_next.1 = Some(res);
                self.a.get_mut(p1).unwrap().prev_next.0 = Some(res);
                Ok(res)
            }
        }
    }

    /// Inserts `t` as a single link in a new chain and returns a `PLink` to it
    pub fn insert_new(&mut self, t: T) -> PLink {
        self.a.insert(Link::_from_raw((None, None), t))
    }

    /// Inserts `t` as a single link cyclical chain and returns a `PLink` to it
    pub fn insert_new_cyclic(&mut self, t: T) -> PLink {
        self.a
            .insert_with(|p| Link::_from_raw((Some(p), Some(p)), t))
    }

    /// Inserts `t` as a new link at the start of a chain which has `p` as its
    /// first link. Returns ownership of `t` if `p` is not valid or is not the
    /// start of a chain
    #[must_use]
    pub fn insert_start(&mut self, p: PLink, t: T) -> Option<PLink> {
        if Link::prev(self.a.get_mut(p)?).is_some() {
            // not at start of chain
            None
        } else {
            let res = Some(self.a.insert(Link::_from_raw((None, Some(p)), t)));
            self.a.get_mut(p).unwrap().prev_next.0 = res;
            res
        }
    }

    /// Inserts `t` as a new link at the end of a chain which has `p` as its
    /// last link. Returns ownership of `t` if `p` is not valid or is not the
    /// end of a chain
    #[must_use]
    pub fn insert_end(&mut self, p: PLink, t: T) -> Option<PLink> {
        if Link::next(self.a.get_mut(p)?).is_some() {
            // not at end of chain
            None
        } else {
            let res = Some(self.a.insert(Link::_from_raw((Some(p), None), t)));
            self.a.get_mut(p).unwrap().prev_next.1 = res;
            res
        }
    }

    /// Returns if `p` is a valid `PLink`
    pub fn contains(&self, p: PLink) -> bool {
        self.a.contains(p)
    }

    /// Returns if `p0` and `p1` are neighbors on the same chain, such that
    /// `Link::next(self[p0]) == Some(p1)` and `Link::prev(self[p1]) ==
    /// Some(p0)`. This is true for the single link cyclic chain case with
    /// `p0 == p1`. Incurs only one internal lookup because of invariants.
    /// Additionally returns `false` if `prev` or `next` are invalid `Ptr`s.
    pub fn are_neighbors(&self, p0: PLink, p1: PLink) -> bool {
        let mut are_neighbors = false;
        if let Some(l0) = self.a.get(p0) {
            if let Some(p) = Link::next(l0) {
                if p == p1 {
                    // `p1` must implicitly exist if the invariants hold
                    are_neighbors = true;
                }
            }
        }
        are_neighbors
    }

    /// Returns a reference to a link pointed to by `p`. Returns
    /// `None` if `p` is invalid.
    #[must_use]
    pub fn get(&self, p: PLink) -> Option<&Link<PLink, T>> {
        self.a.get(p)
    }

    /// Returns a mutable reference to a link pointed to by `p`.
    /// Returns `None` if `p` is invalid.
    #[must_use]
    pub fn get_mut(&mut self, p: PLink) -> Option<&mut Link<PLink, T>> {
        self.a.get_mut(p)
    }

    /// Gets two `&mut Link<PLink, T>` references pointed to by `p0` and `p1`.
    /// If `p0 == p1` or a pointer is invalid, `None` is returned.
    #[allow(clippy::type_complexity)]
    #[must_use]
    pub fn get2_mut(
        &mut self,
        p0: PLink,
        p1: PLink,
    ) -> Option<(&mut Link<PLink, T>, &mut Link<PLink, T>)> {
        self.a.get2_mut(p0, p1)
    }

    /// Removes the link at `p`. If the link is in the middle of the chain, the
    /// neighbors of `p` are rerouted to be neighbors of each other so that the
    /// chain remains continuous. Returns `None` if `p` is not valid.
    #[must_use]
    pub fn remove(&mut self, p: PLink) -> Option<Link<PLink, T>> {
        let l = self.a.remove(p)?;
        match Link::prev_next(&l) {
            (None, None) => (),
            (None, Some(p1)) => {
                self.a.get_mut(p1).unwrap().prev_next.0 = None;
            }
            (Some(p0), None) => {
                self.a.get_mut(p0).unwrap().prev_next.1 = None;
            }
            (Some(p0), Some(p1)) => {
                if p != p0 {
                    self.a.get_mut(p0).unwrap().prev_next.1 = Some(p1);
                    self.a.get_mut(p1).unwrap().prev_next.0 = Some(p0);
                } // else it is a single link circular chain
            }
        }
        Some(l)
    }

    /// Invalidates all references to the link pointed to by `p`, and returns a
    /// new valid reference. Does no invalidation and returns `None` if `p` is
    /// invalid.
    #[must_use]
    pub fn invalidate(&mut self, p: PLink) -> Option<PLink> {
        self.a.invalidate(p)
    }

    /// Swaps the `T` at indexes `p0` and `p1` and keeps the generation counters
    /// and link connections as-is. If `p0 == p1` then nothing occurs.
    /// Returns `None` if `p0` or `p1` are invalid.
    #[must_use]
    pub fn swap(&mut self, p0: PLink, p1: PLink) -> Option<()> {
        if p0 == p1 {
            // need to check that they are valid
            if self.contains(p0) && self.contains(p1) {
                Some(())
            } else {
                None
            }
        } else {
            let (lhs, rhs) = self.a.get2_mut(p0, p1)?;
            mem::swap(&mut lhs.t, &mut rhs.t);
            Some(())
        }
    }

    /// Connects the link at `p0` as previous to the link at `p1`. Returns
    /// `None` if `p0` has a next link, `p1` has a prev link, or the pointers
    /// are invalid.
    #[must_use]
    pub fn connect(&mut self, p0: PLink, p1: PLink) -> Option<()> {
        if Link::next(self.get(p0)?).is_none() && Link::prev(self.get(p1)?).is_none() {
            self[p0].prev_next.1 = Some(p1);
            self[p1].prev_next.0 = Some(p0);
            Some(())
        } else {
            None
        }
    }

    /// Breaks the previous interlink of `p`. Returns `None` if `p` is invalid
    /// or does not have a prev link.
    #[must_use]
    pub fn break_prev(&mut self, p: PLink) -> Option<()> {
        let u = Link::prev(self.get(p)?)?;
        self[p].prev_next.0 = None;
        self[u].prev_next.1 = None;
        Some(())
    }

    /// Breaks the next interlink of `p`. Returns `None` if `p` is invalid or
    /// does not have a next link.
    #[must_use]
    pub fn break_next(&mut self, p: PLink) -> Option<()> {
        let d = Link::next(self.get(p)?)?;
        self[p].prev_next.1 = None;
        self[d].prev_next.0 = None;
        Some(())
    }

    /// Exchanges the endpoints of the interlinks right after `p0` and `p1`.
    /// Returns `None` if the links do not have next interlinks or if the
    /// pointers are invalid.
    #[must_use]
    pub fn exchange_next(&mut self, p0: PLink, p1: PLink) -> Option<()> {
        if self.contains(p0) && self.contains(p1) {
            // get downstream links
            let d0 = Link::next(&self[p0])?;
            let d1 = Link::next(&self[p1])?;
            self[p0].prev_next.1 = Some(d1);
            self[p1].prev_next.1 = Some(d0);
            self[d0].prev_next.0 = Some(p1);
            self[d1].prev_next.0 = Some(p0);
            Some(())
        } else {
            None
        }
    }

    /// Drops all links from the arena and invalidates all pointers previously
    /// created from it. This has no effect on allocated capacity.
    pub fn clear(&mut self) {
        self.a.clear()
    }

    /// Performs an [ChainArena::clear] and resets capacity to 0
    pub fn clear_and_shrink(&mut self) {
        self.a.clear_and_shrink()
    }
}

impl<P: Ptr, T, B: Borrow<P>> Index<B> for ChainArena<P, T> {
    type Output = Link<P, T>;

    fn index(&self, index: B) -> &Self::Output {
        self.a.get(*index.borrow()).unwrap()
    }
}

impl<P: Ptr, T, B: Borrow<P>> IndexMut<B> for ChainArena<P, T> {
    fn index_mut(&mut self, index: B) -> &mut Self::Output {
        self.a.get_mut(*index.borrow()).unwrap()
    }
}

impl<P: Ptr, T: Debug> Debug for Link<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "({:?}, {:?}) {:?}",
            Link::prev(self),
            Link::next(self),
            self.t
        )
    }
}

impl<P: Ptr, T: Hash> Hash for Link<P, T> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.prev_next.hash(state);
        self.t.hash(state);
    }
}

impl<P: Ptr, T: Clone> Clone for Link<P, T> {
    fn clone(&self) -> Self {
        Self {
            prev_next: self.prev_next,
            t: self.t.clone(),
        }
    }
}

impl<P: Ptr, T: Copy> Copy for Link<P, T> {}

impl<P: Ptr, T: PartialEq> PartialEq for Link<P, T> {
    fn eq(&self, other: &Self) -> bool {
        (self.prev_next == other.prev_next) && (self.t == other.t)
    }
}

impl<P: Ptr, T: Eq> Eq for Link<P, T> {}

impl<P: Ptr, T: PartialOrd> PartialOrd for Link<P, T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        match self.prev_next.partial_cmp(&other.prev_next) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.t.partial_cmp(&other.t)
    }
}

impl<P: Ptr, T: Ord> Ord for Link<P, T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

// `Send` and `Sync` automatically implemented

impl<P: Ptr, T: Display> Display for Link<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "({:?}, {:?}) {}",
            Link::prev(self),
            Link::next(self),
            self.t
        )
    }
}

impl<P: Ptr, T: Debug> Debug for ChainArena<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.a)
    }
}

impl<P: Ptr, T: Clone> Clone for ChainArena<P, T> {
    fn clone(&self) -> Self {
        Self { a: self.a.clone() }
    }
}

impl<PLink: Ptr, T> Default for ChainArena<PLink, T> {
    fn default() -> Self {
        Self::new()
    }
}
