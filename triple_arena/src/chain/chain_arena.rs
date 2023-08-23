use core::{
    borrow::Borrow,
    fmt,
    fmt::{Debug, Display},
    hash::Hash,
    mem,
    ops::{Index, IndexMut},
};

use crate::{Advancer, Arena, Ptr};

/// This represents a link in a `ChainArena` that has a public `t: T` field and
/// `Option<Ptr<P>>` interlinks to the previous and next links.
pub struct Link<P: Ptr, T> {
    // I think the code gen should be overall better if this is done
    pub(crate) prev_next: (Option<P>, Option<P>),
    pub t: T,
}

impl<P: Ptr, T> Link<P, T> {
    /// Get a `Ptr` to the previous `Link` in the chain before `self`. Returns
    /// `None` if `self` is at the start of the chain.
    pub fn prev(&self) -> Option<P> {
        self.prev_next.0
    }

    /// Get a `Ptr` to the next `Link` in the chain after `self`. Returns
    /// `None` if `self` is at the end of the chain.
    pub fn next(&self) -> Option<P> {
        self.prev_next.1
    }

    /// Shorthand for `(self.prev(), self.next())`
    pub fn prev_next(&self) -> (Option<P>, Option<P>) {
        self.prev_next
    }

    /// Construct a `Link` from its components
    pub fn new(prev_next: (Option<P>, Option<P>), t: T) -> Self {
        Self { prev_next, t }
    }
}

/// A doubly-linked-list based on an arena for handling usecases involving
/// `O(1)` insertion, deletion, and other functions on linear lists of elements
/// that we call "chains" of "links". Multiple separate chains and cyclical
/// chains are supported.
///
/// ```
/// use triple_arena::{ptr_struct, ChainArena, Link};
///
/// ptr_struct!(P0);
/// let mut a: ChainArena<P0, String> = ChainArena::new();
///
/// let p_a = a.insert_new("A".to_owned());
/// let p_b = a.insert_new("B".to_owned());
///
/// // initially, all entries from `insert_new` have `None` interlinks and
/// // are each in their own single link chains, and are completely
/// // unassociated like in a normal `Arena`.
///
/// let link = a.get_link(p_a).unwrap();
/// assert_eq!(link.t, "A");
/// assert!(link.prev().is_none());
/// assert!(link.next().is_none());
///
/// let link = a.get_link(p_b).unwrap();
/// assert_eq!(link.t, "B");
/// assert!(link.prev().is_none());
/// assert!(link.next().is_none());
///
/// assert!(!a.are_neighbors(p_a, p_b));
///
/// // Connect the two links by making the `next` interlink of A point to B,
/// // and the `prev` interlink of B point to A. Note that this is directional
/// // and that `a.connect(p_b, p_a).unwrap()` would result B being the start
/// // and A being the end of the chain instead.
/// a.connect(p_a, p_b).unwrap();
///
/// let link = a.get_link(p_a).unwrap();
/// assert_eq!(link.t, "A");
/// assert!(link.prev().is_none());
/// assert_eq!(link.next().unwrap(), p_b);
///
/// let link = a.get_link(p_b).unwrap();
/// assert_eq!(link.t, "B");
/// assert_eq!(link.prev().unwrap(), p_a);
/// assert!(link.next().is_none());
///
/// assert!(a.are_neighbors(p_a, p_b));
/// assert!(!a.are_neighbors(p_b, p_a));
///
/// // Now let us insert a third link and make it the end of the existing chain
/// // by using `insert_end`.
///
/// // `insert_end` guards against attaching to any part of a chain except for
/// // the preexisting end link.
/// assert_eq!(a.insert_end(p_a, "D".to_owned()), Err("D".to_owned()));
/// let p_d = a.insert_end(p_b, "D".to_owned()).unwrap();
///
/// assert!(a.are_neighbors(p_b, p_d));
///
/// // Inserting a link into the middle
/// let p_c = a.insert((Some(p_b), Some(p_d)), "C".to_owned()).unwrap();
/// assert!(!a.are_neighbors(p_b, p_d));
/// assert!(a.are_neighbors(p_b, p_c));
/// assert!(a.are_neighbors(p_c, p_d));
///
/// // Insert a separate chain
/// let p_x = a.insert_new("X".to_owned());
/// let p_y = a.insert_end(p_x, "Y".to_owned()).unwrap();
/// let p_z = a.insert_end(p_y, "Z".to_owned()).unwrap();
///
/// // Connect the chains end-to-start in `O(1)`.
/// a.connect(p_d, p_x).unwrap();
///
/// // `iter_chain` will iterate over all links in the chain that the given
/// // `Ptr` is a part of. It will iterate across the chain in order (but
/// // check the documentation for how starting in the middle or in a cyclical
/// // chain works).
/// let expected = [
///     (p_a, "A"),
///     (p_b, "B"),
///     (p_c, "C"),
///     (p_d, "D"),
///     (p_x, "X"),
///     (p_y, "Y"),
///     (p_z, "Z"),
/// ];
/// for (i, (p_link, link)) in a.iter_chain(p_a).enumerate() {
///     assert_eq!(expected[i], (p_link, link.t.as_str()));
/// }
///
/// // Remove an element in the middle of a chain in `O(1)` with the same
/// // capabilities that the plain `Arena` has. Interlinks are fixed so
/// // that the link before the removed element is connected with the link
/// // after the element (chains are only broken in two with `break_*` or
/// // `exchange_next`).
/// assert_eq!(a.remove(p_d).unwrap().t, "D".to_owned());
/// assert!(a.are_neighbors(p_c, p_x));
///
/// // Remove a single connected chain efficiently
/// a.remove_chain(p_x).unwrap();
/// assert!(a.is_empty());
/// ```
pub struct ChainArena<P: Ptr, T> {
    pub(crate) a: Arena<P, Link<P, T>>,
}

/// # Note
///
/// `P` `Ptr`s to links in a `ChainArena` follow the same validity rules as
/// `Ptr`s in a regular `Arena` (see the documentation on the main
/// `impl<P: Ptr, T> Arena<P, T>`), except that `ChainArena`s automatically
/// update internal interlinks to maintain the linked-list nature of the chains.
/// The public interface has been designed such that it is not possible to break
/// the doubly linked invariant that each interlink `Ptr` from one link to its
/// neighbor has exactly one corresponding interlink `Ptr` pointing from the
/// neighbor back to itself. However, note that external copies of interlinks
/// may be indirectly invalidated by operations on a neighboring link.
impl<P: Ptr, T> ChainArena<P, T> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        // needs to be done because of upstream manual `InternalEntry` handling
        Arena::_check_invariants(&this.a)?;
        for (p, link) in &this.a {
            // note: we must check both cases of equality when checking for single link
            // cyclic chains, because we _must_ not rely on any kind of induction (any set
            // of interlinks could be bad or misplaced at the same time).
            if let Some(prev) = link.prev() {
                if let Some(prev) = this.a.get(prev) {
                    if let Some(next) = prev.next() {
                        if p != next {
                            return Err("interlink does not correspond")
                        }
                    } else {
                        return Err("next node does not exist")
                    }
                } else {
                    return Err("prev node does not exist")
                }
                if p == prev {
                    // should be a single link cyclic chain
                    if link.next() != Some(p) {
                        return Err("broken single link cyclic chain")
                    }
                }
            }
            // there are going to be duplicate checks but this must be done for invariant
            // breaking cases
            if let Some(next) = link.next() {
                if let Some(next) = this.a.get(next) {
                    if let Some(prev) = next.prev() {
                        if p != prev {
                            return Err("interlink does not correspond")
                        }
                    } else {
                        return Err("prev node does not exist")
                    }
                } else {
                    return Err("next node does not exist")
                }
                if p == next {
                    // should be a single link cyclic chain
                    if link.prev() != Some(p) {
                        return Err("broken single link cyclic chain")
                    }
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

    /// Returns the capacity of the arena
    pub fn capacity(&self) -> usize {
        self.a.capacity()
    }

    /// Follows [Arena::gen]
    pub fn gen(&self) -> P::Gen {
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
    /// unknown `Ptr`, inserting in the middle of the chain as usual. The
    /// `Ptr` to the new link is returned.
    ///
    /// # Errors
    ///
    /// If a `Ptr` is invalid, or `prev_next.0.is_some() &&
    /// prev_next.1.is_some() && !self.are_neighbors(prev, next)`, then
    /// ownership of `t` is returned.
    pub fn insert(&mut self, prev_next: (Option<P>, Option<P>), t: T) -> Result<P, T> {
        match prev_next {
            // new chain
            (None, None) => Ok(self.a.insert(Link::new((None, None), t))),
            (None, Some(p1)) => {
                // if there is a failure it cannot result in a node being inserted
                if let Some(link) = self.a.get(p1) {
                    if let Some(p0) = link.prev() {
                        // insert into middle of chain
                        let res = self.a.insert(Link::new((Some(p0), Some(p1)), t));
                        self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(res);
                        self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = Some(res);
                        Ok(res)
                    } else {
                        let res = self.a.insert(Link::new((None, Some(p1)), t));
                        self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = Some(res);
                        Ok(res)
                    }
                } else {
                    Err(t)
                }
            }
            (Some(p0), None) => {
                if let Some(link) = self.a.get(p0) {
                    if let Some(p1) = link.next() {
                        // insert into middle of chain
                        let res = self.a.insert(Link::new((Some(p0), Some(p1)), t));
                        self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(res);
                        self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = Some(res);
                        Ok(res)
                    } else {
                        let res = self.a.insert(Link::new((Some(p0), None), t));
                        self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(res);
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
                let res = self.a.insert(Link::new((Some(p0), Some(p1)), t));
                self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(res);
                self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = Some(res);
                Ok(res)
            }
        }
    }

    /// The same as [ChainArena::insert] except that the inserted `T` is created
    /// by `create`. The `Ptr` that will point to the new element is passed to
    /// `create`, and this `Ptr` is also returned. `create` is not called and
    /// `None` is returned if the `prev_next` setup would be invalid.
    pub fn insert_with<F: FnOnce(P) -> T>(
        &mut self,
        prev_next: (Option<P>, Option<P>),
        create: F,
    ) -> Option<P> {
        match prev_next {
            // new chain
            (None, None) => Some(self.a.insert_with(|p| Link::new((None, None), create(p)))),
            (None, Some(p1)) => {
                // if there is a failure it cannot result in a node being inserted
                if let Some(link) = self.a.get(p1) {
                    if let Some(p0) = link.prev() {
                        // insert into middle of chain
                        let res = self
                            .a
                            .insert_with(|p| Link::new((Some(p0), Some(p1)), create(p)));
                        self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(res);
                        self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = Some(res);
                        Some(res)
                    } else {
                        let res = self
                            .a
                            .insert_with(|p| Link::new((None, Some(p1)), create(p)));
                        self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = Some(res);
                        Some(res)
                    }
                } else {
                    None
                }
            }
            (Some(p0), None) => {
                if let Some(link) = self.a.get(p0) {
                    if let Some(p1) = link.next() {
                        // insert into middle of chain
                        let res = self
                            .a
                            .insert_with(|p| Link::new((Some(p0), Some(p1)), create(p)));
                        self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(res);
                        self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = Some(res);
                        Some(res)
                    } else {
                        let res = self
                            .a
                            .insert_with(|p| Link::new((Some(p0), None), create(p)));
                        self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(res);
                        Some(res)
                    }
                } else {
                    None
                }
            }
            (Some(p0), Some(p1)) => {
                // check for existence and that the nodes are neighbors
                if !self.are_neighbors(p0, p1) {
                    return None
                }
                let res = self
                    .a
                    .insert_with(|p| Link::new((Some(p0), Some(p1)), create(p)));
                self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(res);
                self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = Some(res);
                Some(res)
            }
        }
    }

    /// Inserts `t` as a single link in a new chain and returns a `Ptr` to it
    pub fn insert_new(&mut self, t: T) -> P {
        self.a.insert(Link::new((None, None), t))
    }

    /// Inserts the `T` returned by `create` as a new single link chain into the
    /// arena and returns a `Ptr` to it. `create` is given the the same
    /// `Ptr` that is returned, which is useful for initialization of
    /// immutable structures that need to reference themselves.
    pub fn insert_new_with<F: FnOnce(P) -> T>(&mut self, create: F) -> P {
        self.a.insert_with(|p| Link::new((None, None), create(p)))
    }

    /// Inserts `t` as a single link cyclical chain and returns a `Ptr` to it
    pub fn insert_new_cyclic(&mut self, t: T) -> P {
        self.a.insert_with(|p| Link::new((Some(p), Some(p)), t))
    }

    /// Like [ChainArena::insert_new_with] but with a single link cyclical
    /// chain.
    pub fn insert_new_cyclic_with<F: FnOnce(P) -> T>(&mut self, create: F) -> P {
        self.a
            .insert_with(|p| Link::new((Some(p), Some(p)), create(p)))
    }

    /// Inserts `t` as a new start link of a chain which has `p_start` as its
    /// preexisting first link. Returns ownership of `t` if `p_start` is not
    /// valid or is not the start of a chain
    pub fn insert_start(&mut self, p_start: P, t: T) -> Result<P, T> {
        if let Some(link) = self.a.get(p_start) {
            if link.prev().is_some() {
                // not at start of chain
                Err(t)
            } else {
                let res = self.a.insert(Link::new((None, Some(p_start)), t));
                self.a.get_inx_mut_unwrap(p_start.inx()).prev_next.0 = Some(res);
                Ok(res)
            }
        } else {
            Err(t)
        }
    }

    /// Inserts `t` as the new end link of a chain which has `p_end` as its
    /// preexisting end link. Returns ownership of `t` if `p_end` is not valid
    /// or is not the end of a chain
    pub fn insert_end(&mut self, p_end: P, t: T) -> Result<P, T> {
        if let Some(link) = self.a.get(p_end) {
            if link.next().is_some() {
                // not at end of chain
                Err(t)
            } else {
                let res = self.a.insert(Link::new((Some(p_end), None), t));
                self.a.get_inx_mut_unwrap(p_end.inx()).prev_next.1 = Some(res);
                Ok(res)
            }
        } else {
            Err(t)
        }
    }

    /// Returns if `p` is a valid `Ptr`
    pub fn contains(&self, p: P) -> bool {
        self.a.contains(p)
    }

    /// Returns if `p_prev` and `p_next` are neighbors on the same chain, such
    /// that `self.get_link(p_prev).unwrap().next() == Some(p_next)` or
    /// `self.get_link(p_next).unwrap().prev() == Some(p_prev)`. Note that
    /// `self.are_neighbors(p0, p1)` is not necessarily equal to
    /// `self.are_neighbors(p1, p0)` because of the directionality. This
    /// function returns true for the single link cyclic chain case with
    /// `p0 == p1`. Incurs only one internal lookup because of invariants.
    /// Additionally returns `false` if `p_prev` or `p_next` are invalid
    /// `Ptr`s.
    pub fn are_neighbors(&self, p_prev: P, p_next: P) -> bool {
        let mut are_neighbors = false;
        if let Some(l0) = self.a.get(p_prev) {
            if let Some(p) = l0.next() {
                if p.inx() == p_next.inx() {
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
    // NOTE: we will not be doing `&Link<P, T>` -> `Link<P, &T>` because we
    // want it all behind one pointer if possible
    pub fn get_link(&self, p: P) -> Option<&Link<P, T>> {
        self.a.get(p)
    }

    /// Returns a mutable reference to a link pointed to by `p`.
    /// Returns `None` if `p` is invalid.
    #[must_use]
    pub fn get_link_mut(&mut self, p: P) -> Option<Link<P, &mut T>> {
        self.a
            .get_mut(p)
            .map(|link| Link::new(link.prev_next, &mut link.t))
    }

    /// Gets two `Link<P, &mut T>` references pointed to by `p0` and `p1`.
    /// If `p0 == p1` or a pointer is invalid, `None` is returned.
    #[allow(clippy::type_complexity)]
    #[must_use]
    pub fn get2_link_mut(&mut self, p0: P, p1: P) -> Option<(Link<P, &mut T>, Link<P, &mut T>)> {
        self.a.get2_mut(p0, p1).map(|(link0, link1)| {
            (
                Link::new(link0.prev_next(), &mut link0.t),
                Link::new(link1.prev_next(), &mut link1.t),
            )
        })
    }

    /// Returns a `&T` reference pointed to by `p`. Returns
    /// `None` if `p` is invalid.
    #[must_use]
    pub fn get(&self, p: P) -> Option<&T> {
        self.a.get(p).map(|link| &link.t)
    }

    /// Returns a `&mut T` reference pointed to by `p`.
    /// Returns `None` if `p` is invalid.
    #[must_use]
    pub fn get_mut(&mut self, p: P) -> Option<&mut T> {
        self.a.get_mut(p).map(|link| &mut link.t)
    }

    /// Gets two `&mut T` references pointed to by `p0` and `p1`.
    /// If `p0 == p1` or a `Ptr` is invalid, `None` is returned.
    #[allow(clippy::type_complexity)]
    #[must_use]
    pub fn get2_mut(&mut self, p0: P, p1: P) -> Option<(&mut T, &mut T)> {
        self.a
            .get2_mut(p0, p1)
            .map(|(link0, link1)| (&mut link0.t, &mut link1.t))
    }

    /// Removes the link at `p`. If the link is in the middle of the chain, the
    /// neighbors of `p` are rerouted to be neighbors of each other so that the
    /// chain remains continuous. Returns `None` if `p` is not valid.
    #[must_use]
    pub fn remove(&mut self, p: P) -> Option<Link<P, T>> {
        let link = self.a.remove(p)?;
        match link.prev_next() {
            (None, None) => (),
            (None, Some(p1)) => {
                self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = None;
            }
            (Some(p0), None) => {
                self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = None;
            }
            (Some(p0), Some(p1)) => {
                if p.inx() != p0.inx() {
                    self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(p1);
                    self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = Some(p0);
                } // else it is a single link cyclic chain
            }
        }
        Some(link)
    }

    /// Efficiently removes the entire chain that `p` is connected to (which
    /// might only include itself). Returns the length of the chain. Returns
    /// `None` if `p` is not valid.
    pub fn remove_chain(&mut self, p: P) -> Option<usize> {
        let init = self.a.remove_internal(p, false)?;
        let mut len = 1;
        self.a.inc_gen();
        let mut tmp = init.next();
        while let Some(next) = tmp {
            if next.inx() == p.inx() {
                // cyclical
                return Some(len)
            }
            tmp = self.a.remove_internal_inx_unwrap(next.inx(), false).next();
            len = len.wrapping_add(1);
        }
        let mut tmp = init.prev();
        while let Some(prev) = tmp {
            tmp = self.a.remove_internal_inx_unwrap(prev.inx(), false).prev();
            len = len.wrapping_add(1);
        }
        Some(len)
    }

    /// Invalidates all references to the link pointed to by `p`, and returns a
    /// new valid reference. Any interlinks inside the arena that also pointed
    /// to `p` are updated to use the new valid reference. Remember that any
    /// external interlink pointers that used `p` are invalidated as well as the
    /// link itself. Does no invalidation and returns `None` if `p` is
    /// invalid.
    #[must_use]
    pub fn invalidate(&mut self, p: P) -> Option<P> {
        let p_new = self.a.invalidate(p)?;
        // fix invalidated interlinks
        match self.a.get_inx_unwrap(p_new.inx()).prev_next() {
            (None, None) => (),
            (None, Some(p1)) => {
                self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = Some(p_new);
            }
            (Some(p0), None) => {
                self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(p_new);
            }
            (Some(p0), Some(p1)) => {
                if p0.inx() == p.inx() {
                    // single link cyclical chain must be handled separately
                    self.a.get_inx_mut_unwrap(p_new.inx()).prev_next = (Some(p_new), Some(p_new));
                } else {
                    self.a.get_inx_mut_unwrap(p1.inx()).prev_next.0 = Some(p_new);
                    self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(p_new);
                }
            }
        }
        Some(p_new)
    }

    /// Replaces the `T` in the link pointed to by `p` with `new`, returns the
    /// old `T`, and keeps the internal generation counter as-is so that
    /// previously constructed `Ptr`s are still valid.
    ///
    /// # Errors
    ///
    /// Returns ownership of `new` instead if `p` is invalid
    pub fn replace_and_keep_gen(&mut self, p: P, new: T) -> Result<T, T> {
        if let Some(t) = self.get_mut(p) {
            let old = mem::replace(t, new);
            Ok(old)
        } else {
            Err(new)
        }
    }

    /// Replaces the `T` in the link pointed to by `p` with `new`, returns a
    /// tuple of the old `T` and new `P`, and updates the internal
    /// generation counter so that previous `Plink`s to this link are
    /// invalidated.
    ///
    /// # Errors
    ///
    /// Does no invalidation and returns ownership of `new` if `p` is invalid
    pub fn replace_and_update_gen(&mut self, p: P, new: T) -> Result<(T, P), T> {
        if let Some(p_new) = self.invalidate(p) {
            let old = mem::replace(self.get_mut(p_new).unwrap(), new);
            Ok((old, p_new))
        } else {
            Err(new)
        }
    }

    /// Swaps the `T` at indexes `p0` and `p1` and keeps the generation counters
    /// and link connections as-is. If `p0 == p1` then nothing occurs.
    /// Returns `None` if `p0` or `p1` are invalid.
    #[must_use]
    pub fn swap(&mut self, p0: P, p1: P) -> Option<()> {
        if p0.inx() == p1.inx() {
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

    /// Connects the interlinks of `p_prev` and `p_next` such that `p_prev` will
    /// be previous to `p_next`. Returns `None` if `p_prev` has a next
    /// interlink, `p_next` has a previous interlink, or the pointers are
    /// invalid.
    #[must_use]
    pub fn connect(&mut self, p_prev: P, p_next: P) -> Option<()> {
        if self.get_link(p_prev)?.next().is_none() && self.get_link(p_next)?.prev().is_none() {
            self.a.get_inx_mut_unwrap(p_prev.inx()).prev_next.1 = Some(p_next);
            self.a.get_inx_mut_unwrap(p_next.inx()).prev_next.0 = Some(p_prev);
            Some(())
        } else {
            None
        }
    }

    /// Breaks the previous interlink of `p`. Returns `None` if `p` is invalid
    /// or does not have a prev link.
    #[must_use]
    pub fn break_prev(&mut self, p: P) -> Option<()> {
        let u = self.get_link(p)?.prev()?;
        self.a.get_inx_mut_unwrap(p.inx()).prev_next.0 = None;
        self.a.get_inx_mut_unwrap(u.inx()).prev_next.1 = None;
        Some(())
    }

    /// Breaks the next interlink of `p`. Returns `None` if `p` is invalid or
    /// does not have a next link.
    #[must_use]
    pub fn break_next(&mut self, p: P) -> Option<()> {
        let d = self.get_link(p)?.next()?;
        self.a.get_inx_mut_unwrap(p.inx()).prev_next.1 = None;
        self.a.get_inx_mut_unwrap(d.inx()).prev_next.0 = None;
        Some(())
    }

    /// Exchanges the endpoints of the interlinks right after `p0` and `p1`.
    /// Returns `None` if the links do not have next interlinks or if the
    /// pointers are invalid.
    ///
    /// An interesting property of this function when applied to cyclic chains,
    /// is that `exchange_next` on two `Ptr`s of the same cyclic chain always
    /// results in two cyclic chains (except for if `p0 == p1`), and
    /// `exchange_next` on two `Ptr`s of two separate cyclic chains always
    /// results in a single cyclic chain.
    #[must_use]
    pub fn exchange_next(&mut self, p0: P, p1: P) -> Option<()> {
        if self.contains(p0) && self.contains(p1) {
            // get downstream links
            let d0 = self.a.get_inx_unwrap(p0.inx()).next()?;
            let d1 = self.a.get_inx_unwrap(p1.inx()).next()?;
            self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(d1);
            self.a.get_inx_mut_unwrap(p1.inx()).prev_next.1 = Some(d0);
            self.a.get_inx_mut_unwrap(d0.inx()).prev_next.0 = Some(p1);
            self.a.get_inx_mut_unwrap(d1.inx()).prev_next.0 = Some(p0);
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

    /// Performs a [ChainArena::clear] and resets capacity to 0
    pub fn clear_and_shrink(&mut self) {
        self.a.clear_and_shrink()
    }

    /// Compresses the arena by moving around entries to be able to shrink the
    /// capacity down to the length. All links and link prev-next relations
    /// remain, but all `Ptr`s and interlinks are invalidated. New `Ptr`s to
    /// the entries can be found again by iterators and advancers. Notably, when
    /// iterating or advancing after a call to this function or during `map`ping
    /// with [ChainArena::compress_and_shrink_with], whole chains at a time are
    /// advanced through without discontinuity (although there is not a
    /// specified ordering of links within the chain). Additionally, cache
    /// locality is improved by neighboring links being moved close together
    /// in memory.
    pub fn compress_and_shrink(&mut self) {
        self.compress_and_shrink_with(|_, _, _| ())
    }

    /// The same as [ChainArena::compress_and_shrink] except that `map` is run
    /// on every `(P, &mut T, P)` with the first `P` being the old `Ptr` and the
    /// last being the new `Ptr`.
    pub fn compress_and_shrink_with<F: FnMut(P, &mut T, P)>(&mut self, mut map: F) {
        // If we try using any linear loop method, we run into a problem where the
        // arbitrary prev or next node has an unknown back interlink. We use this method
        // because it has the added benefit of bringing in order links together in
        // memory.
        self.a.inc_gen();
        let gen = self.gen();
        let mut new = Arena::<P, Link<P, T>>::new();
        new.reserve(self.len());
        new.set_gen(gen);
        let mut adv = self.a.advancer();
        'outer: while let Some(p_init) = adv.advance(&self.a) {
            // an initial prelude is absolutely required to link up cyclic chains and handle
            // SLCCs
            let p = p_init;
            let link = self.a.remove(p_init).unwrap();
            let p_init = p_init.inx();
            let mut p_init_prev = None;
            let mut p_next = link.next().map(|p| p.inx());
            let q_init = if let Some(prev) = link.prev() {
                if prev.inx() == p_init {
                    // SLCC
                    let q = new.insert_with(|q| Link::new((Some(q), Some(q)), link.t));
                    map(p, &mut new.get_inx_mut_unwrap(q.inx()).t, q);
                    continue 'outer
                } else {
                    let q = new.insert(Link::new((None, None), link.t));
                    p_init_prev = Some(prev.inx());
                    q
                }
            } else {
                new.insert(Link::new((None, None), link.t))
            };
            map(p, &mut new.get_inx_mut_unwrap(q_init.inx()).t, q_init);
            let mut q_prev = q_init;
            loop {
                p_next = if let Some(p_next) = p_next {
                    let p_gen = self.a.get_no_gen(p_next).unwrap().0;
                    let p = Ptr::_from_raw(p_next, p_gen);
                    let link = self.a.remove(p).unwrap();
                    let tmp_next = link.next().map(|p| p.inx());
                    let t = link.t;
                    if Some(p_next) == p_init_prev {
                        // cyclic chain, connect in one step
                        let q = new.insert(Link::new((Some(q_prev), Some(q_init)), t));
                        map(p, &mut new.get_inx_mut_unwrap(q.inx()).t, q);
                        new.get_inx_mut_unwrap(q_prev.inx()).prev_next.1 = Some(q);
                        new.get_inx_mut_unwrap(q_init.inx()).prev_next.0 = Some(q);
                        continue 'outer
                    }
                    let q = new.insert(Link::new((Some(q_prev), None), t));
                    map(p, &mut new.get_inx_mut_unwrap(q.inx()).t, q);
                    new.get_inx_mut_unwrap(q_prev.inx()).prev_next.1 = Some(q);
                    q_prev = q;
                    tmp_next
                } else {
                    // reached end of chain, next loop will handle starting from `p_init_prev`
                    break
                };
            }
            let mut p_prev = p_init_prev;
            let mut q_next = q_init;
            loop {
                p_prev = if let Some(p_prev) = p_prev {
                    let p_gen = self.a.get_no_gen(p_prev).unwrap().0;
                    let p = Ptr::_from_raw(p_prev, p_gen);
                    let link = self.a.remove(p).unwrap();
                    let tmp_prev = link.prev().map(|p| p.inx());
                    let t = link.t;
                    let q = new.insert(Link::new((None, Some(q_next)), t));
                    map(p, &mut new.get_inx_mut_unwrap(q.inx()).t, q);
                    new.get_inx_mut_unwrap(q_next.inx()).prev_next.0 = Some(q);
                    q_next = q;
                    tmp_prev
                } else {
                    break
                };
            }
        }
        self.a = new;
    }

    /// Has the same properties of [Arena::clone_from_with], preserving
    /// interlinks as well.
    pub fn clone_from_with<U, F: FnMut(P, &Link<P, U>) -> T>(
        &mut self,
        source: &ChainArena<P, U>,
        mut map: F,
    ) {
        self.a.clone_from_with(&source.a, |p, link| {
            let t = map(p, link);
            Link::new(link.prev_next(), t)
        })
    }

    /// Overwrites `arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`, except that the interlink structure has been dropped.
    pub fn clone_to_arena<U, F: FnMut(P, &Link<P, T>) -> U>(
        &self,
        arena: &mut Arena<P, U>,
        map: F,
    ) {
        arena.clone_from_with(&self.a, map);
    }

    /// Like [ChainArena::get], except generation counters are ignored and the
    /// existing generation is returned.
    #[doc(hidden)]
    pub fn get_no_gen(&self, p: P::Inx) -> Option<(P::Gen, &Link<P, T>)> {
        self.a.get_no_gen(p)
    }

    /// Like [ChainArena::get_mut], except generation counters are ignored and
    /// the existing generation is returned.
    #[doc(hidden)]
    pub fn get_no_gen_mut(&mut self, p: P::Inx) -> Option<(P::Gen, Link<P, &mut T>)> {
        self.a
            .get_no_gen_mut(p)
            .map(|(gen, link)| (gen, Link::new(link.prev_next(), &mut link.t)))
    }

    /// Like [ChainArena::get], except generation counters are ignored and the
    /// result is unwrapped internally
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_unwrap(&self, p: P::Inx) -> &Link<P, T> {
        self.a.get_inx_unwrap(p)
    }

    // do not make a `get_inx_unwrap_t`, we do not want to incur extra offsets

    /// Like [ChainArena::get_mut], except generation counters are ignored and
    /// the result is unwrapped internally
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_mut_unwrap(&mut self, p: P::Inx) -> Link<P, &mut T> {
        let link = self.a.get_inx_mut_unwrap(p);
        Link::new(link.prev_next(), &mut link.t)
    }

    /// Like [ChainArena::get_mut], except generation counters are ignored and
    /// the result is unwrapped internally, and only the `&mut T` is
    /// returned
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_mut_unwrap_t(&mut self, p: P::Inx) -> &mut T {
        &mut self.a.get_inx_mut_unwrap(p).t
    }
}

impl<P: Ptr, T, B: Borrow<P>> Index<B> for ChainArena<P, T> {
    type Output = T;

    fn index(&self, index: B) -> &Self::Output {
        self.get(*index.borrow())
            .expect("indexed `ChainArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T, B: Borrow<P>> IndexMut<B> for ChainArena<P, T> {
    fn index_mut(&mut self, index: B) -> &mut Self::Output {
        self.a
            .get_mut(*index.borrow())
            .map(|link| &mut link.t)
            .expect("indexed `ChainArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T: Debug> Debug for Link<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "({:?}, {:?}) {:#?}", self.prev(), self.next(), self.t)
        } else {
            write!(f, "({:?}, {:?}) {:?}", self.prev(), self.next(), self.t)
        }
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
        if f.alternate() {
            write!(f, "({:?}, {:?}) {:#}", self.prev(), self.next(), self.t)
        } else {
            write!(f, "({:?}, {:?}) {}", self.prev(), self.next(), self.t)
        }
    }
}

impl<P: Ptr, T: Debug> Debug for ChainArena<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // needs to be done this way have the proper formatting
        if f.alternate() {
            write!(f, "{:#?}", self.a)
        } else {
            write!(f, "{:?}", self.a)
        }
    }
}

/// Implemented if `T: Clone`.
impl<P: Ptr, T: Clone> Clone for ChainArena<P, T> {
    /// Has the `Ptr` preserving properties of [Arena::clone]
    fn clone(&self) -> Self {
        Self { a: self.a.clone() }
    }

    /// Has the `Ptr` and capacity preserving properties of [Arena::clone_from]
    fn clone_from(&mut self, source: &Self) {
        self.a.clone_from(&source.a)
    }
}

impl<P: Ptr, T> Default for ChainArena<P, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Ptr, T: PartialEq> PartialEq<ChainArena<P, T>> for ChainArena<P, T> {
    /// Checks if all `(P, Link<P, T>)` pairs are equal. This is sensitive to
    /// `Ptr` indexes and generation counters, but does not compare arena
    /// capacities or `self.gen()`.
    fn eq(&self, other: &ChainArena<P, T>) -> bool {
        self.a == other.a
    }
}

impl<P: Ptr, T: Eq> Eq for ChainArena<P, T> {}
