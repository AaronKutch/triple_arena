use core::{
    borrow::Borrow,
    fmt,
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Index, IndexMut},
};

use crate::{
    Arena, ChainArena, InvalidationOption, Link,
    arena::InternalSlot,
    traits::{ArenaCloneFromWith, ArenaInsertEntryTrait, ArenaInsertTrait, ArenaTrait, Ptr},
    utils::traits::ArenaBacking,
};

/// The same as [crate::Link] except that the interlinks do not have a
/// generation counter
pub struct LinkNoGen<P: Ptr, T> {
    // I think the code generation should be overall better if this is done
    pub(crate) prev_next: (Option<P::Inx>, Option<P::Inx>),
    pub t: T,
}

impl<P: Ptr, T> LinkNoGen<P, T> {
    /// Get a `P::Inx` to the previous `LinkNoGen` in the chain before `self`.
    /// Returns `None` if `self` is at the start of the chain.
    pub fn prev(&self) -> Option<P::Inx> {
        self.prev_next.0
    }

    /// Get a `P::Inx` to the next `LinkNoGen` in the chain after `self`.
    /// Returns `None` if `self` is at the end of the chain.
    pub fn next(&self) -> Option<P::Inx> {
        self.prev_next.1
    }

    /// Shorthand for `(self.prev(), self.next())`
    pub fn prev_next(&self) -> (Option<P::Inx>, Option<P::Inx>) {
        self.prev_next
    }

    /// Construct a `LinkNoGen` from its components
    pub fn new(prev_next: (Option<P::Inx>, Option<P::Inx>), t: T) -> Self {
        Self { prev_next, t }
    }

    /// Construct a `LinkNoGen` from a regular `Link`
    pub fn from_link(link: Link<P, T>) -> Self {
        Self {
            prev_next: (
                link.prev_next.0.map(|p| p.inx()),
                link.prev_next.1.map(|p| p.inx()),
            ),
            t: link.t,
        }
    }
}

/// The same as [crate::ChainArena] except that the interlinks have no
/// generation counters.
///
/// The advantage of this is reduced memory footprint at the expense of
/// generation checks from the interlinks. This is mainly intended for internal
/// usage within data structures.
pub struct ChainNoGenArena<
    P: Ptr,
    T,
    #[cfg(feature = "alloc")] B: ArenaBacking = crate::HeapBacking,
    #[cfg(not(feature = "alloc"))] B: ArenaBacking,
> {
    pub(crate) a: Arena<P, LinkNoGen<P, T>, B>,
}

/// # Note
///
/// `P` `Ptr`s to links in a `ChainNoGenArena` follow the same validity rules as
/// `Ptr`s in a regular `Arena` (see the documentation on the main
/// `impl<P: Ptr, T> Arena<P, T>`), except that `ChainNoGenArena`s automatically
/// update internal interlinks to maintain the linked-list nature of the chains.
/// The public interface has been designed such that it is not possible to break
/// the doubly linked invariant that each interlink `Ptr` from one link to its
/// neighbor has exactly one corresponding interlink `Ptr` pointing from the
/// neighbor back to itself. However, note that external copies of interlinks
/// may be indirectly invalidated by operations on a neighboring link.
impl<P: Ptr, T, B: ArenaBacking> ChainNoGenArena<P, T, B> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        // needs to be done because of upstream manual `InternalEntry` handling
        Arena::_check_invariants(&this.a)?;
        Self::_check_interlinks(this)?;
        Ok(())
    }

    /// Checks that interlink transitivity holds
    #[doc(hidden)]
    pub fn _check_interlinks(this: &Self) -> Result<(), &'static str> {
        let err = Err("interlink transitivity does not hold");
        for (p, link) in &this.a {
            // note: we must check both cases of equality when checking for single link
            // cyclic chains, because we _must_ not rely on any kind of induction (any set
            // of interlinks could be bad or misplaced at the same time).
            if let Some(prev) = link.prev() {
                if let Some((_, prev)) = this.a.get_inx(prev) {
                    if let Some(next) = prev.next() {
                        if p.inx() != next {
                            return err;
                        }
                    } else {
                        return err;
                    }
                } else {
                    return err;
                }
                if p.inx() == prev {
                    // should be a single link cyclic chain
                    if link.next() != Some(p.inx()) {
                        return err;
                    }
                }
            }
            // there are going to be duplicate checks but this must be done for invariant
            // breaking cases
            if let Some(next) = link.next() {
                if let Some((_, next)) = this.a.get_inx(next) {
                    if let Some(prev) = next.prev() {
                        if p.inx() != prev {
                            return err;
                        }
                    } else {
                        return err;
                    }
                } else {
                    return err;
                }
                if p.inx() == next {
                    // should be a single link cyclic chain
                    if link.prev() != Some(p.inx()) {
                        return err;
                    }
                }
            }
        }
        Ok(())
    }

    /// Returns the singular arena generation counter, the same as
    /// [crate::traits::SingularGenerationArena::singular_generation]
    #[inline]
    pub fn generation(&self) -> P::Gen {
        self.a.generation()
    }

    /// Manually set the singular arena generation counter. This can break some
    /// soft invariants such as ABA problem prevention and `P::invalid`
    /// always being invalid with generation counters.
    pub fn set_generation(&mut self, new_gen: P::Gen) {
        self.a.set_generation(new_gen);
    }

    /// Increment the singular arena generation counter, returning if generation
    /// overflow occurred.
    pub fn inc_generation(&mut self) -> InvalidationOption<()> {
        self.a.inc_generation()
    }

    /// Calls [Arena::get_inx_unwrap]
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_unwrap(&self, p: P::Inx) -> &T {
        &self.a.get_inx_unwrap(p).t
    }

    /// Calls [Arena::get_inx_mut_unwrap]
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_mut_unwrap(&mut self, p: P::Inx) -> &mut T {
        &mut self.a.get_inx_mut_unwrap(p).t
    }

    /// Directly returns a reference to the internal backing, for the purposes
    /// of accessing `ArenaBacking`-specific functions
    pub fn backing(&self) -> &B::Stack<InternalSlot<P, LinkNoGen<P, T>>> {
        self.a.backing()
    }

    /// Directly returns a mutable reference to the internal backing, for the
    /// purposes of accessing `ArenaBacking`-specific functions
    ///
    /// # Safety
    ///
    /// The `InternalEntry` allocation state must not be modified, or else the
    /// freelist or entry length could be broken. The `LinkNoGen` interlinks
    /// must also not be modified, or else chain invariants could be broken.
    pub unsafe fn backing_mut(&mut self) -> &mut B::Stack<InternalSlot<P, LinkNoGen<P, T>>> {
        // Safety: called in `unsafe` function with same invariants and added invariants
        unsafe { self.a.backing_mut() }
    }

    /// Gets two `LinkNoGen<P, &mut T>` references pointed to by `p0` and `p1`.
    /// If `p0 == p1` or a pointer is invalid, `None` is returned.
    #[allow(clippy::type_complexity)]
    #[must_use]
    pub fn get2_link_mut(
        &mut self,
        p0: P,
        p1: P,
    ) -> Option<(LinkNoGen<P, &mut T>, LinkNoGen<P, &mut T>)> {
        self.a
            .get_disjoint_mut([p0, p1])
            .ok()
            .map(|[link0, link1]| {
                (
                    LinkNoGen::new(link0.prev_next(), &mut link0.t),
                    LinkNoGen::new(link1.prev_next(), &mut link1.t),
                )
            })
    }

    /// Gets two `&mut T` references pointed to by `p0` and `p1`.
    /// If `p0 == p1` or a `Ptr` is invalid, `None` is returned.
    #[allow(clippy::type_complexity)]
    #[must_use]
    pub fn get2_mut(&mut self, p0: P, p1: P) -> Option<(&mut T, &mut T)> {
        self.a
            .get_disjoint_mut([p0, p1])
            .ok()
            .map(|[link0, link1]| (&mut link0.t, &mut link1.t))
    }

    // this is tested by the `SurjectArena` fuzz test
    /// Like `remove_chain` but assumes the chain is cyclic and `p` is valid
    pub(crate) fn remove_cyclic_chain_internal(&mut self, p: P::Inx, inc_gen: bool) {
        let mut tmp = self
            .a
            .remove_internal(p, None, false)
            .allow()
            .unwrap()
            .1
            .next()
            .unwrap();
        while tmp != p {
            tmp = self
                .a
                .remove_internal(tmp, None, false)
                .allow()
                .unwrap()
                .1
                .next()
                .unwrap();
        }
        if inc_gen {
            self.a.inc_generation().allow();
        }
    }

    /// Efficiently removes the entire chain that `p` is connected to (which
    /// might only include itself). Returns the length of the chain. Returns
    /// `None` if `p` is not valid.
    pub fn remove_chain(&mut self, p: P) -> Option<usize> {
        let init = self
            .a
            .remove_internal(p.inx(), Some(p.generation()), false)
            .allow()?
            .1;
        let mut len = 1;
        self.a.inc_generation().allow();
        let mut tmp = init.next();
        while let Some(next) = tmp {
            if next == p.inx() {
                // cyclical
                return Some(len);
            }
            tmp = self
                .a
                .remove_internal(next, None, false)
                .allow()
                .unwrap()
                .1
                .next();
            len = len.wrapping_add(1);
        }
        let mut tmp = init.prev();
        while let Some(prev) = tmp {
            tmp = self
                .a
                .remove_internal(prev, None, false)
                .allow()
                .unwrap()
                .1
                .prev();
            len = len.wrapping_add(1);
        }
        Some(len)
    }

    /// A variation of `compress_and_shrink_with` that is intended for a single
    /// acyclic chain that has `first_link` as the first link in the chain.
    pub(crate) fn compress_and_shrink_acyclic_chain_with<F: FnMut(P, &mut T, P)>(
        &mut self,
        first_link: P,
        mut map: F,
    ) {
        self.a.inc_generation().allow();
        let generation = self.generation();
        let mut new = Arena::<P, LinkNoGen<P, T>, B>::with_min_capacity(self.len()).unwrap();
        new.set_generation(generation);
        let p_init = first_link;
        let mut link = self.a.remove(p_init).allow().unwrap();
        let mut p_next = link.next();
        let entry = new.entry_insert();
        let mut q_prev = entry.ptr();
        map(p_init, &mut link.t, q_prev);
        entry.insert(LinkNoGen::new((None, None), link.t));
        loop {
            p_next = if let Some(p_next) = p_next {
                let p_gen = self.a.get_inx(p_next).unwrap().0;
                let p = Ptr::_from_raw(p_next, p_gen);
                let link = self.a.remove(p).allow().unwrap();
                let tmp_next = link.next();
                let mut t = link.t;
                let entry = new.entry_insert();
                let q = entry.ptr();
                map(p, &mut t, q);
                entry.insert(LinkNoGen::new((Some(q_prev.inx()), None), t));
                new.get_inx_mut_unwrap(q_prev.inx()).prev_next.1 = Some(q.inx());
                q_prev = q;
                tmp_next
            } else {
                break;
            };
        }
        self.a = new;
    }

    /// Creates a `ChainNoGenArena<P, T>` directly from an
    /// `Arena<P, LinkNoGen<P, T>>`. Returns an error if interlink transitivity
    /// fails to hold.
    pub fn from_arena(arena: Arena<P, LinkNoGen<P, T>, B>) -> Result<Self, &'static str> {
        let res = Self { a: arena };
        Self::_check_interlinks(&res)?;
        Ok(res)
    }

    /// Has the same properties of [Arena::clone_from_with], preserving
    /// interlinks as well.
    pub fn clone_from_with<U, F: FnMut(P, &LinkNoGen<P, U>) -> T>(
        &mut self,
        source: &ChainNoGenArena<P, U, B>,
        mut map: F,
    ) {
        self.a
            .clone_from_with(&source.a, |p, link| {
                let t = map(p, link);
                LinkNoGen::new(link.prev_next(), t)
            })
            .unwrap()
    }

    /// Overwrites `arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`, except that the interlink structure has been dropped.
    pub fn clone_to_chain_arena<U, F: FnMut(P, &T) -> U>(
        &self,
        chain_arena: &mut ChainArena<P, U, B>,
        mut map: F,
    ) {
        chain_arena
            .a
            .clone_from_with(&self.a, |p, link| {
                let prev = if let Some(prev) = link.prev() {
                    let (generation, _) = self.a.get_inx(prev).unwrap();
                    Some(Ptr::_from_raw(prev, generation))
                } else {
                    None
                };
                let next = if let Some(next) = link.next() {
                    let (generation, _) = self.a.get_inx(next).unwrap();
                    Some(Ptr::_from_raw(next, generation))
                } else {
                    None
                };
                Link::new((prev, next), map(p, &link.t))
            })
            .unwrap();
    }

    /// Overwrites `arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`, except that the interlink structure has been dropped.
    pub fn clone_to_arena<U, F: FnMut(P, &LinkNoGen<P, T>) -> U>(
        &self,
        arena: &mut Arena<P, U, B>,
        map: F,
    ) {
        arena.clone_from_with(&self.a, map).unwrap();
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> Index<Q> for ChainNoGenArena<P, T, B> {
    type Output = T;

    fn index(&self, index: Q) -> &Self::Output {
        self.get(*index.borrow())
            .expect("indexed `ChainNoGenArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> IndexMut<Q> for ChainNoGenArena<P, T, B> {
    fn index_mut(&mut self, index: Q) -> &mut Self::Output {
        self.a
            .get_mut(*index.borrow())
            .map(|link| &mut link.t)
            .expect("indexed `ChainNoGenArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T: Debug> Debug for LinkNoGen<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "({:?}, {:?}) {:#?}", self.prev(), self.next(), self.t)
        } else {
            write!(f, "({:?}, {:?}) {:?}", self.prev(), self.next(), self.t)
        }
    }
}

impl<P: Ptr, T: Hash> Hash for LinkNoGen<P, T> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.prev_next.hash(state);
        self.t.hash(state);
    }
}

impl<P: Ptr, T: Clone> Clone for LinkNoGen<P, T> {
    fn clone(&self) -> Self {
        Self {
            prev_next: self.prev_next,
            t: self.t.clone(),
        }
    }
}

impl<P: Ptr, T: Copy> Copy for LinkNoGen<P, T> {}

impl<P: Ptr, T: PartialEq> PartialEq for LinkNoGen<P, T> {
    fn eq(&self, other: &Self) -> bool {
        (self.prev_next == other.prev_next) && (self.t == other.t)
    }
}

impl<P: Ptr, T: Eq> Eq for LinkNoGen<P, T> {}

impl<P: Ptr, T: PartialOrd> PartialOrd for LinkNoGen<P, T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        match self.prev_next.partial_cmp(&other.prev_next) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.t.partial_cmp(&other.t)
    }
}

impl<P: Ptr, T: Ord> Ord for LinkNoGen<P, T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<P: Ptr, T: Display> Display for LinkNoGen<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "({:?}, {:?}) {:#}", self.prev(), self.next(), self.t)
        } else {
            write!(f, "({:?}, {:?}) {}", self.prev(), self.next(), self.t)
        }
    }
}

impl<P: Ptr, T: Debug, B: ArenaBacking> Debug for ChainNoGenArena<P, T, B> {
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
impl<P: Ptr, T: Clone, B: ArenaBacking> Clone for ChainNoGenArena<P, T, B> {
    /// Has the `Ptr` preserving properties of [Arena::clone]
    fn clone(&self) -> Self {
        Self { a: self.a.clone() }
    }

    /// Has the `Ptr` and capacity preserving properties of [Arena::clone_from]
    fn clone_from(&mut self, source: &Self) {
        self.a.clone_from(&source.a)
    }
}

impl<P: Ptr, T, B: ArenaBacking> Default for ChainNoGenArena<P, T, B> {
    fn default() -> Self {
        Self::new()
    }
}
