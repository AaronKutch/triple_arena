use core::{
    borrow::Borrow,
    fmt::{self, Debug},
    num::NonZeroUsize,
    ops::{Index, IndexMut},
};

use crate::{
    Arena, InvalidationOption, LinkNoGen,
    errors::ReallocationError,
    traits::{
        Advancer, ArenaCloneFromWith, ArenaDirectInsertEntryTrait, ArenaDirectInsertTrait,
        ArenaInsertTrait, ArenaTrait, ChainArenaTrait, CompactArenaTrait, Ptr,
    },
    utils::{
        ArenaSlot, from_checked_raw,
        traits::{ArenaBacking, PtrInx},
    },
};

/// A doubly-linked-list based on an arena for handling usecases involving
/// `O(1)` insertion, deletion, and other functions on linear lists of elements
/// that we call "chains" of "links". Multiple separate chains and cyclical
/// chains are supported.
///
/// ```
/// use triple_arena::{
///     ChainArena, LinkInsertKind, errors::ChainInsertionError, ptr_struct, traits::*,
/// };
///
/// ptr_struct!(P0);
/// let mut a: ChainArena<P0, String> = ChainArena::new();
///
/// let p_a = a.insert(LinkInsertKind::Disconnected, "A".to_owned());
/// let p_b = a.insert(LinkInsertKind::Disconnected, "B".to_owned());
///
/// // initially, all entries from inserting with`LinkInsertKind::Disconnected`
/// // have `None` interlinks and are each in their own single link chains, and
/// // are completely unassociated like in a normal `Arena`.
///
/// // `*_no_gen` variants are preferred if only index interlinks are needed
/// let link = a.get_link_no_gen(p_a).unwrap();
/// assert_eq!(link.t, "A");
/// assert_eq!(link.prev(), None);
/// assert_eq!(link.next(), None);
///
/// let link = a.get_link_no_gen(p_b).unwrap();
/// assert_eq!(link.t, "B");
/// assert_eq!(link.prev(), None);
/// assert_eq!(link.next(), None);
///
/// assert!(!a.are_neighbors(p_a, p_b));
///
/// // Connect the two links by making the `next` interlink of A point to B,
/// // and the `prev` interlink of B point to A. Note that this is directional
/// // and that `a.connect(p_b, p_a).unwrap()` would result B being the start
/// // and A being the end of the chain instead.
/// a.connect(p_a, p_b).unwrap();
///
/// let link = a.get_link_no_gen(p_a).unwrap();
/// assert_eq!(link.t, "A");
/// assert_eq!(link.prev(), None);
/// assert_eq!(link.next(), Some(p_b.inx()));
///
/// let link = a.get_link_no_gen(p_b).unwrap();
/// assert_eq!(link.t, "B");
/// assert_eq!(link.prev(), Some(p_a.inx()));
/// assert_eq!(link.next(), None);
///
/// assert!(a.are_neighbors(p_a, p_b));
/// assert!(!a.are_neighbors(p_b, p_a));
///
/// // Now let us insert a third link and make it the end of the existing chain
/// // by using `LinkInsertKind::ChainEnd`.
///
/// // `LinkInsertKind::ChainEnd` guards against attaching to any part of a
/// // chain except for the preexisting end link.
/// assert_eq!(
///     a.insert_reallocating(LinkInsertKind::ChainEnd(p_a), "D".to_owned()),
///     Err(ChainInsertionError::FailedLinkRequirement)
/// );
/// let p_d = a.insert(LinkInsertKind::ChainEnd(p_b), "D".to_owned());
///
/// assert!(a.are_neighbors(p_b, p_d));
///
/// // Inserting a link into the middle
/// let p_c = a.insert(
///     LinkInsertKind::AtInterlink {
///         next_to: p_b,
///         prev_to: p_d,
///     },
///     "C".to_owned(),
/// );
/// assert!(!a.are_neighbors(p_b, p_d));
/// assert!(a.are_neighbors(p_b, p_c));
/// assert!(a.are_neighbors(p_c, p_d));
///
/// // Insert a separate chain
/// let p_x = a.insert(LinkInsertKind::Disconnected, "X".to_owned());
/// let p_y = a.insert(LinkInsertKind::ChainEnd(p_x), "Y".to_owned());
/// let p_z = a.insert(LinkInsertKind::ChainEnd(p_y), "Z".to_owned());
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
/// for (i, (p_link, link)) in a.iter_chain(p_a).unwrap().enumerate() {
///     assert_eq!(expected[i], (p_link, link.t.as_str()));
/// }
///
/// // Remove an element in the middle of a chain in `O(1)` with the same
/// // capabilities that the plain `Arena` has. Interlinks are fixed so
/// // that the link before the removed element is connected with the link
/// // after the element (chains are only broken in two with `break_*` or
/// // `exchange_next`).
/// assert_eq!(a.remove(p_d).allow().unwrap(), "D".to_owned());
/// assert!(a.are_neighbors(p_c, p_x));
///
/// // Remove a single connected chain efficiently
/// let _ = a.drain_chain(p_x).unwrap();
/// assert!(a.is_empty());
/// ```
pub struct ChainArena<
    P: Ptr,
    T,
    #[cfg(feature = "alloc")] B: ArenaBacking = crate::HeapBacking,
    #[cfg(not(feature = "alloc"))] B: ArenaBacking,
> {
    pub(crate) a: Arena<P, LinkNoGen<P, T>, B>,
}

impl<P: Ptr, T, B: ArenaBacking> ChainArena<P, T, B> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        // needs to be done because of upstream manual `ArenaSlot` handling
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
    /// [crate::traits::ArenaTrait::singular_generation]
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

    pub fn transfer_canonical_reallocating<
        Q: Ptr,
        U,
        A: ChainArenaTrait<Q, U> + CompactArenaTrait<Q, U>,
        F: FnMut(Q, InvalidationOption<U>, P) -> T,
        D: ArenaDirectInsertTrait<Q, P>,
    >(
        &mut self,
        new_generation: P::Gen,
        source: &mut A,
        mut map: F,
        recaster: &mut D,
    ) -> Result<(), ReallocationError> {
        let Some(len) = NonZeroUsize::new(source.len()) else {
            // follow what the other path would logically do
            recaster.clear().allow();
            self.clear().allow();
            self.set_generation(new_generation);
            return Ok(());
        };
        // REF(careful_index_checking)
        if P::Inx::try_from_usize(len).is_none() {
            return Err(ReallocationError::AllocError);
        };
        if len.get() > self.capacity() {
            // max capacity is tested here
            self.reallocate_min_capacity(len.get())?;
        }

        // REF(careful_index_checking)
        let q_last = source.find_last_inx_ptr().unwrap();
        let Some(raw_last) = Q::Inx::try_into_usize(q_last.inx()) else {
            return Err(ReallocationError::AllocError);
        };
        if raw_last.get() > recaster.capacity() {
            // max capacity is tested here
            recaster.reallocate_min_capacity(raw_last.get())?;
        }

        // the rest should be infallible if soft invariants are followed
        recaster.clear().allow();
        self.clear().allow();
        self.set_generation(new_generation);

        let mut p_raw = NonZeroUsize::new(1).unwrap();
        let mut adv_outer = source.advancer();
        while let Some(q_start) = adv_outer.advance(source) {
            if recaster.contains(q_start) {
                // part of a chain that has already been mapped, critical to prevent `O(n^2)`
                // because in the acyclic case `advancer_chain` will find the beginning of the
                // chain
                continue;
            }
            let mut adv_chain = source.advancer_chain(q_start).unwrap();
            while let Some(q) = adv_chain.advance(source) {
                // cannot panic for `Ptr`s following soft invariants since we checked the
                // highest index
                let p_inx = from_checked_raw::<P>(p_raw);
                let p = P::_from_raw(p_inx, new_generation);
                match recaster.direct_insert_within_capacity(q) {
                    Ok(entry) => {
                        entry.insert(p);
                    }
                    _ => unreachable!(),
                }

                // increment here as we find the pointers in the order that they will actually
                // be drained, the repeat of the outer advancer and chain_drain will encounter
                // in the same order
                p_raw = p_raw.checked_add(1).unwrap();
            }
        }

        let mut adv_outer = source.advancer();
        while let Some(q_start) = adv_outer.advance(source) {
            for o in source.drain_chain(q_start).unwrap() {
                let ((q, q_link), o) = o.overflowing();
                let p = *recaster.get(q).unwrap();
                let prev_next = (
                    q_link
                        .prev()
                        .map(|q_inx| recaster.get_inx(q_inx).unwrap().1.inx()),
                    q_link
                        .next()
                        .map(|q_inx| recaster.get_inx(q_inx).unwrap().1.inx()),
                );
                let arg = if o {
                    InvalidationOption::GenerationOverflow(q_link.t)
                } else {
                    InvalidationOption::Success(q_link.t)
                };
                let t = map(q, arg, p);
                let p_link = LinkNoGen::<P, T>::new(prev_next, t);

                // relying on standard behavior with slots and generation
                if self.a.insert_within_capacity(p_link).is_err() {
                    unreachable!()
                }
            }
        }
        Ok(())
    }

    /// Creates a `ChainArena<P, T>` directly from an
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
        source: &ChainArena<P, U, B>,
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
    pub fn clone_to_arena<U, F: FnMut(P, &LinkNoGen<P, T>) -> U>(
        &self,
        arena: &mut Arena<P, U, B>,
        map: F,
    ) {
        arena.clone_from_with(&self.a, map).unwrap();
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
    pub fn backing(&self) -> &B::Stack<ArenaSlot<P, LinkNoGen<P, T>>> {
        self.a.backing()
    }

    /// Directly returns a mutable reference to the internal backing, for the
    /// purposes of accessing `ArenaBacking`-specific functions
    ///
    /// # Safety
    ///
    /// The `ArenaSlot` allocation state must not be modified, or else the
    /// freelist or entry length could be broken. The `LinkNoGen` interlinks
    /// must also not be modified, or else chain invariants could be broken.
    pub unsafe fn backing_mut(&mut self) -> &mut B::Stack<ArenaSlot<P, LinkNoGen<P, T>>> {
        // Safety: called in `unsafe` function with same invariants and added invariants
        unsafe { self.a.backing_mut() }
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> Index<Q> for ChainArena<P, T, B> {
    type Output = T;

    fn index(&self, index: Q) -> &Self::Output {
        self.get(*index.borrow())
            .expect("indexed `ChainArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> IndexMut<Q> for ChainArena<P, T, B> {
    fn index_mut(&mut self, index: Q) -> &mut Self::Output {
        self.a
            .get_mut(*index.borrow())
            .map(|link| &mut link.t)
            .expect("indexed `ChainArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T: Debug, B: ArenaBacking> Debug for ChainArena<P, T, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // grouping by chain is not efficiently possible without extra state
        // unfortunately
        f.debug_map().entries(self.iter_link_no_gen()).finish()
    }
}

/// Implemented if `T: Clone`.
impl<P: Ptr, T: Clone, B: ArenaBacking> Clone for ChainArena<P, T, B> {
    /// Has the `Ptr` preserving properties of [Arena::clone]
    fn clone(&self) -> Self {
        Self { a: self.a.clone() }
    }

    /// Has the `Ptr` and capacity preserving properties of [Arena::clone_from]
    fn clone_from(&mut self, source: &Self) {
        self.a.clone_from(&source.a)
    }
}

impl<P: Ptr, T, B: ArenaBacking> Default for ChainArena<P, T, B> {
    fn default() -> Self {
        Self::new()
    }
}
