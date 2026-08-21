use core::{
    borrow::Borrow,
    fmt::{self, Debug},
    num::NonZeroUsize,
    ops::{Index, IndexMut},
};

use crate::{
    Arena, InvalidationOption, LinkNoGen,
    errors::{MaxCapacityReductionError, ReallocationError},
    traits::{
        Advancer, ArenaCloneFromWith, ArenaInsertEntryTrait, ArenaInsertTrait, ArenaTrait,
        ChainArenaTrait, CompactArenaTrait, Ptr, SetMaxCapacity,
    },
    utils::{
        ArenaSlot,
        traits::{ArenaBacking, PtrInx},
    },
};

// note: SLCC = Single Link Cyclic Chain

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
/// // initially, all entries from inserting with `LinkInsertKind::Disconnected`
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
/// let expected = [
///     (p_a, "A"),
///     (p_b, "B"),
///     (p_c, "C"),
///     (p_x, "X"),
///     (p_y, "Y"),
///     (p_z, "Z"),
/// ];
/// for (i, (p_link, link)) in a.iter_chain(p_a).unwrap().enumerate() {
///     assert_eq!(expected[i], (p_link, link.t.as_str()));
/// }
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

/// Walks backwards to find the start of the chain that `p` is part of, and
/// whether the chain is cyclic. Cyclic chains have no start, in which case `p`
/// itself is returned.
fn find_chain_start<P: Ptr, U, A: ChainArenaTrait<P, U>>(source: &A, p: P) -> (P, bool) {
    let mut target_inx = p.inx();
    loop {
        let (generation, link) = source.get_inx_link_no_gen(target_inx).unwrap();
        let target = P::_from_raw(target_inx, generation);
        let Some(prev) = link.prev() else {
            return (target, false);
        };
        if prev == p.inx() {
            return (p, true);
        }
        target_inx = prev;
    }
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
            // Note: both directions have to be checked on every link even though that
            // duplicates work, because we _must_ not rely on any kind of induction (any
            // set of interlinks could be bad or misplaced at the same time).
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
            }
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
    /// Like `drain_chain` but assumes the chain is cyclic and `p` is valid.
    pub(crate) fn remove_cyclic_chain_internal(&mut self, p: P::Inx) {
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
    }

    /// The chain arena counterpart of
    /// [transfer_reallocating](Arena::transfer_reallocating), transferring
    /// every entry out of `source` and into `self`, but also in a
    /// canonicalizing way. Given any `source` implementing both
    /// [ChainArenaTrait] and [CompactArenaTrait] with any `Q: Ptr` and `U`
    /// entry type, this transfers all of the links by reallocating `self`
    /// if necessary, clearing `self`, and removing every link from `source`
    /// and inserting a mapped `T` into `self`, preserving the interlink
    /// structure. Every link is given by value to `map` with the
    /// original source `Q: Ptr`, an [InvalidationOption]`<U>` for being able to
    /// determine if the removal caused a generation overflow in `source`, the
    /// destination `P: Ptr`, and then `map` must return the `T` that will be
    /// inserted into `self`. The new links are all given `new_generation`.
    ///
    /// The normal [transfer_reallocating](Arena::transfer_reallocating) keeps
    /// the entries in the same order of increasing index before and after the
    /// transfer, but this function will reorder entries to bring links of
    /// the same chain together. The links are canonically laid out in
    /// `self`, such that their `P::Inx`s are `1..=source.len()` and each
    /// chain occupies one contiguous run of indexes in
    /// [Link::next](crate::Link::next) order. Acyclic chains begin at their
    /// start link, while cyclic chains begin at the link that the
    /// source advancer reaches first.
    ///
    /// Reallocation only occurs if `source.len() > self.capacity()`. All of
    /// the fallible points happen before anything is modified, such that
    /// `self` and `source` are logically unchanged if an error is
    /// returned. An error is returned if a reallocation fails, if a
    /// [max_capacity](ArenaTrait::max_capacity) limit prevents a reallocation,
    /// or if `source.len()` or the largest index in `source` is more than what
    /// `P::Inx` can represent.
    ///
    /// This is the chain arena counterpart of the recaster example on
    /// [compress_with](ArenaTrait::compress_with). Links have to travel between
    /// two domains in order to be laid out in chain order, so instead of
    /// compressing in place we transfer into a fresh arena and replace the old
    /// one through the `&mut`:
    /// ```
    /// use triple_arena::{
    ///     ChainArena, DirectArena, HeapBacking, LinkInsertKind, ptr_struct,
    ///     traits::*,
    ///     utils::traits::{PtrGen, PtrInx},
    /// };
    ///
    /// // (This would be a standard function, except there are far too many choices to
    /// // make on the backing of the recaster arena and how fallibility should be
    /// // handled)
    /// fn compress_canonical_recaster<P: Ptr, T>(
    ///     this: &mut ChainArena<P, T, HeapBacking>,
    ///     reset_generation: bool,
    /// ) -> DirectArena<P, P, HeapBacking> {
    ///     let new_generation = if reset_generation {
    ///         // reset for compactness, only safe if logically old domain `Ptr`s can be
    ///         // eliminated
    ///         P::Gen::two()
    ///     } else {
    ///         // use incremented generation so that all `Ptr`s of the old domain are
    ///         // invalidated
    ///         P::Gen::generational_inc(this.generation()).0
    ///     };
    ///     // This arena will be a recaster in which we create a mapping from the old `Ptr`
    ///     // domain to the new one. We use a `DirectArena` for this since it will only
    ///     // be used for this purpose and then discarded.
    ///     let mut recaster = DirectArena::<P, P, HeapBacking>::new();
    ///     // This all the keys of the mapping, by cloning the `Ptr` validities of the
    ///     // pre-transfer `this` into the recaster, and puts in invalid placeholders
    ///     // for the new domain because we do not know them yet.
    ///     recaster.clone_from_with(this, |_, _| P::invalid()).unwrap();
    ///     let mut replacement = ChainArena::<P, T, HeapBacking>::new();
    ///     // Transfer and write the new `Ptr`s at the indexes of the corresponding old
    ///     // `Ptr`s, using the values seen by the closure to complete the mapping of
    ///     // the old domain to the new domain.
    ///     replacement
    ///         .transfer_canonical_reallocating(new_generation, this, |q, o, p| {
    ///             recaster[q] = p;
    ///             o.allow()
    ///         })
    ///         .unwrap();
    ///     *this = replacement;
    ///     recaster
    /// }
    ///
    /// ptr_struct!(P0);
    ///
    /// let mut a: ChainArena<P0, &str> = ChainArena::new();
    /// let p_x = a.insert(LinkInsertKind::Disconnected, "X");
    /// let p_a = a.insert(LinkInsertKind::Disconnected, "A");
    /// a.insert(LinkInsertKind::ChainEnd(p_x), "Y");
    /// let p_b = a.insert(LinkInsertKind::ChainEnd(p_a), "B");
    /// // make an internal slot unallocated, and scatter the chains further
    /// a.remove(p_x).allow().unwrap();
    /// a.insert(LinkInsertKind::ChainEnd(p_b), "C");
    ///
    /// // the "A" -> "B" -> "C" chain is spread over the indexes 2, 4, 1
    /// assert_eq!(
    ///     &format!("{a:#?}"),
    ///     r#"{
    ///     P0[1](3): {4, (end)} "C",
    ///     P0[2](2): {(start), 4} "A",
    ///     P0[3](2): {(start), (end)} "Y",
    ///     P0[4](2): {2, 1} "B",
    /// }"#
    /// );
    ///
    /// let recaster = compress_canonical_recaster(&mut a, false);
    ///
    /// // now each chain is one contiguous run of indexes in `Link::next` order
    /// let layout: Vec<(usize, &str)> = a
    ///     .iter()
    ///     .map(|(p, t)| (PtrInx::try_into_usize(p.inx()).unwrap().get(), *t))
    ///     .collect();
    /// assert_eq!(layout, vec![(1, "A"), (2, "B"), (3, "C"), (4, "Y")]);
    /// // and the recaster is a complete description of where the links went
    /// println!("{recaster:#?}");
    /// assert_eq!(
    ///     &format!("{recaster:#?}"),
    ///     r#"{
    ///     P0[1](3): P0[3](4),
    ///     P0[2](2): P0[1](4),
    ///     P0[3](2): P0[4](4),
    ///     P0[4](2): P0[2](4),
    /// }"#
    /// );
    ///
    /// // external `Ptr`s are fixed up with it
    /// let mut external = p_a;
    /// external.recast(&recaster).unwrap();
    /// assert_eq!(a[external], "A");
    /// ```
    ///
    /// # Unwind Safety
    ///
    /// If `map` panics, the link it was called with is lost to whatever `map`
    /// does, the rest of the chain that was being drained is dropped, and
    /// `source` and `self` are left with the chains that have yet to be
    /// transferred and the links that were already transferred respectively.
    pub fn transfer_canonical_reallocating<
        Q: Ptr,
        U,
        A: ChainArenaTrait<Q, U> + CompactArenaTrait<Q, U>,
        F: FnMut(Q, InvalidationOption<U>, P) -> T,
    >(
        &mut self,
        new_generation: P::Gen,
        source: &mut A,
        mut map: F,
    ) -> Result<(), ReallocationError> {
        let Some(len) = NonZeroUsize::new(source.len()) else {
            // follow what the other path would logically do
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

        // the rest should be infallible if soft invariants are followed
        self.clear().allow();
        self.set_generation(new_generation);

        // using a normal advancer and inner canonically ordered drain_chain loop
        // automatically gives us what we want
        let mut adv_outer = source.advancer();
        while let Some(q_start) = adv_outer.advance(source) {
            let (start, cyclic) = find_chain_start(source, q_start);
            // key links of this chain that have been inserted into `self` so far
            let mut chain_first: Option<P::Inx> = None;
            let mut chain_prev: Option<P::Inx> = None;
            for o in source.drain_chain(start).unwrap() {
                let ((q, q_link), o) = o.overflowing();
                let Ok(entry) = self.a.entry_insert_within_capacity() else {
                    unreachable!()
                };
                let p = entry.ptr();
                let arg = if o {
                    InvalidationOption::GenerationOverflow(q_link.t)
                } else {
                    InvalidationOption::Success(q_link.t)
                };
                let t = map(q, arg, p);
                // keep chain invariants at every `map` call
                entry.insert(LinkNoGen::new((chain_prev, None), t));
                if let Some(prev) = chain_prev {
                    self.a.get_inx_mut_unwrap(prev).prev_next.1 = Some(p.inx());
                }
                if chain_first.is_none() {
                    chain_first = Some(p.inx());
                }
                chain_prev = Some(p.inx());
            }
            if cyclic
                && let Some(first) = chain_first
                && let Some(last) = chain_prev
            {
                // close the loop, also handles SLCCs
                self.a.get_inx_mut_unwrap(last).prev_next.1 = Some(first);
                self.a.get_inx_mut_unwrap(first).prev_next.0 = Some(last);
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

    /// Has the same properties as
    /// [clone_from_with](ArenaCloneFromWith::clone_from_with), preserving
    /// interlinks as well.
    ///
    /// # Unwind Safety
    ///
    /// If `map` panics, it can break the interlink invariants (which can cause
    /// panics with some functions) and `self` must be cleared.
    pub fn clone_from_with<B1: ArenaBacking, U, F: FnMut(P, &LinkNoGen<P, U>) -> T>(
        &mut self,
        source: &ChainArena<P, U, B1>,
        mut map: F,
    ) -> Result<(), ReallocationError> {
        self.a.clone_from_with(&source.a, |p, link| {
            let t = map(p, link);
            LinkNoGen::new(link.prev_next(), t)
        })
    }

    /// Calls [clone_from_with](ArenaCloneFromWith::clone_from_with) on `arena`,
    /// giving all the [LinkNoGen]s of `self` to the `Ptr` preserving mapping.
    pub fn clone_to_arena<U, A: ArenaCloneFromWith<P, U>, F: FnMut(P, &LinkNoGen<P, T>) -> U>(
        &self,
        arena: &mut A,
        map: F,
    ) -> Result<(), ReallocationError> {
        arena.clone_from_with(&self.a, map)
    }

    /// Calls [Arena::get_inx_unwrap]
    ///
    /// # Panics
    ///
    /// If `p` does not point to an allocated entry
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_unwrap(&self, p: P::Inx) -> &T {
        &self.a.get_inx_unwrap(p).t
    }

    /// Calls [Arena::get_inx_mut_unwrap]
    ///
    /// # Panics
    ///
    /// If `p` does not point to an allocated entry
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

    /// Returns a reference to the `T` pointed to by `inx`. Use
    /// [get](ArenaTrait::get) if invalid `Ptr`s need to be handled, or
    /// [get_link_no_gen](ChainArenaTrait::get_link_no_gen) if the interlinks
    /// are also needed.
    ///
    /// # Panics
    ///
    /// If `inx` is invalid
    #[track_caller]
    fn index(&self, inx: Q) -> &T {
        let p: P = *inx.borrow();
        self.get(p)
            .expect("indexed `ChainArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> IndexMut<Q> for ChainArena<P, T, B> {
    /// Returns a mutable reference to the `T` pointed to by `inx`. Use
    /// [get_mut](ArenaTrait::get_mut) if invalid `Ptr`s need to be handled.
    ///
    /// # Panics
    ///
    /// If `inx` is invalid
    #[track_caller]
    fn index_mut(&mut self, inx: Q) -> &mut T {
        let p: P = *inx.borrow();
        self.a
            .get_mut(p)
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
    /// Has the `Ptr` preserving properties of [Arena::clone], and the
    /// interlinks are preserved as well.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure, or if a
    /// [max_capacity](ArenaTrait::max_capacity) limit of the fresh `Self::new`
    /// arena prevents reaching the needed capacity. Use
    /// [clone_from_with](ChainArena::clone_from_with) if these need to be
    /// handled.
    ///
    /// # Unwind Safety
    ///
    /// If a `T::clone` panics, the partially cloned arena is dropped.
    #[track_caller]
    fn clone(&self) -> Self {
        Self { a: self.a.clone() }
    }

    /// Has the `Ptr` and capacity preserving properties of [Arena::clone_from],
    /// and the interlinks are preserved as well.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure, or if a
    /// [max_capacity](ArenaTrait::max_capacity) limit of `self` prevents
    /// reaching the needed capacity. Use
    /// [clone_from_with](ChainArena::clone_from_with) if these need to be
    /// handled.
    ///
    /// # Unwind Safety
    ///
    /// A panicking `T::clone` or `T::drop` leaves `self` with the same
    /// guarantees as [clone_from_with](ChainArena::clone_from_with).
    #[track_caller]
    fn clone_from(&mut self, source: &Self) {
        self.a.clone_from(&source.a)
    }
}

impl<P: Ptr, T, B: ArenaBacking> Default for ChainArena<P, T, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Ptr, T, B: ArenaBacking> SetMaxCapacity for ChainArena<P, T, B>
where
    <B as ArenaBacking>::Stack<ArenaSlot<P, LinkNoGen<P, T>>>: SetMaxCapacity,
{
    fn set_max_capacity(&mut self, max_capacity: usize) -> Result<(), MaxCapacityReductionError> {
        self.a.set_max_capacity(max_capacity)
    }
}
