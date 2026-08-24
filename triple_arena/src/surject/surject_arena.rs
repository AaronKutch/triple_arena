use core::{
    borrow::Borrow,
    fmt, mem,
    num::NonZeroUsize,
    ops::{Index, IndexMut},
    slice::GetDisjointMutError,
};

use fmt::Debug;

use crate::{
    Arena, ChainArena, InvalidationOption, InvalidationResult, LinkInsertKind, LinkNoGen,
    arena::{ArenaSlot, from_checked_ptr, from_checked_raw},
    errors::{
        AllocError, ChainInsertionError, MaxCapacityReductionError, NotWithinCapacityError,
        ReallocationError,
    },
    traits::{
        Advancer, ArenaCloneFromWith, ArenaInsertEntryTrait, ArenaInsertTrait, ArenaTrait,
        ChainArenaTrait, DisjointableArenaTrait, Ptr, SetMaxCapacity,
    },
    utils::{
        PtrNoGen, nzusize_iter,
        traits::{ArenaBacking, NonZeroInxGenericStack, PtrInx},
    },
};

/// Internal surject element for [SurjectArena]
#[derive(Clone)]
pub struct SurjectElement<P: Ptr, T> {
    pub t: T,
    /// we want to have the size of `P::Inx` since we do not need the generation
    /// counter on the internal indirection
    pub p_shared: PtrNoGen<P>,
}

/// Internal shared value for [SurjectArena]
#[derive(Clone)]
pub struct SurjectShared<S> {
    pub s: S,
    /// we ultimately need a reference count for efficient unions, and it
    /// has the bonus of being able to easily query element chain lengths
    pub element_count: NonZeroUsize,
}

/// A generalization of an `Arena` with three parameters: a `P: Ptr` type, a `T`
/// element type, and an `S` shared type. Each `P` points to a single `T` like
/// in a normal arena, but multiple `(P, T)` entries can point to a single
/// shared `S` in a surjective map structure. When all `Ptr`s to a single `S`
/// are removed, the `S` is removed as well. Efficient union-find functionality
/// is also possible.
///
/// This is a more powerful version of union-find data structures, incorporating
/// types on both sides of the surjection, individual entry `Ptr` validity
/// tracking, `O(1)` single and double element operations, and allowing
/// generation counted removal. Under the hood, this uses a `O(n log n)`
/// strategy for union-find, but for many usecases this should actually be
/// faster than the theoretical `O(n iterated log n)`, because there is always
/// only a single layer of indirections at any one time for caches to deal with
/// (we use a clever `ChainArena` based strategy that avoids any tree structures
/// or element reinsertion).
///
/// `SurjectArena<P, (), S>` is more like a classic union-find structure, and
/// `SurjectArena<P, T, ()>` is a kind of non-hereditary set. Even
/// `SurjectArena<P, (), ()>` can be useful (assuming `P` has generation
/// counters) for its `O(1)` validity tracking capabilities under any order
/// of adding and removing of pointers. This is more powerful than pure
/// reference counting or epoch-like structures.
///
/// ```
/// use triple_arena::{SurjectArena, errors::ChainInsertionError, ptr_struct, traits::ArenaTrait};
///
/// ptr_struct!(P0);
/// let mut a: SurjectArena<P0, String, String> = SurjectArena::new();
///
/// // There must be at least one element associated with each shared value, so
/// // the first insertion must always be a surject insertion
/// let p0_42 = a.insert_surject("e0".to_owned(), "42".to_owned());
/// // If we want new elements to be associated with the same surject that
/// // shares "42", then instead of calling `insert_surject` we call `insert` to
/// // insert elements into an existing surject
/// let p1_42 = a.insert(p0_42, "e1".to_owned());
/// // We could use either `p0_42` or `p1_42` as our reference to get associated
/// // with the same surject; any valid pointer in the preexisting surject can
/// // be used with the same `O(1)` computational complexity incurred.
/// let p2_42 = a.insert(p0_42, "e2".to_owned());
///
/// assert_eq!(a.get(p0_42).unwrap(), "e0");
/// assert_eq!(a.get(p1_42).unwrap(), "e1");
/// assert_eq!(a.get(p2_42).unwrap(), "e2");
/// assert_eq!(a.get_shared(p0_42).unwrap(), "42");
/// assert_eq!(a.get_shared(p1_42).unwrap(), "42");
/// assert_eq!(a.get_shared(p2_42).unwrap(), "42");
///
/// assert_eq!(
///     a.remove_element(p1_42).allow(),
///     Some(("e1".to_owned(), None))
/// );
/// assert!(a.contains(p0_42));
/// assert!(!a.contains(p1_42));
/// assert!(a.contains(p2_42));
/// // the shared value is perpetuated as long as the surject still has at least
/// // one element
/// assert_eq!(a.get_shared(p2_42).unwrap(), "42");
///
/// // We cannot use an invalidated pointer as a reference
/// assert_eq!(
///     a.insert_reallocating(p1_42, "e3".to_owned()),
///     Err(ChainInsertionError::FailedLinkRequirement)
/// );
/// // We need to use an existing valid element
/// let p3_42 = a.insert(p2_42, "e3".to_owned());
/// assert_eq!(a.get_shared(p3_42).unwrap(), "42");
///
/// let other42 = a.insert_surject("test".to_owned(), "42".to_owned());
/// // note this is still a general `Arena`-like structure and not a hereditary
/// // set or map, so multiple of the same exact shared values can exist in
/// // different surjects.
/// assert!(!a.in_same_surject(p0_42, other42).unwrap());
/// // removes the entire surject
/// a.remove_shared(other42).unwrap().allow();
///
/// let p4_7 = a.insert_surject("e4".to_owned(), "7".to_owned());
/// let p5_7 = a.insert(p4_7, "e5".to_owned());
///
/// assert_eq!(a.len_surject(p0_42).unwrap().get(), 3);
/// assert_eq!(a.len_surject(p4_7).unwrap().get(), 2);
///
/// // The order here is known ahead of time because the arena is deterministic,
/// // but note that in general this will be completely unsorted with respect to
/// // the elements or the shared values.
/// let expected = [
///     (p0_42, "e0", "42"),
///     (p3_42, "e3", "42"),
///     (p2_42, "e2", "42"),
///     (p4_7, "e4", "7"),
///     (p5_7, "e5", "7"),
/// ];
/// // this iterator is not cloning the shared values, it is simply repeatedly
/// // indexing them when multiple elements are associated with a single shared
/// // value
/// for (i, (p, element, shared)) in a.iter_combined().enumerate() {
///     assert_eq!(expected[i], (p, element.as_str(), shared.as_str()));
/// }
///
/// let (removed_s, kept_p) = a.union(p0_42, p4_7).unwrap();
/// // One of the "7" or "42" shared values was removed from the arena, and the
/// // other remains in the arena. Suppose we want to take a custom union of the
/// // `String`s to go along with the union of the elements, we would do
/// // something like
/// *a.get_shared_mut(kept_p).unwrap() =
///     format!("{} + {}", a.get_shared(kept_p).unwrap(), removed_s);
///
/// assert_eq!(a.len_surject(p0_42).unwrap().get(), 5);
/// let expected = [
///     (p0_42, "e0", "42 + 7"),
///     (p3_42, "e3", "42 + 7"),
///     (p2_42, "e2", "42 + 7"),
///     (p4_7, "e4", "42 + 7"),
///     (p5_7, "e5", "42 + 7"),
/// ];
/// for (i, (p, element, shared)) in a.iter_combined().enumerate() {
///     assert_eq!(expected[i], (p, element.as_str(), shared.as_str()));
/// }
///
/// // only upon removing the last element is the shared value returned
/// // (or we could use the wholesale `remove_shared`)
/// assert_eq!(
///     a.remove_element(p4_7).allow(),
///     Some(("e4".to_owned(), None))
/// );
/// assert_eq!(
///     a.remove_element(p0_42).allow(),
///     Some(("e0".to_owned(), None))
/// );
/// assert_eq!(
///     a.remove_element(p3_42).allow(),
///     Some(("e3".to_owned(), None))
/// );
/// assert_eq!(
///     a.remove_element(p5_7).allow(),
///     Some(("e5".to_owned(), None))
/// );
/// assert_eq!(
///     a.remove_element(p2_42).allow(),
///     Some(("e2".to_owned(), Some("42 + 7".to_owned())))
/// );
/// ```
pub struct SurjectArena<
    P: Ptr,
    T,
    S,
    #[cfg(feature = "alloc")] B: ArenaBacking = crate::HeapBacking,
    #[cfg(not(feature = "alloc"))] B: ArenaBacking,
> {
    pub(crate) elements: ChainArena<P, SurjectElement<P, T>, B>,
    pub(crate) shared_vals: Arena<PtrNoGen<P>, SurjectShared<S>, B>,
}

// REF(insertion_idempotency)

/// See [ArenaInsertTrait](crate::traits::ArenaInsertTrait)
pub struct SurjectArenaInsertSurjectEntry<'a, P: Ptr, T, S, B: ArenaBacking> {
    this: &'a mut SurjectArena<P, T, S, B>,
    p: P,
}

impl<'a, P: Ptr, T, S, B: ArenaBacking> SurjectArenaInsertSurjectEntry<'a, P, T, S, B> {
    /// Returns the `P` that the single element of the new surject will be
    /// associated with
    pub fn ptr(&self) -> P {
        self.p
    }

    /// Inserts a new surject consisting of the single element `t` and the
    /// shared value `s`
    pub fn insert(self, t: T, s: S) {
        let p_shared = self.this.shared_vals.insert(SurjectShared {
            s,
            element_count: NonZeroUsize::new(1).unwrap(),
        });
        let p = self
            .this
            .elements
            .insert(LinkInsertKind::SingleLinkCyclic, SurjectElement {
                t,
                p_shared,
            });
        // REF(insertion_idempotency)
        if p != self.p {
            unreachable!()
        }
    }
}

/// See [ArenaInsertTrait](crate::traits::ArenaInsertTrait)
pub struct SurjectArenaInsertEntry<'a, P: Ptr, T, S, B: ArenaBacking> {
    this: &'a mut SurjectArena<P, T, S, B>,
    p_target: P::Inx,
    p_new: P,
}

impl<'a, P: Ptr, T, S, B: ArenaBacking> SurjectArenaInsertEntry<'a, P, T, S, B> {
    /// Returns the `P` that the newly inserted element will be associated with,
    /// and not the `ptr_in_target_surject`
    pub fn ptr(&self) -> P {
        self.p_new
    }

    /// Inserts the element `t` into the target surject
    pub fn insert(self, t: T) {
        let this = self.this;
        let p_shared = this.elements.get_inx_unwrap(self.p_target).p_shared;
        let element_count = &mut this
            .shared_vals
            .get_inx_mut_unwrap(p_shared.inx())
            .element_count;
        // it is impossible to overflow this, it would mean that we have already
        // inserted `usize + 1` elements
        *element_count = NonZeroUsize::new(element_count.get().wrapping_add(1)).unwrap();
        let p = this
            .elements
            .insert(LinkInsertKind::NextToInx(self.p_target), SurjectElement {
                t,
                p_shared,
            });
        // REF(insertion_idempotency)
        if p != self.p_new {
            unreachable!()
        }
    }
}

impl<P: Ptr, T, S, B: ArenaBacking> SurjectArena<P, T, S, B> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        // needs to be done because of manual `ArenaSlot` handling
        ChainArena::_check_invariants(&this.elements)?;
        Arena::_check_invariants(&this.shared_vals)?;
        Self::_check_surjects(this)?;
        Ok(())
    }

    #[doc(hidden)]
    pub fn _check_surjects(this: &Self) -> Result<(), &'static str> {
        // there should be exactly one element chain associated with each shared value
        let mut count = Arena::<PtrNoGen<P>, usize, B>::new();
        count.clone_from_with(&this.shared_vals, |_, _| 0).unwrap();
        for element in this.elements.vals() {
            match count.get_mut(element.p_shared) {
                Some(len) => *len = len.checked_add(1).unwrap(),
                None => return Err("element points to nonexistent shared value"),
            }
        }
        for (p_shared, n) in &count {
            if this.shared_vals.get(p_shared).unwrap().element_count.get() != *n {
                return Err("element count does not match actual");
            }
        }

        let mut adv = this.elements.advancer();
        while let Some(p) = adv.advance(&this.elements) {
            let mut c = *count.get(this.elements.get(p).unwrap().p_shared).unwrap();
            if c != 0 {
                // upon encountering a nonzero count for the first time, we follow the chain and
                // count down, and if we reach back to the beginning (verifying cyclic chain)
                // and reach a count of zero, then we know that the chain encountered all the
                // needed elements. Subsequent encounters with the rest of the chain is ignored
                // because the count is zeroed afterwards.
                let mut tmp = p.inx();
                loop {
                    if c == 0 {
                        return Err("did not reach end of surject chain in expected time");
                    }
                    c = c.checked_sub(1).unwrap();
                    let (_, link) = this.elements.get_inx_link_no_gen(tmp).unwrap();
                    if let Some(next) = link.next() {
                        tmp = next;
                    } else {
                        return Err("surject chain is not cyclic");
                    }
                    // have the test after the match so that we check for single node cyclics
                    if tmp == p.inx() {
                        if c != 0 {
                            return Err("surject chain did not have all elements associated with \
                                        the shared value");
                        }
                        *count
                            .get_mut(this.elements.get(p).unwrap().p_shared)
                            .unwrap() = 0;
                        break;
                    }
                }
            }
        }
        Ok(())
    }

    /// See [ArenaTrait::with_min_capacity], this has separate capacities for
    /// the elements and the shared values
    pub fn with_min_capacity_separated(
        min_capacity_elements: usize,
        min_capacity_shared: usize,
    ) -> Result<Self, AllocError> {
        Ok(Self {
            elements: ChainArena::with_min_capacity(min_capacity_elements)?,
            shared_vals: Arena::with_min_capacity(min_capacity_shared)?,
        })
    }

    /// Returns the number of shared values, or equivalently the number of
    /// surjects in the arena. `self.len() >= self.len_shared()` is always true.
    pub fn len_shared(&self) -> usize {
        self.shared_vals.len()
    }

    /// Returns the number of elements in the surject that contains `p`, with
    /// `p` being a `Ptr` to any one of those elements. Returns `None` if `p` is
    /// invalid.
    #[must_use]
    pub fn len_surject(&self, p: P) -> Option<NonZeroUsize> {
        let p_shared = self.elements.get(p)?.p_shared;
        Some(
            self.shared_vals
                .get_inx_unwrap(p_shared.inx())
                .element_count,
        )
    }

    /// Returns the capacity of shared values of the arena
    pub fn capacity_shared(&self) -> usize {
        self.shared_vals.capacity()
    }

    /// Returns the max shared value capacity of the arena
    pub fn max_capacity_shared(&self) -> Option<usize> {
        self.shared_vals.max_capacity()
    }

    /// Follows [Arena::generation]
    pub fn generation(&self) -> P::Gen {
        self.elements.generation()
    }

    /// Follows [Arena::set_generation]
    pub fn set_generation(&mut self, new_gen: P::Gen) {
        self.elements.set_generation(new_gen)
    }

    /// Follows [Arena::inc_generation]
    pub fn inc_generation(&mut self) -> InvalidationOption<()> {
        self.elements.inc_generation()
    }

    /// Follows [ArenaTrait::reallocate_min_capacity] for the elements
    pub fn reallocate_min_capacity_elements(
        &mut self,
        min_capacity: usize,
    ) -> Result<(), ReallocationError> {
        self.elements.reallocate_min_capacity(min_capacity)
    }

    /// Follows [ArenaTrait::reallocate_min_capacity] for the shared values
    pub fn reallocate_min_capacity_shared(
        &mut self,
        min_capacity: usize,
    ) -> Result<(), ReallocationError> {
        self.shared_vals.reallocate_min_capacity(min_capacity)
    }

    /// Inserts a new surject into the arena, consisting of the single element
    /// `t` and the shared value `s`. Returns a `Ptr` to the element.
    pub fn insert_surject_within_capacity(
        &mut self,
        t: T,
        s: S,
    ) -> Result<P, NotWithinCapacityError> {
        let entry = self.entry_insert_surject_within_capacity()?;
        let p = entry.ptr();
        entry.insert(t, s);
        Ok(p)
    }

    /// Reallocating version of
    /// [insert_surject_within_capacity](SurjectArena::insert_surject_within_capacity)
    pub fn insert_surject_reallocating(&mut self, t: T, s: S) -> Result<P, ReallocationError> {
        let entry = self.entry_insert_surject_reallocating()?;
        let p = entry.ptr();
        entry.insert(t, s);
        Ok(p)
    }

    /// Panicking version of
    /// [insert_surject_within_capacity](SurjectArena::insert_surject_within_capacity)
    ///
    /// # Panics
    ///
    /// Panics on allocation failure or if max capacity is used up
    #[track_caller]
    pub fn insert_surject(&mut self, t: T, s: S) -> P {
        self.insert_surject_reallocating(t, s)
            .expect("`SurjectArena::insert_surject_reallocating` failed")
    }

    /// Entry version of
    /// [insert_surject_within_capacity](SurjectArena::insert_surject_within_capacity)
    pub fn entry_insert_surject_within_capacity(
        &mut self,
    ) -> Result<SurjectArenaInsertSurjectEntry<'_, P, T, S, B>, NotWithinCapacityError> {
        let entry = self
            .elements
            .entry_insert_within_capacity(LinkInsertKind::SingleLinkCyclic)
            .map_err(|_| NotWithinCapacityError)?;
        let p = entry.ptr();
        // will need space for a new shared value
        let _ = self.shared_vals.entry_insert_within_capacity()?;
        Ok(SurjectArenaInsertSurjectEntry { this: self, p })
    }

    /// Entry version of
    /// [insert_surject_reallocating](SurjectArena::insert_surject_reallocating)
    pub fn entry_insert_surject_reallocating(
        &mut self,
    ) -> Result<SurjectArenaInsertSurjectEntry<'_, P, T, S, B>, ReallocationError> {
        let p = match self
            .elements
            .entry_insert_reallocating(LinkInsertKind::SingleLinkCyclic)
        {
            Ok(entry) => entry.ptr(),
            Err(ChainInsertionError::BeyondMaxCapacity) => {
                return Err(ReallocationError::BeyondMaxCapacity);
            }
            Err(_) => return Err(ReallocationError::AllocError),
        };
        let _ = self.shared_vals.entry_insert_reallocating()?;
        Ok(SurjectArenaInsertSurjectEntry { this: self, p })
    }

    /// Inserts a new element `t` into the arena, associating it with an
    /// existing surject, of which `ptr_in_target_surject` is an existing
    /// element of that surject. Returns
    /// [FailedLinkRequirement](ChainInsertionError::FailedLinkRequirement) if
    /// `ptr_in_target_surject` is invalid.
    pub fn insert_within_capacity(
        &mut self,
        ptr_in_target_surject: P,
        t: T,
    ) -> Result<P, ChainInsertionError> {
        let entry = self.entry_insert_within_capacity(ptr_in_target_surject)?;
        let p = entry.ptr();
        entry.insert(t);
        Ok(p)
    }

    /// Reallocating version of
    /// [insert_within_capacity](SurjectArena::insert_within_capacity)
    pub fn insert_reallocating(
        &mut self,
        ptr_in_target_surject: P,
        t: T,
    ) -> Result<P, ChainInsertionError> {
        let entry = self.entry_insert_reallocating(ptr_in_target_surject)?;
        let p = entry.ptr();
        entry.insert(t);
        Ok(p)
    }

    /// Panicking version of
    /// [insert_within_capacity](SurjectArena::insert_within_capacity)
    ///
    /// # Panics
    ///
    /// Panics on allocation failure, or if max capacity is used up, or if
    /// `ptr_in_target_surject` was invalid
    #[track_caller]
    pub fn insert(&mut self, ptr_in_target_surject: P, t: T) -> P {
        self.insert_reallocating(ptr_in_target_surject, t)
            .expect("`SurjectArena::insert_reallocating` failed")
    }

    /// Entry version of
    /// [insert_within_capacity](SurjectArena::insert_within_capacity)
    pub fn entry_insert_within_capacity(
        &mut self,
        ptr_in_target_surject: P,
    ) -> Result<SurjectArenaInsertEntry<'_, P, T, S, B>, ChainInsertionError> {
        if !self.contains(ptr_in_target_surject) {
            return Err(ChainInsertionError::FailedLinkRequirement);
        }
        // only need space for the element, the shared value already exists
        let entry = self
            .elements
            .entry_insert_within_capacity(LinkInsertKind::SingleLinkCyclic)?;
        let p = entry.ptr();
        Ok(SurjectArenaInsertEntry {
            this: self,
            p_target: ptr_in_target_surject.inx(),
            p_new: p,
        })
    }

    /// Entry version of
    /// [insert_reallocating](SurjectArena::insert_reallocating)
    pub fn entry_insert_reallocating(
        &mut self,
        ptr_in_target_surject: P,
    ) -> Result<SurjectArenaInsertEntry<'_, P, T, S, B>, ChainInsertionError> {
        if !self.contains(ptr_in_target_surject) {
            return Err(ChainInsertionError::FailedLinkRequirement);
        }
        // only need space for the element, the shared value already exists
        let entry = self
            .elements
            .entry_insert_reallocating(LinkInsertKind::SingleLinkCyclic)?;
        let p = entry.ptr();
        Ok(SurjectArenaInsertEntry {
            this: self,
            p_target: ptr_in_target_surject.inx(),
            p_new: p,
        })
    }

    /// Returns if `p0` and `p1` point to elements in the same surject. Returns
    /// `None` if `p0` or `p1` are invalid.
    #[must_use]
    pub fn in_same_surject(&self, p0: P, p1: P) -> Option<bool> {
        Some(self.elements.get(p0)?.p_shared == self.elements.get(p1)?.p_shared)
    }

    /// Returns a reference to the shared value of the surject that contains the
    /// element pointed to by `p`
    #[must_use]
    pub fn get_shared(&self, p: P) -> Option<&S> {
        let p_shared = self.elements.get(p)?.p_shared;
        Some(&self.shared_vals.get_inx_unwrap(p_shared.inx()).s)
    }

    /// Returns a mutable reference to the shared value of the surject that
    /// contains the element pointed to by `p`
    #[must_use]
    pub fn get_shared_mut(&mut self, p: P) -> Option<&mut S> {
        let p_shared = self.elements.get(p)?.p_shared;
        Some(&mut self.shared_vals.get_inx_mut_unwrap(p_shared.inx()).s)
    }

    /// The same as
    /// [get_disjoint_mut](crate::traits::DisjointableArenaTrait::get_disjoint_mut)
    /// except that it is for the shared values, and so this additionally
    /// requires that the `indices` all be from different surjects.
    pub fn get_disjoint_shared_mut<const N: usize>(
        &mut self,
        indices: [P; N],
    ) -> Result<[&mut S; N], GetDisjointMutError> {
        let mut p_shareds = [PtrNoGen::<P>::invalid(); N];
        for (p_shared, p) in p_shareds.iter_mut().zip(indices) {
            *p_shared = self
                .elements
                .get(p)
                .ok_or(GetDisjointMutError::IndexOutOfBounds)?
                .p_shared;
        }
        self.shared_vals
            .get_disjoint_mut(p_shareds)
            .map(|shareds| shareds.map(|shared| &mut shared.s))
    }

    /// Returns the generation associated with `p` and a `LinkNoGen<P, &T>`, the
    /// interlinks of which point to the other elements in the surject. Each
    /// surject is a cyclic chain of `LinkNoGen`s.
    #[must_use]
    pub fn get_inx_link_no_gen(&self, p: P::Inx) -> Option<(P::Gen, LinkNoGen<P, &T>)> {
        self.elements
            .get_inx_link_no_gen(p)
            .map(|(generation, link)| (generation, LinkNoGen::new(link.prev_next(), &link.t.t)))
    }

    /// Takes the union of two surjects, of which `p0` points to an element in
    /// one surject and `p1` points to an element in the other surject. If
    /// `self.len_surject(p0) < self.len_surject(p1)`, then the shared value
    /// associated with `p0` is removed and returned in a tuple with `p1`,
    /// and the surject of `p0` is changed to point to the shared value of
    /// `p1`'s surject. If `self.len_surject(p0) >= self.len_surject(p1)`,
    /// the shared value pointed to by `p1` is removed and returned in a
    /// tuple with `p0`, and the surject of `p1` is changed to point to the
    /// shared value of `p0`'s surject. Returns `None` if
    /// `self.in_same_surject(p0, p1)`.
    ///
    /// # Note
    ///
    /// No `Ptr`s are invalidated even though a shared value is removed, all
    /// that happens is both sets of elements are redirected to point to a
    /// common shared value.
    ///
    /// This function is defined in this way to guarantee a `O(n log n)` cost
    /// for performing repeated unions in any order on a given starting arena.
    /// If the two `S`s are some kind of additive structure that also need to
    /// have their union taken, then the contents of the `S` in the return tuple
    /// can be transferred to the shared value pointed to by the `P` also in the
    /// return tuple. This way, users do not actually need to consider surject
    /// sizes explicitly.
    ///
    /// We purposely reverse the typical order from `(P, S)` to `(S, P)`
    /// to give a visual that the returned things were not pointing to each
    /// other.
    #[must_use]
    pub fn union(&mut self, mut p0: P, mut p1: P) -> Option<(S, P)> {
        let mut p_shared0 = self.elements.get(p0)?.p_shared;
        let mut p_shared1 = self.elements.get(p1)?.p_shared;
        if p_shared0 == p_shared1 {
            // corresponds to the same surject
            return None;
        }
        let len0 = self
            .shared_vals
            .get_inx_unwrap(p_shared0.inx())
            .element_count
            .get();
        let len1 = self
            .shared_vals
            .get_inx_unwrap(p_shared1.inx())
            .element_count
            .get();
        if len0 < len1 {
            mem::swap(&mut p_shared0, &mut p_shared1);
            mem::swap(&mut p0, &mut p1);
        }
        // overwrite the `p_shared`s in the smaller chain
        let mut tmp = p1.inx();
        loop {
            self.elements.get_inx_mut_unwrap(tmp).p_shared = p_shared0;
            tmp = self
                .elements
                .get_inx_link_no_gen(tmp)
                .unwrap()
                .1
                .next()
                .unwrap();
            if tmp == p1.inx() {
                break;
            }
        }
        // combine chains cheaply, this is why they need to be cyclic because exchanging
        // two interlinks anywhere between the chains results in a combined single
        // cyclic chain.
        self.elements.exchange_next(p0, p1).unwrap();
        // it is impossible to overflow this, it would mean that we have already
        // inserted `usize + 1` elements
        self.shared_vals
            .get_inx_mut_unwrap(p_shared0.inx())
            .element_count = NonZeroUsize::new(len0.wrapping_add(len1)).unwrap();
        Some((self.shared_vals.remove(p_shared1).allow().unwrap().s, p0))
    }

    /// Removes the element pointed to by `p`. If there were other elements
    /// still in the surject, the shared value is not removed and `Some((t,
    /// None))` is returned. If `p` was the last remaining element in the
    /// surject, then the shared value is removed and returned like
    /// `Some((t, Some(s)))`. Returns `None` if `p` is not valid.
    pub fn remove_element(&mut self, p: P) -> InvalidationResult<(T, Option<S>)> {
        if !self.contains(p) {
            return InvalidationResult::InvalidPtr;
        }
        self.remove_element_inx(p.inx()).map(|(_, t, s)| (t, s))
    }

    /// The same as [remove_element](SurjectArena::remove_element) except that
    /// the generation is ignored and the existing generation is returned.
    pub fn remove_element_inx(&mut self, p: P::Inx) -> InvalidationResult<(P::Gen, T, Option<S>)> {
        let ((generation, element), o) = match self.elements.remove_inx(p) {
            InvalidationResult::Success(element) => (element, false),
            InvalidationResult::GenerationOverflow(element) => (element, true),
            InvalidationResult::InvalidPtr => return InvalidationResult::InvalidPtr,
        };
        let p_shared = element.p_shared;
        let t = element.t;
        let element_count = &mut self
            .shared_vals
            .get_inx_mut_unwrap(p_shared.inx())
            .element_count;
        let res = if let Some(next) = NonZeroUsize::new(element_count.get() - 1) {
            // decrement the element count
            *element_count = next;
            (generation, t, None)
        } else {
            // last element, remove the shared value
            (
                generation,
                t,
                Some(self.shared_vals.remove(p_shared).allow().unwrap().s),
            )
        };
        if o {
            InvalidationResult::GenerationOverflow(res)
        } else {
            InvalidationResult::Success(res)
        }
    }

    /// Removes the entire surject that contains `p`, dropping all of its
    /// elements and returning the shared value. `p` can point to any element of
    /// the surject. This is a version of
    /// [drain_surject](SurjectArena::drain_surject) optimized for just
    /// returning the shared value.
    pub fn remove_shared(&mut self, p: P) -> InvalidationResult<S> {
        let Some(element) = self.elements.get(p) else {
            return InvalidationResult::InvalidPtr;
        };
        let s = self.shared_vals.remove(element.p_shared).allow().unwrap().s;
        self.elements.remove_cyclic_chain_internal(p.inx());
        match self.inc_generation() {
            InvalidationOption::Success(()) => InvalidationResult::Success(s),
            InvalidationOption::GenerationOverflow(()) => InvalidationResult::GenerationOverflow(s),
        }
    }

    /// REF(surject_canonical_perm) Reads back an entry of the permutation that
    /// the first pass of [compress_canonical](SurjectArena::compress_canonical)
    /// wrote into the first `self.len_shared()` elements
    fn permutation_entry(&self, raw_inx: NonZeroUsize) -> NonZeroUsize {
        let p_shared = self
            .elements
            .get_inx_unwrap(from_checked_raw::<P>(raw_inx))
            .p_shared;
        from_checked_ptr::<PtrNoGen<P>>(p_shared.inx())
    }

    /// This is similar to
    /// [compress_canonical](crate::traits::ChainArenaTrait::compress_canonical),
    /// laying out the elements within the same surject to be contiguous with
    /// one another, and improving cache locality. Unlike
    /// [compress_with](ArenaTrait::compress_with), which only compresses the
    /// elements, this also removes any free slots among the shared values.
    ///
    /// The shared values are internally laid out canonically as well, such that
    /// their indexes are `1..=self.len_shared()` in the same order that
    /// their surjects occupy the elements.
    ///
    /// Because an element can be internally swapped multiple times to achieve
    /// this in-place in the allocation, this cannot have a map. Use
    /// [transfer_canonical_reallocating](SurjectArena::transfer_canonical_reallocating)
    /// if you need a recaster.
    pub fn compress_canonical(&mut self, reset_generation: bool) -> InvalidationOption<()> {
        let res = self.elements.compress_canonical(reset_generation);
        let Some(len_shared) = NonZeroUsize::new(self.shared_vals.len()) else {
            // guaranteed empty, but there can still be free slots to remove
            self.shared_vals.remove_free_end_slots();
            self.shared_vals.freelist_root = None;
            return res;
        };

        // The surjects are continuous within themselves first and also between
        // themselves, so there is one well defined order where the `k`th surject has
        // its shared value at index `k`. We can't look up elements from shared values,
        // so we do this in three passes with temporarily suspended invariants to
        // support encoding the permutation in the `p_shared`s of the first `k`
        // elements.

        // REF(surject_canonical_perm) the `k`th surject starts at element index `s >=
        // k`, and every surject has at least one element, so we can write the current
        // index of its shared value into element `k`, so that in the next pass the
        // swaps can know what to change, and in the final pass we can recover with the
        // canonical ordering and surject sizes. This loop works because by the time we
        // reach element index `s`, we are either doing a no-op with the existing value
        // (happens for the first surjects that are all of length 1) or clobbering an
        // element of a surject that has already been saved earlier.
        let mut s = NonZeroUsize::new(1).unwrap();
        for raw_k in nzusize_iter(NonZeroUsize::new(1).unwrap(), Some(len_shared)) {
            let raw_s = from_checked_raw::<P>(s);
            let p_shared = self.elements.get_inx_unwrap(raw_s).p_shared;
            // get this while `p_shared` is still valid
            let element_count = self
                .shared_vals
                .get_inx_unwrap(p_shared.inx())
                .element_count;
            self.elements
                .get_inx_mut_unwrap(from_checked_raw::<P>(raw_k))
                .p_shared = p_shared;
            s = s.checked_add(element_count.get()).unwrap();
        }

        // canonicalize the shared values
        for raw_i in nzusize_iter(NonZeroUsize::new(1).unwrap(), Some(len_shared)) {
            let mut raw_j = self.permutation_entry(raw_i);
            while raw_j < raw_i {
                raw_j = self.permutation_entry(raw_j);
            }
            if raw_j != raw_i {
                let [slot_i, slot_j] = self
                    .shared_vals
                    .m
                    .get_disjoint_mut([raw_i, raw_j])
                    .unwrap_or_else(|_| unreachable!());
                mem::swap(slot_i, slot_j);
            }
        }

        // recover, can be done purely from shared values and their element counts
        let mut s = NonZeroUsize::new(1).unwrap();
        for raw_k in nzusize_iter(NonZeroUsize::new(1).unwrap(), Some(len_shared)) {
            let inx_k = from_checked_raw::<PtrNoGen<P>>(raw_k);
            let element_count = self.shared_vals.get_inx_unwrap(inx_k).element_count.get();
            let p_shared = Ptr::_from_raw(inx_k, ());
            for _ in 0..element_count {
                self.elements
                    .get_inx_mut_unwrap(from_checked_raw::<P>(s))
                    .p_shared = p_shared;
                s = s.checked_add(1).unwrap();
            }
        }

        self.shared_vals.remove_free_end_slots();
        self.shared_vals.freelist_root = None;
        res
    }

    /// FIXME recaster example
    pub fn transfer_canonical_reallocating<
        Q: Ptr,
        T1,
        S1,
        B1: ArenaBacking,
        F0: FnMut(Q, InvalidationOption<T1>, P) -> T,
        F1: FnMut(S1) -> S,
    >(
        &mut self,
        new_generation: P::Gen,
        source: &mut SurjectArena<Q, T1, S1, B1>,
        mut map_element: F0,
        mut map_shared: F1,
    ) -> Result<(), ReallocationError> {
        // precheck both the elements and the shared values first, can't have atomic
        // fallibility without it

        let Some(len) = NonZeroUsize::new(source.len()) else {
            // follow what the other path would logically do
            self.clear().allow();
            self.set_generation(new_generation);
            return Ok(());
        };
        // REF(careful_index_checking) here and in the rest of this function
        if P::Inx::try_from_usize(len).is_none() {
            return Err(ReallocationError::AllocError);
        };
        if len.get() > self.capacity() {
            // max capacity is tested here
            self.reallocate_min_capacity_elements(len.get())?;
        }

        // guaranteed nonempty at this point
        let len_shared = NonZeroUsize::new(source.len_shared()).unwrap();
        if P::Inx::try_from_usize(len_shared).is_none() {
            return Err(ReallocationError::AllocError);
        };
        if len_shared.get() > self.capacity_shared() {
            // max capacity is tested here
            self.reallocate_min_capacity_shared(len_shared.get())?;
        }

        // the rest should be infallible if soft invariants are followed
        self.clear().allow();
        self.set_generation(new_generation);

        // Transfer and canonicalize the elements first. We rely on the canonical
        // ordering to focus on the surjects one at a time completely, and in order so
        // that we can map the shared value and its new `Ptr` all in one step

        let mut current_source_p_shared = None;
        let mut mapped_p_shared = PtrNoGen::<P>::invalid();
        self.elements
            .transfer_canonical_reallocating(new_generation, &mut source.elements, |q, o, p| {
                let (element, o) = o.overflowing();
                let arg = if o {
                    InvalidationOption::GenerationOverflow(element.t)
                } else {
                    InvalidationOption::Success(element.t)
                };
                let t = map_element(q, arg, p);

                let new_surject = if let Some(p_shared) = current_source_p_shared {
                    element.p_shared != p_shared
                } else {
                    true
                };
                if new_surject {
                    current_source_p_shared = Some(element.p_shared);
                    let shared = source.shared_vals.remove(element.p_shared).allow().unwrap();
                    let mapped_shared = map_shared(shared.s);
                    mapped_p_shared = self.shared_vals.insert(SurjectShared {
                        s: mapped_shared,
                        element_count: shared.element_count,
                    });
                }

                SurjectElement {
                    t,
                    p_shared: mapped_p_shared,
                }
            })
            .unwrap();

        Ok(())
    }

    /// Has the same properties of [Arena::clone_from_with]. `map_shared` is
    /// given the number of elements in the surject along with the `&S1`.
    pub fn clone_from_with<T1, S1, F0: FnMut(P, &T1) -> T, F1: FnMut(NonZeroUsize, &S1) -> S>(
        &mut self,
        source: &SurjectArena<P, T1, S1, B>,
        mut map_element: F0,
        mut map_shared: F1,
    ) -> Result<(), ReallocationError> {
        // FIXME try to reallocate the shared values and fail ahead of time
        self.elements.clone_from_with(&source.elements, |p, link| {
            let t = map_element(p, &link.t.t);
            SurjectElement {
                t,
                p_shared: link.t.p_shared,
            }
        })?;
        self.shared_vals
            .clone_from_with(&source.shared_vals, |_, shared| {
                let s = map_shared(shared.element_count, &shared.s);
                SurjectShared {
                    s,
                    element_count: shared.element_count,
                }
            })?;
        Ok(())
    }

    /// Overwrites `chain_arena` (dropping all preexisting `U`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`, with surjects each preserved as cyclical chains.
    pub fn clone_to_chain_arena<U, F: FnMut(P, &T) -> U>(
        &self,
        chain_arena: &mut ChainArena<P, U, B>,
        mut map: F,
    ) -> Result<(), ReallocationError> {
        chain_arena.clone_from_with(&self.elements, |p, link| map(p, &link.t.t))
    }

    /// Overwrites `arena` (dropping all preexisting `U` and relations,
    /// overwriting the generation counter, and reusing capacity) with the
    /// `Ptr` mapping of `self`.
    pub fn clone_to_arena<U, F: FnMut(P, &T) -> U>(
        &self,
        arena: &mut Arena<P, U, B>,
        mut map: F,
    ) -> Result<(), ReallocationError> {
        self.elements
            .clone_to_arena(arena, |p, link| map(p, &link.t.t))
    }

    /// Directly returns a reference to the internal backing, for the purposes
    /// of accessing `ArenaBacking`-specific functions
    pub fn backing(
        &self,
    ) -> (
        &B::Stack<ArenaSlot<P, LinkNoGen<P, SurjectElement<P, T>>>>,
        &B::Stack<ArenaSlot<PtrNoGen<P>, SurjectShared<S>>>,
    ) {
        (self.elements.backing(), self.shared_vals.backing())
    }

    /// Directly returns a mutable reference to the internal backing, for the
    /// purposes of accessing `ArenaBacking`-specific functions
    ///
    /// # Safety
    ///
    /// The `ArenaSlot` allocation state must not be modified, or else the
    /// freelist or entry length could be broken. The `LinkNoGen` interlinks
    /// must also not be modified, or else chain invariants could be broken, and
    /// `SurjectArena` related invariants should not be mutated.
    pub unsafe fn backing_mut(
        &mut self,
    ) -> (
        &mut B::Stack<ArenaSlot<P, LinkNoGen<P, SurjectElement<P, T>>>>,
        &mut B::Stack<ArenaSlot<PtrNoGen<P>, SurjectShared<S>>>,
    ) {
        // Safety: called in `unsafe` function with same invariants and added invariants
        unsafe { (self.elements.backing_mut(), self.shared_vals.backing_mut()) }
    }
}

impl<P: Ptr, T, S, B: ArenaBacking> Default for SurjectArena<P, T, S, B> {
    fn default() -> Self {
        Self::new()
    }
}

// Note: I would try returning both, but `&(&T, &S)` becomes problematic and we
// may as well follow the other arenas with respect to `ArenaTrait` definitions

impl<P: Ptr, T, S, B: ArenaBacking, Q: Borrow<P>> Index<Q> for SurjectArena<P, T, S, B> {
    type Output = T;

    /// Returns a reference to the `T` pointed to by `inx`. Use
    /// [get](ArenaTrait::get) if invalid `Ptr`s need to be handled,
    /// [get_shared](SurjectArena::get_shared) if the shared value is wanted
    /// instead, or
    /// [get_inx_link_no_gen](SurjectArena::get_inx_link_no_gen) if the
    /// neighboring elements of the surject are also needed.
    ///
    /// # Panics
    ///
    /// If `inx` is invalid
    #[track_caller]
    fn index(&self, inx: Q) -> &T {
        let p: P = *inx.borrow();
        self.get(p)
            .expect("indexed `SurjectArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T, S, B: ArenaBacking, Q: Borrow<P>> IndexMut<Q> for SurjectArena<P, T, S, B> {
    /// Returns a mutable reference to the `T` pointed to by `inx`. Use
    /// [get_mut](ArenaTrait::get_mut) if invalid `Ptr`s need to be handled, or
    /// [get_shared_mut](SurjectArena::get_shared_mut) if the shared value is
    /// wanted instead.
    ///
    /// # Panics
    ///
    /// If `inx` is invalid
    #[track_caller]
    fn index_mut(&mut self, inx: Q) -> &mut T {
        let p: P = *inx.borrow();
        self.get_mut(p)
            .expect("indexed `SurjectArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T: Debug, S: Debug, B: ArenaBacking> Debug for SurjectArena<P, T, S, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.internal_iter()).finish()
    }
}

/// Implemented if `T: Clone` and `S: Clone`.
impl<P: Ptr, T: Clone, S: Clone, B: ArenaBacking> Clone for SurjectArena<P, T, S, B> {
    /// Has the `Ptr` preserving properties of [Arena::clone]
    fn clone(&self) -> Self {
        Self {
            elements: self.elements.clone(),
            shared_vals: self.shared_vals.clone(),
        }
    }

    /// Has the `Ptr` and capacity preserving properties of [Arena::clone_from]
    fn clone_from(&mut self, source: &Self) {
        self.elements.clone_from(&source.elements);
        self.shared_vals.clone_from(&source.shared_vals);
    }
}

impl<P: Ptr, T, S, B: ArenaBacking> SetMaxCapacity for SurjectArena<P, T, S, B>
where
    <B as ArenaBacking>::Stack<ArenaSlot<P, LinkNoGen<P, SurjectElement<P, T>>>>: SetMaxCapacity,
    <B as ArenaBacking>::Stack<ArenaSlot<PtrNoGen<P>, SurjectShared<S>>>: SetMaxCapacity,
{
    fn set_max_capacity(&mut self, max_capacity: usize) -> Result<(), MaxCapacityReductionError> {
        // the shared values are implicitly limited by the elements, but we may be
        // increasing beyond the original limits
        self.shared_vals.set_max_capacity(max_capacity)?;
        self.elements.set_max_capacity(max_capacity)
    }
}
