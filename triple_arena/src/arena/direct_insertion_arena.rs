use core::{
    borrow::Borrow,
    fmt, mem,
    num::NonZeroUsize,
    ops::{Index, IndexMut},
};

use crate::{
    InvalidationOption,
    errors::{MaxCapacityReductionError, ReallocationError},
    traits::{
        Advancer, ArenaCloneFromWith, ArenaDirectInsertEntryTrait, ArenaDirectInsertTrait,
        ArenaTrait, CompactArenaTrait, Ptr, SetMaxCapacity,
    },
    utils::{
        from_checked_ptr, from_checked_raw,
        traits::{ArenaBacking, NonZeroInxGenericStack, PtrInx},
    },
};

// See REF(arena_terminology)

/// Internal slot for a freelist-less direct insertion arena. Note the `P::Gen`
/// is a ZST in logically generationless cases, and should have a niche
/// otherwise. Unlike [ArenaSlot](crate::utils::ArenaSlot), the free variant
/// does not need a freelist index.
#[derive(Clone)]
pub enum DirectSlot<P: Ptr, T> {
    /// A free slot with no `T`
    Free,
    /// A slot allocated for a `(P::Gen, T)` pair in the arena.
    Allocated(P::Gen, T),
}

use DirectSlot::*;

/// A freelist-less direct insertion arena implementing
/// [ArenaDirectInsertTrait]. The main purpose of this type is to follow the
/// state of another arena, or to be used as a low level building block in a
/// custom compound arena.
///
/// [ArenaInsertTrait](crate::traits::ArenaInsertTrait) is not implemented,
/// because without a freelist there is no efficient way of finding the next
/// unallocated slot. Instead,
/// [direct_insert_within_capacity](
/// ArenaDirectInsertTrait::direct_insert_within_capacity) inserts at a `Ptr`
/// chosen by the caller.
///
/// There is no global generation and [ArenaTrait::singular_generation] will
/// always return `None`. Instead, each slot keeps whatever generation it was
/// directly inserted with. This means that [ArenaTrait::invalidate] can only
/// check that its `Ptr` is valid and return it unchanged, and the compress
/// functions ignore their `reset_generation` argument and move generations
/// along with their entries. Because nothing can increment a generation
/// counter, no generation overflow can occur from any operation on this arena,
/// but it is up to the user to avoid ABA problems.
///
/// ```
/// use triple_arena::{Arena, DirectArena, ptr_struct, traits::*};
///
/// ptr_struct!(P0);
///
/// let mut a = Arena::<P0, u64>::new();
/// let p0 = a.insert(42);
/// let p1 = a.insert(1337);
/// a.remove(p0).allow().unwrap();
///
/// // mirror the state of `a`, mapping the entries to something else
/// let mut mirror = DirectArena::<P0, String>::new();
/// mirror.clone_from_with(&a, |_, t| t.to_string()).unwrap();
/// assert_eq!(&format!("{mirror:?}"), "{P0[2](2): \"1337\"}");
///
/// // the `Ptr`s of `a` are directly usable on the mirror
/// assert_eq!(mirror[p1], "1337");
/// assert!(mirror.get(p0).is_none());
///
/// // mirror a new insertion in `a`, reusing the internal slot that `p0` had
/// let p2 = a.insert(7);
/// mirror
///     .direct_insert_within_capacity(p2)
///     .unwrap()
///     .insert("7".to_owned());
/// assert_eq!(
///     &format!("{mirror:?}"),
///     "{P0[1](3): \"7\", P0[2](2): \"1337\"}"
/// );
/// ```
pub struct DirectArena<
    P: Ptr,
    T,
    #[cfg(feature = "alloc")] B: ArenaBacking = crate::HeapBacking,
    #[cfg(not(feature = "alloc"))] B: ArenaBacking,
> {
    /// # Invariants
    ///
    /// - `len` is equal to the number of allocated slots
    pub(crate) m: B::Stack<DirectSlot<P, T>>,
    pub(crate) len: usize,
}

impl<P: Ptr, T, B: ArenaBacking> DirectArena<P, T, B> {
    pub(crate) fn nziter(&self) -> crate::fundamental::IntoNonZeroUsizeIterator {
        crate::fundamental::nzusize_iter(
            NonZeroUsize::new(1).unwrap(),
            NonZeroUsize::new(self.m.len()),
        )
    }

    /// Used by tests. Note that some errors are only for "soft" invariants.
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        // assume the backing is sane

        // clamped by both backing limits and the max `P::Inx`
        if (this.len() > this.capacity()) || (this.m.len() > this.capacity()) {
            return Err("len > capacity");
        }
        let mut n_allocated = 0usize;
        for i in this.nziter() {
            if matches!(this.m.get(i).unwrap(), Allocated(..)) {
                n_allocated = n_allocated.checked_add(1).unwrap();
            }
        }
        if this.len() != n_allocated {
            return Err("len != n_allocated");
        }
        Ok(())
    }

    /// `remove` but with an optional generation check. `None` is returned upon
    /// an invalid `Ptr`.
    pub(crate) fn remove_internal(
        &mut self,
        inx: P::Inx,
        generation: Option<P::Gen>,
    ) -> Option<(P::Gen, T)> {
        let raw_inx = P::Inx::try_into_usize(inx)?;
        let allocation = self.m.get_mut(raw_inx)?;
        match allocation {
            // invalid by being already free
            Free => None,
            Allocated(generation1, _) => {
                if let Some(generation) = generation
                    && *generation1 != generation
                {
                    // invalid by generation
                    return None;
                }

                let Allocated(generation, t) = mem::replace(allocation, Free) else {
                    unreachable!()
                };
                self.len = self.len.wrapping_sub(1);

                Some((generation, t))
            }
        }
    }

    /// The most general way to translate between domains. Given any `source`
    /// implementing [CompactArenaTrait] with any `Q: Ptr` and `U` entry type,
    /// this will transfer all of the entries by reallocating `self` if
    /// necessary, clearing `self`, and removing every entry from `source` and
    /// inserting a mapped `T` into `self`. Every entry is given by value to
    /// `map` with the original source `Q: Ptr`, an [InvalidationOption]`<U>`
    /// for being able to determine if the removal caused a generation overflow
    /// in `source`, the destination `P: Ptr`, and then `map` must return
    /// the `T` that will be inserted into `self`. The new entries are all
    /// given `new_generation`. The entries are guaranteed to be canonically
    /// compressed in `self`, such that their `P::Inx`s are
    /// `1..=source.len()` in advancer order.
    ///
    /// Reallocation only occurs if `source.len() > self.capacity()`. All of the
    /// fallible points happen before anything is modified, such that `self` and
    /// `source` are logically unchanged if an error is returned. An error is
    /// returned if the reallocation fails, if a
    /// [max_capacity](ArenaTrait::max_capacity) limit prevents the
    /// reallocation, or if `source.len()` is more than what `P::Inx` can
    /// represent.
    ///
    /// # Unwind Safety
    ///
    /// If `map` panics, the entry it was called with is lost to whatever `map`
    /// does, and `self` and `source` are left with the entries that were
    /// already transferred and the entries that have yet to be transferred
    /// respectively.
    pub fn transfer_reallocating<
        Q: Ptr,
        U,
        A: CompactArenaTrait<Q, U>,
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

        let mut p_raw = NonZeroUsize::new(1).unwrap();
        let mut adv = source.advancer();
        while let Some(q) = adv.advance(source) {
            let p = P::_from_raw(from_checked_raw::<P>(p_raw), new_generation);
            let t = map(q, source.remove(q).unwrap(), p);
            self.direct_insert_within_capacity(p).unwrap().insert(t);
            p_raw = p_raw.checked_add(1).unwrap();
        }
        Ok(())
    }

    /// Like [ArenaTrait::get], except generation counters are ignored and the
    /// result is unwrapped internally
    ///
    /// # Panics
    ///
    /// If `p` does not point to an allocated entry
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_unwrap(&self, p: P::Inx) -> &T {
        match self.m.get(from_checked_ptr::<P>(p)) {
            Some(Allocated(_, t)) => t,
            // if we use `panic` it induces stack management on every hot path according to the
            // assembly
            _ => unreachable!(), /* panic!("get_inx_unwrap of unallocated entry"), */
        }
    }

    /// Like [ArenaTrait::get_mut], except generation counters are ignored and
    /// the result is unwrapped internally
    ///
    /// # Panics
    ///
    /// If `p` does not point to an allocated entry
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_mut_unwrap(&mut self, p: P::Inx) -> &mut T {
        match self.m.get_mut(from_checked_ptr::<P>(p)) {
            Some(Allocated(_, t)) => t,
            _ => unreachable!(), /* panic!("get_inx_mut_unwrap of unallocated entry"), */
        }
    }

    /// Pops up to `num` free slots off of the end of the internal backing,
    /// stopping early upon reaching an allocated slot or popping off all slots.
    /// Returns the number of slots that were actually popped.
    ///
    /// Internal free slots on the end of a direct insertion arena are logically
    /// indistinguishable from unused capacity, and for random direct insertions
    /// these slots should be kept (because if there is not an internal slot at
    /// the needed index, it will have to push free slots up to that index).
    /// Advancing, however, has to iterate over all slots, so this function
    /// may be wanted in certain contexts.
    pub fn pop_free_end_slots(&mut self, num: usize) -> usize {
        let mut popped = 0usize;
        while popped < num {
            let Some(inx) = NonZeroUsize::new(self.m.len()) else {
                break;
            };
            if let Free = self.m.get(inx).unwrap() {
                self.m.pop();
                // bounded by the starting length
                popped = popped.wrapping_add(1);
            } else {
                break;
            }
        }
        popped
    }

    /// Directly returns a reference to the internal backing, for the purposes
    /// of accessing `ArenaBacking`-specific functions
    pub fn backing(&self) -> &B::Stack<DirectSlot<P, T>> {
        &self.m
    }

    // follow same logic as base arena in making this `unsafe`, `len` could be
    // messed up

    /// Directly returns a mutable reference to the internal backing, for the
    /// purposes of accessing `ArenaBacking`-specific functions
    ///
    /// # Safety
    ///
    /// The `DirectSlot` allocation state must not be modified, or else the
    /// entry length could be broken.
    pub unsafe fn backing_mut(&mut self) -> &mut B::Stack<DirectSlot<P, T>> {
        &mut self.m
    }

    /// Directly sets the number of allocated entries
    ///
    /// # Safety
    ///
    /// `len` must be kept equal to the number of allocated slots, or else other
    /// methods can panic or misbehave. See also
    /// [backing_mut](DirectArena::backing_mut).
    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }
}

impl<P: Ptr, T, B: ArenaBacking> Default for DirectArena<P, T, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> Index<Q> for DirectArena<P, T, B> {
    type Output = T;

    /// Returns a reference to the `T` pointed to by `inx`. Use
    /// [get](ArenaTrait::get) if invalid `Ptr`s need to be handled.
    ///
    /// # Panics
    ///
    /// If `inx` is invalid
    #[track_caller]
    fn index(&self, inx: Q) -> &T {
        let p: P = *inx.borrow();
        self.get(p)
            .expect("indexed `DirectArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> IndexMut<Q> for DirectArena<P, T, B> {
    /// Returns a mutable reference to the `T` pointed to by `inx`. Use
    /// [get_mut](ArenaTrait::get_mut) if invalid `Ptr`s need to be handled.
    ///
    /// # Panics
    ///
    /// If `inx` is invalid
    #[track_caller]
    fn index_mut(&mut self, inx: Q) -> &mut T {
        let p: P = *inx.borrow();
        self.get_mut(p)
            .expect("indexed `DirectArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T: fmt::Debug, B: ArenaBacking> fmt::Debug for DirectArena<P, T, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// Implemented if `T: Clone`.
impl<P: Ptr, T: Clone, B: ArenaBacking> Clone for DirectArena<P, T, B> {
    /// When an `DirectArena<P, T>` is cloned, the `P`s to an original `T` will
    /// initially be valid to the corresponding `T` in the cloned arena.
    /// Invalidations will continue independently, so the meaning of the `Ptr`
    /// with respect to the different arenas can diverge.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure, or if a
    /// [max_capacity](ArenaTrait::max_capacity) limit of the fresh `Self::new`
    /// arena prevents reaching the needed capacity. Use
    /// [clone_from_with](ArenaCloneFromWith::clone_from_with) if these need to
    /// be handled.
    ///
    /// # Unwind Safety
    ///
    /// If a `T::clone` panics, the partially cloned arena is dropped.
    #[track_caller]
    fn clone(&self) -> Self {
        let mut res = Self::new();
        res.clone_from_with(self, |_, t| t.clone())
            .expect("failed when cloning arena");
        res
    }

    /// Overwrites `self` (dropping all preexisting `T` and overwriting the
    /// generation counter) with a clone of `source`. Has the validity cloning
    /// property of arena cloning, but now the capacity of `self` is reused.
    /// Allocations may happen if the capacity of `self` is not large enough.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure, or if a
    /// [max_capacity](ArenaTrait::max_capacity) limit of `self` prevents
    /// reaching the needed capacity. Use
    /// [clone_from_with](ArenaCloneFromWith::clone_from_with) if these need to
    /// be handled.
    ///
    /// # Unwind Safety
    ///
    /// A panicking `T::clone` or `T::drop` leaves `self` with the same
    /// guarantees as
    /// [clone_from_with](ArenaCloneFromWith::clone_from_with).
    #[track_caller]
    fn clone_from(&mut self, source: &Self) {
        self.clone_from_with(source, |_, t| t.clone())
            .expect("failed when cloning arena");
    }
}

impl<P: Ptr, T, B: ArenaBacking> SetMaxCapacity for DirectArena<P, T, B>
where
    <B as ArenaBacking>::Stack<DirectSlot<P, T>>: SetMaxCapacity,
{
    fn set_max_capacity(&mut self, max_capacity: usize) -> Result<(), MaxCapacityReductionError> {
        // follow `reallocate_min_capacity`
        let excess = self.m.len().saturating_sub(max_capacity);
        self.pop_free_end_slots(excess);
        self.m.set_max_capacity(max_capacity)
    }
}
