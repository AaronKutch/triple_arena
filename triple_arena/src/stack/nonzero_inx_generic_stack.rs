use core::{num::NonZeroUsize, slice::GetDisjointMutError};

use crate::errors::{
    AllocError, MaxCapacityReductionError, NotWithinCapacityError, ReallocationError,
};

/*
Regarding design choices, we would have a collision between two approaches: approach (1) where we want to use the full allocation given back by the allocator (some allocator interfaces can give back more than requested, because the allocator's blocks had extra space that would otherwise be unused, in fact the base `Vec` type practically _must_ accept extra capacity or else it needs to have another field added, this and avoiding confusions regarding this is ultimately why we have the `reallocate_min_capacity` function that can only guarantee a lower bound), and approach (2) where we want to rely on a hard maximum capacity and thus exact maximum length of elements (and there would be an especially dangerous bug if `reallocate_min_capacity` resulted in a larger capacity and thus actual length limit than the limit, and this would only show up occasionally). It would be annoying in (2) that the "limit" isn't actually a hard limit we can rely on at all and we would still need a further limit.

If we added a separate `len_limit` with a limit directly on length that operated independently of capacity, it would break the assumption that `self.capacity() - self.len()` elements can be safely inserted, and some downstream user would inevitably run into this.

What we have to do is have a single `reallocate_min_capacity` function (see its documentation) which forces users to consider exactly what they want and bring attention to edge cases. Then we have a `max_capacity` capacity function that returns a hard max capacity if and only if the type supports the ability to limit capacity to an exact maximum. We also have `with_min_capacity` (needed by fixed heap back types to work without OOB stuff), and we assume that the `new` function can always be implemented infallibly (it is always the case as far as I know that a nonallocating niche can be defined).

We do not have a "clear_and_shrink" function or something that might imply reducing capacity to zero, this is not possible with certain types like arrays without adding on fields that are unnecessary, also it is another edge case colliding with the minimal behavior which should be to request floors on capacity and have a max_capacity that is set OOB only by types that can support it exactly.

Some collections have `try_*` functions for reasons unrelated to capacity, we use `*_within_capacity` to completely avoid ambiguity.

"reallocate_min_capacity" is the best name I could come up with, the fact that it is a minimum must be encoded in the name. Maybe I should have named it "reallocate_with_min_capacity" but I think we make a terseness exception, also the "min" could be as "minimize" to reference its ability to shrink. We don't need "try_*" since in any universe allocation is infallible and allocator v2 does this. Note there are concievable defragmentation cases where an implementor and allocator would make `min_capacity == self.len()` not a no-op.

I would consider things like `fn is_full(&self) -> bool {self.len() == self.max_capacity()}`, but there is still too high of a chance for assuming alternatives like `self.len() == self.capacity()` based on context, minimize the functions we have access to

I added the invariant `self.capacity() <= self.max_capacity()` which will prevent some logical transitivity bugs people may run into. It would be nice to be able to assume that the length cannot possibly be longer than the current "max capacity". The only seemingly strange consequence of this is that, for `with_min_capacity` to not have to return an error, it needs to initialize with a nonzero maximum capacity. However, `with_min_capacity` would have to return an error if requested with any nonzero value on a limitable type, unless it started with a nonzero maximum capacity anyways, and for limited fixed capacity types `with_min_capacity` would be unusable and we would need OOB methods for it. We decide to also say that `new` can start with any max capacity limit and generics have to be mindful of that.

The original idea with `set_max_capacity` was that it would be mandated that it would fail if and only if the requested max capacity was less than the existing `self.capacity()`. `reallocate_min_capacity` would have to be called first to reduce `self.capacity()` before the max capacity could be reduced. However, dynamically limited types like `NonZeroInxLimitedVec` actually support reducing down to `self.len()` if we accepted also changing `self.capacity()` itself during `set_max_capacity`. If we wanted to deterministically set an exact limit, `reallocate_min_capacity` may prevent us by always giving us too much capacity. Because of this and the implication that a direct limiter to capacity is being changed, we allowed `set_max_capacity` to also change `self.capacity()`.

Regarding entry methods (this is talking generally, the index logic becomes more critical with `Ptr`s in the analogous arena insertion methods, I have decided to mirror those higher level methods even though the index at this level can be calculated relatively easily and deterministically):
    - Some downstream uses must know the index they will be inserted into, it helps with preventing bugs (and especially with our nonzero indexing scheme) to be able to have the entry type calculate this for them. And the entry type owning the structure during this helps prevent intermediate improper invalidation bugs (note also that we don't have a method on the entry struct to get an immutable reference of the main struct, we wouldn't want usage of the still invalid index).
    - The index can be used for other invariants, and if construction fails users would want to be able to cancel the insertion. Note that even in regular practice, obvious signatures like `fn insert_method(&mut self, t: T) -> Result<..., T>;` that return back the `T` on error tend to be problematic even when we aren't directly encountering the other bullet points. They encourage bad recovery strategies and bugs in error cases where something isn't restored properly because it had to be set before the method is called. They are annoying when chaining up through the analogous methods on arenas, chain arenas, etc. They are also annoying when writing signatures to return possible error cases. Instead, we make the non-entry methods for common use cases just drop the `T` internally and we get to return a proper error. Any more complicated case should just jump straight to the full on entry methods
    - Sometimes `T` has to be specially constructed at insertion time and depends on the known index as an input for its construction, but also the `T` construction itself can be fallible and wants to cancel insertion. This rules out many intermediate designs.
*/

// this is an obnoxiously long name but it is meant to be glob-import-able

/// Dropping the struct cancels the insertion
#[must_use]
pub trait NonZeroInxGenericStackPushEntryTrait<'a, T> {
    /// The index at which the element will be, if inserted. Because of the
    /// one-indexing this is always `NonZeroUsize::new_unchecked(self.len() +
    /// 1)` based on the `self.len()` of the stack right before the entry was
    /// created, equivalently it is the `self.len()` immediately after a
    /// successful [push](NonZeroInxGenericStackPushEntryTrait::push).
    fn inx(&self) -> NonZeroUsize;

    /// Pushes `t` onto the stack at [inx](
    /// NonZeroInxGenericStackPushEntryTrait::inx)
    fn push(self, t: T);
}

// the `Option<impl triple_arena::Ptr>` is on purpose in case we extract this to
// a different crate
/// A trait for `Vec`-like collection structs that are one-indexed by
/// `NonZeroUsize` instead of zero-indexed.
///
/// # Note
///
/// This is intended for the backing of arena-like data structures that pass
/// out independent indexes. It is important that these indexes can be a
/// `NonZero` integer for niche optimization purposes (e.x. this stops aligned
/// `Option<impl triple_arena::Ptr>` from unnecessarily exploding the memory
/// footprint everywhere it is used).
///
/// This will never support slices and zero indexing (Besides
/// one-indexing being horrible for this, there may be discontiguous
/// implementors. A separate trait would be used).
///
/// # Safety
///
/// These conditions must hold:
/// - `self.is_empty() == (self.len() == 0)`
/// - `self.len() <= self.capacity()`
/// - `self.capacity() <= self.max_capacity()` if set
/// - `self.capacity() >= min_capacity` must hold after succeeding with
///   `reallocate_min_capacity`
/// - Must act consistently as a stack should with regards to pushes, pops,
///   `self.capacity()`, and accesses
/// - See the functions for other requirements
/// - The limit for slices where the total size in bytes cannot exceed
///   `isize::MAX`
///
/// It is implied that `reallocate_min_capacity` must fail if `max_capacity` is
/// set and the requested `min_capacity` is greater than it. On success, it must
/// also make sure that capacity never ever exceeds max capacity (as some
/// allocators can return more than requested, it may require a virtualized
/// capacity so that `self.capacity()` and other stack behavior is different
/// than the actual capacity with respect to allocation details). Types that
/// cannot guarantee this should instead return `None` from `self.max_capacity`.
pub unsafe trait NonZeroInxGenericStack<T>: Sized {
    /// The type returned by the `entry_push_*` functions
    type PushEntry<'a>: NonZeroInxGenericStackPushEntryTrait<'a, T>
    where
        Self: 'a;

    /// Creates an empty stack, which may have any capacity and max capacity
    /// limit to start with
    fn new() -> Self;

    /// Creates an empty stack with a minimum capacity of at least
    /// `min_capacity`. The max capacity, if set, is also initialized to at
    /// least the capacity of the returned stack. Returns an error upon
    /// allocation failure.
    ///
    /// In most cases [new](NonZeroInxGenericStack::new) followed by
    /// [reallocate_min_capacity](NonZeroInxGenericStack::reallocate_min_capacity) would be sufficient,
    /// but this function needs to exist for certain fixed capacity structures
    /// that can only have their capacity set once at construction time.
    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError>;

    /// Returns the existing capacity, in elements, already in memory for
    /// `self`. `self.capacity() - self.len()` elements can be inserted before
    /// reallocation needs to happen.
    fn capacity(&self) -> usize;

    /// Returns if there is an exact maximum allowed capacity for `self`. Types
    /// backed by an array, for instance, would return the maximum number of
    /// elements they could ever hold (and should hold `self.capacity` to that
    /// constant). Dynamically allocated types can also return a maximum, if
    /// they internally limit themselves in order to bound memory (and their
    /// [reallocate_min_capacity](NonZeroInxGenericStack::reallocate_min_capacity) behaves strictly to
    /// avoid `self.capacity()` exceeding this limit). But most dynamically
    /// allocated types would return `None` to indicate that they will try
    /// to increase in length until memory allocation failure. If set,
    /// `self.capacity() <= self.max_capacity()` is always true.
    fn max_capacity(&self) -> Option<usize>;

    /// Reallocates in order to try and change `self.capacity()` to have a lower
    /// bound of `min_capacity` elements of capacity. This can act both to
    /// grow and shrink the memory allocation. If `min_capacity < self.len()`,
    /// this will never remove elements and will always result in a capacity of
    /// at least `self.len()`. Can return an allocation error in all cases
    /// depending on implementor choice and allocator behavior, even
    /// `min_capacity <= self.capacity()`.
    ///
    /// `self.reallocate_min_capacity(self.len())` is a replacement for the
    /// typical `shrink_to_fit` function. We have limited manual capacity
    /// modification to this single function, because classically it was
    /// easy to assume that things like `Vec::reserve_exact` actually would
    /// set capacity to an exact value, when in fact they could reserve more
    /// than the requested capacity. Some implementors of this trait
    /// combined with certain allocator designs absolutely require being able to
    /// give back more than requested.
    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), ReallocationError>;

    /// The number of elements in the stack
    fn len(&self) -> usize;

    /// If `self.len() == 0`
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Pushes an element to the end such that its index is
    /// `NonZeroUsize::new_unchecked(self.len())` immediately _after_ this call.
    /// Returns the index to the element and a mutable reference to it on
    /// success. If there was no remaining capacity, `t` is dropped and an error
    /// is returned (use
    /// [entry_push_within_capacity](
    /// NonZeroInxGenericStack::entry_push_within_capacity) instead if `t` needs
    /// to be recovered).
    fn push_within_capacity(
        &mut self,
        t: T,
    ) -> Result<(NonZeroUsize, &mut T), NotWithinCapacityError> {
        let entry = self.entry_push_within_capacity()?;
        let inx = entry.inx();
        entry.push(t);
        // Safety: this is accessing the element just after it was inserted, and using
        // the correct index
        unsafe { Ok((inx, self.get_unchecked_mut(inx))) }
    }

    /// The same as
    /// [push_within_capacity](NonZeroInxGenericStack::push_within_capacity),
    /// except that it will automatically reallocate to try and extend the
    /// capacity upon running out. `t` is dropped upon an allocation
    /// error or using up
    /// [max_capacity](NonZeroInxGenericStack::max_capacity).
    fn push_reallocating(&mut self, t: T) -> Result<(NonZeroUsize, &mut T), ReallocationError> {
        let entry = self.entry_push_reallocating()?;
        let inx = entry.inx();
        entry.push(t);
        // Safety: this is accessing the element just after it was inserted, and using
        // the correct index
        unsafe { Ok((inx, self.get_unchecked_mut(inx))) }
    }

    /// The same as
    /// [push_reallocating](NonZeroInxGenericStack::push_reallocating), except
    /// that this panics upon an allocation error or using up
    /// [max_capacity](NonZeroInxGenericStack::max_capacity).
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure when needing to extend
    /// capacity, or if `self.len()` is at the maximum capacity.
    #[track_caller]
    fn push(&mut self, t: T) -> (NonZeroUsize, &mut T) {
        // TODO it would be nice if Rust had a way to mark functions such that
        // downstream uses would warn if downstream assertions (something like
        // `clippy::cast_possible_wrap` but not just lexical and something more general
        // that guards against other fallible things in the language)
        self.push_reallocating(t)
            .expect("`NonZeroInxGenericStack::push_reallocating` failed")
    }

    /// If capacity is available, a push entry for pushing an element onto the
    /// stack is returned. Returns an error if there was no available capacity.
    fn entry_push_within_capacity(&mut self)
    -> Result<Self::PushEntry<'_>, NotWithinCapacityError>;

    /// Returns a push entry, reallocating if necessary and returning an
    /// error if reallocation failed or if
    /// [max_capacity](NonZeroInxGenericStack::max_capacity) is used up. Be
    /// aware that any reallocation happens upon calling this method, and the
    /// effects remain even if pushing onto the stack is cancelled.
    fn entry_push_reallocating(&mut self) -> Result<Self::PushEntry<'_>, ReallocationError> {
        if self.len() == self.capacity() {
            // TODO REF(better_reallocation) may want something more sophisticated, see https://github.com/rust-lang/rust/issues/29931

            // follow `RawVec`
            let mut next = if self.capacity() == 0 {
                if size_of::<T>() <= 1024 { 4 } else { 1 }
            } else {
                self.capacity().saturating_mul(2)
            };
            // but be able to saturate max capacity before causing an error
            if let Some(max_capacity) = self.max_capacity() {
                next = next.min(max_capacity);
            }
            if next <= self.capacity() {
                // the max capacity is limiting us
                return Err(ReallocationError::BeyondMaxCapacity);
            }
            self.reallocate_min_capacity(next)?;
        }
        // an error shouldn't happen, but if it does it is logically the allocator's
        // fault
        self.entry_push_within_capacity()
            .map_err(|NotWithinCapacityError| ReallocationError::AllocError)
    }

    /// Returns an insertion entry, panicking if an allocation error occurs or
    /// if [max_capacity](NonZeroInxGenericStack::max_capacity) is used up.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure when needing to extend
    /// capacity, or if `self.len()` is at the maximum capacity.
    #[track_caller]
    fn entry_push(&mut self) -> Self::PushEntry<'_> {
        self.entry_push_reallocating()
            .expect("`NonZeroInxGenericStack::entry_push_reallocating` failed")
    }

    /// Gets a reference to an element without doing checks
    ///
    /// # Safety
    ///
    /// Must not be called with `inx.get() > self.len()`
    unsafe fn get_unchecked(&self, inx: NonZeroUsize) -> &T;

    /// Gets a reference to an element, returning `None` if `inx.get() >
    /// self.len()`
    fn get(&self, inx: NonZeroUsize) -> Option<&T> {
        if inx.get() > self.len() {
            None
        } else {
            // Safety: we checked that we are in bounds
            unsafe { Some(self.get_unchecked(inx)) }
        }
    }

    /// Gets a mutable reference to an element without doing checks
    ///
    /// # Safety
    ///
    /// Must not be called with `inx.get() > self.len()`
    unsafe fn get_unchecked_mut(&mut self, inx: NonZeroUsize) -> &mut T;

    /// Gets a mutable reference to an element, returning `None` if `inx.get() >
    /// self.len()`
    fn get_mut(&mut self, inx: NonZeroUsize) -> Option<&mut T> {
        if inx.get() > self.len() {
            None
        } else {
            // Safety: we checked that we are in bounds
            unsafe { Some(self.get_unchecked_mut(inx)) }
        }
    }

    /// Returns mutable references without doing checks
    ///
    /// # Safety
    ///
    /// Must not be called with overlapping or out-of-bounds indices
    unsafe fn get_disjoint_unchecked_mut<const N: usize>(
        &mut self,
        indices: [NonZeroUsize; N],
    ) -> [&mut T; N];

    /// Returns mutable references to many indexes at once, in order. Returns an
    /// error if any indexes overlap or are out of bounds.
    ///
    /// This method does a `O(n^2)` check for overlapping, be careful when
    /// passing in many indices
    fn get_disjoint_mut<const N: usize>(
        &mut self,
        indices: [NonZeroUsize; N],
    ) -> Result<[&mut T; N], GetDisjointMutError> {
        // Adapted from the Rust slice source code. Normally I would want to optimize
        // for a common case of passing indexes in an ordered fashion so that the
        // comparisons could be `O(n)`, but in the case of arenas this makes more sense.
        // We have the unchecked variation anyways
        for (i, idx) in indices.iter().enumerate() {
            // only safe with one-indexing
            if idx.get() > self.len() {
                return Err(GetDisjointMutError::IndexOutOfBounds);
            }
            for idx2 in &indices[..i] {
                if *idx == *idx2 {
                    return Err(GetDisjointMutError::OverlappingIndices);
                }
            }
        }

        // Safety: we checked above that all indices are disjunct and in bounds.
        unsafe { Ok(self.get_disjoint_unchecked_mut(indices)) }
    }

    /// Pops off the element at index `self.len()`, unless `self.is_empty()` in
    /// which case this returns `None`
    fn pop(&mut self) -> Option<T>;

    /// Clears all elements, dropping all `T`. This has no effect on allocated
    /// capacity.
    fn clear(&mut self);
}

/// A trait for types that have a settable maximum capacity, complementing
/// traits like
/// [NonZeroInxGenericStack](crate::utils::traits::NonZeroInxGenericStack) and
/// [ArenaTrait](crate::traits::ArenaTrait) that have a `max_capacity` function.
pub trait SetMaxCapacity {
    /// Changes the maximum allowed capacity to `max_capacity` and modifies
    /// `self.capacity()` in some cases. Always allows increasing the maximum
    /// capacity to any `usize` value (however, actually growing the capacity to
    /// try and reach this limit may fail from allocation errors). This also
    /// always allows decreasing the maximum capacity down to the current
    /// `self.capacity()`. If reducing the maximum capacity below the existing
    /// `self.capacity()`, however, implementations may choose to mutate and
    /// reduce `self.capacity()` to equal the `max_capacity` (using a virtual
    /// capacity that is different from an internal capacity, such that
    /// reallocation is not needed or used). Or, implementations may need to
    /// return an error from reducing the capacity depending on internal details
    /// (and invariants imply that all implementations must return an error if
    /// requesting a `max_capacity` less than `self.len()`). It is also possible
    /// for `self.capacity()` to increase from increasing the maximum capacity.
    ///
    /// To reiterate, there can be 3 different values at play:
    /// - The logical capacity according to `self.capacity()`, which is what
    ///   `self.len()` and other logical element operations are limited by.
    /// - A hidden internal allocated capacity (which can be separate from the
    ///   logical capacity in some implementations because some allocators can
    ///   allocate more than was requested, but an exact `self.capacity()` is
    ///   desired for logical determinism reasons).
    /// - The `self.max_capacity()`, which is not either of the previous two and
    ///   is simply a _limit_ on `self.capacity()` and a way to directly control
    ///   the exact value of `self.capacity()` when the `*_min_capacity`
    ///   functions are only able to establish a floor. In dynamic limited
    ///   capacity types, we want to be able to set an arbitrary limit that does
    ///   not require having all of the capacity physically allocated up front.
    ///   The current internal allocated capacity, and the logical capacity
    ///   within it, should be the only things that require a live memory
    ///   impact.
    ///
    /// In most circumstances, users should just set the max capacity once at
    /// creation, and don't have to worry about the decreasing max_capacity
    /// cases. Most structures can start with zero logical capacity and zero max
    /// capacity with their `new` functions, such that a `new` function
    /// followed by calling `set_max_capacity`, further followed by
    /// `reallocate_min_capacity`, usually accomplishes this with only one
    /// actually fallible point (since we require that increasing the maximum
    /// capacity should be infallible).
    ///
    /// If reducing the max capacity, the internal allocated capacity will never
    /// change from calling this function, and memory usage will not actually be
    /// reduced until `reallocate_min_capacity(self.capacity())` is called
    /// afterwards.
    ///
    /// If `self.capacity()` was limited by the maximum capacity, it is possible
    /// for `self.capacity()` to actually increase by this method if the
    /// implementation had available internal allocation capacity (this
    /// happens without actual change to the internal allocated capacity,
    /// usually because `self.capacity()` is calculated as the minimum of
    /// the internal allocated capacity and the max capacity, and if the max
    /// capacity was the limiting factor, then increasing the max capacity
    /// also increases the logical capacity).
    ///
    /// The max capacity can be set to `usize::MAX`, but the allocation
    /// functions will usually fail before the capacity can actually reach the
    /// max capacity. Additionally, some fixed capacity types have a maximum
    /// achievable capacity set upon construction. This function is only
    /// fallible to prevent violating the invariant `self.capacity() <=
    /// self.max_capacity()` at runtime, and does not warn for fixed width
    /// unreachabilities and cannot be relied upon for reallocation
    /// infallibility.
    ///
    /// This is usually an `O(1)` operation, but if `self.capacity()` decreases,
    /// it can be an `O(n)` operation (not because it reallocates, but
    /// because of things like freelist canonicalization in order to achieve
    /// the lowest possible capacity).
    fn set_max_capacity(&mut self, max_capacity: usize) -> Result<(), MaxCapacityReductionError>;
}
