use core::{num::NonZeroUsize, slice::GetDisjointMutError};

use crate::{AllocError, NotWithinCapacityError, ReallocationError};

/*
Regarding design choices, we would have a collision between two approaches: approach (1) where we want to use the full allocation given back by the allocator (some allocator interfaces can give back more than requested, because the allocator's blocks had extra space that would otherwise be unused, in fact the base `Vec` type practically _must_ accept extra capacity or else it needs to have another field added, this and avoiding confusions regarding this is ultimately why we have the `reallocate_min_capacity` function that can only guarantee a lower bound), and approach (2) where we want to rely on a hard maximum capacity and thus exact maximum length of elements (and there would be an especially dangerous bug if `reallocate_min_capacity` resulted in a larger capacity and thus actual length limit than the limit, and this would only show up occasionally). It would be annoying in (2) that the "limit" isn't actually a hard limit we can rely on at all and we would still need a further limit.

If we added a separate `len_limit` with a limit directly on length that operated independently of capacity, it would break the assumption that `self.capacity() - self.len()` elements can be safely inserted, and some downstream user would inevitably run into this.

What we have to do is have a single `reallocate_min_capacity` function (see its documentation) which forces users to consider exactly what they want and bring attention to edge cases. Then we have a `max_capacity` capacity function that returns a hard max capacity if and only if the type supports the ability to limit capacity to an exact maximum. We also have `with_min_capacity` (needed by fixed heap back types to work without OOB stuff), and we assume that the `new` function can always be implemented infallibly (it is always the case as far as I know that a nonallocating niche can be defined).

We do not have a "clear_and_shrink" function or something that might imply reducing capacity to zero, this is not possible with certain types like arrays without adding on fields that are unnecessary, also it is another edge case colliding with the minimal behavior which should be to request floors on capacity and have a max_capacity that is set OOB only by types that can support it exactly.

Some collections have `try_*` functions for reasons unrelated to capacity, we use `*_within_capacity` to completely avoid ambiguity.

"reallocate_min_capacity" is the best name I could come up with, the fact that it is a minimum must be encoded in the name. Maybe I should have named it "reallocate_with_min_capacity" but I think we make a terseness exception, also the "min" could be as "minimize" to reference its ability to shrink. We don't need "try_*" since in any universe allocation is infallible and allocator v2 does this. Note there are concievable defragmentation cases where an implementor and allocator would make `min_capacity == self.len()` not a no-op.

I would consider things like `fn is_full(&self) -> bool {self.len() == self.max_capacity()}`, but there is still too high of a chance for assuming alternatives like `self.len() == self.capacity()` based on context, minimize the functions we have access to

Regarding entry methods (this is talking generally, the index logic becomes more critical with `Ptr`s in the analogous arena insertion methods, I have decided to mirror those higher level methods even though the index at this level can be calculated relatively easily and deterministically):
    - Some downstream uses must know the index they will be inserted into, it helps with preventing bugs (and especially with our nonzero indexing scheme) to be able to have the entry type calculate this for them. And the entry type owning the structure during this helps prevent intermediate improper invalidation bugs (note also that we don't have a method on the entry struct to get an immutable reference of the main struct, we wouldn't want usage of the still invalid index).
    - The index can be used for other invariants, and if construction fails users would want to be able to cancel the insertion. Note that even in regular practice, obvious signatures like `fn insert_method(&mut self, t: T) -> Result<..., T>;` that return back the `T` on error tend to be problematic even when we aren't directly encountering the other bullet points. They encourage bad recovery strategies and bugs in error cases where something isn't restored properly because it had to be set before the method is called. They are annoying when chaining up through the analogous methods on arenas, chain arenas, etc. They are also annoying when writing signatures to return possible error cases. Instead, we make the non-entry methods for common use cases just drop the `T` internally and we get to return a proper error. Any more complicated case should just jump straight to the full on entry methods
    - Sometimes `T` has to be specially constructed at insertion time and depends on the known index as an input for its construction, but also the `T` construction itself can be fallible and wants to cancel insertion. This rules out many intermediate designs.
*/

// this is an obnoxiously long name but it is meant to be glob-import-able

/// Dropping the struct cancels the insertion
#[must_use]
pub trait NonZeroInxGenericStackPushEntryTrait<'a, T> {
    /// The index at which the element will be, if inserted. This is always
    fn inx(&self) -> NonZeroUsize;
    fn push(self, t: T);
}

/// A trait for `Vec`-like collection structs that are one-indexed by
/// `NonZeroUsize` instead of zero-indexed.
///
/// # Note
///
/// This is intended for the backing of arena-like data structures that pass
/// out independent indexes. It is important that these indexes can be a
/// `NonZero` integer for niche optimization purposes (e.x. this stops aligned
/// `Option<impl triple_arena::Ptr>` from unnecessarily exploding the memory
/// footprint).
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
/// - After calling `reallocate_min_capacity` and getting Ok, `self.capacity()
///   >= min_capacity`
/// - Must act consistently as a stack should with regards to pushes, pops,
///   `self.capacity()`, and accesses
/// - See the functions for other requirements
///
/// It is implied that `reallocate_min_capacity` must fail if `max_capacity` is
/// set and the requested `min_capacity` is greater than it. On success, it must
/// also make sure that capacity never ever exceeds max capacity (as some
/// allocators can return more than requested, it may require a virtualized
/// capacity so that `self.capacity()` and other stack behavior is different
/// than the actual capacity with respect to allocation details). Types that
/// cannot guarantee this should instead return `None` from `self.max_capacity`.
pub unsafe trait NonZeroInxGenericStack<T>: Sized {
    type PushEntry<'a>: NonZeroInxGenericStackPushEntryTrait<'a, T>
    where
        Self: 'a;

    /// Creates an empty stack, which may have any capacity to start with
    fn new() -> Self;

    /// Creates an empty stack with a minimum capacity of at least
    /// `min_capacity`. Returns an error upon allocation failure.
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
    /// [NonZeroInxGenericStack::reallocate_min_capacity] behaves strictly to
    /// avoid exceeding this limit). But most dynamically allocated types
    /// would return `None` to indicate that they will try to increase in
    /// length until memory allocation failure.
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
    /// success, else returns the element if there was no remaining capacity.
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

    /// The same as [NonZeroInxGenericStack::push_within_capacity], except that
    /// it will automatically reallocate to try and extend the capacity upon
    /// running out, and returns the element upon an allocation error or using
    /// up [NonZeroInxGenericStack::max_capacity].
    fn push_reallocating(&mut self, t: T) -> Result<(NonZeroUsize, &mut T), ReallocationError> {
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
        self.push_within_capacity(t)
            .map_err(|NotWithinCapacityError| ReallocationError::AllocError)
    }

    /// The same as [NonZeroInxGenericStack::push_reallocating], except that
    /// this panics upon an allocation error or using up
    /// [NonZeroInxGenericStack::max_capacity].
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure when needing to extend
    /// capacity
    #[track_caller]
    fn push(&mut self, t: T) -> (NonZeroUsize, &mut T) {
        // TODO it would be nice if Rust had a way to mark functions such that
        // downstream uses would warn if downstream assertions (something like
        // `clippy::cast_possible_wrap` but not just lexical and something more general
        // that guards against other fallible things in the language)
        self.push_reallocating(t)
            .expect("`NonZeroInxGenericStack::push_reallocating` failed")
    }

    /// If capacity is available, a push entry for pushing `t` onto the
    /// stack is returned. Returns an error if there was no available capacity.
    fn entry_push_within_capacity(&mut self)
    -> Result<Self::PushEntry<'_>, NotWithinCapacityError>;

    /// Returns a push entry, reallocating if necessary and returning an
    /// error if reallocation failed or if
    /// [NonZeroInxGenericStack::max_capacity] is used up. Be aware that any
    /// reallocation happens upon calling this method, and the affects
    /// remain even if pushing onto the stack is cancelled.
    fn entry_push_reallocating(&mut self) -> Result<Self::PushEntry<'_>, ReallocationError> {
        if self.len() == self.capacity() {
            // REF(better_reallocation)

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
        self.entry_push_within_capacity()
            .map_err(|NotWithinCapacityError| ReallocationError::AllocError)
    }

    /// Returns an insertion entry, panicking if an allocation error occurs or
    /// if [NonZeroInxGenericStack::max_capacity] is used up.
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
/// traits like [crate::utils::traits::NonZeroInxGenericStack] and
/// [crate::traits::ArenaTrait] that have a `max_capacity` function.
pub trait SetMaxCapacity {
    /// Changes the maximum allowed capacity to `max_capacity`, returning `None`
    /// if and only if `max_capacity < self.capacity()`.
    ///
    /// The max capacity can be set to `usize::MAX`, but the allocation
    /// functions will usually fail before the capacity can actually reach the
    /// max capacity. Additionally, some fixed capacity types have a maximum
    /// achievable capacity set upon construction. This function is only
    /// fallible to prevent violating the invariant `self.capacity() <=
    /// self.max_capacity()` at runtime, and cannot be relied upon for
    /// reallocation infallibility.
    #[must_use]
    fn set_max_capacity(&mut self, max_capacity: usize) -> Option<()>;
}
