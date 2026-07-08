use core::{num::NonZeroUsize, slice::GetDisjointMutError};

use crate::fundamental::AllocError;

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
/// This is not ever intended to support slices and zero indexing (besides
/// one-indexing being horrible for this, there may be discontiguous
/// implementors). Implementors are currently not required to implement ZST
/// support either (but must panic on construction).
///
/// # Safety
///
/// These conditions must hold:
/// - `self.is_empty() == (self.len() == 0)`
/// - `self.len() <= self.capacity()`
/// - After calling `ensure_capacity` and getting Ok, `self.capacity() >=
///   min_capacity`
/// - Must act consistently as a stack should with regards to pushes, pops, and
///   accesses
///
/// `self.capacity_limit` is a hint with respect to downstream assumptions and
/// can be anything (because of the potential to modify limits with some
/// implementations, but they should try to be sane)
pub unsafe trait NonZeroInxGenericStack<T> {
    fn new() -> Self;

    /// The number of elements in the stack
    fn len(&self) -> usize;

    /// If `self.len() == 0`
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    // I would consider things like `fn is_full(&self) -> bool {self.len() ==
    // self.capacity_limit()}`, but there is still too high of a chance for assuming
    // alternatives like `self.len() == self.capacity()` based on context, just have
    // these three functions and the specially controllable case `clear_and_shrink`
    // (not `shrink_to_fit`, replace that with just
    // `self.ensure_capacity(self.len())`) only for interacting with capacity

    /// Returns the existing capacity, in elements, already in memory for
    /// `self`. `self.capacity() - self.len()` elements can be inserted before
    /// reallocation needs to happen.
    fn capacity(&self) -> usize;

    /// Returns if there is a known maximum allowed capacity for `self`. Types
    /// backed by an array, for instance, would return the maximum number of
    /// elements they could ever hold (and should set capacity to that
    /// constant). Dynamically allocated types can also return a maximum, if
    /// they internally limit themselves in order to bound memory. But most
    /// dynamically allocated types would return `None` to indicate that
    /// they will try to increase in length until memory allocation failure.
    fn capacity_limit(&self) -> Option<usize>;

    // We decide not to add a "try_" prefix, since in any universe allocation things
    // are fallible. Also, there are concievable defragmentation cases where an
    // implementor and allocator would make `min_capacity == self.len()` not a
    // no-op.

    /// Reallocates in order to try and change `self.capacity()` to have a lower
    /// bound of `min_capacity` elements of capacity. This can act both to
    /// grow and shrink the memory allocation. If `min_capacity < self.len()`,
    /// this will never remove elements and will always result in a capacity of
    /// at least `self.len()`. If `min_capacity >= self.len()`, it can still
    /// always result in a higher capacity than `min_capacity` depending on
    /// implementor choices and allocator behavior. Can return an allocation
    /// error depending on implementor choice and allocator behavior, on both
    /// growing, `min_capacity == self.len()`, and shrinking.
    ///
    /// `self.ensure_capacity(self.len())` is a replacement for the typical
    /// `shrink_to_fit` function. We have limited manual capacity modification
    /// to this single function, because classically it was easy to assume that
    /// things like `Vec::reserve_exact` actually would set capacity to an exact
    /// value, when in fact they could reserve more than the requested capacity.
    /// Some allocator designs absolutely require being able to give back more
    /// than requested. The only exception is `clear_and_shrink`, for which a
    /// guaranteed zero capacity special case is usually naturally available or
    /// can be special cased.
    fn ensure_capacity(&mut self, min_capacity: usize) -> Result<(), AllocError>;

    /// Pushes an element to the end such that its index is
    /// `NonZeroUsize::new_unchecked(self.len())` immediately _after_ this call.
    /// Returns the index to the element and a mutable reference to it on
    /// success, else returns the element if there was no remaining capacity.
    fn push(&mut self, t: T) -> Result<(NonZeroUsize, &mut T), T>;

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

    /// Clears all elements, dropping all `T`
    fn clear(&mut self);

    /// Runs `self.clear()` and shrinks the capacity to zero.
    fn clear_and_shrink(&mut self);
}
