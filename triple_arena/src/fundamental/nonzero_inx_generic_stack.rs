use core::{num::NonZeroUsize, slice::GetDisjointMutError};

use crate::fundamental::AllocError;

/*
Regarding design choices, we would have a collision between two approaches: approach (1) where we want to use the full allocation given back by the allocator (some allocator interfaces can give back more than requested, because the allocator's blocks had extra space that would otherwise be unused, in fact the base `Vec` type practically _must_ accept extra capacity or else it needs to have another field added, this and avoiding confusions regarding this is ultimately why we have the `reallocate_min_capacity` function that can only guarantee a lower bound), and approach (2) where we want to rely on a hard maximum capacity and thus exact maximum length of elements (and there would be an especially dangerous bug if `reallocate_min_capacity` resulted in a larger capacity and thus actual length limit than the limit, and this would only show up occasionally). It would be annoying in (2) that the "limit" isn't actually a hard limit we can rely on at all and we would still need a further limit.

If we added a separate `len_limit` with a limit directly on length that operated independently of capacity, it would break the assumption that `self.capacity() - self.len()` elements can be safely inserted, and some downstream user would inevitably run into this.

What we have to do is have a single `reallocate_min_capacity` function (see its documentation) which forces users to consider exactly what they want and bring attention to edge cases. Then we have a `max_capacity` capacity function that returns a hard max capacity if and only if the type supports the ability to limit capacity to an exact maximum.

We do not have a "clear_and_shrink" function or something that might imply reducing capacity to zero, this is not possible with certain types like arrays without adding on fields that are unnecessary, also it is another edge case colliding with the minimal behavior which should be to request floors on capacity and have a max_capacity that is set OOB only by types that can support it exactly.

Some collections have `try_*` functions for reasons unrelated to capacity, we use `push_within_capacity` to completely avoid ambiguity.

"reallocate_min_capacity" is the best name I could come up with, the fact that it is a minimum must be encoded in the name. Maybe I should have named it "reallocate_with_min_capacity" but I think we make a terseness exception, also the "min" could be as "minimize". We don't need "try_*" on some of theses since in any universe allocation is infallible and allocator v2 does this. Note there are concievable defragmentation cases where an implementor and allocator would make `min_capacity == self.len()` not a no-op.

I would consider things like `fn is_full(&self) -> bool {self.len() == self.max_capacity()}`, but there is still too high of a chance for assuming alternatives like `self.len() == self.capacity()` based on context, minimize the functions we have access to

*/

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
pub unsafe trait NonZeroInxGenericStack<T> {
    /// Creates an empty stack, which may have any capacity to start with
    fn new() -> Self;

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
    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), AllocError>;

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
    fn push_within_capacity(&mut self, t: T) -> Result<(NonZeroUsize, &mut T), T>;

    /// The same as [NonZeroInxGenericStack::push_within_capacity], except that
    /// it will automatically reallocate to try and extend the capacity upon
    /// running out, and returns the element upon an allocation error or using
    /// up [NonZeroInxGenericStack::max_capacity].
    fn push_reallocating(&mut self, t: T) -> Result<(NonZeroUsize, &mut T), T> {
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
            if self.reallocate_min_capacity(next).is_err() {
                return Err(t);
            }
        }
        self.push_within_capacity(t)
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
            .ok()
            .expect("`push_reallocating` failed")
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
/// traits like [NonZeroInxGenericStack] that have a `max_capacity` function.
pub trait SetMaxCapacity {
    /// Changes the maximum allowed capacity to `max_capacity`, returning `None`
    /// iff `max_capacity < self.capacity()`.
    ///
    /// The max capacity can be set to `usize::MAX`, but the allocation
    /// functions will usually fail before the capacity can actually reach the
    /// max capacity. This function is only fallible to prevent violating the
    /// invariant `self.capacity() <= self.max_capacity()`.
    #[must_use]
    fn set_max_capacity(&mut self, max_capacity: usize) -> Option<()>;
}
