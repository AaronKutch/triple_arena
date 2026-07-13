use crate::{Link, chain::LinkNoGen, traits::Ptr, utils::AllocError};

pub enum InsertionFailure {
    OutOfCapacity,
    GenerationOverflow,
}

/// The base trait for `triple_arena` style Arenas.
pub unsafe trait ArenaTrait<P: Ptr, T> {
    /// Creates an empty arena, which may have any capacity to start with
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
    /// [ArenaTrait::reallocate_min_capacity] behaves strictly to
    /// avoid exceeding this limit). But most dynamically allocated types
    /// would return `None` to indicate that they will try to increase in
    /// length until memory allocation failure.
    fn max_capacity(&self) -> Option<usize>;

    /// Reallocates in order to try and change `self.capacity()` to have a lower
    /// bound of `min_capacity` elements of capacity. This can act both to
    /// grow and shrink the memory allocation. This will never remove elements
    /// and will always result in a capacity of at least `self.len()`. Note
    /// that, depending on internal element allocation, the capacity can be
    /// prevented from shrinking unless `Ptr`s are recast with FIXME. Can return
    /// an allocation error in all cases depending on implementor choice and
    /// allocator behavior, even `min_capacity <= self.capacity()`.
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

    /// Return the arena generation counter (unless `P::Gen` is `()` in which
    /// case there is no generation counting).
    ///
    /// Unless overflow or generation jumps from certain special operations
    /// happens, this is equal to the number of invalidation operations
    /// performed on this arena plus 2
    fn generation(&self) -> P::Gen;

    //fn insert_within_capacity(&mut self, t: T) -> Result<(P, &mut T), T>;
    //fn insert_reallocating(&mut self, t: T) -> Result<(P, &mut T), T>;
    // Never panics on generation overflow
    //fn insert
    //fn insert_with // maybe?

    /// Returns if `p` is a valid `Ptr`
    fn contains(&self, p: P) -> bool;

    /*
    /// Gets a reference to an element without doing checks
    ///
    /// # Safety
    ///
    /// Must not be called with `inx.get() > self.len()`
    unsafe fn get_unchecked(&self, inx: NonZeroUsize) -> &T;*/

    /*
    /// Like [Arena::get], except generation counters are ignored and the
    /// existing generation is returned.
    #[doc(hidden)]
    fn get_no_gen(&self, p: P::Inx) -> Option<(P::Gen, &T)>*/

    /// Invalidates all references to the `T` pointed to by `p`, and returns a
    /// new valid reference. Does no invalidation and returns `None` if `p` is
    /// invalid.
    #[must_use]
    fn invalidate(&mut self, p: P) -> Option<P>;

    /// Replaces the `T` pointed to by `p` with `new`, returns the old `T`, and
    /// keeps the internal generation counter as-is so that previously
    /// constructed `Ptr`s to this allocation are still valid.
    ///
    /// # Errors
    ///
    /// Returns ownership of `new` instead if `p` is invalid
    fn replace_and_keep_gen(&mut self, p: P, new: T) -> Result<T, T>;

    /// Replaces the `T` pointed to by `p` with `new`, returns a tuple of the
    /// old `T` and new `Ptr`, and updates the internal generation counter so
    /// that previous `Ptr`s to this allocation are invalidated.
    ///
    /// # Errors
    ///
    /// Does no invalidation and returns ownership of `new` if `p` is invalid
    fn replace_and_update_gen(&mut self, p: P, new: T) -> Result<(T, P), T>;

    /// Swaps the `T` at indexes `p0` and `p1` and keeps the generation counters
    /// as-is. If `p0 == p1` then nothing occurs. Returns `None` if `p0` or `p1`
    /// are invalid.
    #[must_use]
    fn swap(&mut self, p0: P, p1: P) -> Option<()>;

    /// Removes the `T` pointed to by `p`, returns the `T`, and invalidates old
    /// `Ptr`s to the `T`. Does no invalidation and returns `None` if `p` is
    /// invalid.
    #[must_use]
    fn remove(&mut self, p: P) -> Option<T>;

    /// Drops all `T` from the arena and invalidates all pointers previously
    /// created from it. This has no effect on allocated capacity.
    fn clear(&mut self);
}

// Index traits, Clone, clone_from_with get associated with another trait?

/// This inherits all the methods of [ArenaTrait] but adds on some [Link]-aware
/// ones
pub unsafe trait ChainArenaTrait<P: Ptr, T>: ArenaTrait<P, T> {
    fn get_link(&self, p: P) -> Option<&Link<P, T>>;
}

// this will end up being entirely separate, will eventually want advanced
// allocation control on key and value arenas

pub unsafe trait OrdArenaTrait<P: Ptr, K, V> {
    //fn insert_nonhereditary_linear(&mut self, p_init: P, num: usize, k: K, v: V)
    // -> P {

    //fn get_link(&self, p: P) -> Option<(P, Link<P, &T>)>;
    fn get_link_no_gen(&self, p: P::Inx) -> Option<(P::Gen, LinkNoGen<P, (&K, &V)>)>;
    //fn find_with<F: FnMut(P, &T) -> Ordering>(&self, f: F) -> Option<P>;

    //fn replace_val_*
    //fn swap_vals

    //fn insert_overwrite
    //fn insert_unique
}

// this just needs to be entirely separate
pub unsafe trait SurjectArenaTrait<P: Ptr, T> {
    fn len_keys(&self) -> usize;
}
