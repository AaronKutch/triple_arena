use core::{iter::from_fn, slice::GetDisjointMutError};

use crate::{
    traits::{Advancer, Ptr},
    utils::AllocError,
};

/*
REF(arena_terminology): Internally an arena has a main memory (usually `m`) of slots, usually a stack of free or allocated slots. I decide to use the terminology "slots" to refer to the actual internal stack elements that exist. "entries" for the public logical behavior docs and entry APIs may involve capacity in the internal stack that doesn't have a slot yet, or beyond. I use "root" for single linked lists.

REF(exponential_double_buffer_blowup): In earlier versions of `triple_arena`, there was an invariant that we would keep all slots of the internal arena memory at least filled with free slots so that `self.m.capacity() == self.m.len()`. However, functions like `clone_from_with` exposed a flaw with this that is absolutely catastrophic for some use cases of this crate: `reserve` and `reserve_exact` are allowed to allocate inconsistently, e.x. one arena gets 32 capacity from doubling and another arena gets 24 from taking a half step (it happens that more recent versions of Rust's `Vec` reserve exactly, but this is not a guarantee for future versions to follow). If `clone_from` is called to copy the 24 capacity arena to the 32 capacity arena, then it must reserve 8 more capacity. `reserve_exact` can then choose to start allocating by only doubling, in which case the 24 capacity arena gets 24 additional capacity. If the new 48 capacity arena is cloned to the 32 capacity arena, it can get 32 more capacity to increase to 64 capacity despite nothing being inserted. If the arenas in a double buffer setup `clone_from` to each other in a loop, they leap frog each other exponentially. This means that there must be a detached internal length (in slots which is different from the Arena's logical length) from an internal capacity. The current version has introduced the philosophy around `NonZeroInxGenericStack::reallocate_min_capacity` which we use and follow at the arena level in order to prevent issues. We also canonicalize the freelist with certain operations, which in some cases means that compression isn't even necessary to guarantee compact arenas over time.

other notes:

We don't need a `insert_with_manual_generation` function for `ArenaInsertTrait`, `set_generation` can be used in combination instead.

Originally there were complementary `replace_and_update_gen` and `replace_and_keep_gen` functions to emphasize the ability to deal with non-Clone types and how they should deal with generations, but these were barely used in practice and the signature of `replace_and_update_gen` was unavoidably awkward and increasingly so with the new strict generation overflow fallibility and the future possibility of `!Overwrite` types that can't be `mem::replace`d.

I don't think we need a `vals_mut`, may as well be advancing
*/

/// Returned from operations that are infallible but could involve generation
/// overflow
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
#[must_use]
pub enum InvalidationOption<T> {
    /// The operation was successful without generation counter overflow
    Success(T),
    /// The operation was completed successfully, except that a generation
    /// counter overflowed
    GenerationOverflow(T),
}

impl<T> InvalidationOption<T> {
    // I chose this naming because it is very short and is what is wanted extremely
    // often

    /// Maps both options to `T`. This is the preferred method for most uses
    /// that don't care about the incredible difficulty of
    /// reaching generation overflow with the default `NonZeroU64`.
    pub fn ok(self) -> T {
        match self {
            Self::Success(t) => t,
            Self::GenerationOverflow(t) => t,
        }
    }

    /// Maps `Success` to `Ok`, `GenerationOverflow` to `Err`. Recommended only
    /// for small `P::Gen` sizes or ABA prevention situations that require
    /// absolute strictness.
    pub fn strict(self) -> Result<T, T> {
        match self {
            Self::Success(t) => Ok(t),
            Self::GenerationOverflow(t) => Err(t),
        }
    }
}

/// Returned from fallible operations that have two different degrees of
/// success.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
#[must_use]
pub enum InvalidationResult<T> {
    /// The operation was successful without generation counter overflow
    Success(T),
    /// The operation was completed successfully, except that a generation
    /// counter overflowed
    GenerationOverflow(T),
    /// The `Ptr` that invalidation was targeting was invalid, and the operation
    /// was never executed
    InvalidPtr,
}

impl<T> InvalidationResult<T> {
    /// Maps both `Success` and `GenerationOverflow` to `Some`, and maps
    /// `InvalidPtr` to `None`. This is the preferred method for most uses
    /// that don't care about the incredible difficulty of
    /// reaching generation overflow with the default `NonZeroU64`.
    pub fn ok(self) -> Option<T> {
        match self {
            Self::Success(t) => Some(t),
            Self::GenerationOverflow(t) => Some(t),
            Self::InvalidPtr => None,
        }
    }

    /// Maps `Success` to `Ok`, `GenerationOverflow` to `Err(Some)`, and
    /// `InvalidPtr` to `Err(None)`. Recommended only for small `P::Gen` sizes
    /// or ABA prevention situations that require absolute strictness.
    pub fn strict(self) -> Result<T, Option<T>> {
        match self {
            Self::Success(t) => Ok(t),
            Self::GenerationOverflow(t) => Err(Some(t)),
            Self::InvalidPtr => Err(None),
        }
    }
}

/// The base trait for `triple_arena` style Arenas. See [crate::Arena] for the
/// standard implementor.
///
/// # Note
///
/// A `P: Ptr` instance is logically invalid if:
///  - it points to a different arena than the one it is being used as an
///    argument to
///  - it points to a `T` that has been the target of some `Ptr` invalidation
///    operation such as removal
///
/// However, the functions here might not detect invalidity and return a `T`
/// different than the one a `Ptr` originally pointed to. The first case is
/// caught if different `Ptr` structs are being used for different arenas, in
/// which case Rust's type system will prevent using the wrong pointers. The
/// second case is only guaranteed to be caught if `P` has a generation counter
/// and generation overflow is guarded against. Otherwise, it is possible for
/// another `T` to get allocated in the same allocation, and pointers to the
/// previous `T` will now point to a different `T` (otherwise known as the ABA
/// problem).
///
/// # Overflow
///
/// When using the default `P::Inx = usize` and `P::Gen = NonZeroU64`, only
/// memory exhaustion should be a concern on all platforms. It would take over
/// 500 years for generation overflow to occur if 1 billion invalidations per
/// second occured. Note that generation overflow with the `NonZero*` primitives
/// wraps around and skips the invalid `Ptr` generation case, and does not
/// panic.
///
/// For example, in most cases, you should just use [ArenaInsertTrait::insert]
/// to insert elements into the arena and [InvalidationResult::ok] on
/// invalidation operations. If the arena backing type is limited or you must
/// handle allocation failures, then [ArenaInsertTrait::insert_reallocating] and
/// similar should be used.
pub trait ArenaTrait<P: Ptr, T> {
    // An advancer over the valid `Ptr`s of this arena
    type PtrAdvancer: Advancer<Self, Item = P>;

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

    /// Returns the number of elements in the arena
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

    /// Manually set the arena generation counter. This can break some soft
    /// invariants such as ABA problem prevention and `P::invalid` always being
    /// invalid with generation counters.
    fn set_generation(&mut self, new_gen: P::Gen);

    /// Returns if `p` is a valid `Ptr`
    fn contains(&self, p: P) -> bool {
        self.get(p).is_some()
    }

    /// Returns a reference to a `T` pointed to by `p`. Returns `None` if `p` is
    /// invalid.
    #[must_use]
    fn get(&self, p: P) -> Option<&T> {
        self.get_inx(p.inx())
            .and_then(|(generation, t)| (generation == p.generation()).then_some(t))
    }

    /// Like [Arena::get], except generation counters are ignored and the
    /// existing generation is returned.
    fn get_inx(&self, p: P::Inx) -> Option<(P::Gen, &T)>;

    /// Returns a mutable reference to a `T` pointed to by `p`. Returns `None`
    /// if `p` is invalid.
    #[must_use]
    fn get_mut(&mut self, p: P) -> Option<&mut T> {
        self.get_inx_mut(p.inx())
            .and_then(|(generation, t)| (generation == p.generation()).then_some(t))
    }

    // I'd rather just reuse `GetDisjointMutError`, there are necessarily so many
    // specific cases from `P` overtruncation to unallocated vs out-of-bounds in the
    // underlying stack anyways that wouldn't be general to split up, we would end
    // up having a isomorphic enum with essentially the same useful semantics.

    /// Returns mutable references to many elements at once, in order according
    /// to the `indices` passed in. Returns an error if any `Ptr`s are invalid
    /// or if any are repeated.
    ///
    /// This method does a `O(n^2)` check for overlapping indices, be careful
    /// when passing in many indices. Any kind of invalid `Ptr` is reported
    /// as `GetDisjointMutError::IndexOutOfBounds` and any repeated `Ptr`s are
    /// reported as `GetDisjointMutError::OverlappingIndices`.
    fn get_disjoint_mut<const N: usize>(
        &mut self,
        indices: [P; N],
    ) -> Result<[&mut T; N], GetDisjointMutError> {
        // check generations before `IndexOutOfBounds` could be returned, because it
        // would be normal to have an invalidated `Ptr` collide with a newer `Ptr` by
        // index, when the `Ptr`s were not actually equal
        for p in indices {
            if !self.contains(p) {
                return Err(GetDisjointMutError::IndexOutOfBounds);
            }
        }
        self.get_disjoint_inx_mut(indices.map(|p| p.inx()))
            .map(|a| a.map(|(_, t)| t))
    }

    /// Like [Arena::get_mut], except generation counters are ignored and the
    /// existing generation is returned.
    fn get_inx_mut(&mut self, p: P::Inx) -> Option<(P::Gen, &mut T)> {
        let [res] = self.get_disjoint_inx_mut([p]).ok()?;
        Some(res)
    }

    /// Like [Arena::get_disjoint_mut], except generation counters are ignored
    /// and the existing generations are returned with the mutable
    /// references.
    fn get_disjoint_inx_mut<const N: usize>(
        &mut self,
        indices: [P::Inx; N],
    ) -> Result<[(P::Gen, &mut T); N], GetDisjointMutError>;

    /// Finds the first valid `Ptr` in terms of the `P::Inx` ordering, be aware
    /// that this can be an `O(n)` operation on some implementations
    fn find_first_ptr(&self) -> Option<P>;

    /// Finds the last valid `Ptr` in terms of the `P::Inx` ordering, be aware
    /// that this can be an `O(n)` operation on some implementations
    fn find_last_ptr(&self) -> Option<P>;

    /// Advances over every valid `Ptr` in `self` starting from the first.
    ///
    /// When using the correct [Advancer] loop structure, every `Ptr` valid from
    /// before the loop began will be witnessed as long as it is kept valid
    /// during the loop. The `Ptr`s of insertions that occur during the loop
    /// can both be witnessed or not witnessed before the loop terminates.
    fn advancer(&self) -> Self::PtrAdvancer {
        if let Some(first) = self.find_first_ptr() {
            self.ordered_advancer(first.inx(), false)
        } else {
            Self::PtrAdvancer::empty()
        }
    }

    /// The same as [ArenaTrait::advancer], but it starts from `inx` and goes
    /// forwards or in reverse if `rev` is set. `inx` does not have to point at
    /// a valid entry, and it will find the nexte valid entry if it exists in
    /// the direction the advancer is going.
    fn ordered_advancer(&self, inx: P::Inx, rev: bool) -> Self::PtrAdvancer;

    /// Iteration over all valid `P` in the arena
    fn ptrs(&self) -> impl Iterator<Item = P> {
        let mut adv = self.advancer();
        from_fn(move || adv.advance(self))
    }

    /// Iteration over all `&T` in the arena
    fn vals<'a>(&'a self) -> impl Iterator<Item = &'a T>
    where
        T: 'a,
    {
        let mut adv = self.advancer();
        from_fn(move || {
            // we would need to handle the ability to handle invalidation in the middle of
            // advancing, but `advance` is supposed to return a guaranteed valid `Ptr` that
            // is good if we immediately use it here
            adv.advance(self).and_then(|p| self.get(p))
        })
    }

    fn vals_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut T>
    where
        T: 'a,
    {
        self.iter_mut().map(|(_, t)| t)
    }

    /// Iteration over all `(P, &T)` in the arena
    fn iter<'a>(&'a self) -> impl Iterator<Item = (P, &'a T)>
    where
        T: 'a,
    {
        let mut adv = self.advancer();
        from_fn(move || {
            let p = adv.advance(self)?;
            Some((p, self.get(p)?))
        })
    }

    /// Iteration over all `(P, &mut T)` in the arena
    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (P, &'a mut T)>
    where
        T: 'a;

    /// A draining iterator over `(P, T)` in the arena.
    ///
    /// The `InvalidationOption` is returned per-element because of certain
    /// arena designs that have a generation per internal slot or region instead
    /// of a global generation.
    fn drain(&mut self) -> impl Iterator<Item = InvalidationOption<(P, T)>> {
        let mut adv = self.advancer();
        from_fn(move || {
            let p = adv.advance(self)?;
            match self.remove(p) {
                InvalidationResult::Success(t) => Some(InvalidationOption::Success((p, t))),
                InvalidationResult::GenerationOverflow(t) => {
                    Some(InvalidationOption::GenerationOverflow((p, t)))
                }
                InvalidationResult::InvalidPtr => None,
            }
        })
    }

    /// Invalidates all references to the `T` pointed to by `p`, and returns a
    /// new valid reference. Does no invalidation and returns `None` if `p` is
    /// invalid.
    fn invalidate(&mut self, p: P) -> InvalidationResult<P>;

    /// Removes the `T` pointed to by `p`, returns the `T`, and invalidates old
    /// `Ptr`s to the `T`. Does no invalidation and returns `None` if `p` is
    /// invalid.
    fn remove(&mut self, p: P) -> InvalidationResult<T>;

    /// Drops all `T` from the arena and invalidates all pointers previously
    /// created from it. This has no effect on allocated capacity.
    fn clear(&mut self) -> InvalidationOption<()>;

    // `clone_from_with_within_capacity() -> Option<()>` is getting ridiculous and
    // the fallible return is only for if it was called in a trivially checkable
    // state, just make this one reallocating with a condition that it will never
    // reallocate if there is enough capacity. Also we break with old requirements
    // and always canonicalize the freelist and check for the last actually
    // allocated slot in `source`, this solves certain double buffering exponential
    // growth problems that early versions of `triple_arena` ran into.

    /// Overwrites `self` with a clone of `source` (dropping all preexisting `T`
    /// and overwriting the generation counter with `source.generation()`).
    /// The `Ptr` validities are also cloned so that the `P` associated with a
    /// `U` is a valid reference to its mapped `T`. Reallocation occurs if the
    /// capacity of `self` is not large enough. If the highest `P::Inx` index of
    /// an allocated entry in `source` would fit in `self.capacity()`, this is
    /// guaranteed to _not_ reallocate and the function is infallible. Returns
    /// an error upon reallocation failure.
    fn clone_from_with<U, A: ArenaTrait<P, U>, F: FnMut(P, &U) -> T>(
        &mut self,
        source: &A,
        map: F,
    ) -> Result<(), AllocError>;
}

/// The standard trait for insertion into [ArenaTrait] arenas. Some arenas do
/// not have a freelist however, and this trait could not be implemented
/// efficiently. The [ArenaDirectInsertTrait] trait is a separate trait because
/// direct insertions would not be efficient on an arena with a one-way linked
/// freelist.
pub trait ArenaInsertTrait<P: Ptr, T>: ArenaTrait<P, T> {
    /// Inserts `t` into the arena and returns a `Ptr` and mutable reference to
    /// it. Returns the `t` if there was no available capacity.
    fn insert_within_capacity(&mut self, t: T) -> Result<(P, &mut T), T>;

    /// Inserts `t` into the arena and returns a `Ptr` and mutable reference to
    /// it. Automatically reallocates if needing more capacity. Returns the `t`
    /// if there was no available capacity.
    fn insert_reallocating(&mut self, t: T) -> Result<(P, &mut T), T> {
        if self.len() == self.capacity() {
            // TODO may want something more sophisticated, see https://github.com/rust-lang/rust/issues/29931

            if self
                .reallocate_min_capacity(self.capacity().saturating_mul(2))
                .is_err()
            {
                return Err(t);
            }
        }
        self.insert_within_capacity(t)
    }

    /// Inserts `t` into the arena and returns a `Ptr` and mutable reference to
    /// it.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure when needing to extend
    /// capacity
    fn insert(&mut self, t: T) -> (P, &mut T) {
        self.insert_reallocating(t)
            .ok()
            .expect("`ArenaTrait::insert_reallocating` failed")
    }
}

/// See [ArenaInsertTrait], this mainly is for special arenas without a
/// freelist, that are supposed to follow the state of another arena.
pub trait ArenaDirectInsertTrait<P: Ptr, T>: ArenaTrait<P, T> {
    /// Inserts `t` directly at raw [PtrInx] `p` into the arena and returns a
    /// `Ptr` and mutable reference to it. Returns an error with the `t` if
    /// the index was beyond capacity or if there was an existing entry at `p`.
    /// Uses the current `self.generation()` of the arena for the generation.
    fn insert_direct_inx(&mut self, p: P::Inx, t: T) -> Result<(P, &mut T), T>;

    /// Inserts `t` directly at `p` into the arena, accepting `p` and its
    /// generation as the valid `Ptr` to the element, returning a mutable
    /// reference to it. Returns an error with the `t` if the index was beyond
    /// capacity or if there was an existing entry at `p.inx()`.
    fn insert_direct(&mut self, p: P, t: T) -> Result<&mut T, T>;
}

/*
/// This inherits all the methods of [ArenaTrait] but adds on some [Link]-aware
/// ones
pub trait ChainArenaTrait<P: Ptr, T>: ArenaTrait<P, T> {
    fn get_link(&self, p: P) -> Option<&Link<P, T>>;
}

// this will end up being entirely separate, will eventually want advanced
// allocation control on key and value arenas

pub trait OrdArenaTrait<P: Ptr, K, V> {
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
pub trait SurjectArenaTrait<P: Ptr, T> {
    fn len_keys(&self) -> usize;
}
*/
