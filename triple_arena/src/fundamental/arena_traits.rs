use core::{iter::from_fn, slice::GetDisjointMutError};

use crate::{
    AllocError, ChainInsertionError, DirectInsertionError, Link, NotWithinCapacityError,
    ReallocationError,
    chain::LinkNoGen,
    traits::{Advancer, Ptr},
};

/*
See first the comments in nonzero_inx_generic_stack.rs

REF(arena_terminology): Internally an arena has a main memory (usually `m`) of slots, usually a stack of free or allocated slots. I decide to use the terminology "slots" to refer to the actual internal stack elements that exist. "entries" for the public logical behavior docs and entry APIs may involve capacity in the internal stack that doesn't have a slot yet, or beyond. I use "root" for single linked lists.

REF(exponential_double_buffer_blowup): In earlier versions of `triple_arena`, there was an invariant that we would keep all slots of the internal arena memory at least filled with free slots so that `self.m.capacity() == self.m.len()`. However, functions like `clone_from_with` exposed a flaw with this that is absolutely catastrophic for some use cases of this crate: `reserve` and `reserve_exact` are allowed to allocate inconsistently, e.x. one arena gets 32 capacity from doubling and another arena gets 24 from taking a half step (it happens that more recent versions of Rust's `Vec` reserve exactly, but this is not a guarantee for future versions to follow). If `clone_from` is called to copy the 24 capacity arena to the 32 capacity arena, then it must reserve 8 more capacity. `reserve_exact` can then choose to start allocating by only doubling, in which case the 24 capacity arena gets 24 additional capacity. If the new 48 capacity arena is cloned to the 32 capacity arena, it can get 32 more capacity to increase to 64 capacity despite nothing being inserted. If the arenas in a double buffer setup `clone_from` to each other in a loop, they leap frog each other exponentially. This means that there must be a detached internal length (in slots which is different from the Arena's logical length) from an internal capacity. The current version has introduced the philosophy around `NonZeroInxGenericStack::reallocate_min_capacity` which we use and follow at the arena level in order to prevent issues. We also canonicalize the freelist with certain operations, which in some cases means that compression isn't even necessary to guarantee compact arenas over time.

other notes:

There is no `generation` or `set_generation` function (or at least there won't be one without an index involved), because some implementations will have generations per slot or per domain

Originally there were complementary `replace_and_update_gen` and `replace_and_keep_gen` functions to emphasize the ability to deal with non-Clone types and how they should deal with generations, but these were barely used in practice and the signature of `replace_and_update_gen` was unavoidably awkward and increasingly so with the new strict generation overflow fallibility and the future possibility of `!Overwrite` types that can't be `mem::replace`d.

The defaulted iterator designs mean that concrete associated types can't be used, but the advancer can do anything so we just have it as the associated type

`find_first_inx_ptr` and `find_last_inx_ptr` are weird from a more pure perspective, but they have a bunch of miscellanious uses in helping generics and in finding things like the last element's index etc. On all nonlinear arenas I am aware of, it is still possible to have an ordering that corresponds to advancer ordering.

We can almost avoid "entry" style function and structs, except that some downstream uses simply must know the `Ptr` slot that they will be inserted into, and not only that but they need to be able to cancel the insertion if some internal contruction using that `Ptr` also goes wrong, and also there is the case where `T` has to be specially constructed and users want to only do so once it is known an entry is guaranteed. We decide to have "entry_insert*" functions and multiply them in parallel with the other insert functions. The other potential way to have done it is some "next_insertion_ptr" function (which might be added in parallel for other reasons, note that you have to be careful for randomly generated `Ptr` designs), however the entry style promotes better typing and reduces broken intermediate changes, also the signature is technically more optimized for the fallible cases.

We call them "entry_insert*" in opposite order to the associated "InsertionEntry", because the method is an insert method with a modifier that it is of entry type (see also "direct_insert*"), and it returns an entry that is of the insertion kind (like "VacantEntry"). For direct insertion we only have an entry type method (needed even though the `P` is known, because construction of the `T` may not want to occur unless the entry is known to be available) and drop "direct" from the method name, otherwise we would have too many methods and the non-entry method would be too awkward with error handling. A panicking `direct_insert` function would be too fallible if it avoided returning a `Result` and panicked for reasons of slot collision, and if it returned any fallible enum we may as well return other errors.

I would have signatures like `Result<..., T>` for nonentry fallible insertion methods, but since the entry methods exist (and often the `Result<..., T>` form promoted bad undo strategies anyways), I have made them all `Result<..., *Error>` instead.

I decided to only have a `direct_insert_within_capacity` method for direct insertion, and no `_reallocating` or panicking variations. Capacity should be manually managed for such arenas, because in several contexts direct insertion would be used in, arbitrary indexes would easily lead to OOM. dealing with automatic reallocation fallibility in the signatures would also be annoying, and usually this is a mirror arena that will not have many places in the code calling direct insertion methods.

I wanted to avoid adding new error enums for chain insertion and would have used something like `Option<Result<Self::InsertionEntry<'_>, NotWithinCapacityError>>`, but the problem is that users will want to assume certain errors take priority and that the outer errors could be unwrapped if their associated errors would not happen. The `ChainInsertionError` has variants that don't show with certain inputs, but having a single set of functions with a single unified `LinkInsertKind` is superior for many reasons.

The `drain` function ends up allowing invalidating every element separately because of "certain arena designs that have a generation per internal slot or domain". For singular generation arenas I also considered maybe adding an invariant that the generation counter equals the number of element invalidations minus 2, but I don't know of a use for it and it costs more and it is awkward to deal with edge cases with `drain` iterator dropping. I decide that we just make `drain` dropping just guarantee a single unseen `clear` invalidation (if there are elements), and make `clear` do a single invalidation if there are any entries. `drain` individually dropping could also make more sense if it stopped part way through on iterator drop, but `clear` by default is safer. The `compress` functions make sense to only increment the generation once.

I almost considered `fn ok` instead of `fn allow` but that could easily lead to confusion and would make finding these uses difficult

`insert` could have returned `(P, &mut T)` as an extension of what stacks do, but it definitely does not carry its weight and the entry methods replace most places where it would be used
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
    /// Maps both options to `T`. This is the preferred method for most uses
    /// that don't care about the incredible difficulty of
    /// reaching generation overflow with the default `NonZeroU64`.
    pub fn allow(self) -> T {
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

    /// If `matches!(self, Self::GenerationOverflow(_))`
    pub fn is_overflow(&self) -> bool {
        matches!(self, Self::GenerationOverflow(_))
    }

    /// Maps `T` to `U` in the corresponding variants
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> InvalidationOption<U> {
        match self {
            Self::Success(t) => InvalidationOption::Success(f(t)),
            Self::GenerationOverflow(t) => InvalidationOption::GenerationOverflow(f(t)),
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
    pub fn allow(self) -> Option<T> {
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

    /// Maps `T` to `U` in the corresponding variants
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> InvalidationResult<U> {
        match self {
            Self::Success(t) => InvalidationResult::Success(f(t)),
            Self::GenerationOverflow(t) => InvalidationResult::GenerationOverflow(f(t)),
            Self::InvalidPtr => InvalidationResult::InvalidPtr,
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
/// to insert elements into the arena and [InvalidationResult::allow] on
/// invalidation operations. If the arena backing type is limited or you must
/// handle allocation failures, then [ArenaInsertTrait::insert_reallocating] and
/// similar should be used.
pub trait ArenaTrait<P: Ptr, T>: Sized {
    /// An advancer over the valid `Ptr`s of this arena
    type PtrAdvancer: Advancer<Self, Item = P>;

    /// Creates an empty arena, which may have any capacity to start with
    fn new() -> Self;

    /// Creates an empty stack with a minimum capacity of at least
    /// `min_capacity`. The max capacity, if set, is also initialized to at
    /// least the capacity of the returned stack. Returns an error upon
    /// allocation failure.
    ///
    /// In most cases [ArenaTrait::new] followed by
    /// [ArenaTrait::reallocate_min_capacity] would be sufficient,
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
    /// [ArenaTrait::reallocate_min_capacity] behaves strictly to
    /// avoid `self.capacity()` exceeding this limit). But most dynamically
    /// allocated types would return `None` to indicate that they will try
    /// to increase in length until memory allocation failure. If set,
    /// `self.capacity() <= self.max_capacity()` is always true.
    fn max_capacity(&self) -> Option<usize>;

    /// Reallocates in order to try and change `self.capacity()` to have a lower
    /// bound of `min_capacity` elements of capacity. This can act both to
    /// grow and shrink the memory allocation. **Note** that, depending on
    /// internal element allocation, the capacity may be unable to converge on
    /// `self.len()` (because `Ptr` indexes need to be stable, a single element
    /// allocated at a high index can prevent removing all the unallocated slots
    /// less than it). This can be fixed by compressing with a function like
    /// [ArenaTrait::compress_with], calling this function afterwards, and
    /// fixing any external `Ptr`s with recasting. This will never remove
    /// elements and will always result in a capacity of at least
    /// `self.len()`. Can return an allocation error in all cases depending
    /// on implementor choice and allocator behavior, even `min_capacity <=
    /// self.capacity()`.
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

    /// Returns the number of elements in the arena
    fn len(&self) -> usize;

    /// If `self.len() == 0`
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns if `p` is a valid `Ptr`
    fn contains(&self, p: P) -> bool {
        self.get(p).is_some()
    }

    /// Returns a reference to a `T` pointed to by `p`. Returns `None` if `p` is
    /// invalid.
    fn get(&self, p: P) -> Option<&T> {
        self.get_inx(p.inx())
            .and_then(|(generation, t)| (generation == p.generation()).then_some(t))
    }

    /// Like [ArenaTrait::get], except generation counters are ignored and the
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
        // index, when the `Ptr`s were actually completely logically independent
        for p in indices {
            if !self.contains(p) {
                return Err(GetDisjointMutError::IndexOutOfBounds);
            }
        }
        self.get_disjoint_inx_mut(indices.map(|p| p.inx()))
            .map(|a| a.map(|(_, t)| t))
    }

    /// Like [ArenaTrait::get_mut], except generation counters are ignored and
    /// the existing generation is returned.
    fn get_inx_mut(&mut self, p: P::Inx) -> Option<(P::Gen, &mut T)> {
        let [res] = self.get_disjoint_inx_mut([p]).ok()?;
        Some(res)
    }

    /// Like [ArenaTrait::get_disjoint_mut], except generation counters are
    /// ignored and the existing generations are returned with the mutable
    /// references.
    fn get_disjoint_inx_mut<const N: usize>(
        &mut self,
        indices: [P::Inx; N],
    ) -> Result<[(P::Gen, &mut T); N], GetDisjointMutError>;

    /// Finds the index-first valid `Ptr` in terms of the `P::Inx` ordering, be
    /// aware that this can be an `O(n)` operation on some implementations
    fn find_first_inx_ptr(&self) -> Option<P>;

    /// Finds the index-last valid `Ptr` in terms of the `P::Inx` ordering, be
    /// aware that this can be an `O(n)` operation on some implementations
    fn find_last_inx_ptr(&self) -> Option<P>;

    /// Advances over every valid `Ptr` in `self` starting from the first.
    ///
    /// When using the correct [Advancer] loop structure, every `Ptr` valid from
    /// before the loop began will be witnessed as long as it is kept valid
    /// during the loop. The `Ptr`s of insertions that occur during the loop
    /// can both be witnessed or not witnessed before the loop terminates.
    fn advancer(&self) -> Self::PtrAdvancer {
        if let Some(first) = self.find_first_inx_ptr() {
            self.ordered_advancer(first.inx(), false)
        } else {
            Self::PtrAdvancer::empty()
        }
    }

    /// The same as [ArenaTrait::advancer], but it starts from `inx` and goes
    /// forwards or in reverse if `rev` is set. `inx` does not have to point at
    /// a valid entry, and it will find the next valid entry if it exists in
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

    /// A draining iterator over `(P, T)` in the arena. This will run
    /// `self.clear()` (and any invalidation notifications will be lost) if the
    /// iterator is dropped.
    ///
    /// The `InvalidationOption` is returned per-element because of certain
    /// arena designs that have a generation per internal slot or domain instead
    /// of a global generation.
    fn drain(&mut self) -> impl Iterator<Item = InvalidationOption<(P, T)>>;
    /* // Is logically this but also needs the clear-on-drop logic
    let mut adv = self.advancer();
    from_fn(move || {
        let p = adv.advance(self)?;
        // for global generation arenas, just do this for simplicity and so that the
        // invalidation is associated with a particular element
        match self.remove(p) {
            InvalidationResult::Success(t) => Some(InvalidationOption::Success((p, t))),
            InvalidationResult::GenerationOverflow(t) => {
                Some(InvalidationOption::GenerationOverflow((p, t)))
            }
            InvalidationResult::InvalidPtr => None,
        }
    })
    */

    /// Invalidates all references to the `T` pointed to by `p`, and returns a
    /// new valid reference. Does no invalidation and returns `None` if `p` is
    /// invalid.
    fn invalidate(&mut self, p: P) -> InvalidationResult<P>;

    /// Removes the `T` pointed to by `p`, returns the `T`, and invalidates old
    /// `Ptr`s to the `T`. Does no invalidation and returns `None` if `p` is
    /// invalid.
    fn remove(&mut self, p: P) -> InvalidationResult<T>;

    /// Drops all `T` from the arena and invalidates all pointers previously
    /// created from it. This has no effect on allocated capacity. Returns if
    /// any generation overflow occured (for arena implementations that have
    /// generations per internal slot or domain, this will return overflow if
    /// any single one overflowed).
    ///
    /// Does not invalidate and is always successful if `self.is_empty()`.
    fn clear(&mut self) -> InvalidationOption<()>;

    /// Compresses the arena as much as possible by moving all internal
    /// allocated indexes to be one after another with no unallocated gaps
    /// between them, such that `self.reallocate_min_capacity(self.len())` would
    /// reduce the capacity as much as possible. After this, the capacity can be
    /// reduced as much as possible with
    /// `self.reallocate_min_capacity(self.len())`. All `T` remains, but all
    /// `Ptr`s are logically invalidated. New `Ptr`s to the entries can be found
    /// again by advancers and iterators. If all extant `Ptr`s are recast or
    /// invalidated `Ptr`s will not be a problem, `reset_generation` should be
    /// set in order to reset the generation counter on all of the new `Ptr`s
    /// (and `InvalidationOption::Success` will always be returned).
    fn compress(&mut self, reset_generation: bool) -> InvalidationOption<()> {
        self.compress_with(reset_generation, |_, _, _| ())
    }

    /// The same as [ArenaTrait::compress] except that `map` is run on
    /// `(P, &mut T, P)`, with the first `P` being the old `Ptr` and the last
    /// `P` being the new `Ptr` that points to the `T` after compression. If all
    /// extant `Ptr`s are recast or invalidated `Ptr`s will not be a problem,
    /// `reset_generation` should be set in order to reset the generation
    /// counter on all of the new `Ptr`s (and `InvalidationOption::Success` will
    /// always be returned).
    ///
    /// This can be used to create a custom [crate::traits::Recaster] for
    /// recasting external `Ptr`s:
    /// ```
    /// use triple_arena::{Arena, HeapBacking, ptr_struct, traits::*};
    ///
    /// // (This would be a standard function, except there are far too many choices to
    /// // make on the backing of the recaster arena and how fallibility should be
    /// // handled)
    /// fn compress_recaster<
    ///     P: Ptr,
    ///     T,
    ///     A: ArenaTrait<P, T> + SingularGenerationArena<P> + ArenaCloneFromWith<P, T>,
    /// >(
    ///     this: &mut A,
    ///     reset_generation: bool,
    /// ) -> Arena<P, P, HeapBacking> {
    ///     // this arena will be a recaster in which we create a mapping from the old `Ptr`
    ///     // domain to the new one
    ///     let mut res = Arena::<P, P, HeapBacking>::new();
    ///     // this sets all the keys of the mapping by cloning the `Ptr` validities of the
    ///     // pre-compression `self` into the recaster and puts in invalid placeholders for
    ///     // the new domain
    ///     res.clone_from_with(this, |_, _| P::invalid()).unwrap();
    ///     // compress and write the new `Ptr`s at the indexes of the corresponding old
    ///     // ones, completing the mapping
    ///     this.compress_with(reset_generation, |p, _, q| *res.get_mut(p).unwrap() = q)
    ///         .allow();
    ///     res
    /// }
    ///
    /// ptr_struct!(P0);
    ///
    /// impl Recast<P0> for (u64, Option<P0>) {
    ///     fn recast<R: Recaster<Item = P0>>(
    ///         &mut self,
    ///         recaster: &R,
    ///     ) -> Result<(), <R as Recaster>::Item> {
    ///         self.1.recast(recaster)?;
    ///         Ok(())
    ///     }
    /// }
    ///
    /// let mut a = Arena::<P0, (u64, Option<P0>)>::new();
    ///
    /// let p0 = a.insert((0, None));
    /// let p42 = a.insert((42, None));
    /// let p1 = a.insert((1, None));
    /// a.insert((1337, Some(p42)));
    /// // make some internal slots unallocated
    /// a.remove(p0).allow().unwrap();
    /// a.remove(p1).allow().unwrap();
    ///
    /// assert_eq!(
    ///     &format!("{a:?}"),
    ///     "{P0[2](2): (42, None), P0[4](2): (1337, Some(P0[2](2)))}"
    /// );
    ///
    /// // This is what the `Recast` trait is for. We call this before
    /// // serialization. This fixes both the indexes of the `Ptr` keys
    /// // and the indexes inside the values of the arena, so that
    /// // relations are preserved.
    /// let recaster = compress_recaster(&mut a, false);
    /// a.recast(&recaster).unwrap();
    /// // the recaster had this
    /// assert_eq!(
    ///     &format!("{recaster:?}"),
    ///     "{P0[2](2): P0[1](5), P0[4](2): P0[2](5)}"
    /// );
    /// // now the allocated slots are compressed and we could shrink capacity or use
    /// // this for compact serialization
    /// assert_eq!(
    ///     &format!("{a:?}"),
    ///     "{P0[1](5): (42, None), P0[2](5): (1337, Some(P0[1](5)))}"
    /// );
    ///
    /// // try again but with resetting the generation, useful in some cases
    /// let recaster = compress_recaster(&mut a, true);
    /// a.recast(&recaster).unwrap();
    /// // maps all the generations down to a minimal value
    /// assert_eq!(
    ///     &format!("{recaster:?}"),
    ///     "{P0[1](5): P0[1](2), P0[2](5): P0[2](2)}"
    /// );
    /// assert_eq!(
    ///     &format!("{a:?}"),
    ///     "{P0[1](2): (42, None), P0[2](2): (1337, Some(P0[1](2)))}"
    /// );
    /// ```
    fn compress_with<F: FnMut(P, &mut T, P)>(
        &mut self,
        reset_generation: bool,
        map: F,
    ) -> InvalidationOption<()>;
}

/// Implemented for most "simple" arenas. Some arenas do not have a global
/// generation (which also usually comes along with a complex `P::Inx` that
/// would not be suitable for things like [ArenaCloneFromWith::clone_from_with],
/// although that trait is separate because there are other conditions), and
/// thus should not implement this.
pub trait SingularGenerationArena<P: Ptr> {
    /// Returns a singular generation for the arena, that is usually the
    /// generation of entries that would be inserted now
    fn singular_generation(&self) -> P::Gen;
}

/// A type implementing this can have a fully generic mapping clone operation
/// from another type implementing this.
pub trait ArenaCloneFromWith<P: Ptr, T>: ArenaTrait<P, T> {
    // `clone_from_with_within_capacity() -> Option<()>` is getting ridiculous and
    // the fallible return is only for if it was called in a trivially checkable
    // state, just make this one reallocating with a condition that it will never
    // reallocate if there is enough capacity. Also we break with old requirements
    // and always canonicalize the freelist and check for the last actually
    // allocated slot in `source`, this solves certain double buffering exponential
    // growth problems that early versions of `triple_arena` ran into.

    // This function is fundamentally problematic in some scenarios, we have put it
    // on its own trait and restrict the source to also require it. Wrappers can be
    // used where needed.

    /// Overwrites `self` with a clone of `source` (dropping all preexisting `T`
    /// and overwriting the singular generation counter if any with
    /// `source.singular_generation()`. The `Ptr` validities are also cloned so
    /// that the `P` associated with a `U` in `source` is also precisely the
    /// valid `Ptr` to its mapped `T`. Reallocation occurs if the capacity
    /// of `self` is not large enough. With simple arenas and indexes, if
    /// the `P::Inx` from the highest index is such that
    /// `source.find_last_inx_ptr(). unwrap().inx().get() <=
    /// self.capacity()`, this is guaranteed to _not_ reallocate and the
    /// function is infallible. Does _not_ clone max capacity limits, and
    /// will fail if any set limit on `self` is exceeded. Returns an error
    /// upon reallocation failure.
    fn clone_from_with<
        U,
        A: ArenaCloneFromWith<P, U> + SingularGenerationArena<P>,
        F: FnMut(P, &U) -> T,
    >(
        &mut self,
        source: &A,
        map: F,
    ) -> Result<(), ReallocationError>;
}

fn handle_reallocation<P: Ptr, T, A: ArenaTrait<P, T>>(
    this: &mut A,
) -> Result<(), ReallocationError> {
    if this.len() == this.capacity() {
        // REF(better_reallocation)

        // follow `RawVec`
        let mut next = if this.capacity() == 0 {
            if size_of::<T>() <= 1024 { 4 } else { 1 }
        } else {
            this.capacity().saturating_mul(2)
        };
        // but be able to saturate max capacity before causing an error
        if let Some(max_capacity) = this.max_capacity() {
            next = next.min(max_capacity);
        }
        if next <= this.capacity() {
            // the max capacity is limiting us
            return Err(ReallocationError::BeyondMaxCapacity);
        }
        this.reallocate_min_capacity(next)?;
    }
    Ok(())
}

/// Dropping the struct cancels the insertion
#[must_use]
pub trait ArenaInsertEntryTrait<'a, P: Ptr, T> {
    /// The `Ptr` at which this entry could be referenced, if inserted
    fn ptr(&self) -> P;

    /// Inserts `T` into the arena
    fn insert(self, t: T);
}

/// The standard trait for insertion into [ArenaTrait] arenas. Some arenas do
/// not have a freelist however, and this trait could not be implemented
/// efficiently. The [ArenaDirectInsertTrait] trait is a separate trait because
/// direct insertions would not be efficient on an arena with a one-way linked
/// freelist.
pub trait ArenaInsertTrait<P: Ptr, T>: ArenaTrait<P, T> {
    type InsertionEntry<'a>: ArenaInsertEntryTrait<'a, P, T>
    where
        Self: 'a;

    /// Inserts `t` into the arena and returns a `Ptr` to it. Returns an error
    /// if there was no available capacity.
    fn insert_within_capacity(&mut self, t: T) -> Result<P, NotWithinCapacityError>;

    /// Inserts `t` into the arena and returns a `Ptr` to it. Automatically
    /// reallocates if needing more capacity. Returns the `t`
    /// if an allocation error occurs or if [ArenaTrait::max_capacity] is used
    /// up.
    fn insert_reallocating(&mut self, t: T) -> Result<P, ReallocationError> {
        handle_reallocation(self)?;
        // an error shouldn't happen, but if it does it is logically the allocator's
        // fault
        self.insert_within_capacity(t)
            .map_err(|NotWithinCapacityError| ReallocationError::AllocError)
    }

    /// Inserts `t` into the arena and returns a `Ptr` to it. Panics if an
    /// allocation error occurs or if [ArenaTrait::max_capacity] is used up.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure when needing to extend
    /// capacity, or if `self.len()` is at the maximum capacity.
    #[track_caller]
    fn insert(&mut self, t: T) -> P {
        self.insert_reallocating(t)
            .expect("`ArenaInsertTrait::insert_reallocating` failed")
    }

    /// If capacity is available, an insertion entry for inserting into the
    /// arena is returned. Returns if there was no available capacity.
    fn entry_insert_within_capacity(
        &mut self,
    ) -> Result<Self::InsertionEntry<'_>, NotWithinCapacityError>;

    /// Returns an insertion entry, reallocating if necessary and returning an
    /// error if reallocation failed or if [ArenaTrait::max_capacity] is used
    /// up. Be aware that any reallocation happens upon calling this method, and
    /// the affects remain even if inserting into the arena is cancelled.
    fn entry_insert_reallocating(&mut self) -> Result<Self::InsertionEntry<'_>, ReallocationError> {
        handle_reallocation(self)?;
        self.entry_insert_within_capacity()
            .map_err(|NotWithinCapacityError| ReallocationError::AllocError)
    }

    /// Returns an insertion entry, panicking if an allocation error occurs or
    /// if [ArenaTrait::max_capacity] is used up.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure when needing to extend
    /// capacity, or if `self.len()` is at the maximum capacity.
    #[track_caller]
    fn entry_insert(&mut self) -> Self::InsertionEntry<'_> {
        self.entry_insert_reallocating()
            .expect("`ArenaInsertTrait::entry_insert_reallocating` failed")
    }
}

/// Describes multiple ways to insert a link. All the "*Inx" variants disregard
/// generation counters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkInsertKind<P: Ptr> {
    /// Insert a single link by itself, in a single link chain that is
    /// disconnected from anything else
    Disconnected,
    /// Insert a single link by itself but connected to itself, that is, a
    /// single link cyclic chain
    SingleLinkCyclic,
    /// Insert a link at the start of a chain. The `P` must point to the current
    /// start link of a noncyclic chain, and the inserted node will become the
    /// new start of the chain
    ChainStart(P),
    ChainStartInx(P::Inx),
    /// Insert a link at the end of a chain. The `P` must point to the current
    /// end link of a noncyclic chain, and the inserted node will become the new
    /// end of the chain
    ChainEnd(P),
    ChainEndInx(P::Inx),
    /// Insert a link as the previous link from the existing link at `P`, which
    /// could be anywhere on any chain, maintaining continuity of the chain
    PrevTo(P),
    PrevToInx(P::Inx),
    /// Insert a link as the next link from the existing link  at`P`, which
    /// could be anywhere on any chain, maintaining continuity of the chain
    NextTo(P),
    NextToInx(P::Inx),
    /// Insert a link inbetween two links on any chain with at least two links,
    /// maintaining continuity of the chain. The insertion will fail if the two
    /// links are not neighbors. Note that the arguments are directionally
    /// sensitive, calling [Link::next] on the link at `next_to` must result in
    /// `prev_to` and not the other way around.
    Inbetween {
        next_to: P,
        prev_to: P,
    },
    InbetweenInx {
        next_to: P::Inx,
        prev_to: P::Inx,
    },
}

/// Dropping the struct cancels the insertion
#[must_use]
pub trait ArenaDirectInsertEntryTrait<'a, P: Ptr, T> {
    /// Inserts `T` into the arena
    fn insert(self, t: T);
}

/// See [ArenaInsertTrait], this mainly is for special arenas without a
/// freelist, that are supposed to follow the state of another arena.
///
/// Note: An analogous chain arena version of this trait would not be feasible
/// because of questions around intermediate validities, however it can be
/// mimicked to arbitrary degrees by using a direct insertion arena and using
/// the [Link] struct directly in custom values. The same can be used for the
/// other arena types
pub trait ArenaDirectInsertTrait<P: Ptr, T>: ArenaTrait<P, T> {
    type DirectInsertionEntry<'a>: ArenaDirectInsertEntryTrait<'a, P, T>
    where
        Self: 'a;

    /// Returns an entry for direct insertion at `p.inx()`, if the index points
    /// to an internal slot that fits within existing capacity, and there is not
    /// already another element allocated at that index. `p.generation()` is
    /// always accepted and used as the valid generation for use with this
    /// entry.
    fn direct_insert_within_capacity(
        &mut self,
        p: P,
    ) -> Result<Self::DirectInsertionEntry<'_>, DirectInsertionError>;
}

/// This inherits all the methods of [ArenaTrait] but adds on some [Link]-aware
/// ones
pub trait ChainArenaTrait<P: Ptr, T>: ArenaTrait<P, T> {
    type InsertionEntry<'a>: ArenaInsertEntryTrait<'a, P, T>
    where
        Self: 'a;

    /// Returns a reference to the link pointed to by `p`. Returns `None` if `p`
    /// is invalid.
    ///
    /// Be aware that unlike the functions returning `LinkNoGen<P, T>`, this has
    /// to look up neighboring links to find their generation counters and may
    /// be less performant.
    fn get_link(&self, p: P) -> Option<Link<P, &T>> {
        let link = self.get_link_no_gen(p)?;
        let mut prev_next = (None, None);
        if let Some(p) = link.prev() {
            let Some((generation, _)) = self.get_inx(p) else {
                // better assembly
                unreachable!()
            };
            prev_next.0 = Some(P::_from_raw(p, generation))
        }
        if let Some(p) = link.next() {
            let Some((generation, _)) = self.get_inx(p) else {
                unreachable!()
            };
            prev_next.1 = Some(P::_from_raw(p, generation))
        }
        Some(Link::new(prev_next, &link.t))
    }

    // no `get_inx_link`, there are a bunch of lookups it has to do anyways

    /// Returns a reference to the link pointed to by `p`. Returns `None` if `p`
    /// is invalid.
    fn get_link_no_gen(&self, p: P) -> Option<&LinkNoGen<P, T>> {
        self.get_inx_link_no_gen(p.inx())
            .and_then(|(generation, link)| (generation == p.generation()).then_some(link))
    }

    /// Like [ChainArenaTrait::get_link_no_gen], except generation counters are
    /// ignored and the existing generation is returned.
    fn get_inx_link_no_gen(&self, p: P::Inx) -> Option<(P::Gen, &LinkNoGen<P, T>)>;

    /// Returns if `p_prev` and `p_next` are neighbors on the same chain, such
    /// that `self.get_link(p_prev).unwrap().next() == Some(p_next)` or
    /// `self.get_link(p_next).unwrap().prev() == Some(p_prev)`. Note that
    /// `self.are_neighbors(p0, p1)` is not necessarily equal to
    /// `self.are_neighbors(p1, p0)` because of the directionality. This
    /// function returns true for the single link cyclic chain case with
    /// `p0 == p1`. Additionally returns `false` if `p_prev` or `p_next` are
    /// invalid `Ptr`s.
    ///
    /// Incurs only one internal lookup because of invariants.
    fn are_neighbors(&self, p_prev: P, p_next: P) -> bool {
        if let Some(link) = self.get_link_no_gen(p_prev)
            && let Some(p) = link.next()
        {
            //  if equal,`p_next` must implicitly exist because of invariants
            p == p_next.inx()
        } else {
            false
        }
    }

    /// The same as [ChainNoGenArena::are_neighbors] but generation counters are
    /// ignored
    fn are_neighbors_inx(&self, p_prev: P::Inx, p_next: P::Inx) -> bool {
        if let Some((_, link)) = self.get_inx_link_no_gen(p_prev)
            && let Some(p) = link.next()
        {
            //  if equal,`p_next` must implicitly exist because of invariants
            p == p_next
        } else {
            false
        }
    }

    /// Inserts `t` into the arena and returns a `Ptr` to it. Returns an error
    /// if there was no available capacity or if the requirements of `kind` are
    /// not met.
    fn insert_within_capacity(
        &mut self,
        kind: LinkInsertKind<P>,
        t: T,
    ) -> Result<P, ChainInsertionError> {
        let entry = self.entry_insert_within_capacity(kind)?;
        let p = entry.ptr();
        entry.insert(t);
        Ok(p)
    }

    /// Inserts `t` into the arena and returns a `Ptr` to it. Automatically
    /// reallocates if needing more capacity. Returns the `t`
    /// if an allocation error occurs, if [ArenaTrait::max_capacity] is used
    /// up, or if the requirements of `kind` are not met.
    fn insert_reallocating(
        &mut self,
        kind: LinkInsertKind<P>,
        t: T,
    ) -> Result<P, ChainInsertionError> {
        let entry = self.entry_insert_reallocating(kind)?;
        let p = entry.ptr();
        entry.insert(t);
        Ok(p)
    }

    /// Inserts `t` into the arena and returns a `Ptr` to it. Panics if an
    /// allocation error occurs or if [ArenaTrait::max_capacity] is used up.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure when needing to extend
    /// capacity, or if `self.len()` is at the maximum capacity, or if the
    /// requirements of `kind` are not met.
    #[track_caller]
    fn insert(&mut self, kind: LinkInsertKind<P>, t: T) -> P {
        self.insert_reallocating(kind, t)
            .expect("`ArenaInsertTrait::insert_reallocating` failed")
    }

    /// If capacity is available and the requirements for the `kind` are met, an
    /// insertion entry for inserting a new link into the arena is returned.
    /// Returns an error if there was no available capacity, or some
    /// requirement was not met.
    fn entry_insert_within_capacity(
        &mut self,
        kind: LinkInsertKind<P>,
    ) -> Result<Self::InsertionEntry<'_>, ChainInsertionError>;

    /// The same as [ChainArenaTrait::entry_insert_within_capacity] but
    /// automatically reallocating if necessary with the same semantics as other
    /// `*_reallocating` functions.
    fn entry_insert_reallocating(
        &mut self,
        kind: LinkInsertKind<P>,
    ) -> Result<Self::InsertionEntry<'_>, ChainInsertionError> {
        match handle_reallocation(self) {
            Ok(()) => self.entry_insert_within_capacity(kind),
            Err(ReallocationError::AllocError) => Err(ChainInsertionError::AllocError),
            Err(ReallocationError::BeyondMaxCapacity) => {
                Err(ChainInsertionError::BeyondMaxCapacity)
            }
        }
    }

    /// The same as [ChainArenaTrait::entry_insert_reallocating], but panics
    /// if an error occurs
    ///
    /// # Panics
    ///
    /// This function can panic on failures of
    /// [ChainArenaTrait::entry_insert_reallocating]
    #[track_caller]
    fn entry_insert(&mut self, kind: LinkInsertKind<P>) -> Self::InsertionEntry<'_> {
        self.entry_insert_reallocating(kind)
            .expect("`ChainArenaTrait::entry_insert_reallocating` failed")
    }

    /// Connects the interlinks of `p_prev` and `p_next` such that `p_prev` will
    /// be previous to `p_next`. Returns `None` if `p_prev` has an existing next
    /// interlink, `p_next` has an existing previous interlink, or the pointers
    /// are invalid.
    #[must_use]
    fn connect(&mut self, p_prev: P, p_next: P) -> Option<()>;

    /// Breaks the previous interlink of `p`. Returns `None` if `p` is invalid
    /// or does not have an existing prev link.
    #[must_use]
    fn break_prev(&mut self, p: P) -> Option<()>;

    /// Breaks the next interlink of `p`. Returns `None` if `p` is invalid or
    /// does not have an existing next link.
    #[must_use]
    fn break_next(&mut self, p: P) -> Option<()>;

    /// Exchanges the endpoints of the interlinks right after `p0` and `p1`.
    /// Returns `None` if the links do not have next interlinks or if the
    /// pointers are invalid.
    ///
    /// An interesting property of this function when applied to cyclic chains,
    /// is that `exchange_next` on two `Ptr`s of the same cyclic chain always
    /// results in two cyclic chains (except for if `p0 == p1`), and
    /// `exchange_next` on two `Ptr`s of two separate cyclic chains always
    /// results in a single cyclic chain. This is used by [SurjectArena] to
    /// efficiently track and merge sets of nodes.
    #[must_use]
    fn exchange_next(&mut self, p0: P, p1: P) -> Option<()>;

    /*
    /// Efficiently removes the entire chain that `p` is connected to (which
    /// might only include itself). Returns `None` if `p` is not valid.
    fn drain_chain(&mut self, p: P) -> Option<impl Iterator<Item = InvalidationOption<(P, T)>>>;
    */
}

/*
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
