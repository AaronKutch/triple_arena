use core::{
    borrow::Borrow,
    fmt, mem,
    num::NonZeroUsize,
    ops::{Index, IndexMut},
};

use crate::{
    InvalidationOption, InvalidationResult,
    arena::ArenaBacking,
    traits::{ArenaCloneFromWith, ArenaTrait, Ptr, SetMaxCapacity},
    utils::traits::{NonZeroInxGenericStack, PtrGen, PtrInx},
};

// See REF(arena_terminology)

/// Internal slot for an one-way linked freelist arena. Note the `P::Gen` is a
/// ZST in logically generationless cases, and there are niches in both if
/// `NonZero*` is being used like it should.
#[derive(Clone)]
pub enum InternalSlot<P: Ptr, T> {
    /// A free slot with no `T`. This index points to the next free slot (and it
    /// is encoded as a `P::Inx` which can be smaller than a `usize`, this is
    /// safe because its limitations are the same as the limitations that could
    /// have pushed an allocated slot in the first case), except if it
    /// points to the self slot in which case it is the last free slot.
    Free(P::Inx),
    /// A slot allocated for a `(P::Gen, T)` pair in the arena.
    Allocated(P::Gen, T),
}

use InternalSlot::*;

/// An arena supporting non-Clone `T` (`T` has no requirements other than
/// `Sized`, but some traits are only active if `T` implements them), deletion,
/// and optional generation counters.
///
/// `P` is a struct implementing `Ptr`, which has associated types for
/// determining what the arena's indexes and generation counters should be.
/// When using multiple arenas, it is encouraged to use different `P` in order
/// to have the type system guard against confusion and mistakenly using
/// pointers from one arena in another. The arena will use generation counters
/// to check for invalidated pointers if `P` has a generation counter.
///
/// See also the documentation on [ArenaTrait].
///
/// ```
/// use triple_arena::{Arena, ptr_struct, traits::*};
///
/// // In implementations that always use valid indexes and only want the
/// // generation counter in debug mode, we can use `cfg`s like this:
/// /* // commented out because of doc tests
/// #[cfg(Debug)]
/// ptr_struct!(P0);
/// #[cfg(Debug)]
/// ptr_struct!(Q2);
/// #[cfg(not(Debug))]
/// ptr_struct!(P0());
/// #[cfg(not(Debug))]
/// ptr_struct!(Q2());
/// */
/// ptr_struct!(P0);
/// ptr_struct!(Q2);
///
/// // By convention we use short names for `Ptr` structs beginning with `P`,
/// // `Q`, or `R`. In simple contexts we add a single digit to differentiate
/// // the generic `P: Ptr` from a instantiated `P0`. If the number of arenas
/// // exceeds a small number or the types will be public, you should use more
/// // descriptive names like `PNode`, `PComponent`, `PNameOfEntryKind`, etc.
///
/// let mut arena: Arena<P0, String> = Arena::new();
///
/// let test_ptr: P0 = arena.insert("test".to_string());
/// let hello_ptr: P0 = arena.insert("hello".to_string());
///
/// // Nice debug representations. See also the `triple_arena_render` crate for
/// // trait-based rendering of graphs. Note that the internal indexes are
/// // starting at 1 because `NonZero` types are used. This allows for memory
/// // niche optimizations of `Option<P>` and other such things.
/// assert_eq!(
///     &format!("{:?}", arena),
///     "{P0[1](2): \"test\", P0[2](2): \"hello\"}"
/// );
///
/// // use the `Ptr`s we got from insertion to reference the stored data
/// assert_eq!(arena[hello_ptr], "hello");
///
/// // Remove objects. The `Arena` uses internal freelists to keep the capacity
/// // for future inserts to reuse. Invalidation functions like
/// // `ArenaTrait::remove` return an `InvalidationResult` or
/// // `InvalidationOption` that allow checking for generation overflow. For
/// // most use cases with the default generation counter size, however, you
/// // should just use `.allow()` to allow generation overflow because it is
/// // practically impossible to reach.
/// let removed = arena.remove(test_ptr).allow().unwrap();
/// assert_eq!(removed, "test");
///
/// // When using generation counters, invalidated pointers are guaranteed to
/// // never work again.
/// assert!(arena.get(test_ptr).is_none());
///
/// // Using different `Ptr` generics is extremely useful in complicated
/// // multiple arena code with self pointers and inter-arena pointers. This is
/// // an arena storing a tuple of pointers that work on the first arena and
/// // itself.
/// let mut arena2: Arena<Q2, (P0, Q2)> = Arena::new();
///
/// let p2_ptr: Q2 = arena2.insert((hello_ptr, Ptr::invalid()));
/// let another: Q2 = arena2.insert((hello_ptr, p2_ptr));
///
/// // With many arena crates, no compile time or runtime checks would prevent
/// // you from using the wrong pointers. Here, the compiler protects us.
/// // error: expected struct `P0`, found struct `Q2`
/// //let _ = arena.get(p2_ptr);
///
/// assert_eq!(arena[arena2[p2_ptr].0], "hello");
///
/// // In cases where we are forced to have the same `Ptr` struct, we can still
/// // have type guards against semantically different `Ptr`s by using generics:
/// fn example<P0: Ptr, P1: Ptr, T>(a0: &mut Arena<P0, T>, a1: &mut Arena<P1, T>, p1: P1) {
///     // error: expected type parameter `P0`, found type parameter `P1`
///     //let _ = a0.remove(p1);
///
///     a0.insert(a1.remove(p1).allow().unwrap());
/// }
///
/// let mut arena3: Arena<Q2, String> = Arena::new();
/// example(&mut arena3, &mut arena, hello_ptr);
/// assert_eq!(arena3.iter().next().unwrap().1, "hello");
/// ```
///
/// Note: See the `triple_arena_render` crate for a trait-based way to visualize
/// graph structures in `Arena`s
pub struct Arena<
    P: Ptr,
    T,
    #[cfg(feature = "alloc")] B: ArenaBacking = crate::arena::HeapBacking,
    #[cfg(not(feature = "alloc"))] B: ArenaBacking,
> {
    /// # Invariants
    ///
    /// - If there are free slots, all free slots have their freelist nodes in a
    ///   single linked list with the start being pointed to by `freelist_root`
    ///   and the end pointing to itself
    /// - If there are no free slots, `freelist_root` is `None`
    ///
    /// # Soft Invariants
    ///
    /// - The generation value starts at 2 in a new Arena, so that the
    ///   `Ptr::invalid` function works
    /// - During an invalidation operation, the arena `generation` is
    ///   incremented _and_ the allocation in question is turned into a `Free`,
    ///   or has its generation updated to equal the arena's `generation`. Newer
    ///   allocations must use the new `generation` value.
    pub(crate) m: B::Stack<InternalSlot<P, T>>,
    pub(crate) len: usize,
    /// Points to the root of the chain of freelist nodes
    pub(crate) freelist_root: Option<P::Inx>,
    pub(crate) generation: P::Gen,
}

// FIXME restrict visibility above to pub(in arena) and check other structs

impl<P: Ptr, T, B: ArenaBacking> Arena<P, T, B> {
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
        if this.generation() < P::Gen::two() {
            return Err("bad generation");
        }
        if this.capacity() != this.m.capacity() {
            return Err("virtual capacity != m.capacity()");
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
        let n_free = this.m.len().wrapping_sub(n_allocated);
        if (n_free == 0) != this.freelist_root.is_none() {
            return Err("bad freelist_root");
        }
        // checking freelist integrity
        let mut freelist_len = 0usize;
        if let Some(root) = this.freelist_root {
            let mut tmp_inx = root;
            for i in 0.. {
                let Some(p) = P::Inx::try_into_usize(tmp_inx) else {
                    return Err("try_into_usize failed");
                };
                let Some(entry) = this.m.get(p) else {
                    return Err("getting entry failed");
                };
                if let Free(inx) = entry {
                    freelist_len = freelist_len.checked_add(1).unwrap();
                    if *inx == tmp_inx {
                        // last one
                        break;
                    }
                    tmp_inx = *inx;
                } else {
                    return Err("bad freelist node");
                }
                if i > this.m.len() {
                    return Err("endless loop");
                }
            }
        }
        if freelist_len != n_free {
            return Err("freelist discontinuous");
        }
        Ok(())
    }

    // FIXME we may want `unreachable` for assembly perf, see u32 Ptr case

    /// We assume that if a slot has been successfully pushed before (implying
    /// that `P::Inx::try_from_usize` has succeeded with this exact value
    /// before), then passing the same raw index again to this will not fail,
    /// this function is to check places where this assumption happens
    pub(crate) fn from_checked(inx: NonZeroUsize) -> P::Inx {
        <P::Inx as PtrInx>::try_from_usize(inx).expect(
            "`<P::Inx as PtrInx>::try_from_usize` failed on a value that has succeeded before",
        )
    }

    pub(crate) fn into_checked(inx: P::Inx) -> NonZeroUsize {
        <P::Inx as PtrInx>::try_into_usize(inx).expect(
            "`<P::Inx as PtrInx>::try_into_usize` failed on a value that has succeeded before",
        )
    }

    /// Pops off free slots on the end, and rebuilds the freelist so it is
    /// ordered to allocate from the earliest free slot forwards
    pub(crate) fn canonicalize_free_list(&mut self) {
        // remove free slots off the end
        for inx in self.nziter().into_iter().rev() {
            if let Free(_) = self.m.get(inx).unwrap() {
                self.m.pop();
            } else {
                break;
            }
        }

        let mut earliest_free = None;
        for inx in self.nziter().into_iter().rev() {
            if let Free(overwrite) = self.m.get_mut(inx).unwrap() {
                if let Some(next) = earliest_free {
                    // point to the next free slot, the last one we encountered
                    *overwrite = next;
                    earliest_free = Some(Self::from_checked(inx));
                } else {
                    // point to self on first one going in reverse
                    *overwrite = Self::from_checked(inx);
                    earliest_free = Some(*overwrite);
                }
            }
        }
        // there being no free slots is automatically handled
        self.freelist_root = earliest_free;
    }

    /// `remove` but with optional generation counter increment
    pub(crate) fn remove_internal(
        &mut self,
        inx: P::Inx,
        generation: Option<P::Gen>,
        inc_gen: bool,
    ) -> InvalidationResult<T> {
        let Some(raw_inx) = P::Inx::try_into_usize(inx) else {
            return InvalidationResult::InvalidPtr;
        };
        let len = self.m.len();
        let Some(allocation) = self.m.get_mut(raw_inx) else {
            return InvalidationResult::InvalidPtr;
        };
        match allocation {
            // invalid by being already free
            Free(_) => InvalidationResult::InvalidPtr,
            Allocated(generation1, _) => {
                if let Some(generation) = generation {
                    if *generation1 != generation {
                        // invalid by generation
                        return InvalidationResult::InvalidPtr;
                    }
                }

                let old_t = if len == raw_inx.get() {
                    // Special optimization case: if this was the last slot in the stack, pop it off
                    // without touching the freelist at all. We can't efficiently keep the end
                    // canonicalized in general if using a one-way freelist (if something in the
                    // middle is freed before elements to the right are freed, it leads to free
                    // slots on the end). This decision does make a change in the deterministic
                    // behavior of this standard arena, but I think it has its own idealness if we
                    // accept stack lengths within capacities to begin with (which has uninit
                    // advantages with small lengths in large array capacities, and I _think_ it may
                    // be necessary to prevent the REF(exponential_double_buffer_blowup) problem).
                    // If deterministic compatibility needs to be a thing again (and I don't think
                    // it will ever since we introduced `ArenaDirectInsertTrait` mirror arenas), I
                    // don't see it being difficult to follow this case.
                    let Allocated(_, old_t) = self.m.pop().unwrap() else {
                        unreachable!()
                    };
                    old_t
                } else {
                    let freelist_ptr = if let Some(free) = self.freelist_root {
                        // points to previous root
                        free
                    } else {
                        // points to itself
                        inx
                    };
                    // in both cases the new root is the slot we just freed
                    self.freelist_root = Some(inx);
                    let Allocated(_, old_t) = mem::replace(allocation, Free(freelist_ptr)) else {
                        unreachable!()
                    };
                    old_t
                };

                self.len = self.len.wrapping_sub(1);
                if inc_gen {
                    let tmp = PtrGen::generational_inc(self.generation);
                    self.generation = tmp.0;
                    if tmp.1 {
                        InvalidationResult::GenerationOverflow(old_t)
                    } else {
                        InvalidationResult::Success(old_t)
                    }
                } else {
                    InvalidationResult::Success(old_t)
                }
            }
        }
    }

    /// Returns the singular arena generation counter, the same as
    /// [crate::traits::SingularGenerationArena::singular_generation]
    #[inline]
    pub fn generation(&self) -> P::Gen {
        self.generation
    }

    /// Manually set the singular arena generation counter. This can break some
    /// soft invariants such as ABA problem prevention and `P::invalid`
    /// always being invalid with generation counters.
    pub fn set_generation(&mut self, new_gen: P::Gen) {
        self.generation = new_gen;
    }

    /// Increment the singular arena generation counter, returning if generation
    /// overflow occurred.
    pub fn inc_generation(&mut self) -> InvalidationOption<()> {
        let tmp = P::Gen::generational_inc(self.generation);
        self.generation = tmp.0;
        if tmp.1 {
            InvalidationOption::GenerationOverflow(())
        } else {
            InvalidationOption::Success(())
        }
    }

    // FIXME remove this if possible

    /// This is currently only used by `SurjectArena::compress_and_shrink_with`
    /// in a way that avoids a broken freelist.
    pub(crate) fn raw_entry_swap_special(&mut self, i0: NonZeroUsize, i1: NonZeroUsize) {
        if i0 != i1 {
            let [entry0, entry1] = self.m.get_disjoint_mut([i0, i1]).unwrap();
            mem::swap(entry0, entry1);
        }
    }

    /// Like [Arena::get], except generation counters are ignored and the
    /// result is unwrapped internally
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_unwrap(&self, p: P::Inx) -> &T {
        match self.m.get(Self::into_checked(p)) {
            Some(Allocated(_, t)) => t,
            // if we use `panic` it induces stack management on every hot path according to the
            // assembly
            _ => unreachable!(), /* panic!("get_inx_unwrap of unallocated entry"), */
        }
    }

    /// Like [Arena::get_mut], except generation counters are ignored and the
    /// result is unwrapped internally
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_mut_unwrap(&mut self, p: P::Inx) -> &mut T {
        match self.m.get_mut(Self::into_checked(p)) {
            Some(Allocated(_, t)) => t,
            _ => unreachable!(), /* panic!("get_inx_mut_unwrap of unallocated entry"), */
        }
    }

    /// Directly returns a reference to the internal backing, for the purposes
    /// of accessing `ArenaBacking`-specific functions
    pub fn backing(&self) -> &B::Stack<InternalSlot<P, T>> {
        &self.m
    }

    // at the moment we aren't using unsafe operations that would lead this to be
    // unsound (and may never because of the generics that would be problematic to
    // make `unsafe`), but messing up the freelist is essentially a memory
    // corruption issue anyways even if not causing language level UB

    /// Directly returns a mutable reference to the internal backing, for the
    /// purposes of accessing `ArenaBacking`-specific functions
    ///
    /// # Safety
    ///
    /// The `InternalEntry` allocation state must not be modified, or else the
    /// freelist or entry length could be broken.
    pub unsafe fn backing_mut(&mut self) -> &mut B::Stack<InternalSlot<P, T>> {
        &mut self.m
    }
}

impl<P: Ptr, T, B: ArenaBacking> Default for Arena<P, T, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> Index<Q> for Arena<P, T, B> {
    type Output = T;

    fn index(&self, inx: Q) -> &T {
        let p: P = *inx.borrow();
        self.get(p).expect("indexed `Arena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> IndexMut<Q> for Arena<P, T, B> {
    fn index_mut(&mut self, inx: Q) -> &mut T {
        let p: P = *inx.borrow();
        self.get_mut(p)
            .expect("indexed `Arena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T: fmt::Debug, B: ArenaBacking> fmt::Debug for Arena<P, T, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// Implemented if `T: Clone`.
impl<P: Ptr, T: Clone, B: ArenaBacking> Clone for Arena<P, T, B> {
    /// When an `Arena<P, T>` is cloned, the `P`s to an original `T` will
    /// initially be valid to the corresponding `T` in the cloned arena.
    /// Invalidations will continue independently, so the meaning of the `Ptr`
    /// with respect to the different arenas can diverge.
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
    fn clone_from(&mut self, source: &Self) {
        self.clone_from_with(source, |_, t| t.clone())
            .expect("failed when cloning arena");
    }
}

impl<P: Ptr, T, B: ArenaBacking> SetMaxCapacity for Arena<P, T, B>
where
    <B as ArenaBacking>::Stack<InternalSlot<P, T>>: SetMaxCapacity,
{
    fn set_max_capacity(
        &mut self,
        max_capacity: usize,
    ) -> Result<(), crate::MaxCapacityReductionError> {
        // If reducing below the logical `self.capacity()`, we may need to pop off free
        // slots off the end to achieve the ideal, instead of special casing it do this
        // and always call `canonicalize_free_list` for determinism idealness,
        // the reduction below capacity case is specifically special anyways by
        // the documentation of `set_max_capacity`

        // FIXME use the trait when the old capacity has been removed
        if self
            .max_capacity()
            .is_some_and(|old_max| max_capacity < old_max)
            && max_capacity < self.m.capacity()
        {
            self.canonicalize_free_list();
        }
        self.m.set_max_capacity(max_capacity)
    }
}
