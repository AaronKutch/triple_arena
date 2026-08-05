use core::{
    borrow::Borrow,
    fmt, mem,
    num::NonZeroUsize,
    ops::{Index, IndexMut},
};

use crate::{
    errors::MaxCapacityReductionError,
    traits::{ArenaTrait, Ptr, SetMaxCapacity},
    utils::{
        from_checked_ptr,
        traits::{ArenaBacking, NonZeroInxGenericStack, PtrInx},
    },
};

// See REF(arena_terminology)

/// Internal slot for a freelist-less direct insertion arena. Note the `P::Gen`
/// is a ZST in logically generationless cases.
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
/// state of another arena.
///
/// Note that [ArenaTrait::invalidate] and the compress functions leave
/// generations unchanged. No generation overflow can occur from any operations
/// on this arena.
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
        Ok(())
    }

    /// Pops off free slots on the end
    pub(crate) fn canonicalize_free_slots(&mut self) {
        // remove free slots off the end
        for inx in self.nziter().into_iter().rev() {
            if let Free = self.m.get(inx).unwrap() {
                self.m.pop();
            } else {
                break;
            }
        }
    }

    #[must_use]
    pub(crate) fn remove_internal(
        &mut self,
        inx: P::Inx,
        generation: Option<P::Gen>,
    ) -> Option<(P::Gen, T)> {
        let raw_inx = P::Inx::try_into_usize(inx)?;
        let allocation = self.m.get_mut(raw_inx)?;
        match allocation {
            Free => None,
            Allocated(generation1, _) => {
                if let Some(generation) = generation {
                    if *generation1 != generation {
                        // invalid by generation
                        return None;
                    }
                }

                let Allocated(generation, t) = mem::replace(allocation, Free) else {
                    unreachable!()
                };

                Some((generation, t))
            }
        }
    }

    /// Like [ArenaTrait::get], except generation counters are ignored and the
    /// result is unwrapped internally
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
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_mut_unwrap(&mut self, p: P::Inx) -> &mut T {
        match self.m.get_mut(from_checked_ptr::<P>(p)) {
            Some(Allocated(_, t)) => t,
            _ => unreachable!(), /* panic!("get_inx_mut_unwrap of unallocated entry"), */
        }
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
    /// The `InternalEntry` allocation state must not be modified, or else the
    /// entry length could be broken.
    pub unsafe fn backing_mut(&mut self) -> &mut B::Stack<DirectSlot<P, T>> {
        &mut self.m
    }
}

impl<P: Ptr, T, B: ArenaBacking> Default for DirectArena<P, T, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> Index<Q> for DirectArena<P, T, B> {
    type Output = T;

    fn index(&self, inx: Q) -> &T {
        let p: P = *inx.borrow();
        self.get(p)
            .expect("indexed `DirectArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> IndexMut<Q> for DirectArena<P, T, B> {
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

// FIXME
/*
/// Implemented if `T: Clone`.
impl<P: Ptr, T: Clone, B: ArenaBacking> Clone for DirectArena<P, T, B> {
    /// When a `DirectArena<P, T>` is cloned, the `P`s to an original `T` will
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
*/

impl<P: Ptr, T, B: ArenaBacking> SetMaxCapacity for DirectArena<P, T, B>
where
    <B as ArenaBacking>::Stack<DirectSlot<P, T>>: SetMaxCapacity,
{
    fn set_max_capacity(&mut self, max_capacity: usize) -> Result<(), MaxCapacityReductionError> {
        // If reducing below the logical `self.capacity()`, we may need to pop off free
        // slots off the end to achieve the ideal, instead of special casing it do this
        // and always call `canonicalize_free_slots` for determinism idealness,
        // the reduction below capacity case is specifically special anyways by
        // the documentation of `set_max_capacity`

        if self
            .max_capacity()
            .is_some_and(|old_max| max_capacity < old_max)
            && max_capacity < self.capacity()
        {
            self.canonicalize_free_slots();
        }
        self.m.set_max_capacity(max_capacity)
    }
}
