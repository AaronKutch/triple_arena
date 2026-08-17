use alloc::vec::Vec;
use core::num::NonZeroUsize;

use crate::{
    errors::{AllocError, NotWithinCapacityError, ReallocationError},
    utils::traits::{NonZeroInxGenericStack, NonZeroInxGenericStackPushEntryTrait},
};

// Note: an older version of `triple_arena` had manually managed allocations and
// an extreme microoptimization where we pre-offset the allocation pointer so
// that `get`s etc only need a single addition in machine code to arrive at the
// destination address. But on most architectures, even RISC-V, they can have an
// immediate offset to their loads and zero instructions are saved. Also, it
// precluded `NonNull` optimizations from existing on the struct.

/// The standard heap-based unlimited `max_capacity` implementation of
/// [NonZeroInxGenericStack]
pub struct NonZeroInxVec<T> {
    v: Vec<T>,
}

/// The [NonZeroInxVec] implementation of
/// [NonZeroInxGenericStackPushEntryTrait]
#[must_use]
pub struct NonZeroInxVecPushEntry<'a, T> {
    this: &'a mut NonZeroInxVec<T>,
}

impl<'a, T> NonZeroInxGenericStackPushEntryTrait<'a, T> for NonZeroInxVecPushEntry<'a, T> {
    fn inx(&self) -> NonZeroUsize {
        // note this assumes that `push` is the only other mutable function
        // Safety: overflow from pushing was checked for before creating the entry
        unsafe { NonZeroUsize::new_unchecked(self.this.v.len().wrapping_add(1)) }
    }

    fn push(self, t: T) {
        let this = self.this;
        this.v.push(t);
    }
}

// Safety: we follow the requirements of the trait
unsafe impl<T> NonZeroInxGenericStack<T> for NonZeroInxVec<T> {
    type PushEntry<'a>
        = NonZeroInxVecPushEntry<'a, T>
    where
        Self: 'a;

    fn new() -> Self {
        Self { v: Vec::new() }
    }

    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError> {
        // TODO change when `try_with_capacity` is stabilized

        // the only stable way to do it
        let mut v = Vec::new();
        v.try_reserve(min_capacity).map_err(|_| AllocError)?;
        Ok(Self { v })
    }

    fn len(&self) -> usize {
        self.v.len()
    }

    fn capacity(&self) -> usize {
        self.v.capacity()
    }

    fn max_capacity(&self) -> Option<usize> {
        None
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), ReallocationError> {
        if min_capacity > self.capacity() {
            self.v
                .try_reserve(min_capacity.wrapping_sub(self.len()))
                .map_err(|_| ReallocationError::AllocError)?;
        } else if min_capacity < self.capacity() {
            // TODO change when `try_shrink_to` is stabilized

            // the only stable way to do it
            let mut v = Vec::new();
            // N.B. we must raise the capacity to at least `self.v.len()`, otherwise the
            // `append` will try to reallocate internally
            v.try_reserve(min_capacity.max(self.v.len()))
                .map_err(|_| ReallocationError::AllocError)?;
            v.append(&mut self.v);
            self.v = v;
        }
        Ok(())
    }

    fn entry_push_within_capacity(
        &mut self,
    ) -> Result<Self::PushEntry<'_>, NotWithinCapacityError> {
        if self.v.len() < self.v.capacity() {
            Ok(NonZeroInxVecPushEntry { this: self })
        } else {
            Err(NotWithinCapacityError)
        }
    }

    unsafe fn get_unchecked(&self, inx: NonZeroUsize) -> &T {
        unsafe { self.v.get_unchecked(inx.get().wrapping_sub(1)) }
    }

    unsafe fn get_unchecked_mut(&mut self, inx: NonZeroUsize) -> &mut T {
        unsafe { self.v.get_unchecked_mut(inx.get().wrapping_sub(1)) }
    }

    unsafe fn get_disjoint_unchecked_mut<const N: usize>(
        &mut self,
        indices: [NonZeroUsize; N],
    ) -> [&mut T; N] {
        unsafe {
            self.v
                .get_disjoint_unchecked_mut(indices.map(|inx| inx.get().wrapping_sub(1)))
        }
    }

    fn pop(&mut self) -> Option<T> {
        self.v.pop()
    }

    fn clear(&mut self) {
        self.v.clear()
    }
}
