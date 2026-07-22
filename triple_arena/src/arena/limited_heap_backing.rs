//! This is a safer implementation of the heap backing for reference

use core::{cmp::min, num::NonZeroUsize};

use crate::{
    AllocError, NotWithinCapacityError, ReallocationError,
    arena::NonZeroInxVec,
    utils::{
        NonZeroInxVecPushEntry,
        traits::{NonZeroInxGenericStack, NonZeroInxGenericStackPushEntryTrait, SetMaxCapacity},
    },
};

/// The standard heap-based limited `max_capacity` implementation of
/// [NonZeroInxGenericStack]
pub struct NonZeroInxLimitedVec<T> {
    v: NonZeroInxVec<T>,
    // N.B. it happens that the current impl of `Vec` as of writing has the ability to exactly
    // allocate with `reserve_exact` but this is not a guaranteed behavior into the future.
    // `min(v.capacity(), max_capacity)` is used as the actual virtual capacity.
    max_capacity: usize,
}

impl<T> SetMaxCapacity for NonZeroInxLimitedVec<T> {
    fn set_max_capacity(&mut self, max_capacity: usize) -> Option<()> {
        if max_capacity < self.capacity() {
            None
        } else {
            self.max_capacity = max_capacity;
            Some(())
        }
    }
}

pub struct NonZeroInxLimitedVecPushEntry<'a, T> {
    this: NonZeroInxVecPushEntry<'a, T>,
}

impl<'a, T> NonZeroInxGenericStackPushEntryTrait<'a, T> for NonZeroInxLimitedVecPushEntry<'a, T> {
    fn inx(&self) -> NonZeroUsize {
        self.this.inx()
    }

    fn push(self, t: T) {
        self.this.push(t);
    }
}

// Safety: we follow the requirements of the trait
unsafe impl<T> NonZeroInxGenericStack<T> for NonZeroInxLimitedVec<T> {
    type PushEntry<'a>
        = NonZeroInxLimitedVecPushEntry<'a, T>
    where
        Self: 'a;

    fn new() -> Self {
        Self {
            v: NonZeroInxVec::new(),
            max_capacity: 0,
        }
    }

    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError> {
        Ok(Self {
            v: NonZeroInxVec::with_min_capacity(min_capacity)?,
            max_capacity: 0,
        })
    }

    fn len(&self) -> usize {
        self.v.len()
    }

    fn capacity(&self) -> usize {
        min(self.v.capacity(), self.max_capacity)
    }

    fn max_capacity(&self) -> Option<usize> {
        Some(self.max_capacity)
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), ReallocationError> {
        if min_capacity > self.max_capacity {
            return Err(ReallocationError::BeyondMaxCapacity);
        }
        self.v.reallocate_min_capacity(min_capacity)
    }

    fn entry_push_within_capacity(
        &mut self,
    ) -> Result<Self::PushEntry<'_>, NotWithinCapacityError> {
        // extra condition needed to avoid exceeding virtual capacity
        if self.v.len() == self.max_capacity {
            return Err(NotWithinCapacityError);
        }
        Ok(NonZeroInxLimitedVecPushEntry {
            this: self.v.entry_push_within_capacity()?,
        })
    }

    unsafe fn get_unchecked(&self, inx: NonZeroUsize) -> &T {
        unsafe { self.v.get_unchecked(inx) }
    }

    unsafe fn get_unchecked_mut(&mut self, inx: NonZeroUsize) -> &mut T {
        unsafe { self.v.get_unchecked_mut(inx) }
    }

    unsafe fn get_disjoint_unchecked_mut<const N: usize>(
        &mut self,
        indices: [NonZeroUsize; N],
    ) -> [&mut T; N] {
        unsafe { self.v.get_disjoint_unchecked_mut(indices) }
    }

    fn pop(&mut self) -> Option<T> {
        self.v.pop()
    }

    fn clear(&mut self) {
        self.v.clear()
    }
}
