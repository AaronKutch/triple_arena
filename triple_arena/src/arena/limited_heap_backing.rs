//! This is a safer implementation of the heap backing for reference

use core::num::NonZeroUsize;

use crate::{
    arena::NonZeroInxVec,
    fundamental::SettableCapacityLimit,
    utils::{AllocError, NonZeroInxGenericStack},
};

/// The standard heap-based limited `capacity_limit` implementation of
/// [NonZeroInxGenericStack]
pub struct NonZeroInxLimitedVec<T> {
    v: NonZeroInxVec<T>,
    limit: usize,
}

impl<T> SettableCapacityLimit for NonZeroInxLimitedVec<T> {
    /// Changes the capacity limit to `limit`
    fn set_capacity_limit(&mut self, limit: usize) {
        self.limit = limit;
    }
}

// Safety: we use safe ops internally and follow the requirements of the trait
unsafe impl<T> NonZeroInxGenericStack<T> for NonZeroInxLimitedVec<T> {
    fn new() -> Self {
        Self {
            v: NonZeroInxVec::new(),
            limit: 0,
        }
    }

    fn len(&self) -> usize {
        self.v.len()
    }

    fn capacity(&self) -> usize {
        self.v.capacity()
    }

    fn capacity_limit(&self) -> Option<usize> {
        Some(self.limit)
    }

    fn ensure_capacity(&mut self, min_capacity: usize) -> Result<(), AllocError> {
        // always check, the limit may have been manually changed to be below
        // `self.capacity()`
        if min_capacity > self.limit {
            return Err(AllocError);
        }
        self.v.ensure_capacity(min_capacity)
    }

    fn push(&mut self, t: T) -> Result<(NonZeroUsize, &mut T), T> {
        self.v.push(t)
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

    fn clear_and_shrink(&mut self) {
        self.v.clear_and_shrink();
    }
}
