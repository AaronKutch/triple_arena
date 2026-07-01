use alloc::vec::Vec;
use core::num::NonZeroUsize;

use crate::utils::{AllocError, NonZeroInxGenericStack};

#[derive(Clone)]
pub struct NonZeroInxVec<T> {
    v: Vec<T>,
}

impl<T> NonZeroInxVec<T> {
    pub const fn new() -> Self {
        Self { v: Vec::new() }
    }

    pub fn nziter(&self) -> IntoNonZeroUsizeIterator {
        nzusize_iter(unsafe { NonZeroUsize::new_unchecked(1) }, self.len())
    }
}

// Safety: we use safe ops internally and follow the requirements of the trait
unsafe impl<T> NonZeroInxGenericStack<T> for NonZeroInxVec<T> {
    fn len(&self) -> usize {
        self.v.len()
    }

    fn capacity(&self) -> usize {
        self.v.capacity()
    }

    fn capacity_limit(&self) -> Option<usize> {
        None
    }

    fn ensure_capacity(&mut self, min_capacity: usize) -> Result<(), AllocError> {
        if min_capacity > self.capacity() {
            self.v.try_reserve(min_capacity - self.len()).map_err(|_| AllocError)?;
        } else if min_capacity < self.capacity() {
            // TODO change when `try_shrink_to` is stabilized

            // the only stable way to do it
            let mut v = Vec::new();
            v.try_reserve(min_capacity).map_err(|_| AllocError)?;
            v.extend(self.v.drain(..));
            self.v = v;
        }
        Ok(())
    }

    fn push(&mut self, t: T) {
        self.v.push(t)
    }

    unsafe fn get_unchecked(&self, inx: NonZeroUsize) -> &T {
        unsafe {self.v.get_unchecked(inx.get().wrapping_sub(1))}
    }

    unsafe fn get_unchecked_mut(&mut self, inx: NonZeroUsize) -> &mut T {
        unsafe {self.v.get_unchecked_mut(inx.get().wrapping_sub(1))}
    }

    unsafe fn get_disjoint_unchecked_mut<const N: usize>(
        &mut self,
        indices: [NonZeroUsize; N],
    ) -> [&mut T; N] {
        unsafe {self.v.get_disjoint_unchecked_mut(indices.map(|inx|inx.get().wrapping_sub(1)))}
    }

    fn pop(&mut self) -> Option<T> {
        self.v.pop()
    }

    fn clear(&mut self) {
        self.v.clear()
    }

    fn clear_and_shrink(&mut self) {
        self.v.clear();
        self.v.shrink_to_fit();
    }
}

pub struct NonZeroUsizeIterator {
    // invariant: if `end_inclusive.is_some()`, `current <= end_inclusive.get()` must be true
    current: NonZeroUsize,
    end_inclusive: Option<NonZeroUsize>,
}

impl Iterator for NonZeroUsizeIterator {
    type Item = NonZeroUsize;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(end_inclusive) = self.end_inclusive {
            let res = self.current;
            // safety: this is safe since `current < end_inclusive.get()` and
            // `end_inclusive` cannot be more than the maximum, meaning it
            // cannot overflow into zero. We maintain the invariant by checking
            // for equality.
            self.current = NonZeroUsize::new(res.get().wrapping_add(1)).unwrap();
            if self.current > end_inclusive {
                self.end_inclusive = None;
            }
            Some(res)
        } else {
            None
        }
    }
}

pub struct IntoNonZeroUsizeIterator(NonZeroUsizeIterator);

impl IntoIterator for IntoNonZeroUsizeIterator {
    type IntoIter = NonZeroUsizeIterator;
    type Item = NonZeroUsize;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0
    }
}

#[inline]
pub const fn nzusize_iter(start: NonZeroUsize, end_inclusive: usize) -> IntoNonZeroUsizeIterator {
    // we do it this way for better branching
    let end = if start.get() > end_inclusive {
        None
    } else {
        // Safety: if `start` is `NonZeroUsize`, and `start <= end_inclusive`, then
        // `end_inclusive` must be at least 1
        let tmp = NonZeroUsize::new(end_inclusive);
        assert!(tmp.is_some());
        tmp
    };
    IntoNonZeroUsizeIterator(NonZeroUsizeIterator {
        current: start,
        end_inclusive: end,
    })
}

impl<T> Default for NonZeroInxVec<T> {
    fn default() -> Self {
        Self::new()
    }
}
