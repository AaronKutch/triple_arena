use alloc::vec::Vec;
use core::num::NonZeroUsize;

/// Shorthand for `NonZeroUsize::new_unchecked(x)`, and has a debug assertion
/// that the input is not zero.
///
/// # Safety
///
/// `x` must not be 0
pub const unsafe fn nzusize_unchecked(x: usize) -> NonZeroUsize {
    if let Some(nz) = NonZeroUsize::new(x) {
        nz
    } else {
        panic!();
    }
}

pub const NZONE: NonZeroUsize = unsafe { nzusize_unchecked(1) };

#[derive(Clone)]
pub struct NonZeroInxVec<T> {
    v: Vec<T>,
}

impl<T> NonZeroInxVec<T> {
    pub const fn new() -> Self {
        Self { v: Vec::new() }
    }

    pub fn capacity(&self) -> usize {
        self.v.capacity()
    }

    pub fn len(&self) -> usize {
        self.v.len()
    }

    pub fn is_empty(&self) -> bool {
        self.v.is_empty()
    }

    pub fn reserve(&mut self, additional: usize) {
        self.v.reserve(additional)
    }

    pub fn clear(&mut self) {
        self.v.clear()
    }

    pub fn clear_and_shrink(&mut self) {
        self.v.clear();
        self.v.shrink_to_fit();
    }

    pub fn push(&mut self, t: T) {
        self.v.push(t)
    }

    #[allow(dead_code)]
    pub fn pop(&mut self) -> Option<T> {
        self.v.pop()
    }

    pub fn get(&self, inx: NonZeroUsize) -> Option<&T> {
        self.v.get(inx.get().wrapping_sub(1))
    }

    pub fn get_mut(&mut self, inx: NonZeroUsize) -> Option<&mut T> {
        self.v.get_mut(inx.get().wrapping_sub(1))
    }

    pub fn get2_mut(&mut self, inx0: NonZeroUsize, inx1: NonZeroUsize) -> Option<(&mut T, &mut T)> {
        if (inx0 == inx1) || (inx0.get() > self.len()) || (inx1.get() > self.len()) {
            None
        } else {
            let i0 = inx0.get().wrapping_sub(1);
            let i1 = inx1.get().wrapping_sub(1);
            let res = if i0 < i1 {
                let (lhs, rhs) = self.v.split_at_mut(i1);
                Some((&mut lhs[i0], &mut rhs[0]))
            } else {
                let (lhs, rhs) = self.v.split_at_mut(i0);
                Some((&mut rhs[0], &mut lhs[i1]))
            };
            res
        }
    }

    pub fn shrink_to_fit(&mut self) {
        self.v.shrink_to_fit();
    }

    pub fn nziter(&self) -> IntoNonZeroUsizeIterator {
        nzusize_iter(NZONE, self.len())
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
