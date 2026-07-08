use core::{error::Error, fmt, num::NonZeroUsize};

use crate::utils::PtrInx;

/// Shorthand for `PtrInx::new(NonZeroUsize::new_unchecked(x))`.
///
/// # Safety
///
/// `x` must not be 0 and must be within the `PtrInx` limits
pub unsafe fn ptrinx_unchecked<P: PtrInx>(x: usize) -> P {
    PtrInx::new(unsafe { NonZeroUsize::new_unchecked(x) })
}

// TODO
/// Placeholder until `allocator_api` stabilizes
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct AllocError;

impl fmt::Display for AllocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("memory allocation failed")
    }
}

impl Error for AllocError {}

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

/// Starts from 1
#[inline]
pub fn nzusize_iter(end_inclusive: Option<NonZeroUsize>) -> IntoNonZeroUsizeIterator {
    IntoNonZeroUsizeIterator(NonZeroUsizeIterator {
        current: NonZeroUsize::new(1).unwrap(),
        end_inclusive,
    })
}
