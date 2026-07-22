use core::{error::Error, fmt, num::NonZeroUsize};

use crate::utils::traits::PtrInx;

// FIXME remove

/// Shorthand for `PtrInx::new(NonZeroUsize::new_unchecked(x))`.
///
/// # Safety
///
/// `x` must not be 0 and must be within the `PtrInx` limits
pub unsafe fn ptrinx_unchecked<P: PtrInx>(x: usize) -> P {
    PtrInx::try_from_usize(NonZeroUsize::new(x).unwrap()).unwrap()
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

/// The operation would not be within existing capacity
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct NotWithinCapacityError;

impl fmt::Display for NotWithinCapacityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an operation would not be within existing capacity")
    }
}

impl Error for NotWithinCapacityError {}

/// For reallocating functions
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ReallocationError {
    /// Extending the capacity further to the required amount would exceed a max
    /// capacity limit
    BeyondMaxCapacity,
    /// There was an allocation error when attempting to reallocate
    AllocError,
}

impl fmt::Display for ReallocationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReallocationError::BeyondMaxCapacity => {
                f.write_str("a max capacity limit prevents growing the capacity")
            }
            ReallocationError::AllocError => f.write_str("a memory reallocation failed"),
        }
    }
}

impl Error for ReallocationError {}

pub struct NonZeroUsizeIterator {
    // invariant: if `end_inclusive.is_some()`, `start <= end_inclusive.get()` must be true
    start: NonZeroUsize,
    end_inclusive: Option<NonZeroUsize>,
}

impl Iterator for NonZeroUsizeIterator {
    type Item = NonZeroUsize;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(end_inclusive) = self.end_inclusive {
            let res = self.start;
            // safety: this is safe since `start < end_inclusive.get()` and
            // `end_inclusive` cannot be more than the maximum, meaning it
            // cannot overflow into zero. We maintain the invariant by checking
            // for equality.
            self.start = NonZeroUsize::new(res.get().wrapping_add(1)).unwrap();
            if self.start > end_inclusive {
                self.end_inclusive = None;
            }
            Some(res)
        } else {
            None
        }
    }
}

impl DoubleEndedIterator for NonZeroUsizeIterator {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(end_inclusive) = self.end_inclusive {
            let res = end_inclusive;
            if res == self.start {
                // the range is now empty
                self.end_inclusive = None;
            } else {
                // safety: `1 <= self.start < res`, so `res.get() - 1 >= 1` and
                // cannot underflow into zero.
                self.end_inclusive = Some(NonZeroUsize::new(res.get() - 1).unwrap());
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
pub fn nzusize_iter(
    start: NonZeroUsize,
    end_inclusive: Option<NonZeroUsize>,
) -> IntoNonZeroUsizeIterator {
    if let Some(end_inclusive) = end_inclusive
        && start > end_inclusive
    {
        // must make empty
        return IntoNonZeroUsizeIterator(NonZeroUsizeIterator {
            start,
            end_inclusive: None,
        });
    }
    IntoNonZeroUsizeIterator(NonZeroUsizeIterator {
        start,
        end_inclusive,
    })
}
