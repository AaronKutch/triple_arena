use core::{error::Error, fmt, num::NonZeroUsize};

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

/// Indicates that the max capacity limit could not be reduced, because the
/// capacity would also need to be reduced to equal it, and the capacity could
/// not be reduced in this case
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct MaxCapacityReductionError;

impl fmt::Display for MaxCapacityReductionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(
            "the max capacity limit could not be reduced, because the capacity would also need to \
             be reduced to equal it, and the capacity could not be reduced in this case",
        )
    }
}

impl Error for MaxCapacityReductionError {}

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
            Self::BeyondMaxCapacity => {
                f.write_str("a max capacity limit prevents growing the capacity")
            }
            Self::AllocError => f.write_str("a memory reallocation failed"),
        }
    }
}

impl Error for ReallocationError {}

/// For direct insertion arenas
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum DirectInsertionError {
    /// The index points to an internal slot that does not fit within existing
    /// capacity
    NotWithinCapacity,
    /// There is already an element existing at the index that would be directly
    /// inserted into
    ExistingElementAtIndex,
}

impl fmt::Display for DirectInsertionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotWithinCapacity => f.write_str(
                "a direct insertion index points to an internal slot that does not fit within \
                 existing capacity",
            ),
            Self::ExistingElementAtIndex => f.write_str(
                "a direct insertion index points to an internal slot where there is already an \
                 existing element",
            ),
        }
    }
}

impl Error for DirectInsertionError {}

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

#[inline]
pub fn nzusize_iter(
    start: NonZeroUsize,
    end_inclusive: Option<NonZeroUsize>,
) -> IntoNonZeroUsizeIterator {
    if let Some(end_inclusive) = end_inclusive {
        if start > end_inclusive {
            // must make empty
            return IntoNonZeroUsizeIterator(NonZeroUsizeIterator {
                start,
                end_inclusive: None,
            });
        }
    }
    IntoNonZeroUsizeIterator(NonZeroUsizeIterator {
        start,
        end_inclusive,
    })
}
