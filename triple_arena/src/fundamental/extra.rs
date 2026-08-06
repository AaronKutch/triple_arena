use core::num::NonZeroUsize;

/// Returned from operations that are infallible but could involve generation
/// overflow
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
#[must_use]
pub enum InvalidationOption<T> {
    /// The operation was successful without generation counter overflow
    Success(T),
    /// The operation was completed successfully, except that a generation
    /// counter overflowed
    GenerationOverflow(T),
}

// FIXME scan through and update based on these methods

impl<T> InvalidationOption<T> {
    /// If `matches!(self, Self::Success(_))`
    pub fn is_success(&self) -> bool {
        matches!(self, Self::Success(_))
    }

    /// If `matches!(self, Self::GenerationOverflow(_))`
    pub fn is_overflow(&self) -> bool {
        matches!(self, Self::GenerationOverflow(_))
    }

    /// Maps both options to `T`. This is the preferred method for most uses
    /// that don't care about the incredible difficulty of
    /// reaching generation overflow with the default `NonZeroU64`.
    pub fn allow(self) -> T {
        match self {
            Self::Success(t) => t,
            Self::GenerationOverflow(t) => t,
        }
    }

    /// Maps `Success` to `Ok`, `GenerationOverflow` to `Err`. Recommended only
    /// for small `P::Gen` sizes or ABA prevention situations that require
    /// absolute strictness.
    pub fn strict(self) -> Result<T, T> {
        match self {
            Self::Success(t) => Ok(t),
            Self::GenerationOverflow(t) => Err(t),
        }
    }

    /// Maps `T` to `U` in the corresponding variants
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> InvalidationOption<U> {
        match self {
            Self::Success(t) => InvalidationOption::Success(f(t)),
            Self::GenerationOverflow(t) => InvalidationOption::GenerationOverflow(f(t)),
        }
    }

    /// Maps `Success(T)` to `(T, false)` and `GenerationOverflow(T)` to `(T,
    /// true)`
    pub fn overflowing(self) -> (T, bool) {
        match self {
            Self::Success(t) => (t, false),
            Self::GenerationOverflow(t) => (t, true),
        }
    }
}

/// Returned from fallible operations that have two different degrees of
/// success.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
#[must_use]
pub enum InvalidationResult<T> {
    /// The operation was successful without generation counter overflow
    Success(T),
    /// The operation was completed successfully, except that a generation
    /// counter overflowed
    GenerationOverflow(T),
    /// The `Ptr` that invalidation was targeting was invalid, and the operation
    /// was never executed
    InvalidPtr,
}

impl<T> InvalidationResult<T> {
    /// If `matches!(self, Self::Success(_))`
    pub fn is_success(&self) -> bool {
        matches!(self, Self::Success(_))
    }

    /// If `matches!(self, Self::GenerationOverflow(_))`
    pub fn is_overflow(&self) -> bool {
        matches!(self, Self::GenerationOverflow(_))
    }

    /// If `matches!(self, Self::InvalidPtr)`
    pub fn is_invalid(&self) -> bool {
        matches!(self, Self::InvalidPtr)
    }

    /// Maps both `Success` and `GenerationOverflow` to `Some`, and maps
    /// `InvalidPtr` to `None`. This is the preferred method for most uses
    /// that don't care about the incredible difficulty of
    /// reaching generation overflow with the default `NonZeroU64`.
    #[must_use]
    pub fn allow(self) -> Option<T> {
        match self {
            Self::Success(t) => Some(t),
            Self::GenerationOverflow(t) => Some(t),
            Self::InvalidPtr => None,
        }
    }

    /// Maps `Success` to `Ok`, `GenerationOverflow` to `Err(Some)`, and
    /// `InvalidPtr` to `Err(None)`. Recommended only for small `P::Gen` sizes
    /// or ABA prevention situations that require absolute strictness.
    pub fn strict(self) -> Result<T, Option<T>> {
        match self {
            Self::Success(t) => Ok(t),
            Self::GenerationOverflow(t) => Err(Some(t)),
            Self::InvalidPtr => Err(None),
        }
    }

    /// Maps `T` to `U` in the corresponding variants
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> InvalidationResult<U> {
        match self {
            Self::Success(t) => InvalidationResult::Success(f(t)),
            Self::GenerationOverflow(t) => InvalidationResult::GenerationOverflow(f(t)),
            Self::InvalidPtr => InvalidationResult::InvalidPtr,
        }
    }

    /// Maps `Success(T)` to `(Some(T), false)`, `GenerationOverflow(T)` to
    /// `(Some(T), true)`, and `InvalidPtr` to `(None, false)`.
    pub fn overflowing(self) -> (Option<T>, bool) {
        match self {
            Self::Success(t) => (Some(t), false),
            Self::GenerationOverflow(t) => (Some(t), true),
            Self::InvalidPtr => (None, false),
        }
    }

    /// Maps to an `InvalidationOption`, panicking if `self.is_invalid()`.
    ///
    /// # Panics
    ///
    /// If `self.is_invalid()`.
    #[track_caller]
    pub fn unwrap(self) -> InvalidationOption<T> {
        match self {
            Self::Success(t) => InvalidationOption::Success(t),
            Self::GenerationOverflow(t) => InvalidationOption::GenerationOverflow(t),
            Self::InvalidPtr => {
                panic!("called `InvalidationOption::unwrap()` on an `InvalidPtr` value")
            }
        }
    }
}

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
