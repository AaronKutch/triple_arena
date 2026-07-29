use core::num::NonZeroUsize;

use crate::traits::Ptr;

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

impl<T> InvalidationOption<T> {
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

    /// If `matches!(self, Self::GenerationOverflow(_))`
    pub fn is_overflow(&self) -> bool {
        matches!(self, Self::GenerationOverflow(_))
    }

    /// Maps `T` to `U` in the corresponding variants
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> InvalidationOption<U> {
        match self {
            Self::Success(t) => InvalidationOption::Success(f(t)),
            Self::GenerationOverflow(t) => InvalidationOption::GenerationOverflow(f(t)),
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

/// Describes multiple ways to insert a link. All the "*Inx" variants disregard
/// generation counters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkInsertKind<P: Ptr> {
    /// Insert a single link by itself, in a single link chain that is
    /// disconnected from anything else
    Disconnected,
    /// Insert a single link by itself but connected to itself, that is, a
    /// single link cyclic chain
    SingleLinkCyclic,
    /// Insert a link at the end of a chain. The `P` must point to the current
    /// end link of a noncyclic chain, and the inserted node will become the new
    /// end of the chain
    ChainEnd(P),
    ChainEndInx(P::Inx),
    /// Insert a link at the start of a chain. The `P` must point to the current
    /// start link of a noncyclic chain, and the inserted node will become the
    /// new start of the chain
    ChainStart(P),
    ChainStartInx(P::Inx),
    /// Insert a link as the next link from the existing link  at`P`, which
    /// could be anywhere on any chain, maintaining continuity of the chain
    NextTo(P),
    NextToInx(P::Inx),
    /// Insert a link as the previous link from the existing link at `P`, which
    /// could be anywhere on any chain, maintaining continuity of the chain
    PrevTo(P),
    PrevToInx(P::Inx),
    /// Insert a link inbetween two `P` that have an interlink between them,
    /// maintaining continuity of the chain. The insertion will fail if the two
    /// links are not neighbors. Note that the arguments are directionally
    /// sensitive, calling [crate::Link::next] on the link at `next_to` must result in
    /// `prev_to` and not the other way around. Note that this can act on a
    /// single link cyclic chain with `next_to == prev_to`, but `next_to ==
    /// prev_to` is allowed only in that case as the "inbetween" acts upon the
    /// interlink of a link with itself. Single link chains without a cycle can
    /// never succeed with this operation, because there is no interlink.
    AtInterlink {
        next_to: P,
        prev_to: P,
    },
    AtInterlinkInx {
        next_to: P::Inx,
        prev_to: P::Inx,
    },
    // (named bridge because 3 links are involved, "connect" only involves interlinks)
    /// Insert a link as a bridge inbetween the end and start of chains. If this
    /// is the end and start of the same chain, this creates a unified cyclic
    /// chain. If this is the end and start of different chains, this makes a
    /// unified linear chain.
    Bridge {
        end: P,
        start: P,
    },
    BridgeInx {
        end: P::Inx,
        start: P::Inx,
    },
}

// for internal convenience
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LinkInsertInxKind<P: Ptr> {
    Disconnected,
    SingleLinkCyclic,
    ChainEndInx(P::Inx),
    ChainStartInx(P::Inx),
    NextToInx(P::Inx),
    PrevToInx(P::Inx),
    // `AtInterlinkInx` and `BridgeInx` unify for the purposes of a verified entry insertion
    InternalConnect { next_to: P::Inx, prev_to: P::Inx },
}
