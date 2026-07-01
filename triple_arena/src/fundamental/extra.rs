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

// TODO it was stabilized in 1.86 but so many things are MSRV'ed on 1.85
/// Placeholder until we bump MSRV
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GetDisjointMutError {
    /// An index provided was out-of-bounds for the slice.
    IndexOutOfBounds,
    /// Two indices provided were overlapping.
    OverlappingIndices,
}

impl fmt::Display for GetDisjointMutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            GetDisjointMutError::IndexOutOfBounds => "an index is out of bounds",
            GetDisjointMutError::OverlappingIndices => "there were overlapping indices",
        };
        fmt::Display::fmt(msg, f)
    }
}

impl Error for GetDisjointMutError {}
