use core::{error::Error, fmt};

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

/// For chain arena insertion
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ChainInsertionError {
    /// A `Ptr` was invalid or some requirement of a `LinkInsertKind` was failed
    FailedLinkRequirement,
    /// The operation would not be within existing capacity
    NotWithinCapacity,
    /// Extending the capacity further to the required amount would exceed a max
    /// capacity limit
    BeyondMaxCapacity,
    /// There was an allocation error when attempting to reallocate
    AllocError,
}

impl fmt::Display for ChainInsertionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FailedLinkRequirement => {
                f.write_str("a `LinkInsertKind` requirement was not met")
            }
            Self::NotWithinCapacity => {
                f.write_str("an operation would not be within existing capacity")
            }
            Self::BeyondMaxCapacity => {
                f.write_str("a max capacity limit prevents growing the capacity")
            }
            Self::AllocError => f.write_str("a memory reallocation failed"),
        }
    }
}

impl Error for ChainInsertionError {}

/// For ordered arena insertion
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum OrdInsertionError {
    /// A `Ptr` was invalid or some requirement of a `OrdInsertKind` was failed
    FailedOrdRequirement,
    /// The operation would not be within existing capacity
    NotWithinCapacity,
    /// Extending the capacity further to the required amount would exceed a max
    /// capacity limit
    BeyondMaxCapacity,
    /// There was an allocation error when attempting to reallocate
    AllocError,
}

impl fmt::Display for OrdInsertionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FailedOrdRequirement => f.write_str("a `OrdInsertKind` requirement was not met"),
            Self::NotWithinCapacity => {
                f.write_str("an operation would not be within existing capacity")
            }
            Self::BeyondMaxCapacity => {
                f.write_str("a max capacity limit prevents growing the capacity")
            }
            Self::AllocError => f.write_str("a memory reallocation failed"),
        }
    }
}

impl Error for OrdInsertionError {}
