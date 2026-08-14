use crate::utils::{NonZeroInxArray, traits::NonZeroInxGenericStack};
#[cfg(feature = "alloc")]
use crate::utils::{NonZeroInxBoxedSlice, NonZeroInxLimitedVec, NonZeroInxVec};

/// A trait describing the backing for an Arena
///
/// # Safety
///
/// In addition to what [NonZeroInxGenericStack] requires, the `Stack` type must
/// not have certain kinds of internal mutability that would make functions like
/// [crate::Arena::backing] unsound.
pub unsafe trait ArenaBacking {
    type Stack<U>: NonZeroInxGenericStack<U>;
}

/// The default heap backing for arenas. When creating new arenas, this will not
/// allocate until the first reallocation.
#[cfg(feature = "alloc")]
pub struct HeapBacking;

#[cfg(feature = "alloc")]
unsafe impl ArenaBacking for HeapBacking {
    type Stack<U> = NonZeroInxVec<U>;
}

/// The standard limited heap backing for arenas
#[cfg(feature = "alloc")]
pub struct LimitedHeapBacking;

#[cfg(feature = "alloc")]
unsafe impl ArenaBacking for LimitedHeapBacking {
    type Stack<U> = NonZeroInxLimitedVec<U>;
}

/// The standard fixed capacity heap backing for arenas
#[cfg(feature = "alloc")]
pub struct FixedHeapBacking;

#[cfg(feature = "alloc")]
unsafe impl ArenaBacking for FixedHeapBacking {
    type Stack<U> = NonZeroInxBoxedSlice<U>;
}

/// The standard stack-based backing for arenas, where `LIMIT` is the number of
/// entries the arena can hold (but be careful to not make this too large)
pub struct StackBacking<const LIMIT: usize>;

unsafe impl<const LIMIT: usize> ArenaBacking for StackBacking<LIMIT> {
    type Stack<U> = NonZeroInxArray<U, LIMIT>;
}
