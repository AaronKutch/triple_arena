use crate::utils::{NonZeroInxArray, traits::NonZeroInxGenericStack};
#[cfg(feature = "alloc")]
use crate::utils::{NonZeroInxBoxedSlice, NonZeroInxLimitedVec, NonZeroInxVec};

/// A trait describing the backing for an Arena.
///
/// # Safety
///
/// In addition to what [NonZeroInxGenericStack] requires, the `Stack` type must
/// not have certain kinds of internal mutability that would make functions like
/// [Arena::backing](crate::Arena::backing) unsound.
pub unsafe trait ArenaBacking {
    /// The stack type that arenas with this backing store their slots in
    type Stack<U>: NonZeroInxGenericStack<U>;
}

/// The default unlimited heap backing for arenas. This is like a `Vec`. When
/// creating new arenas, this will not allocate until the first reallocation.
#[cfg(feature = "alloc")]
pub struct HeapBacking;

#[cfg(feature = "alloc")]
unsafe impl ArenaBacking for HeapBacking {
    type Stack<U> = NonZeroInxVec<U>;
}

/// The standard limited heap backing for arenas. This is the same as
/// [HeapBacking] but with an additional max logical capacity setting. Plain
/// `new` functions with this backing will start with zero max capacity, use
/// `with_min_capacity` or change with `set_max_capacity`.
#[cfg(feature = "alloc")]
pub struct LimitedHeapBacking;

#[cfg(feature = "alloc")]
unsafe impl ArenaBacking for LimitedHeapBacking {
    type Stack<U> = NonZeroInxLimitedVec<U>;
}

/// The standard fixed capacity heap backing for arenas, capacity can only be
/// created once at `with_min_capacity` and never changed.
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
