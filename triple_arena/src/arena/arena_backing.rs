use crate::{
    arena::{NonZeroInxArray, NonZeroInxLimitedVec, NonZeroInxVec},
    utils::NonZeroInxGenericStack,
};

pub trait ArenaBacking {
    type Stack<U>: NonZeroInxGenericStack<U>;
}

pub struct HeapBacking;

impl ArenaBacking for HeapBacking {
    type Stack<U> = NonZeroInxVec<U>;
}

pub struct LimitedHeapBacking;

impl ArenaBacking for LimitedHeapBacking {
    type Stack<U> = NonZeroInxLimitedVec<U>;
}

pub struct StackBacking<const LIMIT: usize>;

impl<const LIMIT: usize> ArenaBacking for StackBacking<LIMIT> {
    type Stack<U> = NonZeroInxArray<U, LIMIT>;
}
