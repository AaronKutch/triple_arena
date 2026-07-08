use crate::{
    arena::{NonZeroInxArray, NonZeroInxVec},
    utils::NonZeroInxGenericStack,
};

pub trait ArenaBacking {
    type Stack<U>: NonZeroInxGenericStack<U>;
}

pub struct HeapBacking;

impl ArenaBacking for HeapBacking {
    type Stack<U> = NonZeroInxVec<U>;
}

// FIXME a Limited dynamic type
pub struct StackBacking<const LIMIT: usize>;

impl<const LIMIT: usize> ArenaBacking for StackBacking<LIMIT> {
    type Stack<U> = NonZeroInxArray<U, LIMIT>;
}
