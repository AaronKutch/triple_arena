use std::{
    mem::size_of,
    num::{NonZeroU8, NonZeroUsize},
};

use triple_arena::{
    ptr_struct,
    utils::{InternalEntry, Node, PtrNoGen},
    Link, Ptr,
};

ptr_struct!(P0);
ptr_struct!(P1());
ptr_struct!(P2[NonZeroU8](NonZeroU8));

// make sure the structs from `ptr_struct` are compiling correctly
#[test]
fn size_of_ptr() {
    assert_eq!(size_of::<P0>(), size_of::<(NonZeroUsize, u64)>());
    assert_eq!(size_of::<PtrNoGen<P0>>(), size_of::<NonZeroUsize>());
    assert_eq!(size_of::<Option<PtrNoGen<P0>>>(), size_of::<usize>());
    assert_eq!(size_of::<P1>(), size_of::<NonZeroUsize>());
    assert_eq!(size_of::<Option<P1>>(), size_of::<usize>());
    assert_eq!(size_of::<<P1 as Ptr>::Inx>(), size_of::<NonZeroUsize>());
    assert_eq!(size_of::<Option<<P1 as Ptr>::Inx>>(), size_of::<usize>());
    assert_eq!(size_of::<P2>(), size_of::<(NonZeroU8, NonZeroU8)>());
}

#[test]
fn size_of_node() {
    assert_eq!(size_of::<Node<P0, (), ()>>(), 32);
    assert_eq!(size_of::<Link<P0, ()>>(), 32);
    assert_eq!(size_of::<InternalEntry<P0, ()>>(), 16);
    assert_eq!(
        size_of::<InternalEntry<P0, Link<P0, Node<P0, (), ()>>>>(),
        72
    );

    assert_eq!(size_of::<Node<P1, (), ()>>(), 32);
    assert_eq!(size_of::<Link<P1, ()>>(), 16);
    assert_eq!(size_of::<InternalEntry<P1, ()>>(), 8);
    assert_eq!(
        size_of::<InternalEntry<P1, Link<P1, Node<P1, (), ()>>>>(),
        56
    );
}
