use std::{
    mem::size_of,
    num::{NonZeroU8, NonZeroUsize},
};

use triple_arena::{
    Link, ptr_struct,
    traits::*,
    utils::{ArenaSlot, PtrNoGen, SimpleOrdArenaNode},
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

#[cfg(target_pointer_width = "64")]
#[test]
fn size_of_node() {
    use triple_arena::LinkNoGen;

    assert_eq!(size_of::<SimpleOrdArenaNode<P0, ()>>(), 32);
    assert_eq!(size_of::<Link<P0, ()>>(), 32);
    assert_eq!(size_of::<LinkNoGen<P0, ()>>(), 16);
    assert_eq!(size_of::<ArenaSlot<P0, ()>>(), 16);
    assert_eq!(
        size_of::<ArenaSlot<P0, Link<P0, SimpleOrdArenaNode<P0, ()>>>>(),
        72
    );

    assert_eq!(size_of::<SimpleOrdArenaNode<P1, ()>>(), 32);
    assert_eq!(size_of::<Link<P1, ()>>(), 16);
    assert_eq!(size_of::<LinkNoGen<P1, ()>>(), 16);
    assert_eq!(size_of::<ArenaSlot<P1, ()>>(), 8);
    assert_eq!(
        size_of::<ArenaSlot<P1, Link<P1, SimpleOrdArenaNode<P1, ()>>>>(),
        56
    );
}
