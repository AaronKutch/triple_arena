use std::{
    mem::size_of,
    num::{NonZeroU64, NonZeroU8},
};

use triple_arena::ptr_struct;

ptr_struct!(P0);
ptr_struct!(P1());
ptr_struct!(P2[u8](NonZeroU8));

// make sure the structs from `ptr_struct` are compiling correctly
#[test]
fn size_of_ptr() {
    assert_eq!(size_of::<P0>(), size_of::<(usize, NonZeroU64)>());
    assert_eq!(size_of::<P1>(), size_of::<usize>());
    assert_eq!(size_of::<P2>(), size_of::<(u8, NonZeroU8)>());
}
