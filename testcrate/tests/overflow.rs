use std::num::{NonZeroU8, NonZeroU128};

use triple_arena::{Arena, HeapBacking, LimitedHeapBacking, StackBacking, ptr_struct, traits::*};

ptr_struct!(P0[NonZeroU8]);
ptr_struct!(P1(NonZeroU8));
ptr_struct!(P2[NonZeroU8]());

ptr_struct!(PLargeInx[NonZeroU128]());

// The `PtrInx` trait could use truncation, and if only `Ptr`s constructed by
// the arena were used it could never lead to observable different index
// collisions. However, I'd rather not let this potentiality exist and just make
// it checked (and it will be a zero cost operation with the default
// `NonZeroUsize` index).
#[test]
fn ptr_inx_no_truncate() {
    let mut a = Arena::<PLargeInx, (), StackBacking<128>>::new();
    a.insert(());
    let p = Ptr::_from_raw(NonZeroU128::new(7 << 64).unwrap(), ());
    assert!(a.get(p).is_none());
}

// note: we have two tests, because we need to make sure both that there is not
// a premature panic and that there is a panic when is should happen

#[test]
fn overflow_inx_stack() {
    let mut a = Arena::<P0, (), StackBacking<512>>::new();
    // it caps to the index limit and not the stack cap
    a.reallocate_min_capacity(255).unwrap();
    assert!(a.reallocate_min_capacity(256).is_err());
    assert_eq!(a.capacity(), 255);
    // this is by consequence of `set_max_capacity` needing to unconditionally
    // succeed on arbitrary increases and setting `max_capacity` exactly to the
    // argument, see arena_traits.rs
    assert_eq!(a.max_capacity(), Some(512));
    for _ in 0..255 {
        a.insert(());
    }
    assert!(a.insert_within_capacity(()).is_err());
}

#[test]
fn overflow_inx_heap() {
    let mut a = Arena::<P0, (), HeapBacking>::new();
    // it caps to the index limit and not the stack cap
    a.reallocate_min_capacity(255).unwrap();
    assert!(a.reallocate_min_capacity(256).is_err());
    assert_eq!(a.capacity(), 255);
    assert_eq!(a.max_capacity(), None);
    for _ in 0..255 {
        a.insert(());
    }
    assert!(a.insert_within_capacity(()).is_err());
}

#[test]
fn overflow_inx_limited_heap() {
    let mut a = Arena::<P0, (), LimitedHeapBacking>::new();
    a.set_max_capacity(255).unwrap();
    // it caps to the index limit and not the stack cap
    a.reallocate_min_capacity(255).unwrap();
    assert!(a.reallocate_min_capacity(256).is_err());
    assert_eq!(a.capacity(), 255);
    assert_eq!(a.max_capacity(), Some(255));
    for _ in 0..255 {
        a.insert(());
    }
    assert!(a.insert_within_capacity(()).is_err());
}

#[test]
#[should_panic]
fn overflow_inx_panic() {
    let mut a = Arena::<P0, (), StackBacking<512>>::new();
    for _ in 0..256 {
        a.insert(());
    }
}

#[test]
fn overflow_generation() {
    let mut a = Arena::<P1, (), StackBacking<512>>::new();
    for _ in 0..253 {
        let p = a.insert(());
        a.remove(p).strict().unwrap();
    }
    let p = a.insert(());
    assert!(a.remove(p).strict().is_err());
}

// makes sure that advancers behave around limits
#[test]
fn advance_cap() {
    let mut a = Arena::<P2, (), StackBacking<512>>::new();
    let mut v = vec![];
    for _ in 0..255 {
        v.push(a.insert(()));
    }
    let mut i = 0;
    let mut adv = a.advancer();
    while let Some(p) = adv.advance(&a) {
        assert_eq!(p, v[i]);
        i += 1;
    }
    assert_eq!(i, 255);
    a.remove(v[0]).allow().unwrap();
    a.remove(v[254]).allow().unwrap();

    // check that it skips the ends
    let mut i = 1;
    let mut adv = a.advancer();
    while let Some(p) = adv.advance(&a) {
        assert_eq!(p, v[i]);
        i += 1;
    }
    assert_eq!(i, 254);
}
