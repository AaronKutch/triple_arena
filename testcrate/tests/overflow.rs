use std::num::NonZeroU8;

use triple_arena::{ptr_struct, Advancer, Arena};

ptr_struct!(P0[NonZeroU8]);
ptr_struct!(P1(NonZeroU8));
ptr_struct!(P2[NonZeroU8]());

// note: we have two tests, because we need to make sure both that there is not
// a premature panic and that there is a panic when is should happen

#[test]
fn overflow_inx() {
    let mut a = Arena::<P0, ()>::new();
    for _ in 0..255 {
        a.insert(());
    }
    let cap = a.capacity();
    assert!(cap >= 255);
    a.reserve(0);
    // capacity should not change
    assert_eq!(cap, a.capacity());
    assert!(a.try_insert(()).is_err());
}

#[test]
#[should_panic]
fn overflow_inx_panic() {
    let mut a = Arena::<P0, ()>::new();
    for _ in 0..256 {
        a.insert(());
    }
}

#[test]
fn overflow_cap() {
    let mut a = Arena::<P1, ()>::new();
    for _ in 0..253 {
        let p = a.insert(());
        a.remove(p).unwrap();
    }
}

// should force panic
#[test]
#[should_panic]
fn overflow_cap_panic() {
    let mut a = Arena::<P1, ()>::new();
    for _ in 0..253 {
        let p = a.insert(());
        a.remove(p).unwrap();
    }
    let p = a.insert(());
    let _ = a.remove(p);
}

#[test]
fn advance_cap() {
    let mut a = Arena::<P2, ()>::new();
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
    a.remove(v[0]).unwrap();
    a.remove(v[254]).unwrap();
    let mut i = 1;
    let mut adv = a.advancer();
    while let Some(p) = adv.advance(&a) {
        assert_eq!(p, v[i]);
        i += 1;
    }
    assert_eq!(i, 254);
}
