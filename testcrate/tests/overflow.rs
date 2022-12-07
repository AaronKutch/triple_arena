use std::num::NonZeroU8;

use triple_arena::{ptr_struct, Arena};

ptr_struct!(P0[u8]);
ptr_struct!(P1(NonZeroU8));
ptr_struct!(P2[u8]());

// note: we have two tests, because we need to make sure both that there is not
// a premature panic and that there is a panic when is should happen

#[test]
fn overflow_inx() {
    let mut a = Arena::<P0, ()>::new();
    for _ in 0..256 {
        a.insert(());
    }
    let cap = a.capacity();
    assert!(cap >= 256);
    a.reserve(0);
    a.reserve(1);
    // capacity should not change
    assert_eq!(cap, a.capacity());
    assert!(a.try_insert(()).is_err());
}

#[test]
#[should_panic]
fn overflow_inx_panic() {
    let mut a = Arena::<P0, ()>::new();
    for _ in 0..257 {
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
fn next_ptr_cap() {
    let mut a = Arena::<P2, ()>::new();
    let mut v = vec![];
    for _ in 0..256 {
        v.push(a.insert(()));
    }
    let (mut p, mut b) = a.first_ptr();
    let mut i = 0;
    loop {
        if b {
            break
        }
        assert_eq!(p, v[i]);
        a.next_ptr(&mut p, &mut b);
        i += 1;
    }
    assert_eq!(i, 256);
    a.remove(v[0]).unwrap();
    a.remove(v[255]).unwrap();
    let (mut p, mut b) = a.first_ptr();
    let mut i = 1;
    loop {
        if b {
            break
        }
        assert_eq!(p, v[i]);
        a.next_ptr(&mut p, &mut b);
        i += 1;
    }
    assert_eq!(i, 255);
}
