use std::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};

use testcrate::P0;
use triple_arena::{
    ptr_struct,
    utils::{PtrInx, PtrNoGen},
    Advancer, Arena, Ptr,
};

#[test]
fn ptrs() {
    let x: NonZeroUsize = <NonZeroUsize as PtrInx>::max();
    assert_eq!(x.get(), usize::MAX);
    let x: NonZeroUsize = <NonZeroU8 as PtrInx>::max();
    assert_eq!(x.get(), u8::MAX as usize);
    let x: NonZeroUsize = <NonZeroU16 as PtrInx>::max();
    assert_eq!(x.get(), u16::MAX as usize);
    let x: NonZeroUsize = <NonZeroU32 as PtrInx>::max();
    assert_eq!(x.get(), u32::MAX as usize);
    let x: NonZeroUsize = <NonZeroU64 as PtrInx>::max();
    assert_eq!(x.get(), u64::MAX as usize);
    let x: NonZeroUsize = <NonZeroU128 as PtrInx>::max();
    assert_eq!(x.get(), u128::MAX as usize);

    let max = NonZeroUsize::new(usize::MAX).unwrap();
    let x: NonZeroUsize = PtrInx::new(max);
    assert_eq!(x.get(), usize::MAX);
    assert_eq!(PtrInx::get(x).get(), usize::MAX);
    let x: NonZeroU8 = PtrInx::new(max);
    assert_eq!(PtrInx::get(x).get(), u8::MAX as usize);
    assert_eq!(x.get(), usize::MAX as u8);
    let x: NonZeroU16 = PtrInx::new(max);
    assert_eq!(x.get(), usize::MAX as u16);
    let x: NonZeroU32 = PtrInx::new(max);
    assert_eq!(x.get(), usize::MAX as u32);
    let x: NonZeroU64 = PtrInx::new(max);
    assert_eq!(x.get(), usize::MAX as u64);
    let x: NonZeroU128 = PtrInx::new(max);
    assert_eq!(x.get(), usize::MAX as u128);
    assert_eq!(PtrInx::get(x).get(), usize::MAX);
}

#[test]
fn ptr_display() {
    ptr_struct!(P1[NonZeroU128](NonZeroU8));
    ptr_struct!(P2[NonZeroU128]());
    assert_eq!(
        &format!("{}", P1::_from_raw(NonZeroU128::MAX, NonZeroU8::MAX)),
        "P1[ffffffffffffffffffffffffffffffff](ff)"
    );
    assert_eq!(
        &format!("{}", P2::_from_raw(NonZeroU128::MAX, ())),
        "P2[ffffffffffffffffffffffffffffffff]"
    );
    assert_eq!(
        &format!("{}", PtrNoGen::<P1>::_from_raw(NonZeroU128::MAX, ())),
        "P1[ffffffffffffffffffffffffffffffff]"
    );
}

// this is a hard coded test, there is a section in the fuzz test and in the
// overflow tests
#[test]
fn advancer() {
    let mut a = Arena::<P0, u8>::new();

    let mut adv = a.advancer();
    assert!(adv.advance(&a).is_none());

    let p0 = a.insert(0);
    let p1 = a.insert(1);
    let p2 = a.insert(2);
    let p3 = a.insert(3);
    let p4 = a.insert(4);
    a.remove(p1).unwrap();
    let p5 = a.insert(5);
    a.remove(p3).unwrap();
    a.remove(p0).unwrap();

    let mut v = vec![];
    let mut adv = a.advancer();
    while let Some(p) = adv.advance(&a) {
        v.push(p);
    }
    assert_ne!(v, vec![p1, p2, p4]);
    assert_eq!(v, vec![p5, p2, p4]);
}
