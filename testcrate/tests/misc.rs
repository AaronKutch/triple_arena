use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};

use testcrate::P0;
use triple_arena::{
    Arena, StackBacking, ptr_struct,
    traits::*,
    utils::{PtrNoGen, traits::PtrInx},
};

#[test]
fn ptrs() {
    let x: NonZeroUsize = <NonZeroUsize as PtrInx>::best_effort_invalid();
    assert_eq!(x.get(), usize::MAX);
    let x: NonZeroU8 = <NonZeroU8 as PtrInx>::best_effort_invalid();
    assert_eq!(x.get(), u8::MAX);
    let x: NonZeroU16 = <NonZeroU16 as PtrInx>::best_effort_invalid();
    assert_eq!(x.get(), u16::MAX);
    let x: NonZeroU32 = <NonZeroU32 as PtrInx>::best_effort_invalid();
    assert_eq!(x.get(), u32::MAX);
    let x: NonZeroU64 = <NonZeroU64 as PtrInx>::best_effort_invalid();
    assert_eq!(x.get(), u64::MAX);
    let x: NonZeroU128 = <NonZeroU128 as PtrInx>::best_effort_invalid();
    assert_eq!(x.get(), u128::MAX);

    let max = NonZeroUsize::new(usize::MAX).unwrap();
    let x: NonZeroUsize = PtrInx::try_from_usize(max).unwrap();
    assert_eq!(x.get(), usize::MAX);
    assert_eq!(PtrInx::try_into_usize(x).unwrap().get(), usize::MAX);
    assert!(
        <NonZeroU8 as PtrInx>::try_from_usize(NonZeroUsize::new(1usize << 8).unwrap()).is_none()
    );
    // every linear `PtrInx` must report truncation rather than wrapping, and
    // must agree with `max_index`
    assert!(
        <NonZeroU16 as PtrInx>::try_from_usize(NonZeroUsize::new(1usize << 16).unwrap()).is_none()
    );
    #[cfg(target_pointer_width = "64")]
    assert!(
        <NonZeroU32 as PtrInx>::try_from_usize(NonZeroUsize::new(1usize << 32).unwrap()).is_none()
    );
    assert_eq!(
        <NonZeroU8 as PtrInx>::max_index().unwrap().get(),
        u8::MAX as usize
    );
    assert_eq!(
        <NonZeroU16 as PtrInx>::max_index().unwrap().get(),
        u16::MAX as usize
    );
    assert_eq!(
        <NonZeroU32 as PtrInx>::max_index().unwrap().get(),
        u32::MAX as usize
    );
    assert_eq!(
        <NonZeroUsize as PtrInx>::max_index().unwrap().get(),
        usize::MAX
    );
    // widening `max_index` saturates at `usize::MAX` rather than truncating to
    // something smaller
    assert_eq!(
        <NonZeroU128 as PtrInx>::max_index().unwrap().get(),
        usize::MAX
    );

    let x: NonZeroU128 =
        <NonZeroU128 as PtrInx>::try_from_usize(NonZeroUsize::new(usize::MAX).unwrap()).unwrap();
    assert_eq!(
        <NonZeroU128 as PtrInx>::try_into_usize(x).unwrap().get(),
        usize::MAX
    );
    #[cfg(target_pointer_width = "64")]
    assert!(
        <NonZeroU128 as PtrInx>::try_into_usize(NonZeroU128::new(usize::MAX as u128 + 1).unwrap())
            .is_none()
    );
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

    // FIXME display links and arenas
}

// this is a hard coded test, there is a section in the fuzz test and in the
// overflow tests
#[test]
fn advancer() {
    let mut a = Arena::<P0, u8, StackBacking<5>>::new();

    let mut adv = a.advancer();
    assert!(adv.advance(&a).is_none());

    let p0 = a.insert(0);
    let p1 = a.insert(1);
    let p2 = a.insert(2);
    let p3 = a.insert(3);
    let p4 = a.insert(4);
    a.remove(p1).allow().unwrap();
    let p5 = a.insert(5);
    a.remove(p3).allow().unwrap();
    a.remove(p0).allow().unwrap();

    let mut v = vec![];
    let mut adv = a.advancer();
    while let Some(p) = adv.advance(&a) {
        v.push(p);
    }
    assert_ne!(v, vec![p1, p2, p4]);
    assert_eq!(v, vec![p5, p2, p4]);
}
