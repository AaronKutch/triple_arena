use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};

use testcrate::P0;
use triple_arena::{
    Arena, ChainArena, DirectArena, LinkInsertKind, OrdPair, SimpleOrdArena, StackBacking,
    SurjectArena, ptr_struct,
    traits::*,
    utils::{
        PtrNoGen,
        traits::{PtrGen, PtrInx},
    },
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
}

fn nz(x: usize) -> NonZeroUsize {
    NonZeroUsize::new(x).unwrap()
}

#[test]
fn arena_display() {
    // the unordered arenas are `Debug` maps in internal slot order, and free
    // slots are simply not shown
    let mut a = Arena::<P0, u8, StackBacking<8>>::new();
    a.insert(10);
    let p1 = a.insert(11);
    a.insert(12);
    a.remove(p1).allow().unwrap();
    assert_eq!(&format!("{a:?}"), "{P0[1](2): 10, P0[3](2): 12}");
    assert_eq!(
        &format!("{a:#?}"),
        r#"{
    P0[1](2): 10,
    P0[3](2): 12,
}"#
    );

    let mut d = DirectArena::<P0, u8, StackBacking<8>>::new();
    for (i, t) in [30u8, 31].into_iter().enumerate() {
        let p: P0 = Ptr::_from_raw(PtrInx::try_from_usize(nz(i + 1)).unwrap(), PtrGen::two());
        d.direct_insert_within_capacity(p).unwrap().insert(t);
    }
    assert_eq!(&format!("{d:?}"), "{P0[1](2): 30, P0[2](2): 31}");
    assert_eq!(
        &format!("{d:#?}"),
        r#"{
    P0[1](2): 30,
    P0[2](2): 31,
}"#
    );

    // a chain arena prefixes each entry with its interlinks in hex, using
    // `(start)` and `(end)` for the ends of a noncyclic chain. The `&str`
    // entries show that the `Debug` and `Display` impls really do dispatch to
    // the corresponding impl of the entry.
    let mut c = ChainArena::<P0, &str, StackBacking<128>>::new();
    let q0 = c.insert(LinkInsertKind::Disconnected, "x");
    c.insert(LinkInsertKind::ChainEnd(q0), "y");
    c.insert(LinkInsertKind::SingleLinkCyclic, "z");
    // make sure it is hex
    let mut v = vec![];
    for _ in 0..10 {
        v.push(c.insert(LinkInsertKind::Disconnected, "w"));
    }
    c.insert(LinkInsertKind::SingleLinkCyclic, "w");
    for i in 0..9 {
        c.remove(v[i]).allow().unwrap();
    }
    assert_eq!(
        &format!("{c:?}"),
        r#"{P0[1](2): {(start), 2} "x", P0[2](2): {1, (end)} "y", P0[3](2): {3, 3} "z", P0[d](2): {(start), (end)} "w", P0[e](2): {e, e} "w"}"#
    );
    assert_eq!(
        &format!("{c:#?}"),
        r#"{
    P0[1](2): {(start), 2} "x",
    P0[2](2): {1, (end)} "y",
    P0[3](2): {3, 3} "z",
    P0[d](2): {(start), (end)} "w",
    P0[e](2): {e, e} "w",
}"#
    );

    // and the same prefix is used by the standalone links
    let link = c.get_link(q0).unwrap();
    let link_no_gen = c.get_link_no_gen(q0).unwrap();
    assert_eq!(&format!("{link:?}"), r#"{(start), 2} "x""#);
    assert_eq!(&format!("{link:#?}"), r#"{(start), 2} "x""#);
    assert_eq!(&format!("{link}"), "{(start), 2} x");
    assert_eq!(&format!("{link:#}"), "{(start), 2} x");
    assert_eq!(&format!("{link_no_gen:?}"), r#"{(start), 2} "x""#);
    assert_eq!(&format!("{link_no_gen:#?}"), r#"{(start), 2} "x""#);
    assert_eq!(&format!("{link_no_gen}"), "{(start), 2} x");
    assert_eq!(&format!("{link_no_gen:#}"), "{(start), 2} x");

    // in key order
    let mut o = SimpleOrdArena::<P0, OrdPair<u8, u8>, StackBacking<8>>::new();
    let _ = o.insert(OrdPair::new(3, 40));
    let _ = o.insert(OrdPair::new(1, 41));
    let _ = o.insert(OrdPair::new(2, 42));
    assert_eq!(
        &format!("{o:?}"),
        "{P0[2](2): (1, 41), P0[3](2): (2, 42), P0[1](2): (3, 40)}"
    );
    assert_eq!(&format!("{:?}", OrdPair::new(1u8, 41u8)), "(1, 41)");

    let mut s = SurjectArena::<P0, u8, u8, StackBacking<8>>::new();
    let r0 = s.insert_surject(50, 200);
    s.insert(r0, 51);
    s.insert_surject(52, 202);
    assert_eq!(
        &format!("{s:?}"),
        "{(P0[1](2), 50, 200), (P0[2](2), 51, 200), (P0[3](2), 52, 202)}"
    );

    // maybe we should change this, see the TODO on the `SimpleOrdArena` `Debug`
    // impl
    assert_eq!(
        &format!("{o:#?}"),
        r#"{
    P0[2](2): (
        1,
        41,
    ),
    P0[3](2): (
        2,
        42,
    ),
    P0[1](2): (
        3,
        40,
    ),
}"#
    );
    assert_eq!(
        &format!("{s:#?}"),
        r#"{
    (
        P0[1](2),
        50,
        200,
    ),
    (
        P0[2](2),
        51,
        200,
    ),
    (
        P0[3](2),
        52,
        202,
    ),
}"#
    );
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
