//! LLM One-off instance tests for branches that the fuzz tests do not reach.
//!
//! Everything here avoids the `alloc` feature so that it runs under every
//! feature configuration, which matters because `ptr.rs` and `ptr_serde.rs` are
//! separately compiled depending on `serde_support`.

use core::{
    fmt,
    num::{NonZeroU8, NonZeroUsize},
};

use triple_arena::{
    Arena, InvalidationOption, InvalidationResult, StackBacking, ptr_struct,
    traits::{ArenaInsertTrait, ArenaTrait, Ptr, Recast},
    utils::{PtrNoGen, nzusize_iter, traits::PtrGen},
};

fn nz(x: usize) -> NonZeroUsize {
    NonZeroUsize::new(x).unwrap()
}

#[test]
fn nzusize_iter_ranges() {
    let collect = |start, end| -> Vec<usize> {
        nzusize_iter(start, end)
            .into_iter()
            .map(|x| x.get())
            .collect()
    };
    let collect_rev = |start, end| -> Vec<usize> {
        nzusize_iter(start, end)
            .into_iter()
            .rev()
            .map(|x| x.get())
            .collect()
    };

    assert_eq!(collect(nz(1), Some(nz(4))), vec![1, 2, 3, 4]);
    assert_eq!(collect_rev(nz(1), Some(nz(4))), vec![4, 3, 2, 1]);
    assert_eq!(collect(nz(3), Some(nz(3))), vec![3]);
    assert_eq!(collect_rev(nz(3), Some(nz(3))), vec![3]);
    // a `None` end is empty, as is an inverted range
    assert_eq!(collect(nz(1), None), Vec::<usize>::new());
    assert_eq!(collect_rev(nz(1), None), Vec::<usize>::new());
    assert_eq!(collect(nz(5), Some(nz(4))), Vec::<usize>::new());
    assert_eq!(collect_rev(nz(5), Some(nz(4))), Vec::<usize>::new());

    // the ends must not overflow, which is the reason this exists instead of a
    // standard library range
    assert_eq!(collect(nz(usize::MAX), Some(nz(usize::MAX))), vec![
        usize::MAX
    ]);
    assert_eq!(collect_rev(nz(usize::MAX), Some(nz(usize::MAX))), vec![
        usize::MAX
    ]);
    let mut iter = nzusize_iter(nz(usize::MAX - 1), Some(nz(usize::MAX))).into_iter();
    assert_eq!(iter.next().map(|x| x.get()), Some(usize::MAX - 1));
    assert_eq!(iter.next().map(|x| x.get()), Some(usize::MAX));
    assert_eq!(iter.next(), None);
    // fused
    assert_eq!(iter.next(), None);

    // meeting in the middle from both ends
    let mut iter = nzusize_iter(nz(1), Some(nz(3))).into_iter();
    assert_eq!(iter.next().map(|x| x.get()), Some(1));
    assert_eq!(iter.next_back().map(|x| x.get()), Some(3));
    assert_eq!(iter.next().map(|x| x.get()), Some(2));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
}

ptr_struct!(Q0);
ptr_struct!(Q1());

#[test]
fn invalidation_option() {
    let s = InvalidationOption::Success(7u8);
    let o = InvalidationOption::GenerationOverflow(7u8);

    assert!(s.is_success());
    assert!(!s.is_overflow());
    assert!(!o.is_success());
    assert!(o.is_overflow());

    assert_eq!(s.allow(), 7);
    assert_eq!(o.allow(), 7);

    assert_eq!(s.strict(), Ok(7));
    assert_eq!(o.strict(), Err(7));

    assert_eq!(s.map(|x| x + 1), InvalidationOption::Success(8));
    assert_eq!(o.map(|x| x + 1), InvalidationOption::GenerationOverflow(8));

    assert_eq!(s.overflowing(), (7, false));
    assert_eq!(o.overflowing(), (7, true));

    assert_eq!(format!("{s:?}"), "Success(7)");
    assert_eq!(format!("{o:?}"), "GenerationOverflow(7)");
}

#[test]
fn invalidation_result() {
    let s = InvalidationResult::Success(7u8);
    let o = InvalidationResult::GenerationOverflow(7u8);
    let i = InvalidationResult::<u8>::InvalidPtr;

    assert!(s.is_success());
    assert!(!s.is_overflow());
    assert!(!s.is_invalid());
    assert!(!o.is_success());
    assert!(o.is_overflow());
    assert!(!o.is_invalid());
    assert!(!i.is_success());
    assert!(!i.is_overflow());
    assert!(i.is_invalid());

    assert_eq!(s.allow(), Some(7));
    assert_eq!(o.allow(), Some(7));
    assert_eq!(i.allow(), None);

    assert_eq!(s.strict(), Ok(7));
    assert_eq!(o.strict(), Err(Some(7)));
    assert_eq!(i.strict(), Err(None));

    assert_eq!(s.map(|x| x + 1), InvalidationResult::Success(8));
    assert_eq!(o.map(|x| x + 1), InvalidationResult::GenerationOverflow(8));
    assert_eq!(i.map(|x| x + 1), InvalidationResult::InvalidPtr);

    assert_eq!(s.overflowing(), (Some(7), false));
    assert_eq!(o.overflowing(), (Some(7), true));
    assert_eq!(i.overflowing(), (None, false));

    assert_eq!(s.unwrap(), InvalidationOption::Success(7));
    assert_eq!(o.unwrap(), InvalidationOption::GenerationOverflow(7));

    assert_eq!(format!("{s:?}"), "Success(7)");
    assert_eq!(format!("{o:?}"), "GenerationOverflow(7)");
    assert_eq!(format!("{i:?}"), "InvalidPtr");
}

#[test]
#[should_panic = "called `InvalidationResult::unwrap()` on an `InvalidPtr` value"]
fn invalidation_result_unwrap_panic() {
    let _ = InvalidationResult::<u8>::InvalidPtr.unwrap();
}

struct GenHex<G: PtrGen>(G);

impl<G: PtrGen> fmt::Display for GenHex<G> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PtrGen::fmt_hex(self.0, f)
    }
}

#[test]
fn ptr_gen_unit() {
    // the generationless `()` implementation is mostly only reachable through
    // generics, so it is exercised directly here
    assert_eq!(<() as PtrGen>::one(), ());
    assert_eq!(<() as PtrGen>::two(), ());
    assert_eq!(<() as PtrGen>::generational_inc(()), ((), false));
    assert_eq!(format!("{}", GenHex(())), "()");

    // generation 1 is the reserved invalid generation, and incrementing the
    // maximum skips both 0 and 1
    assert_eq!(<NonZeroU8 as PtrGen>::one().get(), 1);
    assert_eq!(<NonZeroU8 as PtrGen>::two().get(), 2);
    let (g, overflow) = <NonZeroU8 as PtrGen>::generational_inc(NonZeroU8::MAX);
    assert_eq!((g.get(), overflow), (2, true));
    let (g, overflow) = <NonZeroU8 as PtrGen>::generational_inc(NonZeroU8::new(2).unwrap());
    assert_eq!((g.get(), overflow), (3, false));
    assert_eq!(format!("{}", GenHex(NonZeroU8::MAX)), "ff");
}

#[test]
fn ptr_default_and_invalid() {
    // `Default` must agree with `invalid` for every `ptr_struct` shape
    assert_eq!(Q0::default(), Q0::invalid());
    assert_eq!(Q1::default(), Q1::invalid());
    assert_eq!(PtrNoGen::<Q0>::default(), PtrNoGen::<Q0>::invalid());

    // the generationless cases rely entirely on `best_effort_invalid`
    assert_eq!(Q1::invalid().inx().get(), usize::MAX);
    assert_eq!(PtrNoGen::<Q0>::invalid().inx().get(), usize::MAX);
    assert_eq!(PtrNoGen::<Q0>::invalid().generation(), ());
    assert_eq!(Q1::invalid().generation(), ());

    // the generational case additionally uses the reserved generation 1
    assert_eq!(Q0::invalid().generation().get(), 1);
}

#[test]
fn ptr_recast() {
    // `Arena<P, P>` is the `Recaster<Item = P>` used to translate `Ptr` domains

    // generationless `ptr_struct`
    let mut recaster = Arena::<Q1, Q1, StackBacking<4>>::new();
    let old = recaster.insert(Q1::invalid());
    let new = recaster.insert(Q1::invalid());
    *recaster.get_mut(old).unwrap() = new;
    let mut p = old;
    p.recast(&recaster).unwrap();
    assert_eq!(p, new);
    // an item the recaster does not recognize is handed back as an error
    let mut bad = Q1::invalid();
    assert_eq!(bad.recast(&recaster), Err(Q1::invalid()));

    // `PtrNoGen`
    let mut recaster = Arena::<PtrNoGen<Q0>, PtrNoGen<Q0>, StackBacking<4>>::new();
    let old = recaster.insert(PtrNoGen::invalid());
    let new = recaster.insert(PtrNoGen::invalid());
    *recaster.get_mut(old).unwrap() = new;
    let mut p = old;
    p.recast(&recaster).unwrap();
    assert_eq!(p, new);
    let mut bad = PtrNoGen::<Q0>::invalid();
    assert_eq!(bad.recast(&recaster), Err(PtrNoGen::<Q0>::invalid()));
}
