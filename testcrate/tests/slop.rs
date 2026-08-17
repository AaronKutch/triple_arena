//! LLM One-off instance tests for branches that the fuzz tests do not reach.
//!
//! Anything that can avoid the `alloc` feature should, so that it runs under
//! every feature configuration, which matters because `ptr.rs` and
//! `ptr_serde.rs` are separately compiled depending on `serde_support`. The
//! rest is behind `#[cfg(feature = "alloc")]`.

use core::{
    fmt,
    num::{NonZeroU8, NonZeroUsize},
    slice::GetDisjointMutError,
};
use std::{
    cell::Cell,
    panic::{AssertUnwindSafe, catch_unwind},
};

use triple_arena::{
    Arena, InvalidationOption, InvalidationResult, StackBacking,
    errors::{AllocError, NotWithinCapacityError, ReallocationError},
    ptr_struct,
    traits::{ArenaInsertTrait, ArenaTrait, Ptr, Recast},
    utils::{
        NonZeroInxArray, PtrNoGen, nzusize_iter,
        traits::{NonZeroInxGenericStack, NonZeroInxGenericStackPushEntryTrait, PtrGen},
    },
};
#[cfg(feature = "alloc")]
use triple_arena::{
    FixedHeapBacking,
    utils::{NonZeroInxBoxedSlice, NonZeroInxVec},
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

// `crate::stack`

thread_local! {
    static DROPS: Cell<usize> = const { Cell::new(0) };
}

/// Increments [DROPS] when dropped, and panics on the way if constructed with
/// `true`
struct PanickyDrop(bool);

impl Drop for PanickyDrop {
    fn drop(&mut self) {
        DROPS.with(|drops| drops.set(drops.get().wrapping_add(1)));
        if self.0 {
            panic!("PanickyDrop");
        }
    }
}

/// Runs `f` and returns the number of [PanickyDrop]s that were dropped while it
/// ran, requiring that it panicked
fn count_drops_of_panicking(f: impl FnOnce()) -> usize {
    DROPS.with(|drops| drops.set(0));
    let res = catch_unwind(AssertUnwindSafe(f));
    assert!(res.is_err(), "expected the closure to panic");
    DROPS.with(|drops| drops.get())
}

#[test]
fn stack_panicking_drop_does_not_double_drop() {
    // A `T::drop` that panics unwinds through `clear`, and the `Drop` impls of the
    // `MaybeUninit` based stacks call `clear` again. The length must therefore be
    // zeroed before any drop code runs, or else the already dropped elements get
    // dropped a second time.

    let mut a = NonZeroInxArray::<PanickyDrop, 4>::new();
    a.push(PanickyDrop(false));
    a.push(PanickyDrop(true));
    a.push(PanickyDrop(false));
    let drops = count_drops_of_panicking(|| a.clear());
    // all three were dropped exactly once, the two after the panicking one are not
    // leaked either
    assert_eq!(drops, 3);
    assert_eq!(a.len(), 0);
    assert!(a.is_empty());
    // dropping `a` now must not drop anything again
    DROPS.with(|drops| drops.set(0));
    drop(a);
    assert_eq!(DROPS.with(|drops| drops.get()), 0);

    // the same through the `Drop` impl rather than an explicit `clear`
    let mut a = NonZeroInxArray::<PanickyDrop, 4>::new();
    a.push(PanickyDrop(false));
    a.push(PanickyDrop(true));
    assert_eq!(count_drops_of_panicking(move || drop(a)), 2);

    // and the same through a whole arena, which is how this is publicly reachable
    let mut a = Arena::<Q0, PanickyDrop, StackBacking<4>>::new();
    a.insert(PanickyDrop(false));
    a.insert(PanickyDrop(true));
    let drops = count_drops_of_panicking(|| {
        let _ = a.clear();
    });
    assert_eq!(drops, 2);
    assert!(a.is_empty());
    DROPS.with(|drops| drops.set(0));
    drop(a);
    assert_eq!(DROPS.with(|drops| drops.get()), 0);
}

#[cfg(feature = "alloc")]
#[test]
fn boxed_slice_panicking_drop_does_not_double_drop() {
    let mut a = NonZeroInxBoxedSlice::<PanickyDrop>::with_min_capacity(4).unwrap();
    a.push(PanickyDrop(false));
    a.push(PanickyDrop(true));
    a.push(PanickyDrop(false));
    assert_eq!(count_drops_of_panicking(|| a.clear()), 3);
    assert_eq!(a.len(), 0);
    DROPS.with(|drops| drops.set(0));
    drop(a);
    assert_eq!(DROPS.with(|drops| drops.get()), 0);

    let mut a = Arena::<Q0, PanickyDrop, FixedHeapBacking>::with_min_capacity(4).unwrap();
    a.insert(PanickyDrop(false));
    a.insert(PanickyDrop(true));
    assert_eq!(
        count_drops_of_panicking(|| {
            let _ = a.clear();
        }),
        2
    );
    assert!(a.is_empty());
}

#[cfg(feature = "alloc")]
#[test]
fn boxed_slice_zst_and_new() {
    // `NonZeroInxBoxedSlice::new` is the only way to get a permanently zero
    // capacity one
    let mut a = NonZeroInxBoxedSlice::<u8>::new();
    assert_eq!(a.capacity(), 0);
    assert_eq!(a.max_capacity(), Some(0));
    assert!(a.is_empty());
    assert!(a.entry_push_within_capacity().is_err());
    assert!(a.pop().is_none());

    // `Vec` reports a capacity of `usize::MAX` for ZSTs, which must not be used as
    // the number of elements to initialize
    let mut a = NonZeroInxBoxedSlice::<()>::with_min_capacity(3).unwrap();
    assert_eq!(a.capacity(), 3);
    assert_eq!(a.max_capacity(), Some(3));
    for i in 1..=3 {
        assert_eq!(a.push(()).0, nz(i));
    }
    assert!(a.entry_push_within_capacity().is_err());
    assert_eq!(a.len(), 3);
    assert_eq!(a.pop(), Some(()));

    // a ZST can be asked for a capacity that could never be allocated for a sized
    // type
    let a = NonZeroInxBoxedSlice::<()>::with_min_capacity(usize::MAX).unwrap();
    assert_eq!(a.capacity(), usize::MAX);
    assert_eq!(a.len(), 0);
}

#[cfg(feature = "alloc")]
#[test]
fn heap_backing_large_element_growth() {
    // elements larger than 1024 bytes start at a capacity of 1 instead of 4
    let mut a = NonZeroInxVec::<[u8; 2048]>::new();
    assert_eq!(a.capacity(), 0);
    a.push([0; 2048]);
    assert_eq!(a.capacity(), 1);
    a.push([1; 2048]);
    assert!(a.capacity() >= 2);

    // and the shrinking path must keep every element even when asked for less
    a.reallocate_min_capacity(0).unwrap();
    assert_eq!(a.len(), 2);
    assert!(a.capacity() >= 2);
    assert_eq!(a.pop(), Some([1; 2048]));
    assert_eq!(a.pop(), Some([0; 2048]));
    a.reallocate_min_capacity(0).unwrap();
    assert_eq!(a.capacity(), 0);
}

#[test]
fn stack_push_entry_inx() {
    // the documented contract is that `inx` is the `self.len()` immediately after a
    // successful push, i.e. one more than the length the entry was created at
    let mut a = NonZeroInxArray::<u8, 4>::new();
    for i in 1..=4 {
        let entry = a.entry_push_within_capacity().unwrap();
        assert_eq!(entry.inx(), nz(i));
        entry.push(u8::try_from(i).unwrap());
        assert_eq!(a.len(), i);
        assert_eq!(a.get(nz(i)), Some(&u8::try_from(i).unwrap()));
    }
    // cancelling leaves the next index unchanged
    a.pop().unwrap();
    let entry = a.entry_push_reallocating().unwrap();
    assert_eq!(entry.inx(), nz(4));
    drop(entry);
    assert_eq!(a.len(), 3);
    let entry = a.entry_push();
    assert_eq!(entry.inx(), nz(4));
    entry.push(4);
    assert_eq!(a.len(), 4);
}

#[test]
fn stack_zero_limit() {
    // a `LIMIT` of zero is degenerate but must still behave
    let mut a = NonZeroInxArray::<u8, 0>::new();
    assert_eq!(a.capacity(), 0);
    assert_eq!(a.max_capacity(), Some(0));
    assert!(a.is_empty());
    assert!(a.pop().is_none());
    assert!(a.get(nz(1)).is_none());
    assert!(a.push_within_capacity(0).is_err());
    // growth is impossible rather than an allocation error
    assert!(a.push_reallocating(0).is_err());
    assert!(a.entry_push_within_capacity().is_err());
    assert!(a.entry_push_reallocating().is_err());
    assert!(a.reallocate_min_capacity(0).is_ok());
    assert!(a.reallocate_min_capacity(1).is_err());
    assert!(NonZeroInxArray::<u8, 0>::with_min_capacity(0).is_ok());
    assert!(NonZeroInxArray::<u8, 0>::with_min_capacity(1).is_err());
}

/// A minimal third party [NonZeroInxGenericStack] that is permanently empty and
/// whose allocation always fails. This exercises the default trait methods
/// against an implementor outside of the crate, and is the only way to reach
/// the allocation failure paths of those defaults.
struct FaultyStack;

struct FaultyPushEntry<'a>(#[allow(dead_code)] &'a mut FaultyStack);

impl<'a> NonZeroInxGenericStackPushEntryTrait<'a, u8> for FaultyPushEntry<'a> {
    fn inx(&self) -> NonZeroUsize {
        unreachable!()
    }

    fn push(self, _t: u8) {
        unreachable!()
    }
}

// Safety: this is a stack that is always empty with zero capacity, so the
// conditions hold vacuously
unsafe impl NonZeroInxGenericStack<u8> for FaultyStack {
    type PushEntry<'a> = FaultyPushEntry<'a>;

    fn new() -> Self {
        Self
    }

    fn with_min_capacity(_min_capacity: usize) -> Result<Self, AllocError> {
        Err(AllocError)
    }

    fn capacity(&self) -> usize {
        0
    }

    fn max_capacity(&self) -> Option<usize> {
        // `None` so that the growth path gets as far as `reallocate_min_capacity`
        // instead of returning `BeyondMaxCapacity` early
        None
    }

    fn reallocate_min_capacity(&mut self, _min_capacity: usize) -> Result<(), ReallocationError> {
        Err(ReallocationError::AllocError)
    }

    fn len(&self) -> usize {
        0
    }

    fn entry_push_within_capacity(
        &mut self,
    ) -> Result<Self::PushEntry<'_>, NotWithinCapacityError> {
        Err(NotWithinCapacityError)
    }

    unsafe fn get_unchecked(&self, _inx: NonZeroUsize) -> &u8 {
        unreachable!()
    }

    unsafe fn get_unchecked_mut(&mut self, _inx: NonZeroUsize) -> &mut u8 {
        unreachable!()
    }

    unsafe fn get_disjoint_unchecked_mut<const N: usize>(
        &mut self,
        indices: [NonZeroUsize; N],
    ) -> [&mut u8; N] {
        // the closure is never called for the only reachable case of `N == 0`
        indices.map(|_| unreachable!())
    }

    fn pop(&mut self) -> Option<u8> {
        None
    }

    fn clear(&mut self) {}
}

#[test]
fn faulty_stack_defaults() {
    assert!(FaultyStack::with_min_capacity(0).is_err());

    let mut a = FaultyStack::new();
    assert_eq!(a.len(), 0);
    assert!(a.is_empty());
    assert!(a.pop().is_none());
    assert!(a.get(nz(1)).is_none());
    assert!(a.get_mut(nz(1)).is_none());
    let [] = a.get_disjoint_mut([]).unwrap();
    assert_eq!(
        a.get_disjoint_mut([nz(1)]).unwrap_err(),
        GetDisjointMutError::IndexOutOfBounds
    );

    // no capacity is available and growing always fails
    assert_eq!(
        a.push_within_capacity(0).map(|_| ()),
        Err(NotWithinCapacityError)
    );
    assert_eq!(
        a.push_reallocating(0).map(|_| ()),
        Err(ReallocationError::AllocError)
    );
    assert!(a.entry_push_within_capacity().is_err());
    assert!(a.entry_push_reallocating().is_err());
}

#[test]
#[should_panic = "`NonZeroInxGenericStack::push_reallocating` failed"]
fn faulty_stack_push_panic() {
    FaultyStack::new().push(0);
}

#[test]
#[should_panic = "`NonZeroInxGenericStack::entry_push_reallocating` failed"]
fn faulty_stack_entry_push_panic() {
    FaultyStack::new().entry_push();
}
