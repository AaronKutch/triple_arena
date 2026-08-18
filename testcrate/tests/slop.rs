//! LLM One-off instance tests for branches that the fuzz tests do not reach.
//!
//! Anything that can avoid the `alloc` feature should, so that it runs under
//! every feature configuration, which matters because `ptr.rs` and
//! `ptr_serde.rs` are separately compiled depending on `serde_support`. The
//! rest is behind `#[cfg(feature = "alloc")]`.

use core::{
    fmt,
    num::{NonZeroU8, NonZeroU128, NonZeroUsize},
    slice::GetDisjointMutError,
};
use std::{
    cell::Cell,
    panic::{AssertUnwindSafe, catch_unwind},
};

use triple_arena::{
    Arena, DirectArena, InvalidationOption, InvalidationResult, StackBacking,
    errors::{AllocError, NotWithinCapacityError, ReallocationError},
    ptr_struct,
    traits::{
        Advancer, ArenaCloneFromWith, ArenaDirectInsertEntryTrait, ArenaDirectInsertTrait,
        ArenaInsertEntryTrait, ArenaInsertTrait, ArenaTrait, CompactArenaTrait, Ptr, Recast,
    },
    utils::{
        ArenaSlot, DirectSlot, NonZeroInxArray, PtrNoGen, nzusize_iter,
        traits::{NonZeroInxGenericStack, NonZeroInxGenericStackPushEntryTrait, PtrGen, PtrInx},
    },
};
#[cfg(feature = "alloc")]
use triple_arena::{
    FixedHeapBacking, HeapBacking,
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

// `crate::arena`

ptr_struct!(QLarge[NonZeroU128]);

type A8 = Arena<Q0, u8, StackBacking<8>>;

/// Returns an arena of capacity 8 with slots `[Allocated, Free, Allocated]`
fn arena_with_hole() -> A8 {
    let mut a = A8::new();
    a.insert(0);
    let p = a.insert(1);
    a.insert(2);
    a.remove(p).allow().unwrap();
    a
}

fn q0_inx(i: usize) -> <Q0 as Ptr>::Inx {
    PtrInx::try_from_usize(nz(i)).unwrap()
}

/// A `Q0` at raw index `i` with the first valid generation
fn q0(i: usize) -> Q0 {
    Ptr::_from_raw(q0_inx(i), PtrGen::two())
}

#[test]
fn arena_default_and_indexing() {
    let a = A8::default();
    assert!(a.is_empty());
    assert_eq!(a.freelist_root(), None);
    assert_eq!(a.backing().len(), 0);

    let mut a = arena_with_hole();
    assert_eq!(a.freelist_root(), Some(q0_inx(2)));
    // the free slot is still a slot in the backing
    assert_eq!(a.backing().len(), 3);

    let p = a.find_first_inx_ptr().unwrap();
    assert_eq!(a[p], 0);
    // `Index` is also implemented for anything that borrows a `Ptr`
    assert_eq!(a[&p], 0);
    a[p] = 3;
    a[&p] = 4;
    assert_eq!(a[p], 4);
}

#[test]
#[should_panic = "indexed `Arena` with invalidated `Ptr`"]
fn arena_index_panic() {
    let a = arena_with_hole();
    let _ = a[Q0::invalid()];
}

#[test]
#[should_panic = "indexed `Arena` with invalidated `Ptr`"]
fn arena_index_mut_panic() {
    let mut a = arena_with_hole();
    a[Q0::invalid()] = 0;
}

#[test]
#[should_panic]
fn arena_get_inx_unwrap_panic() {
    // the hidden index based accessors used by the higher layers assume an
    // allocated slot, the free slot in the middle is not one
    let a = arena_with_hole();
    let _ = a.get_inx_unwrap(q0_inx(2));
}

#[test]
#[should_panic]
fn arena_get_inx_mut_unwrap_panic() {
    let mut a = arena_with_hole();
    let _ = a.get_inx_mut_unwrap(q0_inx(2));
}

#[test]
#[should_panic]
fn arena_get_inx_unwrap_untranslatable_panic() {
    // an index that no slot could exist at also has no `T` to unwrap
    let mut a = Arena::<QLarge, u8, StackBacking<4>>::new();
    a.insert(0);
    let _ = a.get_inx_unwrap(NonZeroU128::new(1 << 64).unwrap());
}

#[test]
fn arena_into_iterators() {
    let a = arena_with_hole();
    let ptrs: Vec<Q0> = a.ptrs().collect();

    // `&Arena`
    let by_ref: Vec<(Q0, u8)> = (&a).into_iter().map(|(p, t)| (p, *t)).collect();
    assert_eq!(by_ref, vec![(ptrs[0], 0), (ptrs[1], 2)]);

    // `&mut Arena`
    let mut a = a;
    for (_, t) in &mut a {
        *t = t.wrapping_add(10);
    }
    let by_ref: Vec<(Q0, u8)> = (&a).into_iter().map(|(p, t)| (p, *t)).collect();
    assert_eq!(by_ref, vec![(ptrs[0], 10), (ptrs[1], 12)]);

    // `Arena`, which drains the arena along with its capacity
    let owned: Vec<(Q0, u8)> = a.into_iter().collect();
    assert_eq!(owned, vec![(ptrs[0], 10), (ptrs[1], 12)]);
}

#[test]
fn arena_recast_values() {
    // `Recast for Arena` maps over the values, and propagates the item that the
    // recaster does not recognize
    let mut recaster = Arena::<Q1, Q1, StackBacking<4>>::new();
    let old = recaster.insert(Q1::invalid());
    let new = recaster.insert(Q1::invalid());
    *recaster.get_mut(old).unwrap() = new;

    let mut a = Arena::<Q0, Q1, StackBacking<4>>::new();
    a.insert(old);
    assert_eq!(a.recast(&recaster), Ok(()));
    assert_eq!(*a.vals().next().unwrap(), new);

    let mut a = Arena::<Q0, Q1, StackBacking<4>>::new();
    a.insert(Q1::invalid());
    assert_eq!(a.recast(&recaster), Err(Q1::invalid()));
}

#[cfg(feature = "alloc")]
#[test]
fn arena_large_element_growth() {
    // the automatic reallocation starts at a capacity of 1 instead of 4 for
    // elements larger than 1024 bytes
    let mut a = Arena::<Q0, [u8; 2048], HeapBacking>::new();
    assert_eq!(a.capacity(), 0);
    a.insert([0; 2048]);
    assert_eq!(a.capacity(), 1);
    a.insert([1; 2048]);
    assert!(a.capacity() >= 2);
}

#[test]
fn arena_clone() {
    let a = arena_with_hole();
    // the `Ptr` validities are cloned along with the entries
    let b = a.clone();
    for (p, t) in a.iter() {
        assert_eq!(b.get(p), Some(t));
    }
    assert_eq!(b.len(), a.len());
    assert_eq!(b.generation(), a.generation());
    assert_eq!(format!("{a:?}"), format!("{b:?}"));

    // `clone_from` reuses the capacity of the destination
    let mut c = A8::new();
    c.insert(42);
    c.clone_from(&a);
    for (p, t) in a.iter() {
        assert_eq!(c.get(p), Some(t));
    }
    assert_eq!(c.len(), a.len());

    // cloning from an empty arena copies the generation and clears
    let mut empty = A8::new();
    let _ = empty.clear();
    c.clone_from(&empty);
    assert!(c.is_empty());
    assert_eq!(c.generation(), empty.generation());
}

#[test]
fn arena_compress_with_panicking_map() {
    // an unwinding closure loses the entry it was called with, but the arena must
    // be left usable and internally consistent

    // panicking on the first call, where the entry is compressed in place and so
    // never leaves its slot
    let mut a = arena_with_hole();
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = a.compress_with(false, |_, _, _| panic!("map"));
    }));
    assert!(res.is_err());
    assert_eq!(a.len(), 2);
    assert_eq!(Arena::_check_invariants(&a), Ok(()));

    // panicking on the second call, which is the one that has to move an entry from
    // a later slot into the hole and therefore has it in flight
    let mut a = arena_with_hole();
    let mut n = 0;
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = a.compress_with(false, |_, _, _| {
            n += 1;
            assert_ne!(n, 2, "map");
        });
    }));
    assert!(res.is_err());
    // only the entry that was in flight was lost
    assert_eq!(a.len(), 1);
    assert_eq!(Arena::_check_invariants(&a), Ok(()));
    // and insertion still works instead of following a half rewritten freelist
    let p = a.insert(5);
    assert_eq!(a[p], 5);
    assert_eq!(Arena::_check_invariants(&a), Ok(()));
}

#[test]
fn arena_clear_invalidates_through_panicking_drop() {
    // the generation is incremented before any `T::drop` runs, so that an unwinding
    // drop still leaves every old `Ptr` invalidated
    let mut a = Arena::<Q0, PanickyDrop, StackBacking<4>>::new();
    let p = a.insert(PanickyDrop(false));
    a.insert(PanickyDrop(true));
    let generation = a.generation();
    assert_eq!(
        count_drops_of_panicking(|| {
            let _ = a.clear();
        }),
        2
    );
    assert!(a.generation() > generation);
    assert!(!a.contains(p));
    assert!(a.is_empty());
    assert_eq!(Arena::_check_invariants(&a), Ok(()));
}

#[test]
fn arena_clone_from_with_panicking_map() {
    let source = arena_with_hole();
    let mut a = A8::new();
    a.insert(42);
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = a.clone_from_with(&source, |_, _| -> u8 { panic!("map") });
    }));
    assert!(res.is_err());
    // the preexisting entry was dropped and nothing was cloned in, and the gap
    // filling free slots did not corrupt anything
    assert!(a.is_empty());
    assert_eq!(Arena::_check_invariants(&a), Ok(()));
    let p = a.insert(5);
    assert_eq!(a[p], 5);
    assert_eq!(Arena::_check_invariants(&a), Ok(()));
}

/// A minimal third party [CompactArenaTrait] that breaks the trait's
/// requirements in a configurable way, in order to reach the defensive
/// `unreachable`s of
/// [clone_from_with](triple_arena::traits::ArenaCloneFromWith::clone_from_with).
/// Only the few methods that function actually uses are implemented.
struct FaultyArena {
    /// what [find_last_inx_ptr](ArenaTrait::find_last_inx_ptr) reports
    last: Option<QLarge>,
    /// what the advancer yields, in order
    ptrs: Vec<QLarge>,
    /// if [get_inx](ArenaTrait::get_inx) should fail for everything
    no_get: bool,
}

impl FaultyArena {
    fn new(last: u128, ptrs: &[u128], no_get: bool) -> Self {
        let ptr =
            |inx: u128| -> QLarge { Ptr::_from_raw(NonZeroU128::new(inx).unwrap(), PtrGen::two()) };
        Self {
            last: Some(ptr(last)),
            ptrs: ptrs.iter().map(|inx| ptr(*inx)).collect(),
            no_get,
        }
    }
}

struct FaultyAdvancer(usize);

impl Advancer<FaultyArena> for FaultyAdvancer {
    type Item = QLarge;

    fn advance(&mut self, collection: &FaultyArena) -> Option<QLarge> {
        let res = collection.ptrs.get(self.0).copied();
        self.0 = self.0.saturating_add(1);
        res
    }

    fn empty() -> Self {
        Self(usize::MAX)
    }
}

impl ArenaTrait<QLarge, u8> for FaultyArena {
    type PtrAdvancer = FaultyAdvancer;

    fn singular_generation(&self) -> Option<<QLarge as Ptr>::Gen> {
        Some(PtrGen::two())
    }

    fn get_inx(&self, _p: <QLarge as Ptr>::Inx) -> Option<(<QLarge as Ptr>::Gen, &u8)> {
        if self.no_get {
            None
        } else {
            Some((PtrGen::two(), &0))
        }
    }

    fn find_first_inx_ptr(&self) -> Option<QLarge> {
        self.ptrs.first().copied()
    }

    fn find_last_inx_ptr(&self) -> Option<QLarge> {
        self.last
    }

    fn advancer_inx(&self, _inx: <QLarge as Ptr>::Inx, _rev: bool) -> Self::PtrAdvancer {
        FaultyAdvancer(0)
    }

    // none of the rest is used by `clone_from_with`

    fn new() -> Self {
        unimplemented!()
    }

    fn with_min_capacity(_min_capacity: usize) -> Result<Self, AllocError> {
        unimplemented!()
    }

    fn capacity(&self) -> usize {
        unimplemented!()
    }

    fn max_capacity(&self) -> Option<usize> {
        unimplemented!()
    }

    fn reallocate_min_capacity(&mut self, _min_capacity: usize) -> Result<(), ReallocationError> {
        unimplemented!()
    }

    fn len(&self) -> usize {
        unimplemented!()
    }

    fn get_disjoint_inx_mut<const N: usize>(
        &mut self,
        _indices: [<QLarge as Ptr>::Inx; N],
    ) -> Result<[(<QLarge as Ptr>::Gen, &mut u8); N], GetDisjointMutError> {
        unimplemented!()
    }

    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (QLarge, &'a mut u8)>
    where
        u8: 'a,
    {
        core::iter::empty()
    }

    fn drain(&mut self) -> impl Iterator<Item = InvalidationOption<(QLarge, u8)>> {
        core::iter::empty()
    }

    fn invalidate(&mut self, _p: QLarge) -> InvalidationResult<QLarge> {
        unimplemented!()
    }

    fn remove(&mut self, _p: QLarge) -> InvalidationResult<u8> {
        unimplemented!()
    }

    fn remove_inx(
        &mut self,
        _p: <QLarge as Ptr>::Inx,
    ) -> InvalidationResult<(<QLarge as Ptr>::Gen, u8)> {
        unimplemented!()
    }

    fn clear(&mut self) -> InvalidationOption<()> {
        unimplemented!()
    }

    fn compress_with<F: FnMut(QLarge, &mut u8, QLarge)>(
        &mut self,
        _reset_generation: bool,
        _map: F,
    ) -> InvalidationOption<()> {
        unimplemented!()
    }
}

impl CompactArenaTrait<QLarge, u8> for FaultyArena {}

/// Clones from `source` into a fresh arena with a capacity of exactly 4
fn clone_from_faulty(source: &FaultyArena) -> Result<(), ReallocationError> {
    let mut a = Arena::<QLarge, u8, StackBacking<4>>::new();
    assert_eq!(a.capacity(), 4);
    a.clone_from_with(source, |_, u| *u)
}

#[test]
fn faulty_arena_last_inx_too_big() {
    // an index that no arena could have inserted at is an allocation error rather
    // than a panic, because `reallocate_min_capacity` is not reached to report it
    assert_eq!(
        clone_from_faulty(&FaultyArena::new(1 << 64, &[], false)),
        Err(ReallocationError::AllocError)
    );
}

#[test]
#[should_panic]
fn faulty_arena_advance_inx_too_big() {
    let _ = clone_from_faulty(&FaultyArena::new(1, &[1 << 64], false));
}

#[test]
#[should_panic]
fn faulty_arena_advance_out_of_order() {
    let _ = clone_from_faulty(&FaultyArena::new(2, &[2, 1], false));
}

#[test]
#[should_panic]
fn faulty_arena_gap_beyond_capacity() {
    // `find_last_inx_ptr` said 1, so only a capacity of 1 was ensured and filling
    // the gap up to index 6 runs out
    let _ = clone_from_faulty(&FaultyArena::new(1, &[6], false));
}

#[test]
#[should_panic]
fn faulty_arena_entry_beyond_capacity() {
    // the gap filling exactly uses up the capacity, so the entry itself is the one
    // that does not fit
    let _ = clone_from_faulty(&FaultyArena::new(1, &[5], false));
}

#[test]
#[should_panic]
fn faulty_arena_advance_unknown_ptr() {
    let _ = clone_from_faulty(&FaultyArena::new(1, &[1], true));
}

/// Clones from `source` into a fresh direct insertion arena with a capacity of
/// exactly 4. `clone_from_with` has its own implementation there, so it needs
/// its own set of these.
fn direct_clone_from_faulty(source: &FaultyArena) -> Result<(), ReallocationError> {
    let mut a = DirectArena::<QLarge, u8, StackBacking<4>>::new();
    assert_eq!(a.capacity(), 4);
    a.clone_from_with(source, |_, u| *u)
}

#[test]
fn faulty_direct_arena_last_inx_too_big() {
    assert_eq!(
        direct_clone_from_faulty(&FaultyArena::new(1 << 64, &[], false)),
        Err(ReallocationError::AllocError)
    );
}

#[test]
#[should_panic]
fn faulty_direct_arena_advance_inx_too_big() {
    let _ = direct_clone_from_faulty(&FaultyArena::new(1, &[1 << 64], false));
}

#[test]
#[should_panic]
fn faulty_direct_arena_advance_out_of_order() {
    let _ = direct_clone_from_faulty(&FaultyArena::new(2, &[2, 1], false));
}

#[test]
#[should_panic]
fn faulty_direct_arena_gap_beyond_capacity() {
    let _ = direct_clone_from_faulty(&FaultyArena::new(1, &[6], false));
}

#[test]
#[should_panic]
fn faulty_direct_arena_entry_beyond_capacity() {
    let _ = direct_clone_from_faulty(&FaultyArena::new(1, &[5], false));
}

#[test]
#[should_panic]
fn faulty_direct_arena_advance_unknown_ptr() {
    let _ = direct_clone_from_faulty(&FaultyArena::new(1, &[1], true));
}

/// Returns an arena whose freelist root points at an allocated slot, which is
/// exactly what the `# Safety` section of
/// [set_freelist_root](Arena::set_freelist_root) forbids
fn arena_with_broken_freelist() -> A8 {
    let mut a = arena_with_hole();
    unsafe { a.set_freelist_root(Some(q0_inx(1))) };
    a
}

#[test]
#[should_panic]
fn arena_broken_freelist_insert_panic() {
    let _ = arena_with_broken_freelist().insert_within_capacity(9);
}

#[test]
#[should_panic]
fn arena_broken_freelist_entry_insert_panic() {
    let mut a = arena_with_broken_freelist();
    let entry = a.entry_insert_within_capacity().unwrap();
    entry.insert(9);
}

#[test]
fn arena_check_invariants_detects_corruption() {
    let mut a = arena_with_hole();
    assert_eq!(Arena::_check_invariants(&a), Ok(()));

    // the generation must never be below the first valid generation
    let generation = a.generation();
    a.set_generation(PtrGen::one());
    assert_eq!(Arena::_check_invariants(&a), Err("bad generation"));
    a.set_generation(generation);

    // `len` counts allocated entries and cannot exceed the capacity
    unsafe { a.set_len(usize::MAX) };
    assert_eq!(Arena::_check_invariants(&a), Err("len > capacity"));
    unsafe { a.set_len(1) };
    assert_eq!(Arena::_check_invariants(&a), Err("len != n_allocated"));
    unsafe { a.set_len(2) };
    assert_eq!(Arena::_check_invariants(&a), Ok(()));

    // there is a free slot, so the freelist root cannot be unset
    unsafe { a.set_freelist_root(None) };
    assert_eq!(Arena::_check_invariants(&a), Err("bad freelist_root"));
    // the root must point at an existing slot
    unsafe { a.set_freelist_root(Some(q0_inx(9))) };
    assert_eq!(Arena::_check_invariants(&a), Err("getting entry failed"));
    // ... and that slot must be a free one
    unsafe { a.set_freelist_root(Some(q0_inx(1))) };
    assert_eq!(Arena::_check_invariants(&a), Err("bad freelist node"));
    unsafe { a.set_freelist_root(Some(q0_inx(2))) };
    assert_eq!(Arena::_check_invariants(&a), Ok(()));

    // every free slot must be reachable from the root
    let mut a = A8::new();
    let p0 = a.insert(0);
    let p1 = a.insert(1);
    a.insert(2);
    a.remove(p0).allow().unwrap();
    a.remove(p1).allow().unwrap();
    assert_eq!(Arena::_check_invariants(&a), Ok(()));
    unsafe { a.set_freelist_root(Some(q0_inx(1))) };
    assert_eq!(Arena::_check_invariants(&a), Err("freelist discontinuous"));

    // the freelist must terminate by pointing at itself
    unsafe {
        *a.backing_mut().get_mut(nz(1)).unwrap() = ArenaSlot::Free(q0_inx(2));
        *a.backing_mut().get_mut(nz(2)).unwrap() = ArenaSlot::Free(q0_inx(1));
    }
    assert_eq!(Arena::_check_invariants(&a), Err("endless loop"));

    // an index that cannot round trip back to a `NonZeroUsize` is caught
    let mut a = Arena::<QLarge, u8, StackBacking<4>>::new();
    let p = a.insert(0);
    a.insert(1);
    a.remove(p).allow().unwrap();
    assert_eq!(Arena::_check_invariants(&a), Ok(()));
    unsafe { a.set_freelist_root(Some(NonZeroU128::new(1 << 64).unwrap())) };
    assert_eq!(Arena::_check_invariants(&a), Err("try_into_usize failed"));
}

// ============================== `crate::arena` direct insertion ==============

type D8 = DirectArena<Q0, u8, StackBacking<8>>;

/// Returns a direct insertion arena of capacity 8 with slots
/// `[Allocated, Free, Allocated]`, which is the same layout that
/// [arena_with_hole] has
fn direct_arena_with_hole() -> D8 {
    let mut a = D8::new();
    for i in 1..=3 {
        a.direct_insert_within_capacity(q0(i))
            .unwrap()
            .insert((i - 1) as u8);
    }
    a.remove(q0(2)).allow().unwrap();
    a
}

#[test]
fn direct_arena_default_and_indexing() {
    let a = D8::default();
    assert!(a.is_empty());
    assert_eq!(a.backing().len(), 0);
    // there is never a singular generation
    assert_eq!(a.singular_generation(), None);

    let mut a = direct_arena_with_hole();
    assert_eq!(a.len(), 2);
    // unlike the base arena there is no freelist, and the free slot in the middle
    // is simply skipped over
    assert_eq!(a.backing().len(), 3);

    let p = a.find_first_inx_ptr().unwrap();
    assert_eq!(a[p], 0);
    // `Index` is also implemented for anything that borrows a `Ptr`
    assert_eq!(a[&p], 0);
    a[p] = 3;
    a[&p] = 4;
    assert_eq!(a[p], 4);

    // the hidden index based accessors used by the higher layers
    assert_eq!(*a.get_inx_unwrap(q0_inx(1)), 4);
    *a.get_inx_mut_unwrap(q0_inx(1)) = 5;
    assert_eq!(a[p], 5);

    // `invalidate` can only report whether the `Ptr` is valid
    assert_eq!(a.invalidate(p), InvalidationResult::Success(p));
    assert!(a.invalidate(q0(2)).is_invalid());
    assert!(a.invalidate(Q0::invalid()).is_invalid());
}

#[test]
#[should_panic = "indexed `DirectArena` with invalidated `Ptr`"]
fn direct_arena_index_panic() {
    let a = direct_arena_with_hole();
    let _ = a[Q0::invalid()];
}

#[test]
#[should_panic = "indexed `DirectArena` with invalidated `Ptr`"]
fn direct_arena_index_mut_panic() {
    let mut a = direct_arena_with_hole();
    a[Q0::invalid()] = 0;
}

#[test]
#[should_panic]
fn direct_arena_get_inx_unwrap_panic() {
    let a = direct_arena_with_hole();
    let _ = a.get_inx_unwrap(q0_inx(2));
}

#[test]
#[should_panic]
fn direct_arena_get_inx_mut_unwrap_panic() {
    let mut a = direct_arena_with_hole();
    let _ = a.get_inx_mut_unwrap(q0_inx(2));
}

#[test]
#[should_panic]
fn direct_arena_get_inx_unwrap_untranslatable_panic() {
    // an index that no slot could exist at also has no `T` to unwrap
    let mut a = DirectArena::<QLarge, u8, StackBacking<4>>::new();
    let p: QLarge = Ptr::_from_raw(NonZeroU128::new(1).unwrap(), PtrGen::two());
    a.direct_insert_within_capacity(p).unwrap().insert(0);
    let _ = a.get_inx_unwrap(NonZeroU128::new(1 << 64).unwrap());
}

#[test]
fn direct_arena_into_iterators() {
    let a = direct_arena_with_hole();
    let ptrs: Vec<Q0> = a.ptrs().collect();

    // `&DirectArena`
    let by_ref: Vec<(Q0, u8)> = (&a).into_iter().map(|(p, t)| (p, *t)).collect();
    assert_eq!(by_ref, vec![(ptrs[0], 0), (ptrs[1], 2)]);

    // `&mut DirectArena`
    let mut a = a;
    for (_, t) in &mut a {
        *t = t.wrapping_add(10);
    }
    let by_ref: Vec<(Q0, u8)> = (&a).into_iter().map(|(p, t)| (p, *t)).collect();
    assert_eq!(by_ref, vec![(ptrs[0], 10), (ptrs[1], 12)]);

    // `DirectArena`, which drains the arena along with its capacity
    let owned: Vec<(Q0, u8)> = a.into_iter().collect();
    assert_eq!(owned, vec![(ptrs[0], 10), (ptrs[1], 12)]);
}

#[test]
fn direct_arena_recast_values() {
    // `Recast for DirectArena` maps over the values, and propagates the item that
    // the recaster does not recognize
    let q1 = |i: usize| -> Q1 { Ptr::_from_raw(PtrInx::try_from_usize(nz(i)).unwrap(), ()) };
    let mut recaster = DirectArena::<Q1, Q1, StackBacking<4>>::new();
    let old = q1(1);
    let new = q1(2);
    for p in [old, new] {
        recaster
            .direct_insert_within_capacity(p)
            .unwrap()
            .insert(Q1::invalid());
    }
    *recaster.get_mut(old).unwrap() = new;

    let mut a = DirectArena::<Q0, Q1, StackBacking<4>>::new();
    a.direct_insert_within_capacity(q0(1)).unwrap().insert(old);
    assert_eq!(a.recast(&recaster), Ok(()));
    assert_eq!(*a.vals().next().unwrap(), new);

    let mut a = DirectArena::<Q0, Q1, StackBacking<4>>::new();
    a.direct_insert_within_capacity(q0(1))
        .unwrap()
        .insert(Q1::invalid());
    assert_eq!(a.recast(&recaster), Err(Q1::invalid()));
}

#[test]
fn direct_arena_clone() {
    let a = direct_arena_with_hole();
    // the `Ptr` validities are cloned along with the entries
    let b = a.clone();
    for (p, t) in a.iter() {
        assert_eq!(b.get(p), Some(t));
    }
    assert_eq!(b.len(), a.len());
    assert_eq!(format!("{a:?}"), format!("{b:?}"));

    // `clone_from` reuses the capacity of the destination
    let mut c = D8::new();
    c.direct_insert_within_capacity(q0(4)).unwrap().insert(42);
    c.clone_from(&a);
    for (p, t) in a.iter() {
        assert_eq!(c.get(p), Some(t));
    }
    assert_eq!(c.len(), a.len());
    // the entry that only the destination had is gone
    assert!(!c.contains(q0(4)));

    // cloning from an empty arena just clears
    c.clone_from(&D8::new());
    assert!(c.is_empty());
    assert_eq!(c.backing().len(), 0);
}

#[test]
fn direct_arena_compress_with_panicking_map() {
    // an unwinding closure loses the entry it was called with, but the arena must
    // be left usable and internally consistent

    // panicking on the first call, where the entry is compressed in place and so
    // never leaves its slot
    let mut a = direct_arena_with_hole();
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = a.compress_with(false, |_, _, _| panic!("map"));
    }));
    assert!(res.is_err());
    assert_eq!(a.len(), 2);
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));

    // panicking on the second call, which is the one that has to move an entry from
    // a later slot into the hole and therefore has it in flight
    let mut a = direct_arena_with_hole();
    let mut n = 0;
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = a.compress_with(false, |_, _, _| {
            n += 1;
            assert_ne!(n, 2, "map");
        });
    }));
    assert!(res.is_err());
    // only the entry that was in flight was lost, and `len` accounts for it
    assert_eq!(a.len(), 1);
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));
    // the free slots that the unwind left on the end are valid state and are
    // deliberately kept, see `pop_free_end_slots`
    assert_eq!(a.backing().len(), 3);
    // and direct insertion into a vacated slot still works, reusing one of them
    // instead of pushing again
    let p = q0(2);
    a.direct_insert_within_capacity(p).unwrap().insert(5);
    assert_eq!(a[p], 5);
    assert_eq!(a.backing().len(), 3);
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));
}

#[test]
fn direct_arena_compress_preserves_generations() {
    // unlike the base arena, the compress functions carry each generation along
    // with its entry and `reset_generation` does nothing
    let mut a = D8::new();
    let p1: Q0 = Ptr::_from_raw(q0_inx(1), PtrGen::two());
    let p3: Q0 = Ptr::_from_raw(q0_inx(3), PtrGen::generational_inc(PtrGen::two()).0);
    a.direct_insert_within_capacity(p1).unwrap().insert(0);
    a.direct_insert_within_capacity(p3).unwrap().insert(2);

    let mut map = vec![];
    assert_eq!(
        a.compress_with(true, |p_old, _, p_new| map.push((p_old, p_new))),
        InvalidationOption::Success(())
    );
    assert_eq!(map, vec![
        (p1, p1),
        (p3, Ptr::_from_raw(q0_inx(2), p3.generation()))
    ]);
    assert_eq!(a.backing().len(), 2);
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));
}

#[test]
fn direct_arena_clone_from_with_panicking_map() {
    let source = direct_arena_with_hole();

    // panicking on the first call
    let mut a = D8::new();
    a.direct_insert_within_capacity(q0(1)).unwrap().insert(42);
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = a.clone_from_with(&source, |_, _| -> u8 { panic!("map") });
    }));
    assert!(res.is_err());
    // the preexisting entry was dropped and nothing was cloned in
    assert!(a.is_empty());
    assert_eq!(a.backing().len(), 0);
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));

    // panicking on the second call, which is after the free slots filling the gap
    // were already pushed
    let mut a = D8::new();
    let mut n = 0;
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = a.clone_from_with(&source, |_, t| {
            n += 1;
            assert_ne!(n, 2, "map");
            *t
        });
    }));
    assert!(res.is_err());
    assert_eq!(a.len(), 1);
    // the free slot that was pushed to fill the gap is left in place
    assert_eq!(a.backing().len(), 2);
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));
    let p = q0(2);
    a.direct_insert_within_capacity(p).unwrap().insert(5);
    assert_eq!(a[p], 5);
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));
}

#[test]
fn direct_arena_pop_free_end_slots() {
    let mut a = direct_arena_with_hole();
    // `[Allocated, Free, Allocated]`, so there is nothing free on the end yet
    assert_eq!(a.backing().len(), 3);
    assert_eq!(a.pop_free_end_slots(usize::MAX), 0);
    assert_eq!(a.backing().len(), 3);

    // removing does not pop, unlike the base arena which has to keep its freelist
    // reachable
    a.remove(q0(3)).allow().unwrap();
    assert_eq!(a.backing().len(), 3);

    // only as many as asked for, and the count is reported back
    assert_eq!(a.pop_free_end_slots(1), 1);
    assert_eq!(a.backing().len(), 2);
    assert_eq!(a.pop_free_end_slots(0), 0);
    assert_eq!(a.backing().len(), 2);

    // it stops at the allocated slot rather than at the requested count, and an
    // empty backing stops it too
    assert_eq!(a.pop_free_end_slots(usize::MAX), 1);
    assert_eq!(a.backing().len(), 1);
    assert_eq!(a.pop_free_end_slots(usize::MAX), 0);
    a.remove(q0(1)).allow().unwrap();
    assert_eq!(a.pop_free_end_slots(usize::MAX), 1);
    assert!(a.is_empty());
    assert_eq!(a.backing().len(), 0);
    assert_eq!(a.pop_free_end_slots(usize::MAX), 0);
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));
}

#[cfg(feature = "alloc")]
#[test]
fn direct_arena_shrinking_pops_only_what_it_needs() {
    // the free end slots are what stands in the way of a reduction, so exactly
    // those are popped and no more
    let mut a = DirectArena::<Q0, u8, HeapBacking>::new();
    a.reallocate_min_capacity(8).unwrap();
    for i in 1..=6 {
        a.direct_insert_within_capacity(q0(i))
            .unwrap()
            .insert(i as u8);
    }
    for i in 2..=6 {
        a.remove(q0(i)).allow().unwrap();
    }
    assert_eq!(a.len(), 1);
    assert_eq!(a.backing().len(), 6);

    // asking for 4 only needs the two slots past index 4 gone
    a.reallocate_min_capacity(4).unwrap();
    assert_eq!(a.backing().len(), 4);
    assert!(a.capacity() >= 4);

    // and the one allocated slot is the floor on how far this can go
    a.reallocate_min_capacity(0).unwrap();
    assert_eq!(a.backing().len(), 1);
    assert!(a.contains(q0(1)));
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));
}

#[test]
fn direct_arena_transfer_reallocating_panicking_map() {
    let mut source = arena_with_hole();
    let mut a = D8::new();
    let mut n = 0;
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = a.transfer_reallocating(PtrGen::two(), &mut source, |_, o, _| {
            n += 1;
            assert_ne!(n, 2, "map");
            o.allow()
        });
    }));
    assert!(res.is_err());
    // the entry that `map` was called with is lost, and the rest is split between
    // the entries that were already transferred and the ones that were not
    assert_eq!(a.len(), 1);
    assert_eq!(source.len(), 0);
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));
    assert_eq!(Arena::_check_invariants(&source), Ok(()));
}

#[test]
fn direct_arena_check_invariants_detects_corruption() {
    let mut a = direct_arena_with_hole();
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));

    // `len` counts allocated entries and cannot exceed the capacity
    unsafe { a.set_len(usize::MAX) };
    assert_eq!(DirectArena::_check_invariants(&a), Err("len > capacity"));
    unsafe { a.set_len(1) };
    assert_eq!(
        DirectArena::_check_invariants(&a),
        Err("len != n_allocated")
    );
    unsafe { a.set_len(2) };
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));

    // filling in the hole through the backing needs the matching `set_len`
    unsafe {
        *a.backing_mut().get_mut(nz(2)).unwrap() = DirectSlot::Allocated(PtrGen::two(), 7);
    }
    assert_eq!(
        DirectArena::_check_invariants(&a),
        Err("len != n_allocated")
    );
    unsafe { a.set_len(3) };
    assert_eq!(DirectArena::_check_invariants(&a), Ok(()));
    assert_eq!(a[q0(2)], 7);
}
