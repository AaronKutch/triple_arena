//! LLM One-off instance tests for branches that the fuzz tests of the chain,
//! ord, and surject layers do not reach.
//!
//! Anything that can avoid the `alloc` feature should, so that it runs under
//! every feature configuration. See also the notes in `basics_slop.rs`.

use core::{
    fmt::{self, Write},
    hash::{Hash, Hasher},
    num::{NonZeroU8, NonZeroU128, NonZeroUsize},
    slice::GetDisjointMutError,
};
use std::{
    cmp::Ordering,
    collections::hash_map::DefaultHasher,
    panic::{AssertUnwindSafe, catch_unwind},
};

use triple_arena::{
    Arena, ChainArena, DirectArena, InvalidationOption, InvalidationResult, Link, LinkInsertKind,
    LinkNoGen, StackBacking,
    chain_iterators::ChainPtrAdvancer,
    errors::{AllocError, ChainInsertionError, ReallocationError},
    ptr_struct,
    traits::{
        Advancer, ArenaInsertTrait, ArenaTrait, ChainArenaTrait, CompactArenaTrait, Ptr, Recast,
    },
    utils::{
        ArenaSlot, ChainArenaInsertEntry,
        traits::{NonZeroInxGenericStack, PtrGen, PtrInx},
    },
};
#[cfg(feature = "alloc")]
use triple_arena::{
    HeapBacking, LimitedHeapBacking, errors::MaxCapacityReductionError,
    utils::traits::SetMaxCapacity,
};

ptr_struct!(Q0);
ptr_struct!(Q1);
ptr_struct!(QSmall[NonZeroU8]);
ptr_struct!(QLargeInx[NonZeroU128]);

type C8 = ChainArena<Q0, u8, StackBacking<8>>;

fn nz(x: usize) -> NonZeroUsize {
    NonZeroUsize::new(x).unwrap()
}

fn q0_inx(i: usize) -> <Q0 as Ptr>::Inx {
    PtrInx::try_from_usize(nz(i)).unwrap()
}

/// The chain that `p` is a part of, in `advancer_chain` order
fn chain_of<P: Ptr, T: Copy, A: ChainArenaTrait<P, T>>(a: &A, p: P) -> Vec<T> {
    a.iter_chain(p).unwrap().map(|(_, link)| link.t).collect()
}

/// The raw indexes of the whole arena in advancer order, paired with the value
fn layout<P: Ptr, T: Copy, A: ArenaTrait<P, T>>(a: &A) -> Vec<(usize, T)> {
    a.iter()
        .map(|(p, t)| (PtrInx::try_into_usize(p.inx()).unwrap().get(), *t))
        .collect()
}

/// `0 -> 1 -> 2` with `p_init` being the middle link, plus a separate
/// `3 -> 4 -> 3` cyclic chain entered at its second link
fn mixed_chains() -> (C8, Q0, Q0) {
    let mut a = C8::new();
    let p0 = a.insert(LinkInsertKind::Disconnected, 0);
    let p1 = a.insert(LinkInsertKind::ChainEnd(p0), 1);
    a.insert(LinkInsertKind::ChainEnd(p1), 2);
    let p3 = a.insert(LinkInsertKind::SingleLinkCyclic, 3);
    let p4 = a.insert(LinkInsertKind::NextTo(p3), 4);
    (a, p1, p4)
}

#[test]
fn chain_drain_matches_advancer_order() {
    // REF(chain_drain_ordering) `drain_chain` has to yield the same order as
    // `advancer_chain` for the same starting `Ptr`, which is what
    // `transfer_canonical_reallocating` relies on to lay chains out in order
    let (a, p_middle, p_cyclic) = mixed_chains();
    for p in [p_middle, p_cyclic] {
        let expected = chain_of(&a, p);
        let mut b = a.clone();
        let drained: Vec<u8> = b.drain_chain(p).unwrap().map(|o| o.allow().1.t).collect();
        assert_eq!(drained, expected);
        // only that one chain was removed
        assert_eq!(b.len(), a.len() - expected.len());
        assert_eq!(ChainArena::_check_invariants(&b), Ok(()));
    }

    // starting in the middle of an acyclic chain goes forwards first and then
    // backwards from the start
    assert_eq!(chain_of(&a, p_middle), vec![1, 2, 0]);
    // and a cyclic chain always goes forwards
    assert_eq!(chain_of(&a, p_cyclic), vec![4, 3]);
}

#[test]
fn chain_drain_chain_partial_drop() {
    // dropping the iterator early still removes the rest of the chain, and only
    // the chain
    let (mut a, p_middle, _) = mixed_chains();
    let mut drain = a.drain_chain(p_middle).unwrap();
    assert_eq!(drain.next().unwrap().allow().1.t, 1);
    drop(drain);
    assert_eq!(a.len(), 2);
    assert_eq!(ChainArena::_check_invariants(&a), Ok(()));
}

#[test]
fn transfer_canonical_reallocating_layout() {
    // every chain gets one contiguous run of indexes in `next` order, starting
    // at the start link of an acyclic chain
    let (mut source, ..) = mixed_chains();
    let mut dst = ChainArena::<Q1, u8, StackBacking<8>>::new();
    let mut recaster = DirectArena::<Q0, Q1, StackBacking<8>>::new();
    dst.transfer_canonical_reallocating(
        PtrGen::two(),
        &mut source,
        |_, o, _| o.allow(),
        &mut recaster,
    )
    .unwrap();
    assert!(source.is_empty());
    assert_eq!(ChainArena::_check_invariants(&dst), Ok(()));
    assert_eq!(layout(&dst), vec![(1, 0), (2, 1), (3, 2), (4, 3), (5, 4)]);
    // the chains are the same ones, and the recaster is a complete mapping
    let p0 = dst.find_first_inx_ptr().unwrap();
    assert_eq!(chain_of(&dst, p0), vec![0, 1, 2]);
    assert_eq!(recaster.len(), 5);

    // an empty source is the same as a clear
    let mut source = ChainArena::<Q0, u8, StackBacking<8>>::new();
    dst.transfer_canonical_reallocating(
        PtrGen::two(),
        &mut source,
        |_, o, _| o.allow(),
        &mut recaster,
    )
    .unwrap();
    assert!(dst.is_empty());
    assert!(recaster.is_empty());
}

#[test]
fn transfer_canonical_reallocating_panicking_map() {
    // the links that did arrive are valid prefixes of their chains instead of
    // having interlinks to links that never arrive
    let (mut source, ..) = mixed_chains();
    let mut dst = ChainArena::<Q1, u8, StackBacking<8>>::new();
    let mut recaster = DirectArena::<Q0, Q1, StackBacking<8>>::new();
    let mut n = 0;
    let res = catch_unwind(AssertUnwindSafe(|| {
        dst.transfer_canonical_reallocating(
            PtrGen::two(),
            &mut source,
            |_, o, _| {
                n += 1;
                assert_ne!(n, 2, "map");
                o.allow()
            },
            &mut recaster,
        )
        .unwrap();
    }));
    assert!(res.is_err());
    // the first link arrived, the second was lost to `map`, and the rest of the
    // chain it was in was dropped
    assert_eq!(dst.len(), 1);
    assert_eq!(ChainArena::_check_invariants(&dst), Ok(()));
    // the chains that had not been reached are untouched and still valid
    assert_eq!(source.len(), 2);
    assert_eq!(ChainArena::_check_invariants(&source), Ok(()));
}

#[test]
fn link_formatting() {
    let mut a = C8::new();
    let p0 = a.insert(LinkInsertKind::Disconnected, 0);
    let p1 = a.insert(LinkInsertKind::ChainEnd(p0), 1);
    let p2 = a.insert(LinkInsertKind::ChainEnd(p1), 2);

    // the start and end of a chain print the direction they are missing
    let start = a.get_link_no_gen(p0).unwrap();
    assert_eq!(format!("{start:?}"), "{(start), 2} 0");
    assert_eq!(format!("{start}"), "{(start), 2} 0");
    let end = a.get_link_no_gen(p2).unwrap();
    assert_eq!(format!("{end:?}"), "{2, (end)} 2");
    assert_eq!(format!("{end}"), "{2, (end)} 2");
    // and the middle prints both interlinks in hex
    let middle = a.get_link_no_gen(p1).unwrap();
    assert_eq!(format!("{middle:?}"), "{1, 3} 1");
    assert_eq!(format!("{middle}"), "{1, 3} 1");
    // the alternate forms only affect the `T`
    assert_eq!(format!("{middle:#?}"), "{1, 3} 1");
    assert_eq!(format!("{middle:#}"), "{1, 3} 1");

    // `Link` formats through `no_gen_ref`, so it looks the same
    let middle = a.get_link(p1).unwrap();
    assert_eq!(format!("{middle:?}"), "{1, 3} 1");
    assert_eq!(format!("{middle}"), "{1, 3} 1");
    assert_eq!(format!("{middle:#?}"), "{1, 3} 1");
    assert_eq!(format!("{middle:#}"), "{1, 3} 1");

    // and the whole arena is a map of them
    assert_eq!(
        format!("{a:?}"),
        "{Q0[1](2): {(start), 2} 0, Q0[2](2): {1, 3} 1, Q0[3](2): {2, (end)} 2}"
    );

    let empty = C8::default();
    assert_eq!(format!("{empty:?}"), "{}");
}

/// A `fmt::Write` that starts failing after `remaining` writes, for reaching
/// the error propagation of the formatting impls
struct FailingWriter {
    remaining: usize,
}

impl fmt::Write for FailingWriter {
    fn write_str(&mut self, _s: &str) -> fmt::Result {
        if self.remaining == 0 {
            Err(fmt::Error)
        } else {
            self.remaining -= 1;
            Ok(())
        }
    }
}

#[test]
fn link_formatting_errors() {
    // every write of the interlink prelude propagates a formatter error instead
    // of being ignored, for both the interlink and the `(start)`/`(end)` forms
    let mut a = C8::new();
    let p0 = a.insert(LinkInsertKind::Disconnected, 0);
    let p1 = a.insert(LinkInsertKind::ChainEnd(p0), 1);
    for p in [p0, p1] {
        let link = a.get_link_no_gen(p).unwrap();
        for alternate in [false, true] {
            for debug in [false, true] {
                // walk the failure point outwards until the whole thing fits, so
                // that every write in between gets to be the failing one
                let mut first_ok = None;
                for i in 0..16 {
                    let mut w = FailingWriter { remaining: i };
                    let res = match (debug, alternate) {
                        (true, false) => write!(w, "{link:?}"),
                        (true, true) => write!(w, "{link:#?}"),
                        (false, false) => write!(w, "{link}"),
                        (false, true) => write!(w, "{link:#}"),
                    };
                    if res.is_ok() {
                        first_ok = Some(i);
                        break;
                    }
                }
                assert!(first_ok.is_some());
            }
        }
    }
}

fn hash_of<T: Hash>(t: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    t.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn link_traits() {
    let p1: Q0 = Ptr::_from_raw(q0_inx(1), PtrGen::two());
    let p2: Q0 = Ptr::_from_raw(q0_inx(2), PtrGen::two());

    // `Link` keeps whole `Ptr`s and `LinkNoGen` only the indexes
    let link = Link::new((Some(p1), Some(p2)), 5u8);
    assert_eq!(link.prev(), Some(p1));
    assert_eq!(link.next(), Some(p2));
    assert_eq!(link.prev_next(), (Some(p1), Some(p2)));
    let no_gen = link.no_gen_ref();
    assert_eq!(no_gen.prev_next(), (Some(p1.inx()), Some(p2.inx())));
    assert_eq!(*no_gen.t, 5);
    let no_gen = link.no_gen();
    assert_eq!(no_gen.prev_next(), (Some(p1.inx()), Some(p2.inx())));
    assert_eq!(no_gen.t, 5);

    // the derived-by-hand impls all compare the interlinks first and the `T`
    // second
    for (a, b, ord) in [
        (
            Link::new((Some(p1), Some(p2)), 5u8),
            Link::new((Some(p1), Some(p2)), 5u8),
            Ordering::Equal,
        ),
        (
            Link::new((Some(p1), Some(p2)), 5u8),
            Link::new((Some(p1), Some(p2)), 6u8),
            Ordering::Less,
        ),
        (
            Link::new((Some(p2), Some(p2)), 5u8),
            Link::new((Some(p1), Some(p2)), 6u8),
            Ordering::Greater,
        ),
    ] {
        assert_eq!(a.cmp(&b), ord);
        assert_eq!(a.partial_cmp(&b), Some(ord));
        assert_eq!(a == b, ord == Ordering::Equal);
        assert_eq!(hash_of(&a) == hash_of(&b), ord == Ordering::Equal);
        // `LinkNoGen` behaves the same on its own
        let (a, b) = (a.no_gen(), b.no_gen());
        assert_eq!(a.cmp(&b), ord);
        assert_eq!(a.partial_cmp(&b), Some(ord));
        assert_eq!(a == b, ord == Ordering::Equal);
        assert_eq!(hash_of(&a) == hash_of(&b), ord == Ordering::Equal);
        // and `Clone` and `Copy` preserve everything
        #[allow(clippy::clone_on_copy)]
        let c = a.clone();
        assert_eq!(c, a);
        let c = a;
        assert_eq!(c, a);
    }

    let link = Link::new((Some(p1), Some(p2)), 5u8);
    #[allow(clippy::clone_on_copy)]
    let c = link.clone();
    assert_eq!(c, link);
    let c = link;
    assert_eq!(c, link);
}

#[test]
fn chain_arena_clone_and_default() {
    let (a, ..) = mixed_chains();
    let b = a.clone();
    assert_eq!(ChainArena::_check_invariants(&b), Ok(()));
    for (p, link) in a.iter_link_no_gen() {
        assert_eq!(b.get_link_no_gen(p).unwrap().prev_next(), link.prev_next());
    }

    // `clone_from` reuses the capacity and overwrites everything
    let mut c = C8::default();
    assert!(c.is_empty());
    c.insert(LinkInsertKind::Disconnected, 9);
    c.clone_from(&a);
    assert_eq!(ChainArena::_check_invariants(&c), Ok(()));
    assert_eq!(c.len(), a.len());
    for (p, link) in a.iter_link_no_gen() {
        assert_eq!(c.get_link_no_gen(p).unwrap().prev_next(), link.prev_next());
    }

    // and `clone_from_with` is the fallible mapping version
    let mut d = ChainArena::<Q0, u16, StackBacking<8>>::new();
    d.clone_from_with(&a, |_, link| u16::from(link.t) + 100)
        .unwrap();
    assert_eq!(ChainArena::_check_invariants(&d), Ok(()));
    for (p, link) in a.iter_link_no_gen() {
        assert_eq!(d.get_link_no_gen(p).unwrap().prev_next(), link.prev_next());
        assert_eq!(d[p], u16::from(link.t) + 100);
    }
}

#[test]
fn chain_arena_from_arena_and_clone_to_arena() {
    let (a, ..) = mixed_chains();

    // the interlink structure is dropped on the way to a plain arena
    let mut plain = Arena::<Q0, u8, StackBacking<8>>::new();
    a.clone_to_arena(&mut plain, |_, link| link.t).unwrap();
    assert_eq!(plain.len(), a.len());
    for (p, t) in a.iter() {
        assert_eq!(plain[p], *t);
    }

    // and going back through `from_arena` only succeeds if the interlinks of the
    // source arena happen to be transitive
    let mut arena = Arena::<Q0, LinkNoGen<Q0, u8>, StackBacking<8>>::new();
    for (_, link) in a.iter_link_no_gen() {
        arena.insert(LinkNoGen::new(link.prev_next(), link.t));
    }
    let rebuilt = ChainArena::from_arena(arena).unwrap();
    assert_eq!(ChainArena::_check_invariants(&rebuilt), Ok(()));

    let mut arena = Arena::<Q0, LinkNoGen<Q0, u8>, StackBacking<8>>::new();
    arena.insert(LinkNoGen::new((None, Some(q0_inx(1))), 0));
    assert_eq!(
        ChainArena::from_arena(arena).map(|_| ()),
        Err("interlink transitivity does not hold")
    );
}

#[test]
fn chain_arena_recast_values() {
    // `Recast for ChainArena` maps over the values and propagates the item that
    // the recaster does not recognize, and the interlinks are left alone because
    // they belong to the arena itself
    let mut recaster = Arena::<Q1, Q1, StackBacking<4>>::new();
    let old = recaster.insert(Q1::invalid());
    let new = recaster.insert(Q1::invalid());
    *recaster.get_mut(old).unwrap() = new;

    let mut a = ChainArena::<Q0, Q1, StackBacking<4>>::new();
    let p0 = a.insert(LinkInsertKind::Disconnected, old);
    let p1 = a.insert(LinkInsertKind::ChainEnd(p0), old);
    assert_eq!(a.recast(&recaster), Ok(()));
    assert_eq!(a[p0], new);
    assert_eq!(a[p1], new);
    assert_eq!(a.get_link_no_gen(p1).unwrap().prev(), Some(p0.inx()));

    let mut a = ChainArena::<Q0, Q1, StackBacking<4>>::new();
    a.insert(LinkInsertKind::Disconnected, Q1::invalid());
    assert_eq!(a.recast(&recaster), Err(Q1::invalid()));
}

#[test]
fn chain_arena_indexing_and_panics() {
    let (mut a, p_middle, _) = mixed_chains();
    assert_eq!(a[p_middle], 1);
    a[p_middle] = 7;
    assert_eq!(a[p_middle], 7);
    assert_eq!(*a.get_inx_unwrap(p_middle.inx()), 7);
    *a.get_inx_mut_unwrap(p_middle.inx()) = 8;
    assert_eq!(a[p_middle], 8);

    let invalid = Q0::invalid();
    assert!(catch_unwind(AssertUnwindSafe(|| a[invalid])).is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| a[invalid] = 0)).is_err());
    let free = q0_inx(8);
    assert!(catch_unwind(AssertUnwindSafe(|| *a.get_inx_unwrap(free))).is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| *a.get_inx_mut_unwrap(free) = 0)).is_err());
}

#[test]
fn chain_arena_check_invariants_detects_corruption() {
    const ERR: Result<(), &str> = Err("interlink transitivity does not hold");
    // the base arena invariants are checked first
    let mut a = C8::new();
    a.set_generation(PtrGen::one());
    assert_eq!(ChainArena::_check_invariants(&a), Err("bad generation"));

    // a two link chain that the corruptions below are applied to
    let build = || {
        let mut a = C8::new();
        let p0 = a.insert(LinkInsertKind::Disconnected, 0);
        let p1 = a.insert(LinkInsertKind::ChainEnd(p0), 1);
        (a, p0, p1)
    };
    let set = |a: &mut C8, i: usize, prev_next: (Option<usize>, Option<usize>), t: u8| {
        let prev_next = (prev_next.0.map(q0_inx), prev_next.1.map(q0_inx));
        // Safety: this is exactly what the doc warns against, the point of the
        // test is that `_check_interlinks` notices
        unsafe {
            *a.backing_mut().get_mut(nz(i)).unwrap() =
                ArenaSlot::Allocated(PtrGen::two(), LinkNoGen::new(prev_next, t));
        }
    };

    // the `prev` of a link has to point at an allocated slot ...
    let mut a = C8::new();
    a.insert(LinkInsertKind::Disconnected, 0);
    set(&mut a, 1, (Some(7), None), 0);
    assert_eq!(ChainArena::_check_invariants(&a), ERR);
    // ... that has a `next` ...
    let (mut a, ..) = build();
    set(&mut a, 1, (None, None), 0);
    assert_eq!(ChainArena::_check_invariants(&a), ERR);
    // ... which points back at us. Note that the earlier links have to be made
    // consistent with wherever they point instead, or their own `next` check
    // would be the one to fire first.
    let mut a = C8::new();
    let p0 = a.insert(LinkInsertKind::Disconnected, 0);
    let p1 = a.insert(LinkInsertKind::ChainEnd(p0), 1);
    a.insert(LinkInsertKind::ChainEnd(p1), 2);
    set(&mut a, 1, (None, Some(3)), 0);
    set(&mut a, 2, (Some(1), Some(3)), 1);
    set(&mut a, 3, (Some(1), None), 2);
    assert_eq!(ChainArena::_check_invariants(&a), ERR);

    // the `next` of a link has to point at an allocated slot ...
    let (mut a, ..) = build();
    set(&mut a, 1, (None, Some(7)), 0);
    assert_eq!(ChainArena::_check_invariants(&a), ERR);
    // ... that has a `prev` ...
    let (mut a, ..) = build();
    set(&mut a, 2, (None, None), 1);
    assert_eq!(ChainArena::_check_invariants(&a), ERR);
    // ... which points back at us
    let (mut a, ..) = build();
    set(&mut a, 2, (Some(2), None), 1);
    assert_eq!(ChainArena::_check_invariants(&a), ERR);

    // a link whose interlinks point at itself has to be a single link cyclic
    // chain, which falls out of the checks above landing back on the link itself
    let mut a = C8::new();
    a.insert(LinkInsertKind::SingleLinkCyclic, 0);
    assert_eq!(ChainArena::_check_invariants(&a), Ok(()));
    let mut b = a.clone();
    set(&mut b, 1, (Some(1), None), 0);
    assert_eq!(ChainArena::_check_invariants(&b), ERR);
    let mut b = a.clone();
    set(&mut b, 1, (None, Some(1)), 0);
    assert_eq!(ChainArena::_check_invariants(&b), ERR);
}

#[test]
fn chain_alloc_error() {
    // the index type runs out before the backing does, which is an allocation
    // error rather than a max capacity one
    let mut a = ChainArena::<QSmall, (), StackBacking<512>>::new();
    for _ in 0..255 {
        a.insert(LinkInsertKind::Disconnected, ());
    }
    assert_eq!(a.capacity(), 255);
    assert_eq!(
        a.insert_within_capacity(LinkInsertKind::Disconnected, ()),
        Err(ChainInsertionError::NotWithinCapacity)
    );
    assert_eq!(
        a.insert_reallocating(LinkInsertKind::Disconnected, ()),
        Err(ChainInsertionError::AllocError)
    );
    assert_eq!(
        a.entry_insert_reallocating(LinkInsertKind::Disconnected)
            .map(|_| ()),
        Err(ChainInsertionError::AllocError)
    );
    // and the link requirement still takes priority
    assert_eq!(
        a.insert_reallocating(LinkInsertKind::ChainEnd(QSmall::invalid()), ()),
        Err(ChainInsertionError::FailedLinkRequirement)
    );
}

#[test]
fn chain_advancer_invalidation() {
    // the advancer is documented to not support invalidating `Ptr`s of the chain
    // during the loop, but it must still terminate and never produce an invalid
    // `Ptr`
    let (mut a, p_middle, _) = mixed_chains();

    // the link the advancer is about to move to is removed while going forwards
    let mut adv = a.advancer_chain(p_middle).unwrap();
    assert_eq!(adv.advance(&a), Some(p_middle));
    let next = a.get_link(p_middle).unwrap().next().unwrap();
    a.remove(next).allow().unwrap();
    assert_eq!(adv.advance(&a), None);
    assert_eq!(adv.advance(&a), None);

    // and the same while going backwards
    let (mut a, p_middle, _) = mixed_chains();
    let mut adv = a.advancer_chain(p_middle).unwrap();
    assert_eq!(adv.advance(&a), Some(p_middle));
    assert!(adv.advance(&a).is_some());
    let prev = a.get_link(p_middle).unwrap().prev().unwrap();
    a.remove(prev).allow().unwrap();
    assert_eq!(adv.advance(&a), None);

    // the initial link is removed before the advancer switches directions, which
    // is where it has to look the initial link up again
    let (mut a, p_middle, _) = mixed_chains();
    let mut adv = a.advancer_chain(p_middle).unwrap();
    assert_eq!(adv.advance(&a), Some(p_middle));
    a.remove(p_middle).allow().unwrap();
    // the end of the chain is still reached
    assert!(adv.advance(&a).is_some());
    // but the previous direction cannot be resumed
    assert_eq!(adv.advance(&a), None);

    // an empty advancer never produces anything
    let mut adv = <ChainPtrAdvancer<Q0> as Advancer<C8>>::empty();
    let a = C8::new();
    assert_eq!(adv.advance(&a), None);
}

#[cfg(feature = "alloc")]
#[test]
fn chain_set_max_capacity() {
    let mut a = ChainArena::<Q0, u8, LimitedHeapBacking>::new();
    // this backing starts out unable to hold anything
    assert_eq!(a.max_capacity(), Some(0));
    a.set_max_capacity(4).unwrap();
    a.insert(LinkInsertKind::Disconnected, 0);
    a.set_max_capacity(1).unwrap();
    assert_eq!(a.max_capacity(), Some(1));
    assert_eq!(a.capacity(), 1);
    // the one entry cannot be dropped by a reduction
    assert_eq!(a.set_max_capacity(0), Err(MaxCapacityReductionError));
    assert_eq!(
        a.insert_reallocating(LinkInsertKind::Disconnected, 1),
        Err(ChainInsertionError::BeyondMaxCapacity)
    );
    // the link requirement is checked first no matter how full it is
    assert_eq!(
        a.insert_reallocating(LinkInsertKind::ChainEnd(Q0::invalid()), 1),
        Err(ChainInsertionError::FailedLinkRequirement)
    );
}

#[test]
fn chain_overflow_transfer() {
    // more links than the destination index type can represent
    let mut source = ChainArena::<Q0, (), StackBacking<512>>::new();
    for _ in 0..256 {
        source.insert(LinkInsertKind::Disconnected, ());
    }
    let mut a = ChainArena::<QSmall, (), StackBacking<512>>::new();
    let mut recaster = DirectArena::<Q0, QSmall, StackBacking<512>>::new();
    assert_eq!(
        a.transfer_canonical_reallocating(
            PtrGen::two(),
            &mut source,
            |_, o, _| o.allow(),
            &mut recaster
        ),
        Err(ReallocationError::AllocError)
    );
    // neither side was touched
    assert_eq!(source.len(), 256);
    assert!(a.is_empty());

    // a source index that the recaster cannot represent
    let mut source = ChainArena::<QLargeInx, (), StackBacking<512>>::new();
    let p = source.insert(LinkInsertKind::Disconnected, ());
    let mut a = ChainArena::<Q0, (), StackBacking<512>>::new();
    let mut recaster = DirectArena::<QLargeInx, Q0, StackBacking<512>>::new();
    // this index is beyond what a `usize` recaster can be indexed by
    let far: QLargeInx = Ptr::_from_raw(NonZeroU128::new(1 << 100).unwrap(), PtrGen::two());
    assert!(!source.contains(far));
    assert_eq!(
        a.transfer_canonical_reallocating(
            PtrGen::two(),
            &mut source,
            |_, o, _| o.allow(),
            &mut recaster
        ),
        Ok(())
    );
    assert_eq!(a.len(), 1);
    assert!(source.is_empty());
    let _ = p;
}

#[cfg(feature = "alloc")]
#[test]
fn chain_transfer_grows_the_recaster() {
    // the recaster is indexed by the raw source indexes, so it has to be able to
    // reach the largest one and not just `source.len()`
    let mut source = ChainArena::<Q0, u8, HeapBacking>::new();
    let mut ptrs = vec![];
    for i in 0..8 {
        ptrs.push(source.insert(LinkInsertKind::Disconnected, i));
    }
    for p in &ptrs[..7] {
        source.remove(*p).allow().unwrap();
    }
    assert_eq!(source.len(), 1);

    let mut a = ChainArena::<Q0, u8, HeapBacking>::new();
    let mut recaster = DirectArena::<Q0, Q0, LimitedHeapBacking>::new();
    recaster.set_max_capacity(4).unwrap();
    // the last source index is 8, which the recaster cannot be grown to
    assert_eq!(
        a.transfer_canonical_reallocating(
            PtrGen::two(),
            &mut source,
            |_, o, _| o.allow(),
            &mut recaster
        ),
        Err(ReallocationError::BeyondMaxCapacity)
    );
    assert_eq!(source.len(), 1);
    assert!(a.is_empty());

    recaster.set_max_capacity(8).unwrap();
    assert_eq!(
        a.transfer_canonical_reallocating(
            PtrGen::two(),
            &mut source,
            |_, o, _| o.allow(),
            &mut recaster
        ),
        Ok(())
    );
    assert_eq!(a.len(), 1);
    assert!(recaster.capacity() >= 8);
}

/// A `ChainArenaTrait` implementor that misreports its state, for reaching the
/// paths that a correct implementor cannot. Only the few methods that the
/// functions under test actually use are implemented.
struct FaultyChainArena {
    /// what [len](ArenaTrait::len) reports
    len: usize,
    /// what [find_last_inx_ptr](ArenaTrait::find_last_inx_ptr) reports
    last: Option<QLargeInx>,
    /// what the advancers yield, in order
    ptrs: Vec<QLargeInx>,
}

impl FaultyChainArena {
    fn new(len: usize, last: u128, ptrs: &[u128]) -> Self {
        let ptr = |inx: u128| -> QLargeInx {
            Ptr::_from_raw(NonZeroU128::new(inx).unwrap(), PtrGen::two())
        };
        Self {
            len,
            last: Some(ptr(last)),
            ptrs: ptrs.iter().map(|inx| ptr(*inx)).collect(),
        }
    }
}

struct FaultyChainAdvancer(usize);

impl Advancer<FaultyChainArena> for FaultyChainAdvancer {
    type Item = QLargeInx;

    fn advance(&mut self, collection: &FaultyChainArena) -> Option<QLargeInx> {
        let res = collection.ptrs.get(self.0).copied();
        self.0 = self.0.saturating_add(1);
        res
    }

    fn empty() -> Self {
        Self(usize::MAX)
    }
}

impl ArenaTrait<QLargeInx, u8> for FaultyChainArena {
    type PtrAdvancer = FaultyChainAdvancer;

    fn len(&self) -> usize {
        self.len
    }

    fn find_first_inx_ptr(&self) -> Option<QLargeInx> {
        self.ptrs.first().copied()
    }

    fn find_last_inx_ptr(&self) -> Option<QLargeInx> {
        self.last
    }

    fn advancer_inx(&self, _inx: <QLargeInx as Ptr>::Inx, _rev: bool) -> Self::PtrAdvancer {
        FaultyChainAdvancer(0)
    }

    fn singular_generation(&self) -> Option<<QLargeInx as Ptr>::Gen> {
        Some(PtrGen::two())
    }

    // none of the rest is reached

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

    fn get_inx(&self, _p: <QLargeInx as Ptr>::Inx) -> Option<(<QLargeInx as Ptr>::Gen, &u8)> {
        unimplemented!()
    }

    fn get_disjoint_inx_mut<const N: usize>(
        &mut self,
        _indices: [<QLargeInx as Ptr>::Inx; N],
    ) -> Result<[(<QLargeInx as Ptr>::Gen, &mut u8); N], GetDisjointMutError> {
        unimplemented!()
    }

    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (QLargeInx, &'a mut u8)>
    where
        u8: 'a,
    {
        core::iter::empty()
    }

    fn drain(&mut self) -> impl Iterator<Item = InvalidationOption<(QLargeInx, u8)>> {
        core::iter::empty()
    }

    fn invalidate(&mut self, _p: QLargeInx) -> InvalidationResult<QLargeInx> {
        unimplemented!()
    }

    fn remove(&mut self, _p: QLargeInx) -> InvalidationResult<u8> {
        unimplemented!()
    }

    fn remove_inx(
        &mut self,
        _p: <QLargeInx as Ptr>::Inx,
    ) -> InvalidationResult<(<QLargeInx as Ptr>::Gen, u8)> {
        unimplemented!()
    }

    fn clear(&mut self) -> InvalidationOption<()> {
        unimplemented!()
    }

    fn compress_with<F: FnMut(QLargeInx, &mut u8, QLargeInx)>(
        &mut self,
        _reset_generation: bool,
        _map: F,
    ) -> InvalidationOption<()> {
        unimplemented!()
    }
}

impl CompactArenaTrait<QLargeInx, u8> for FaultyChainArena {}

impl ChainArenaTrait<QLargeInx, u8> for FaultyChainArena {
    type ChainPtrAdvancer = FaultyChainAdvancer;
    type InsertionEntry<'a>
        = ChainArenaInsertEntry<'a, QLargeInx, u8, StackBacking<4>>
    where
        Self: 'a;

    /// This is what makes the `get_link_no_gen` of the defaulted iterators fail
    /// on `Ptr`s that the advancers do produce
    fn get_inx_link_no_gen(
        &self,
        _p: <QLargeInx as Ptr>::Inx,
    ) -> Option<(<QLargeInx as Ptr>::Gen, &LinkNoGen<QLargeInx, u8>)> {
        None
    }

    fn advancer_chain(&self, _p_init: QLargeInx) -> Option<Self::ChainPtrAdvancer> {
        Some(FaultyChainAdvancer(0))
    }

    // none of the rest is reached

    fn entry_insert_within_capacity(
        &mut self,
        _kind: LinkInsertKind<QLargeInx>,
    ) -> Result<Self::InsertionEntry<'_>, ChainInsertionError> {
        unimplemented!()
    }

    fn connect(&mut self, _p_prev: QLargeInx, _p_next: QLargeInx) -> Option<()> {
        unimplemented!()
    }

    fn break_prev(&mut self, _p: QLargeInx) -> Option<()> {
        unimplemented!()
    }

    fn break_next(&mut self, _p: QLargeInx) -> Option<()> {
        unimplemented!()
    }

    fn exchange_next(&mut self, _p0: QLargeInx, _p1: QLargeInx) -> Option<()> {
        unimplemented!()
    }

    fn remove_inx_link_no_gen(
        &mut self,
        _p: <QLargeInx as Ptr>::Inx,
    ) -> InvalidationResult<(<QLargeInx as Ptr>::Gen, LinkNoGen<QLargeInx, u8>)> {
        unimplemented!()
    }

    fn drain_chain(
        &mut self,
        _p: QLargeInx,
    ) -> Option<impl Iterator<Item = InvalidationOption<(QLargeInx, LinkNoGen<QLargeInx, u8>)>>>
    {
        None::<core::iter::Empty<_>>
    }

    fn compress_canonical(&mut self, _reset_generation: bool) -> InvalidationOption<()> {
        unimplemented!()
    }
}

#[test]
fn faulty_chain_arena_last_inx_too_big() {
    // REF(careful_index_checking) an index that no arena could have inserted at
    // cannot be used to size the recaster, and it is an allocation error rather
    // than a panic because `reallocate_min_capacity` is not reached to report it
    let mut source = FaultyChainArena::new(1, 1 << 100, &[]);
    let mut a = ChainArena::<Q0, u8, StackBacking<4>>::new();
    let mut recaster = DirectArena::<QLargeInx, Q0, StackBacking<4>>::new();
    assert_eq!(
        a.transfer_canonical_reallocating(
            PtrGen::two(),
            &mut source,
            |_, o, _| o.allow(),
            &mut recaster
        ),
        Err(ReallocationError::AllocError)
    );
    // nothing was modified
    assert!(a.is_empty());
    assert!(recaster.is_empty());
}

#[test]
fn faulty_chain_arena_unknown_ptr() {
    // the defaulted iterators stop instead of panicking when the advancer
    // produces a `Ptr` that the link lookup does not recognize
    let source = FaultyChainArena::new(1, 1, &[1]);
    assert_eq!(source.iter_link_no_gen().count(), 0);
    assert_eq!(
        source
            .iter_chain(Ptr::_from_raw(NonZeroU128::new(1).unwrap(), PtrGen::two()))
            .unwrap()
            .count(),
        0
    );
}
