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
    LinkNoGen, OrdEntryKind, OrdInsertKind, OrdPair, SimpleOrdArena, StackBacking,
    chain_iterators::ChainPtrAdvancer,
    errors::{AllocError, ChainInsertionError, OrdInsertionError, ReallocationError},
    ptr_struct,
    traits::{
        Advancer, ArenaCloneFromWith, ArenaInsertTrait, ArenaTrait, ChainArenaTrait,
        CompactArenaTrait, Ptr, Recast,
    },
    utils::{
        ArenaSlot, ChainArenaInsertEntry, SimpleOrdArenaNode,
        traits::{ArenaBacking, NonZeroInxGenericStack, PtrGen, PtrInx, SimpleOrdItem},
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

// ---------------------------------------------------------------------------
// `SimpleOrdArena`
// ---------------------------------------------------------------------------

/// A key of a small domain so that equal keys are easy to arrange
type O8 = SimpleOrdArena<Q0, OrdPair<u8, u8>, StackBacking<8>>;

type ONode = SimpleOrdArenaNode<Q0, OrdPair<u8, u8>>;

/// Builds an ordered arena from `(key, value)` pairs in insertion order
fn ord_of(pairs: &[(u8, u8)]) -> (O8, Vec<Q0>) {
    let mut a = O8::new();
    let mut ptrs = vec![];
    for (k, v) in pairs {
        ptrs.push(a.insert(OrdPair::new(*k, *v)).0);
    }
    (a, ptrs)
}

/// The `(key, value)` pairs in key order
fn ord_pairs<P: Ptr, B: ArenaBacking>(a: &SimpleOrdArena<P, OrdPair<u8, u8>, B>) -> Vec<(u8, u8)> {
    a.iter_ordered().map(|(_, t)| (*t.k(), *t.v())).collect()
}

/// Overwrites the internal node at the raw index `i`
fn set_node(a: &mut O8, i: usize, f: impl FnOnce(&mut ONode)) {
    // Safety: this is exactly what the doc warns against, the point is that
    // `_check_invariants` notices
    unsafe {
        let slot = a.backing_mut().get_mut(nz(i)).unwrap();
        let ArenaSlot::Allocated(_, link) = slot else {
            panic!()
        };
        f(&mut link.t);
    }
}

/// Overwrites the interlinks of the internal node at the raw index `i`
fn set_links(a: &mut O8, i: usize, prev_next: (Option<usize>, Option<usize>)) {
    let prev_next = (prev_next.0.map(q0_inx), prev_next.1.map(q0_inx));
    // Safety: as above
    unsafe {
        let slot = a.backing_mut().get_mut(nz(i)).unwrap();
        let ArenaSlot::Allocated(_, link) = slot else {
            panic!()
        };
        *link = LinkNoGen::new(
            prev_next,
            core::mem::replace(&mut link.t, ONode {
                t: OrdPair::new(0, 0),
                p_back: None,
                p_tree0: None,
                p_tree1: None,
                rank: 0,
            }),
        );
    }
}

#[test]
fn ord_check_invariants_detects_corruption() {
    // the chain arena invariants are checked first
    let mut a = O8::new();
    let _ = a.insert(OrdPair::new(0, 0));
    a.set_generation(PtrGen::one());
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Err("bad generation"));

    // an empty arena has invalid `root`, `first`, and `last`, which is allowed
    let a = O8::new();
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Ok(()));

    // Three entries at the indexes 1, 2, 3 with the keys 1, 0, 2, which puts the
    // root at index 1 with the leaves 2 and 3 as its subtree 0 and 1, and the
    // chain in the order 2, 1, 3. Note that most of the corruptions below have to
    // be at an index that the arena advancer reaches before it reaches an index
    // that a different check would fire on.
    let build = || ord_of(&[(1, 0), (0, 0), (2, 0)]).0;
    let a = build();
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Ok(()));
    let node = |a: &O8, i: usize| {
        let n = &a.get_inx_node(q0_inx(i)).unwrap().1.t;
        (n.p_back, n.p_tree0, n.p_tree1, n.rank)
    };
    assert_eq!(node(&a, 1), (None, Some(q0_inx(2)), Some(q0_inx(3)), 2));
    assert_eq!(node(&a, 2), (Some(q0_inx(1)), None, None, 1));
    assert_eq!(node(&a, 3), (Some(q0_inx(1)), None, None, 1));
    assert_eq!(a.first().unwrap().inx(), q0_inx(2));
    assert_eq!(a.last().unwrap().inx(), q0_inx(3));

    // the same three keys inserted in ascending order instead, which rotates the
    // root onto index 2 so that a leaf is reached first
    let build_rotated = || ord_of(&[(0, 0), (1, 0), (2, 0)]).0;
    let a = build_rotated();
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Ok(()));
    assert_eq!(node(&a, 2), (None, Some(q0_inx(1)), Some(q0_inx(3)), 2));

    // the root cannot have a back pointer
    let mut a = build();
    set_node(&mut a, 1, |n| n.p_back = Some(q0_inx(2)));
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("root node has a back pointer")
    );

    // `first` has to be the start of the chain. Note that the interlinks have to
    // stay transitive or else the chain arena check would be the one to fire, so
    // the chain is closed into a cycle instead.
    let mut a = build();
    set_links(&mut a, 2, (Some(3), Some(1)));
    set_links(&mut a, 3, (Some(1), Some(2)));
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("this.first is broken")
    );

    // the keys have to be in order along the chain, which
    // `insert_inx_manual_unwrap` does not enforce
    let (mut a, ptrs) = ord_of(&[(1, 0), (0, 0)]);
    assert!(
        a.insert_inx_manual_unwrap(ptrs[1].inx(), Ordering::Less, OrdPair::new(9, 0))
            .is_none()
    );
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("incorrect ordering")
    );

    // `last` has to be the end of the chain that `first` starts
    let mut a = build();
    set_links(&mut a, 1, (Some(2), None));
    set_links(&mut a, 3, (None, None));
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("this.last is not correct")
    );

    // every entry has to be on the one chain. The second chain is put in the
    // middle of the key order so that `first` and `last` stay correct.
    let (mut a, _) = ord_of(&[(0, 0), (1, 0), (2, 0), (3, 0)]);
    set_links(&mut a, 1, (None, Some(4)));
    set_links(&mut a, 4, (Some(1), None));
    set_links(&mut a, 2, (None, Some(3)));
    set_links(&mut a, 3, (Some(2), None));
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("multiple chains")
    );

    // a back pointer has to point at an allocated slot that claims us as a child
    let mut a = build_rotated();
    set_node(&mut a, 1, |n| n.p_back = Some(q0_inx(7)));
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Err("broken tree"));
    let mut a = build_rotated();
    set_node(&mut a, 1, |n| n.p_back = Some(q0_inx(3)));
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Err("broken tree"));
    // and a child pointer has to point at a node that points back
    let mut a = build();
    set_node(&mut a, 2, |n| n.p_back = Some(q0_inx(3)));
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Err("broken tree"));
    let mut a = build_rotated();
    set_node(&mut a, 3, |n| n.p_back = Some(q0_inx(1)));
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Err("broken tree"));
    // and only the root can have no back pointer
    let mut a = build_rotated();
    set_node(&mut a, 1, |n| n.p_back = None);
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("more than one root node")
    );

    // the two children of a node have to be different
    let mut a = build();
    set_node(&mut a, 1, |n| n.p_tree1 = Some(q0_inx(2)));
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("`p_tree0` and `p_tree1` are the same")
    );
    // a child pointer has to point at an allocated slot ...
    let mut a = build();
    set_node(&mut a, 1, |n| n.p_tree0 = Some(q0_inx(7)));
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Err("broken tree"));
    let mut a = build();
    set_node(&mut a, 1, |n| n.p_tree1 = Some(q0_inx(7)));
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Err("broken tree"));
    // ... and is not the node itself. This has to be a nonroot node, or else
    // the root back pointer check would be the one to fire.
    let mut a = build_rotated();
    set_node(&mut a, 1, |n| {
        n.p_tree0 = Some(q0_inx(1));
        n.p_back = Some(q0_inx(1));
    });
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Err("cycle"));
    let mut a = build_rotated();
    set_node(&mut a, 1, |n| {
        n.p_tree1 = Some(q0_inx(1));
        n.p_back = Some(q0_inx(1));
    });
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Err("cycle"));

    // ranks have to strictly decrease from parent to child ...
    let mut a = build();
    set_node(&mut a, 2, |n| n.rank = 2);
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("rank difference is zero or negative")
    );
    let mut a = build();
    set_node(&mut a, 3, |n| n.rank = 2);
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("rank difference is zero or negative")
    );
    // ... by at most 2 ...
    let mut a = build();
    set_node(&mut a, 1, |n| n.rank = 4);
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("rank difference is greater than 2")
    );
    // ... and a leaf can only be rank 1
    let mut a = build_rotated();
    set_node(&mut a, 1, |n| n.rank = 2);
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("leaf node is not rank 1")
    );

    // the in-order traversal of the tree has to be the chain order, which none of
    // the checks above can see
    let mut a = build();
    set_node(&mut a, 1, |n| {
        n.p_tree0 = Some(q0_inx(3));
        n.p_tree1 = Some(q0_inx(2));
    });
    assert_eq!(
        SimpleOrdArena::_check_invariants(&a),
        Err("in-order tree traversal does not match the chain order")
    );
}

#[test]
fn ord_pair_and_item() {
    let mut pair = OrdPair::new(7u8, 8u16);
    assert_eq!(*pair.k(), 7);
    assert_eq!(*pair.v(), 8);
    *pair.v_mut() = 9;
    assert_eq!(pair.k_v(), (&7, &9));
    let (k, v) = pair.k_v_mut();
    assert_eq!(*k, 7);
    *v = 10;
    assert_eq!(format!("{pair:?}"), "(7, 10)");
    let pair2 = pair;
    assert!(pair == pair2);
    assert_eq!(hash_of(&pair), hash_of(&pair2));
    assert_eq!(pair.cmp(&OrdPair::new(8u8, 0u16)), Ordering::Less);
    assert_eq!(
        pair.partial_cmp(&OrdPair::new(7u8, 11u16)),
        Some(Ordering::Less)
    );
    assert_eq!(pair.into_k_v(), (7, 10));

    // only the value is recast
    let (mut a, ptrs) = ord_of(&[(0, 0)]);
    let mut pair = OrdPair::new(0u8, ptrs[0]);
    let mut recaster = DirectArena::<Q0, Q0, StackBacking<8>>::new();
    recaster.clone_from_with(&a, |p, _| p).unwrap();
    pair.recast(&recaster).unwrap();
    assert_eq!(*pair.v(), ptrs[0]);
    a.clear().allow();
}

/// A user type that projects part of itself as the key, which `OrdPair` cannot
/// do. Note that only `SimpleOrdItem` is required and nothing else.
#[derive(Debug)]
struct Projected {
    name: [u8; 2],
    count: usize,
}

impl SimpleOrdItem for Projected {
    type Key<'a>
        = &'a [u8; 2]
    where
        Self: 'a;

    fn key(&self) -> Self::Key<'_> {
        &self.name
    }

    fn shorten_key<'long: 'short, 'short>(k: Self::Key<'long>) -> Self::Key<'short>
    where
        Self: 'long,
    {
        k
    }
}

#[test]
fn ord_custom_simple_ord_item() {
    let mut a = SimpleOrdArena::<Q0, Projected, StackBacking<8>>::new();
    for name in [*b"cc", *b"aa", *b"bb"] {
        let _ = a.insert(Projected { name, count: 0 });
    }
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Ok(()));
    let names: Vec<[u8; 2]> = a.iter_ordered().map(|(_, t)| t.name).collect();
    assert_eq!(names, vec![*b"aa", *b"bb", *b"cc"]);
    let p = a.find_key(b"bb").unwrap();
    a.get_mut(p).unwrap().count = 5;
    assert_eq!(a[p].count, 5);
    assert_eq!(a.find_key(b"zz"), None);
    // the projected key is what the replacement compares against
    let old = a.insert(Projected {
        name: *b"bb",
        count: 9,
    });
    assert_eq!(old.1.unwrap().count, 5);
    assert_eq!(a.len(), 3);
}

#[test]
fn ord_canonical_comparisons() {
    let (a, _) = ord_of(&[(0, 0), (1, 1), (2, 2)]);
    // a different `Ptr` type and a different backing, and built in a different
    // insertion order so that the internal layouts differ
    let mut b = SimpleOrdArena::<Q1, OrdPair<u8, u8>, StackBacking<16>>::new();
    for (k, v) in [(2, 2), (0, 0), (1, 1)] {
        let _ = b.insert(OrdPair::new(k, v));
    }
    assert!(a.canonical_eq(&b));
    assert_eq!(a.canonical_partial_cmp(&b), Some(Ordering::Equal));
    assert_eq!(a.canonical_cmp(&b), Ordering::Equal);

    // a difference in the prefix returns early
    let mut c = b.clone();
    *c.get_mut(c.find_key(&1).unwrap()).unwrap().v_mut() = 7;
    assert!(!a.canonical_eq(&c));
    assert_eq!(a.canonical_partial_cmp(&c), Some(Ordering::Less));
    assert_eq!(a.canonical_cmp(&c), Ordering::Less);
    assert_eq!(c.canonical_cmp(&a), Ordering::Greater);
    assert_eq!(c.canonical_partial_cmp(&a), Some(Ordering::Greater));

    // and otherwise the longer one is greater
    let mut d = b.clone();
    let _ = d.insert(OrdPair::new(3, 3));
    assert!(!a.canonical_eq(&d));
    assert!(!d.canonical_eq(&a));
    assert_eq!(a.canonical_cmp(&d), Ordering::Less);
    assert_eq!(d.canonical_cmp(&a), Ordering::Greater);
    assert_eq!(a.canonical_partial_cmp(&d), Some(Ordering::Less));
    assert_eq!(d.canonical_partial_cmp(&a), Some(Ordering::Greater));

    // this is sensitive to nonhereditary ordering, and it goes by the key order
    // and not the internal layout. A nonhereditary insertion goes before the
    // equal key it finds, and a manual `Greater` one goes after, so these two
    // reach the same ordering from opposite directions.
    let mut e = O8::new();
    let _ = e.insert(OrdPair::new(0, 0));
    e.entry_insert(OrdInsertKind::Nonhereditary(&0))
        .insert(OrdPair::new(0, 1));
    let mut f = O8::new();
    let p = f.insert(OrdPair::new(0, 1)).0;
    f.entry_insert(OrdInsertKind::Manual {
        p_target: p.inx(),
        direction: Ordering::Greater,
    })
    .insert(OrdPair::new(0, 0));
    assert_eq!(ord_pairs(&e), vec![(0, 1), (0, 0)]);
    assert_eq!(ord_pairs(&f), vec![(0, 1), (0, 0)]);
    assert!(e.canonical_eq(&f));
    // while the reverse ordering of the same keys is not equal
    let mut g = O8::new();
    let _ = g.insert(OrdPair::new(0, 1));
    g.entry_insert(OrdInsertKind::Nonhereditary(&0))
        .insert(OrdPair::new(0, 0));
    assert_eq!(ord_pairs(&g), vec![(0, 0), (0, 1)]);
    assert!(!e.canonical_eq(&g));
}

#[test]
fn ord_clone_and_default() {
    let (a, ptrs) = ord_of(&[(2, 2), (0, 0), (1, 1)]);
    // the `Ptr`s, ordering, and tree are all preserved
    let b = a.clone();
    assert_eq!(SimpleOrdArena::_check_invariants(&b), Ok(()));
    assert_eq!(ord_pairs(&b), vec![(0, 0), (1, 1), (2, 2)]);
    for p in &ptrs {
        assert_eq!(a.get(*p).unwrap().v(), b.get(*p).unwrap().v());
    }
    assert_eq!(b.generation(), a.generation());

    // `clone_from` reuses the capacity
    let mut c = O8::new();
    let _ = c.insert(OrdPair::new(9, 9));
    c.clone_from(&a);
    assert_eq!(SimpleOrdArena::_check_invariants(&c), Ok(()));
    assert_eq!(ord_pairs(&c), vec![(0, 0), (1, 1), (2, 2)]);
    assert_eq!(c.first(), a.first());
    assert_eq!(c.last(), a.last());

    // the internal backing is directly reachable for advanced use
    assert_eq!(a.backing().len(), 3);
    assert_eq!(a.backing().capacity(), 8);

    let d: O8 = Default::default();
    assert!(d.is_empty());
    assert_eq!(SimpleOrdArena::_check_invariants(&d), Ok(()));
    // the `Debug` impl is in key order, unlike the unordered arena ones
    assert_eq!(format!("{d:?}"), "{}");
    assert_eq!(
        format!("{a:?}"),
        "{Q0[2](2): (0, 0), Q0[3](2): (1, 1), Q0[1](2): (2, 2)}"
    );
}

#[test]
fn ord_into_iterators() {
    let (a, ptrs) = ord_of(&[(2, 2), (0, 0), (1, 1)]);
    // by reference
    let by_ref: Vec<(Q0, u8)> = (&a).into_iter().map(|(p, t)| (p, *t.k())).collect();
    assert_eq!(by_ref, vec![(ptrs[1], 0), (ptrs[2], 1), (ptrs[0], 2)]);
    // by value, which is a capacity drain in key order
    let owned: Vec<(Q0, (u8, u8))> = a.into_iter().map(|(p, t)| (p, t.into_k_v())).collect();
    assert_eq!(owned, vec![
        (ptrs[1], (0, 0)),
        (ptrs[2], (1, 1)),
        (ptrs[0], (2, 2))
    ]);

    // partially consuming the owned drain drops the rest
    let (a, _) = ord_of(&[(2, 2), (0, 0), (1, 1)]);
    let mut iter = a.into_iter();
    assert_eq!(*iter.next().unwrap().1.k(), 0);
    drop(iter);

    // and `drain_ordered` clears whatever is left on drop
    let (mut a, _) = ord_of(&[(2, 2), (0, 0), (1, 1)]);
    {
        let mut drain = a.drain_ordered();
        assert_eq!(*drain.next().unwrap().1.k(), 0);
    }
    assert!(a.is_empty());
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Ok(()));

    // an empty arena
    let a = O8::new();
    assert!(a.iter_ordered().next().is_none());
    let mut a = O8::new();
    assert!(a.drain_ordered().next().is_none());
    let a = O8::new();
    assert!(a.into_iter().next().is_none());
}

#[test]
fn ord_advancer_ordered_invalidation() {
    let (mut a, ptrs) = ord_of(&[(0, 0), (1, 1), (2, 2)]);
    assert!(a.advancer_ordered(Q0::invalid(), false).is_none());
    // the advancer holds an index, so removing the entry it is pointing at ends
    // the advancing instead of continuing
    let mut adv = a.advancer_ordered(ptrs[0], false).unwrap();
    assert_eq!(adv.advance(&a), Some(ptrs[0]));
    a.remove(ptrs[1]).allow().unwrap();
    assert!(adv.advance(&a).is_none());
    // and an empty advancer never advances
    let mut adv = <triple_arena::ord_iterators::OrderedPtrAdvancer<Q0> as Advancer<O8>>::empty();
    assert!(adv.advance(&a).is_none());
    let _ = ptrs[2];
}

#[test]
fn ord_recast_values() {
    let mut a = SimpleOrdArena::<Q0, OrdPair<u8, Option<Q0>>, StackBacking<8>>::new();
    let p0 = a.insert(OrdPair::new(0, None)).0;
    let p1 = a.insert(OrdPair::new(1, Some(p0))).0;
    let mut recaster = DirectArena::<Q0, Q0, StackBacking<8>>::new();
    recaster.clone_from_with(&a, |_, _| Q0::invalid()).unwrap();
    *recaster.get_mut(p0).unwrap() = p1;
    *recaster.get_mut(p1).unwrap() = p0;
    a.recast(&recaster).unwrap();
    assert_eq!(*a.get(p1).unwrap().v(), Some(p1));
    // an unknown `Ptr` is reported
    let mut b = SimpleOrdArena::<Q0, OrdPair<u8, Option<Q0>>, StackBacking<8>>::new();
    let _ = b.insert(OrdPair::new(0, Some(Q0::invalid())));
    assert_eq!(b.recast(&recaster), Err(Q0::invalid()));
}

#[test]
fn ord_empty_and_insert_kind_failures() {
    let mut a = O8::new();
    assert!(a.first().is_none());
    assert!(a.last().is_none());
    assert!(a.find_key(&0).is_none());
    assert!(a.find_similar_key(&0).is_none());
    assert!(a.find_key_linear(Q0::invalid(), 4, &0).is_none());
    assert!(a.find_similar_key_linear(q0_inx(1), 4, &0).is_none());
    assert!(a.find_with(|_, _| Ordering::Equal).is_none());
    assert!(a.find_similar_with(|_, _| Ordering::Equal).is_none());
    assert!(a.get_inx_link_no_gen(q0_inx(1)).is_none());
    assert!(a.get_inx_node(q0_inx(1)).is_none());

    // `Manual` always fails on an empty arena, even with `Ordering::Equal`
    for direction in [Ordering::Less, Ordering::Equal, Ordering::Greater] {
        assert_eq!(
            a.entry_insert_within_capacity(OrdInsertKind::Manual {
                p_target: q0_inx(1),
                direction,
            })
            .map(|_| ()),
            Err(OrdInsertionError::FailedOrdRequirement)
        );
    }
    // `Empty` succeeds only on an empty arena
    let entry = a.entry_insert(OrdInsertKind::Empty);
    assert!(matches!(entry.ptr(), OrdEntryKind::New(_)));
    assert!(entry.insert(OrdPair::new(5, 5)).is_none());
    assert_eq!(
        a.entry_insert_within_capacity(OrdInsertKind::Empty)
            .map(|_| ()),
        Err(OrdInsertionError::FailedOrdRequirement)
    );
    assert_eq!(
        a.entry_insert_reallocating(OrdInsertKind::Empty)
            .map(|_| ()),
        Err(OrdInsertionError::FailedOrdRequirement)
    );
    // an invalid index still fails
    assert_eq!(
        a.entry_insert_reallocating(OrdInsertKind::Manual {
            p_target: q0_inx(8),
            direction: Ordering::Less,
        })
        .map(|_| ()),
        Err(OrdInsertionError::FailedOrdRequirement)
    );

    // a replacement needs no capacity, even when the arena is completely full
    let mut a = O8::new();
    for k in 0..8u8 {
        let _ = a.insert(OrdPair::new(k, k));
    }
    assert_eq!(a.len(), a.capacity());
    assert_eq!(
        a.insert_within_capacity(OrdPair::new(8, 8)).map(|_| ()),
        Err(OrdInsertionError::NotWithinCapacity)
    );
    let (p, old) = a.insert_within_capacity(OrdPair::new(3, 30)).unwrap();
    assert_eq!(*old.unwrap().v(), 3);
    assert_eq!(*a.get(p).unwrap().v(), 30);
    // and the elaborated `Ptr` says which entry is being replaced
    let entry = a
        .entry_insert_within_capacity(OrdInsertKind::Manual {
            p_target: p.inx(),
            direction: Ordering::Equal,
        })
        .unwrap();
    assert_eq!(entry.ptr(), OrdEntryKind::Replacing(p));
    assert_eq!(*entry.insert(OrdPair::new(3, 31)).unwrap().v(), 30);
    assert_eq!(a.len(), 8);
}

#[test]
fn ord_find_linear_edges() {
    let (a, ptrs) = ord_of(&[(0, 0), (2, 2), (4, 4), (6, 6), (8, 8)]);
    // zero comparisons falls straight through to the normal search
    assert_eq!(a.find_key_linear(ptrs[0], 0, &8), Some(ptrs[4]));
    assert_eq!(
        a.find_similar_key_linear(ptrs[0].inx(), 0, &8),
        Some((ptrs[4], Ordering::Equal))
    );
    // an invalid start also falls through
    assert_eq!(a.find_key_linear(Q0::invalid(), 4, &4), Some(ptrs[2]));
    assert_eq!(
        a.find_similar_key_linear(q0_inx(8), 4, &4),
        Some((ptrs[2], Ordering::Equal))
    );
    // walking backwards and forwards to a hit
    assert_eq!(a.find_key_linear(ptrs[4], 4, &2), Some(ptrs[1]));
    assert_eq!(a.find_key_linear(ptrs[0], 4, &6), Some(ptrs[3]));
    // reversing direction means the key is bracketed and not present
    assert_eq!(a.find_key_linear(ptrs[0], 4, &5), None);
    assert_eq!(
        a.find_similar_key_linear(ptrs[0].inx(), 4, &5),
        Some((ptrs[3], Ordering::Less))
    );
    assert_eq!(
        a.find_similar_key_linear(ptrs[4].inx(), 4, &5),
        Some((ptrs[2], Ordering::Greater))
    );
    // running off the ends
    assert_eq!(a.find_key_linear(ptrs[0], 4, &200), None);
    assert_eq!(
        a.find_similar_key_linear(ptrs[4].inx(), 4, &200),
        Some((ptrs[4], Ordering::Greater))
    );
    assert_eq!(
        a.find_similar_key_linear(ptrs[0].inx(), 4, &0u8.wrapping_sub(0)),
        Some((ptrs[0], Ordering::Equal))
    );
    let (b, ptrs) = ord_of(&[(1, 0)]);
    assert_eq!(
        b.find_similar_key_linear(ptrs[0].inx(), 4, &0),
        Some((ptrs[0], Ordering::Less))
    );
}

#[test]
fn ord_indexing_and_panics() {
    let (mut a, ptrs) = ord_of(&[(0, 0)]);
    assert_eq!(*a[ptrs[0]].k(), 0);
    assert_eq!(*a[&ptrs[0]].k(), 0);
    *a[ptrs[0]].v_mut() = 7;
    assert_eq!(*a[ptrs[0]].v(), 7);

    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = &a[Q0::invalid()];
    }));
    assert!(res.is_err());
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = &mut a[Q0::invalid()];
    }));
    assert!(res.is_err());

    // `insert_inx_manual_unwrap` panics on an invalid index
    let mut a = O8::new();
    let res = catch_unwind(AssertUnwindSafe(|| {
        a.insert_inx_manual_unwrap(q0_inx(1), Ordering::Less, OrdPair::new(0, 0))
    }));
    assert!(res.is_err());

    // and on a full fixed capacity arena, which is the only other documented
    // panic
    let mut a = O8::new();
    for k in 0..8u8 {
        let _ = a.insert(OrdPair::new(k, k));
    }
    let p = a.first().unwrap();
    let res = catch_unwind(AssertUnwindSafe(|| {
        a.insert_inx_manual_unwrap(p.inx(), Ordering::Less, OrdPair::new(0, 0))
    }));
    assert!(res.is_err());
    let p = a.last().unwrap();
    let res = catch_unwind(AssertUnwindSafe(|| {
        a.insert_inx_manual_unwrap(p.inx(), Ordering::Greater, OrdPair::new(9, 9))
    }));
    assert!(res.is_err());
    // `insert` and `entry_insert` panic for the same reason
    let res = catch_unwind(AssertUnwindSafe(|| a.insert(OrdPair::new(9, 9))));
    assert!(res.is_err());
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = a.entry_insert(OrdInsertKind::Nonhereditary(&0)).ptr();
    }));
    assert!(res.is_err());
}

#[test]
fn ord_alloc_error() {
    // the index type runs out before the backing does, which is an allocation
    // error rather than a max capacity one
    let mut a = SimpleOrdArena::<QSmall, OrdPair<usize, ()>, StackBacking<512>>::new();
    for k in 0..255 {
        let _ = a.insert(OrdPair::new(k, ()));
    }
    assert_eq!(a.capacity(), 255);
    assert_eq!(
        a.insert_within_capacity(OrdPair::new(255, ())).map(|_| ()),
        Err(OrdInsertionError::NotWithinCapacity)
    );
    assert_eq!(
        a.insert_reallocating(OrdPair::new(255, ())).map(|_| ()),
        Err(OrdInsertionError::AllocError)
    );
    assert_eq!(
        a.entry_insert_reallocating(OrdInsertKind::Normal(&255))
            .map(|_| ()),
        Err(OrdInsertionError::AllocError)
    );
    // and the ordering requirement still takes priority
    assert_eq!(
        a.entry_insert_reallocating(OrdInsertKind::Empty)
            .map(|_| ()),
        Err(OrdInsertionError::FailedOrdRequirement)
    );
    // while a replacement still succeeds
    assert!(
        a.insert_reallocating(OrdPair::new(0, ()))
            .unwrap()
            .1
            .is_some()
    );
}

#[test]
fn ord_debug_helpers() {
    // these are development debugging helpers, they just have to not panic
    let a = O8::new();
    assert_eq!(SimpleOrdArena::_debug(&a), "empty\n");
    let (a, _) = ord_of(&[(2, 2), (0, 0), (1, 1)]);
    let s = SimpleOrdArena::_debug(&a);
    assert_eq!(s.lines().count(), 6);
    assert!(s.starts_with("root: "));
    let debug_arena = a._debug_arena();
    assert_eq!(debug_arena.len(), 3);
    // the rank and the tree `Ptr`s of the root
    let root = debug_arena.get(a.find_key(&1).unwrap()).unwrap();
    assert_eq!(root.0, 2);
    assert_eq!(root.2, a.first());
    assert_eq!(root.3, None);
    assert_eq!(root.4, a.last());
}

#[test]
fn ord_compress_with_panicking_map() {
    // REF(ord_rebalance_guard) an unwinding `map` still leaves a valid arena
    let (mut a, ptrs) = ord_of(&[(0, 0), (1, 1), (2, 2), (3, 3)]);
    a.remove(ptrs[1]).allow().unwrap();
    let mut n = 0usize;
    let res = catch_unwind(AssertUnwindSafe(|| {
        a.compress_with(false, |_, _, _| {
            n += 1;
            if n == 2 {
                panic!("test panic")
            }
        })
        .allow()
    }));
    assert!(res.is_err());
    assert_eq!(a.len(), 3);
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Ok(()));
    assert_eq!(ord_pairs(&a), vec![(0, 0), (2, 2), (3, 3)]);
    // and the tree is still usable
    let p = a.find_key(&2).unwrap();
    assert_eq!(*a.get(p).unwrap().v(), 2);
}

#[test]
fn ord_transfer_canonical() {
    let (mut a, _) = ord_of(&[(3, 3), (0, 0), (1, 1), (2, 2)]);
    let mut b = SimpleOrdArena::<Q0, OrdPair<u8, u8>, StackBacking<16>>::new();
    let mut recaster = DirectArena::<Q0, Q0, StackBacking<16>>::new();
    let new_gen = PtrGen::two();
    b.transfer_canonical_reallocating(new_gen, &mut a, |_, o, _| o.allow(), &mut recaster)
        .unwrap();
    assert!(a.is_empty());
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Ok(()));
    assert_eq!(SimpleOrdArena::_check_invariants(&b), Ok(()));
    assert_eq!(ord_pairs(&b), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);
    // the indexes are `1..=len` in key order
    let raw: Vec<(usize, (u8, u8))> = b
        .iter_ordered()
        .map(|(p, t)| {
            (
                PtrInx::try_into_usize(p.inx()).unwrap().get(),
                (*t.k(), *t.v()),
            )
        })
        .collect();
    assert_eq!(raw, vec![
        (1, (0, 0)),
        (2, (1, 1)),
        (3, (2, 2)),
        (4, (3, 3))
    ]);
    assert_eq!(b.generation(), new_gen);

    // an empty source clears the destination and sets the generation
    let mut empty = O8::new();
    let new_gen = PtrGen::generational_inc(new_gen).0;
    b.transfer_canonical_reallocating(new_gen, &mut empty, |_, o, _| o.allow(), &mut recaster)
        .unwrap();
    assert!(b.is_empty());
    assert_eq!(b.generation(), new_gen);
    assert_eq!(SimpleOrdArena::_check_invariants(&b), Ok(()));

    // a panicking `map` leaves both sides valid, REF(ord_rebalance_guard)
    let (mut a, _) = ord_of(&[(3, 3), (0, 0), (1, 1), (2, 2)]);
    let mut n = 0usize;
    let res = catch_unwind(AssertUnwindSafe(|| {
        b.transfer_canonical_reallocating(
            new_gen,
            &mut a,
            |_, o, _| {
                n += 1;
                if n == 3 {
                    panic!("test panic")
                }
                o.allow()
            },
            &mut recaster,
        )
        .unwrap()
    }));
    assert!(res.is_err());
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Ok(()));
    assert_eq!(SimpleOrdArena::_check_invariants(&b), Ok(()));
    // the third entry was lost to the panic, and the rest of the chain that was
    // being drained was dropped, so only what already arrived is left
    assert_eq!(ord_pairs(&b), vec![(0, 0), (1, 1)]);
    assert!(a.is_empty());
    assert_eq!(b.find_key(&1), b.last());
}

#[test]
fn ord_transfer_error_leaves_the_tree_alone() {
    // all the fallible points happen before anything is modified, so a failed
    // transfer must not run the rebalance over the preexisting tree
    let (mut a, _) = ord_of(&[(0, 0), (1, 1), (2, 2)]);
    let mut b = SimpleOrdArena::<Q0, OrdPair<u8, u8>, StackBacking<2>>::new();
    let _ = b.insert(OrdPair::new(9, 9));
    let mut recaster = DirectArena::<Q0, Q0, StackBacking<16>>::new();
    assert_eq!(
        b.transfer_canonical_reallocating(
            PtrGen::two(),
            &mut a,
            |_, o, _| o.allow(),
            &mut recaster
        ),
        Err(ReallocationError::BeyondMaxCapacity)
    );
    assert_eq!(SimpleOrdArena::_check_invariants(&a), Ok(()));
    assert_eq!(SimpleOrdArena::_check_invariants(&b), Ok(()));
    assert_eq!(ord_pairs(&a), vec![(0, 0), (1, 1), (2, 2)]);
    assert_eq!(ord_pairs(&b), vec![(9, 9)]);
}

#[test]
fn ord_clone_to_other_arenas() {
    let (a, ptrs) = ord_of(&[(2, 2), (0, 0), (1, 1)]);
    // the ordering becomes a single chain
    let mut chain = ChainArena::<Q0, u8, StackBacking<8>>::new();
    a.clone_to_chain_arena(&mut chain, |_, t| *t.v()).unwrap();
    assert_eq!(ChainArena::_check_invariants(&chain), Ok(()));
    assert_eq!(chain_of(&chain, ptrs[1]), vec![0, 1, 2]);
    // and the `Ptr`s are preserved
    for (i, p) in ptrs.iter().enumerate() {
        assert_eq!(chain[*p], [2u8, 0, 1][i]);
    }
    let mut arena = Arena::<Q0, u8, StackBacking<8>>::new();
    a.clone_to_arena(&mut arena, |_, link| *link.t.t.v())
        .unwrap();
    for (i, p) in ptrs.iter().enumerate() {
        assert_eq!(arena[*p], [2u8, 0, 1][i]);
    }
    // and the fallibility is reported instead of panicked on
    let mut small = ChainArena::<Q0, u8, StackBacking<2>>::new();
    assert_eq!(
        a.clone_to_chain_arena(&mut small, |_, t| *t.v()),
        Err(ReallocationError::BeyondMaxCapacity)
    );
    let mut small = Arena::<Q0, u8, StackBacking<2>>::new();
    assert_eq!(
        a.clone_to_arena(&mut small, |_, link| *link.t.t.v()),
        Err(ReallocationError::BeyondMaxCapacity)
    );
}

#[test]
#[cfg(feature = "alloc")]
fn ord_set_max_capacity() {
    let mut a = SimpleOrdArena::<Q0, OrdPair<u8, u8>, LimitedHeapBacking>::new();
    assert_eq!(a.max_capacity(), Some(0));
    a.set_max_capacity(4).unwrap();
    assert_eq!(a.max_capacity(), Some(4));
    for k in 0..4u8 {
        let _ = a.insert(OrdPair::new(k, k));
    }
    assert_eq!(
        a.insert_reallocating(OrdPair::new(4, 4)).map(|_| ()),
        Err(OrdInsertionError::BeyondMaxCapacity)
    );
    assert_eq!(a.set_max_capacity(2), Err(MaxCapacityReductionError));
    a.clear().allow();
    a.set_max_capacity(0).unwrap();
    assert_eq!(a.capacity(), 0);
}

// ---------------------------------------------------------------------------
// chain arena gaps that the fuzz does not reach
// ---------------------------------------------------------------------------

/// A link of a chain arena, flattened for comparison
type FlatLink = (Q0, (Option<usize>, Option<usize>), u8);

fn flat_link(p: Q0, link: LinkNoGen<Q0, u8>) -> FlatLink {
    let raw = |i| PtrInx::try_into_usize(i).unwrap().get();
    (p, (link.prev().map(raw), link.next().map(raw)), link.t)
}

#[test]
fn chain_arena_into_iterators() {
    let (mut a, ..) = mixed_chains();
    // by reference, which gives the interlinks as well
    let by_ref: Vec<FlatLink> = (&a)
        .into_iter()
        .map(|(p, link)| flat_link(p, *link))
        .collect();
    assert_eq!(by_ref.len(), a.len());
    assert_eq!(by_ref[0].2, a[by_ref[0].0]);

    // mutably, which also gives the interlinks
    let mut n = 0usize;
    for (p, link) in &mut a {
        assert_eq!(p.inx(), p.inx());
        *link.t = link.t.wrapping_add(1);
        n = n.wrapping_add(1);
    }
    assert_eq!(n, a.len());
    assert_eq!(a[by_ref[0].0], by_ref[0].2.wrapping_add(1));
    for (_, link) in &mut a {
        *link.t = link.t.wrapping_sub(1);
    }
    assert_eq!(a[by_ref[0].0], by_ref[0].2);

    // and by value, which is a capacity drain that keeps the interlinks
    let owned: Vec<FlatLink> = a.into_iter().map(|(p, link)| flat_link(p, link)).collect();
    assert_eq!(owned, by_ref);
}
