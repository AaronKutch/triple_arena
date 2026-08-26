use std::{cmp::max, mem, num::NonZeroUsize};

use stacked_errors::{StackableErr, StackedError, bail, ensure, ensure_eq};
use star_rng::StarRng;
use triple_arena::{
    Arena, DirectArena, InvalidationOption, InvalidationResult, StackBacking,
    errors::{AllocError, DirectInsertionError, MaxCapacityReductionError, ReallocationError},
    traits::{
        Advancer, ArenaCloneFromWith, ArenaDirectInsertEntryTrait, ArenaDirectInsertTrait,
        ArenaInsertTrait, ArenaTrait, CompactArenaTrait, DisjointableArenaTrait, Ptr,
    },
    utils::traits::{ArenaBacking, NonZeroInxGenericStack, PtrGen, PtrInx},
};

// similar enough that we can reuse them
pub use crate::basic_arena::{MultiStats, Stats};
use crate::{
    TestGen,
    basic_arena::{common_compact_fuzz_step250, gen_invalid},
    cdgen::{Cd, CdGen, Ck, CkMap},
    misc::{D1, Meta},
};

/// Returns a random virtual free slot in `1..=a.capacity()`
fn rand_free_inx<P: Ptr, A: CompactArenaTrait<P, Cd<()>>>(
    rng: &mut StarRng,
    a: &A,
) -> Option<NonZeroUsize> {
    let mut free = vec![];
    for raw in 1..=a.capacity() {
        let raw = NonZeroUsize::new(raw).unwrap();
        // the capacity is already clamped by the max index
        let inx = P::Inx::try_from_usize(raw).unwrap();
        if a.get_inx(inx).is_none() {
            free.push(raw);
        }
    }
    free.get(rng.index(free.len())?).copied()
}

/// Attempts a `direct_insert_within_capacity(p)`, determining the expected
/// outcome from the state of `a` beforehand, and recording a successful
/// insertion in `b`. If `cancel` is set then the entry is dropped instead of
/// being inserted into.
fn try_direct_insert<
    P: Ptr,
    A: CompactArenaTrait<P, Cd<()>>
        + DisjointableArenaTrait<P, Cd<()>>
        + ArenaDirectInsertTrait<P, Cd<()>>,
>(
    a: &mut A,
    b: &mut CkMap<(), P>,
    cd_gen: &mut CdGen<()>,
    p: P,
    cancel: bool,
) -> Result<(), StackedError> {
    let len = a.len();
    let cap = a.capacity();
    let expected = if PtrInx::try_into_usize(p.inx()).is_none_or(|raw| raw.get() > cap) {
        Err(DirectInsertionError::NotWithinCapacity)
    } else if a.get_inx(p.inx()).is_some() {
        Err(DirectInsertionError::ExistingElementAtIndex)
    } else {
        Ok(())
    };
    // the entry keeps `a` mutably borrowed, so the checking is done afterwards.
    // `Ok(None)` means the insertion was cancelled.
    let outcome: Result<Option<Ck<()>>, DirectInsertionError> =
        match a.direct_insert_within_capacity(p) {
            Ok(entry) => {
                if cancel {
                    // REF(insertion_idempotency)
                    drop(entry);
                    Ok(None)
                } else {
                    let (k, t) = cd_gen.new_cd();
                    entry.insert(t);
                    Ok(Some(k))
                }
            }
            Err(e) => Err(e),
        };
    match outcome {
        Ok(None) => {
            ensure_eq!(expected, Ok(()));
            ensure!(!a.contains(p));
            ensure!(a.get_inx(p.inx()).is_none());
            ensure_eq!(a.len(), len);
        }
        Ok(Some(k)) => {
            ensure_eq!(expected, Ok(()));
            ensure_eq!(a.len(), len + 1);
            ensure_eq!(a.get(p).stack()?.key(), k);
            // the entry is given exactly the generation that was asked for
            ensure_eq!(a.get_inx(p.inx()).stack()?.0, p.generation());
            b.insert(k, p);
        }
        Err(e) => ensure_eq!(Err(e), expected),
    }
    // direct insertion never reallocates
    ensure_eq!(a.capacity(), cap);
    Ok(())
}

pub fn fuzz<
    P: Ptr,
    A: ArenaCloneFromWith<P, Cd<()>>
        + CompactArenaTrait<P, Cd<()>>
        + DisjointableArenaTrait<P, Cd<()>>
        + ArenaDirectInsertTrait<P, Cd<()>>,
>(
    meta: &mut Meta<Stats>,
    a: &mut A,
    mut check_invariants: impl FnMut(&mut A) -> Result<(), StackedError>,
    // set iff `SetMaxCapacity` is implemented
    set_max_capacity: Option<fn(&mut A, usize) -> Result<(), MaxCapacityReductionError>>,
    transfer_reallocating: fn(
        &mut A,
        P::Gen,
        &mut Arena<P, Cd<D1>, StackBacking<128>>,
        &mut dyn FnMut(P, InvalidationOption<Cd<D1>>, P) -> Cd<()>,
    ) -> Result<(), ReallocationError>,
) -> Result<(), StackedError> {
    let rng = &mut meta.rng;
    let stats = meta.stats.as_mut().stack()?;
    let cd_gen = &mut stats.cd_gen;
    let cd_gen1 = &mut stats.cd_gen1;

    // reference
    let mut b = CkMap::<(), P>::new();
    let mut b_capacity = a.capacity();
    // There is no singular generation, so this stands in for whatever the caller is
    // using as a source of generations, which is the generation of a followed arena
    // in the main use case but can be anything. It is advanced on every insertion
    // only so that reusing an internal slot does not revive the `Ptr`s of whatever
    // was there before.
    let mut g = TestGen::<P>(PtrGen::two());

    // set and used by the clone_from and transfer sections
    let mut a1 = Arena::<P, Cd<D1>, StackBacking<128>>::new();

    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;
    let mut max_len = 0usize;

    for i in 0..stats.n {
        let len = b.len();
        max_len = max(max_len, len);
        ensure_eq!(cd_gen.len(), len);
        ensure_eq!(a.len(), len);
        ensure_eq!(a.is_empty(), b.is_empty());
        ensure_eq!(a.capacity(), b_capacity);
        ensure!(len <= a.capacity());
        if let Some(fixed_cap) = stats.fixed_cap {
            ensure_eq!(a.capacity(), fixed_cap);
        }
        if let Some(max_capacity) = a.max_capacity() {
            ensure!(a.capacity() <= max_capacity);
        }
        // currently I don't know of any direct insertion arena that would have this
        ensure!(a.singular_generation().is_none());
        check_invariants(a).stack()?;

        meta.i = i;
        meta.op_inx = rng.index_inclusive(1023);
        // note: insertions and removals are balanced except for clears which we make
        // rare
        match meta.op_inx {
            0..250 => common_compact_fuzz_step250(
                rng,
                a,
                stats.test_limit,
                meta.op_inx,
                &mut b,
                &mut b_capacity,
                None,
                set_max_capacity,
                |b, rng| b.get_mut_rand(rng),
                Cd::key,
            )
            .stack()?,
            250..300 => {
                // `direct_insert_within_capacity` at an arbitrary index in
                // `1..=(capacity + 1)`. Every index within the capacity is a valid
                // target regardless of whether the backing has reached it yet, so this
                // reaches all of the outcomes: a slot beyond `m.len()`, a free slot in
                // the middle, a slot that already has an element, and an index outside
                // of the capacity.
                let raw = NonZeroUsize::new(rng.index_inclusive(a.capacity()) + 1).unwrap();
                let inx = PtrInx::try_from_usize(raw).stack()?;
                try_direct_insert(a, &mut b, cd_gen, P::_from_raw(inx, g.0), false).stack()?;
                g.invalidate();
            }
            300..450 => {
                // the same but always at a free index, which is what actually drives the
                // arena towards being full
                if let Some(raw) = rand_free_inx(rng, a) {
                    let inx = PtrInx::try_from_usize(raw).stack()?;
                    try_direct_insert(a, &mut b, cd_gen, P::_from_raw(inx, g.0), false).stack()?;
                    g.invalidate();
                } else {
                    // the arena is full, so every index must be rejected
                    ensure_eq!(len, a.capacity());
                    let raw = NonZeroUsize::new(rng.index_inclusive(a.capacity()) + 1).unwrap();
                    let inx = PtrInx::try_from_usize(raw).stack()?;
                    let expected = if raw.get() > a.capacity() {
                        DirectInsertionError::NotWithinCapacity
                    } else {
                        DirectInsertionError::ExistingElementAtIndex
                    };
                    ensure_eq!(
                        a.direct_insert_within_capacity(P::_from_raw(inx, g.0))
                            .map(|_| ()),
                        Err(expected)
                    );
                }
            }
            450..475 => {
                // the same with `Ptr`s that are invalid in the normal sense. Only the
                // index decides the outcome, and whatever generation comes along with it
                // is accepted as the new one.
                let p = gen_invalid(rng, a);
                try_direct_insert(a, &mut b, cd_gen, p, false).stack()?;
            }
            475..500 => {
                // direct insertion with cancellation
                let raw = if rng.next_bool() {
                    rand_free_inx(rng, a)
                } else {
                    NonZeroUsize::new(rng.index_inclusive(a.capacity()) + 1)
                };
                if let Some(raw) = raw {
                    let inx = PtrInx::try_from_usize(raw).stack()?;
                    try_direct_insert(a, &mut b, cd_gen, P::_from_raw(inx, g.0), true).stack()?;
                }
            }
            500..600 => {
                // remove
                if let Some((k, p)) = b.remove_rand(rng) {
                    match a.remove(p) {
                        InvalidationResult::Success(t) => ensure_eq!(k, t.key()),
                        InvalidationResult::GenerationOverflow(_) => bail!(),
                        InvalidationResult::InvalidPtr => bail!(),
                    }
                } else {
                    let invalid = gen_invalid(rng, a);
                    ensure!(matches!(a.remove(invalid), InvalidationResult::InvalidPtr))
                }
            }
            600..700 => {
                // remove_inx
                if let Some((k, p)) = b.remove_rand(rng) {
                    match a.remove_inx(p.inx()) {
                        InvalidationResult::Success((generation, t)) => {
                            ensure_eq!(p.generation(), generation);
                            ensure_eq!(k, t.key());
                        }
                        InvalidationResult::GenerationOverflow(_) => bail!(),
                        InvalidationResult::InvalidPtr => bail!(),
                    }
                } else {
                    let invalid = gen_invalid(rng, a);
                    if a.get_inx(invalid.inx()).is_none() {
                        ensure!(matches!(
                            a.remove_inx(invalid.inx()),
                            InvalidationResult::InvalidPtr
                        ));
                    }
                }
            }
            700..750 => {
                // remove, remove_inx all invalid
                let invalid = gen_invalid(rng, a);
                ensure!(matches!(a.remove(invalid), InvalidationResult::InvalidPtr));
                if a.get_inx(invalid.inx()).is_none() {
                    ensure!(matches!(
                        a.remove_inx(invalid.inx()),
                        InvalidationResult::InvalidPtr
                    ));
                }
            }
            750..800 => {
                // get_inx_unwrap, get_inx_mut_unwrap
                if let Some((k, p)) = b.get_rand(rng) {
                    let p = *p;
                    ensure_eq!(a.get_inx(p.inx()).stack()?.1.key(), k);
                    ensure_eq!(a.get_inx_mut(p.inx()).stack()?.1.key(), k);
                } else {
                    let p = gen_invalid(rng, a);
                    ensure!(!a.contains(p));
                }
            }
            800..825 => {
                // advancer with removals and insertions during the loop
                let mut i = 0;
                let mut rand_remove_i = if len == 0 { 0 } else { rng.index(len).unwrap() };
                let mut rand_insert_i = if len == 0 { 0 } else { rng.index(len).unwrap() };
                if (len == a.capacity()) && (rand_remove_i > rand_insert_i) {
                    // need to remove before there is a free index again
                    mem::swap(&mut rand_insert_i, &mut rand_remove_i);
                }
                let mut adv = a.advancer();
                while let Some(p) = adv.advance(a) {
                    ensure_eq!(p, *b.get(a.get(p).stack()?.key()).stack()?);

                    // remove and insert at random times
                    if i == rand_remove_i {
                        let (k, p) = b.remove(i).stack()?;
                        ensure_eq!(k, a.remove(p).allow().stack()?.key());
                    }
                    if i == rand_insert_i
                        && let Some(raw) = rand_free_inx(rng, a)
                    {
                        let inx = PtrInx::try_from_usize(raw).stack()?;
                        let (k, t) = cd_gen.new_cd();
                        let p = P::_from_raw(inx, g.0);
                        g.invalidate();
                        a.direct_insert_within_capacity(p).stack()?.insert(t);
                        b.insert(k, p);
                    }
                    i += 1;
                }
                // depends on the invalidated elements witnessed
                ensure!((i == len.saturating_sub(1)) || (i == len) || (i == (len + 1)));
            }
            // extra room
            825..1015 => {
                if let Some((_, p)) = b.get_rand(rng) {
                    let p = *p;
                    ensure!(a.contains(p));
                } else {
                    let p = gen_invalid(rng, a);
                    ensure!(!a.contains(p));
                }
            }
            1015 => {
                // compress

                // the generations are always preserved and there is never overflow
                ensure!(!a.compress(rng.next_bool()).is_overflow());
                b.clear();
                for (p, t) in a.iter() {
                    b.insert(t.key(), p);
                }
                if len > 0 {
                    ensure_eq!(
                        PtrInx::try_into_usize(a.find_last_inx_ptr().stack()?.inx())
                            .stack()?
                            .get(),
                        a.len()
                    );
                }
            }
            1016 => {
                // compress_with
                let mut new_map = vec![];
                let mut res = Ok(());
                let o = a
                    .compress_with(rng.next_bool(), |p_old, t, p_new| {
                        if *b.get(t.key()).unwrap() != p_old {
                            res = Err(());
                        }
                        // the generation moves along with the entry
                        if p_old.generation() != p_new.generation() {
                            res = Err(());
                        }
                        new_map.push((p_new, t.key()));
                    })
                    .is_overflow();
                ensure!(res.is_ok());
                ensure!(!o);
                b.clear();
                for (p, k) in new_map {
                    b.insert(k, p);
                }
                if len > 0 {
                    ensure_eq!(
                        PtrInx::try_into_usize(a.find_last_inx_ptr().stack()?.inx())
                            .stack()?
                            .get(),
                        a.len()
                    );
                }
            }
            // these are mainly tested in `multi_direct_arena`, but we want them here to test if
            // `self.m.len()` and `self.m.capacity()` detachments cause issues
            1017 => {
                // clone_from_with part 0

                // `a1` and the like are set here, `a` will diverge again

                let mut i = 0;
                a1.clone_from_with(a, |p, u| {
                    assert_eq!(a.get(p).unwrap().key(), u.key());
                    let (_, t) = cd_gen1.new_cd();
                    i += 1;
                    t
                })
                .unwrap();
                ensure_eq!(len, i);
                for p in a.ptrs() {
                    ensure!(a1.contains(p));
                }
            }
            1018 => {
                // clone_from_with part 1

                // `a1` was unlimited, `a` can be limited and grow capacity and run into
                // changed limits

                if rng.next_bool() {
                    // add a high `Ptr` for fixed capacity cases to deal with
                    for _ in 0..stats.test_limit {
                        if a1.insert_reallocating(cd_gen1.new_cd().1).is_err() {
                            break;
                        }
                    }
                }

                let before = a.capacity();
                let max_before = a.max_capacity();
                let mut on_first_call = true;
                let res = a.clone_from_with(&a1, |p, u| {
                    assert_eq!(a1.get(p).unwrap().key(), u.key());
                    if on_first_call {
                        b.clear();
                        on_first_call = false;
                    }
                    let (k, t) = cd_gen.new_cd();
                    b.insert(k, p);
                    t
                });
                if let Some(max) = max_before
                    && let Some(last) = a1.find_last_inx_ptr()
                    && PtrInx::try_into_usize(last.inx()).stack()?.get() > max
                {
                    ensure!(on_first_call);
                    ensure_eq!(res, Err(ReallocationError::BeyondMaxCapacity));
                } else {
                    // if `a1` was empty
                    if on_first_call {
                        b.clear();
                    }
                    ensure_eq!(res, Ok(()));
                    for p in a1.ptrs() {
                        ensure!(a.contains(p));
                    }
                    ensure_eq!(a.max_capacity(), max_before);
                    ensure!(a.capacity() >= before);
                    // the generations were cloned over from `a1`
                    g.0 = a1.singular_generation().stack()?;
                    b_capacity = a.capacity();
                }
            }
            1019 => {
                // transfer_reallocating part 0

                let mut i = 0;
                let mut list = vec![];
                // do something that isn't setting to a low constant
                let next_gen = PtrGen::generational_inc(a1.generation()).0;
                a1.transfer_reallocating(next_gen, a, |q, o, p| {
                    // there is no generation counter in `a` to overflow
                    assert!(!o.is_overflow());
                    assert_eq!(*b.get(o.allow().key()).unwrap(), q);
                    let (k, t) = cd_gen1.new_cd();
                    list.push((p, k));
                    i += 1;
                    t
                })
                .unwrap();
                ensure!(a.is_empty());
                ensure_eq!(list.len(), len);
                b.clear();
                for (p, k) in list {
                    ensure_eq!(a1.get(p).unwrap().key(), k);
                }
            }
            1020 => {
                // transfer_reallocating part 1

                if rng.next_bool() {
                    // add a high `Ptr` for fixed capacity cases to deal with
                    for _ in 0..stats.test_limit {
                        if a1.insert_reallocating(cd_gen1.new_cd().1).is_err() {
                            break;
                        }
                    }
                }

                let before = a.capacity();
                let max_before = a.max_capacity();
                let a1_len = a1.len();
                let mut on_first_call = true;
                let mut map = |_q: P, _o: InvalidationOption<Cd<D1>>, p: P| -> Cd<()> {
                    if on_first_call {
                        b.clear();
                        on_first_call = false;
                    }
                    let (k, t) = cd_gen.new_cd();
                    b.insert(k, p);
                    t
                };
                let next_gen = PtrGen::generational_inc(g.0).0;
                let res = transfer_reallocating(a, next_gen, &mut a1, &mut map);
                if let Some(max) = max_before
                    && a1_len > max
                {
                    ensure!(on_first_call);
                    ensure_eq!(res, Err(ReallocationError::BeyondMaxCapacity));
                } else {
                    // if `a1` was empty
                    if on_first_call {
                        b.clear();
                    }
                    ensure_eq!(res, Ok(()));
                    ensure!(a1.is_empty());
                    ensure_eq!(a.len(), a1_len);
                    ensure_eq!(a.max_capacity(), max_before);
                    ensure!(a.capacity() >= before);
                    // the entries are canonically compressed with the new generation
                    for (i, (p, _)) in a.iter().enumerate() {
                        ensure_eq!(
                            PtrInx::try_into_usize(p.inx()).stack()?.get(),
                            i.checked_add(1).stack()?
                        );
                        ensure_eq!(p.generation(), next_gen);
                    }
                    g.0 = next_gen;
                    g.invalidate();
                    b_capacity = a.capacity();
                }
            }
            1021 => {
                // drain
                for tmp in a.drain() {
                    // there is no generation counter to overflow
                    ensure!(!tmp.is_overflow());
                    let (p, t) = tmp.allow();
                    ensure_eq!(*b.get(t.key()).stack()?, p);
                }
                ensure!(a.is_empty());
                b.clear();
            }
            1022 => {
                // clear
                b.clear();
                ensure_eq!(a.clear(), InvalidationOption::Success(()));
            }
            1023 => {
                // with_min_capacity and the `Drop` impl
                b.clear();
                // note that we bypass max capacity limits since they are set to begin with in
                // some cases from this function

                // could succeed for ZSTs
                ensure_eq!(
                    A::with_min_capacity(usize::MAX).map(|_| ()),
                    Err(AllocError)
                );

                let min_capacity = rng.index_inclusive(stats.test_limit);
                *a = A::with_min_capacity(min_capacity).stack()?;
                ensure!(a.capacity() >= min_capacity);
                if stats.fixed_cap.is_some() {
                    stats.fixed_cap = Some(a.capacity());
                }
                b_capacity = a.capacity();
                iters999 += 1;
            }
            1024.. => unreachable!(),
        }
    }
    if let Some(x) = &stats.iters999 {
        x.assert_debug_eq(&iters999);
    }
    if let Some(x) = &stats.max_len {
        x.assert_debug_eq(&max_len);
    }
    a.clear().allow();
    Ok(())
}

/// After any of the canonicalizing operations, the internal slot length must be
/// trimmed to exactly the last allocated index. This is what keeps repeatedly
/// cloning and transferring between two arenas from creeping upwards, see
/// REF(exponential_double_buffer_blowup).
fn ensure_canonical_len<P: Ptr, T, B: ArenaBacking>(
    a: &DirectArena<P, T, B>,
) -> Result<(), StackedError> {
    let expected = match a.find_last_inx_ptr() {
        Some(last) => PtrInx::try_into_usize(last.inx()).stack()?.get(),
        None => 0,
    };
    ensure_eq!(a.backing().len(), expected);
    Ok(())
}

pub fn fuzz_multi_direct_arena_step<D: Copy + Default, P: Ptr>(
    rng: &mut StarRng,
    a: &mut DirectArena<P, Cd<D>, StackBacking<128>>,
    g: &mut TestGen<P>,
    b: &mut CkMap<D, P>,
    cd_gen: &mut CdGen<D>,
) -> Result<(), StackedError> {
    let len: usize = a.len();
    ensure_eq!(len, b.len());
    ensure!(a.singular_generation().is_none());
    ensure_eq!(a.is_empty(), b.is_empty());
    if !cfg!(miri) {
        DirectArena::_check_invariants(a).unwrap();
    }
    // insertions have to be weighted more than removals, because unlike the base
    // arena there is no freelist to steer them to a free slot and a good fraction
    // of them land on an existing element and do nothing
    match rng.index_inclusive(127) {
        0..96 => {
            // direct insertion at an arbitrary index
            if let Some(i) = rng.index(a.capacity()) {
                let inx = PtrInx::try_from_usize(NonZeroUsize::new(i + 1).unwrap()).stack()?;
                let p = P::_from_raw(inx, g.0);
                match a.direct_insert_within_capacity(p) {
                    Ok(entry) => {
                        g.invalidate();
                        let (k, t) = cd_gen.new_cd();
                        entry.insert(t);
                        b.insert(k, p);
                    }
                    Err(e) => ensure_eq!(e, DirectInsertionError::ExistingElementAtIndex),
                }
            }
        }
        96..127 => {
            // remove
            if len != 0 {
                let (k, p) = b.remove_rand(rng).unwrap();
                ensure_eq!(k, a.remove(p).allow().stack()?.key());
            }
        }
        127 => {
            // clear and shrink
            ensure_eq!(a.clear(), InvalidationOption::Success(()));
            a.reallocate_min_capacity(0).unwrap();
            b.clear();
        }
        128.. => unreachable!(),
    }
    Ok(())
}

// for testing `clone_from_with` and `transfer_reallocating` which interact
// between multiple arenas, we just hardcode the stack backed arena in here. The
// single arena fuzz always has a base `Arena` on the other side, so this is
// what covers a direct insertion arena being both the source and the
// destination.
pub fn fuzz_multi_direct_arena<P: Ptr>(
    rng: &mut StarRng,
    stats: MultiStats,
    cd_gen0: &mut CdGen<()>,
    cd_gen1: &mut CdGen<D1>,
) -> Result<(), StackedError> {
    let mut a0 = DirectArena::<P, Cd<()>, StackBacking<128>>::new();
    let mut a1 = DirectArena::<P, Cd<D1>, StackBacking<128>>::new();
    let mut g0 = TestGen::<P>(PtrGen::two());
    let mut g1 = TestGen::<P>(PtrGen::two());
    let mut b0 = CkMap::<(), P>::new();
    let mut b1 = CkMap::<D1, P>::new();

    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut max_len = 0;

    for _ in 0..stats.n {
        fuzz_multi_direct_arena_step(rng, &mut a0, &mut g0, &mut b0, cd_gen0).stack()?;
        fuzz_multi_direct_arena_step(rng, &mut a1, &mut g1, &mut b1, cd_gen1).stack()?;
        max_len = max(max_len, a0.len());
        match rng.index_inclusive(1023) {
            // do no major operations most of the time, rack up some random insertions and removals
            // in `inner`
            0..800 => (),
            800..850 => {
                let mut i = 0;
                let mut list = vec![];
                let len = b1.len();
                // don't set to just anything, a `DirectArena` cannot advance a generation
                // on its own and we want the reuse of internal slots to keep being caught
                let transfer_generation = PtrGen::generational_inc(g0.0).0;
                b0.clear();
                a0.transfer_reallocating(transfer_generation, &mut a1, |q, o, p| {
                    // neither side has a generation counter to overflow
                    assert!(!o.is_overflow());
                    assert_eq!(*b1.get(o.allow().key()).unwrap(), q);
                    let (k, t) = cd_gen0.new_cd();
                    list.push((p, k));
                    b0.insert(k, p);
                    i += 1;
                    t
                })
                .unwrap();
                g0.0 = transfer_generation;
                g0.invalidate();
                b1.clear();
                ensure!(a1.is_empty());
                ensure_eq!(list.len(), len);
                for (p, k) in list {
                    ensure_eq!(a0.get(p).unwrap().key(), k);
                }
                ensure_canonical_len(&a0).stack()?;
            }
            850..900 => {
                let mut i = 0;
                let mut list = vec![];
                let len = b0.len();
                let transfer_generation = PtrGen::generational_inc(g1.0).0;
                b1.clear();
                a1.transfer_reallocating(transfer_generation, &mut a0, |q, o, p| {
                    assert!(!o.is_overflow());
                    assert_eq!(*b0.get(o.allow().key()).unwrap(), q);
                    let (k, t) = cd_gen1.new_cd();
                    list.push((p, k));
                    b1.insert(k, p);
                    i += 1;
                    t
                })
                .unwrap();
                g1.0 = transfer_generation;
                g1.invalidate();
                b0.clear();
                ensure!(a0.is_empty());
                ensure_eq!(list.len(), len);
                for (p, k) in list {
                    ensure_eq!(a1.get(p).unwrap().key(), k);
                }
                ensure_canonical_len(&a1).stack()?;
            }
            900..950 => {
                b0.clear();
                a0.clone_from_with(&a1, |p, u| {
                    assert_eq!(a1.get(p).unwrap().key(), u.key());
                    let (k, t) = cd_gen0.new_cd();
                    b0.insert(k, p);
                    t
                })
                .unwrap();
                for p in a1.ptrs() {
                    ensure!(a0.contains(p));
                }
                ensure_canonical_len(&a0).stack()?;
                // the per slot generations were cloned over, so continue on from what
                // the source was using
                g0.0 = g1.0;
                g0.invalidate();
            }
            950..1024 => {
                b1.clear();
                a1.clone_from_with(&a0, |p, u| {
                    assert_eq!(a0.get(p).unwrap().key(), u.key());
                    let (k, t) = cd_gen1.new_cd();
                    b1.insert(k, p);
                    t
                })
                .unwrap();
                for p in a0.ptrs() {
                    ensure!(a1.contains(p));
                }
                ensure_canonical_len(&a1).stack()?;
                g1.0 = g0.0;
                g1.invalidate();
            }
            1024.. => unreachable!(),
        }
    }
    if let Some(max) = stats.max_len {
        max.assert_debug_eq(&max_len);
    }
    Ok(())
}
