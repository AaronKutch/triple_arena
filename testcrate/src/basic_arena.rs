use std::{cmp::max, mem, num::NonZeroUsize, slice::GetDisjointMutError};

use stacked_errors::{StackableErr, StackedError, bail, ensure, ensure_eq};
use star_rng::StarRng;
use triple_arena::{
    AllocError, Arena, HeapBacking, InvalidationResult, MaxCapacityReductionError,
    NotWithinCapacityError, ReallocationError,
    traits::{Advancer, ArenaInsertTrait, ArenaTrait, Ptr, SingularGenerationArena},
    utils::traits::{PtrGen, PtrInx},
};

use crate::{
    P2, TestGen,
    cdgen::{Cd, CdGen, CkMap},
};

#[derive(Clone, Copy)]
pub struct Stats {
    /// The limit that the test stays around (this is not necessarily exactly
    /// followed)
    pub test_limit: usize,
    /// If the capacity is fixed
    pub fixed_cap: Option<usize>,
    pub n: usize,
    pub iters999: Option<usize>,
}

#[derive(Clone, Copy, Default)]
pub struct D1;

/// Use the [LIMIT] for fixed length types and as the limit for settable limit
/// types, ignore otherwise
pub fn fuzz<
    P: Ptr,
    A: ArenaTrait<P, Cd<()>> + ArenaInsertTrait<P, Cd<()>> + SingularGenerationArena<P>,
>(
    mut stats: Stats,
    rng: &mut StarRng,
    cd_gen: &mut CdGen<()>,
    cd_gen1: &mut CdGen<D1>,
    mut a: A,
    mut check_invariants: impl FnMut(&mut A) -> Result<(), StackedError>,
    // set iff `SetMaxCapacity` is implemented
    mut set_max_capacity: Option<fn(&mut A, usize) -> Result<(), MaxCapacityReductionError>>,
) -> Result<(), StackedError> {
    ensure!(cd_gen.is_empty());

    // reference
    let mut b = CkMap::<(), P>::new();
    let mut b_capacity = a.capacity();
    let mut g = TestGen::<P>(PtrGen::two());

    // set and used by the clone_from section
    let mut a1 = Arena::<P, Cd<D1>, HeapBacking>::new();
    let mut b1 = CkMap::<D1, P>::new();

    // for temporary debug changes
    #[allow(unused)]
    let mut op_inx = usize::MAX;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;

    // generate invalid `Ptr`s via `P::invalid()`, an existing allocation but with
    // wrong generation (incremented or gen 1), or index 1 in a free slot, and in
    // the space between `self.m.len()` and `self.m.capacity()`
    let gen_invalid = |rng: &mut StarRng, arena: &A| {
        match rng.index(16).unwrap() {
            0 => return P::invalid(),
            1..4 => {
                if let Some(p) = arena.find_inx_first_ptr() {
                    return P::_from_raw(p.inx(), P::Gen::generational_inc(p.generation()).0);
                }
            }
            4..8 => {
                if let Some(p) = arena.find_inx_first_ptr() {
                    return P::_from_raw(p.inx(), P::Gen::one());
                }
            }
            8..12 => {
                let inx1 = P::Inx::try_from_usize(NonZeroUsize::new(1).unwrap()).unwrap();
                if let Some((generation, _)) = arena.get_inx(inx1) {
                    return P::_from_raw(inx1, P::Gen::generational_inc(generation).0);
                } else {
                    // the primary intention
                    return P::_from_raw(inx1, arena.singular_generation());
                }
            }
            12..16 => {
                if arena.capacity() > 0 {
                    let last_inx =
                        P::Inx::try_from_usize(NonZeroUsize::new(arena.capacity()).unwrap())
                            .unwrap();
                    if let Some((generation, _)) = arena.get_inx(last_inx) {
                        return P::_from_raw(last_inx, P::Gen::generational_inc(generation).0);
                    } else {
                        // the primary intention
                        return P::_from_raw(last_inx, arena.singular_generation());
                    }
                }
            }
            _ => unreachable!(),
        }
        // backup
        P::invalid()
    };

    for _ in 0..stats.n {
        let len = b.len();
        ensure_eq!(cd_gen.len(), len);
        ensure_eq!(a.len(), len);
        ensure_eq!(a.is_empty(), b.is_empty());
        ensure_eq!(a.capacity(), b_capacity);
        ensure!(len <= a.capacity());
        if let Some(fixed_cap) = stats.fixed_cap {
            ensure!(a.capacity() == fixed_cap);
        }
        if let Some(max_capacity) = a.max_capacity() {
            ensure!(a.capacity() <= max_capacity);
        }
        // if not incremented explicitly and the arena increments, then we get a
        // mismatch
        ensure_eq!(a.singular_generation(), g.0);
        check_invariants(&mut a).stack()?;
        op_inx = rng.index(1000).unwrap();
        // note: pushes and pops are balanced except for clears
        match op_inx {
            0..15 => {
                // set_max_capacity

                // except for changes, the invariants are checked at the beginning of the loop
                if let Some(set_max_capacity) = &mut set_max_capacity {
                    let before = a.capacity();
                    let max_before = a.max_capacity().stack()?;
                    if rng.next_bool() {
                        ensure!((*set_max_capacity)(&mut a, usize::MAX).is_ok());
                        // capacity can expand within the internal capacity
                        ensure!(a.capacity() >= before);
                        b_capacity = a.capacity();
                    } else {
                        let next = rng.index_inclusive(stats.test_limit);

                        if next > before {
                            // capacity can expand within the internal capacity
                            ensure!(a.capacity() >= before);
                            b_capacity = a.capacity();
                        } else if next >= a.capacity() {
                            ensure_eq!((*set_max_capacity)(&mut a, next), Ok(()));
                            // b_capacity left unchanged to check that capacity
                            // does not change
                        } else if next >= a.len() {
                            // the only type currently that implements `set_max_capacity` currently
                            // follows the tight `next >= a.next()` bound
                            ensure_eq!((*set_max_capacity)(&mut a, next), Ok(()));
                            ensure!(a.capacity() < before);
                            b_capacity = a.capacity();
                        } else {
                            ensure_eq!(
                                (*set_max_capacity)(&mut a, next),
                                Err(MaxCapacityReductionError)
                            );
                            ensure_eq!(before, a.capacity());
                            ensure_eq!(max_before, a.max_capacity().stack()?);
                        }
                    }
                    ensure!(a.capacity() <= a.max_capacity().stack()?);
                }
            }
            15..75 => {
                // reallocate_min_capacity success
                if let Some(max_capacity) = a.max_capacity()
                    && max_capacity < usize::MAX
                {
                    let new_cap = rng.index_inclusive(max_capacity);
                    a.reallocate_min_capacity(new_cap).stack()?;
                    ensure!(a.capacity() >= new_cap)
                } else {
                    let new_cap = rng.index_inclusive(stats.test_limit);
                    a.reallocate_min_capacity(new_cap).stack()?;
                    ensure!(a.capacity() >= new_cap)
                }
                b_capacity = a.capacity();
            }
            75..100 => {
                // reallocate_min_capacity failure
                let cap = a.capacity();
                if let Some(max_capacity) = a.max_capacity()
                    && max_capacity < usize::MAX
                {
                    ensure_eq!(
                        a.reallocate_min_capacity(max_capacity + 1),
                        Err(ReallocationError::BeyondMaxCapacity)
                    );
                    ensure_eq!(
                        a.reallocate_min_capacity(usize::MAX),
                        Err(ReallocationError::BeyondMaxCapacity)
                    );
                } else {
                    // could succeed for ZSTs
                    ensure_eq!(
                        a.reallocate_min_capacity(usize::MAX),
                        Err(ReallocationError::AllocError)
                    );
                }
                ensure_eq!(cap, a.capacity());
            }
            100..200 => {
                // insert_within_capacity
                if len < a.capacity() {
                    let (k, t) = cd_gen.new_cd();
                    let Ok((p, t1)) = a.insert_within_capacity(t) else {
                        bail!("")
                    };
                    ensure_eq!(t1.key(), k);
                    b.insert(k, p);
                } else {
                    let (_, t) = cd_gen.new_cd();
                    ensure_eq!(
                        a.insert_within_capacity(t).map(|_| ()),
                        Err(NotWithinCapacityError)
                    );
                }
            }
            200..250 => {
                // insert_reallocating

                let max_reached = a
                    .max_capacity()
                    .is_some_and(|max_capacity| max_capacity == len)
                    || stats.fixed_cap.is_some_and(|cap| cap == len);

                if len < a.capacity() {
                    let (k, t) = cd_gen.new_cd();
                    let Ok((p, t1)) = a.insert_reallocating(t) else {
                        bail!("")
                    };
                    ensure_eq!(t1.key(), k);
                    b.insert(k, p);
                } else if max_reached {
                    let (_, t) = cd_gen.new_cd();
                    ensure_eq!(
                        a.insert_reallocating(t).map(|_| ()),
                        Err(ReallocationError::BeyondMaxCapacity)
                    );
                } else if len >= stats.test_limit {
                    // do nothing
                } else {
                    // can increase capacity
                    let (k, t) = cd_gen.new_cd();
                    let cap = a.capacity();
                    let Ok((p, t1)) = a.insert_reallocating(t) else {
                        bail!("")
                    };
                    ensure_eq!(t1.key(), k);
                    // check that capacity increased
                    ensure!(a.capacity() > cap);
                    b.insert(k, p);
                    b_capacity = a.capacity();
                }
            }
            250..300 => {
                // insert

                let max_reached = a
                    .max_capacity()
                    .is_some_and(|max_capacity| max_capacity == len)
                    || stats.fixed_cap.is_some_and(|cap| cap == len);

                if len < a.capacity() {
                    let (k, t) = cd_gen.new_cd();
                    let (p, t1) = a.insert(t);
                    ensure_eq!(t1.key(), k);
                    b.insert(k, p);
                } else if max_reached || len >= stats.test_limit {
                    // do nothing
                } else {
                    let (k, t) = cd_gen.new_cd();
                    let cap = a.capacity();
                    let (p, t1) = a.insert(t);
                    ensure_eq!(t1.key(), k);
                    // check that capacity increased
                    ensure!(a.capacity() > cap);
                    b.insert(k, p);
                    b_capacity = a.capacity();
                }
            }
            300..500 => {
                // remove
                if let Some((k, p)) = b.remove_rand(rng) {
                    match a.remove(p) {
                        InvalidationResult::Success(t) => {
                            ensure_eq!(k, t.key());
                            ensure!(!g.invalidate());
                        }
                        InvalidationResult::GenerationOverflow(t) => {
                            ensure_eq!(k, t.key());
                            ensure!(g.invalidate());
                        }
                        InvalidationResult::InvalidPtr => {
                            bail!("")
                        }
                    }
                } else {
                    let invalid = gen_invalid(rng, &a);
                    ensure!(matches!(a.remove(invalid), InvalidationResult::InvalidPtr))
                }
            }
            // we do these to test against when there are elements in the arena
            500..520 => {
                // remove invalid
                let invalid = gen_invalid(rng, &a);
                ensure!(matches!(a.remove(invalid), InvalidationResult::InvalidPtr))
            }
            520..600 => {
                // invalidate
                if let Some((_, p)) = b.get_mut_rand(rng) {
                    match a.invalidate(*p) {
                        InvalidationResult::Success(p1) => {
                            *p = p1;
                            ensure!(!g.invalidate());
                        }
                        InvalidationResult::GenerationOverflow(p1) => {
                            *p = p1;
                            ensure!(g.invalidate());
                        }
                        InvalidationResult::InvalidPtr => {
                            bail!("")
                        }
                    }
                } else {
                    let invalid = gen_invalid(rng, &a);
                    ensure!(matches!(
                        a.invalidate(invalid),
                        InvalidationResult::InvalidPtr
                    ))
                }
            }
            600..620 => {
                // invalidate invalid
                let invalid = gen_invalid(rng, &a);
                ensure!(matches!(
                    a.invalidate(invalid),
                    InvalidationResult::InvalidPtr
                ))
            }
            620..800 => {
                // contains, get, get_mut, get_inx, get_inx_mut
                if let Some((k, p)) = b.get_rand(rng) {
                    let p = *p;
                    ensure!(a.contains(p));
                    ensure_eq!(a.get(p).map(|t| t.key()), Some(k));
                    ensure_eq!(a.get_mut(p).map(|t| t.key()), Some(k));
                    ensure_eq!(
                        a.get_inx(p.inx())
                            .map(|(generation, t)| (generation, t.key())),
                        Some((p.generation(), k))
                    );
                    ensure_eq!(
                        a.get_inx_mut(p.inx())
                            .map(|(generation, t)| (generation, t.key())),
                        Some((p.generation(), k))
                    );
                } else {
                    let p = gen_invalid(rng, &a);
                    ensure!(!a.contains(p));
                    ensure!(a.get(p).is_none());
                    ensure!(a.get_mut(p).is_none());
                    ensure!(a.get_inx(p.inx()).is_none());
                    ensure!(a.get_inx_mut(p.inx()).is_none());
                }
            }
            800..820 => {
                // contains, get, get_mut all invalid
                let p = gen_invalid(rng, &a);
                ensure!(!a.contains(p));
                ensure!(a.get(p).is_none());
                ensure!(a.get_mut(p).is_none());

                if let Some((generation, _)) = a.get_inx(p.inx()) {
                    ensure!(a.contains(P::_from_raw(p.inx(), generation)));
                }
                if let Some((generation, _)) = a.get_inx_mut(p.inx()) {
                    ensure!(a.contains(P::_from_raw(p.inx(), generation)));
                }
            }
            820..900 => {
                // get_disjoint_mut, get_disjoint_inx_mut and failures

                let [] = a.get_disjoint_mut([]).stack()?;
                let [] = a.get_disjoint_inx_mut([]).stack()?;

                let i =
                    P::Inx::try_from_usize(NonZeroUsize::new(a.capacity() + 1).unwrap()).unwrap();
                ensure!(
                    a.get_disjoint_inx_mut([i])
                        .is_err_and(|e| e == GetDisjointMutError::IndexOutOfBounds)
                );
                ensure!(
                    a.get_disjoint_mut([P::_from_raw(i, a.singular_generation())])
                        .is_err_and(|e| e == GetDisjointMutError::IndexOutOfBounds)
                );

                'outer: {
                    let mut set = [P::invalid().inx(); 3];
                    let mut set1 = [P::invalid(); 3];
                    if len >= set.len() {
                        for i in &mut set {
                            *i = P::Inx::try_from_usize(
                                NonZeroUsize::new(rng.index(len).unwrap() + 1).unwrap(),
                            )
                            .unwrap();
                        }
                        for i in &set {
                            if a.get_inx(*i).is_none() {
                                ensure!(a.get_disjoint_inx_mut(set).is_err());
                                ensure!(a.get_disjoint_mut(set1).is_err());
                                break 'outer;
                            }
                        }
                        for (set_i0, i) in set.iter().enumerate() {
                            for (set_i1, j) in set.iter().enumerate() {
                                if set_i0 != set_i1 && *i == *j {
                                    ensure!(a.get_disjoint_inx_mut(set).is_err_and(
                                        |e| e == GetDisjointMutError::OverlappingIndices
                                    ));
                                    ensure!(a.get_disjoint_mut(set1).is_err());
                                    break 'outer;
                                }
                            }
                        }

                        let res = a
                            .get_disjoint_inx_mut(set)
                            .stack()?
                            .map(|(generation, t)| (generation, t.key()));
                        for ((generation, k), p) in res.iter().zip(set.iter()) {
                            let tmp = a.get_inx(*p).stack()?;
                            ensure_eq!(tmp.0, *generation);
                            ensure_eq!(tmp.1.key(), *k);
                        }
                        for i in 0..set.len() {
                            set1[i] = P::_from_raw(set[i], res[i].0);
                        }

                        match a.get_disjoint_mut(set1) {
                            Ok(res) => {
                                let res = res.map(|t| t.key());
                                for (k, p) in res.iter().zip(set1.iter()) {
                                    ensure_eq!(a.get(*p).stack()?.key(), *k);
                                }
                            }
                            Err(GetDisjointMutError::IndexOutOfBounds) => bail!(""),
                            _ => bail!(""),
                        }
                    }
                }
            }
            900..910 => {
                // advancer
                let mut i = 0;
                let mut rand_remove_i = if len == 0 { 0 } else { rng.index(len).unwrap() };
                let mut rand_insert_i = if len == 0 { 0 } else { rng.index(len).unwrap() };
                if let Some(cap) = stats.fixed_cap
                    && a.len() == cap
                    && rand_remove_i > rand_insert_i
                {
                    // need to remove before inserting again
                    mem::swap(&mut rand_insert_i, &mut rand_remove_i);
                }
                let mut adv = a.advancer();
                while let Some(p) = adv.advance(&a) {
                    assert_eq!(p, *b.get(a.get(p).stack()?.key()).stack()?);

                    // remove and insert at random times
                    if i == rand_remove_i {
                        let (k, p) = b.remove(i).unwrap();
                        assert_eq!(k, a.remove(p).ok().unwrap().key());
                        g.invalidate();
                    }
                    if i == rand_insert_i {
                        let (k, t) = cd_gen.new_cd();
                        let (p, _) = a.insert(t);
                        b.insert(k, p);
                    }
                    i += 1;
                }
                // depends on the invalidated elements witnessed
                assert!((i == len.saturating_sub(1)) || (i == len) || (i == (len + 1)));
            }
            910..920 => {
                // ptrs, ordered_advancer, find_inx_last_ptr, find_inx_first_ptr
                let ptrs: Vec<P> = a.ptrs().collect();
                ensure_eq!(len, ptrs.len());
                if len > 0 {
                    ensure_eq!(a.find_inx_first_ptr().stack()?, *ptrs.first().stack()?);
                    ensure_eq!(a.find_inx_last_ptr().stack()?, *ptrs.last().stack()?);
                } else {
                    ensure!(a.find_inx_first_ptr().is_none());
                    ensure!(a.find_inx_last_ptr().is_none());
                }
                if let Some(mut i) = rng.index(ptrs.len()) {
                    let rev = rng.next_bool();
                    let mut adv = a.ordered_advancer(ptrs[i].inx(), rev);
                    loop {
                        let p = adv.advance(&a).stack()?;
                        ensure_eq!(ptrs[i], p);
                        if rev {
                            if i == 0 {
                                ensure!(adv.advance(&a).is_none());
                                break;
                            }
                            i -= 1;
                        } else {
                            i += 1;
                            if i == len {
                                ensure!(adv.advance(&a).is_none());
                                break;
                            }
                        }
                    }
                } else {
                    let inx1 = P::Inx::try_from_usize(NonZeroUsize::new(1).unwrap()).unwrap();
                    let mut adv = a.ordered_advancer(inx1, false);
                    ensure!(adv.advance(&a).is_none());
                    let mut adv = a.ordered_advancer(inx1, true);
                    ensure!(adv.advance(&a).is_none());
                    if a.capacity() > 0 {
                        let inx_last =
                            P::Inx::try_from_usize(NonZeroUsize::new(a.capacity()).unwrap())
                                .unwrap();
                        let mut adv = a.ordered_advancer(inx_last, false);
                        ensure!(adv.advance(&a).is_none());
                        let mut adv = a.ordered_advancer(inx_last, true);
                        ensure!(adv.advance(&a).is_none());
                    }
                }
            }
            920..930 => {
                // ptrs, vals, vals_mut, iter, iter_mut
                let ptrs: Vec<P> = a.ptrs().collect();
                ensure_eq!(len, ptrs.len());
                let mut x = vec![];
                for p in ptrs {
                    x.push((p, a.get(p).stack()?.key()));
                }

                let mut i = 0;
                for t in a.vals() {
                    ensure_eq!(t.key(), x[i].1);
                    i += 1;
                }
                ensure_eq!(i, len);

                let mut i = 0;
                for t in a.vals_mut() {
                    ensure_eq!(t.key(), x[i].1);
                    i += 1;
                }
                ensure_eq!(i, len);

                let mut i = 0;
                for (p, t) in a.iter() {
                    ensure_eq!(p, x[i].0);
                    ensure_eq!(t.key(), x[i].1);
                    i += 1;
                }
                ensure_eq!(i, len);

                let mut i = 0;
                for (p, t) in a.iter_mut() {
                    ensure_eq!(p, x[i].0);
                    ensure_eq!(t.key(), x[i].1);
                    i += 1;
                }
                ensure_eq!(i, len);
            }
            // future
            930..994 => {
                if let Some((_, p)) = b.get_rand(rng) {
                    let p = *p;
                    ensure!(a.contains(p));
                } else {
                    let p = gen_invalid(rng, &a);
                    ensure!(!a.contains(p));
                }
            }
            994 => {
                // compress
                ensure_eq!(a.compress().is_overflow(), g.invalidate());
                b.clear();
                for (p, t) in a.iter() {
                    b.insert(t.key(), p);
                }
                if len > 0 {
                    ensure_eq!(
                        P::Inx::try_into_usize(a.find_inx_last_ptr().stack()?.inx())
                            .unwrap()
                            .get(),
                        a.len()
                    );
                }
            }
            995 => {
                // compress_with
                let mut new_map = vec![];
                ensure_eq!(
                    a.compress_with(|p_old, t, p_new| {
                        assert_eq!(*b.get(t.key()).unwrap(), p_old);
                        new_map.push((p_new, t.key()));
                    })
                    .is_overflow(),
                    g.invalidate()
                );
                b.clear();
                for (p, k) in new_map {
                    b.insert(k, p);
                }
                if len > 0 {
                    ensure_eq!(
                        P::Inx::try_into_usize(a.find_inx_last_ptr().stack()?.inx())
                            .unwrap()
                            .get(),
                        a.len()
                    );
                }
            }
            996 => {
                // clone_from_with, this is mainly tested in `multi_arena`, but we want
                // them here to test if `self.m.len()` and `self.m.capacity()` detachments cause
                // issues.
                match rng.index(2).unwrap() {
                    // `a1` and the like are set here, `a` will diverge again
                    0 => {
                        let mut i = 0;
                        b1.clear();
                        a1.clone_from_with_new(&a, |p, u| {
                            assert_eq!(a.get(p).unwrap().key(), u.key());
                            let (k, t) = cd_gen1.new_cd();
                            b1.insert(k, p);
                            i += 1;
                            t
                        })
                        .unwrap();
                        ensure_eq!(len, i);
                        for p in a.ptrs() {
                            ensure!(a1.contains(p));
                        }
                    }
                    1 => {
                        b.clear();
                        // `a1` was unlimited, `a` can be limited and grow capacity and run into
                        // changed limits

                        if rng.next_bool() {
                            // add a high `Ptr` for fixed capacity cases to deal
                            // with FIXME

                            // FIXME rename find_inx_last_ptr etc
                        }

                        let before = a.capacity();
                        let max_before = a.max_capacity();
                        let res = a.clone_from_with_new(&a1, |p, u| {
                            assert_eq!(a1.get(p).unwrap().key(), u.key());
                            let (k, t) = cd_gen.new_cd();
                            b.insert(k, p);
                            t
                        });
                        if let Some(max) = max_before
                            && let Some(last) = a1.find_inx_last_ptr()
                            && P::Inx::try_into_usize(last.inx()).unwrap().get() > max
                        {
                            ensure_eq!(res, Err(ReallocationError::BeyondMaxCapacity));
                        } else {
                            ensure_eq!(res, Ok(()));
                            for p in a1.ptrs() {
                                ensure!(a.contains(p));
                            }
                            ensure_eq!(a.max_capacity(), max_before);
                            ensure!(a.capacity() >= before);

                            g.0 = a1.singular_generation();
                            b_capacity = a.capacity();
                        }
                    }
                    _ => unreachable!(),
                }
            }
            997 => {
                // drain
                for tmp in a.drain() {
                    ensure_eq!(tmp.is_overflow(), g.invalidate());
                    let (p, t) = tmp.ok();
                    ensure_eq!(*b.get(t.key()).stack()?, p);
                }
                ensure!(a.is_empty());
                b.clear();
            }
            998 => {
                // clear
                b.clear();
                ensure_eq!(a.clear().is_overflow(), g.invalidate());
                iters999 += 1;
            }
            999 => {
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
                a = A::with_min_capacity(min_capacity).stack()?;
                ensure!(a.capacity() >= min_capacity);
                if stats.fixed_cap.is_some() {
                    stats.fixed_cap = Some(a.capacity());
                }
                b_capacity = a.capacity();
                iters999 += 1;
            }
            1000.. => unreachable!(),
        }
    }
    if let Some(x) = stats.iters999 {
        ensure_eq!(iters999, x);
    }
    Ok(())
}

pub fn fuzz_multi_arena_step<D: Copy + Default, P: Ptr>(
    rng: &mut StarRng,
    a: &mut Arena<P, Cd<D>, HeapBacking>,
    g: &mut TestGen<P>,
    b: &mut CkMap<D, P>,
    cd_gen: &mut CdGen<D>,
) -> Result<(), StackedError> {
    let len = a.len();
    ensure_eq!(len, b.len());
    ensure_eq!(a.singular_generation(), g.0);
    ensure_eq!(a.is_empty(), b.is_empty());
    if !cfg!(miri) {
        Arena::_check_invariants(a).unwrap();
    }
    match rng.next_u32() % 100 {
        0..50 => {
            // insert
            let (k, t) = cd_gen.new_cd();
            let p = a.insert(t);
            b.insert(k, p);
        }
        50..99 => {
            // remove
            if len != 0 {
                let (k, p) = b.remove_rand(rng).unwrap();
                ensure_eq!(k, a.remove(p).unwrap().key());
                g.invalidate();
            }
        }
        99 => {
            // clear and shrink
            a.clear();
            a.reallocate_min_capacity(0).unwrap();
            g.invalidate();
            b.clear();
        }
        100.. => unreachable!(),
    }
    Ok(())
}

#[derive(Clone, Copy)]
pub struct MultiStats {
    pub n: usize,
    pub max_len: Option<usize>,
}

// for testing `clone_from_with` which interact between multiple arenas, we just
// hardcode the heap backed arena in here
pub fn fuzz_multi_arena(
    rng: &mut StarRng,
    stats: MultiStats,
    cd_gen0: &mut CdGen<()>,
    cd_gen1: &mut CdGen<D1>,
) -> Result<(), StackedError> {
    let mut a0 = Arena::<P2, Cd<()>, HeapBacking>::new();
    let mut a1 = Arena::<P2, Cd<D1>, HeapBacking>::new();
    let mut g0 = TestGen(a0.generation());
    let mut g1 = TestGen(a1.generation());
    let mut b0 = CkMap::<(), P2>::new();
    let mut b1 = CkMap::<D1, P2>::new();

    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut max_len = 0;

    for _ in 0..stats.n {
        fuzz_multi_arena_step(rng, &mut a0, &mut g0, &mut b0, cd_gen0).stack()?;
        fuzz_multi_arena_step(rng, &mut a1, &mut g1, &mut b1, cd_gen1).stack()?;
        max_len = max(max_len, a0.len());
        match rng.index(1000).unwrap() {
            // do no major operations most of the time, rack up some random insertions and removals
            // in `inner`
            0..900 => (),
            900..950 => {
                b0.clear();
                a0.clone_from_with_new(&a1, |p, u| {
                    assert_eq!(a1.get(p).unwrap().key(), u.key());
                    let (k, t) = cd_gen0.new_cd();
                    b0.insert(k, p);
                    t
                })
                .unwrap();
                for p in a1.ptrs() {
                    ensure!(a0.contains(p));
                }
                g0.0 = a1.singular_generation();
            }
            950..1000 => {
                b1.clear();
                a1.clone_from_with_new(&a0, |p, u| {
                    assert_eq!(a0.get(p).unwrap().key(), u.key());
                    let (k, t) = cd_gen1.new_cd();
                    b1.insert(k, p);
                    t
                })
                .unwrap();
                for p in a0.ptrs() {
                    ensure!(a1.contains(p));
                }
                g1.0 = a0.singular_generation();
            }
            1000.. => unreachable!(),
        }
    }
    if let Some(max_len1) = stats.max_len {
        ensure_eq!(max_len, max_len1);
    }
    Ok(())
}
