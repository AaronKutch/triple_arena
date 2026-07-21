use std::{cmp::max, mem, num::NonZeroUsize, slice::GetDisjointMutError};

use stacked_errors::{StackableErr, StackedError, bail, ensure, ensure_eq};
use star_rng::StarRng;
use triple_arena::{
    InvalidationResult, traits::{Advancer, ArenaInsertTrait, ArenaTrait, Ptr, SingularGenerationArena}, utils::{AllocError, PtrGen, PtrInx},
};

use crate::{
    TestGen,
    cdgen::{Cd, CdGen, Ck, CkMap},
};

#[derive(Clone, Copy)]
pub struct Stats {
    pub limit: usize,
    pub n: usize,
    pub iters999: Option<usize>,
}

/// Use the [LIMIT] for fixed length types and as the limit for settable limit
/// types, ignore otherwise
pub fn fuzz<
    P: Ptr,
    A: ArenaTrait<P, Cd<()>> + ArenaInsertTrait<P, Cd<()>> + SingularGenerationArena<P>,
>(
    stats: Stats,
    rng: &mut StarRng,
    cd_gen: &mut CdGen<()>,
    mut a: A,
    mut check_invariants: impl FnMut(&mut A) -> Result<(), StackedError>,
) -> Result<(), StackedError> {
    ensure!(cd_gen.is_empty());

    // reference
    let mut b = CkMap::<(), P>::new();
    let mut g = TestGen::<P>(PtrGen::two());

    // FIXME
    // these are set by the `clone_from` variants
    //let mut a1 = A::new();
    //let mut b1 = HashMap::<Ck, P>::new();

    // for temporary debug changes
    #[allow(unused)]
    let mut op_inx = usize::MAX;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;
    let mut max_len = 0;

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
        ensure!(cd_gen.len() <= len);
        ensure_eq!(a.len(), len);
        ensure_eq!(a.is_empty(), b.is_empty());
        // if not incremented explicitly and the arena increments, then we get a
        // mismatch
        ensure_eq!(a.singular_generation(), g.0);
        ensure!(len <= a.capacity());
        let limited = a.max_capacity().is_some();
        if let Some(limit) = a.max_capacity() {
            // required for caller
            ensure_eq!(limit, stats.limit);

            ensure!(a.capacity() <= limit);
        }
        check_invariants(&mut a).stack()?;
        op_inx = rng.index(1000).unwrap();
        // note: pushes and pops are balanced except for clears
        match op_inx {
            0..75 => {
                // reallocate_min_capacity success
                let new_cap = rng.index(stats.limit + 1).unwrap();
                a.reallocate_min_capacity(new_cap).stack()?;
                ensure!(a.capacity() >= new_cap)
            }
            75..100 => {
                // reallocate_min_capacity failure
                let cap = a.capacity();
                if limited {
                    ensure_eq!(a.reallocate_min_capacity(stats.limit + 1), Err(AllocError));
                } else {
                    // could fail for ZSTs
                    ensure_eq!(a.reallocate_min_capacity(usize::MAX), Err(AllocError));
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
                    let (k, t) = cd_gen.new_cd();
                    ensure!(a.insert_within_capacity(t).is_err_and(|t| t.key() == k));
                }
            }
            200..250 => {
                // insert_reallocating
                if len < a.capacity() {
                    let (k, t) = cd_gen.new_cd();
                    let Ok((p, t1)) = a.insert_reallocating(t) else {
                        bail!("")
                    };
                    ensure_eq!(t1.key(), k);
                    b.insert(k, p);
                } else if len < stats.limit {
                    let (k, t) = cd_gen.new_cd();
                    let cap = a.capacity();
                    let Ok((p, t1)) = a.insert_reallocating(t) else {
                        bail!("")
                    };
                    ensure_eq!(t1.key(), k);
                    // check that capacity increased
                    ensure!(a.capacity() > cap);
                    b.insert(k, p);
                } else if limited {
                    let (k, t) = cd_gen.new_cd();
                    ensure!(a.insert_reallocating(t).is_err_and(|t| t.key() == k));
                } else {
                    // do nothing
                }
            }
            250..300 => {
                // insert
                if len < a.capacity() {
                    let (k, t) = cd_gen.new_cd();
                    let (p, t1) = a.insert(t);
                    ensure_eq!(t1.key(), k);
                    b.insert(k, p);
                } else if len < stats.limit {
                    let (k, t) = cd_gen.new_cd();
                    let cap = a.capacity();
                    let (p, t1) = a.insert(t);
                    ensure_eq!(t1.key(), k);
                    // check that capacity increased
                    ensure!(a.capacity() > cap);
                    b.insert(k, p);
                } else {
                    // do nothing
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
                let mut rand_remove_i = if len == 0 {0} else { rng.index(len).unwrap()};
                let mut rand_insert_i = if len == 0 {0} else { rng.index(len).unwrap()};
                if a.len() == stats.limit && rand_remove_i > rand_insert_i {
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
            900..999 => {}
            /*900..=909 => {
                // ptrs
                let mut n = 0;
                for ptr in a.ptrs() {
                    assert_eq!(ptr, b[&a[ptr]]);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            910..=919 => {
                // vals
                let mut n = 0;
                for t in a.vals() {
                    let p = b[t];
                    assert_eq!(a[p], *t);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            920..=929 => {
                // vals_mut
                let mut n = 0;
                let tmp: Vec<u64> = a.vals_mut().map(|t| *t).collect();
                for t in tmp {
                    let p = b[&t];
                    assert_eq!(a[p], t);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            930..=939 => {
                // iter
                let mut n = 0;
                for (ptr, t) in a.iter() {
                    assert_eq!(ptr, b[t]);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            940..=949 => {
                // advancer
                let mut i = 0;
                let rand_remove_i = if len == 0 { 0 } else { next_inx!(rng, len) };
                let rand_insert_i = if len == 0 { 0 } else { next_inx!(rng, len) };
                let mut adv = a.advancer();
                while let Some(p) = adv.advance(&a) {
                    assert_eq!(p, b[&a[p]]);

                    // remove and insert at random times
                    if i == rand_insert_i {
                        let t = new_t();
                        let ptr = a.insert(t);
                        b.insert(t, ptr);
                        list.push(t);
                    }
                    if i == rand_remove_i {
                        let t = list.swap_remove(rand_remove_i);
                        let ptr = b.remove(&t).unwrap();
                        assert_eq!(t, a.remove(ptr).unwrap());
                        generation += 1;
                    }
                    i += 1;
                }
                // depends on the invalidated elements witnessed
                assert!((i == len.saturating_sub(1)) || (i == len) || (i == (len + 1)));
            }
            950..=991 => {
                // iter_mut
                let mut n = 0;
                for (ptr, t) in a.iter_mut() {
                    assert_eq!(ptr, b[t]);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            992 => {
                // compress_and_shrink
                a.compress_and_shrink();
                assert_eq!(a.capacity(), a.len());
                generation += 1;
                // for this base test, manually recast `Ptr`s
                for (p, t) in a.iter() {
                    *b.get_mut(t).unwrap() = p;
                }
            }
            993 => {
                // compress_and_shrink_with
                let mut tmp = HashMap::new();
                let q_gen = PtrGen::generational_inc(a.generation()).0;
                a.compress_and_shrink_with(|p, t, q| {
                    assert_eq!(b[t], p);
                    assert_eq!(q_gen, q.generation());
                    tmp.insert(*t, q);
                });
                assert_eq!(tmp.len(), a.len());
                assert_eq!(a.capacity(), a.len());
                generation += 1;
                for (t, p) in tmp {
                    assert_eq!(t, a[p]);
                }
                // for this base test, manually recast `Ptr`s
                for (p, t) in a.iter() {
                    assert_eq!(q_gen, p.generation());
                    *b.get_mut(t).unwrap() = p;
                }
            }
            994 => {
                // clone_from variants. these are mainly tested in `multi_arena`, but we want
                // them here to test if `self.m.len()` and `self.m.capacity()` detachments cause
                // issues.
                match rng.next_u32() % 4 {
                    0 => {
                        a.clone_from(&a1);
                        generation = a1.generation().get();
                        b.clone_from(&b1);
                        list.clone_from(&list1);
                    }
                    1 => {
                        a.clone_from_with(&a1, |p, u| {
                            assert_eq!(b1[u], p);
                            *u
                        });
                        generation = a1.generation().get();
                        b.clone_from(&b1);
                        list.clone_from(&list1);
                    }
                    // `a1` and the like are set here, `a` will diverge again
                    2 => {
                        a1.clone_from(&a);
                        b1.clone_from(&b);
                        list1.clone_from(&list);
                    }
                    3 => {
                        a1.clone_from_with(&a, |p, u| {
                            assert_eq!(b[u], p);
                            *u
                        });
                        b1.clone_from(&b);
                        list1.clone_from(&list);
                    }
                    _ => unreachable!(),
                }
            }
            // The following reset the length so we can reexplore small cases.
            // Because of exponential probabilities, these need to be rare.
            994 => {
                // `PartialEq` false cases
                if len != 0 {
                    let mut remove = HashSet::new();
                    let num_rm = next_inx!(rng, len);
                    for _ in 0..num_rm {
                        remove.insert(list.swap_remove((rng.next_u32() as usize) % list.len()));
                    }
                    let a_clone = a.clone();
                    a.remove_by(|ptr, t| {
                        if remove.contains(t) {
                            remove.remove(t);
                            assert_eq!(ptr, b.remove(t).unwrap());
                            true
                        } else {
                            false
                        }
                    });
                    if num_rm > 0 {
                        assert_ne!(a_clone, a);
                        // make sure there are no assymetry related problems due to the
                        // implementation
                        assert_ne!(a, a_clone);
                    } else {
                        assert_eq!(a_clone, a);
                        assert_eq!(a, a_clone);
                    }
                    generation += 1;
                    assert!(remove.is_empty());
                }
            }
            995 => {
                // the `IntoIter` impl, and `PartialEq` true cases
                let a_clone = a.clone();
                assert_eq!(a_clone, a);
                // make sure there are no assymetry related problems due to the implementation
                assert_eq!(a, a_clone);
                for (ptr, t) in a_clone {
                    assert_eq!(b[&t], ptr);
                }
            }
            998 => {
                // drain
                let prev_cap = a.capacity();
                for (ptr, t) in a.drain() {
                    assert_eq!(b.remove(&t).unwrap(), ptr);
                }
                generation += 1;
                list.clear();
                assert_eq!(a.capacity(), prev_cap);
            }*/
            999 => {
                // clear
                b.clear();
                ensure_eq!(a.clear().is_overflow(), g.invalidate());
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
