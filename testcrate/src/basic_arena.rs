use std::slice::GetDisjointMutError;

use stacked_errors::{StackableErr, StackedError, bail, ensure, ensure_eq};
use star_rng::StarRng;
use triple_arena::{
    traits::{ArenaTrait, Ptr, SingularGenerationArena},
    utils::{AllocError, PtrGen},
};

use crate::{
    P0, TestGen,
    cdgen::{Cd, CdGen, CdKey},
};

#[derive(Clone, Copy)]
pub struct Stats {
    pub limit: usize,
    pub n: usize,
    pub iters999: Option<usize>,
}

/// Use the [LIMIT] for fixed length types and as the limit for settable limit
/// types, ignore otherwise
pub fn fuzz<P: Ptr>(
    stats: Stats,
    cd_gen: &mut CdGen<()>,
    mut a: impl ArenaTrait<P, Cd<()>> + SingularGenerationArena<P>,
) -> Result<(), StackedError> {
    ensure!(cd_gen.is_empty());
    let mut rng = StarRng::new(0);

    // reference
    let mut b: Vec<CdKey> = vec![];
    let mut g = TestGen::<P>(PtrGen::two());

    // for temporary debug changes
    #[allow(unused)]
    let mut op_inx = usize::MAX;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;

    for _ in 0..stats.n {
        let len = b.len();
        ensure!(cd_gen.len() <= len);
        ensure_eq!(a.len(), len);
        ensure_eq!(a.is_empty(), b.is_empty());
        ensure_eq!(a.singular_generation(), g.0);
        ensure!(len <= a.capacity());
        let limited = a.max_capacity().is_some();
        if let Some(limit) = a.max_capacity() {
            // required for caller
            ensure_eq!(limit, stats.limit);

            ensure!(a.capacity() <= limit);
        }
        op_inx = rng.index(1000).unwrap();
        match op_inx {
            /*0..=50 => {
                // try_insert
                if a.len() < a.capacity() {
                    let t = new_t();
                    let ptr = a.try_insert(t).unwrap();
                    b.insert(t, ptr);
                    list.push(t);
                } else {
                    let t = new_t();
                    assert_eq!(a.try_insert(t), Err(t));
                }
            }
            50..=99 => {
                // try_insert_with
                if a.len() < a.capacity() {
                    let t = new_t();
                    let mut create_ptr = None;
                    let ptr = if let Ok(ptr) = a.try_insert_with(|p| {
                        create_ptr = Some(p);
                        t
                    }) {
                        ptr
                    } else {
                        panic!()
                    };
                    assert_eq!(ptr, create_ptr.unwrap());
                    b.insert(t, ptr);
                    list.push(t);
                } else {
                    let create = |_p: P0| unreachable!();
                    assert!(a.try_insert_with(create).is_err());
                }
            }
            100..=149 => {
                // insert
                let t = new_t();
                let ptr = a.insert(t);
                b.insert(t, ptr);
                list.push(t);
            }
            150..=199 => {
                // insert_with
                let t = new_t();
                let mut create_ptr = None;
                let ptr = a.insert_with(|p| {
                    create_ptr = Some(p);
                    t
                });
                assert_eq!(ptr, create_ptr.unwrap());
                b.insert(t, ptr);
                list.push(t);
            }
            200..=399 => {
                // remove
                if len != 0 {
                    let t = list.swap_remove(next_inx!(rng, len));
                    let ptr = b.remove(&t).unwrap();
                    assert_eq!(t, a.remove(ptr).unwrap());
                    generation += 1;
                } else {
                    assert!(a.remove(invalid).is_none());
                }
            }
            400..=449 => {
                // invalidate
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    let ptr = b.remove(&t).unwrap();
                    let new_ptr = a.invalidate(ptr).unwrap();
                    generation += 1;
                    b.insert(t, new_ptr);
                    assert_eq!(t, a[new_ptr]);
                } else {
                    assert!(a.invalidate(invalid).is_none());
                }
            }
            450..=499 => {}
            500..=549 => {}
            550..=599 => {}*/
            /*600..=799 => {
                // contains
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    assert!(a.contains(b[&t]));
                } else {
                    assert!(!a.contains(invalid));
                }
            }
            800..=839 => {
                // get and index
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    assert_eq!(t, *a.get(b[&t]).unwrap());
                    assert_eq!(t, a[b[&t]]);
                } else {
                    assert!(a.get(invalid).is_none())
                }
            }
            840..=849 => {
                // get2_mut
                if len != 0 {
                    let t0 = list[next_inx!(rng, len)];
                    let t1 = list[next_inx!(rng, len)];
                    if t0 != t1 {
                        let tmp = a.get2_mut(b[&t0], b[&t1]).unwrap();
                        assert_eq!((*tmp.0, *tmp.1), (t0, t1));
                    } else {
                        assert!(a.get2_mut(b[&t0], invalid).is_none());
                        assert!(a.get2_mut(invalid, b[&t0]).is_none());
                        assert!(a.get2_mut(b[&t0], b[&t0]).is_none());
                    }
                } else {
                    assert!(a.get2_mut(invalid, invalid).is_none())
                }
            }
            850..=899 => {
                // get_mut and index_mut
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    assert_eq!(t, *a.get_mut(b[&t]).unwrap());
                    let tmp: &mut u64 = &mut a[b[&t]];
                    assert_eq!(t, *tmp);
                } else {
                    assert!(a.get_mut(invalid).is_none())
                }
            }*/
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
            0..999 => {} //FIXME
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
