use std::collections::{HashMap, HashSet};

use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use testcrate::P0;
use triple_arena::{ChainArena, Ptr};

macro_rules! next_inx {
    ($rng:ident, $len:ident) => {
        $rng.next_u32() as usize % $len
    };
}

#[test]
#[allow(clippy::type_complexity)]
fn fuzz_chain() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    // unique id for checking that the correct elements are returned
    let mut counter = 0u64;
    let mut new_t = || {
        counter += 1;
        counter
    };

    let mut list: Vec<u64> = vec![];

    let mut a: ChainArena<P0, u64> = ChainArena::new();
    let mut gen = 2;
    let mut b: HashMap<u64, (P0, (Option<u64>, Option<u64>))> = HashMap::new();

    let invalid = a.insert_new(u64::MAX);
    a.remove(invalid).unwrap();
    gen += 1;
    a.clear_and_shrink();
    gen += 1;
    let mut op_inx;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;
    let mut max_len = 0;

    for _ in 0..1_000_000 {
        assert_eq!(a.len(), list.len());
        assert_eq!(b.len(), a.len());
        assert_eq!(a.gen().get(), gen);
        assert_eq!(a.is_empty(), list.is_empty());
        let len = list.len();
        if let Err(e) = ChainArena::_check_invariants(&a) {
            panic!("{e}");
        }
        op_inx = rng.next_u32() % 1000;
        match op_inx {
            // testing all nontrivial functions on `ChainArena` not already tested by the regular
            // `Arena` tests
            0..=9 => {
                // insert_new
                let t = new_t();
                list.push(t);
                let p = a.insert_new(t);
                b.insert(t, (p, (None, None)));
            }
            10..=19 => {
                // insert_new_with
                let t = new_t();
                list.push(t);
                let mut tmp = P0::invalid();
                let p = a.insert_new_with(|p_create| {
                    tmp = p_create;
                    t
                });
                assert_eq!(p, tmp);
                b.insert(t, (p, (None, None)));
            }
            20..=29 => {
                // insert_new_cyclic
                let t = new_t();
                list.push(t);
                let p = a.insert_new_cyclic(t);
                b.insert(t, (p, (Some(t), Some(t))));
            }
            30..=39 => {
                // insert_new_cyclic_with
                let t = new_t();
                list.push(t);
                let mut tmp = P0::invalid();
                let p = a.insert_new_cyclic_with(|p_create| {
                    tmp = p_create;
                    t
                });
                assert_eq!(p, tmp);
                b.insert(t, (p, (Some(t), Some(t))));
            }
            40..=79 => {
                // insert
                let op = if len == 0 { 0 } else { rng.next_u32() % 5 };
                let t = new_t();
                list.push(t);
                match op {
                    0 => {
                        let p = a.insert((None, None), t).unwrap();
                        b.insert(t, (p, (None, None)));
                    }
                    1 => {
                        let t0 = list[next_inx!(rng, len)];
                        let p = a.insert((Some(b[&t0].0), None), t).unwrap();
                        if let Some(t1) = b[&t0].1 .1 {
                            b.get_mut(&t0).unwrap().1 .1 = Some(t);
                            b.get_mut(&t1).unwrap().1 .0 = Some(t);
                            b.insert(t, (p, (Some(t0), Some(t1))));
                        } else {
                            b.get_mut(&t0).unwrap().1 .1 = Some(t);
                            b.insert(t, (p, (Some(t0), None)));
                        }
                    }
                    2 => {
                        let t1 = list[next_inx!(rng, len)];
                        let p = a.insert((None, Some(b[&t1].0)), t).unwrap();
                        if let Some(t0) = b[&t1].1 .0 {
                            b.get_mut(&t0).unwrap().1 .1 = Some(t);
                            b.get_mut(&t1).unwrap().1 .0 = Some(t);
                            b.insert(t, (p, (Some(t0), Some(t1))));
                        } else {
                            b.get_mut(&t1).unwrap().1 .0 = Some(t);
                            b.insert(t, (p, (None, Some(t1))));
                        }
                    }
                    3 => {
                        let t0 = list[next_inx!(rng, len)];
                        let t1 = list[next_inx!(rng, len)];
                        if let Ok(p) = a.insert((Some(b[&t0].0), Some(b[&t1].0)), t) {
                            if let Some(t1) = b[&t0].1 .1 {
                                b.get_mut(&t0).unwrap().1 .1 = Some(t);
                                b.get_mut(&t1).unwrap().1 .0 = Some(t);
                                b.insert(t, (p, (Some(t0), Some(t1))));
                            } else {
                                b.get_mut(&t0).unwrap().1 .1 = Some(t);
                                b.insert(t, (p, (Some(t0), None)));
                            }
                        } else {
                            // check that the failure is expected
                            assert_ne!(b[&t0].1 .1, Some(t1));
                            assert_ne!(b[&t1].1 .0, Some(t0));
                            // undo
                            list.pop().unwrap();
                        }
                    }
                    4 => {
                        // test double sided insertion for single link cyclical chains
                        let t0 = list[next_inx!(rng, len)];
                        if let Ok(p) = a.insert((Some(b[&t0].0), Some(b[&t0].0)), t) {
                            if let Some(t1) = b[&t0].1 .1 {
                                b.get_mut(&t0).unwrap().1 .1 = Some(t);
                                b.get_mut(&t1).unwrap().1 .0 = Some(t);
                                b.insert(t, (p, (Some(t0), Some(t1))));
                            } else {
                                b.get_mut(&t0).unwrap().1 .1 = Some(t);
                                b.insert(t, (p, (Some(t0), None)));
                            }
                        } else {
                            // check that the failure is expected
                            assert_ne!(b[&t0].1 .1, Some(t0));
                            assert_ne!(b[&t0].1 .0, Some(t0));
                            // undo
                            list.pop().unwrap();
                        }
                    }
                    _ => unreachable!(),
                }
            }
            80..=99 => {
                // insert_with
                let op = if len == 0 { 0 } else { rng.next_u32() % 5 };
                let t = new_t();
                list.push(t);
                match op {
                    0 => {
                        let mut inner_p = None;
                        let p = a
                            .insert_with((None, None), |p| {
                                inner_p = Some(p);
                                t
                            })
                            .unwrap();
                        assert_eq!(inner_p.unwrap(), p);
                        b.insert(t, (p, (None, None)));
                    }
                    1 => {
                        let t0 = list[next_inx!(rng, len)];
                        let mut inner_p = None;
                        let p = a
                            .insert_with((Some(b[&t0].0), None), |p| {
                                inner_p = Some(p);
                                t
                            })
                            .unwrap();
                        assert_eq!(inner_p.unwrap(), p);
                        if let Some(t1) = b[&t0].1 .1 {
                            b.get_mut(&t0).unwrap().1 .1 = Some(t);
                            b.get_mut(&t1).unwrap().1 .0 = Some(t);
                            b.insert(t, (p, (Some(t0), Some(t1))));
                        } else {
                            b.get_mut(&t0).unwrap().1 .1 = Some(t);
                            b.insert(t, (p, (Some(t0), None)));
                        }
                    }
                    2 => {
                        let t1 = list[next_inx!(rng, len)];
                        let mut inner_p = None;
                        let p = a
                            .insert_with((None, Some(b[&t1].0)), |p| {
                                inner_p = Some(p);
                                t
                            })
                            .unwrap();
                        assert_eq!(inner_p.unwrap(), p);
                        if let Some(t0) = b[&t1].1 .0 {
                            b.get_mut(&t0).unwrap().1 .1 = Some(t);
                            b.get_mut(&t1).unwrap().1 .0 = Some(t);
                            b.insert(t, (p, (Some(t0), Some(t1))));
                        } else {
                            b.get_mut(&t1).unwrap().1 .0 = Some(t);
                            b.insert(t, (p, (None, Some(t1))));
                        }
                    }
                    3 => {
                        let t0 = list[next_inx!(rng, len)];
                        let t1 = list[next_inx!(rng, len)];
                        let mut inner_p = None;
                        if let Some(p) = a.insert_with((Some(b[&t0].0), Some(b[&t1].0)), |p| {
                            inner_p = Some(p);
                            t
                        }) {
                            assert_eq!(inner_p.unwrap(), p);
                            if let Some(t1) = b[&t0].1 .1 {
                                b.get_mut(&t0).unwrap().1 .1 = Some(t);
                                b.get_mut(&t1).unwrap().1 .0 = Some(t);
                                b.insert(t, (p, (Some(t0), Some(t1))));
                            } else {
                                b.get_mut(&t0).unwrap().1 .1 = Some(t);
                                b.insert(t, (p, (Some(t0), None)));
                            }
                        } else {
                            assert!(inner_p.is_none());
                            // check that the failure is expected
                            assert_ne!(b[&t0].1 .1, Some(t1));
                            assert_ne!(b[&t1].1 .0, Some(t0));
                            // undo
                            list.pop().unwrap();
                        }
                    }
                    4 => {
                        // test double sided insertion for single link cyclical chains
                        let t0 = list[next_inx!(rng, len)];
                        let mut inner_p = None;
                        if let Some(p) = a.insert_with((Some(b[&t0].0), Some(b[&t0].0)), |p| {
                            inner_p = Some(p);
                            t
                        }) {
                            assert_eq!(inner_p.unwrap(), p);
                            if let Some(t1) = b[&t0].1 .1 {
                                b.get_mut(&t0).unwrap().1 .1 = Some(t);
                                b.get_mut(&t1).unwrap().1 .0 = Some(t);
                                b.insert(t, (p, (Some(t0), Some(t1))));
                            } else {
                                b.get_mut(&t0).unwrap().1 .1 = Some(t);
                                b.insert(t, (p, (Some(t0), None)));
                            }
                        } else {
                            assert!(inner_p.is_none());
                            // check that the failure is expected
                            assert_ne!(b[&t0].1 .1, Some(t0));
                            assert_ne!(b[&t0].1 .0, Some(t0));
                            // undo
                            list.pop().unwrap();
                        }
                    }
                    _ => unreachable!(),
                }
            }
            100..=199 => {
                // insert_start and insert_end and insert
                if len != 0 {
                    let t_mid = list[next_inx!(rng, len)];
                    let t = new_t();
                    list.push(t);
                    match b[&t_mid].1 {
                        (None, None) => {
                            if (rng.next_u32() & 1) == 0 {
                                let p = a.insert_start(b[&t_mid].0, t).unwrap();
                                b.insert(t, (p, (None, Some(t_mid))));
                                b.get_mut(&t_mid).unwrap().1 .0 = Some(t);
                            } else {
                                let p = a.insert_end(b[&t_mid].0, t).unwrap();
                                b.insert(t, (p, (Some(t_mid), None)));
                                b.get_mut(&t_mid).unwrap().1 .1 = Some(t);
                            }
                        }
                        (None, Some(_)) => {
                            let p = a.insert_start(b[&t_mid].0, t).unwrap();
                            b.insert(t, (p, (None, Some(t_mid))));
                            b.get_mut(&t_mid).unwrap().1 .0 = Some(t);
                        }
                        (Some(_), None) => {
                            let p = a.insert_end(b[&t_mid].0, t).unwrap();
                            b.insert(t, (p, (Some(t_mid), None)));
                            b.get_mut(&t_mid).unwrap().1 .1 = Some(t);
                        }
                        (Some(_), Some(t1)) => {
                            // can't use `insert_end` or `insert_start`, use `insert` with both
                            // `Some`
                            let p = a.insert((Some(b[&t_mid].0), Some(b[&t1].0)), t).unwrap();
                            b.insert(t, (p, (Some(t_mid), Some(t1))));
                            b.get_mut(&t_mid).unwrap().1 .1 = Some(t);
                            b.get_mut(&t1).unwrap().1 .0 = Some(t);
                        }
                    }
                } else {
                    assert!(a.insert_start(invalid, u64::MAX).is_none());
                    assert!(a.insert_end(invalid, u64::MAX).is_none());
                }
            }
            200..=399 => {
                // remove
                if len != 0 {
                    let t = list.swap_remove(next_inx!(rng, len));
                    let p = b[&t].0;
                    match b[&t].1 {
                        (None, None) => (),
                        (None, Some(t1)) => {
                            b.get_mut(&t1).unwrap().1 .0 = None;
                        }
                        (Some(t0), None) => {
                            b.get_mut(&t0).unwrap().1 .1 = None;
                        }
                        (Some(t0), Some(t1)) => {
                            b.get_mut(&t0).unwrap().1 .1 = Some(t1);
                            b.get_mut(&t1).unwrap().1 .0 = Some(t0);
                        }
                    }
                    assert_eq!(a.remove(p).unwrap().t, t);
                    gen += 1;
                    b.remove(&t);
                } else {
                    assert!(a.remove(invalid).is_none());
                }
            }
            400..=499 => {
                // connect
                if len != 0 {
                    let t0 = list[next_inx!(rng, len)];
                    let t1 = list[next_inx!(rng, len)];
                    if b[&t0].1 .1.is_none() && b[&t1].1 .0.is_none() {
                        a.connect(b[&t0].0, b[&t1].0).unwrap();
                        b.get_mut(&t0).unwrap().1 .1 = Some(t1);
                        b.get_mut(&t1).unwrap().1 .0 = Some(t0);
                    } else if b[&t0].1 .0.is_none() && b[&t0].1 .1.is_none() {
                        // connecting for single link cyclical chain case instead
                        a.connect(b[&t0].0, b[&t0].0).unwrap();
                        b.get_mut(&t0).unwrap().1 .0 = Some(t0);
                        b.get_mut(&t0).unwrap().1 .1 = Some(t0);
                    }
                } else {
                    assert!(a.connect(invalid, invalid).is_none());
                }
            }
            500..=549 => {
                // break_prev
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    if a.break_prev(b[&t].0).is_some() {
                        let u = b.get_mut(&t).unwrap().1 .0.unwrap();
                        b.get_mut(&u).unwrap().1 .1 = None;
                        b.get_mut(&t).unwrap().1 .0 = None;
                    }
                } else {
                    assert!(a.break_prev(invalid).is_none());
                }
            }
            550..=599 => {
                // break_next
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    if a.break_next(b[&t].0).is_some() {
                        let d = b.get_mut(&t).unwrap().1 .1.unwrap();
                        b.get_mut(&d).unwrap().1 .0 = None;
                        b.get_mut(&t).unwrap().1 .1 = None;
                    }
                } else {
                    assert!(a.break_prev(invalid).is_none());
                }
            }
            600..=689 => {
                // exchange_next
                if len != 0 {
                    let t0 = list[next_inx!(rng, len)];
                    let t1 = list[next_inx!(rng, len)];
                    if a.exchange_next(b[&t0].0, b[&t1].0).is_some() {
                        let d0 = b.get_mut(&t0).unwrap().1 .1.unwrap();
                        let d1 = b.get_mut(&t1).unwrap().1 .1.unwrap();
                        b.get_mut(&t0).unwrap().1 .1 = Some(d1);
                        b.get_mut(&t1).unwrap().1 .1 = Some(d0);
                        b.get_mut(&d0).unwrap().1 .0 = Some(t1);
                        b.get_mut(&d1).unwrap().1 .0 = Some(t0);
                    } else {
                        assert!(b[&t0].1 .1.is_none() || b[&t1].1 .1.is_none());
                    }
                } else {
                    assert!(a.exchange_next(invalid, invalid).is_none());
                }
            }
            690..=699 => {
                // exchange_next with single nodes
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    if a.exchange_next(b[&t].0, b[&t].0).is_none() {
                        assert!(b[&t].1 .1.is_none());
                    }
                } else {
                    assert!(a.exchange_next(invalid, invalid).is_none());
                }
            }
            700..=749 => {
                // invalidate
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    let (ptr, interlink) = b.remove(&t).unwrap();
                    let new_ptr = a.invalidate(ptr).unwrap();
                    gen += 1;
                    // preserve interlink on node that was invalidated, the incident interlinks
                    // do not need to be updated because we are looking up based on the `t` value
                    // which is unchanged. This includes single link cyclic chains
                    b.insert(t, (new_ptr, interlink));
                    assert_eq!(t, a[new_ptr].t);
                } else {
                    assert!(a.invalidate(invalid).is_none());
                }
            }
            750..=799 => {
                // replace_and_keep_gen
                if len != 0 {
                    let t = list.swap_remove(next_inx!(rng, len));
                    let t_new = new_t();
                    list.push(t_new);
                    let interlink = b[&t].1;
                    // correct `t`-based interlinks, do this before other replacements so we don't
                    // have to special case cyclical chains
                    if let Some(interlink) = interlink.0 {
                        let tmp = b.get_mut(&interlink).unwrap();
                        if let Some(ref mut tmp) = tmp.1 .0 {
                            if *tmp == t {
                                *tmp = t_new;
                            }
                        }
                        if let Some(ref mut tmp) = tmp.1 .1 {
                            if *tmp == t {
                                *tmp = t_new;
                            }
                        }
                    }
                    if let Some(interlink) = interlink.1 {
                        let tmp = b.get_mut(&interlink).unwrap();
                        if let Some(ref mut tmp) = tmp.1 .0 {
                            if *tmp == t {
                                *tmp = t_new;
                            }
                        }
                        if let Some(ref mut tmp) = tmp.1 .1 {
                            if *tmp == t {
                                *tmp = t_new;
                            }
                        }
                    }
                    let (ptr, interlink) = b.remove(&t).unwrap();
                    let t_old = a.replace_and_keep_gen(ptr, t_new).unwrap();
                    assert_eq!(t, t_old);
                    b.insert(t_new, (ptr, interlink));
                } else {
                    assert_eq!(a.replace_and_keep_gen(invalid, u64::MAX), Err(u64::MAX));
                }
            }
            800..=849 => {
                // replace_and_update_gen
                if len != 0 {
                    let t = list.swap_remove(next_inx!(rng, len));
                    let t_new = new_t();
                    list.push(t_new);
                    let interlink = b[&t].1;
                    // correct `t`-based interlinks, do this before other replacements so we don't
                    // have to special case cyclical chains
                    if let Some(interlink) = interlink.0 {
                        let tmp = b.get_mut(&interlink).unwrap();
                        if let Some(ref mut tmp) = tmp.1 .0 {
                            if *tmp == t {
                                *tmp = t_new;
                            }
                        }
                        if let Some(ref mut tmp) = tmp.1 .1 {
                            if *tmp == t {
                                *tmp = t_new;
                            }
                        }
                    }
                    if let Some(interlink) = interlink.1 {
                        let tmp = b.get_mut(&interlink).unwrap();
                        if let Some(ref mut tmp) = tmp.1 .0 {
                            if *tmp == t {
                                *tmp = t_new;
                            }
                        }
                        if let Some(ref mut tmp) = tmp.1 .1 {
                            if *tmp == t {
                                *tmp = t_new;
                            }
                        }
                    }
                    let (ptr, interlink) = b.remove(&t).unwrap();
                    let (ptr_new, t_old) = a.replace_and_update_gen(ptr, t_new).unwrap();
                    gen += 1;
                    assert_eq!(t, t_old);
                    b.insert(t_new, (ptr_new, interlink));
                } else {
                    assert_eq!(a.replace_and_keep_gen(invalid, u64::MAX), Err(u64::MAX));
                }
            }
            850..=899 => {
                // swap
                if len != 0 {
                    let t0 = list[next_inx!(rng, len)];
                    let t1 = list[next_inx!(rng, len)];
                    if t0 == t1 {
                        let t = b[&t0].0;
                        // swapping a node with itself
                        a.swap(t, t).unwrap();
                    } else {
                        let tmp0 = b[&t0];
                        let tmp1 = b[&t1];
                        a.swap(tmp0.0, tmp1.0).unwrap();
                        // because we are using reverse lookups other nodes need to be rerouted
                        if let Some(prev) = tmp0.1 .0 {
                            b.get_mut(&prev).unwrap().1 .1 = Some(t1);
                        }
                        if let Some(next) = tmp0.1 .1 {
                            b.get_mut(&next).unwrap().1 .0 = Some(t1);
                        }
                        if let Some(prev) = tmp1.1 .0 {
                            b.get_mut(&prev).unwrap().1 .1 = Some(t0);
                        }
                        if let Some(next) = tmp1.1 .1 {
                            b.get_mut(&next).unwrap().1 .0 = Some(t0);
                        }
                        let tmp0 = b[&t0];
                        let tmp1 = b[&t1];
                        *b.get_mut(&t0).unwrap() = tmp1;
                        *b.get_mut(&t1).unwrap() = tmp0;
                    }
                } else {
                    assert!(a.swap(invalid, invalid).is_none());
                }
            }
            900..=979 => {
                // are_neighbors
                if len != 0 {
                    let t0 = list[next_inx!(rng, len)];
                    let t1 = list[next_inx!(rng, len)];
                    if a.are_neighbors(b[&t0].0, b[&t1].0) {
                        assert_eq!(b[&t0].1 .1, Some(t1));
                        assert_eq!(b[&t1].1 .0, Some(t0));
                    } else {
                        assert_ne!(b[&t0].1 .1, Some(t1));
                        assert_ne!(b[&t1].1 .0, Some(t0));
                    }
                } else {
                    assert!(!a.are_neighbors(invalid, invalid));
                }
            }
            980..=984 => {
                // next_chain_ptr
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    let mut t_to_explore = HashSet::new();
                    let mut iters = 0;

                    let init = b[&t].0;
                    let mut p = init;
                    let mut switch = false;
                    let mut stop = !a.contains(init);
                    loop {
                        if stop {
                            break
                        }
                        t_to_explore.insert(a[p].t);
                        // make sure we aren't double counting and the hash set is just dropping
                        iters += 1;
                        a.next_chain_ptr(init, &mut p, &mut switch, &mut stop);
                    }
                    assert_eq!(t_to_explore.len(), iters);

                    let init = b[&t];
                    let mut tmp = init.1 .1;
                    let mut cyclical = false;
                    t_to_explore.remove(&t);
                    while let Some(next) = tmp {
                        if next == t {
                            cyclical = true;
                            break
                        }
                        assert!(t_to_explore.remove(&next));
                        tmp = b[&next].1 .1;
                    }
                    if !cyclical {
                        let mut tmp = init.1 .0;
                        while let Some(prev) = tmp {
                            assert!(t_to_explore.remove(&prev));
                            tmp = b[&prev].1 .0;
                        }
                    }
                    assert!(t_to_explore.is_empty());
                } else {
                    let mut stop = false;
                    a.next_chain_ptr(invalid, &mut P0::invalid(), &mut false, &mut stop);
                    assert!(stop);
                }
            }
            985..=989 => {
                // iter_chain
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    let init = b[&t].0;
                    let mut iter = a.iter_chain(init);
                    let mut p = init;
                    let mut switch = false;
                    let mut stop = !a.contains(init);
                    loop {
                        if stop {
                            break
                        }
                        assert_eq!(iter.next().unwrap(), (p, &a[p]));
                        a.next_chain_ptr(init, &mut p, &mut switch, &mut stop);
                    }
                } else {
                    let mut iter = a.iter_chain(invalid);
                    assert!(iter.next().is_none());
                }
            }
            990..=997 => {
                // remove_chain
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    let mut t_to_remove = HashSet::new();
                    t_to_remove.insert(t);
                    let claim_num_removed = a.remove_chain(b[&t].0).unwrap();
                    gen += 1;
                    let init = b.remove(&t).unwrap();
                    let mut num_removed = 1;
                    let mut tmp = init.1 .1;
                    let mut cyclical = false;
                    while let Some(next) = tmp {
                        if next == t {
                            cyclical = true;
                            break
                        }
                        t_to_remove.insert(next);
                        tmp = b.remove(&next).unwrap().1 .1;
                        num_removed += 1;
                    }
                    if !cyclical {
                        let mut tmp = init.1 .0;
                        while let Some(prev) = tmp {
                            t_to_remove.insert(prev);
                            tmp = b.remove(&prev).unwrap().1 .0;
                            num_removed += 1;
                        }
                    }
                    assert_eq!(claim_num_removed, num_removed);
                    let mut i = 0;
                    while i < list.len() {
                        if t_to_remove.contains(&list[i]) {
                            list.swap_remove(i);
                        } else {
                            i += 1;
                        }
                    }
                } else {
                    assert!(a.remove_chain(invalid).is_none());
                }
            }
            998 => {
                // clear
                a.clear();
                b.clear();
                gen += 1;
                list.clear();
            }
            999 => {
                // clear_and_shrink
                a.clear_and_shrink();
                b.clear();
                gen += 1;
                list.clear();
                iters999 += 1;
            }
            _ => unreachable!(),
        }
        max_len = std::cmp::max(max_len, a.len());
    }
    assert_eq!((max_len, iters999, a.gen().get()), (40, 1040, 214030));
}
