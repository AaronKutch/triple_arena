use std::collections::HashMap;

use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use triple_arena::{ptr_struct, ChainArena};

macro_rules! next_inx {
    ($rng:ident, $len:ident) => {
        $rng.next_u32() as usize % $len
    };
}

ptr_struct!(P0);

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
            0..=19 => {
                // insert_new
                let t = new_t();
                list.push(t);
                let p = a.insert_new(t);
                b.insert(t, (p, (None, None)));
            }
            20..=39 => {
                // insert_new_cyclic
                let t = new_t();
                list.push(t);
                let p = a.insert_new_cyclic(t);
                b.insert(t, (p, (Some(t), Some(t))));
            }
            40..=99 => {
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
            700..=849 => {
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
            850..=899 => {
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
            900..=997 => {
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
            998 => {
                // clear
                a.clear();
                gen += 1;
                list.clear();
            }
            999 => {
                // clear_and_shrink
                a.clear_and_shrink();
                gen += 1;
                list.clear();
                iters999 += 1;
            }
            _ => unreachable!(),
        }
        max_len = std::cmp::max(max_len, a.len());
    }
    assert_eq!((max_len, iters999, a.gen().get()), (57, 1050, 265090));
}
