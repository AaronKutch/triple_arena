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
    let mut b: HashMap<u64, (P0, (Option<u64>, Option<u64>))> = HashMap::new();

    let invalid = a.insert_new(u64::MAX);
    a.remove(invalid);
    let mut op_inx;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;
    let mut max_len = 0;

    for _ in 0..1_000_000 {
        assert_eq!(a.len(), list.len());
        assert_eq!(a.is_empty(), list.is_empty());
        let len = list.len();
        ChainArena::_check_invariants(&a).unwrap();
        op_inx = rng.next_u32() % 1000;
        match op_inx {
            // testing all nontrivial functions on `ChainArena` not already tested by the regular
            // `Arena` tests
            /*let mut tmp = vec![];
            for (t, entry) in &b {
                tmp.push((t, entry));
            }
            for (t, entry) in tmp {
                if let Some(x) = entry.1.0 {
                    assert_eq!(b[&x].1.1, Some(*t));
                }
                if let Some(x) = entry.1.1 {
                    assert_eq!(b[&x].1.0, Some(*t));
                }
            }*/
            0..=19 => {
                let t = new_t();
                list.push(t);
                let p = a.insert_new(t);
                b.insert(t, (p, (None, None)));
            }
            20..=99 => {
                // insert, insert_new_cyclic
                let op = if len == 0 { 0 } else { rng.next_u32() % 4 };
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
                    // has `insert_new_cyclic` as a backup
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
                            if let Some(next) = b[&t0].1 .1 {
                                assert_ne!(next, t1);
                            }
                            let p = a.insert_new_cyclic(t);
                            b.insert(t, (p, (Some(t), Some(t))));
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
                    b.remove(&t);
                } else {
                    assert!(a.remove(invalid).is_none());
                }
            }
            400..=849 => (),
            850..=899 => {
                if len != 0 {
                    let t0 = list[next_inx!(rng, len)];
                    let t1 = list[next_inx!(rng, len)];
                    if t0 == t1 {
                        let t = b[&t0].0;
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
                        assert_eq!(b[&t0].1.1, Some(t1));
                        assert_eq!(b[&t1].1.0, Some(t0));
                    }
                } else {
                    assert!(!a.are_neighbors(invalid, invalid));
                }
            },
            998 => {
                // clear
                a.clear();
                list.clear();
            }
            999 => {
                // clear_and_shrink
                a.clear_and_shrink();
                list.clear();
                iters999 += 1;
            }
            _ => unreachable!(),
        }
        max_len = std::cmp::max(max_len, a.len());
    }
    assert_eq!((max_len, iters999, a.gen().get()), (120, 1051, 166444));
}
