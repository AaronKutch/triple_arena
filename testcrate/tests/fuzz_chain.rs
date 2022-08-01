use std::{collections::HashMap, num::NonZeroU64};

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
            0..=49 => {
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
            50..=99 => {
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
            100..=997 => (),
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
    assert_eq!(max_len, 42);
    assert_eq!(iters999, 1043);
    assert_eq!(a.gen(), NonZeroU64::new(42812).unwrap());
}
