use std::{cmp::max, collections::HashMap};

use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use triple_arena::{ptr_struct, SurjectArena};

macro_rules! next_inx {
    ($rng:ident, $len:ident) => {
        $rng.next_u32() as usize % $len
    };
}

ptr_struct!(P0);

#[test]
fn fuzz_surject() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    // unique id for checking that the correct elements are returned
    let mut counter = 0u64;
    let mut new_t = || {
        counter += 1;
        counter
    };

    let mut list: Vec<u64> = vec![];

    let mut a: SurjectArena<P0, u64> = SurjectArena::new();
    let mut gen = 2;
    let mut b: HashMap<u64, Vec<P0>> = HashMap::new();

    let invalid = a.insert_val(u64::MAX);
    a.remove_key(invalid).unwrap();
    gen += 1;
    a.clear_and_shrink();
    gen += 1;
    let mut op_inx = u32::MAX;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;
    let mut max_key_len = 0;
    let mut max_val_len = 0;

    for _ in 0..1_000_000 {
        assert_eq!(a.len_vals(), list.len());
        assert_eq!(a.len_vals(), b.len());
        let len = list.len();
        let mut len_keys = 0;
        for set in b.values() {
            assert!(!set.is_empty());
            let set_len = set.len();
            assert_eq!(
                set.len(),
                a.len_key_set(set[next_inx!(rng, set_len)]).unwrap().get()
            );
            len_keys += set_len;
        }
        assert_eq!(a.len_keys(), len_keys);
        if a.gen().get() != gen {
            dbg!(a.gen().get(), gen, op_inx);
            panic!();
        }
        assert_eq!(a.gen().get(), gen);
        assert_eq!(a.is_empty(), list.is_empty());
        if let Err(e) = SurjectArena::_check_invariants(&a) {
            dbg!(op_inx);
            panic!("{e}");
        }
        op_inx = rng.next_u32() % 1000;
        match op_inx {
            0..=24 => {
                // insert_val
                let t = new_t();
                let p = a.insert_val(t);
                list.push(t);
                b.insert(t, vec![p]);
            }
            25..=99 => {
                // insert_key
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    let set = &b[&t];
                    let set_len = set.len();
                    let p = set[next_inx!(rng, set_len)];
                    let p_new = a.insert_key(p).unwrap();
                    b.get_mut(&t).unwrap().push(p_new);
                } else {
                    assert!(a.insert_key(invalid).is_none());
                }
            }
            100..=104 => {
                // remove_val
                if len != 0 {
                    let t = list.swap_remove(next_inx!(rng, len));
                    let set = b.remove(&t).unwrap();
                    let set_len = set.len();
                    a.remove_val(set[next_inx!(rng, set_len)]);
                    gen += 1;
                } else {
                    assert!(a.remove_val(invalid).is_none());
                }
            }
            105..=199 => {
                // remove_key
                if len != 0 {
                    let i = next_inx!(rng, len);
                    let t = list[i];
                    let set = &b[&t];
                    let set_len = set.len();
                    let i_set = next_inx!(rng, set_len);
                    let res = a.remove_key(set[i_set]);
                    gen += 1;
                    if set_len == 1 {
                        list.swap_remove(i);
                        b.remove(&t).unwrap();
                        assert_eq!(res, Some(Some(t)));
                    } else {
                        b.get_mut(&t).unwrap().swap_remove(i_set);
                        assert_eq!(res, Some(None));
                    }
                } else {
                    assert!(a.remove_val(invalid).is_none());
                }
            }
            200..=249 => {
                // contains
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    let set = &b[&t];
                    let set_len = set.len();
                    let p = set[next_inx!(rng, set_len)];
                    assert!(a.contains(p));
                } else {
                    assert!(!a.contains(invalid));
                }
            }
            250..=299 => {
                // in_same_set
                if len != 0 {
                    let t0 = list[next_inx!(rng, len)];
                    let t1 = list[next_inx!(rng, len)];
                    let set0 = &b[&t0];
                    let set_len0 = set0.len();
                    let set1 = &b[&t1];
                    let set_len1 = set1.len();
                    let p0 = set0[next_inx!(rng, set_len0)];
                    let p1 = set1[next_inx!(rng, set_len1)];
                    if t0 == t1 {
                        assert!(a.in_same_set(p0, p1).unwrap());
                    } else {
                        assert!(!a.in_same_set(p0, p1).unwrap());
                    }
                } else {
                    assert!(a.in_same_set(invalid, invalid).is_none());
                }
            }
            300..=349 => {
                // get
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    let set = &b[&t];
                    let set_len = set.len();
                    let p = set[next_inx!(rng, set_len)];
                    assert_eq!(*a.get(p).unwrap(), t);
                } else {
                    assert!(a.get(invalid).is_none());
                }
            }
            350..=399 => {
                // get_mut
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    let set = &b[&t];
                    let set_len = set.len();
                    let p = set[next_inx!(rng, set_len)];
                    assert_eq!(*a.get_mut(p).unwrap(), t);
                } else {
                    assert!(a.get_mut(invalid).is_none());
                }
            }
            400..=449 => {
                // get2_mut
                if len != 0 {
                    let t0 = list[next_inx!(rng, len)];
                    let t1 = list[next_inx!(rng, len)];
                    let set0 = &b[&t0];
                    let set_len0 = set0.len();
                    let set1 = &b[&t1];
                    let set_len1 = set1.len();
                    let p0 = set0[next_inx!(rng, set_len0)];
                    let p1 = set1[next_inx!(rng, set_len1)];
                    if t0 == t1 {
                        assert!(a.get2_mut(p0, p1).is_none());
                    } else {
                        let tmp = a.get2_mut(p0, p1).unwrap();
                        assert_eq!(*tmp.0, t0);
                        assert_eq!(*tmp.1, t1);
                    }
                } else {
                    assert!(a.get2_mut(invalid, invalid).is_none());
                }
            }
            450..=499 => {
                // union
                if len != 0 {
                    let i0 = next_inx!(rng, len);
                    let i1 = next_inx!(rng, len);
                    let t0 = list[i0];
                    let t1 = list[i1];
                    let set0 = &b[&t0];
                    let set_len0 = set0.len();
                    let set1 = &b[&t1];
                    let set_len1 = set1.len();
                    let p0 = set0[next_inx!(rng, set_len0)];
                    let p1 = set1[next_inx!(rng, set_len1)];
                    if t0 == t1 {
                        assert!(a.union(p0, p1).is_none());
                    } else {
                        let res = a.union(p0, p1).unwrap();
                        if set_len0 < set_len1 {
                            assert_eq!(res.0, t0);
                            assert_eq!(res.1, p1);
                            list.swap_remove(i0);
                            let mut other = set0.clone();
                            b.remove(&t0).unwrap();
                            b.get_mut(&t1).unwrap().append(&mut other);
                        } else {
                            assert_eq!(res.0, t1);
                            assert_eq!(res.1, p0);
                            list.swap_remove(i1);
                            let mut other = set1.clone();
                            b.remove(&t1).unwrap();
                            b.get_mut(&t0).unwrap().append(&mut other);
                        }
                    }
                } else {
                    assert!(a.union(invalid, invalid).is_none());
                }
            }
            // invalidate_key
            // swap

            // TODO insert_val_with, also insert_new/cyclic_with for chain arena
            300..=997 => {
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    let set = &b[&t];
                    let set_len = set.len();
                    let p = set[next_inx!(rng, set_len)];
                    assert_eq!(*a.get(p).unwrap(), t);
                } else {
                    assert!(a.get(invalid).is_none());
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
        max_key_len = max(max_key_len, a.len_keys());
        max_val_len = max(max_val_len, a.len_vals());
    }
    assert_eq!(
        (max_key_len, max_val_len, iters999, a.gen().get()),
        (0, 0, 0, 0)
    );
}
