use std::{
    cmp::max,
    collections::{HashMap, HashSet},
    hint::black_box,
};

use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use testcrate::P0;
use triple_arena::{utils::PtrGen, Advancer, Ptr, SurjectArena};

const N: usize = if cfg!(miri) { 1000 } else { 1_000_000 };

const STATS: (usize, usize, u64, u128) = if cfg!(miri) {
    (8, 3, 0, 71)
} else {
    (41, 8, 1027, 79005)
};

macro_rules! next_inx {
    ($rng:ident, $len:ident) => {
        $rng.next_u32() as usize % $len
    };
}

#[test]
fn fuzz_surject() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    // avoid getting mixups
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Key {
        pub k: u64,
    }
    impl Key {
        const MAX: Key = Key { k: u64::MAX };
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Val {
        pub v: u64,
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Pair {
        pub p: P0,
        pub k: Key,
    }

    // unique id for checking that the correct elements are returned
    let mut counter_k = 0u64;
    let mut new_k = || {
        counter_k += 1;
        Key { k: counter_k }
    };
    let mut counter_v = 0u64;
    let mut new_v = || {
        counter_v += 1;
        Val { v: counter_v }
    };

    let mut list: Vec<Val> = vec![];

    let mut a: SurjectArena<P0, Key, Val> = SurjectArena::new();
    let mut gen = 2;
    let mut b: HashMap<Val, Vec<Pair>> = HashMap::new();

    let invalid = a.insert(Key::MAX, Val { v: u64::MAX });
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

    for _ in 0..N {
        assert_eq!(a.len_vals(), list.len());
        assert_eq!(a.len_vals(), b.len());
        let len = list.len();
        if a.gen().get() != gen {
            dbg!(a.gen().get(), gen, op_inx);
            panic!();
        }
        assert_eq!(a.gen().get(), gen);
        assert_eq!(a.is_empty(), list.is_empty());
        if !cfg!(miri) {
            let mut len_keys = 0;
            for set in b.values() {
                assert!(!set.is_empty());
                let set_len = set.len();
                assert_eq!(
                    set.len(),
                    a.len_key_set(set[next_inx!(rng, set_len)].p).unwrap().get()
                );
                len_keys += set_len;
            }
            assert_eq!(a.len_keys(), len_keys);
            if let Err(e) = SurjectArena::_check_invariants(&a) {
                dbg!(op_inx);
                panic!("{e}");
            }
        }
        op_inx = rng.next_u32() % 1000;
        match op_inx {
            0..=19 => {
                // insert
                let k = new_k();
                let v = new_v();
                let p = a.insert(k, v);
                list.push(v);
                b.insert(v, vec![Pair { p, k }]);
            }
            20..=24 => {
                // insert_with
                let k = new_k();
                let v = new_v();
                let mut outer = P0::invalid();
                let p = a.insert_with(|p_create| {
                    outer = p_create;
                    (k, v)
                });
                assert_eq!(p, outer);
                list.push(v);
                b.insert(v, vec![Pair { p, k }]);
            }
            25..=59 => {
                // insert_key
                if len != 0 {
                    let k = new_k();
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let Pair { p, .. } = set[next_inx!(rng, set_len)];
                    let p_new = a.insert_key(p, k).unwrap();
                    b.get_mut(&v).unwrap().push(Pair { p: p_new, k });
                } else {
                    assert_eq!(a.insert_key(invalid, Key::MAX), Err(Key::MAX));
                }
            }
            60..=99 => {
                // insert_key_with
                if len != 0 {
                    let k = new_k();
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let Pair { p, .. } = set[next_inx!(rng, set_len)];
                    let mut created_k = None;
                    let p_new = a
                        .insert_key_with(p, |p| {
                            created_k = Some(p);
                            k
                        })
                        .unwrap();
                    assert_eq!(created_k.unwrap(), p_new);
                    b.get_mut(&v).unwrap().push(Pair { p: p_new, k });
                } else {
                    assert_eq!(a.insert_key(invalid, Key::MAX), Err(Key::MAX));
                }
            }
            100..=104 => {
                // remove
                if len != 0 {
                    let v = list.swap_remove(next_inx!(rng, len));
                    let set = b.remove(&v).unwrap();
                    let set_len = set.len();
                    let removed = a.remove(set[next_inx!(rng, set_len)].p).unwrap();
                    assert_eq!(removed, v);
                    gen += 1;
                } else {
                    assert!(a.remove(invalid).is_none());
                }
            }
            105..=199 => {
                // remove_key
                if len != 0 {
                    let i = next_inx!(rng, len);
                    let v = list[i];
                    let set = &b[&v];
                    let set_len = set.len();
                    let i_set = next_inx!(rng, set_len);
                    let pair = set[i_set];
                    let res = a.remove_key(pair.p);
                    gen += 1;
                    if set_len == 1 {
                        list.swap_remove(i);
                        b.remove(&v).unwrap();
                        assert_eq!(res, Some((pair.k, Some(v))));
                    } else {
                        b.get_mut(&v).unwrap().swap_remove(i_set);
                        assert_eq!(res, Some((pair.k, None)));
                    }
                } else {
                    assert!(a.remove(invalid).is_none());
                }
            }
            200..=249 => {
                // contains
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    assert!(a.contains(pair.p));
                } else {
                    assert!(!a.contains(invalid));
                }
            }
            250..=299 => {
                // in_same_set
                if len != 0 {
                    let v0 = list[next_inx!(rng, len)];
                    let v1 = list[next_inx!(rng, len)];
                    let set0 = &b[&v0];
                    let set_len0 = set0.len();
                    let set1 = &b[&v1];
                    let set_len1 = set1.len();
                    let pair0 = set0[next_inx!(rng, set_len0)];
                    let pair1 = set1[next_inx!(rng, set_len1)];
                    if v0 == v1 {
                        assert!(a.in_same_set(pair0.p, pair1.p).unwrap());
                    } else {
                        assert!(!a.in_same_set(pair0.p, pair1.p).unwrap());
                    }
                } else {
                    assert!(a.in_same_set(invalid, invalid).is_none());
                }
            }
            300..=329 => {
                // get
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    let tmp = a.get(pair.p).unwrap();
                    assert_eq!((*tmp.0, *tmp.1), (pair.k, v));
                } else {
                    assert!(a.get(invalid).is_none());
                }
            }
            330..=339 => {
                // get_key
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    assert_eq!(*a.get_key(pair.p).unwrap(), pair.k);
                } else {
                    assert!(a.get_key(invalid).is_none());
                }
            }
            340..=349 => {
                // get_val
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    assert_eq!(*a.get_val(pair.p).unwrap(), v);
                } else {
                    assert!(a.get_val(invalid).is_none());
                }
            }
            350..=379 => {
                // get_mut
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    let tmp = a.get_mut(pair.p).unwrap();
                    assert_eq!((*tmp.0, *tmp.1), (pair.k, v));
                } else {
                    assert!(a.get_mut(invalid).is_none());
                }
            }
            380..=389 => {
                // get_key_mut
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    assert_eq!(*a.get_key_mut(pair.p).unwrap(), pair.k);
                } else {
                    assert!(a.get_key_mut(invalid).is_none());
                }
            }
            390..=399 => {
                // get_val_mut
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    assert_eq!(*a.get_val_mut(pair.p).unwrap(), v);
                } else {
                    assert!(a.get_val_mut(invalid).is_none());
                }
            }
            400..=429 => {
                // get2_mut
                if len != 0 {
                    let v0 = list[next_inx!(rng, len)];
                    let v1 = list[next_inx!(rng, len)];
                    let set0 = &b[&v0];
                    let set_len0 = set0.len();
                    let set1 = &b[&v1];
                    let set_len1 = set1.len();
                    let pair0 = set0[next_inx!(rng, set_len0)];
                    let pair1 = set1[next_inx!(rng, set_len1)];
                    if v0 == v1 {
                        assert!(a.get2_mut(pair0.p, pair1.p).is_none());
                    } else {
                        let tmp = a.get2_mut(pair0.p, pair1.p).unwrap();
                        assert_eq!(*tmp.0 .0, pair0.k);
                        assert_eq!(*tmp.1 .0, pair1.k);
                        assert_eq!(*tmp.0 .1, v0);
                        assert_eq!(*tmp.1 .1, v1);
                    }
                } else {
                    assert!(a.get2_mut(invalid, invalid).is_none());
                }
            }
            430..=439 => {
                // get2_key_mut
                if len != 0 {
                    let v0 = list[next_inx!(rng, len)];
                    let v1 = list[next_inx!(rng, len)];
                    let set0 = &b[&v0];
                    let set_len0 = set0.len();
                    let set1 = &b[&v1];
                    let set_len1 = set1.len();
                    let pair0 = set0[next_inx!(rng, set_len0)];
                    let pair1 = set1[next_inx!(rng, set_len1)];
                    if pair0.k == pair1.k {
                        assert!(a.get2_key_mut(pair0.p, pair1.p).is_none());
                    } else {
                        let tmp = a.get2_key_mut(pair0.p, pair1.p).unwrap();
                        assert_eq!(*tmp.0, pair0.k);
                        assert_eq!(*tmp.1, pair1.k);
                    }
                } else {
                    assert!(a.get2_key_mut(invalid, invalid).is_none());
                }
            }
            440..=445 => {
                // get2_val_mut
                if len != 0 {
                    let v0 = list[next_inx!(rng, len)];
                    let v1 = list[next_inx!(rng, len)];
                    let set0 = &b[&v0];
                    let set_len0 = set0.len();
                    let set1 = &b[&v1];
                    let set_len1 = set1.len();
                    let pair0 = set0[next_inx!(rng, set_len0)];
                    let pair1 = set1[next_inx!(rng, set_len1)];
                    if v0 == v1 {
                        assert!(a.get2_val_mut(pair0.p, pair1.p).is_none());
                    } else {
                        let tmp = a.get2_val_mut(pair0.p, pair1.p).unwrap();
                        assert_eq!(*tmp.0, v0);
                        assert_eq!(*tmp.1, v1);
                    }
                } else {
                    assert!(a.get2_val_mut(invalid, invalid).is_none());
                }
            }
            446..=449 => {
                // get_link_no_gen
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    let (_, link) = a.get_link_no_gen(pair.p.inx()).unwrap();
                    assert_eq!(*link.t, pair.k);
                } else {
                    assert!(a.get_link_no_gen(P0::invalid().inx()).is_none());
                }
            }
            450..=499 => {
                // union
                if len != 0 {
                    let i0 = next_inx!(rng, len);
                    let i1 = next_inx!(rng, len);
                    let v0 = list[i0];
                    let v1 = list[i1];
                    let set0 = &b[&v0];
                    let set_len0 = set0.len();
                    let set1 = &b[&v1];
                    let set_len1 = set1.len();
                    let pair0 = set0[next_inx!(rng, set_len0)];
                    let pair1 = set1[next_inx!(rng, set_len1)];
                    if v0 == v1 {
                        assert!(a.union(pair0.p, pair1.p).is_none());
                    } else {
                        let res = a.union(pair0.p, pair1.p).unwrap();
                        if set_len0 < set_len1 {
                            assert_eq!(res.0, v0);
                            assert_eq!(res.1, pair1.p);
                            list.swap_remove(i0);
                            let mut other = set0.clone();
                            b.remove(&v0).unwrap();
                            b.get_mut(&v1).unwrap().append(&mut other);
                        } else {
                            assert_eq!(res.0, v1);
                            assert_eq!(res.1, pair0.p);
                            list.swap_remove(i1);
                            let mut other = set1.clone();
                            b.remove(&v1).unwrap();
                            b.get_mut(&v0).unwrap().append(&mut other);
                        }
                    }
                } else {
                    assert!(a.union(invalid, invalid).is_none());
                }
            }
            500..=549 => {
                // invalidate
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let i_set = next_inx!(rng, set_len);
                    let pair = set[i_set];
                    let p_new = a.invalidate(pair.p).unwrap();
                    gen += 1;
                    // keep key value
                    b.get_mut(&v).unwrap()[i_set] = Pair {
                        p: p_new,
                        k: pair.k,
                    };
                } else {
                    assert!(a.invalidate(invalid).is_none());
                }
            }
            550..=579 => {
                // swap_keys
                if len != 0 {
                    let v0 = list[next_inx!(rng, len)];
                    let v1 = list[next_inx!(rng, len)];
                    let set0 = &b[&v0];
                    let set_len0 = set0.len();
                    let set1 = &b[&v1];
                    let set_len1 = set1.len();
                    let i0 = next_inx!(rng, set_len0);
                    let i1 = next_inx!(rng, set_len1);
                    let pair0 = set0[i0];
                    let pair1 = set1[i1];
                    a.swap_keys(pair0.p, pair1.p).unwrap();
                    if pair0.p != pair1.p {
                        b.get_mut(&v0).unwrap()[i0].k = pair1.k;
                        b.get_mut(&v1).unwrap()[i1].k = pair0.k;
                    }
                } else {
                    assert!(a.swap_keys(invalid, invalid).is_none());
                }
            }
            580..=599 => {
                // swap_vals
                if len != 0 {
                    let v0 = list[next_inx!(rng, len)];
                    let v1 = list[next_inx!(rng, len)];
                    let set0 = &b[&v0];
                    let set_len0 = set0.len();
                    let set1 = &b[&v1];
                    let set_len1 = set1.len();
                    let pair0 = set0[next_inx!(rng, set_len0)];
                    let pair1 = set1[next_inx!(rng, set_len1)];
                    a.swap_vals(pair0.p, pair1.p).unwrap();
                    if v0 != v1 {
                        let tmp0 = b.remove(&v0).unwrap();
                        let tmp1 = b.remove(&v1).unwrap();
                        b.insert(v0, tmp1);
                        b.insert(v1, tmp0);
                    }
                } else {
                    assert!(a.swap_vals(invalid, invalid).is_none());
                }
            }
            600..=968 => {
                // reserved
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    let tmp = a.get(pair.p).unwrap();
                    assert_eq!((*tmp.0, *tmp.1), (pair.k, v));
                } else {
                    assert!(a.get(invalid).is_none());
                }
            }
            969 => {
                // compress_and_shrink_with
                // compress_and_shrink is difficult to test, we just note its definition is
                // self.compress_and_shrink_with(|_, _, _| ())

                let mut tmp: HashMap<Val, HashMap<Key, P0>> = HashMap::new();
                let q_gen = PtrGen::increment(a.gen());
                a.compress_and_shrink_with(|p, key, val, q| {
                    for pair in b.get(val).unwrap() {
                        if pair.k == *key {
                            assert_eq!(pair.p, p);
                        }
                    }
                    assert_eq!(q_gen, q.gen());
                    if let Some(set) = tmp.get_mut(val) {
                        set.insert(*key, q);
                    } else {
                        let mut set = HashMap::new();
                        set.insert(*key, q);
                        tmp.insert(*val, set);
                    }
                });
                assert_eq!(tmp.len(), a.len_vals());
                assert_eq!(a.capacity_keys(), a.len_keys());
                assert_eq!(a.capacity_vals(), a.len_vals());
                gen += 1;
                let mut total_keys = 0;
                for (val, set) in &tmp {
                    for (key, q) in set {
                        assert_eq!(val, a.get_val(*q).unwrap());
                        assert_eq!(key, a.get_key(*q).unwrap());
                        total_keys += 1;
                    }
                    let q_any = set.iter().next().unwrap().1;
                    assert_eq!(set.len(), a.len_key_set(*q_any).unwrap().get());
                }
                assert_eq!(total_keys, a.len_keys());
                // fix `Ptr`s
                for (val, set) in &tmp {
                    for pair in b.get_mut(val).unwrap() {
                        let q = set[&pair.k];
                        pair.p = q;
                    }
                }
            }
            970..=979 => {
                // advancer
                let mut i = 0;
                let mut adv = a.advancer();
                while let Some(p) = adv.advance(&a) {
                    assert!(a.contains(p));
                    i += 1;
                }
                // depends on the invalidated elements witnessed
                assert!(
                    (i == a.len_keys().saturating_sub(1))
                        || (i == a.len_keys())
                        || (i == (a.len_keys() + 1))
                );
            }
            980..=989 => {
                // advancer_surject
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    let mut iters = 0;
                    let mut seen = HashSet::new();

                    let mut adv = a.advancer_surject(pair.p);
                    while let Some(p) = adv.advance(&a) {
                        seen.insert(p);
                        iters += 1;
                    }
                    assert_eq!(seen.len(), iters);

                    for pair in set {
                        assert!(seen.remove(&pair.p));
                    }
                    assert!(seen.is_empty());
                } else {
                    let mut adv = a.advancer_surject(P0::invalid());
                    assert!(adv.advance(&a).is_none());
                }
            }
            990..=996 => {
                // iter_surject
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    let init = pair.p;
                    let mut iter = a.iter_surject(init);
                    let mut adv = a.advancer_surject(init);
                    while let Some(p) = adv.advance(&a) {
                        assert_eq!(
                            iter.next().unwrap(),
                            (p, a.get_key(p).unwrap(), a.get_val(p).unwrap())
                        );
                    }
                } else {
                    let mut iter = a.iter_surject(invalid);
                    assert!(iter.next().is_none());
                }
            }
            997 => {
                // iter, keys, keys_mut, ptrs, vals, vals_mut
                for (_, _, v) in &a {
                    assert!(b.contains_key(v));
                }
                for k in a.keys() {
                    black_box(k);
                }
                for k in a.keys_mut() {
                    black_box(k);
                }
                for p in a.ptrs() {
                    black_box(p);
                }
                for v in a.vals() {
                    assert!(b.contains_key(v));
                }
                for v in a.vals_mut() {
                    assert!(b.contains_key(v));
                }
            }
            998 => {
                // clear
                let prev_cap_keys = a.capacity_keys();
                let prev_cap_vals = a.capacity_vals();
                a.clear();
                assert_eq!(a.capacity_keys(), prev_cap_keys);
                assert_eq!(a.capacity_vals(), prev_cap_vals);
                b.clear();
                gen += 1;
                list.clear();
            }
            999 => {
                // clear_and_shrink
                a.clear_and_shrink();
                assert_eq!(a.capacity_keys(), 0);
                assert_eq!(a.capacity_vals(), 0);
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
    assert_eq!((max_key_len, max_val_len, iters999, a.gen().get()), STATS);
}
