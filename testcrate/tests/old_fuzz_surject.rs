#![cfg(feature = "alloc")]

use std::{
    cmp::max,
    collections::{HashMap, HashSet},
    hint::black_box,
};

use rand_xoshiro::{
    Xoshiro128StarStar,
    rand_core::{Rng, SeedableRng},
};
use testcrate::P0;
use triple_arena::{SurjectArena, traits::*};

const N: usize = if cfg!(miri) { 1000 } else { 1_000_000 };

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
    let mut generation = 2;
    let mut b: HashMap<Val, Vec<Pair>> = HashMap::new();

    let invalid = a.insert(Key::MAX, Val { v: u64::MAX });
    a.remove_key(invalid).allow().unwrap();
    generation += 1;
    a.clear().allow();
    generation += 1;
    let mut op_inx;
    let mut max_key_len = 0;
    let mut max_val_len = 0;

    for _ in 0..N {
        assert_eq!(a.len_vals(), list.len());
        assert_eq!(a.len_vals(), b.len());
        let len = list.len();
        let _ = generation;
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
                panic!("{e}");
            }
        }
        op_inx = rng.next_u32() % 1000;
        match op_inx {
            0..25 => {
                // insert
                let k = new_k();
                let v = new_v();
                let p = a.insert(k, v);
                list.push(v);
                b.insert(v, vec![Pair { p, k }]);
            }
            25..100 => {
                // insert_key
                if len != 0 {
                    let k = new_k();
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let Pair { p, .. } = set[next_inx!(rng, set_len)];
                    let p_new = a.insert_key(p, k);
                    b.get_mut(&v).unwrap().push(Pair { p: p_new, k });
                } else {
                    assert!(a.insert_key_reallocating(invalid, Key::MAX).is_err());
                }
            }
            100..=104 => {
                // remove
                if len != 0 {
                    let v = list.swap_remove(next_inx!(rng, len));
                    let set = b.remove(&v).unwrap();
                    let set_len = set.len();
                    let removed = a
                        .remove_surject(set[next_inx!(rng, set_len)].p)
                        .allow()
                        .unwrap();
                    assert_eq!(removed, v);
                    generation += 1;
                } else {
                    assert!(a.remove_surject(invalid).allow().is_none());
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
                    let res = a.remove_key(pair.p).allow();
                    generation += 1;
                    if set_len == 1 {
                        list.swap_remove(i);
                        b.remove(&v).unwrap();
                        assert_eq!(res, Some((pair.k, Some(v))));
                    } else {
                        b.get_mut(&v).unwrap().swap_remove(i_set);
                        assert_eq!(res, Some((pair.k, None)));
                    }
                } else {
                    assert!(a.remove_key(invalid).allow().is_none());
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
            390..446 => {
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
            446..=449 => {
                // get_inx_link_no_gen
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let pair = set[next_inx!(rng, set_len)];
                    let (_, link) = a.get_inx_link_no_gen(pair.p.inx()).unwrap();
                    assert_eq!(*link.t, pair.k);
                } else {
                    assert!(a.get_inx_link_no_gen(P0::invalid().inx()).is_none());
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
            500..600 => {
                // invalidate
                if len != 0 {
                    let v = list[next_inx!(rng, len)];
                    let set = &b[&v];
                    let set_len = set.len();
                    let i_set = next_inx!(rng, set_len);
                    let pair = set[i_set];
                    let p_new = a.invalidate(pair.p).allow().unwrap();
                    generation += 1;
                    // keep key value
                    b.get_mut(&v).unwrap()[i_set] = Pair {
                        p: p_new,
                        k: pair.k,
                    };
                } else {
                    assert!(a.invalidate(invalid).allow().is_none());
                }
            }
            600..970 => {
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
            /*969 => {
                // compress_and_shrink_with
                // compress_and_shrink is difficult to test, we just note its definition is
                // self.compress_and_shrink_with(|_, _, _| ())

                let mut tmp: HashMap<Val, HashMap<Key, P0>> = HashMap::new();
                let q_gen = PtrGen::generational_inc(a.generation()).0;
                a.compress_and_shrink_with(|p, key, val, q| {
                    for pair in b.get(val).unwrap() {
                        if pair.k == *key {
                            assert_eq!(pair.p, p);
                        }
                    }
                    assert_eq!(q_gen, q.generation());
                    if let Some(set) = tmp.get_mut(val) {
                        set.insert(*key, q);
                    } else {
                        let mut set = HashMap::new();
                        set.insert(*key, q);
                        tmp.insert(*val, set);
                    }
                });
                assert_eq!(tmp.len(), a.len_vals());
                generation += 1;
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
            }*/
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
                a.clear().allow();
                assert_eq!(a.capacity_keys(), prev_cap_keys);
                assert_eq!(a.capacity_vals(), prev_cap_vals);
                b.clear();
                generation += 1;
                list.clear();
            }
            999 => {
                // clear_and_shrink
                a.clear().allow();
                b.clear();
                generation += 1;
                list.clear();
            }
            _ => unreachable!(),
        }
        max_key_len = max(max_key_len, a.len_keys());
        max_val_len = max(max_val_len, a.len_vals());
    }
}
