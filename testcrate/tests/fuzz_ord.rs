use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashMap},
    hint::black_box,
};

use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use testcrate::P0;
use triple_arena::{utils::PtrGen, Advancer, OrdArena, Ptr};

const N: usize = if cfg!(miri) {
    1000
} else if cfg!(debug_assertions) {
    100_000
} else {
    5_000_000
};

const STATS: (usize, u64, u128) = if cfg!(miri) {
    (70, 1, 122)
} else if cfg!(debug_assertions) {
    (239, 107, 14567)
} else {
    (418, 5049, 749771)
};

macro_rules! next_inx {
    ($rng:ident, $len:ident) => {
        $rng.next_u32() as usize % $len
    };
}

#[test]
#[allow(clippy::type_complexity)]
fn fuzz_ord() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    // avoid getting mixups
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Key {
        pub k: u64,
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Val {
        pub v: u64,
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Triple {
        pub p: P0,
        pub k: Key,
        pub v: Val,
    }

    // make sure we have collisions
    const MAX_KEY: u64 = 128;

    // unique id for checking that the correct elements are returned
    let mut key_rng = Xoshiro128StarStar::seed_from_u64(0);
    let mut new_k = || Key {
        k: key_rng.next_u64() % MAX_KEY,
    };
    let mut counter_v = 0u64;
    let mut new_v = || {
        counter_v += 1;
        Val { v: counter_v }
    };

    let mut list: Vec<Triple> = vec![];

    let mut a: OrdArena<P0, Key, Val> = OrdArena::new();
    let mut gen = 2;
    // the tricky part is that we need to handle nonhereditary cases
    let mut b: BTreeMap<Key, BTreeMap<Val, Triple>> = BTreeMap::new();

    let invalid = a.insert_nonhereditary(Key { k: 0 }, Val { v: 0 });
    assert!(a.insert_empty(Key { k: 0 }, Val { v: 0 }).is_none());
    a.clear_and_shrink();
    gen += 1;
    let mut op_inx;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;
    let mut max_len = 0;
    for _ in 0..N {
        assert_eq!(a.len(), list.len());
        let mut true_len = 0;
        for set in b.values() {
            assert!(!set.is_empty());
            true_len += set.len();
        }
        assert_eq!(true_len, a.len());
        assert_eq!(a.gen().get(), gen);
        assert_eq!(a.is_empty(), list.is_empty());
        let len = list.len();
        if !cfg!(miri) {
            if let Err(e) = OrdArena::_check_invariants(&a) {
                //if i == 9 {
                /*let debug0 = a.debug_arena();
                let mut debug1 = triple_arena::Arena::new();
                debug1.clone_from_with(&debug0, |p, t| triple_arena_render::DebugNode {
                    sources: if let Some(tmp) = t.4 {
                        vec![(tmp, String::new())]
                    } else {
                        vec![]
                    },
                    center: vec![
                        format!("p: {:?}", p),
                        format!("rank: {:?}", t.0),
                        format!("k: {:?}", t.1),
                        format!("v: {:?}", t.2),
                    ],
                    sinks: {
                        let mut v = vec![];
                        if let Some(tmp) = t.3 {
                            v.push((tmp, "0".to_owned()))
                        }
                        if let Some(tmp) = t.5 {
                            v.push((tmp, "1".to_owned()))
                        }
                        v
                    },
                });
                triple_arena_render::render_to_svg_file(
                    &debug1,
                    false,
                    std::path::PathBuf::from("./debug.svg"),
                )
                .unwrap();
                println!("{}", a.debug());*/
                panic!("{e}");
            }
        }
        //println!("i: {i}");

        op_inx = rng.next_u32() % 1000;
        match op_inx {
            // note: we give slightly more single inserts than single removes to encourage larger
            // trees, also we have more of them vs whole clears to test large trees
            0..=99 => {
                // insert, insert_similar
                let k = new_k();
                let v = new_v();
                let (p, k_v) = if (rng.next_u32() & 1) == 0 {
                    a.insert(k, v)
                } else {
                    let p_init = if a.is_empty() {
                        Ptr::invalid()
                    } else {
                        // start from anywhere
                        list[next_inx!(rng, len)].p
                    };
                    a.insert_linear(p_init, 4, k, v)
                };
                let triple = Triple { p, k, v };
                list.push(triple);
                if let Some(set) = b.get_mut(&k) {
                    let k_v = k_v.unwrap();
                    assert_eq!(k_v.0, k);
                    let triple_replaced = set.remove(&k_v.1).unwrap();
                    // we have to find it in the list to remove
                    let mut tmp = None;
                    for (i, t) in list.iter().enumerate() {
                        if t.v == triple_replaced.v {
                            tmp = Some(i);
                        }
                    }
                    list.remove(tmp.unwrap());
                    set.insert(v, triple);
                } else {
                    assert!(k_v.is_none());
                    let mut set = BTreeMap::new();
                    set.insert(v, triple);
                    b.insert(k, set);
                }
            }
            100..=209 => {
                // insert_nonhereditary, insert_nonhereditary_linear
                let k = new_k();
                let v = new_v();
                let p = if (rng.next_u32() % 100) < 90 {
                    a.insert_nonhereditary(k, v)
                } else {
                    let p_init = if a.is_empty() {
                        Ptr::invalid()
                    } else {
                        // start from anywhere
                        list[next_inx!(rng, len)].p
                    };
                    a.insert_nonhereditary_linear(p_init, 4, k, v)
                };
                let triple = Triple { p, k, v };
                list.push(triple);
                if let Some(set) = b.get_mut(&k) {
                    set.insert(v, triple);
                } else {
                    let mut set = BTreeMap::new();
                    set.insert(v, triple);
                    b.insert(k, set);
                }
            }
            210..=299 => {
                // remove
                if len != 0 {
                    let t = list.swap_remove(next_inx!(rng, len));
                    assert_eq!(a.remove(t.p).unwrap(), (t.k, t.v));
                    let set = b.get_mut(&t.k).unwrap();
                    assert_eq!(set.remove(&t.v).unwrap(), t);
                    if set.is_empty() {
                        b.remove(&t.k);
                    }
                    gen += 1;
                } else {
                    assert!(a.remove(invalid).is_none());
                }
            }
            300..=349 => {
                // find_similar_key, find_similar_key_linear
                let new_k = new_k();
                if len != 0 {
                    let (p, ord) = if (rng.next_u32() & 1) == 0 {
                        a.find_similar_key(&new_k).unwrap()
                    } else {
                        a.find_similar_key_linear(list[next_inx!(rng, len)].p, 4, &new_k)
                            .unwrap()
                    };
                    let link = a.get_link(p).unwrap();
                    match ord {
                        Ordering::Less => {
                            if let Some(prev) = link.prev() {
                                assert!(a.get_key(prev).unwrap().lt(&new_k));
                            }
                            assert!(new_k.lt(link.t.0));
                        }
                        Ordering::Equal => {
                            assert_eq!(*link.t.0, new_k);
                        }
                        Ordering::Greater => {
                            assert!(link.t.0.lt(&new_k));
                            if let Some(next) = link.next() {
                                assert!(new_k.lt(a.get_key(next).unwrap()));
                            }
                        }
                    }
                } else {
                    assert!(a.find_similar_key(&new_k).is_none());
                    assert!(a.find_similar_key_linear(invalid, 4, &new_k).is_none());
                }
            }
            350..=399 => {
                // find_key, find_key_linear
                let new_k = new_k();
                if let Some(set) = b.get(&new_k) {
                    let p = if (rng.next_u32() & 1) == 0 {
                        a.find_key(&new_k).unwrap()
                    } else {
                        a.find_key_linear(list[next_inx!(rng, len)].p, 4, &new_k)
                            .unwrap()
                    };
                    let v = *a.get_val(p).unwrap();
                    assert!(set.contains_key(&v));
                } else if (rng.next_u32() & 1) == 0 {
                    assert!(a.find_key(&new_k).is_none());
                } else if len == 0 {
                    assert!(a.find_key_linear(invalid, 4, &new_k).is_none());
                } else {
                    assert!(a
                        .find_key_linear(list[next_inx!(rng, len)].p, 4, &new_k)
                        .is_none());
                }
            }
            400..=419 => {
                // contains, get_link, get, get_key, get_val, get_link_mut, get_mut, get_val_mut
                if len != 0 {
                    let t = &list[next_inx!(rng, len)];
                    assert!(a.contains(t.p));
                    assert_eq!(a.get_link(t.p).unwrap().t, (&t.k, &t.v));
                    assert_eq!(a.get(t.p).unwrap(), (&t.k, &t.v));
                    assert_eq!(a.get_key(t.p).unwrap(), &t.k);
                    assert_eq!(a.get_val(t.p).unwrap(), &t.v);
                    let mut tmp = t.v;
                    assert_eq!(a.get_mut(t.p).unwrap(), (&t.k, &mut tmp));
                    assert_eq!(a.get_val_mut(t.p).unwrap(), &mut tmp);
                } else {
                    assert!(!a.contains(invalid));
                    assert!(a.get_link(invalid).is_none());
                    assert!(a.get(invalid).is_none());
                    assert!(a.get_key(invalid).is_none());
                    assert!(a.get_val(invalid).is_none());
                    assert!(a.get_mut(invalid).is_none());
                    assert!(a.get_val_mut(invalid).is_none());
                }
            }
            420..=439 => {
                // get2_val_mut
                if len != 0 {
                    let t0 = &list[next_inx!(rng, len)];
                    let t1 = &list[next_inx!(rng, len)];
                    if t0.p == t1.p {
                        assert!(a.get2_val_mut(t0.p, t1.p).is_none())
                    } else {
                        let tmp = a.get2_val_mut(t0.p, t1.p).unwrap();
                        let mut val0 = t0.v;
                        assert_eq!(tmp.0, &mut val0);
                        let mut val1 = t1.v;
                        assert_eq!(tmp.1, &mut val1);
                    }
                } else {
                    assert!(a.get2_val_mut(invalid, invalid).is_none())
                }
            }
            440..=459 => {
                // replace_val_and_keep_gen
                if len != 0 {
                    let t = &mut list[next_inx!(rng, len)];
                    let v = new_v();
                    assert_eq!(a.replace_val_and_keep_gen(t.p, v), Ok(t.v));
                    let set = b.get_mut(&t.k).unwrap();
                    set.remove(&t.v).unwrap();
                    set.insert(v, Triple { p: t.p, k: t.k, v });
                    t.v = v;
                } else {
                    assert_eq!(
                        a.replace_val_and_keep_gen(invalid, Val { v: 0 }),
                        Err(Val { v: 0 })
                    );
                }
            }
            460..=479 => {
                // replace_val_and_update_gen
                if len != 0 {
                    let t = &mut list[next_inx!(rng, len)];
                    let v = new_v();
                    let (old_v, new_p) = a.replace_val_and_update_gen(t.p, v).unwrap();
                    assert_eq!(t.v, old_v);
                    let set = b.get_mut(&t.k).unwrap();
                    set.remove(&t.v).unwrap();
                    set.insert(v, Triple {
                        p: new_p,
                        k: t.k,
                        v,
                    });
                    t.p = new_p;
                    t.v = v;
                    gen += 1;
                } else {
                    assert_eq!(
                        a.replace_val_and_update_gen(invalid, Val { v: 0 }),
                        Err(Val { v: 0 })
                    );
                }
            }
            480..=499 => {
                // invalidate
                if len != 0 {
                    let t = &mut list[next_inx!(rng, len)];
                    let new_p = a.invalidate(t.p).unwrap();
                    let set = b.get_mut(&t.k).unwrap();
                    set.get_mut(&t.v).unwrap().p = new_p;
                    t.p = new_p;
                    gen += 1;
                } else {
                    assert!(a.invalidate(invalid).is_none());
                }
            }
            500..=519 => {
                // swap_vals
                if len != 0 {
                    let inx0 = next_inx!(rng, len);
                    let inx1 = next_inx!(rng, len);
                    let t0 = &list[inx0];
                    let t1 = &list[inx1];
                    a.swap_vals(t0.p, t1.p).unwrap();
                    let val0 = t0.v;
                    let val1 = t1.v;
                    if t0.p != t1.p {
                        b.get_mut(&t0.k).unwrap().remove(&t0.v).unwrap();
                        b.get_mut(&t1.k).unwrap().remove(&t1.v).unwrap();
                        b.get_mut(&t0.k).unwrap().insert(val1, Triple {
                            p: t0.p,
                            k: t0.k,
                            v: val1,
                        });
                        b.get_mut(&t1.k).unwrap().insert(val0, Triple {
                            p: t1.p,
                            k: t1.k,
                            v: val0,
                        });
                    }
                    list[inx0].v = val1;
                    list[inx1].v = val0;
                } else {
                    assert!(a.swap_vals(invalid, invalid).is_none())
                }
            }
            520..=994 => {
                // find_key with get_val
                let new_k = new_k();
                if let Some(set) = b.get(&new_k) {
                    let p = a.find_key(&new_k).unwrap();
                    let v = *a.get_val(p).unwrap();
                    assert!(set.contains_key(&v));
                } else {
                    assert!(a.find_key(&new_k).is_none())
                }
            }
            995 => {
                // advancer, ptrs, iter, keys, keys_mut, vals, vals_mut
                let mut adv = a.advancer();
                let mut ptrs = a.ptrs();
                let mut iter = a.iter();
                let mut keys = a.keys();
                let mut vals = a.vals();
                while let Some(p) = adv.advance(&a) {
                    let (k, v) = a.get(p).unwrap();
                    assert_eq!(ptrs.next().unwrap(), p);
                    assert_eq!(iter.next().unwrap(), (p, k, v));
                    assert_eq!(*keys.next().unwrap(), *k);
                    assert_eq!(*vals.next().unwrap(), *v);
                }
                for v in a.vals_mut() {
                    black_box(v);
                }
            }
            996 => {
                // min
                if len != 0 {
                    let set = b.first_entry().unwrap();
                    let v = a.get_val(a.min().unwrap()).unwrap();
                    assert!(set.get().contains_key(v));
                } else {
                    assert!(a.min().is_none());
                }
            }
            997 => {
                // max
                if len != 0 {
                    let set = b.last_entry().unwrap();
                    let v = a.get_val(a.max().unwrap()).unwrap();
                    assert!(set.get().contains_key(v));
                } else {
                    assert!(a.max().is_none());
                }
            }
            998 => {
                // compress_and_shrink_with
                // compress_and_shrink is difficult to test, we just note its definition is
                // self.compress_and_shrink_with(|_, _, _| ())

                let mut tmp: HashMap<Val, Triple> = HashMap::new();
                let q_gen = PtrGen::increment(a.gen());
                a.compress_and_shrink_with(|p, key, val, q| {
                    let set = &b[key];
                    assert_eq!(set[val].p, p);
                    assert_eq!(q_gen, q.gen());
                    tmp.insert(*val, Triple {
                        p: q,
                        k: *key,
                        v: *val,
                    });
                });
                assert_eq!(tmp.len(), a.len());
                assert_eq!(a.capacity(), a.len());
                gen += 1;
                for (val, triple) in &tmp {
                    assert_eq!(val, a.get_val(triple.p).unwrap());
                    assert_eq!(triple.k, *a.get_key(triple.p).unwrap());
                }
                // fix `Ptr`s
                for (val, triple) in &tmp {
                    for set_part in b.get_mut(&triple.k).unwrap() {
                        if set_part.0 == val {
                            set_part.1.p = triple.p;
                            break
                        }
                    }
                }
                for triple in &mut list {
                    for set_part in &b[&triple.k] {
                        if *set_part.0 == triple.v {
                            triple.p = set_part.1.p;
                            break
                        }
                    }
                }
            }
            999 => {
                match rng.next_u32() % 4 {
                    0 => {
                        // clear_and_shrink
                        a.clear_and_shrink();
                        assert_eq!(a.capacity(), 0);
                        gen += 1;
                    }
                    1 => {
                        // clear
                        let prev_cap = a.capacity();
                        a.clear();
                        assert_eq!(a.capacity(), prev_cap);
                        gen += 1;
                    }
                    2 => {
                        // drain
                        // TODO improve
                        gen += a.len() as u128;
                        let prev_cap = a.capacity();
                        for (p, k, v) in a.drain() {
                            black_box((p, k, v));
                        }
                        assert_eq!(a.capacity(), prev_cap);
                    }
                    3 => {
                        // drain_capacity
                        for (p, k, v) in a.clone() {
                            black_box((p, k, v));
                        }
                        a.clear();
                        gen += 1;
                    }
                    _ => unreachable!(),
                }
                b.clear();
                list.clear();
                iters999 += 1;
            }
            _ => unreachable!(),
        }
        max_len = std::cmp::max(max_len, a.len());
    }
    assert_eq!((max_len, iters999, a.gen().get()), STATS);
}
