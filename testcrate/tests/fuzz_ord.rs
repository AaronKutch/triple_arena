use std::{cmp::Ordering, collections::BTreeMap};

use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use testcrate::P0;
use triple_arena::{Link, OrdArena};

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
    assert!(a.insert_linear(None, Key { k: 0 }, Val { v: 0 }).is_err());
    assert!(a
        .insert_nonhereditary_linear(None, Key { k: 0 }, Val { v: 0 })
        .is_err());
    a.remove(invalid).unwrap();
    assert!(a
        .insert_linear(Some(invalid), Key { k: 0 }, Val { v: 0 })
        .is_err());
    assert!(a
        .insert_nonhereditary_linear(Some(invalid), Key { k: 0 }, Val { v: 0 })
        .is_err());
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
        let mut true_len = 0;
        for set in b.values() {
            assert!(!set.is_empty());
            true_len += set.len();
        }
        assert_eq!(true_len, a.len());
        assert_eq!(a.gen().get(), gen);
        assert_eq!(a.is_empty(), list.is_empty());
        let len = list.len();
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
        //println!("i: {i}");

        op_inx = rng.next_u32() % 1000;
        match op_inx {
            // note: we give slightly more single inserts than single removes to encourage larger
            // trees
            0..=49 => {
                // insert, insert_similar
                let k = new_k();
                let v = new_v();
                let (p, k_v) = if (rng.next_u32() % 100) < 90 {
                    a.insert(k, v)
                } else {
                    let p_init = if a.is_empty() {
                        None
                    } else {
                        // start from anywhere
                        Some(list[next_inx!(rng, len)].p)
                    };
                    a.insert_linear(p_init, k, v).unwrap()
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
            50..=104 => {
                // insert_nonhereditary, insert_nonhereditary_linear
                let k = new_k();
                let v = new_v();
                let p = if (rng.next_u32() % 100) < 90 {
                    a.insert_nonhereditary(k, v)
                } else {
                    let p_init = if a.is_empty() {
                        None
                    } else {
                        // start from anywhere
                        Some(list[next_inx!(rng, len)].p)
                    };
                    a.insert_nonhereditary_linear(p_init, k, v).unwrap()
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
            105..=199 => {
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
            200..=249 => {
                // find_similar_key, find_similar_key_linear
                let new_k = new_k();
                if len != 0 {
                    let (p, ord) = if (rng.next_u32() % 100) < 90 {
                        a.find_similar_key(&new_k).unwrap()
                    } else {
                        a.find_similar_key_linear(list[next_inx!(rng, len)].p, &new_k)
                            .unwrap()
                    };
                    let link = a.get_link(p).unwrap();
                    match ord {
                        Ordering::Less => {
                            if let Some(prev) = Link::prev(&link) {
                                assert!(a.get_key(prev).unwrap().lt(&new_k));
                            }
                            assert!(new_k.lt(link.t.0));
                        }
                        Ordering::Equal => {
                            assert_eq!(*link.t.0, new_k);
                        }
                        Ordering::Greater => {
                            assert!(link.t.0.lt(&new_k));
                            if let Some(next) = Link::next(&link) {
                                assert!(new_k.lt(a.get_key(next).unwrap()));
                            }
                        }
                    }
                } else {
                    assert!(a.find_similar_key(&new_k).is_none());
                    assert!(a.find_similar_key_linear(invalid, &new_k).is_none());
                }
            }
            250..=299 => {
                // find_key, find_key_linear
                let new_k = new_k();
                if let Some(set) = b.get(&new_k) {
                    let p = if (rng.next_u32() % 100) < 90 {
                        a.find_key(&new_k).unwrap()
                    } else {
                        a.find_key_linear(list[next_inx!(rng, len)].p, &new_k)
                            .unwrap()
                    };
                    let v = *a.get_val(p).unwrap();
                    assert!(set.contains_key(&v));
                } else if (rng.next_u32() % 100) < 90 {
                    assert!(a.find_key(&new_k).is_none());
                } else if len == 0 {
                    assert!(a.find_key_linear(invalid, &new_k).is_none());
                } else {
                    assert!(a
                        .find_key_linear(list[next_inx!(rng, len)].p, &new_k)
                        .is_none());
                }
            }
            // TODO test everything
            300..=995 => {
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
    assert_eq!((max_len, iters999, a.gen().get()), (85, 1047, 87961));
}
