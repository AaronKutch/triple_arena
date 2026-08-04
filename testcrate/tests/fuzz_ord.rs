#![cfg(feature = "alloc")]

use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashMap},
    hint::black_box,
};

use rand_xoshiro::{
    Xoshiro128StarStar,
    rand_core::{Rng, SeedableRng},
};
use testcrate::P0;
use triple_arena::{OrdInsertKind, OrdPair, SimpleOrdArena, traits::*, utils::traits::PtrGen};

const N: usize = if cfg!(miri) {
    1000
} else if cfg!(debug_assertions) {
    100_000
} else {
    5_000_000
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

    let mut a: SimpleOrdArena<P0, OrdPair<Key, Val>> = SimpleOrdArena::new();
    let mut generation = 2;
    // the tricky part is that we need to handle nonhereditary cases
    let mut b: BTreeMap<Key, BTreeMap<Val, Triple>> = BTreeMap::new();

    let invalid = a.insert(OrdPair::new(Key { k: 0 }, Val { v: 0 })).0;
    assert!(a.entry_insert_reallocating(OrdInsertKind::Empty).is_err());
    a.clear().allow();
    generation += 1;
    let mut op_inx;
    let mut max_len = 0;
    for _ in 0..N {
        assert_eq!(a.len(), list.len());
        let mut true_len = 0;
        for set in b.values() {
            assert!(!set.is_empty());
            true_len += set.len();
        }
        assert_eq!(true_len, a.len());
        let _ = generation;
        assert_eq!(a.is_empty(), list.is_empty());
        let len = list.len();
        if !cfg!(miri)
            && let Err(e) = SimpleOrdArena::_check_invariants(&a)
        {
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
            // trees, also we have more of them vs whole clears to test large trees
            0..=99 => {
                // insert, insert_similar
                let k = new_k();
                let v = new_v();
                let (p, k_v) = if (rng.next_u32() & 1) == 0 {
                    a.insert(OrdPair::new(k, v))
                } else {
                    let p_init = if a.is_empty() {
                        Ptr::invalid()
                    } else {
                        // start from anywhere
                        list[next_inx!(rng, len)].p
                    };
                    let pair = OrdPair::new(k, v);
                    let entry = a.entry_insert(OrdInsertKind::Linear {
                        k: pair.k(),
                        p_init: p_init.inx(),
                        num: 4,
                    });
                    (entry.ptr().any(), entry.insert(pair))
                };
                let triple = Triple { p, k, v };
                list.push(triple);
                if let Some(set) = b.get_mut(&k) {
                    let k_v = k_v.unwrap();
                    assert_eq!(*k_v.k(), k);
                    let triple_replaced = set.remove(k_v.v()).unwrap();
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
                let pair = OrdPair::new(k, v);
                let (p, replaced) = if (rng.next_u32() % 100) < 90 {
                    let entry = a.entry_insert(OrdInsertKind::Nonhereditary(pair.k()));
                    (entry.ptr().any(), entry.insert(pair))
                } else {
                    let p_init = if a.is_empty() {
                        Ptr::invalid()
                    } else {
                        // start from anywhere
                        list[next_inx!(rng, len)].p
                    };
                    let entry = a.entry_insert(OrdInsertKind::NonhereditaryLinear {
                        k: pair.k(),
                        p_init: p_init.inx(),
                        num: 4,
                    });
                    (entry.ptr().any(), entry.insert(pair))
                };
                assert!(replaced.is_none());
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
            210..300 => {
                // remove
                if len != 0 {
                    let t = list.swap_remove(next_inx!(rng, len));
                    assert_eq!(a.remove(t.p).allow().unwrap(), OrdPair::new(t.k, t.v));
                    let set = b.get_mut(&t.k).unwrap();
                    assert_eq!(set.remove(&t.v).unwrap(), t);
                    if set.is_empty() {
                        b.remove(&t.k);
                    }
                    generation += 1;
                } else {
                    assert!(a.remove(invalid).allow().is_none());
                }
            }
            300..=349 => {
                // find_similar_key, find_similar_key_linear
                let new_k = new_k();
                if len != 0 {
                    let (p, ord) = if (rng.next_u32() & 1) == 0 {
                        a.find_similar_key(&new_k).unwrap()
                    } else {
                        a.find_similar_key_linear(list[next_inx!(rng, len)].p.inx(), 4, &new_k)
                            .unwrap()
                    };
                    let link = a.get_inx_link_no_gen(p.inx()).unwrap().1;
                    match ord {
                        Ordering::Less => {
                            if let Some(prev) = link.prev() {
                                assert!(a.get_inx(prev).unwrap().1.k().lt(&new_k));
                            }
                            assert!(new_k.lt(link.t.k()));
                        }
                        Ordering::Equal => {
                            assert_eq!(*link.t.k(), new_k);
                        }
                        Ordering::Greater => {
                            assert!(link.t.k().lt(&new_k));
                            if let Some(next) = link.next() {
                                assert!(new_k.lt(a.get_inx(next).unwrap().1.k()));
                            }
                        }
                    }
                } else {
                    assert!(a.find_similar_key(&new_k).is_none());
                    assert!(
                        a.find_similar_key_linear(invalid.inx(), 4, &new_k)
                            .is_none()
                    );
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
                    let v = a.get(p).unwrap().v();
                    assert!(set.contains_key(&v));
                } else if (rng.next_u32() & 1) == 0 {
                    assert!(a.find_key(&new_k).is_none());
                } else if len == 0 {
                    assert!(a.find_key_linear(invalid, 4, &new_k).is_none());
                } else {
                    assert!(
                        a.find_key_linear(list[next_inx!(rng, len)].p, 4, &new_k)
                            .is_none()
                    );
                }
            }
            400..480 => {
                // contains, get_link, get, get_key, get_val, get_link_mut, get_mut, get_val_mut
                if len != 0 {
                    let t = &list[next_inx!(rng, len)];
                    assert!(a.contains(t.p));
                    assert_eq!(a.get(t.p).unwrap(), &OrdPair::new(t.k, t.v));
                    /*assert_eq!(a.get(t.p).unwrap(), (&t.k, &t.v));
                    assert_eq!(a.get_key(t.p).unwrap(), &t.k);
                    assert_eq!(a.get_val(t.p).unwrap(), &t.v);
                    let mut tmp = t.v;
                    assert_eq!(a.get_mut(t.p).unwrap(), (&t.k, &mut tmp));
                    assert_eq!(a.get_val_mut(t.p).unwrap(), &mut tmp);*/
                } else {
                    assert!(!a.contains(invalid));
                    /*assert!(a.get_link(invalid).is_none());
                    assert!(a.get(invalid).is_none());
                    assert!(a.get_key(invalid).is_none());
                    assert!(a.get_val(invalid).is_none());
                    assert!(a.get_mut(invalid).is_none());
                    assert!(a.get_val_mut(invalid).is_none());*/
                }
            }
            480..520 => {
                // invalidate
                if len != 0 {
                    let t = &mut list[next_inx!(rng, len)];
                    let new_p = a.invalidate(t.p).allow().unwrap();
                    let set = b.get_mut(&t.k).unwrap();
                    set.get_mut(&t.v).unwrap().p = new_p;
                    t.p = new_p;
                    generation += 1;
                } else {
                    assert!(a.invalidate(invalid).allow().is_none());
                }
            }

            520..=549 => {
                // find_with
                let new_k = new_k();
                if let Some(set) = b.get(&new_k) {
                    let p = a
                        .find_with(|p, pair| {
                            assert_eq!(a.get(p).unwrap(), pair);
                            new_k.cmp(pair.k())
                        })
                        .unwrap();
                    let v = a.get(p).unwrap().v();
                    assert!(set.contains_key(v));
                } else {
                    assert!(a.find_with(|_, pair| new_k.cmp(pair.k())).is_none());
                }
            }
            550..=579 => {
                // find_similar_with
                let new_k = new_k();
                if let Some(set) = b.get(&new_k) {
                    let (p, ord) = a
                        .find_similar_with(|p, pair| {
                            assert_eq!(a.get(p).unwrap(), pair);
                            new_k.cmp(pair.k())
                        })
                        .unwrap();
                    let v = a.get(p).unwrap().v();
                    assert!(set.contains_key(&v));
                    assert_eq!(ord, Ordering::Equal);
                } else if a.is_empty() {
                    assert!(a.find_similar_with(|_, pair| new_k.cmp(pair.k())).is_none());
                } else {
                    let (p, ord) = a.find_similar_with(|_, pair| new_k.cmp(pair.k())).unwrap();
                    let k = a.get(p).unwrap().k();
                    match ord {
                        Ordering::Less => {
                            if let Some(prev) = a.get_inx_link_no_gen(p.inx()).unwrap().1.prev() {
                                assert!(*a.get_inx(prev).unwrap().1.k() < new_k);
                            }
                            assert!(new_k < *k);
                        }
                        Ordering::Equal => unreachable!(),
                        Ordering::Greater => {
                            if let Some(next) = a.get_inx_link_no_gen(p.inx()).unwrap().1.next() {
                                assert!(new_k < *a.get_inx(next).unwrap().1.k());
                            }
                            assert!(*k < new_k);
                        }
                    }
                }
            }
            580..995 => {
                // find_key with get_val
                let new_k = new_k();
                if let Some(set) = b.get(&new_k) {
                    let p = a.find_key(&new_k).unwrap();
                    let v = a.get(p).unwrap().v();
                    assert!(set.contains_key(v));
                } else {
                    assert!(a.find_key(&new_k).is_none())
                }
            }
            995 => {
                // advancer, ptrs, iter, keys, keys_mut, vals, vals_mut, advancer_starting_from
                let mut adv = a.advancer();
                //let mut ptrs = a.ptrs();
                //let mut iter = a.iter();
                //let mut keys = a.keys();
                //let mut vals = a.vals();
                let new_k = new_k();
                let p_start = a.find_key(&new_k).unwrap_or(Ptr::invalid());
                let mut adv_from = a.advancer_inx(p_start.inx(), false);
                let mut adv_from_started = false;
                while let Some(p) = adv.advance(&a) {
                    //let (k, v) = a.get(p).unwrap().k_v();
                    //assert_eq!(ptrs.next().unwrap(), p);
                    //assert_eq!(iter.next().unwrap(), (p, k, v));
                    //assert_eq!(*keys.next().unwrap(), *k);
                    //assert_eq!(*vals.next().unwrap(), *v);
                    if p_start == p {
                        adv_from_started = true;
                    }
                    if adv_from_started {
                        assert_eq!(adv_from.advance(&a).unwrap(), p);
                    }
                }
                assert!(adv_from.advance(&a).is_none());
                for v in a.vals_mut() {
                    black_box(v);
                }
            }
            996 => {
                // first
                if len != 0 {
                    let set = b.first_entry().unwrap();
                    let v = a.get(a.first().unwrap()).unwrap().v();
                    assert!(set.get().contains_key(v));
                } else {
                    assert!(a.first().is_none());
                }
            }
            997..998 => {
                // last
                if len != 0 {
                    let set = b.last_entry().unwrap();
                    let v = a.get(a.last().unwrap()).unwrap().v();
                    assert!(set.get().contains_key(v));
                } else {
                    assert!(a.last().is_none());
                }
            }
            998 => {
                // compress_with

                let mut tmp: HashMap<Val, Triple> = HashMap::new();
                let q_gen = PtrGen::generational_inc(a.generation()).0;
                SimpleOrdArena::_check_invariants(&a).unwrap();
                a.compress_with(false, |p, pair, q| {
                    let set = &b[pair.k()];
                    assert_eq!(set[pair.v()].p, p);
                    assert_eq!(q_gen, q.generation());
                    tmp.insert(*pair.v(), Triple {
                        p: q,
                        k: *pair.k(),
                        v: *pair.v(),
                    });
                })
                .allow();
                assert_eq!(tmp.len(), a.len());
                generation = a.generation().get();
                for (val, triple) in &tmp {
                    assert_eq!(val, a.get(triple.p).unwrap().v());
                    assert_eq!(triple.k, *a.get(triple.p).unwrap().k());
                }
                // fix `Ptr`s
                for (val, triple) in &tmp {
                    for set_part in b.get_mut(&triple.k).unwrap() {
                        if set_part.0 == val {
                            set_part.1.p = triple.p;
                            break;
                        }
                    }
                }
                for triple in &mut list {
                    for set_part in &b[&triple.k] {
                        if *set_part.0 == triple.v {
                            triple.p = set_part.1.p;
                            break;
                        }
                    }
                }
            }
            999 => {
                match rng.next_u32() % 4 {
                    0 => {
                        // clear_and_shrink
                        a.clear().allow();
                        // FIXME
                        generation += 1;
                    }
                    1 => {
                        // clear
                        let prev_cap = a.capacity();
                        if !a.is_empty() {
                            generation += 1;
                        }
                        a.clear().allow();
                        assert_eq!(a.capacity(), prev_cap);
                    }
                    2 => {
                        // drain
                        // TODO improve
                        generation += a.len() as u128;
                        let prev_cap = a.capacity();
                        for o in a.drain() {
                            black_box(o).allow();
                        }
                        assert_eq!(a.capacity(), prev_cap);
                    }
                    3 => {
                        // drain_capacity
                        /*for (p, k, v) in a.clone() {
                            black_box((p, k, v));
                        }
                        if !a.is_empty() {
                            generation += 1;
                        }
                        a.clear();*/
                        a.clear().allow();
                        // FIXME
                        generation += 1;
                    }
                    _ => unreachable!(),
                }
                b.clear();
                list.clear();
            }
            _ => unreachable!(),
        }
        max_len = std::cmp::max(max_len, a.len());
    }
}
