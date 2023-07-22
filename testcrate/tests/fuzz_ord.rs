use std::collections::BTreeMap;

use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use testcrate::P0;
use triple_arena::OrdArena;

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
            println!("{}", a.debug());
            dbg!(last_i);
            panic!();*/
            panic!("{e}");
        }
        //println!("i: {i}");

        op_inx = rng.next_u32() % 1000;
        match op_inx {
            // note: we give slightly more single inserts than single removes to encourage larger
            // trees
            0..=104 => {
                // insert_nonhereditary
                let k = new_k();
                let v = new_v();
                let p = a.insert_nonhereditary(k, v);
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
                    //dbg!(t.p);
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
            200..=997 => {
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
