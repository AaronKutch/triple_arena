use std::collections::{HashMap, HashSet};

use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use triple_arena::{ptr_trait_struct_with_gen, Arena, Ptr};

macro_rules! next_inx {
    ($rng:ident, $len:ident) => {
        $rng.next_u32() as usize % $len
    };
}

ptr_trait_struct_with_gen!(P0);

#[test]
fn fuzz() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    // unique id for checking that the correct elements are returned
    let mut counter = 0u64;
    let mut new_t = || {
        counter += 1;
        counter
    };

    let mut a: Arena<u64, P0> = Arena::new();
    // map of all `T` and their pointers contained in the arena
    let mut b: HashMap<u64, Ptr<P0>> = HashMap::new();
    // list of `T`. We need this alongside the hashmap because we need random
    // indexing (and hashmaps will be prone to biases)
    let mut list: Vec<u64> = vec![];
    let mut op_inx = 1000;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;
    let mut max_len = 0;

    // get invalid pointer
    let invalid = a.insert(0);
    a.remove(invalid);
    a.clear_and_shrink();

    for _ in 0..1_000_000 {
        assert_eq!(b.len(), list.len());
        assert_eq!(a.len(), b.len());
        let len = list.len();
        assert_eq!(a.is_empty(), b.is_empty());
        let check = Arena::_check_arena_invariants(&a);
        if check.is_err() {
            dbg!(op_inx);
            check.unwrap();
        }
        op_inx = rng.next_u32() % 1000;
        // I am only using inclusive ranges because exclusive ones are not stable as of
        // writing
        match op_inx {
            0 => {
                // reserve
                a.reserve((rng.next_u32() % 8) as usize);
            }
            1..=49 => {
                // try_insert
                if a.len() < a.capacity() {
                    let t = new_t();
                    let ptr = a.try_insert(t).unwrap();
                    b.insert(t, ptr);
                    list.push(t);
                } else {
                    let t = new_t();
                    assert_eq!(a.try_insert(t), Err(t));
                }
            }
            50..=99 => {
                // try_insert_with
                if a.len() < a.capacity() {
                    let t = new_t();
                    let ptr = if let Ok(ptr) = a.try_insert_with(|| t) {
                        ptr
                    } else {
                        panic!()
                    };
                    b.insert(t, ptr);
                    list.push(t);
                } else {
                    let t = new_t();
                    let create = || t;
                    assert!(a.try_insert(create()) == Err(create()));
                }
            }
            100..=199 => {
                // insert
                let t = new_t();
                let ptr = a.insert(t);
                b.insert(t, ptr);
                list.push(t);
            }
            200..=399 => {
                // remove
                if len != 0 {
                    let t = list.swap_remove(next_inx!(rng, len));
                    let ptr = b.remove(&t).unwrap();
                    assert_eq!(t, a.remove(ptr).unwrap());
                } else {
                    assert!(a.remove(invalid).is_none());
                }
            }
            // TODO test failure cases
            400..=799 => {
                // contains
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    assert!(a.contains(b[&t]));
                } else {
                    assert!(!a.contains(invalid));
                }
            }
            800..=849 => {
                // get and index
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    assert_eq!(t, *a.get(b[&t]).unwrap());
                    assert_eq!(t, a[b[&t]]);
                } else {
                    assert!(a.get(invalid).is_none())
                }
            }
            850..=899 => {
                // get_mut and index_mut
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    assert_eq!(t, *a.get_mut(b[&t]).unwrap());
                    let tmp: &mut u64 = &mut a[b[&t]];
                    assert_eq!(t, *tmp);
                } else {
                    assert!(a.get_mut(invalid).is_none())
                }
            }
            900..=949 => {
                // iter
                let mut n = 0;
                for (ptr, t) in a.iter() {
                    assert_eq!(ptr, b[t]);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            950..=995 => {
                // iter_mut
                let mut n = 0;
                for (ptr, t) in a.iter_mut() {
                    assert_eq!(ptr, b[t]);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            // The following reset the length so we can reexplore small cases.
            // Because of exponential probabilities, these need to be rare.
            996 => {
                // remove_by
                if len != 0 {
                    let mut remove = HashSet::new();
                    for _ in 0..next_inx!(rng, len) {
                        remove.insert(list.swap_remove((rng.next_u32() as usize) % list.len()));
                    }
                    a.remove_by(|(ptr, t)| {
                        if remove.contains(t) {
                            remove.remove(t);
                            assert_eq!(ptr, b.remove(t).unwrap());
                            true
                        } else {
                            false
                        }
                    });
                    assert!(remove.is_empty());
                }
            }
            997 => {
                // drain
                for (ptr, t) in a.drain() {
                    assert_eq!(b.remove(&t).unwrap(), ptr);
                }
                list.clear();
                assert_eq!(a.capacity(), 0);
            }
            998 => {
                // clear
                a.clear_and_shrink();
                list.clear();
                b.clear();
            }
            999 => {
                // clear_and_shrink
                a.clear_and_shrink();
                list.clear();
                b.clear();
                iters999 += 1;
            }
            _ => unreachable!(),
        }
        max_len = std::cmp::max(max_len, a.len());
    }
    assert_eq!(iters999, 1061);
    assert_eq!(max_len, 81);
}
