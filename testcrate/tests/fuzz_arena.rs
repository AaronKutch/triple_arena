use std::collections::{HashMap, HashSet};

use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use testcrate::P0;
use triple_arena::{utils::PtrGen, Advancer, Arena, Ptr};

const N: usize = if cfg!(miri) { 1000 } else { 1_000_000 };

const STATS: (usize, usize, u128) = if cfg!(miri) {
    (1, 11, 239)
} else {
    (1069, 74, 138703)
};

macro_rules! next_inx {
    ($rng:ident, $len:ident) => {
        $rng.next_u32() as usize % $len
    };
}

#[test]
fn fuzz_arena() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    // unique id for checking that the correct elements are returned
    let mut counter = 0u64;
    let mut new_t = || {
        counter += 1;
        counter
    };

    let mut a: Arena<P0, u64> = Arena::new();
    // map of all `T` and their pointers contained in the arena
    let mut b: HashMap<u64, P0> = HashMap::new();
    // list of `T`. We need this alongside the hashmap because we need random
    // indexing (and hashmaps will be prone to biases)
    let mut list: Vec<u64> = vec![];

    // these are set by the `clone_from` variants
    let mut a1: Arena<P0, u64> = Arena::new();
    let mut b1: HashMap<u64, P0> = HashMap::new();
    let mut list1: Vec<u64> = vec![];
    let mut generation = 2;

    let mut op_inx;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;
    let mut max_len = 0;

    // get invalid `Ptr` (from 0th index and not `Ptr::invalid()`)
    let invalid = a.insert(0);
    a.remove(invalid).unwrap();
    generation += 1;
    a.clear_and_shrink();
    generation += 1;

    for _ in 0..N {
        assert_eq!(b.len(), list.len());
        assert_eq!(a.len(), b.len());
        assert_eq!(a.generation().get(), generation);
        let len = list.len();
        assert_eq!(a.is_empty(), b.is_empty());
        if !cfg!(miri) {
            Arena::_check_invariants(&a).unwrap();
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
                    let mut create_ptr = None;
                    let ptr = if let Ok(ptr) = a.try_insert_with(|p| {
                        create_ptr = Some(p);
                        t
                    }) {
                        ptr
                    } else {
                        panic!()
                    };
                    assert_eq!(ptr, create_ptr.unwrap());
                    b.insert(t, ptr);
                    list.push(t);
                } else {
                    let create = |_p: P0| unreachable!();
                    assert!(a.try_insert_with(create).is_err());
                }
            }
            100..=149 => {
                // insert
                let t = new_t();
                let ptr = a.insert(t);
                b.insert(t, ptr);
                list.push(t);
            }
            150..=199 => {
                // insert_with
                let t = new_t();
                let mut create_ptr = None;
                let ptr = a.insert_with(|p| {
                    create_ptr = Some(p);
                    t
                });
                assert_eq!(ptr, create_ptr.unwrap());
                b.insert(t, ptr);
                list.push(t);
            }
            200..=399 => {
                // remove
                if len != 0 {
                    let t = list.swap_remove(next_inx!(rng, len));
                    let ptr = b.remove(&t).unwrap();
                    assert_eq!(t, a.remove(ptr).unwrap());
                    generation += 1;
                } else {
                    assert!(a.remove(invalid).is_none());
                }
            }
            400..=449 => {
                // invalidate
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    let ptr = b.remove(&t).unwrap();
                    let new_ptr = a.invalidate(ptr).unwrap();
                    generation += 1;
                    b.insert(t, new_ptr);
                    assert_eq!(t, a[new_ptr]);
                } else {
                    assert!(a.invalidate(invalid).is_none());
                }
            }
            450..=499 => {
                // replace_and_keep_gen
                if len != 0 {
                    let t0 = list.swap_remove(next_inx!(rng, len));
                    let t1 = new_t();
                    let same_ptr = b.remove(&t0).unwrap();
                    assert_eq!(t0, a.replace_and_keep_gen(same_ptr, t1).unwrap());
                    list.push(t1);
                    b.insert(t1, same_ptr);
                    assert_eq!(t1, a[same_ptr]);
                } else {
                    assert_eq!(
                        a.replace_and_keep_gen(invalid, u64::MAX).unwrap_err(),
                        u64::MAX
                    );
                }
            }
            500..=549 => {
                // replace_and_update_gen
                if len != 0 {
                    let t0 = list.swap_remove(next_inx!(rng, len));
                    let t1 = new_t();
                    let old_ptr = b.remove(&t0).unwrap();
                    let (output_t, new_ptr) = a.replace_and_update_gen(old_ptr, t1).unwrap();
                    generation += 1;
                    assert_eq!(t0, output_t);
                    list.push(t1);
                    b.insert(t1, new_ptr);
                    assert_eq!(t1, a[new_ptr]);
                    assert!(a.remove(old_ptr).is_none());
                } else {
                    assert_eq!(
                        a.replace_and_update_gen(invalid, u64::MAX).unwrap_err(),
                        u64::MAX
                    );
                }
            }
            550..=599 => {
                // swap
                if len != 0 {
                    let t0 = list[next_inx!(rng, len)];
                    let t1 = list[next_inx!(rng, len)];
                    let tmp0 = b[&t0];
                    let tmp1 = b[&t1];
                    a.swap(tmp0, tmp1).unwrap();
                    *b.get_mut(&t1).unwrap() = tmp0;
                    *b.get_mut(&t0).unwrap() = tmp1;
                } else {
                    assert!(a.swap(invalid, invalid).is_none())
                }
            }
            600..=799 => {
                // contains
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    assert!(a.contains(b[&t]));
                } else {
                    assert!(!a.contains(invalid));
                }
            }
            800..=839 => {
                // get and index
                if len != 0 {
                    let t = list[next_inx!(rng, len)];
                    assert_eq!(t, *a.get(b[&t]).unwrap());
                    assert_eq!(t, a[b[&t]]);
                } else {
                    assert!(a.get(invalid).is_none())
                }
            }
            840..=849 => {
                // get2_mut
                if len != 0 {
                    let t0 = list[next_inx!(rng, len)];
                    let t1 = list[next_inx!(rng, len)];
                    if t0 != t1 {
                        let tmp = a.get2_mut(b[&t0], b[&t1]).unwrap();
                        assert_eq!((*tmp.0, *tmp.1), (t0, t1));
                    } else {
                        assert!(a.get2_mut(b[&t0], invalid).is_none());
                        assert!(a.get2_mut(invalid, b[&t0]).is_none());
                        assert!(a.get2_mut(b[&t0], b[&t0]).is_none());
                    }
                } else {
                    assert!(a.get2_mut(invalid, invalid).is_none())
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
            900..=909 => {
                // ptrs
                let mut n = 0;
                for ptr in a.ptrs() {
                    assert_eq!(ptr, b[&a[ptr]]);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            910..=919 => {
                // vals
                let mut n = 0;
                for t in a.vals() {
                    let p = b[t];
                    assert_eq!(a[p], *t);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            920..=929 => {
                // vals_mut
                let mut n = 0;
                let tmp: Vec<u64> = a.vals_mut().map(|t| *t).collect();
                for t in tmp {
                    let p = b[&t];
                    assert_eq!(a[p], t);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            930..=939 => {
                // iter
                let mut n = 0;
                for (ptr, t) in a.iter() {
                    assert_eq!(ptr, b[t]);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            940..=949 => {
                // advancer
                let mut i = 0;
                let rand_remove_i = if len == 0 { 0 } else { next_inx!(rng, len) };
                let rand_insert_i = if len == 0 { 0 } else { next_inx!(rng, len) };
                let mut adv = a.advancer();
                while let Some(p) = adv.advance(&a) {
                    assert_eq!(p, b[&a[p]]);

                    // remove and insert at random times
                    if i == rand_insert_i {
                        let t = new_t();
                        let ptr = a.insert(t);
                        b.insert(t, ptr);
                        list.push(t);
                    }
                    if i == rand_remove_i {
                        let t = list.swap_remove(rand_remove_i);
                        let ptr = b.remove(&t).unwrap();
                        assert_eq!(t, a.remove(ptr).unwrap());
                        generation += 1;
                    }
                    i += 1;
                }
                // depends on the invalidated elements witnessed
                assert!((i == len.saturating_sub(1)) || (i == len) || (i == (len + 1)));
            }
            950..=991 => {
                // iter_mut
                let mut n = 0;
                for (ptr, t) in a.iter_mut() {
                    assert_eq!(ptr, b[t]);
                    n += 1;
                }
                assert_eq!(n, list.len());
            }
            992 => {
                // compress_and_shrink
                a.compress_and_shrink();
                assert_eq!(a.capacity(), a.len());
                generation += 1;
                // for this base test, manually recast `Ptr`s
                for (p, t) in a.iter() {
                    *b.get_mut(t).unwrap() = p;
                }
            }
            993 => {
                // compress_and_shrink_with
                let mut tmp = HashMap::new();
                let q_gen = PtrGen::increment(a.generation());
                a.compress_and_shrink_with(|p, t, q| {
                    assert_eq!(b[t], p);
                    assert_eq!(q_gen, q.generation());
                    tmp.insert(*t, q);
                });
                assert_eq!(tmp.len(), a.len());
                assert_eq!(a.capacity(), a.len());
                generation += 1;
                for (t, p) in tmp {
                    assert_eq!(t, a[p]);
                }
                // for this base test, manually recast `Ptr`s
                for (p, t) in a.iter() {
                    assert_eq!(q_gen, p.generation());
                    *b.get_mut(t).unwrap() = p;
                }
            }
            994 => {
                // clone_from variants. these are mainly tested in `multi_arena`, but we want
                // them here to test if `self.m.len()` and `self.m.capacity()` detachments cause
                // issues.
                match rng.next_u32() % 4 {
                    0 => {
                        a.clone_from(&a1);
                        generation = a1.generation().get();
                        b.clone_from(&b1);
                        list.clone_from(&list1);
                    }
                    1 => {
                        a.clone_from_with(&a1, |p, u| {
                            assert_eq!(b1[u], p);
                            *u
                        });
                        generation = a1.generation().get();
                        b.clone_from(&b1);
                        list.clone_from(&list1);
                    }
                    // `a1` and the like are set here, `a` will diverge again
                    2 => {
                        a1.clone_from(&a);
                        b1.clone_from(&b);
                        list1.clone_from(&list);
                    }
                    3 => {
                        a1.clone_from_with(&a, |p, u| {
                            assert_eq!(b[u], p);
                            *u
                        });
                        b1.clone_from(&b);
                        list1.clone_from(&list);
                    }
                    _ => unreachable!(),
                }
            }
            // The following reset the length so we can reexplore small cases.
            // Because of exponential probabilities, these need to be rare.
            995 => {
                // remove_by and `PartialEq` false cases
                if len != 0 {
                    let mut remove = HashSet::new();
                    let num_rm = next_inx!(rng, len);
                    for _ in 0..num_rm {
                        remove.insert(list.swap_remove((rng.next_u32() as usize) % list.len()));
                    }
                    let a_clone = a.clone();
                    a.remove_by(|ptr, t| {
                        if remove.contains(t) {
                            remove.remove(t);
                            assert_eq!(ptr, b.remove(t).unwrap());
                            true
                        } else {
                            false
                        }
                    });
                    if num_rm > 0 {
                        assert_ne!(a_clone, a);
                        // make sure there are no assymetry related problems due to the
                        // implementation
                        assert_ne!(a, a_clone);
                    } else {
                        assert_eq!(a_clone, a);
                        assert_eq!(a, a_clone);
                    }
                    generation += 1;
                    assert!(remove.is_empty());
                }
            }
            996 => {
                // capacity_drain via the `IntoIter` impl, and `PartialEq` true cases
                let a_clone = a.clone();
                assert_eq!(a_clone, a);
                // make sure there are no assymetry related problems due to the implementation
                assert_eq!(a, a_clone);
                for (ptr, t) in a_clone {
                    assert_eq!(b[&t], ptr);
                }
            }
            997 => {
                // drain
                let prev_cap = a.capacity();
                for (ptr, t) in a.drain() {
                    assert_eq!(b.remove(&t).unwrap(), ptr);
                }
                generation += 1;
                list.clear();
                assert_eq!(a.capacity(), prev_cap);
            }
            998 => {
                // clear
                a.clear();
                generation += 1;
                list.clear();
                b.clear();
            }
            999 => {
                // clear_and_shrink
                a.clear_and_shrink();
                assert_eq!(a.capacity(), 0);
                generation += 1;
                list.clear();
                b.clear();
                iters999 += 1;
            }
            _ => unreachable!(),
        }
        max_len = std::cmp::max(max_len, a.len());
    }
    // I may need a custom allocator, because some of the determinism is dependent
    // on the interactions between `reserve` and `try_insert`
    assert_eq!((iters999, max_len, a.generation().get()), STATS);
}

const M: usize = if cfg!(miri) { 1000 } else { 100_000 };

const STATS_2: (usize, u128) = if cfg!(miri) { (23, 450) } else { (77, 46957) };

// for testing `clone` and `clone_from` which interact between multiple arenas
#[test]
fn fuzz_multi_arena() {
    fn inner(
        rng: &mut Xoshiro128StarStar,
        a: &mut Arena<P0, u64>,
        generation: &mut u128,
        b: &mut HashMap<u64, P0>,
        list: &mut Vec<u64>,
        new_t: &mut dyn FnMut() -> u64,
    ) {
        assert_eq!(b.len(), list.len());
        assert_eq!(a.len(), b.len());
        assert_eq!(a.generation().get(), *generation);
        assert_eq!(a.is_empty(), b.is_empty());
        if !cfg!(miri) {
            Arena::_check_invariants(a).unwrap();
        }
        let len = a.len();
        match rng.next_u32() % 1000 {
            0..=499 => {
                // insert
                let t = new_t();
                let ptr = a.insert(t);
                b.insert(t, ptr);
                list.push(t);
            }
            500..=997 => {
                // remove
                if len != 0 {
                    let t = list.swap_remove(next_inx!(rng, len));
                    let ptr = b.remove(&t).unwrap();
                    assert_eq!(t, a.remove(ptr).unwrap());
                    *generation += 1;
                }
            }
            998 => {
                // clear
                let prev_cap = a.capacity();
                a.clear();
                assert_eq!(a.capacity(), prev_cap);
                *generation += 1;
                list.clear();
                b.clear();
            }
            999 => {
                // clear_and_shrink
                a.clear_and_shrink();
                assert_eq!(a.capacity(), 0);
                *generation += 1;
                list.clear();
                b.clear();
            }
            _ => unreachable!(),
        }
    }

    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    // unique id for checking that the correct elements are returned
    let mut counter = 0u64;
    let mut new_t = || {
        counter += 1;
        counter
    };

    let mut a0: Arena<P0, u64> = Arena::new();
    let mut a1: Arena<P0, u64> = Arena::new();
    let mut gen0 = 2;
    let mut gen1 = 2;

    // map of all `T` and their pointers contained in the arena
    let mut b0: HashMap<u64, P0> = HashMap::new();
    let mut b1: HashMap<u64, P0> = HashMap::new();

    // list of `T`. We need this alongside the hashmap because we need random
    // indexing (and hashmaps will be prone to biases)
    let mut list0: Vec<u64> = vec![];
    let mut list1: Vec<u64> = vec![];
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut max_len0 = 0;

    for _ in 0..M {
        inner(
            &mut rng, &mut a0, &mut gen0, &mut b0, &mut list0, &mut new_t,
        );
        inner(
            &mut rng, &mut a1, &mut gen1, &mut b1, &mut list1, &mut new_t,
        );
        max_len0 = std::cmp::max(max_len0, a0.len());
        match rng.next_u32() % 1000 {
            // do no major operations most of the time, rack up some random insertions and removals
            // in `inner`
            0..=899 => (),
            // clone_from
            900..=924 => {
                a0.clone_from(&a1);
                gen0 = gen1;
                b0.clone_from(&b1);
                list0.clone_from(&list1);
            }
            925..=949 => {
                a1.clone_from(&a0);
                gen1 = gen0;
                b1.clone_from(&b0);
                list1.clone_from(&list0);
            }
            // clone_from_with
            950..=974 => {
                a0.clone_from_with(&a1, |p, u| {
                    assert_eq!(b1[u], p);
                    *u
                });
                gen0 = gen1;
                b0.clone_from(&b1);
                list0.clone_from(&list1);
            }
            975..=999 => {
                a1.clone_from_with(&a0, |p, u| {
                    assert_eq!(b0[u], p);
                    *u
                });
                gen1 = gen0;
                b1.clone_from(&b0);
                list1.clone_from(&list0);
            }
            _ => unreachable!(),
        }
    }
    assert_eq!((max_len0, a0.generation().get()), STATS_2);
}
