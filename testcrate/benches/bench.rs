#![feature(test)]

// TODO: rework these benchmarks, can I make the iter work over all the
// individual loop steps?

extern crate test;
use std::{collections::BTreeMap, hint::black_box};

use rand_xoshiro::{rand_core::SeedableRng, Xoshiro128StarStar};
use test::Bencher;
use testcrate::{fuzz_fill_inst_bench, get_next_seed, A, P1};
use triple_arena::{Arena, OrdArena};

fn get_std_bench_insts(seed: u64) -> Vec<Result<(u128, u128), usize>> {
    let mut rng = Xoshiro128StarStar::seed_from_u64(seed);
    // we fill the arena up to `A` elements, then randomly insert and remove the
    // same number of `B` elements, then empty it in the same random way
    let (mut insts, sim) = fuzz_fill_inst_bench(&mut rng, &[], 2 * A, A);
    let tmp = fuzz_fill_inst_bench(&mut rng, &sim, A, A);
    insts.extend_from_slice(&tmp.0);
    let tmp = fuzz_fill_inst_bench(&mut rng, &tmp.1, A, 2 * A);
    insts.extend_from_slice(&tmp.0);
    assert!(tmp.1.is_empty());
    insts
}

fn get_insert_insts(seed: u64) -> Vec<(u128, u128)> {
    let mut rng = Xoshiro128StarStar::seed_from_u64(seed);
    let (insts, _) = fuzz_fill_inst_bench(&mut rng, &[], 8 * A, 0);
    insts.into_iter().map(|r| r.unwrap()).collect()
}

fn get_remove_insts(seed: u64) -> Vec<usize> {
    // must be the same opening as `get_insert_insts`
    let mut rng = Xoshiro128StarStar::seed_from_u64(seed);
    let (_, sim) = fuzz_fill_inst_bench(&mut rng, &[], 8 * A, 0);
    let (insts, _) = fuzz_fill_inst_bench(&mut rng, &sim, 0, 8 * A);
    insts.into_iter().map(|r| r.unwrap_err()).collect()
}

// simulates approximately what a perfect arena with no extra checks and the
// same size of data could achieve
#[bench]
fn baseline(bencher: &mut Bencher) {
    bencher.iter(|| {
        let mut a: Vec<(u128, u128)> = vec![];
        let mut repr_inxs: Vec<u128> = vec![];
        let insts = get_std_bench_insts(get_next_seed());
        for inst in &insts {
            match inst {
                Ok(pair) => {
                    a.push(*pair);
                    repr_inxs.push(pair.0);
                }
                Err(inx) => {
                    a.swap_remove(*inx);
                    repr_inxs.swap_remove(*inx);
                }
            }
        }
    })
}

#[bench]
fn arena(bencher: &mut Bencher) {
    bencher.iter(|| {
        let mut a = Arena::<P1, (u128, u128)>::new();
        let mut repr_inxs: Vec<P1> = vec![];
        let insts = get_std_bench_insts(get_next_seed());
        for inst in &insts {
            match inst {
                Ok(pair) => {
                    repr_inxs.push(a.insert(*pair));
                }
                Err(inx) => {
                    a.remove(repr_inxs.swap_remove(*inx)).unwrap();
                }
            }
        }
    })
}

#[bench]
fn std_bench_std_btree(bencher: &mut Bencher) {
    bencher.iter(|| {
        let mut a = BTreeMap::<u128, u128>::new();
        let mut repr_keys: Vec<u128> = vec![];
        let insts = get_std_bench_insts(get_next_seed());
        for inst in &insts {
            match inst {
                Ok(pair) => {
                    repr_keys.push(pair.0);
                    a.insert(pair.0, pair.1);
                }
                Err(inx) => {
                    a.remove(&repr_keys.swap_remove(*inx)).unwrap();
                }
            }
        }
    })
}

// compare this against `std_btree`, since it finds the value to remove by key
#[bench]
fn std_bench_ord_arena_find_to_remove(bencher: &mut Bencher) {
    bencher.iter(|| {
        let mut a = OrdArena::<P1, u128, u128>::new();
        let mut repr_keys: Vec<u128> = vec![];
        let insts = get_std_bench_insts(get_next_seed());
        for inst in &insts {
            match inst {
                Ok((k, v)) => {
                    repr_keys.push(*k);
                    let _ = a.insert(*k, *v);
                }
                Err(inx) => {
                    let key = repr_keys.swap_remove(*inx);
                    let p = a.find_key(&key).unwrap();
                    a.remove(p).unwrap();
                }
            }
        }
    })
}

#[bench]
fn std_bench_ord_arena(bencher: &mut Bencher) {
    bencher.iter(|| {
        let mut a = OrdArena::<P1, u128, u128>::new();
        let mut repr_inxs: Vec<P1> = vec![];
        let insts = get_std_bench_insts(get_next_seed());
        for inst in &insts {
            match inst {
                Ok((k, v)) => {
                    repr_inxs.push(a.insert(*k, *v).0);
                }
                Err(inx) => {
                    a.remove(repr_inxs.swap_remove(*inx)).unwrap();
                }
            }
        }
    })
}

#[bench]
fn insert_only_std_btree(bencher: &mut Bencher) {
    bencher.iter(|| {
        let mut a = BTreeMap::<u128, u128>::new();
        let insts = get_insert_insts(get_next_seed());
        for inst in &insts {
            a.insert(inst.0, inst.1);
        }
    })
}

#[bench]
fn insert_only_ord_arena(bencher: &mut Bencher) {
    bencher.iter(|| {
        let mut a = OrdArena::<P1, u128, u128>::new();
        let insts = get_insert_insts(get_next_seed());
        for (k, v) in &insts {
            let _ = a.insert(*k, *v);
        }
    })
}

#[bench]
fn find_only_std_btree(bencher: &mut Bencher) {
    bencher.iter(|| {
        let mut a = BTreeMap::<u128, u128>::new();
        let insts = get_insert_insts(get_next_seed());
        let mut repr_keys: Vec<u128> = vec![];
        for inst in &insts {
            a.insert(inst.0, inst.1);
            repr_keys.push(inst.0);
        }
        for key in &repr_keys {
            let tmp = a.get(key).unwrap();
            let _ = black_box(tmp);
        }
    })
}

#[bench]
fn find_only_ord_arena(bencher: &mut Bencher) {
    bencher.iter(|| {
        let mut a = OrdArena::<P1, u128, u128>::new();
        let insts = get_insert_insts(get_next_seed());
        let mut repr_keys: Vec<u128> = vec![];
        for (k, v) in &insts {
            let _ = a.insert(*k, *v);
            repr_keys.push(*k);
        }
        for key in &repr_keys {
            let tmp = a.find_key(key).unwrap();
            let _ = black_box(tmp);
        }
    })
}

#[bench]
fn remove_only_std_btree(bencher: &mut Bencher) {
    bencher.iter(|| {
        let mut a = BTreeMap::<u128, u128>::new();
        let insts = get_insert_insts(get_next_seed());
        let mut repr_keys: Vec<u128> = vec![];
        for (k, v) in &insts {
            repr_keys.push(*k);
            a.insert(*k, *v);
        }
        let insts = get_remove_insts(get_next_seed());
        for inst in &insts {
            a.remove(&repr_keys.swap_remove(*inst)).unwrap();
        }
    })
}

#[bench]
fn remove_only_ord_arena(bencher: &mut Bencher) {
    bencher.iter(|| {
        let mut a = OrdArena::<P1, u128, u128>::new();
        let insts = get_insert_insts(get_next_seed());
        let mut repr_inxs: Vec<P1> = vec![];
        for (k, v) in &insts {
            repr_inxs.push(a.insert(*k, *v).0);
        }
        let insts = get_remove_insts(get_next_seed());
        for inst in &insts {
            a.remove(repr_inxs.swap_remove(*inst)).unwrap();
        }
    })
}
