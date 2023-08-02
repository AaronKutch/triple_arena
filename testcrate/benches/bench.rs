#![feature(test)]

extern crate test;
use std::collections::BTreeMap;

use rand_xoshiro::{rand_core::SeedableRng, Xoshiro128StarStar};
use test::Bencher;
use testcrate::{fuzz_fill_inst_bench, P1};
use triple_arena::{Arena, OrdArena};

const A: u64 = B << 1;
const B: u64 = 1 << 11;

fn get_std_insts() -> Vec<Result<(u128, u128), usize>> {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    // we fill the arena up to `A` elements, then randomly insert and remove the
    // same number of `B` elements, then empty it in the same random way
    let (mut insts, sim) = fuzz_fill_inst_bench(&mut rng, &[], A, B);
    let tmp = fuzz_fill_inst_bench(&mut rng, &sim, B, B);
    insts.extend_from_slice(&tmp.0);
    let tmp = fuzz_fill_inst_bench(&mut rng, &tmp.1, B, A);
    insts.extend_from_slice(&tmp.0);
    assert!(tmp.1.is_empty());
    insts
}

// simulates approximately what a perfect arena with no extra checks and the
// same size of data could achieve
#[bench]
fn baseline(bencher: &mut Bencher) {
    let mut a = vec![];
    let mut repr_inxs = vec![];

    bencher.iter(|| {
        let insts = get_std_insts();
        for inst in insts {
            match inst {
                Ok(pair) => {
                    a.push(pair);
                    repr_inxs.push(pair.0);
                }
                Err(inx) => {
                    a.swap_remove(inx);
                    repr_inxs.swap_remove(inx);
                }
            }
        }
    })
}

#[bench]
fn arena(bencher: &mut Bencher) {
    let mut a = Arena::<P1, (u128, u128)>::new();
    let mut repr_inxs = vec![];

    bencher.iter(|| {
        let insts = get_std_insts();
        for inst in insts {
            match inst {
                Ok(pair) => {
                    repr_inxs.push(a.insert(pair));
                }
                Err(inx) => {
                    a.remove(repr_inxs.swap_remove(inx)).unwrap();
                }
            }
        }
    })
}

#[bench]
fn std_btree(bencher: &mut Bencher) {
    let mut a = BTreeMap::<u128, u128>::new();
    let mut repr_inxs = vec![];

    bencher.iter(|| {
        let insts = get_std_insts();
        for inst in insts {
            match inst {
                Ok(pair) => {
                    repr_inxs.push(pair.0);
                    a.insert(pair.0, pair.1);
                }
                Err(inx) => {
                    a.remove(&repr_inxs.swap_remove(inx)).unwrap();
                }
            }
        }
    })
}

// compare this against `std_btree`, since it finds the value to remove by key
#[bench]
fn ord_arena_find_to_remove(bencher: &mut Bencher) {
    let mut a = OrdArena::<P1, u128, u128>::new();
    let mut repr_inxs = vec![];

    bencher.iter(|| {
        let insts = get_std_insts();
        for inst in insts {
            match inst {
                Ok(pair) => {
                    repr_inxs.push(pair.0);
                    let _ = a.insert(pair);
                }
                Err(inx) => {
                    let key = repr_inxs.swap_remove(inx);
                    let p = a.find_key(&key).unwrap();
                    a.remove(p).unwrap();
                }
            }
        }
    })
}

#[bench]
fn ord_arena(bencher: &mut Bencher) {
    let mut a = OrdArena::<P1, u128, u128>::new();
    let mut repr_inxs = vec![];

    bencher.iter(|| {
        let insts = get_std_insts();
        for inst in insts {
            match inst {
                Ok(pair) => {
                    repr_inxs.push(a.insert(pair).0);
                }
                Err(inx) => {
                    a.remove(repr_inxs.swap_remove(inx)).unwrap();
                }
            }
        }
    })
}
