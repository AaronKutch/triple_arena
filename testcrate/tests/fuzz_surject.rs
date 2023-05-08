use std::{
    cmp::max,
    collections::{HashMap, HashSet},
};

use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use triple_arena::{ptr_struct, SurjectArena};

macro_rules! next_inx {
    ($rng:ident, $len:ident) => {
        $rng.next_u32() as usize % $len
    };
}

ptr_struct!(P0);

#[test]
fn fuzz_surject() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    // unique id for checking that the correct elements are returned
    let mut counter = 0u64;
    let mut new_t = || {
        counter += 1;
        counter
    };

    let mut list: Vec<u64> = vec![];

    let mut a: SurjectArena<P0, u64> = SurjectArena::new();
    let mut gen = 2;
    let mut b: HashMap<u64, HashSet<P0>> = HashMap::new();

    let invalid = a.insert_val(u64::MAX);
    a.remove(invalid).unwrap();
    gen += 1;
    a.clear_and_shrink();
    gen += 1;
    let mut op_inx = u32::MAX;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;
    let mut max_key_len = 0;
    let mut max_val_len = 0;

    for _ in 0..1_000_000 {
        let mut len_keys = 0;
        for set in b.values() {
            len_keys += set.len();
        }
        assert_eq!(a.len_keys(), len_keys);
        assert_eq!(a.len_vals(), b.len());
        if a.gen().get() != gen {
            dbg!(a.gen().get(), gen, op_inx);
            panic!();
        }
        assert_eq!(a.gen().get(), gen);
        assert_eq!(a.is_empty(), list.is_empty());
        let len = list.len();
        if let Err(e) = SurjectArena::_check_invariants(&a) {
            dbg!(op_inx);
            panic!("{e}");
        }
        op_inx = rng.next_u32() % 1000;
        match op_inx {
            0..=997 => (),
            998 => {
                // clear
                a.clear();
                gen += 1;
                list.clear();
            }
            999 => {
                // clear_and_shrink
                a.clear_and_shrink();
                gen += 1;
                list.clear();
                iters999 += 1;
            }
            _ => unreachable!(),
        }
        max_key_len = max(max_key_len, a.len_keys());
        max_val_len = max(max_val_len, a.len_vals());
    }
    assert_eq!(
        (max_key_len, max_val_len, iters999, a.gen().get()),
        (0, 0, 0, 0)
    );
}
