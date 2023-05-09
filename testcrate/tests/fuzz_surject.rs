use std::{cmp::max, collections::HashMap};

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
    let mut b: HashMap<u64, Vec<P0>> = HashMap::new();

    let invalid = a.insert_val(u64::MAX);
    a.remove_key(invalid).unwrap();
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
        assert_eq!(a.len_keys(), list.len());
        assert_eq!(a.len_vals(), b.len());
        let len = list.len();
        let mut len_keys = 0;
        for set in b.values() {
            assert!(!set.is_empty());
            let set_len = set.len();
            assert_eq!(
                set.len(),
                a.len_key_set(set[next_inx!(rng, set_len)]).unwrap().get()
            );
            len_keys += set_len;
        }
        assert_eq!(a.len_keys(), len_keys);
        if a.gen().get() != gen {
            dbg!(a.gen().get(), gen, op_inx);
            panic!();
        }
        assert_eq!(a.gen().get(), gen);
        assert_eq!(a.is_empty(), list.is_empty());
        if let Err(e) = SurjectArena::_check_invariants(&a) {
            dbg!(op_inx);
            panic!("{e}");
        }
        op_inx = rng.next_u32() % 1000;
        match op_inx {
            0..=24 => {
                // insert_val
                let t = new_t();
                let p = a.insert_val(t);
                list.push(t);
                b.insert(t, vec![p]);
            }
            25..=99 => {
                // insert_key
            }
            100..=124 => {
                // remove_val
                if len != 0 {
                    let t = list.swap_remove(next_inx!(rng, len));
                    let set = b.remove(&t).unwrap();
                    let set_len = set.len();
                    a.remove_val(set[next_inx!(rng, set_len)]);
                    gen += 1;
                } else {
                    assert!(a.remove_val(invalid).is_none());
                }
            }
            125..=199 => {
                // remove_key
            }
            200..=249 => {
                // contains
            }
            250..=299 => {
                // in_same_set
            }
            // get
            300..=997 => {}
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
        max_key_len = max(max_key_len, a.len_keys());
        max_val_len = max(max_val_len, a.len_vals());
    }
    assert_eq!(
        (max_key_len, max_val_len, iters999, a.gen().get()),
        (0, 0, 0, 0)
    );
}
