use rand_xoshiro::{rand_core::SeedableRng, Xoshiro128StarStar};
use testcrate::{fuzz_fill_inst, get_cmp_count, CKey, CVal, A, P1};
use triple_arena::OrdArena;

fn get_std_insts() -> Vec<Result<(CKey, CVal), usize>> {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    // we fill the arena up to `A` elements, then randomly insert and remove the
    // same number of `B` elements, then empty it in the same random way
    let (mut insts, sim) = fuzz_fill_inst(&mut rng, &[], 2 * A, A);
    let tmp = fuzz_fill_inst(&mut rng, &sim, A, A);
    insts.extend_from_slice(&tmp.0);
    let tmp = fuzz_fill_inst(&mut rng, &tmp.1, A, 2 * A);
    insts.extend_from_slice(&tmp.0);
    assert!(tmp.1.is_empty());
    insts
}

#[test]
fn ord_arena_count() {
    let mut a = OrdArena::<P1, CKey, CVal>::new();
    let mut repr_inxs = vec![];
    let insts = get_std_insts();
    for inst in insts {
        match inst {
            Ok((k, v)) => {
                repr_inxs.push(a.insert(k, v).0);
            }
            Err(inx) => {
                a.remove(repr_inxs.swap_remove(inx)).unwrap();
            }
        }
    }
    assert_eq!(get_cmp_count(), if cfg!(miri) { 208 } else { 83611 });
}

#[test]
fn ord_arena_find_to_remove_count() {
    let mut a = OrdArena::<P1, CKey, CVal>::new();
    let mut repr_keys = vec![];
    let insts = get_std_insts();
    for inst in insts {
        match inst {
            Ok((k, v)) => {
                repr_keys.push(k.clone_uncounting());
                let _ = a.insert(k, v);
            }
            Err(inx) => {
                let key = repr_keys.swap_remove(inx);
                let p = a.find_key(&key).unwrap();
                a.remove(p).unwrap();
            }
        }
    }
    assert_eq!(get_cmp_count(), if cfg!(miri) { 395 } else { 159913 });
}

// in case the implementation of `BTreeMap` changes, do not want to break CI or
// crater
/*
#[test]
fn std_btree_count() {
    let mut a = std::collections::BTreeMap::<CKey, CVal>::new();
    let mut repr_keys = vec![];
    let insts = get_std_insts();
    for inst in insts {
        match inst {
            Ok(pair) => {
                repr_keys.push(pair.0.clone_uncounting());
                let _ = a.insert(pair.0, pair.1);
            }
            Err(inx) => {
                let key = repr_keys.swap_remove(inx);
                a.remove(&key).unwrap();
            }
        }
    }
    assert_eq!(get_cmp_count(), 234337);
}
*/
