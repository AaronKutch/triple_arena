use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use testcrate::{fuzz_fill_inst, CKey, CVal, A, P1};
use triple_arena::{Arena, ChainArena, OrdArena, SurjectArena};

#[test]
fn test_inst_framework() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    let mut a = Arena::<P1, (CKey, CVal)>::new();
    let mut repr = vec![];
    let mut repr_inxs = vec![];
    let (insts, expected) = fuzz_fill_inst(&mut rng, &repr, 2 * A, A);
    for inst in insts {
        match inst {
            Ok(pair) => {
                repr.push((pair.0.clone_uncounting(), pair.1.clone_uncounting()));
                repr_inxs.push(a.insert(pair));
            }
            Err(inx) => {
                a.remove(repr_inxs.swap_remove(inx)).unwrap();
                repr.swap_remove(inx);
            }
        }
    }
    assert_eq!(repr, expected);
}

fn std_arena() -> Arena<P1, (CKey, CVal)> {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    let mut a = Arena::<P1, (CKey, CVal)>::new();
    let mut repr = vec![];
    let mut repr_inxs = vec![];
    let (mut insts, expected) = fuzz_fill_inst(&mut rng, &repr, 3 * A, A);
    let tmp = fuzz_fill_inst(&mut rng, &expected, 2 * A, 3 * A);
    insts.extend_from_slice(&tmp.0);
    for inst in insts {
        match inst {
            Ok(pair) => {
                repr.push((pair.0.clone_uncounting(), pair.1.clone_uncounting()));
                repr_inxs.push(a.insert(pair));
            }
            Err(inx) => {
                a.remove(repr_inxs.swap_remove(inx)).unwrap();
                repr.swap_remove(inx);
            }
        }
    }
    // need empty entries
    assert_eq!(a.len(), A as usize);
    assert!(a.capacity() >= (2 * A as usize));
    a
}

fn std_chain() -> ChainArena<P1, (CKey, CVal)> {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    let mut a = ChainArena::<P1, (CKey, CVal)>::new();
    let mut repr = vec![];
    let mut repr_inxs = vec![];
    let (mut insts, expected) = fuzz_fill_inst(&mut rng, &repr, 3 * A, A);
    let tmp = fuzz_fill_inst(&mut rng, &expected, 2 * A, 3 * A);
    insts.extend_from_slice(&tmp.0);
    for inst in insts {
        match inst {
            Ok(pair) => {
                repr.push((pair.0.clone_uncounting(), pair.1.clone_uncounting()));
                repr_inxs.push(a.insert_new_cyclic(pair));
            }
            Err(inx) => {
                a.remove(repr_inxs.swap_remove(inx)).unwrap();
                repr.swap_remove(inx);
            }
        }
    }
    let ptrs: Vec<P1> = a.ptrs().collect();
    let len = ptrs.len();
    // randomly connect
    for _ in 0..A {
        let p0 = ptrs[(rng.next_u64() as usize) % len];
        let p1 = ptrs[(rng.next_u64() as usize) % len];
        a.exchange_next(p0, p1).unwrap();
    }
    assert_eq!(a.len(), A as usize);
    assert!(a.capacity() >= (2 * A as usize));
    a
}

fn std_surject() -> SurjectArena<P1, CKey, CVal> {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    let mut a = SurjectArena::<P1, CKey, CVal>::new();
    let mut repr = vec![];
    let mut repr_inxs = vec![];
    let (mut insts, expected) = fuzz_fill_inst(&mut rng, &repr, 3 * A, A);
    let tmp = fuzz_fill_inst(&mut rng, &expected, 2 * A, 3 * A);
    insts.extend_from_slice(&tmp.0);
    for inst in insts {
        match inst {
            Ok(pair) => {
                repr.push((pair.0.clone_uncounting(), pair.1.clone_uncounting()));
                repr_inxs.push(a.insert(pair.0, pair.1));
            }
            Err(inx) => {
                a.remove(repr_inxs.swap_remove(inx)).unwrap();
                repr.swap_remove(inx);
            }
        }
    }
    let ptrs: Vec<P1> = a.ptrs().collect();
    let len = ptrs.len();
    // randomly union, go for `A` rounds since a lot will go to the same set
    for _ in 0..A {
        let p0 = ptrs[(rng.next_u64() as usize) % len];
        let p1 = ptrs[(rng.next_u64() as usize) % len];
        let _ = a.union(p0, p1);
    }
    assert_eq!(a.len_keys(), A as usize);
    assert!(a.capacity_keys() >= (2 * A as usize));
    a
}

fn std_ord() -> OrdArena<P1, CKey, CVal> {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    let mut a = OrdArena::<P1, CKey, CVal>::new();
    let mut repr = vec![];
    let mut repr_inxs = vec![];
    let (mut insts, expected) = fuzz_fill_inst(&mut rng, &repr, 3 * A, A);
    let tmp = fuzz_fill_inst(&mut rng, &expected, 2 * A, 3 * A);
    insts.extend_from_slice(&tmp.0);
    for inst in insts {
        match inst {
            Ok(pair) => {
                repr.push((pair.0.clone_uncounting(), pair.1.clone_uncounting()));
                repr_inxs.push(a.insert(pair.0, pair.1).0);
            }
            Err(inx) => {
                a.remove(repr_inxs.swap_remove(inx)).unwrap();
                repr.swap_remove(inx);
            }
        }
    }
    assert_eq!(a.len(), A as usize);
    assert!(a.capacity() >= (2 * A as usize));
    a
}

#[test]
fn clone_from_to_recast() {
    // tests `clone*`, recasting, also tests the `PartialEq` impls

    // do not take the variations for granted, some specializations were broken
    // before
    let a0 = std_arena();
    let a1 = a0.clone();
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let mut a1 = Arena::new();
    a0.clone_into(&mut a1);
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let mut a1 = Arena::new();
    a1.clone_from(&a0);
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let recaster = a1.compress_and_shrink_recaster();
    assert_eq!(recaster.len(), a0.len());
    for (p, q) in recaster {
        assert_eq!(a0.get(p).unwrap(), a1.get(q).unwrap());
    }

    let a0 = std_chain();
    let a1 = a0.clone();
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let mut a1 = ChainArena::new();
    a0.clone_into(&mut a1);
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let mut a1 = ChainArena::new();
    a1.clone_from(&a0);
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let recaster = a1.compress_and_shrink_recaster();
    assert_eq!(recaster.len(), a0.len());
    for (p, q) in recaster {
        assert_eq!(a0.get(p).unwrap(), a1.get(q).unwrap());
    }
    a1.clone_from(&a0);
    let mut a2 = Arena::new();
    a0.clone_to_arena(&mut a2, |p, link| {
        assert_eq!(a1.get_link(p).unwrap(), link);
    });

    let a0 = std_surject();
    let a1 = a0.clone();
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let mut a1 = SurjectArena::new();
    a0.clone_into(&mut a1);
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let mut a1 = SurjectArena::new();
    a1.clone_from(&a0);
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let recaster = a1.compress_and_shrink_recaster();
    assert_eq!(recaster.len(), a0.len_keys());
    for (p, q) in recaster {
        assert_eq!(a0.get(p).unwrap(), a1.get(q).unwrap());
    }
    a1.clone_from(&a0);
    let mut a2 = ChainArena::new();
    a0.clone_keys_to_chain_arena(&mut a2, |p, key| {
        assert_eq!(a1.get_key(p).unwrap(), key);
    });
    a1.clone_from(&a0);
    let mut a2 = Arena::new();
    a0.clone_keys_to_arena(&mut a2, |p, key| {
        assert_eq!(a1.get_key(p).unwrap(), key);
    });

    let a0 = std_ord();
    let a1 = a0.clone();
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let mut a1 = OrdArena::new();
    a0.clone_into(&mut a1);
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let mut a1 = OrdArena::new();
    a1.clone_from(&a0);
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let recaster = a1.compress_and_shrink_recaster();
    assert_eq!(recaster.len(), a0.len());
    for (p, q) in recaster {
        assert_eq!(a0.get(p).unwrap(), a1.get(q).unwrap());
    }
    a1.clone_from(&a0);
    let mut a2 = ChainArena::new();
    a0.clone_to_chain_arena(&mut a2, |p, link| {
        assert_eq!(a1.get_link(p).unwrap(), link);
    });
    a1.clone_from(&a0);
    let mut a2 = Arena::new();
    a0.clone_to_arena(&mut a2, |p, link| {
        assert_eq!(a1.get_link(p).unwrap(), link);
    });
}
