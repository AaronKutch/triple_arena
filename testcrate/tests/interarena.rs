use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use testcrate::{
    fuzz_fill_inst, std_arena, std_chain, std_chain_no_gen, std_ord, std_surject, CKey, CVal, A, P1,
};
use triple_arena::{utils::ChainNoGenArena, Arena, ChainArena, OrdArena, SurjectArena};

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

    let a0 = std_chain_no_gen();
    let a1 = a0.clone();
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let mut a1 = ChainNoGenArena::new();
    a0.clone_into(&mut a1);
    assert_eq!(a0, a1);
    assert_eq!(a1, a0);
    let mut a1 = ChainNoGenArena::new();
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
    a1.clone_from(&a0);
    let mut a2 = ChainArena::new();
    a0.clone_to_chain_arena(&mut a2, |p, pair| {
        assert_eq!(a1.get(p).unwrap(), pair);
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
    a0.clone_to_chain_arena(&mut a2, |p, key, val| {
        assert_eq!(a1.get(p).unwrap(), (key, val));
    });
    a1.clone_from(&a0);
    let mut a2 = Arena::new();
    a0.clone_to_arena(&mut a2, |p, key, val| {
        assert_eq!(a1.get(p).unwrap(), (key, val));
    });
}

// also retests a bunch of misc stuff
#[test]
fn ord_arena_order() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    let mut set_of_vecs = vec![];
    for _ in 0..A {
        let mut v = vec![];
        for _ in 0..(rng.next_u32() % 16) {
            v.push((rng.next_u32() % 16, rng.next_u64() % 16));
        }
        set_of_vecs.push(v);
    }
    let mut set_of_arenas: Vec<OrdArena<P1, u32, u64>> = vec![];
    for v in &set_of_vecs {
        set_of_arenas.push(OrdArena::from_iter(v.iter().copied()))
    }
    set_of_vecs.sort();
    // first use `PartialOrd`
    set_of_arenas
        .clone()
        .sort_by(|a, b| a.partial_cmp(b).unwrap());
    let res: Vec<Vec<(u32, u64)>> = set_of_arenas
        .iter()
        .map(|a| a.iter().map(|(_, k, v)| (*k, *v)).collect())
        .collect();
    assert_eq!(set_of_vecs, res);
    set_of_arenas.sort();
    let res: Vec<Vec<(u32, u64)>> = set_of_arenas
        .iter()
        .map(|a| a.iter().map(|(_, k, v)| (*k, *v)).collect())
        .collect();
    assert_eq!(set_of_vecs, res);
}
