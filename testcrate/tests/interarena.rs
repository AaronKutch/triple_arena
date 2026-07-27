use rand_xoshiro::{
    Xoshiro128StarStar,
    rand_core::{Rng, SeedableRng},
};
use testcrate::{
    A, CKey, CVal, P1, fuzz_fill_inst, std_arena, std_chain, std_chain_no_gen, std_ord, std_surject,
};
use triple_arena::{
    Arena, ChainArena, HeapBacking, OrdArena, SurjectArena, traits::*, utils::ChainNoGenArena,
};

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
                a.remove(repr_inxs.swap_remove(inx)).allow().unwrap();
                repr.swap_remove(inx);
            }
        }
    }
    assert_eq!(repr, expected);
}

// (This would be a standard function, except there are far too many choices to
// make on the backing of the recaster arena and how fallibility should be
// handled)
fn compress_recaster<
    P: Ptr,
    T,
    A: ArenaTrait<P, T> + SingularGenerationArena<P> + ArenaCloneFromWith<P, T>,
>(
    this: &mut A,
    reset_generation: bool,
) -> Arena<P, P, HeapBacking> {
    // this arena will be a recaster in which we create a mapping from the old `Ptr`
    // domain to the new one
    let mut res = Arena::<P, P, HeapBacking>::new();
    // this sets all the keys of the mapping by cloning the `Ptr` validities of the
    // pre-compression `self` into the recaster and puts in invalid placeholders for
    // the new domain
    res.clone_from_with(this, |_, _| P::invalid()).unwrap();
    // compress and write the new `Ptr`s at the indexes of the corresponding old
    // ones, completing the mapping
    this.compress_with(reset_generation, |p, _, q| *res.get_mut(p).unwrap() = q)
        .allow();
    res
}

#[test]
fn compress_with_example() {
    use triple_arena::{Arena, ptr_struct, traits::*};

    ptr_struct!(P0);

    impl Recast<P0> for (u64, Option<P0>) {
        fn recast<R: Recaster<Item = P0>>(
            &mut self,
            recaster: &R,
        ) -> Result<(), <R as Recaster>::Item> {
            self.1.recast(recaster)?;
            Ok(())
        }
    }

    let mut a = Arena::<P0, (u64, Option<P0>)>::new();

    let p0 = a.insert((0, None));
    let p42 = a.insert((42, None));
    let p1 = a.insert((1, None));
    a.insert((1337, Some(p42)));
    // make some internal slots unallocated
    a.remove(p0).allow().unwrap();
    a.remove(p1).allow().unwrap();

    assert_eq!(
        &format!("{a:?}"),
        "{P0[2](2): (42, None), P0[4](2): (1337, Some(P0[2](2)))}"
    );

    // This is what the `Recast` trait is for. We call this before
    // serialization. This fixes both the indexes of the `Ptr` keys
    // and the indexes inside the values of the arena, so that
    // relations are preserved.
    let recaster = compress_recaster(&mut a, false);
    a.recast(&recaster).unwrap();
    // the recaster had this
    assert_eq!(
        &format!("{recaster:?}"),
        "{P0[2](2): P0[1](5), P0[4](2): P0[2](5)}"
    );
    // now the allocated slots are compressed and we could shrink capacity or use
    // this for compact serialization
    assert_eq!(
        &format!("{a:?}"),
        "{P0[1](5): (42, None), P0[2](5): (1337, Some(P0[1](5)))}"
    );

    // try again but with resetting the generation, useful in some cases
    let recaster = compress_recaster(&mut a, true);
    a.recast(&recaster).unwrap();
    // maps all the generations down to a minimal value
    assert_eq!(
        &format!("{recaster:?}"),
        "{P0[1](5): P0[1](2), P0[2](5): P0[2](2)}"
    );
    assert_eq!(
        &format!("{a:?}"),
        "{P0[1](2): (42, None), P0[2](2): (1337, Some(P0[1](2)))}"
    );
}

#[test]
fn clone_from_to_recast() {
    // tests `clone*`, recasting, also tests the `PartialEq` impls

    // do not take the variations for granted, some specializations were broken
    // before
    let a0 = std_arena();
    let _a1 = a0.clone();
    let mut a1 = Arena::new();
    a0.clone_into(&mut a1);
    let mut a1 = Arena::new();
    a1.clone_from(&a0);
    let recaster = compress_recaster(&mut a1, false);
    assert_eq!(recaster.len(), a0.len());
    for (p, q) in recaster {
        assert_eq!(a0.get(p).unwrap(), a1.get(q).unwrap());
    }

    let a0 = std_chain();
    let _a1 = a0.clone();
    let mut a1 = ChainArena::new();
    a0.clone_into(&mut a1);
    let mut a1 = ChainArena::new();
    a1.clone_from(&a0);
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
    let _a1 = a0.clone();
    let mut a1 = ChainNoGenArena::new();
    a0.clone_into(&mut a1);
    let mut a1 = ChainNoGenArena::new();
    a1.clone_from(&a0);
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
    let _a1 = a0.clone();
    let mut a1 = SurjectArena::new();
    a0.clone_into(&mut a1);
    let mut a1 = SurjectArena::new();
    a1.clone_from(&a0);
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
        v.sort();
        v.dedup_by(|(k0, _), (k1, _)| k0 == k1);
        set_of_vecs.push(v);
    }
    let mut set_of_arenas: Vec<OrdArena<P1, u32, u64>> = vec![];
    for v in &set_of_vecs {
        set_of_arenas.push(OrdArena::from_iter(v.iter().copied()))
    }
    set_of_vecs.sort();
    // first use `PartialOrd`
    let mut tmp = set_of_arenas.clone();
    tmp.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let res: Vec<Vec<(u32, u64)>> = tmp
        .iter()
        .map(|a| a.iter().map(|(_, k, v)| (*k, *v)).collect())
        .collect();
    assert_eq!(set_of_vecs, res);
    // use `Ord`
    set_of_arenas.sort();
    let res: Vec<Vec<(u32, u64)>> = set_of_arenas
        .iter()
        .map(|a| a.iter().map(|(_, k, v)| (*k, *v)).collect())
        .collect();
    assert_eq!(set_of_vecs, res);
}
