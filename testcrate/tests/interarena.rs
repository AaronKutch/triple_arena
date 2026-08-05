use triple_arena::{Arena, DirectArena, StackBacking, traits::*};

#[cfg(feature = "alloc")]
#[test]
fn test_inst_framework() {
    use rand_xoshiro::{Xoshiro128StarStar, rand_core::SeedableRng};
    use testcrate::{A, CKey, CVal, P1, fuzz_fill_inst};
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

// also test exact stack backing for this case

// (This would be a standard function, except there are far too many choices to
// make on the backing of the recaster arena and how fallibility should be
// handled)
fn compress_recaster<P: Ptr, T, A: CompactArenaTrait<P, T>>(
    this: &mut A,
    reset_generation: bool,
) -> DirectArena<P, P, StackBacking<4>> {
    // This arena will be a recaster in which we create a mapping from the old `Ptr`
    // domain to the new one. We use a `DirectArena` for this since it is its only
    // use.
    let mut res = DirectArena::<P, P, StackBacking<4>>::new();
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

    let mut a = Arena::<P0, (u64, Option<P0>), StackBacking<4>>::new();

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
