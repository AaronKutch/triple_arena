use triple_arena::{Arena, DirectArena, traits::*};

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

// for ease of copying to the doc example
#[test]
fn compress_with_example() {
    use triple_arena::{Arena, HeapBacking, ptr_struct, traits::*};

    // (This would be a standard function, except there are far too many choices to
    // make on the backing of the recaster arena and how fallibility should be
    // handled)
    fn compress_recaster<P: Ptr, T, A: CompactArenaTrait<P, T>>(
        this: &mut A,
        reset_generation: bool,
    ) -> DirectArena<P, P, HeapBacking> {
        // This arena will be a recaster in which we create a mapping from the old `Ptr`
        // domain to the new one. We use a `DirectArena` for this since it will only
        // be used for this purpose and then discarded.
        let mut recaster = DirectArena::<P, P, HeapBacking>::new();
        // This all the keys of the mapping, by cloning the `Ptr` validities of the
        // pre-compression `this` into the recaster, and puts in invalid placeholders
        // for the new domain because we do not know them yet.
        recaster.clone_from_with(this, |_, _| P::invalid()).unwrap();
        // Compress and write the new `Ptr`s at the indexes of the corresponding old
        // `Ptr`s, and using the values seen by the closure to complete the mapping of
        // the old domain to the new domain.
        this.compress_with(reset_generation, |p, _, q| {
            *recaster.get_mut(p).unwrap() = q
        })
        .allow();
        recaster
    }

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
        &format!("{a:#?}"),
        r#"{
    P0[2](2): (
        42,
        None,
    ),
    P0[4](2): (
        1337,
        Some(
            P0[2](2),
        ),
    ),
}"#
    );

    // This is what the `Recast` trait is for. We call this before
    // serialization. This fixes both the indexes of the `Ptr` keys
    // and the indexes inside the values of the arena, so that
    // relations are preserved.
    let recaster = compress_recaster(&mut a, false);
    a.recast(&recaster).unwrap();

    // the recaster had this, a complete description of where entries went
    assert_eq!(
        &format!("{recaster:#?}"),
        r#"{
    P0[2](2): P0[1](5),
    P0[4](2): P0[2](5),
}"#
    );
    // now the allocated slots are compressed, and we could shrink capacity or use
    // this for compact serialization
    assert_eq!(
        &format!("{a:#?}"),
        r#"{
    P0[1](5): (
        42,
        None,
    ),
    P0[2](5): (
        1337,
        Some(
            P0[1](5),
        ),
    ),
}"#
    );

    // try again but with resetting the generation, be aware this can cause ABA
    // violations or worse if `Ptr`s from the old domain are not all recast
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
