//! for ease of copying to the doc examples

#[test]
fn compress_with_example() {
    use triple_arena::{Arena, DirectArena, HeapBacking, ptr_struct, traits::*};

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

#[test]
fn chain_transfer_canonical_example() {
    use triple_arena::{
        ChainArena, DirectArena, HeapBacking, LinkInsertKind, ptr_struct,
        traits::*,
        utils::traits::{PtrGen, PtrInx},
    };

    // (This would be a standard function, except there are far too many choices to
    // make on the backing of the recaster arena and how fallibility should be
    // handled)
    fn compress_canonical_recaster<P: Ptr, T>(
        a: &mut ChainArena<P, T, HeapBacking>,
        reset_generation: bool,
    ) -> DirectArena<P, P, HeapBacking> {
        // This arena will be a recaster in which we create a mapping from the old
        // `Ptr` domain to the new one. We use a `DirectArena` for this since it will
        // only be used for this purpose and then discarded.
        let mut recaster = DirectArena::<P, P, HeapBacking>::new();
        let mut res = ChainArena::<P, T, HeapBacking>::new();
        let new_generation = if reset_generation {
            // reset for compactness, only safe if logically old domain `Ptr`s can be
            // eliminated
            P::Gen::two()
        } else {
            // use incremented generation so that all `Ptr`s of the old domain are
            // invalidated
            P::Gen::generational_inc(a.generation()).0
        };
        res.transfer_canonical_reallocating(new_generation, a, |_, o, _| o.allow(), &mut recaster)
            .unwrap();
        *a = res;
        recaster
    }

    ptr_struct!(P0);

    let mut a: ChainArena<P0, &str> = ChainArena::new();
    let p_x = a.insert(LinkInsertKind::Disconnected, "X");
    let p_a = a.insert(LinkInsertKind::Disconnected, "A");
    a.insert(LinkInsertKind::ChainEnd(p_x), "Y");
    let p_b = a.insert(LinkInsertKind::ChainEnd(p_a), "B");
    // make an internal slot unallocated, and scatter the chains further
    a.remove(p_x).allow().unwrap();
    a.insert(LinkInsertKind::ChainEnd(p_b), "C");

    // the "A" -> "B" -> "C" chain is spread over the indexes 2, 4, 1
    assert_eq!(
        &format!("{a:#?}"),
        r#"{
    P0[1](3): {4, (end)} "C",
    P0[2](2): {(start), 4} "A",
    P0[3](2): {(start), (end)} "Y",
    P0[4](2): {2, 1} "B",
}"#
    );

    let recaster = compress_canonical_recaster(&mut a, false);

    // now each chain is one contiguous run of indexes in `Link::next` order
    let layout: Vec<(usize, &str)> = a
        .iter()
        .map(|(p, t)| (PtrInx::try_into_usize(p.inx()).unwrap().get(), *t))
        .collect();
    assert_eq!(layout, vec![(1, "A"), (2, "B"), (3, "C"), (4, "Y")]);
    // and the recaster is a complete description of where the links went
    println!("{recaster:#?}");
    assert_eq!(
        &format!("{recaster:#?}"),
        r#"{
    P0[1](3): P0[3](4),
    P0[2](2): P0[1](4),
    P0[3](2): P0[4](4),
    P0[4](2): P0[2](4),
}"#
    );

    // external `Ptr`s are fixed up with it
    let mut external = p_a;
    external.recast(&recaster).unwrap();
    assert_eq!(a[external], "A");
}

#[test]
fn simple_ord_arena_example() {
    use core::cmp::Ordering;

    use triple_arena::{HeapBacking, OrdPair, SimpleOrdArena, ptr_struct, traits::*};

    ptr_struct!(P0);
    let mut a = SimpleOrdArena::<P0, OrdPair<u64, ()>, HeapBacking>::new();

    let p50 = a.insert(OrdPair::new(50, ())).0;
    let p30 = a.insert(OrdPair::new(30, ())).0;
    let p70 = a.insert(OrdPair::new(70, ())).0;
    let p60 = a.insert(OrdPair::new(60, ())).0;
    let p10 = a.insert(OrdPair::new(10, ())).0;

    assert_eq!(a.first().unwrap(), p10);
    assert_eq!(a.last().unwrap(), p70);

    // note that this is `O(1)` because we are using a `Ptr` to directly
    // index
    assert_eq!(*a.get(p50).unwrap().k(), 50);

    // the `insert_*`, `find_*`, and `remove` operations are the only
    // `O(log n)` per-element operations
    assert_eq!(a.find_key(&50).unwrap(), p50);

    // this could find either `(p50, Ordering::Greater)` or
    // `(p60, Ordering::Less)`
    assert_eq!(a.find_similar_key(&53).unwrap(), (p60, Ordering::Less));

    // in `O(1)` time get the previous and next pairs
    assert_eq!(
        a.get_inx_link_no_gen(p60.inx()).unwrap().1.prev_next(),
        (Some(p50.inx()), Some(p70.inx()))
    );

    // `remove` does have to do `O(log n)` tree rebalancing, but it avoids
    // needing to redo the lookup if the `Ptr` is kept around
    let pair = a.remove(p50).allow().unwrap();
    assert_eq!(pair.into_k_v(), (50, ()));

    // The `*_ordered` iterators are fully deterministic and iterate from the
    // least element to the greatest
    let expected = [(p10, 10), (p30, 30), (p60, 60), (p70, 70)];
    for (i, (p, pair)) in a.iter_ordered().enumerate() {
        assert_eq!(expected[i], (p, *pair.k()));
    }
}
