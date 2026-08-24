//! for ease of copying to the doc examples

use triple_arena::traits::ArenaTrait;

// SYNC(triple_arena/src/arena/arena_traits.rs, compress_with)
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
        // `Ptr`s, using the values seen by the closure to complete the mapping of
        // the old domain to the new domain.
        this.compress_with(reset_generation, |q, _, p| recaster[q] = p)
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

// SYNC(triple_arena/src/chain/chain_arena.rs, transfer_canonical_reallocating)
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
        this: &mut ChainArena<P, T, HeapBacking>,
        reset_generation: bool,
    ) -> DirectArena<P, P, HeapBacking> {
        let new_generation = if reset_generation {
            // reset for compactness, only safe if logically old domain `Ptr`s can be
            // eliminated
            P::Gen::two()
        } else {
            // use incremented generation so that all `Ptr`s of the old domain are
            // invalidated
            P::Gen::generational_inc(this.generation()).0
        };
        // This arena will be a recaster in which we create a mapping from the old `Ptr`
        // domain to the new one. We use a `DirectArena` for this since it will only
        // be used for this purpose and then discarded.
        let mut recaster = DirectArena::<P, P, HeapBacking>::new();
        // This all the keys of the mapping, by cloning the `Ptr` validities of the
        // pre-transfer `this` into the recaster, and puts in invalid placeholders
        // for the new domain because we do not know them yet.
        recaster.clone_from_with(this, |_, _| P::invalid()).unwrap();
        let mut replacement = ChainArena::<P, T, HeapBacking>::new();
        // Transfer and write the new `Ptr`s at the indexes of the corresponding old
        // `Ptr`s, using the values seen by the closure to complete the mapping of
        // the old domain to the new domain.
        replacement
            .transfer_canonical_reallocating(new_generation, this, |q, o, p| {
                recaster[q] = p;
                o.allow()
            })
            .unwrap();
        *this = replacement;
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

// SYNC(triple_arena/src/ord/simple_ord_arena.rs, SimpleOrdArena)
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

// SYNC(triple_arena/src/ord/simple_ord_arena.rs,
// transfer_canonical_reallocating)
#[test]
fn simple_ord_arena_transfer_canonical_example() {
    use triple_arena::{
        DirectArena, HeapBacking, OrdPair, SimpleOrdArena, ptr_struct,
        traits::*,
        utils::traits::{PtrGen, PtrInx},
    };

    // (This would be a standard function, except there are far too many choices to
    // make on the backing of the recaster arena and how fallibility should be
    // handled)
    fn compress_canonical_recaster<P: Ptr, T>(
        this: &mut SimpleOrdArena<P, T, HeapBacking>,
        reset_generation: bool,
    ) -> DirectArena<P, P, HeapBacking> {
        let new_generation = if reset_generation {
            // reset for compactness, only safe if logically old domain `Ptr`s can be
            // eliminated
            P::Gen::two()
        } else {
            // use incremented generation so that all `Ptr`s of the old domain are
            // invalidated
            P::Gen::generational_inc(this.generation()).0
        };
        // This arena will be a recaster in which we create a mapping from the old `Ptr`
        // domain to the new one. We use a `DirectArena` for this since it will only
        // be used for this purpose and then discarded.
        let mut recaster = DirectArena::<P, P, HeapBacking>::new();
        // This all the keys of the mapping, by cloning the `Ptr` validities of the
        // pre-transfer `this` into the recaster, and puts in invalid placeholders
        // for the new domain because we do not know them yet.
        recaster.clone_from_with(this, |_, _| P::invalid()).unwrap();
        let mut replacement = SimpleOrdArena::<P, T, HeapBacking>::new();
        // Transfer and write the new `Ptr`s at the indexes of the corresponding old
        // `Ptr`s, using the values seen by the closure to complete the mapping of
        // the old domain to the new domain.
        replacement
            .transfer_canonical_reallocating(new_generation, this, |q, o, p| {
                recaster[q] = p;
                o.allow()
            })
            .unwrap();
        *this = replacement;
        recaster
    }

    ptr_struct!(P0);

    type A = SimpleOrdArena<P0, OrdPair<&'static str, ()>, HeapBacking>;
    fn layout(a: &A) -> Vec<(usize, &'static str)> {
        a.iter_ordered()
            .map(|(p, pair)| (PtrInx::try_into_usize(p.inx()).unwrap().get(), *pair.k()))
            .collect()
    }

    let mut a = A::new();
    let _ = a.insert(OrdPair::new("C", ()));
    let p_a = a.insert(OrdPair::new("A", ())).0;
    let p_d = a.insert(OrdPair::new("D", ())).0;
    let _ = a.insert(OrdPair::new("B", ()));
    // make an internal slot unallocated, and scatter the keys further
    a.remove(p_d).allow().unwrap();
    let _ = a.insert(OrdPair::new("E", ()));

    // with respect to `*_ordered` iteration, the keys are in order, but at
    // the index level they are scattered
    assert_eq!(layout(&a), vec![(2, "A"), (4, "B"), (1, "C"), (3, "E")]);

    let recaster = compress_canonical_recaster(&mut a, false);

    // now the keys are in index order as well, and the internal tree is
    // deterministically rebalanced to be perfectly canonical
    assert_eq!(layout(&a), vec![(1, "A"), (2, "B"), (3, "C"), (4, "E")]);
    // and the recaster is a complete description of where the entries went
    assert_eq!(
        &format!("{recaster:#?}"),
        r#"{
    P0[1](2): P0[3](4),
    P0[2](2): P0[1](4),
    P0[3](3): P0[4](4),
    P0[4](2): P0[2](4),
}"#
    );

    // external `Ptr`s are fixed up with it
    let mut external = p_a;
    external.recast(&recaster).unwrap();
    assert_eq!(*a[external].k(), "A");
}

// SYNC(triple_arena/src/arena/base_arena.rs, Arena)
// SYNC(triple_arena/README.md, base_arena_example)
#[test]
fn arena_example() {
    use triple_arena::{Arena, ptr_struct, traits::*};

    // In implementations that always use valid indexes and only want the
    // generation counter in debug mode, we can use `cfg`s like this:
    /* // commented out because of doc tests
    #[cfg(Debug)]
    ptr_struct!(P0);
    #[cfg(Debug)]
    ptr_struct!(Q2);
    #[cfg(not(Debug))]
    ptr_struct!(P0());
    #[cfg(not(Debug))]
    ptr_struct!(Q2());
    */
    ptr_struct!(P0);
    ptr_struct!(Q2);

    // By convention we use short names for `Ptr` structs beginning with `P`,
    // `Q`, or `R`. In simple contexts we add a single digit to differentiate
    // the generic `P: Ptr` from a instantiated `P0`. If the number of arenas
    // exceeds a small number or the types will be public, you should use more
    // descriptive names like `PNode`, `PComponent`, `PNameOfEntryKind`, etc.

    // Note: if the crate was compiled with the "alloc" flag, the third
    // `B: ArenaBacking` generic argument is defaulted to `crate::HeapBacking`.
    // Otherwise, this would need to be something like
    // `Arena<P0, String, StackBacking<...>>`.

    let mut arena: Arena<P0, String> = Arena::new();

    let test_ptr: P0 = arena.insert("test".to_string());
    let hello_ptr: P0 = arena.insert("hello".to_string());

    // Nice debug representations. See also the `triple_arena_render` crate for
    // trait-based rendering of graphs. Note that the internal indexes are
    // starting at 1 because `NonZero` types are used. This allows for memory
    // niche optimizations of `Option<P>` and other such things.
    assert_eq!(
        &format!("{:?}", arena),
        "{P0[1](2): \"test\", P0[2](2): \"hello\"}"
    );

    // use the `Ptr`s we got from insertion to reference the stored data
    assert_eq!(arena[hello_ptr], "hello");

    // Remove objects. The `Arena` uses internal freelists to keep the capacity
    // for future inserts to reuse. Invalidation functions like
    // `ArenaTrait::remove` return an `InvalidationResult` or
    // `InvalidationOption` that allow checking for generation overflow. For
    // most use cases with the default generation counter size, however, you
    // should just use `.allow()` to allow generation overflow because it is
    // practically impossible to reach.
    let removed = arena.remove(test_ptr).allow().unwrap();
    assert_eq!(removed, "test");

    // When using generation counters, invalidated pointers are guaranteed to
    // never work again.
    assert!(arena.get(test_ptr).is_none());

    // Using different `Ptr` generics is extremely useful in complicated
    // multiple arena code with self pointers and inter-arena pointers. This is
    // an arena storing a tuple of pointers that work on the first arena and
    // itself.
    let mut arena2: Arena<Q2, (P0, Q2)> = Arena::new();

    let p2_ptr: Q2 = arena2.insert((hello_ptr, Ptr::invalid()));
    let another: Q2 = arena2.insert((hello_ptr, p2_ptr));
    assert_eq!(arena2[another].1, p2_ptr);

    // With many arena crates, no compile time or runtime checks would prevent
    // you from using the wrong pointers. Here, the compiler protects us.
    // error: expected struct `P0`, found struct `Q2`
    //let _ = arena.get(p2_ptr);

    assert_eq!(arena[arena2[p2_ptr].0], "hello");

    // In cases where we are forced to have the same `Ptr` struct, we can still
    // have type guards against semantically different `Ptr`s by using generics:
    fn example<P0: Ptr, P1: Ptr, T>(a0: &mut Arena<P0, T>, a1: &mut Arena<P1, T>, p1: P1) {
        // error: expected type parameter `P0`, found type parameter `P1`
        //let _ = a0.remove(p1);

        a0.insert(a1.remove(p1).allow().unwrap());
    }

    let mut arena3: Arena<Q2, String> = Arena::new();
    example(&mut arena3, &mut arena, hello_ptr);
    assert_eq!(arena3.iter().next().unwrap().1, "hello");
}

// SYNC(triple_arena/src/arena/direct_insertion_arena.rs, DirectArena)
#[test]
fn direct_arena_example() {
    use triple_arena::{Arena, DirectArena, ptr_struct, traits::*};

    ptr_struct!(P0);

    let mut a = Arena::<P0, u64>::new();
    let p0 = a.insert(42);
    let p1 = a.insert(1337);
    a.remove(p0).allow().unwrap();

    // mirror the state of `a`, mapping the entries to something else
    let mut mirror = DirectArena::<P0, String>::new();
    mirror.clone_from_with(&a, |_, t| t.to_string()).unwrap();
    assert_eq!(&format!("{mirror:?}"), "{P0[2](2): \"1337\"}");

    // the `Ptr`s of `a` are directly usable on the mirror
    assert_eq!(mirror[p1], "1337");
    assert!(mirror.get(p0).is_none());

    // mirror a new insertion in `a`, reusing the internal slot that `p0` had
    let p2 = a.insert(7);
    mirror
        .direct_insert_within_capacity(p2)
        .unwrap()
        .insert("7".to_owned());
    assert_eq!(
        &format!("{mirror:?}"),
        "{P0[1](3): \"7\", P0[2](2): \"1337\"}"
    );
}

// SYNC(triple_arena/src/chain/chain_arena.rs, ChainArena)
#[test]
fn chain_arena_example() {
    use triple_arena::{
        ChainArena, LinkInsertKind, errors::ChainInsertionError, ptr_struct, traits::*,
    };

    ptr_struct!(P0);
    let mut a: ChainArena<P0, String> = ChainArena::new();

    let p_a = a.insert(LinkInsertKind::Disconnected, "A".to_owned());
    let p_b = a.insert(LinkInsertKind::Disconnected, "B".to_owned());

    // initially, all entries from inserting with `LinkInsertKind::Disconnected`
    // have `None` interlinks and are each in their own single link chains, and
    // are completely unassociated like in a normal `Arena`.

    // `*_no_gen` variants are preferred if only index interlinks are needed
    let link = a.get_link_no_gen(p_a).unwrap();
    assert_eq!(link.t, "A");
    assert_eq!(link.prev(), None);
    assert_eq!(link.next(), None);

    let link = a.get_link_no_gen(p_b).unwrap();
    assert_eq!(link.t, "B");
    assert_eq!(link.prev(), None);
    assert_eq!(link.next(), None);

    assert!(!a.are_neighbors(p_a, p_b));

    // Connect the two links by making the `next` interlink of A point to B,
    // and the `prev` interlink of B point to A. Note that this is directional
    // and that `a.connect(p_b, p_a).unwrap()` would result B being the start
    // and A being the end of the chain instead.
    a.connect(p_a, p_b).unwrap();

    let link = a.get_link_no_gen(p_a).unwrap();
    assert_eq!(link.t, "A");
    assert_eq!(link.prev(), None);
    assert_eq!(link.next(), Some(p_b.inx()));

    let link = a.get_link_no_gen(p_b).unwrap();
    assert_eq!(link.t, "B");
    assert_eq!(link.prev(), Some(p_a.inx()));
    assert_eq!(link.next(), None);

    assert!(a.are_neighbors(p_a, p_b));
    assert!(!a.are_neighbors(p_b, p_a));

    // Now let us insert a third link and make it the end of the existing chain
    // by using `LinkInsertKind::ChainEnd`.

    // `LinkInsertKind::ChainEnd` guards against attaching to any part of a
    // chain except for the preexisting end link.
    assert_eq!(
        a.insert_reallocating(LinkInsertKind::ChainEnd(p_a), "D".to_owned()),
        Err(ChainInsertionError::FailedLinkRequirement)
    );
    let p_d = a.insert(LinkInsertKind::ChainEnd(p_b), "D".to_owned());

    assert!(a.are_neighbors(p_b, p_d));

    // Inserting a link into the middle
    let p_c = a.insert(
        LinkInsertKind::AtInterlink {
            next_to: p_b,
            prev_to: p_d,
        },
        "C".to_owned(),
    );
    assert!(!a.are_neighbors(p_b, p_d));
    assert!(a.are_neighbors(p_b, p_c));
    assert!(a.are_neighbors(p_c, p_d));

    // Insert a separate chain
    let p_x = a.insert(LinkInsertKind::Disconnected, "X".to_owned());
    let p_y = a.insert(LinkInsertKind::ChainEnd(p_x), "Y".to_owned());
    let p_z = a.insert(LinkInsertKind::ChainEnd(p_y), "Z".to_owned());

    // Connect the chains end-to-start in `O(1)`.
    a.connect(p_d, p_x).unwrap();

    // `iter_chain` will iterate over all links in the chain that the given
    // `Ptr` is a part of. It will iterate across the chain in order (but
    // check the documentation for how starting in the middle or in a cyclical
    // chain works).
    let expected = [
        (p_a, "A"),
        (p_b, "B"),
        (p_c, "C"),
        (p_d, "D"),
        (p_x, "X"),
        (p_y, "Y"),
        (p_z, "Z"),
    ];
    for (i, (p_link, link)) in a.iter_chain(p_a).unwrap().enumerate() {
        assert_eq!(expected[i], (p_link, link.t.as_str()));
    }

    // Remove an element in the middle of a chain in `O(1)` with the same
    // capabilities that the plain `Arena` has. Interlinks are fixed so
    // that the link before the removed element is connected with the link
    // after the element (chains are only broken in two with `break_*` or
    // `exchange_next`).
    assert_eq!(a.remove(p_d).allow().unwrap(), "D".to_owned());
    assert!(a.are_neighbors(p_c, p_x));
    let expected = [
        (p_a, "A"),
        (p_b, "B"),
        (p_c, "C"),
        (p_x, "X"),
        (p_y, "Y"),
        (p_z, "Z"),
    ];
    for (i, (p_link, link)) in a.iter_chain(p_a).unwrap().enumerate() {
        assert_eq!(expected[i], (p_link, link.t.as_str()));
    }

    // Remove a single connected chain efficiently
    let _ = a.drain_chain(p_x).unwrap();
    assert!(a.is_empty());
}

// SYNC(triple_arena/src/surject/surject_arena.rs, SurjectArena)
#[test]
fn surject_arena_example() {
    use triple_arena::{SurjectArena, errors::ChainInsertionError, ptr_struct};

    ptr_struct!(P0);
    let mut a: SurjectArena<P0, String, String> = SurjectArena::new();

    // There must be at least one key associated with each value
    let p0_42 = a.insert("key0".to_owned(), "42".to_owned());
    // If we want new keys to be associated with the same key set pointing to
    // "42", then instead of calling `insert_val` we call `insert_key`
    let p1_42 = a.insert_key(p0_42, "key1".to_owned());
    // We could use either `p0_42` or `p1_42` as our reference to get
    // associated with the same key set; any valid pointer in the preexisting
    // set can be used with the same `O(1)` computational complexity incurred.
    let p2_42 = a.insert_key(p0_42, "key2".to_owned());

    assert_eq!(a.get(p0_42).unwrap(), "key0");
    assert_eq!(a.get(p1_42).unwrap(), "key1");
    assert_eq!(a.get(p2_42).unwrap(), "key2");
    assert_eq!(a.get_val(p0_42).unwrap(), "42");
    assert_eq!(a.get_val(p1_42).unwrap(), "42");
    assert_eq!(a.get_val(p2_42).unwrap(), "42");

    assert_eq!(a.remove_key(p1_42).allow(), Some(("key1".to_owned(), None)));
    assert!(a.contains(p0_42));
    assert!(!a.contains(p1_42));
    assert!(a.contains(p2_42));
    // the value is perpetuated as long as there is a nonempty set of
    // pointer-keys associated with it
    assert_eq!(a.get_val(p2_42).unwrap(), "42");

    // We cannot use an invalidated pointer as a reference
    assert_eq!(
        a.insert_key_reallocating(p1_42, "key3".to_owned()),
        Err(ChainInsertionError::FailedLinkRequirement)
    );
    // We need to use an existing valid key
    let p3_42 = a.insert_key(p2_42, "key3".to_owned());
    assert_eq!(a.get_val(p3_42).unwrap(), "42");

    let other42 = a.insert("test".to_owned(), "42".to_owned());
    // note this is still a general `Arena`-like structure and not a hereditary
    // set or map, so multiple of the same exact values can exist in different
    // surjects.
    assert!(!a.in_same_set(p0_42, other42).unwrap());
    // removes the entire set
    a.remove_shared(other42).unwrap().allow();

    let p4_7 = a.insert("key4".to_owned(), "7".to_owned());
    let p5_7 = a.insert_key(p4_7, "key5".to_owned());

    assert_eq!(a.len_surject(p0_42).unwrap().get(), 3);
    assert_eq!(a.len_surject(p4_7).unwrap().get(), 2);

    // I know the order ahead of time because the arena is deterministic, but
    // note that in general this will be completely unsorted with respect to
    // keys or values.
    let expected = [
        (p0_42, "key0", "42"),
        (p3_42, "key3", "42"),
        (p2_42, "key2", "42"),
        (p4_7, "key4", "7"),
        (p5_7, "key5", "7"),
    ];
    // this iterator is not cloning the values, it is simply repeatedly
    // indexing the values when multiple keys are associated with a single
    // value
    for (i, (p, key, val)) in a.iter_combined().enumerate() {
        assert_eq!(expected[i], (p, key.as_str(), val.as_str()));
    }

    let (removed_v, kept_p) = a.union(p0_42, p4_7).unwrap();
    // One of the "7" or "42" values was removed from the arena,
    // and the other remains in the arena. Suppose we want
    // to take a custom union of the `String`s to go along
    // with the union of the keys, we would do something like
    *a.get_val_mut(kept_p).unwrap() = format!("{} + {}", a.get_val(kept_p).unwrap(), removed_v);

    assert_eq!(a.len_surject(p0_42).unwrap().get(), 5);
    let expected = [
        (p0_42, "key0", "42 + 7"),
        (p3_42, "key3", "42 + 7"),
        (p2_42, "key2", "42 + 7"),
        (p4_7, "key4", "42 + 7"),
        (p5_7, "key5", "42 + 7"),
    ];
    for (i, (p, key, val)) in a.iter_combined().enumerate() {
        assert_eq!(expected[i], (p, key.as_str(), val.as_str()));
    }

    // only upon removing the last key is the value is returned
    // (or we could use the wholesale `remove`)
    assert_eq!(a.remove_key(p4_7).allow(), Some(("key4".to_owned(), None)));
    assert_eq!(a.remove_key(p0_42).allow(), Some(("key0".to_owned(), None)));
    assert_eq!(a.remove_key(p3_42).allow(), Some(("key3".to_owned(), None)));
    assert_eq!(a.remove_key(p5_7).allow(), Some(("key5".to_owned(), None)));
    assert_eq!(
        a.remove_key(p2_42).allow(),
        Some(("key2".to_owned(), Some("42 + 7".to_owned())))
    );
}

// SYNC(triple_arena/src/ord/find.rs, _debug_arena)
/// This one is only for development debugging, and it writes a `tmp.svg` in the
/// working directory if it ever does fail
#[test]
#[cfg(feature = "alloc")]
fn simple_ord_arena_debug_example() {
    use std::path::PathBuf;

    use triple_arena::{
        Arena, HeapBacking, OrdPair, SimpleOrdArena, ptr_struct,
        traits::{ArenaCloneFromWith, ArenaTrait},
    };
    use triple_arena_render::{DebugNode, render_to_svg_file};

    ptr_struct!(P0);

    let mut a = SimpleOrdArena::<P0, OrdPair<String, ()>, HeapBacking>::new();

    for i in 0..100 {
        let _ = a.insert(OrdPair::new(format!("K{i:X?}"), ()));
        a.compress(false).allow();

        if let Err(e) = SimpleOrdArena::_check_invariants(&a) {
            let debug_arena = a._debug_arena();
            let mut debug_arena2 = Arena::<_, _, HeapBacking>::new();
            debug_arena2
                .clone_from_with(&debug_arena, |_, (rank, pair, p_tree0, p_back, p_tree1)| {
                    DebugNode {
                        sources: if let Some(p_back) = p_back {
                            vec![(*p_back, String::new())]
                        } else {
                            vec![]
                        },
                        center: vec![format!("r: {rank}, pair: {pair:?}")],
                        sinks: {
                            let mut v = vec![];
                            if let Some(p_tree0) = p_tree0 {
                                v.push((*p_tree0, "0".to_owned()));
                            }
                            if let Some(p_tree1) = p_tree1 {
                                v.push((*p_tree1, "1".to_owned()));
                            }
                            v
                        },
                    }
                })
                .unwrap();
            render_to_svg_file(&debug_arena2, false, PathBuf::from("tmp.svg")).unwrap();
            panic!(
                "{i}: debug: {}\nfailed with: {}",
                SimpleOrdArena::_debug(&a),
                e
            );
        }
    }
}
