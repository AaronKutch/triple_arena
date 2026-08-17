// FIXME
/*

    // avoid getting mixups
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Key {
        pub k: u8,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Triple<P> {
        pub k: Key,
        pub v: Ck<()>,
        pub p: P,
    }

impl SimpleOrdItem for Triple

    // make sure we have collisions
    const KEY_LIMIT: u8 = 64;
    let mut new_k = || Key {
        k: key_rng.index(KEY_LIMIT).unwrap(),
    };


    let mut a = SimpleOrdArena::<P, Triple<P>>::new();

    // this handles nonhereditary cases
    let mut b: BTreeMap<Key, BTreeMap<Ck<()>, Triple<P>>> = BTreeMap::new();
*/