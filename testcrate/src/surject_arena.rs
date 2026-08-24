// FIXME
/*

    struct Entry {
        pub s: Shared,
        pub p: P,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Shared {
        pub s: u64,
    }

    let mut counter_s = 0u64;
    let mut new_s = || {
        counter_s += 1;
        Shared { s: counter_s }
    };

    let mut a = SurjectArena::<P, Ck<()>, Shared>::new();
    let mut b_elements = CkMap::<(), Entry>;
    let mut b_surjects = HashMap<Shared, Vec<Ck<()>>>;
*/
