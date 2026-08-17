// FIXME
/*

    struct Entry {
        pub v: Val,
        pub p: P,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Val {
        pub v: u64,
    }

    let mut counter_v = 0u64;
    let mut new_v = || {
        counter_v += 1;
        Val { v: counter_v }
    };

    let mut a = SurjectArena::<P, Ck<()>, Val>::new();
    let mut b_entries = CkMap::<(), Entry>;
    let mut b_sets = HashMap<Val, Vec<Ck<()>>>;
*/
