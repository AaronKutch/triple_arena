use stacked_errors::{StackableErr, StackedError};
use star_rng::StarRng;
use testcrate::{
    P2,
    basic_arena::{self},
    cdgen::{Cd, CdGen},
    nonzero_inx_generic_stack,
};
use triple_arena::{
    Arena, HeapBacking, LimitedHeapBacking, StackBacking,
    traits::Ptr,
    utils::{
        NonZeroInxArray, NonZeroInxBoxedSlice, NonZeroInxLimitedVec, NonZeroInxVec,
        traits::{ArenaBacking, NonZeroInxGenericStack, SetMaxCapacity},
    },
};

#[test]
fn fuzz_nonzero_inx_generic_stack() -> Result<(), StackedError> {
    let rng = &mut StarRng::new(0);

    const N: usize = if cfg!(miri) { 10_000 } else { 10_000_000 };
    const ITERS999: usize = if cfg!(miri) { 5 } else { 9826 };
    pub const LIMIT: usize = 7;

    let mut stats = nonzero_inx_generic_stack::Stats {
        test_limit: LIMIT,
        fixed_cap: Some(LIMIT),
        n: N,
        iters999: Some(ITERS999),
    };
    nonzero_inx_generic_stack::fuzz(
        stats,
        rng,
        &mut CdGen::new(),
        NonZeroInxArray::<_, { LIMIT }>::new(),
        None,
    )
    .stack()?;

    // I could get a custom allocator to make this deterministic, but I think one
    // check is good enough
    stats.iters999 = None;
    stats.fixed_cap = None;

    let mut a = NonZeroInxLimitedVec::new();
    a.set_max_capacity(LIMIT).unwrap();
    nonzero_inx_generic_stack::fuzz(
        stats,
        rng,
        &mut CdGen::new(),
        a,
        Some(|a, max_capacity| a.set_max_capacity(max_capacity)),
    )
    .stack()?;
    nonzero_inx_generic_stack::fuzz(stats, rng, &mut CdGen::new(), NonZeroInxVec::new(), None)
        .stack()?;

    let a = NonZeroInxBoxedSlice::with_min_capacity(LIMIT).stack()?;
    stats.fixed_cap = Some(a.capacity());

    nonzero_inx_generic_stack::fuzz(stats, rng, &mut CdGen::new(), a, None).stack()?;

    Ok(())
}

#[test]
fn fuzz_basic_arena() -> Result<(), StackedError> {
    let rng = &mut StarRng::new(1);

    const N: usize = if cfg!(miri) {
        10_000
    } else if cfg!(debug_assertions) {
        1_000_000
    } else {
        10_000_000
    };
    const ITERS999: usize = if cfg!(miri) {
        8
    } else if cfg!(debug_assertions) {
        977
    } else {
        9956
    };
    pub const LIMIT: usize = 7;

    let mut stats = basic_arena::Stats {
        limit: LIMIT,
        n: N,
        iters999: Some(ITERS999),
    };

    fn check_arena<P: Ptr, T, B: ArenaBacking>(
        this: &mut Arena<P, T, B>,
    ) -> Result<(), StackedError> {
        if !cfg!(miri) {
            Arena::_check_invariants(this).stack()
        } else {
            Ok(())
        }
    }

    basic_arena::fuzz(
        stats,
        rng,
        &mut CdGen::new(),
        &mut CdGen::new(),
        Arena::<P2, Cd<()>, StackBacking<LIMIT>>::new(),
        check_arena,
    )
    .stack()?;

    stats.iters999 = None;

    let mut a = Arena::<P2, Cd<()>, LimitedHeapBacking>::new();
    unsafe {
        a.backing_mut().set_max_capacity(LIMIT).unwrap();
    }
    basic_arena::fuzz(
        stats,
        rng,
        &mut CdGen::new(),
        &mut CdGen::new(),
        a,
        check_arena,
    )
    .stack()?;
    basic_arena::fuzz(
        stats,
        rng,
        &mut CdGen::new(),
        &mut CdGen::new(),
        Arena::<P2, Cd<()>, HeapBacking>::new(),
        check_arena,
    )
    .stack()?;

    Ok(())
}

// for testing `clone` and `clone_from_with` which interact between multiple
// arenas, we just hardcode the heap backed arena in here
#[test]
fn fuzz_multi_arena() -> Result<(), StackedError> {
    let mut rng = StarRng::new(2);

    const N: usize = if cfg!(miri) {
        1_000
    } else if cfg!(debug_assertions) {
        1_000_000
    } else {
        10_000_000
    };
    const MAX_LEN: usize = if cfg!(miri) {
        18
    } else if cfg!(debug_assertions) {
        75
    } else {
        96
    };

    let stats = basic_arena::MultiStats {
        n: N,
        max_len: Some(MAX_LEN),
    };
    basic_arena::fuzz_multi_arena(&mut rng, stats, &mut CdGen::new(), &mut CdGen::new()).stack()?;
    Ok(())
}
