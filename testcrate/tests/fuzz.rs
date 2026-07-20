use stacked_errors::{StackableErr, StackedError};
use star_rng::StarRng;
use testcrate::{
    P2, basic_arena,
    cdgen::{Cd, CdGen},
    nonzero_inx_generic_stack,
};
use triple_arena::{
    Arena,
    traits::Ptr,
    utils::{
        ArenaBacking, NonZeroInxArray, NonZeroInxGenericStack, NonZeroInxLimitedVec, NonZeroInxVec,
        SetMaxCapacity, StackBacking,
    },
};

#[test]
fn fuzz_nonzero_inx_generic_stack() -> Result<(), StackedError> {
    let rng = &mut StarRng::new(0);

    const N: usize = if cfg!(miri) { 10_000 } else { 10_000_000 };
    const ITERS999: usize = if cfg!(miri) { 5 } else { 9819 };
    pub const LIMIT: usize = 7;

    let mut stats = nonzero_inx_generic_stack::Stats {
        limit: LIMIT,
        n: N,
        iters999: Some(ITERS999),
    };
    nonzero_inx_generic_stack::fuzz(
        stats,
        rng,
        &mut CdGen::new(),
        NonZeroInxArray::<_, { LIMIT }>::new(),
    )
    .stack()?;

    // I could get a custom allocator to make this deterministic, but I think one
    // check is good enough
    stats.iters999 = None;

    let mut a = NonZeroInxLimitedVec::new();
    a.set_max_capacity(LIMIT).unwrap();
    nonzero_inx_generic_stack::fuzz(stats, rng, &mut CdGen::new(), a).stack()?;
    nonzero_inx_generic_stack::fuzz(stats, rng, &mut CdGen::new(), NonZeroInxVec::new()).stack()?;

    Ok(())
}

#[test]
fn fuzz_basic_arena() -> Result<(), StackedError> {
    let rng = &mut StarRng::new(1);

    const N: usize = if cfg!(miri) { 10_000 } else { 10_000_000 };
    const ITERS999: usize = if cfg!(miri) { 5 } else { 9939 };
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
        Arena::<P2, Cd<()>, StackBacking<LIMIT>>::new(),
        check_arena,
    )
    .stack()?;

    stats.iters999 = None;
    /*
    let mut a = NonZeroInxLimitedVec::new();
    a.set_max_capacity(LIMIT).unwrap();
    basic_arena::fuzz(stats, &mut CdGen::new(), a).stack()?;
    basic_arena::fuzz(stats, &mut CdGen::new(), NonZeroInxVec::new()).stack()?;*/

    Ok(())
}
