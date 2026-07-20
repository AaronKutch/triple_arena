use stacked_errors::{StackableErr, StackedError};
use testcrate::{cdgen::CdGen, nonzero_inx_generic_stack};
use triple_arena::utils::{
    NonZeroInxArray, NonZeroInxGenericStack, NonZeroInxLimitedVec, NonZeroInxVec, SetMaxCapacity,
};

#[test]
fn fuzz_nonzero_inx_generic_stack() -> Result<(), StackedError> {
    const N: usize = if cfg!(miri) { 10_000 } else { 10_000_000 };
    const ITERS999: usize = if cfg!(miri) { 5 } else { 9922 };
    pub const LIMIT: usize = 8;

    let mut stats = nonzero_inx_generic_stack::Stats {
        limit: LIMIT,
        n: N,
        iters999: Some(ITERS999),
    };
    nonzero_inx_generic_stack::fuzz(
        stats,
        &mut CdGen::new(),
        NonZeroInxArray::<_, { LIMIT }>::new(),
    )
    .stack()?;

    // TODO use a custom allocator so that this can be deterministic
    stats.iters999 = None;

    let mut a = NonZeroInxLimitedVec::new();
    a.set_max_capacity(LIMIT).unwrap();
    nonzero_inx_generic_stack::fuzz(stats, &mut CdGen::new(), a).stack()?;
    nonzero_inx_generic_stack::fuzz(stats, &mut CdGen::new(), NonZeroInxVec::new()).stack()?;

    Ok(())
}
