use stacked_errors::{StackableErr, StackedError};
use testcrate::nonzero_inx_generic_stack;
use triple_arena::utils::{NonZeroInxGenericStack, NonZeroInxLimitedVec, SettableCapacityLimit};

#[test]
fn fuzz_nonzero_inx_generic_stack() -> Result<(), StackedError> {
    let mut a = NonZeroInxLimitedVec::new();
    a.set_capacity_limit(nonzero_inx_generic_stack::LIMIT);
    nonzero_inx_generic_stack::fuzz(a).stack()?;

    Ok(())
}
