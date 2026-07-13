use stacked_errors::{StackableErr, StackedError};
use testcrate::nonzero_inx_generic_stack;
use triple_arena::utils::{NonZeroInxGenericStack, NonZeroInxLimitedVec, SetMaxCapacity};

#[test]
fn fuzz_nonzero_inx_generic_stack() -> Result<(), StackedError> {
    let mut a = NonZeroInxLimitedVec::new();
    a.set_max_capacity(nonzero_inx_generic_stack::LIMIT)
        .unwrap();
    nonzero_inx_generic_stack::fuzz(a).stack()?;

    Ok(())
}
