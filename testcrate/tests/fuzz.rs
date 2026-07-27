use expect_test::expect;
use stacked_errors::{StackableErr, StackedError};
use star_rng::StarRng;
use testcrate::{
    P2,
    basic_arena::{self},
    cdgen::{Cd, CdGen},
    misc::Meta,
    nonzero_inx_generic_stack,
};
use triple_arena::{
    Arena, StackBacking,
    traits::{ArenaTrait, Ptr},
    utils::{
        NonZeroInxArray,
        traits::{ArenaBacking, NonZeroInxGenericStack},
    },
};
#[cfg(feature = "alloc")]
use triple_arena::{
    FixedHeapBacking, HeapBacking, LimitedHeapBacking,
    utils::{NonZeroInxBoxedSlice, NonZeroInxLimitedVec, NonZeroInxVec, traits::SetMaxCapacity},
};

#[test]
fn fuzz_nonzero_inx_generic_stack() -> Result<(), StackedError> {
    let mut meta = Meta::new(0);

    const N: usize = if cfg!(miri) {
        10_000
    } else if cfg!(debug_assertions) {
        1_000_000
    } else {
        10_000_000
    };
    pub const LIMIT: usize = 7;

    fn inner(meta: &mut Meta<nonzero_inx_generic_stack::Stats>) -> Result<(), StackedError> {
        // I could get a custom allocator to make this deterministic, but I think one
        // check is on non Miri arrays is good enough
        let iters999 = if cfg!(miri) {
            None
        } else if cfg!(debug_assertions) {
            Some(expect![[r#"
                944
            "#]])
        } else {
            Some(expect![[r#"
                9826
            "#]])
        };
        meta.test(
            nonzero_inx_generic_stack::Stats {
                test_limit: LIMIT,
                fixed_cap: Some(LIMIT),
                n: N,
                iters999,
                cd_gen: CdGen::new(),
            },
            |meta| {
                nonzero_inx_generic_stack::fuzz(
                    meta,
                    &mut NonZeroInxArray::<_, { LIMIT }>::new(),
                    None,
                )
            },
        )
        .stack()?;

        #[cfg(feature = "alloc")]
        {
            let mut a = NonZeroInxLimitedVec::new();
            a.set_max_capacity(LIMIT).unwrap();
            meta.test(
                nonzero_inx_generic_stack::Stats {
                    test_limit: LIMIT,
                    fixed_cap: None,
                    n: N,
                    iters999: None,
                    cd_gen: CdGen::new(),
                },
                |meta| {
                    nonzero_inx_generic_stack::fuzz(
                        meta,
                        &mut a,
                        Some(|a, max_capacity| a.set_max_capacity(max_capacity)),
                    )
                },
            )
            .stack()?;

            meta.test(
                nonzero_inx_generic_stack::Stats {
                    test_limit: LIMIT,
                    fixed_cap: None,
                    n: N,
                    iters999: None,
                    cd_gen: CdGen::new(),
                },
                |meta| nonzero_inx_generic_stack::fuzz(meta, &mut NonZeroInxVec::new(), None),
            )
            .stack()?;

            let mut a = NonZeroInxBoxedSlice::with_min_capacity(LIMIT).stack()?;
            let stats = nonzero_inx_generic_stack::Stats {
                test_limit: LIMIT,
                fixed_cap: Some(a.capacity()),
                n: N,
                iters999: None,
                cd_gen: CdGen::new(),
            };
            meta.test(stats, |meta| {
                nonzero_inx_generic_stack::fuzz(meta, &mut a, None)
            })
            .stack()?;
        }

        Ok(())
    }

    if let Err(e) = inner(&mut meta).stack_err(format!("{meta:#?}")) {
        Err(e)
    } else {
        Ok(())
    }
}

#[test]
fn fuzz_basic_arena() -> Result<(), StackedError> {
    let mut meta = Meta::new(7);

    const N: usize = if cfg!(miri) {
        100
    } else if cfg!(debug_assertions) {
        1_000_000
    } else {
        10_000_000
    };
    pub const LIMIT: usize = 7;

    fn check_arena<P: Ptr, T, B: ArenaBacking>(
        this: &mut Arena<P, T, B>,
    ) -> Result<(), StackedError> {
        if !cfg!(miri) {
            Arena::_check_invariants(this).stack()
        } else {
            Ok(())
        }
    }

    fn inner(meta: &mut Meta<basic_arena::Stats>) -> Result<(), StackedError> {
        let iters999 = if cfg!(miri) {
            None
        } else if cfg!(debug_assertions) {
            Some(expect![[r#"
                980
            "#]])
        } else {
            Some(expect![[r#"
                9852
            "#]])
        };
        meta.test(
            basic_arena::Stats {
                test_limit: LIMIT,
                fixed_cap: Some(LIMIT),
                n: N,
                iters999,
                cd_gen: CdGen::new(),
                cd_gen1: CdGen::new(),
            },
            |meta| {
                basic_arena::fuzz(
                    meta,
                    &mut Arena::<P2, Cd<()>, StackBacking<LIMIT>>::new(),
                    check_arena,
                    None,
                )
            },
        )
        .stack()?;

        #[cfg(feature = "alloc")]
        {
            let mut a = Arena::<P2, Cd<()>, LimitedHeapBacking>::new();
            a.set_max_capacity(LIMIT).stack()?;
            meta.test(
                basic_arena::Stats {
                    test_limit: LIMIT,
                    fixed_cap: None,
                    n: N,
                    iters999: None,
                    cd_gen: CdGen::new(),
                    cd_gen1: CdGen::new(),
                },
                |meta| {
                    basic_arena::fuzz(
                        meta,
                        &mut a,
                        check_arena,
                        Some(|a, max_capacity| a.set_max_capacity(max_capacity)),
                    )
                },
            )
            .stack()?;

            meta.test(
                basic_arena::Stats {
                    test_limit: LIMIT,
                    fixed_cap: None,
                    n: N,
                    iters999: None,
                    cd_gen: CdGen::new(),
                    cd_gen1: CdGen::new(),
                },
                |meta| {
                    basic_arena::fuzz(
                        meta,
                        &mut Arena::<P2, Cd<()>, HeapBacking>::new(),
                        check_arena,
                        None,
                    )
                },
            )
            .stack()?;

            let mut a = Arena::<P2, Cd<()>, FixedHeapBacking>::with_min_capacity(LIMIT).stack()?;
            let stats = basic_arena::Stats {
                test_limit: LIMIT,
                fixed_cap: Some(ArenaTrait::capacity(&a)), // FIXME
                n: N,
                iters999: None,
                cd_gen: CdGen::new(),
                cd_gen1: CdGen::new(),
            };
            meta.test(stats, |meta| {
                basic_arena::fuzz(meta, &mut a, check_arena, None)
            })
            .stack()?;
        }

        Ok(())
    }

    if let Err(e) = inner(&mut meta).stack_err(format!("{meta:#?}")) {
        Err(e)
    } else {
        Ok(())
    }
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
