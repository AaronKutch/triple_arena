use expect_test::{Expect, expect};
use stacked_errors::{StackableErr, StackedError};
use star_rng::StarRng;
use testcrate::{
    P2,
    basic_arena::{self},
    cdgen::{Cd, CdGen},
    direct_arena,
    misc::Meta,
    nonzero_inx_generic_stack,
};
use triple_arena::{
    Arena, DirectArena, StackBacking,
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
                947
            "#]])
        } else {
            Some(expect![[r#"
                9905
            "#]])
        };
        let max_len = if cfg!(miri) {
            None
        } else if cfg!(debug_assertions) {
            Some(expect![[r#"
                7
            "#]])
        } else {
            Some(expect![[r#"
                7
            "#]])
        };
        meta.test(
            nonzero_inx_generic_stack::Stats {
                test_limit: LIMIT,
                fixed_cap: Some(LIMIT),
                n: N,
                iters999,
                max_len,
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
                    max_len: None,
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
                    max_len: None,
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
                max_len: None,
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
                1018
            "#]])
        } else {
            Some(expect![[r#"
                9894
            "#]])
        };
        let max_len = if cfg!(miri) {
            None
        } else if cfg!(debug_assertions) {
            Some(expect![[r#"
                7
            "#]])
        } else {
            Some(expect![[r#"
                7
            "#]])
        };
        meta.test(
            basic_arena::Stats {
                test_limit: LIMIT,
                fixed_cap: Some(LIMIT),
                n: N,
                iters999,
                max_len,
                cd_gen: CdGen::new(),
                cd_gen1: CdGen::new(),
            },
            |meta| {
                basic_arena::fuzz(
                    meta,
                    &mut Arena::<P2, Cd<()>, StackBacking<LIMIT>>::new(),
                    check_arena,
                    None,
                    Some(|a, new_gen, src, map| a.transfer_reallocating(new_gen, src, map)),
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
                    max_len: None,
                    cd_gen: CdGen::new(),
                    cd_gen1: CdGen::new(),
                },
                |meta| {
                    basic_arena::fuzz(
                        meta,
                        &mut a,
                        check_arena,
                        Some(|a, max_capacity| a.set_max_capacity(max_capacity)),
                        Some(|a, new_gen, src, map| a.transfer_reallocating(new_gen, src, map)),
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
                    max_len: None,
                    cd_gen: CdGen::new(),
                    cd_gen1: CdGen::new(),
                },
                |meta| {
                    basic_arena::fuzz(
                        meta,
                        &mut Arena::<P2, Cd<()>, HeapBacking>::new(),
                        check_arena,
                        None,
                        Some(|a, new_gen, src, map| a.transfer_reallocating(new_gen, src, map)),
                    )
                },
            )
            .stack()?;

            let mut a = Arena::<P2, Cd<()>, FixedHeapBacking>::with_min_capacity(LIMIT).stack()?;
            let stats = basic_arena::Stats {
                test_limit: LIMIT,
                fixed_cap: Some(a.capacity()),
                n: N,
                iters999: None,
                max_len: None,
                cd_gen: CdGen::new(),
                cd_gen1: CdGen::new(),
            };
            meta.test(stats, |meta| {
                basic_arena::fuzz(
                    meta,
                    &mut a,
                    check_arena,
                    None,
                    Some(|a, new_gen, src, map| a.transfer_reallocating(new_gen, src, map)),
                )
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
fn fuzz_direct_arena() -> Result<(), StackedError> {
    let mut meta = Meta::new(11);

    const N: usize = if cfg!(miri) {
        100
    } else if cfg!(debug_assertions) {
        1_000_000
    } else {
        10_000_000
    };
    pub const LIMIT: usize = 7;

    fn check_arena<P: Ptr, T, B: ArenaBacking>(
        this: &mut DirectArena<P, T, B>,
    ) -> Result<(), StackedError> {
        if !cfg!(miri) {
            DirectArena::_check_invariants(this).stack()
        } else {
            Ok(())
        }
    }

    fn inner(meta: &mut Meta<direct_arena::Stats>) -> Result<(), StackedError> {
        let iters999 = if cfg!(miri) {
            None
        } else if cfg!(debug_assertions) {
            Some(expect![[r#"
                934
            "#]])
        } else {
            Some(expect![[r#"
                9852
            "#]])
        };
        let max_len = if cfg!(miri) {
            None
        } else if cfg!(debug_assertions) {
            Some(expect![[r#"
                7
            "#]])
        } else {
            Some(expect![[r#"
                7
            "#]])
        };
        meta.test(
            direct_arena::Stats {
                test_limit: LIMIT,
                fixed_cap: Some(LIMIT),
                n: N,
                iters999,
                max_len,
                cd_gen: CdGen::new(),
                cd_gen1: CdGen::new(),
            },
            |meta| {
                direct_arena::fuzz(
                    meta,
                    &mut DirectArena::<P2, Cd<()>, StackBacking<LIMIT>>::new(),
                    check_arena,
                    None,
                    |a, new_gen, src, map| a.transfer_reallocating(new_gen, src, map),
                )
            },
        )
        .stack()?;

        #[cfg(feature = "alloc")]
        {
            let mut a = DirectArena::<P2, Cd<()>, LimitedHeapBacking>::new();
            a.set_max_capacity(LIMIT).stack()?;
            meta.test(
                direct_arena::Stats {
                    test_limit: LIMIT,
                    fixed_cap: None,
                    n: N,
                    iters999: None,
                    max_len: None,
                    cd_gen: CdGen::new(),
                    cd_gen1: CdGen::new(),
                },
                |meta| {
                    direct_arena::fuzz(
                        meta,
                        &mut a,
                        check_arena,
                        Some(|a, max_capacity| a.set_max_capacity(max_capacity)),
                        |a, new_gen, src, map| a.transfer_reallocating(new_gen, src, map),
                    )
                },
            )
            .stack()?;

            meta.test(
                direct_arena::Stats {
                    test_limit: LIMIT,
                    fixed_cap: None,
                    n: N,
                    iters999: None,
                    max_len: None,
                    cd_gen: CdGen::new(),
                    cd_gen1: CdGen::new(),
                },
                |meta| {
                    direct_arena::fuzz(
                        meta,
                        &mut DirectArena::<P2, Cd<()>, HeapBacking>::new(),
                        check_arena,
                        None,
                        |a, new_gen, src, map| a.transfer_reallocating(new_gen, src, map),
                    )
                },
            )
            .stack()?;

            let mut a =
                DirectArena::<P2, Cd<()>, FixedHeapBacking>::with_min_capacity(LIMIT).stack()?;
            let stats = direct_arena::Stats {
                test_limit: LIMIT,
                fixed_cap: Some(a.capacity()),
                n: N,
                iters999: None,
                max_len: None,
                cd_gen: CdGen::new(),
                cd_gen1: CdGen::new(),
            };
            meta.test(stats, |meta| {
                direct_arena::fuzz(meta, &mut a, check_arena, None, |a, new_gen, src, map| {
                    a.transfer_reallocating(new_gen, src, map)
                })
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
    const MAX_LEN: Option<Expect> = if cfg!(miri) {
        None
    } else if cfg!(debug_assertions) {
        Some(expect![[r#"
            32
        "#]])
    } else {
        Some(expect![[r#"
            46
        "#]])
    };

    let stats = basic_arena::MultiStats {
        n: N,
        max_len: MAX_LEN,
    };
    basic_arena::fuzz_multi_arena::<P2>(&mut rng, stats, &mut CdGen::new(), &mut CdGen::new())
        .stack()?;
    Ok(())
}

#[test]
fn fuzz_multi_direct_arena() -> Result<(), StackedError> {
    let mut rng = StarRng::new(13);

    const N: usize = if cfg!(miri) {
        1_000
    } else if cfg!(debug_assertions) {
        1_000_000
    } else {
        10_000_000
    };
    const MAX_LEN: Option<Expect> = if cfg!(miri) {
        None
    } else if cfg!(debug_assertions) {
        Some(expect![[r#"
            65
        "#]])
    } else {
        Some(expect![[r#"
            75
        "#]])
    };

    let stats = direct_arena::MultiStats {
        n: N,
        max_len: MAX_LEN,
    };
    direct_arena::fuzz_multi_direct_arena::<P2>(
        &mut rng,
        stats,
        &mut CdGen::new(),
        &mut CdGen::new(),
    )
    .stack()?;
    Ok(())
}
