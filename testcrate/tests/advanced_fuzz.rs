use expect_test::expect;
use stacked_errors::{StackableErr, StackedError};
use star_rng::StarRng;
use testcrate::{
    P2,
    cdgen::{Cd, CdGen},
    chain_arena,
    misc::Meta,
};
use triple_arena::{
    ChainArena, StackBacking,
    traits::{ArenaTrait, Ptr},
    utils::traits::ArenaBacking,
};
#[cfg(feature = "alloc")]
use triple_arena::{
    FixedHeapBacking, HeapBacking, LimitedHeapBacking, utils::traits::SetMaxCapacity,
};

#[test]
fn fuzz_chain_arena() -> Result<(), StackedError> {
    let mut meta = Meta::new(17);

    const N: usize = if cfg!(miri) {
        100
    } else if cfg!(debug_assertions) {
        1_000_000
    } else {
        10_000_000
    };
    pub const LIMIT: usize = 7;

    fn check_arena<P: Ptr, T, B: ArenaBacking>(
        this: &mut ChainArena<P, T, B>,
    ) -> Result<(), StackedError> {
        if !cfg!(miri) {
            ChainArena::_check_invariants(this).stack()
        } else {
            Ok(())
        }
    }

    fn inner(meta: &mut Meta<chain_arena::Stats>) -> Result<(), StackedError> {
        let iters999 = if cfg!(miri) {
            None
        } else if cfg!(debug_assertions) {
            Some(expect![[r#"
                985
            "#]])
        } else {
            Some(expect![[r#"
                9793
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
            chain_arena::Stats {
                test_limit: LIMIT,
                fixed_cap: Some(LIMIT),
                n: N,
                iters999,
                max_len,
                cd_gen: CdGen::new(),
                cd_gen1: CdGen::new(),
            },
            |meta| {
                chain_arena::fuzz(
                    meta,
                    &mut ChainArena::<P2, Cd<()>, StackBacking<LIMIT>>::new(),
                    check_arena,
                    None,
                    |a1: &mut ChainArena<P2, Cd<_>, StackBacking<128>>, a, map| {
                        a1.clone_from_with(a, map)
                    },
                    |a, a1, map| a.clone_from_with(a1, map),
                    |a, new_gen, src, map, recaster| {
                        a.transfer_canonical_reallocating(new_gen, src, map, recaster)
                    },
                )
            },
        )
        .stack()?;

        #[cfg(feature = "alloc")]
        {
            let mut a = ChainArena::<P2, Cd<()>, LimitedHeapBacking>::new();
            a.set_max_capacity(LIMIT).stack()?;
            meta.test(
                chain_arena::Stats {
                    test_limit: LIMIT,
                    fixed_cap: None,
                    n: N,
                    iters999: None,
                    max_len: None,
                    cd_gen: CdGen::new(),
                    cd_gen1: CdGen::new(),
                },
                |meta| {
                    chain_arena::fuzz(
                        meta,
                        &mut a,
                        check_arena,
                        Some(|a, max_capacity| a.set_max_capacity(max_capacity)),
                        |a1: &mut ChainArena<P2, Cd<_>, HeapBacking>, a, map| {
                            a1.clone_from_with(a, map)
                        },
                        |a, a1, map| a.clone_from_with(a1, map),
                        |a, new_gen, src, map, recaster| {
                            a.transfer_canonical_reallocating(new_gen, src, map, recaster)
                        },
                    )
                },
            )
            .stack()?;

            meta.test(
                chain_arena::Stats {
                    test_limit: LIMIT,
                    fixed_cap: None,
                    n: N,
                    iters999: None,
                    max_len: None,
                    cd_gen: CdGen::new(),
                    cd_gen1: CdGen::new(),
                },
                |meta| {
                    chain_arena::fuzz(
                        meta,
                        &mut ChainArena::<P2, Cd<()>, HeapBacking>::new(),
                        check_arena,
                        None,
                        |a1: &mut ChainArena<P2, Cd<_>, StackBacking<128>>, a, map| {
                            a1.clone_from_with(a, map)
                        },
                        |a, a1, map| a.clone_from_with(a1, map),
                        |a, new_gen, src, map, recaster| {
                            a.transfer_canonical_reallocating(new_gen, src, map, recaster)
                        },
                    )
                },
            )
            .stack()?;

            let mut a =
                ChainArena::<P2, Cd<()>, FixedHeapBacking>::with_min_capacity(LIMIT).stack()?;
            let stats = chain_arena::Stats {
                test_limit: LIMIT,
                fixed_cap: Some(a.capacity()),
                n: N,
                iters999: None,
                max_len: None,
                cd_gen: CdGen::new(),
                cd_gen1: CdGen::new(),
            };
            meta.test(stats, |meta| {
                chain_arena::fuzz(
                    meta,
                    &mut a,
                    check_arena,
                    None,
                    |a1: &mut ChainArena<P2, Cd<_>, HeapBacking>, a, map| {
                        a1.clone_from_with(a, map)
                    },
                    |a, a1, map| a.clone_from_with(a1, map),
                    |a, new_gen, src, map, recaster| {
                        a.transfer_canonical_reallocating(new_gen, src, map, recaster)
                    },
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
fn fuzz_multi_chain_arena() -> Result<(), StackedError> {
    let mut rng = StarRng::new(19);

    const N: usize = if cfg!(miri) {
        1_000
    } else if cfg!(debug_assertions) {
        1_000_000
    } else {
        10_000_000
    };
    // miri is only really necessary at the lower levels
    let max_len = if cfg!(miri) {
        None
    } else if cfg!(debug_assertions) {
        Some(expect![[r#"
            24
        "#]])
    } else {
        Some(expect![[r#"
            26
        "#]])
    };

    let stats = chain_arena::MultiStats { n: N, max_len };
    chain_arena::fuzz_multi_chain_arena::<P2>(
        &mut rng,
        stats,
        &mut CdGen::new(),
        &mut CdGen::new(),
    )
    .stack()?;
    Ok(())
}
