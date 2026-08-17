use stacked_errors::{StackableErr, StackedError, ensure, ensure_eq};
use triple_arena::{
    ChainArena, InvalidationOption, StackBacking,
    errors::{AllocError, MaxCapacityReductionError, ReallocationError},
    traits::{ArenaCloneFromWith, ArenaTrait, ChainArenaTrait, CompactArenaTrait, Ptr},
    utils::traits::PtrGen,
};

use crate::{
    TestGen,
    basic_arena::{Stats, gen_invalid},
    cdgen::{Cd, Ck, CkMap},
    misc::{D1, Meta},
};

struct TLink<P> {
    prev: Ck<()>,
    next: Ck<()>,
    p: P,
}

pub fn fuzz<
    P: Ptr,
    A: ArenaCloneFromWith<P, Cd<()>> + CompactArenaTrait<P, Cd<()>> + ChainArenaTrait<P, Cd<()>>,
>(
    meta: &mut Meta<Stats>,
    a: &mut A,
    mut check_invariants: impl FnMut(&mut A) -> Result<(), StackedError>,
    // set iff `SetMaxCapacity` is implemented
    set_max_capacity: Option<fn(&mut A, usize) -> Result<(), MaxCapacityReductionError>>,
    // set iff `transfer_reallocating` is available
    mut transfer_reallocating: Option<
        fn(
            &mut A,
            P::Gen,
            &mut ChainArena<P, Cd<D1>, StackBacking<128>>,
            &mut dyn FnMut(P, InvalidationOption<Cd<D1>>, P) -> Cd<()>,
        ) -> Result<(), ReallocationError>,
    >,
) -> Result<(), StackedError> {
    let rng = &mut meta.rng;
    let stats = meta.stats.as_mut().stack()?;
    let cd_gen = &mut stats.cd_gen;
    let cd_gen1 = &mut stats.cd_gen1;

    // the interlinks are the `(Ck<()>, Ck<()>)`
    let mut b = CkMap::<(), TLink<P>>::new();
    let mut b_capacity = a.capacity();
    let mut g = TestGen::<P>(PtrGen::two());

    // set and used by the clone_from section
    let mut a1 = ChainArena::<P, Cd<D1>, StackBacking<128>>::new();

    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;

    for i in 0..stats.n {
        let len = b.len();
        ensure_eq!(cd_gen.len(), len);
        ensure_eq!(a.len(), len);
        ensure_eq!(a.is_empty(), b.is_empty());
        ensure_eq!(a.capacity(), b_capacity);
        ensure!(len <= a.capacity());
        if let Some(fixed_cap) = stats.fixed_cap {
            ensure_eq!(a.capacity(), fixed_cap);
        }
        if let Some(max_capacity) = a.max_capacity() {
            ensure!(a.capacity() <= max_capacity);
        }
        // if not incremented explicitly and the arena increments, then we get a
        // mismatch
        ensure_eq!(a.singular_generation().unwrap(), g.0);
        check_invariants(a).stack()?;

        meta.i = i;
        meta.op_inx = rng.index_inclusive(1023);
        // note: pushes and pops are balanced except for clears which we make rare
        match meta.op_inx {
            0..250 => crate::basic_arena::common_compact_fuzz_step250(
                rng,
                a,
                stats.test_limit,
                meta.op_inx,
                &mut b,
                &mut b_capacity,
                &mut g,
                set_max_capacity,
                |b, rng| b.get_mut_rand(rng).map(|(k, link)| (k, &mut link.p)),
            )
            .stack()?,
            // FIXME
            250..500 => {}
            500..750 => {}
            // FIXME
            // extra room
            /*750..998 => {
                if let Some((_, link)) = b.get_rand(rng) {
                    ensure!(a.contains(link.p));
                } else {
                    let p = gen_invalid(rng, a);
                    ensure!(!a.contains(p));
                }
            }
            998 => {
                // clear
                b.clear();
                if a.is_empty() {
                    ensure_eq!(a.clear(), InvalidationOption::Success(()));
                } else {
                    ensure_eq!(a.clear().is_overflow(), g.invalidate());
                }
            }
            999 => {
                // with_min_capacity and the `Drop` impl
                b.clear();
                // note that we bypass max capacity limits since they are set to begin with in
                // some cases from this function

                // could succeed for ZSTs
                ensure_eq!(
                    A::with_min_capacity(usize::MAX).map(|_| ()),
                    Err(AllocError)
                );

                let min_capacity = rng.index_inclusive(stats.test_limit);
                *a = A::with_min_capacity(min_capacity).stack()?;
                ensure!(a.capacity() >= min_capacity);
                if stats.fixed_cap.is_some() {
                    stats.fixed_cap = Some(a.capacity());
                }
                g.0 = a.singular_generation().unwrap();
                b_capacity = a.capacity();
                iters999 += 1;
            }*/
            750.. => unreachable!(),
        }
    }
    if let Some(x) = &stats.iters999 {
        x.assert_debug_eq(&iters999);
    }
    a.clear().allow();
    Ok(())
}
