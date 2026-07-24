use std::{num::NonZeroUsize, slice::GetDisjointMutError};

use stacked_errors::{StackableErr, StackedError, bail, ensure, ensure_eq};
use star_rng::StarRng;
use triple_arena::{
    AllocError, MaxCapacityReductionError, NotWithinCapacityError, ReallocationError,
    utils::traits::NonZeroInxGenericStack,
};

use crate::cdgen::{Cd, CdGen, Ck};

#[derive(Clone, Copy)]
pub struct Stats {
    /// The limit that the test stays around (this is not necessarily exactly
    /// followed)
    pub test_limit: usize,
    /// If the capacity is fixed
    pub fixed_cap: Option<usize>,
    pub n: usize,
    pub iters999: Option<usize>,
}

// The `CdGen` is passed in, because otherwise it can be dropped upon returning
// an error (because it will get dropped first because of bad drop ordering that
// is verbose to correct) and give another error, all the `Cd`s will be dropped
// by the time the function returns so that the `CdGen` can be dropped then.

// The `StarRng` is passed in so that more is fuzzed across multiple calls

/// Use the [LIMIT] for fixed length types and as the limit for settable limit
/// types, ignore otherwise
pub fn fuzz<S: NonZeroInxGenericStack<Cd<()>>>(
    mut stats: Stats,
    rng: &mut StarRng,
    cd_gen: &mut CdGen<()>,
    mut a: S,
    // set iff `SetMaxCapacity` is implemented
    mut set_max_capacity: Option<fn(&mut S, usize) -> Result<(), MaxCapacityReductionError>>,
) -> Result<(), StackedError> {
    ensure!(cd_gen.is_empty());

    // reference
    let mut b: Vec<Ck<()>> = vec![];
    let mut b_capacity = a.capacity();

    // for temporary debug changes
    #[allow(unused)]
    let mut op_inx = usize::MAX;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;

    for _ in 0..stats.n {
        let len = b.len();
        ensure_eq!(cd_gen.len(), len);
        ensure_eq!(a.len(), len);
        ensure_eq!(a.is_empty(), b.is_empty());
        ensure_eq!(a.capacity(), b_capacity);
        ensure!(len <= a.capacity());
        if let Some(fixed_cap) = stats.fixed_cap {
            ensure!(a.capacity() == fixed_cap);
        }
        if let Some(max_capacity) = a.max_capacity() {
            ensure!(a.capacity() <= max_capacity);
        }
        op_inx = rng.index(1000).unwrap();
        // note: pushes and pops are balanced except for clears
        match op_inx {
            0..15 => {
                // set_max_capacity

                // except for changes, the invariants are checked at the beginning of the loop
                if let Some(set_max_capacity) = &mut set_max_capacity {
                    let before = a.capacity();
                    let max_before = a.max_capacity().stack()?;
                    if rng.next_bool() {
                        ensure!((*set_max_capacity)(&mut a, usize::MAX).is_ok());
                        // capacity can expand within the internal capacity
                        ensure!(a.capacity() >= before);
                        b_capacity = a.capacity();
                    } else {
                        let next = rng.index_inclusive(stats.test_limit);

                        if next > before {
                            // capacity can expand within the internal capacity
                            ensure!(a.capacity() >= before);
                            b_capacity = a.capacity();
                        } else if next >= a.capacity() {
                            ensure_eq!((*set_max_capacity)(&mut a, next), Ok(()));
                            // b_capacity left unchanged to check that capacity
                            // does not change
                        } else if next >= a.len() {
                            // the only type currently that implements `set_max_capacity` currently
                            // follows the tight `next >= a.next()` bound
                            ensure_eq!((*set_max_capacity)(&mut a, next), Ok(()));
                            ensure!(a.capacity() < before);
                            b_capacity = a.capacity();
                        } else {
                            ensure_eq!(
                                (*set_max_capacity)(&mut a, next),
                                Err(MaxCapacityReductionError)
                            );
                            ensure_eq!(before, a.capacity());
                            ensure_eq!(max_before, a.max_capacity().stack()?);
                        }
                    }
                    ensure!(a.capacity() <= a.max_capacity().stack()?);
                }
            }
            15..75 => {
                // reallocate_min_capacity success
                if let Some(max_capacity) = a.max_capacity()
                    && max_capacity < usize::MAX
                {
                    let new_cap = rng.index_inclusive(max_capacity);
                    a.reallocate_min_capacity(new_cap).stack()?;
                    ensure!(a.capacity() >= new_cap)
                } else {
                    let new_cap = rng.index_inclusive(stats.test_limit);
                    a.reallocate_min_capacity(new_cap).stack()?;
                    ensure!(a.capacity() >= new_cap)
                }
                b_capacity = a.capacity();
            }
            75..100 => {
                // reallocate_min_capacity failure
                let cap = a.capacity();
                if let Some(max_capacity) = a.max_capacity()
                    && max_capacity < usize::MAX
                {
                    ensure_eq!(
                        a.reallocate_min_capacity(max_capacity + 1),
                        Err(ReallocationError::BeyondMaxCapacity)
                    );
                    ensure_eq!(
                        a.reallocate_min_capacity(usize::MAX),
                        Err(ReallocationError::BeyondMaxCapacity)
                    );
                } else {
                    // could succeed for ZSTs
                    ensure_eq!(
                        a.reallocate_min_capacity(usize::MAX),
                        Err(ReallocationError::AllocError)
                    );
                }
                ensure_eq!(cap, a.capacity());
            }
            100..200 => {
                // push_within_capacity
                if len < a.capacity() {
                    let (k, t) = cd_gen.new_cd();
                    b.push(k);
                    let inx = NonZeroUsize::new(b.len()).unwrap();
                    let Ok((inx1, t1)) = a.push_within_capacity(t) else {
                        bail!("")
                    };
                    ensure_eq!((inx1, t1.key()), (inx, k));
                } else {
                    let (_, t) = cd_gen.new_cd();
                    ensure_eq!(
                        a.push_within_capacity(t).map(|_| ()),
                        Err(NotWithinCapacityError)
                    );
                }
            }
            200..250 => {
                // push_reallocating

                let max_reached = a
                    .max_capacity()
                    .is_some_and(|max_capacity| max_capacity == len)
                    || stats.fixed_cap.is_some_and(|cap| cap == len);

                if len < a.capacity() {
                    let (k, t) = cd_gen.new_cd();
                    b.push(k);
                    let inx = NonZeroUsize::new(b.len()).unwrap();
                    let Ok((inx1, t1)) = a.push_reallocating(t) else {
                        bail!("")
                    };
                    ensure_eq!((inx1, t1.key()), (inx, k));
                } else if max_reached {
                    let (_, t) = cd_gen.new_cd();
                    ensure_eq!(
                        a.push_reallocating(t).map(|_| ()),
                        Err(ReallocationError::BeyondMaxCapacity)
                    );
                } else if len >= stats.test_limit {
                    // do nothing
                } else {
                    // can increase capacity
                    let (k, t) = cd_gen.new_cd();
                    b.push(k);
                    let inx = NonZeroUsize::new(b.len()).unwrap();
                    let cap = a.capacity();
                    let Ok((inx1, t1)) = a.push_reallocating(t) else {
                        bail!("")
                    };
                    ensure_eq!((inx1, t1.key()), (inx, k));
                    // check that capacity increased
                    ensure!(a.capacity() > cap);
                    b_capacity = a.capacity();
                }
            }
            250..300 => {
                // push

                let max_reached = a
                    .max_capacity()
                    .is_some_and(|max_capacity| max_capacity == len)
                    || stats.fixed_cap.is_some_and(|cap| cap == len);

                if len < a.capacity() {
                    let (k, t) = cd_gen.new_cd();
                    b.push(k);
                    let inx = NonZeroUsize::new(b.len()).unwrap();
                    let (inx1, t1) = a.push(t);
                    ensure_eq!((inx1, t1.key()), (inx, k));
                } else if max_reached || len >= stats.test_limit {
                    // do nothing
                } else {
                    let (k, t) = cd_gen.new_cd();
                    b.push(k);
                    let inx = NonZeroUsize::new(b.len()).unwrap();
                    let cap = a.capacity();
                    let (inx1, t1) = a.push(t);
                    ensure_eq!((inx1, t1.key()), (inx, k));
                    // check that capacity increased
                    ensure!(a.capacity() > cap);
                    b_capacity = a.capacity();
                }
            }
            // FIXME entry versions
            300..500 => {
                // pop
                ensure_eq!(a.pop().map(|t| t.key()), b.pop());
            }
            500..950 => {
                // get, get_unchecked, get_unchecked_mut, get_mut
                if let Some(i) = rng.index(len) {
                    let i = NonZeroUsize::new(i + 1).unwrap();
                    ensure_eq!(a.get(i).map(|t| t.key()), b.get(i.get() - 1).copied());
                    unsafe {
                        ensure_eq!(a.get_unchecked(i).key(), *b.get_unchecked(i.get() - 1));
                    }
                }
                let i = NonZeroUsize::new(len + 1).unwrap();
                ensure!(a.get(i).is_none());
                ensure!(a.get_mut(i).is_none());
            }
            950..998 => {
                // get_disjoint_unchecked_mut, get_disjoint_mut

                let [] = a.get_disjoint_mut([]).stack()?;
                unsafe {
                    let [] = a.get_disjoint_unchecked_mut([]);
                }

                let i = NonZeroUsize::new(len + 1).unwrap();
                ensure!(
                    a.get_disjoint_mut([i])
                        .is_err_and(|e| e == GetDisjointMutError::IndexOutOfBounds)
                );

                'outer: {
                    let mut set = [NonZeroUsize::new(1).unwrap(); 4];
                    if len >= set.len() {
                        for i in &mut set {
                            *i = NonZeroUsize::new(rng.index(len).unwrap() + 1).unwrap();
                        }
                        for (set_i0, i) in set.iter().enumerate() {
                            for (set_i1, j) in set.iter().enumerate() {
                                if set_i0 != set_i1 && *i == *j {
                                    ensure!(a.get_disjoint_mut(set).is_err_and(
                                        |e| e == GetDisjointMutError::OverlappingIndices
                                    ));
                                    break 'outer;
                                }
                            }
                        }

                        ensure_eq!(
                            a.get_disjoint_mut(set).stack()?.map(|t| t.key()),
                            b.get_disjoint_mut(set.map(|i| i.get() - 1))
                                .unwrap()
                                .map(|k| *k)
                        );
                    }
                }
            }
            998 => {
                // clear
                a.clear();
                b.clear();
            }
            999 => {
                // with_min_capacity and the `Drop` impl
                b.clear();
                // note that we bypass max capacity limits since they are set to begin with in
                // some cases from this function

                // could succeed for ZSTs
                ensure_eq!(
                    S::with_min_capacity(usize::MAX).map(|_| ()),
                    Err(AllocError)
                );

                let min_capacity = rng.index_inclusive(stats.test_limit);
                a = S::with_min_capacity(min_capacity).stack()?;
                ensure!(a.capacity() >= min_capacity);
                if stats.fixed_cap.is_some() {
                    stats.fixed_cap = Some(a.capacity());
                }
                b_capacity = a.capacity();
                iters999 += 1;
            }
            1000.. => unreachable!(),
        }
    }
    if let Some(x) = stats.iters999 {
        ensure_eq!(iters999, x);
    }
    Ok(())
}
