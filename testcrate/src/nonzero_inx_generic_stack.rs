use std::{num::NonZeroUsize, slice::GetDisjointMutError};

use stacked_errors::{StackableErr, StackedError, bail, ensure, ensure_eq};
use star_rng::StarRng;
use triple_arena::utils::{AllocError, NonZeroInxGenericStack};

use crate::cdgen::{Cd, CdGen, CdKey};

const N: usize = if cfg!(miri) { 1000 } else { 1_000_000 };

const STATS: usize = if cfg!(miri) { 1 } else { 1020 };

pub const LIMIT: usize = 8;

// the `CdGen` is passed in, because otherwise it can be dropped upon returning
// an error

/// Use the [LIMIT] for fixed length types and as the limit for settable limit
/// types, ignore otherwise
pub fn fuzz(
    cd_gen: &mut CdGen<()>,
    mut a: impl NonZeroInxGenericStack<Cd<()>>,
) -> Result<(), StackedError> {
    ensure!(cd_gen.is_empty());
    let mut rng = StarRng::new(0);

    // reference
    let mut b: Vec<CdKey> = vec![];

    // for temporary debug changes
    #[allow(unused)]
    let mut op_inx = usize::MAX;
    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;

    for _ in 0..N {
        let len = b.len();
        ensure_eq!(a.len(), len);
        ensure_eq!(a.is_empty(), b.is_empty());
        ensure!(len <= a.capacity());
        ensure!(a.capacity() <= LIMIT);
        ensure!(cd_gen.len() <= LIMIT);
        let limited = a.max_capacity().is_some();
        if let Some(limit) = a.max_capacity() {
            // required for caller
            ensure_eq!(limit, LIMIT);

            ensure!(a.capacity() <= limit);
        }
        op_inx = rng.index(1000).unwrap();
        match op_inx {
            0..20 => {
                // reallocate_min_capacity success
                let new_cap = rng.index(LIMIT + 1).unwrap();
                a.reallocate_min_capacity(new_cap).stack()?;
                ensure!(a.capacity() >= new_cap)
            }
            20..25 => {
                // reallocate_min_capacity failure
                let cap = a.capacity();
                if limited {
                    ensure_eq!(a.reallocate_min_capacity(LIMIT + 1), Err(AllocError));
                } else {
                    // could fail for ZSTs
                    ensure_eq!(a.reallocate_min_capacity(usize::MAX), Err(AllocError));
                }
                ensure_eq!(cap, a.capacity());
            }
            25..100 => {}
            100..300 => {
                // push_within_capacity
                if len < a.capacity() {
                    let (k, t) = cd_gen.next(());
                    b.push(k);
                    let inx = NonZeroUsize::new(b.len()).unwrap();
                    let Ok((inx1, t1)) = a.push_within_capacity(t) else {
                        bail!("")
                    };
                    ensure_eq!((inx1, t1.key()), (inx, k));
                } else {
                    let (k, t) = cd_gen.next(());
                    ensure!(a.push_within_capacity(t).is_err_and(|t| t.key() == k));
                }
            }
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
            950..999 => {
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
            999 => {
                // clear
                a.clear();
                b.clear();
                iters999 += 1;
            }
            1000.. => unreachable!(),
        }
    }
    // I may need a custom allocator, because some of the determinism is dependent
    // on reallocation behavior
    ensure_eq!(iters999, STATS);
    Ok(())
}
