use std::slice::GetDisjointMutError;

use stacked_errors::{StackableErr, StackedError, bail, ensure, ensure_eq};
use star_rng::StarRng;
use triple_arena::{traits::ArenaTrait, utils::AllocError};

use crate::{
    P0,
    cdgen::{Cd, CdGen, CdKey},
};

#[derive(Clone, Copy)]
pub struct Stats {
    pub limit: usize,
    pub n: usize,
    pub iters999: Option<usize>,
}

/// Use the [LIMIT] for fixed length types and as the limit for settable limit
/// types, ignore otherwise
pub fn fuzz(
    stats: Stats,
    cd_gen: &mut CdGen<()>,
    mut a: impl ArenaTrait<P0, Cd<()>>,
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

    for _ in 0..stats.n {
        let len = b.len();
        ensure!(cd_gen.len() <= len);
        ensure_eq!(a.len(), len);
        ensure_eq!(a.is_empty(), b.is_empty());
        ensure!(len <= a.capacity());
        let limited = a.max_capacity().is_some();
        if let Some(limit) = a.max_capacity() {
            // required for caller
            ensure_eq!(limit, stats.limit);

            ensure!(a.capacity() <= limit);
        }
        op_inx = rng.index(1000).unwrap();
        match op_inx {
            1000.. => unreachable!(),
        }
    }
    if let Some(x) = stats.iters999 {
        ensure_eq!(iters999, x);
    }
    Ok(())
}
