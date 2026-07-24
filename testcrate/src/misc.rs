use core::fmt;
use std::error::Error;

use stacked_errors::{StackableErr, StackedError};
use star_rng::StarRng;

use crate::cdgen::TryInternalDrop;

/// For inspecting state right before a failure
#[derive(Debug)]
pub struct Meta<T: fmt::Debug + TryInternalDrop> {
    pub rng: StarRng,
    pub i: usize,
    pub op_inx: usize,
    pub stats: Option<T>,
}

impl<T: fmt::Debug + TryInternalDrop> fmt::Display for Meta<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{self:#?}"))
    }
}

impl<T: fmt::Debug + TryInternalDrop> Error for Meta<T> {}

impl<T: fmt::Debug + TryInternalDrop> Meta<T> {
    pub fn new(seed: u64) -> Self {
        Self {
            rng: StarRng::new(seed),
            i: usize::MAX,
            op_inx: usize::MAX,
            stats: None,
        }
    }

    pub fn test<F: FnOnce(&mut Meta<T>) -> Result<(), StackedError>>(
        &mut self,
        stats: T,
        f: F,
    ) -> Result<(), StackedError> {
        self.i = usize::MAX;
        self.op_inx = usize::MAX;
        self.stats = Some(stats);
        let res = f(self).stack();
        let drop_res = self.stats.take().unwrap().try_internal_drop().stack();
        // this is to prevent drop errors from completely overriding root causes
        if let Err(e) = drop_res {
            if let Err(e1) = res.stack_err("both a drop error and normal error happened") {
                return Err(e1.chain_errors(e));
            } else {
                return Err(e);
            }
        }
        res
    }
}

/// For second domains
#[derive(Clone, Copy, Default)]
pub struct D1;
