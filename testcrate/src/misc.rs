use core::fmt;
use std::error::Error;

use star_rng::StarRng;

/// For inspecting state right before a failure
#[derive(Debug)]
pub struct Meta<T: fmt::Debug> {
    pub rng: StarRng,
    pub i: usize,
    pub op_inx: usize,
    pub stats: Option<T>,
}

impl<T: fmt::Debug> fmt::Display for Meta<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{self:#?}"))
    }
}

impl<T: fmt::Debug> Error for Meta<T> {}

impl<T: fmt::Debug> Meta<T> {
    pub fn new(seed: u64) -> Self {
        Self {
            rng: StarRng::new(seed),
            i: usize::MAX,
            op_inx: usize::MAX,
            stats: None,
        }
    }

    pub fn reset<O, F: FnOnce(&mut Meta<T>) -> O>(&mut self, stats: T, f: F) -> O {
        self.i = usize::MAX;
        self.op_inx = usize::MAX;
        self.stats = Some(stats);
        f(self)
    }
}

/// For second domains
#[derive(Clone, Copy, Default)]
pub struct D1;
