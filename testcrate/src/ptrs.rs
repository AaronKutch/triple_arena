use std::num::{NonZeroU8, NonZeroU32, NonZeroU128};

use triple_arena::{ptr_struct, traits::Ptr, utils::PtrGen};

// This is constructed this way to guard against problems with stuff like
// `PtrNoGen` and bad casts
ptr_struct!(P0[NonZeroU32](NonZeroU128));
ptr_struct!(P1);
// for testing generation overflow
ptr_struct!(P2[NonZeroU32](NonZeroU8));

/// helper for testing with arena generations
#[derive(Debug)]
pub struct TestGen<P: Ptr>(pub P::Gen);

impl<P: Ptr> TestGen<P> {
    /// `generational_inc`s the reference generation once and returns if
    /// overflow occured
    pub fn invalidate(&mut self) -> bool {
        let tmp = PtrGen::generational_inc(self.0);
        self.0 = tmp.0;
        tmp.1
    }
}
