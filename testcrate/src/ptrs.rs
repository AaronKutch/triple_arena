use std::num::{NonZeroU32, NonZeroU128};

use triple_arena::ptr_struct;

// This is constructed this way to guard against problems with stuff like
// `PtrNoGen`
ptr_struct!(P0[NonZeroU32](NonZeroU128));
ptr_struct!(P1);
