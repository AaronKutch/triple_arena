use std::num::NonZeroU128;

use triple_arena::ptr_struct;

// makes sure all variations of the macro do not require imports other than the
// macro itself
ptr_struct!(P0[u128](NonZeroU128));
ptr_struct!(P1[u128]());
ptr_struct!(P2[u128]);
ptr_struct!(P3(NonZeroU128));
ptr_struct!(P4());
ptr_struct!(P5);
