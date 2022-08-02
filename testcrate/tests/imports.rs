//! makes sure all variations of the macro compile and do not require imports
//! other than the macro itself

use std::num::NonZeroU128;

use triple_arena::ptr_struct;

ptr_struct!(P0[u128](NonZeroU128));
ptr_struct!(P1[u128]());
ptr_struct!(P2[u128]);
ptr_struct!(P3(NonZeroU128));
ptr_struct!(P4());
ptr_struct!(P5);
ptr_struct!(P6; Q0; Q1);
ptr_struct!(R0[u8](NonZeroU128); R1[u8](NonZeroU128));
