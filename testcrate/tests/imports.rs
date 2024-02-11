//! makes sure all variations of the macro compile and do not require imports
//! other than the macro itself, and also that fully qualified names are being
//! used

#![allow(dead_code)]

use core::num::{NonZeroU128, NonZeroU8};

use triple_arena::ptr_struct;

mod std {}
mod alloc {}
struct Result {}
struct Option {}
trait Hash {}
trait Clone {}
trait Copy {}
trait PartialEq {}
trait Eq {}
trait PartialOrd {}
trait Ord {}
trait Ptr {}
trait PtrInx {}
trait PtrGen {}
trait Default {}
trait Debug {}
trait Display {}

trait Recast {}
trait Serialize {}
trait Deserialize {}

// so the default uses are correct
trait NonZeroUsize {}
trait NonZeroU64 {}

ptr_struct!(P0[NonZeroU128](NonZeroU128));
ptr_struct!(P1[NonZeroU128]());
ptr_struct!(P2[NonZeroU128]);
ptr_struct!(P3(NonZeroU128));
ptr_struct!(P4());
ptr_struct!(P5);
ptr_struct!(P6; Q0; Q1);
ptr_struct!(R0[NonZeroU8](NonZeroU128); R1[NonZeroU8](NonZeroU128));
