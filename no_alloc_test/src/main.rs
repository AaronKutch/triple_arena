#![no_std]
#![no_main]

extern crate panic_halt;

use riscv_minimal_rt::entry;
use triple_arena::{ptr_struct, StackBacking, Arena, traits::*};

ptr_struct!(P0);
ptr_struct!(P1());

#[entry]
fn main() -> ! {
    let mut a = Arena::<P0, (), StackBacking<128>>::new();
    let _p0 = a.insert(());
    let mut b = a.clone();
    b.clone_from(&a);

    panic!("main is not allowed to return")
}
