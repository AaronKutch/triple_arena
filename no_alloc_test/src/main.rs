#![no_std]
#![no_main]

extern crate panic_halt;

use riscv_minimal_rt::entry;
use triple_arena::ptr_struct;

ptr_struct!(P0);
ptr_struct!(P1());

#[entry]
fn main() -> ! {
    panic!("main is not allowed to return")
}
