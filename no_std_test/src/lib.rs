//! insures that the crate is `no_std` and also has some `cargo-show-asm`
//! targets to check
//!
//! `cargo asm --target=riscv32i-unknown-none-elf -p no_std_test`

#![no_std]
#![allow(clippy::all)]

use core::num::NonZeroUsize;

extern crate alloc;
use alloc::vec::Vec;

use triple_arena::{ptr_struct, utils::NonZeroInxVec, Arena};

ptr_struct!(P0());
ptr_struct!(P1);

pub fn asm_vec(v: &Vec<u64>, inx: usize) -> u64 {
    *v.get(inx).unwrap()
}

pub fn asm_nzvec(v: &NonZeroInxVec<u64>, inx: NonZeroUsize) -> u64 {
    *v.get(inx).unwrap()
}

pub fn asm_arena_get(a: &Arena<P0, u64>, inx: P0) -> u64 {
    *a.get(inx).unwrap()
}

pub fn asm_arena_get_gen(a: &Arena<P1, u64>, inx: P1) -> u64 {
    *a.get(inx).unwrap()
}

// make sure this especially is minimal
pub fn asm_arena_get_nogen(a: &Arena<P1, u64>, inx: NonZeroUsize) -> u64 {
    *a.get_inx_unwrap(inx)
}
