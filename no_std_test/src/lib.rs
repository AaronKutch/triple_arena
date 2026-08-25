//! insures that the crate is `no_std` and also has some `cargo-show-asm`
//! targets to check
//!
//! `cargo asm --target=riscv32i-unknown-none-elf -p no_std_test`

#![no_std]
#![allow(clippy::all)]

use core::num::NonZeroUsize;

extern crate alloc;
use alloc::vec::Vec;

use triple_arena::{
    Arena, HeapBacking, ptr_struct,
    traits::*,
    utils::{NonZeroInxVec, traits::NonZeroInxGenericStack},
};

// Last inspected for 0.15.0: each of these compiles down to one bounds check
// against the stack length, one check of whether the slot is allocated (which
// for a generation counted `Ptr` is folded into comparing the generation), and
// then the loads of the entry itself. There is no redundant branching or
// double bounds checking.

ptr_struct!(P0());
ptr_struct!(P1);

pub fn asm_vec(v: &Vec<u64>, inx: usize) -> u64 {
    *v.get(inx).unwrap()
}

pub fn asm_nzvec(v: &NonZeroInxVec<u64>, inx: NonZeroUsize) -> u64 {
    *v.get(inx).unwrap()
}

pub fn asm_arena_get(a: &Arena<P0, u64, HeapBacking>, inx: P0) -> u64 {
    *a.get(inx).unwrap()
}

pub fn asm_arena_get_optional(a: &Arena<P0, u64, HeapBacking>, inx: P0) -> Option<u64> {
    a.get(inx).copied()
}

pub fn asm_arena_get_gen(a: &Arena<P1, u64, HeapBacking>, inx: P1) -> u64 {
    *a.get(inx).unwrap()
}

// make sure this especially is minimal
pub fn asm_arena_get_nogen(a: &Arena<P1, u64, HeapBacking>, inx: NonZeroUsize) -> u64 {
    *a.get_inx_unwrap(inx)
}
