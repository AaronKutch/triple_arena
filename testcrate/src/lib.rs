#![allow(clippy::type_complexity)]

use std::{
    cell::RefCell,
    num::{NonZeroU128, NonZeroU32},
};

use rand_xoshiro::{rand_core::RngCore, Xoshiro128StarStar};
use triple_arena::{ptr_struct, Ptr};
use triple_arena_render::*;

#[cfg(miri)]
pub const A: u64 = B << 1;
#[cfg(miri)]
pub const B: u64 = 1 << 8;

#[cfg(not(miri))]
pub const A: u64 = B << 1;
#[cfg(not(miri))]
pub const B: u64 = 1 << 11;

pub struct MyNode<P: Ptr> {
    pub sources: Vec<(P, String)>,
    pub center: Vec<String>,
    pub sinks: Vec<(P, String)>,
}

impl<P: Ptr> MyNode<P> {
    pub fn new(sources: Vec<(P, String)>, center: Vec<String>, sinks: Vec<(P, String)>) -> Self {
        Self {
            sources,
            center,
            sinks,
        }
    }
}

impl<P: Ptr> DebugNodeTrait<P> for MyNode<P> {
    fn debug_node(_p_this: P, this: &Self) -> DebugNode<P> {
        DebugNode {
            sources: this.sources.clone(),
            center: this.center.clone(),
            sinks: this.sinks.clone(),
        }
    }
}

// This is constructed this way to guard against problems with stuff like
// `PtrNoGen`
ptr_struct!(P0[NonZeroU32](NonZeroU128));
ptr_struct!(P1);

thread_local! {
    pub static CLONE_COUNT: RefCell<u64> = RefCell::new(0);
    pub static CMP_COUNT: RefCell<u64> = RefCell::new(0);
    pub static VAL_NUM: RefCell<u64> = RefCell::new(0);
    //pub static KEY_VAL_RECORD: RefCell<Arena<P1, (CKey, CVal)>> = RefCell::new(Arena::new());
}

pub fn get_clone_count() -> u64 {
    CLONE_COUNT.with(|f| *f.borrow())
}

pub fn inc_clone_count() {
    CLONE_COUNT.with(|f| {
        let x = f.borrow().checked_add(1).unwrap();
        *f.borrow_mut() = x;
    })
}

pub fn get_cmp_count() -> u64 {
    CMP_COUNT.with(|f| *f.borrow())
}

pub fn inc_cmp_count() {
    CMP_COUNT.with(|f| {
        let x = f.borrow().checked_add(1).unwrap();
        *f.borrow_mut() = x;
    })
}

/// Counts `Clone`s and comparisons
#[derive(Debug, Eq)]
pub struct CKey {
    pub k: u64,
}

impl CKey {
    pub fn clone_uncounting(&self) -> Self {
        Self { k: self.k }
    }
}

impl Clone for CKey {
    fn clone(&self) -> Self {
        inc_clone_count();
        Self { k: self.k }
    }
}

impl PartialEq for CKey {
    fn eq(&self, other: &Self) -> bool {
        inc_cmp_count();
        self.k == other.k
    }
}

impl PartialOrd for CKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        inc_cmp_count();
        self.k.partial_cmp(&other.k)
    }
}

impl Ord for CKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        inc_cmp_count();
        self.k.cmp(&other.k)
    }
}

/// Counts `Clone`s
#[derive(Debug, PartialEq, Eq)]
pub struct CVal {
    pub v: u64,
}

impl CVal {
    pub fn clone_uncounting(&self) -> Self {
        Self { v: self.v }
    }
}

impl Clone for CVal {
    fn clone(&self) -> Self {
        inc_clone_count();
        Self { v: self.v }
    }
}

pub fn next_key_val_pair(rng: &mut Xoshiro128StarStar) -> (CKey, CVal) {
    let v = VAL_NUM.with(|f| {
        let x: u64 = *f.borrow();
        *f.borrow_mut() = x.checked_add(1).unwrap();
        x
    });
    let k = rng.next_u64();
    (CKey { k }, CVal { v })
}

/// Returns a random list of insert and remove instructions (random except that
/// it prevents more removals than insertions at any time point). Also returns
/// expected end state.
pub fn fuzz_fill_inst(
    rng: &mut Xoshiro128StarStar,
    // representation of the arena
    repr: &[(CKey, CVal)],
    insertions: u64,
    removals: u64,
) -> (Vec<Result<(CKey, CVal), usize>>, Vec<(CKey, CVal)>) {
    // first, schedule what instructions will be insertions and what will be
    // removals
    let mut blank_insts: Vec<bool> = vec![];
    for _ in 0..insertions {
        blank_insts.push(true)
    }
    for _ in 0..removals {
        blank_insts.push(false)
    }
    let len = blank_insts.len();
    for i in 0..len {
        // randomly sort
        blank_insts.swap(i, (rng.next_u64() as usize) % len);
    }
    // play the blank instructions to make sure we never try remove from an empty
    // arena
    let mut sim_len = repr.len();
    for i in 0..len {
        if blank_insts[i] {
            sim_len += 1;
        } else if sim_len == 0 {
            // need to bring forward an insertion to avoid removing or changing the sums
            let mut found = false;
            for j in i..len {
                if blank_insts[j] {
                    blank_insts.swap(i, j);
                    found = true;
                    break
                }
            }
            if !found {
                panic!("were there too many removals?");
            }
            sim_len += 1;
        } else {
            sim_len -= 1;
        }
    }
    assert_eq!(
        sim_len,
        repr.len() + (insertions as usize) - (removals as usize)
    );

    let mut insts = vec![];
    // now simulate so that we can remove from both old elements and newly inserted
    // elements without running into problems
    let mut repr_sim = repr.to_owned();
    for inst in blank_insts {
        if inst {
            let pair = next_key_val_pair(rng);
            repr_sim.push((pair.0.clone_uncounting(), pair.1.clone_uncounting()));
            insts.push(Ok(pair));
        } else {
            let inx = (rng.next_u64() as usize) % repr_sim.len();
            insts.push(Err(inx));
            repr_sim.swap_remove(inx);
        }
    }
    assert_eq!(insts.len(), (insertions + removals) as usize);
    (insts, repr_sim)
}

/// For benchmarks, `CKey` and `CVal` are meant for tallying comparisons and
/// clones
pub fn fuzz_fill_inst_bench(
    rng: &mut Xoshiro128StarStar,
    // representation of the arena
    repr: &[(u128, u128)],
    insertions: u64,
    removals: u64,
) -> (Vec<Result<(u128, u128), usize>>, Vec<(u128, u128)>) {
    // first, schedule what instructions will be insertions and what will be
    // removals
    let mut blank_insts: Vec<bool> = vec![];
    for _ in 0..insertions {
        blank_insts.push(true)
    }
    for _ in 0..removals {
        blank_insts.push(false)
    }
    let len = blank_insts.len();
    for i in 0..len {
        // randomly sort
        blank_insts.swap(i, (rng.next_u64() as usize) % len);
    }
    // play the blank instructions to make sure we never try remove from an empty
    // arena
    let mut sim_len = repr.len();
    for i in 0..len {
        if blank_insts[i] {
            sim_len += 1;
        } else if sim_len == 0 {
            // need to bring forward an insertion to avoid removing or changing the sums
            let mut found = false;
            for j in i..len {
                if blank_insts[j] {
                    blank_insts.swap(i, j);
                    found = true;
                    break
                }
            }
            if !found {
                panic!("were there too many removals?");
            }
            sim_len += 1;
        } else {
            sim_len -= 1;
        }
    }
    assert_eq!(
        sim_len,
        repr.len() + (insertions as usize) - (removals as usize)
    );

    let mut insts = vec![];
    // now simulate so that we can remove from both old elements and newly inserted
    // elements without running into problems
    let mut repr_sim = repr.to_owned();
    let mut key = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
    for inst in blank_insts {
        if inst {
            // split up the key by alternating bits to make sure the whole thing is being
            // compared against and branch prediction does not get lazy
            let val = (
                key,
                (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64()),
            );
            key = key.wrapping_add((1 << 120) + 7);
            repr_sim.push(val);
            insts.push(Ok(val));
        } else {
            let inx = (rng.next_u64() as usize) % repr_sim.len();
            insts.push(Err(inx));
            repr_sim.swap_remove(inx);
        }
    }
    assert_eq!(insts.len(), (insertions + removals) as usize);
    (insts, repr_sim)
}
