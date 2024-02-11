#![cfg(feature = "serde_support")]

use serde::{de::DeserializeOwned, Serialize};
use testcrate::{std_arena, std_chain, std_chain_no_gen, std_ord, std_surject};
use triple_arena::{
    utils::{ChainNoGenArena, PtrGen},
    Arena, ChainArena, OrdArena, Ptr, SurjectArena,
};

// RON version for debug
/*
fn round_trip<T: Serialize + DeserializeOwned>(t: &T) -> T {
    let s = ron::to_string(t).unwrap();
    let res: T = ron::from_str(&s).unwrap();
    res
}
*/

fn round_trip<T: Serialize + DeserializeOwned>(t: &T) -> T {
    let v = postcard::to_allocvec(t).unwrap();
    let res: T = postcard::from_bytes(&v).unwrap();
    res
}

#[test]
fn serde() {
    let a = std_arena();
    let b = round_trip(&a);
    Arena::_check_invariants(&b).unwrap();
    for (p, t) in &a {
        let q = Ptr::_from_raw(p.inx(), PtrGen::two());
        assert_eq!(b.get(q).unwrap(), t);
    }

    let a = std_chain();
    let b = round_trip(&a);
    ChainArena::_check_invariants(&b).unwrap();
    for (p, t) in &a {
        let q = Ptr::_from_raw(p.inx(), PtrGen::two());
        let link = b.get_link(q).unwrap();
        assert_eq!(link.prev().map(|p| p.inx()), t.prev().map(|p| p.inx()));
        assert_eq!(link.next().map(|p| p.inx()), t.next().map(|p| p.inx()));
        assert_eq!(link.t, t.t);
    }

    let a = std_chain_no_gen();
    let b = round_trip(&a);
    ChainNoGenArena::_check_invariants(&b).unwrap();
    for (p, t) in &a {
        let q = Ptr::_from_raw(p.inx(), PtrGen::two());
        assert_eq!(b.get_link(q).unwrap(), t);
    }

    let a = std_surject();
    let b = round_trip(&a);
    SurjectArena::_check_invariants(&b).unwrap();
    for (p, k, v) in &a {
        let q = Ptr::_from_raw(p.inx(), PtrGen::two());
        assert_eq!(b.get_key(q).unwrap(), k);
        assert_eq!(b.get_val(q).unwrap(), v);
    }

    let mut a = std_ord();
    a.compress_and_shrink();
    let b = round_trip(&a);
    OrdArena::_check_invariants(&b).unwrap();
    for (p, k, v) in &a {
        let q = Ptr::_from_raw(p.inx(), PtrGen::two());
        assert_eq!(b.get_key(q).unwrap(), k);
        assert_eq!(b.get_val(q).unwrap(), v);
    }
}
