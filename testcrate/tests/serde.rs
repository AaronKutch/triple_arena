use serde::{de::DeserializeOwned, Serialize};
use testcrate::{std_arena, std_chain, std_chain_no_gen};
use triple_arena::{
    utils::{ChainNoGenArena, PtrGen},
    Arena, ChainArena, Ptr,
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
}
