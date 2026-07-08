use std::num::NonZeroUsize;

use triple_arena::utils::{NonZeroInxGenericStack, NonZeroInxVec};

fn nz(x: usize) -> NonZeroUsize {
    NonZeroUsize::new(x).unwrap()
}

#[test]
fn nonzero_inx_vec() {
    let mut v = NonZeroInxVec::new();
    assert!(v.is_empty());
    assert_eq!(v.capacity(), 0);
    assert!(v.get(nz(1)).is_none());
    assert!(v.get_mut(nz(1)).is_none());
    assert!(v.pop().is_none());
    // use a `Box` to make sure drop glue works
    v.push(Box::new(7u8)).ok().unwrap();
    assert!(!v.is_empty());
    assert_eq!(v.get(nz(1)), Some(&Box::new(7)));
    assert_eq!(v.get_mut(nz(1)), Some(&mut Box::new(7)));
    assert!(v.get_disjoint_mut([nz(1), nz(1)]).is_err());
    // TODO
    //assert_eq!(unsafe { v.get_unchecked(nz(1)) }, &Box::new(7));
    //assert_eq!(unsafe { v.get_unchecked_mut(nz(1)) }, &mut Box::new(7));
    v.push(Box::new(3u8)).ok().unwrap();
    assert!(v.capacity() >= 2);
    v.ensure_capacity(34).unwrap();
    assert!(v.capacity() >= 34);
    v.ensure_capacity(0).unwrap();
    assert_eq!(v.len(), 2);
    v.ensure_capacity(34).unwrap();
    assert_eq!(
        v.get_disjoint_mut([nz(2), nz(1)]),
        Ok([&mut Box::new(3), &mut Box::new(7)])
    );
    assert_eq!(v.pop(), Some(Box::new(3)));
    assert!(!v.is_empty());
    assert!(v.get(nz(2)).is_none());
    assert!(v.get_mut(nz(2)).is_none());
    assert!(v.get_disjoint_mut([nz(1), nz(2)]).is_err());
    assert!(v.get_disjoint_mut([nz(2), nz(1)]).is_err());
    assert_eq!(v.pop(), Some(Box::new(7)));
    assert!(v.is_empty());
    assert!(v.get(nz(1)).is_none());
    assert!(v.get_mut(nz(1)).is_none());
    assert!(v.pop().is_none());
    assert_eq!(v.len(), 0);
    v.clear();
    v.clear();
    assert!(v.capacity() >= 34);
    v.clear_and_shrink();
    v.clear_and_shrink();
    assert_eq!(v.capacity(), 0);
    v.push(Box::new(1u8)).ok().unwrap();
    v.push(Box::new(2u8)).ok().unwrap();
    v.push(Box::new(4u8)).ok().unwrap();
    assert_eq!(v.get(nz(2)), Some(&Box::new(2)));
    v.clear_and_shrink();
    assert_eq!(v.capacity(), 0);
    assert!(v.is_empty());
    v.push(Box::new(1u8)).ok().unwrap();
    v.push(Box::new(2u8)).ok().unwrap();
    drop(v);
}
