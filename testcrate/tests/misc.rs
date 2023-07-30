use testcrate::P0;
use triple_arena::{Advancer, Arena};

// this is a hard coded test, there is a section in the fuzz test and in the
// overflow tests
#[test]
fn advancer() {
    let mut a = Arena::<P0, u8>::new();

    let mut adv = a.advancer();
    assert!(adv.advance(&a).is_none());

    let p0 = a.insert(0);
    let p1 = a.insert(1);
    let p2 = a.insert(2);
    let p3 = a.insert(3);
    let p4 = a.insert(4);
    a.remove(p1).unwrap();
    let p5 = a.insert(5);
    a.remove(p3).unwrap();
    a.remove(p0).unwrap();

    let mut v = vec![];
    let mut adv = a.advancer();
    while let Some(p) = adv.advance(&a) {
        v.push(p);
    }
    assert_ne!(v, vec![p1, p2, p4]);
    assert_eq!(v, vec![p5, p2, p4]);
}
