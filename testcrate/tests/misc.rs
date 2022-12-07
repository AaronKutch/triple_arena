use testcrate::P0;
use triple_arena::Arena;

// this is a hard coded test, there is a section in the fuzz test and in the
// overflow tests
#[test]
fn next_ptr() {
    let mut a = Arena::<P0, u8>::new();

    let (_, b) = a.first_ptr();
    loop {
        if b {
            break
        }
        unreachable!()
    }

    let p0 = a.insert(0);
    let p1 = a.insert(1);
    let p2 = a.insert(2);
    let p3 = a.insert(3);
    let p4 = a.insert(4);
    a.remove(p1).unwrap();
    let p5 = a.insert(5);
    a.remove(p3).unwrap();
    a.remove(p0).unwrap();

    let (mut p, mut b) = a.first_ptr();
    let mut v = vec![];
    loop {
        if b {
            break
        }
        v.push(p);
        a.next_ptr(&mut p, &mut b);
    }
    assert_ne!(v, vec![p1, p2, p4]);
    assert_eq!(v, vec![p5, p2, p4]);
}
