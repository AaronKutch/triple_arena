use rand_xoshiro::{rand_core::SeedableRng, Xoshiro128StarStar};
use testcrate::{fuzz_fill_inst, CKey, CVal, P1};
use triple_arena::Arena;

#[test]
fn clone_from_to() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);

    let mut a = Arena::<P1, (CKey, CVal)>::new();
    let mut repr = vec![];
    let mut repr_inxs = vec![];
    let (insts, expected) = fuzz_fill_inst(&mut rng, &repr, u64::MAX, 1 << 17, 1 << 16);
    for inst in insts {
        match inst {
            Ok(pair) => {
                repr.push((pair.0.clone_uncounting(), pair.1.clone_uncounting()));
                repr_inxs.push(a.insert(pair));
            }
            Err(inx) => {
                a.remove(repr_inxs.swap_remove(inx)).unwrap();
                repr.swap_remove(inx);
            }
        }
    }
    assert_eq!(repr, expected);
    // TODO test all `clone_from` and `clone_to` functions
}
