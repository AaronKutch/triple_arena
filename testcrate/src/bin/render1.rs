//! basic fuzzing

use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use testcrate::*;
use triple_arena::{Arena, Ptr};
use triple_arena_render::*;

fn main() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(1);
    let mut a: Arena<P0, MyNode<P0>> = Arena::new();
    let mut ptrs = vec![];
    for _ in 0..100 {
        a.insert_with(|p| {
            let mut node = MyNode::new(vec![], vec![], vec![]);
            if (rng.next_u32() % 8) != 0 {
                node.center.push(format!("{}", p))
            }
            loop {
                if (rng.next_u32() % 8) == 0 {
                    node.center.push("center".to_string());
                } else {
                    break
                }
            }
            loop {
                if (rng.next_u32() % 4) == 0 {
                    if !ptrs.is_empty() {
                        let inx = (rng.next_u32() as usize) % ptrs.len();
                        node.sources.push((ptrs[inx], format!("p{}", inx)));
                    }
                } else {
                    break
                }
            }
            loop {
                if (rng.next_u32() % 4) == 0 {
                    if !ptrs.is_empty() {
                        let inx = (rng.next_u32() as usize) % ptrs.len();
                        node.sinks.push((ptrs[inx], format!("p{}", inx)));
                    }
                } else {
                    break
                }
            }
            ptrs.push(p);
            node
        });
    }

    render_to_svg_file(
        &a,
        false,
        std::path::PathBuf::from("./rendered.svg".to_owned()),
    )
    .unwrap();
}
