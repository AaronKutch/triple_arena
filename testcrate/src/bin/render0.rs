//! For manual inspection of SVG output

use testcrate::*;
use triple_arena::prelude::*;
use triple_arena_render::*;

fn main() {
    let mut a: Arena<P0, MyNode<P0>> = Arena::new();

    // large node with only center text
    let _n_null = a.insert(MyNode::new(
        vec![],
        vec![
            "node_null___|_____W".to_string(),
            "_|".to_string(),
            "_|".to_string(),
            "_|".to_string(),
            "_|".to_string(),
            "_|".to_string(),
            "_|WXWXWXWXWXWXWXWX_".to_string(),
        ],
        vec![],
    ));
    let n0 = a.insert(MyNode::new(vec![], vec!["node0".to_string()], vec![]));
    // using odd repeats of "|" to make sure beziers are centered
    let n1 = a.insert(MyNode::new(
        vec![(n0, "|||||".to_string())],
        vec!["node1".to_string()],
        vec![],
    ));
    let n3 = a.insert(MyNode::new(vec![], vec!["node3".to_string()], vec![]));
    // multigraph
    let n2 = a.insert(MyNode::new(
        vec![(Ptr::invalid(), "lhs".to_string()), (n1, "rhs".to_string())],
        vec!["n2".to_string()],
        vec![(n3, "|||".to_string()), (n3, "|".to_string())],
    ));
    // with only input
    let _n4 = a.insert(MyNode::new(vec![(n2, "n4_in".to_string())], vec![], vec![]));
    let _n5 = a.insert(MyNode::new(vec![], vec!["n5".to_string()], vec![(
        n2,
        "|".to_string(),
    )]));
    // empty node
    let n6 = a.insert(MyNode::new(vec![], vec![], vec![]));
    a[n2].sources[0].0 = n6;
    // node with only output
    let _n7 = a.insert(MyNode::new(vec![], vec![], vec![(
        n6,
        "n7_out".to_string(),
    )]));

    // self cycle
    let n8 = a.insert(MyNode::new(vec![], vec!["n8".to_string()], vec![]));
    a[n8].sources.push((n8, "i".to_string()));
    a[n8].sinks.push((n8, "o".to_string()));

    // many sources and sinks

    let sources: Vec<(P0, String)> = (0..1)
        .map(|i| {
            (
                a.insert(MyNode::new(vec![], vec![], vec![])),
                format!("i{}", i),
            )
        })
        .collect();
    let sinks: Vec<(P0, String)> = (0..9)
        .map(|i| {
            (
                a.insert(MyNode::new(vec![], vec![format!("o{}", i)], vec![])),
                String::new(),
            )
        })
        .collect();
    a.insert(MyNode {
        sources,
        center: vec![],
        sinks,
    });

    let sources: Vec<(P0, String)> = (0..9)
        .map(|i| {
            (
                a.insert(MyNode::new(vec![], vec![], vec![])),
                format!("i{}", i),
            )
        })
        .collect();
    let sinks: Vec<(P0, String)> = (0..1)
        .map(|i| {
            (
                a.insert(MyNode::new(vec![], vec![format!("o{}", i)], vec![])),
                String::new(),
            )
        })
        .collect();
    a.insert(MyNode {
        sources,
        center: vec![],
        sinks,
    });

    render_to_svg_file(
        &a,
        false,
        std::path::PathBuf::from("./rendered.svg".to_owned()),
    )
    .unwrap();
}
