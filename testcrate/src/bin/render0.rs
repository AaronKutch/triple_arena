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
    let _n4 = a.insert(MyNode::new(
        vec![(n2, "|".to_string())],
        vec!["n4".to_string()],
        vec![],
    ));
    let _n5 = a.insert(MyNode::new(vec![], vec!["n5".to_string()], vec![(
        n2,
        "|".to_string(),
    )]));
    let n6 = a.insert(MyNode::new(vec![], vec![], vec![]));
    a[n2].sources[0].0 = n6;

    render_to_svg_file(
        &a,
        true,
        std::path::PathBuf::from("./rendered.svg".to_owned()),
    )
    .unwrap();
}
