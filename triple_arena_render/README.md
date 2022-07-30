# Triple Arena Rendering

A crate enabling trait-based visualization of graphs in `triple_arena::Arena<P, T>`s.

There is still work to do with better compactness of large graphs, but the SVG rendering is mostly
complete.

In the future, we could have more rendering styles and backends.

```rust
use triple_arena::prelude::*;
use triple_arena_render::{render_to_svg_file, DebugNode, DebugNodeTrait};

// Suppose we are storing an equation evaluation tree in an arena
// with this type of node
enum MyNode<P: Ptr> {
    /// A literal value in the equation
    Literal(i64),
    /// Negation of the node this `Ptr` is pointing to
    Negation(P),
    /// Summation of all the nodes pointed to
    Summation(Vec<P>),
}

use MyNode::*;

impl<P: Ptr> DebugNodeTrait<P> for MyNode<P> {
    fn debug_node(this: &Self) -> DebugNode<P> {
        // Here we manually write out the fields of the `DebugNode`,
        // but you can also use its `Default` implementation or
        // new` constructor
        match this {
            Literal(x) => DebugNode {
                sources: vec![],
                // We choose in this example to display the
                // literal value by itself
                center: vec![format!("{}", x)],
                // We choose source-to-sink convention for our
                // tree, so `sink` will always be empty
                sinks: vec![],
            },
            Negation(p) => DebugNode {
                // Have a debug edge corresponding to the real
                // edge, but leave the source description empty
                sources: vec![(*p, String::new())],
                // Display a negative sign
                center: vec!["-".to_owned()],
                sinks: vec![],
            },
            Summation(v) => DebugNode {
                // List all the inputs and number them
                sources: v
                    .iter()
                    .enumerate()
                    .map(|(i, p)| (*p, format!("in{}", i)))
                    .collect(),
                center: vec!["+".to_owned()],
                sinks: vec![],
            },
        }
    }
}

ptr_trait_struct!(P0);

fn main() {
    let mut a: Arena<P0, MyNode<P0>> = Arena::new();

    // construct a graph representing `((-(42)) + (256 + 7) + (...))`

    let lit42 = a.insert(Literal(42));
    let neg_lit42 = a.insert(Negation(lit42));

    let lit256 = a.insert(Literal(256));
    let lit7 = a.insert(Literal(7));
    let inner_sum = a.insert(Summation(vec![lit256, lit7]));

    let will_be_removed = a.insert(Literal(10));

    let _sum = a.insert(
        Summation(vec![neg_lit42, inner_sum, will_be_removed])
    );

    // example of an invalid `Ptr` in a graph
    a.remove(will_be_removed).unwrap();

    render_to_svg_file(
        &a,
        false,
        std::path::PathBuf::from("./example.svg".to_owned()),
    )
    .unwrap();
}
```

![Example SVG](https://raw.githubusercontent.com/AaronKutch/triple_arena/main/triple_arena_render/example.svg)
