use triple_arena::prelude::*;
mod grid_process;
mod render_grid;
mod render_node;
mod svg;
pub(crate) use grid_process::{grid_process, ANode};
pub(crate) use render_grid::RenderGrid;
pub(crate) use render_node::RenderNode;
pub use svg::{render_to_svg, render_to_svg_file};

// in the future, we could make these default parameters in some struct

pub(crate) const PAD: i32 = 128;
pub(crate) const FONT_WX: i32 = 256;
pub(crate) const FONT_WY: i32 = 512;
// NOTE: do not change without checking that `|` and `_` fit perfectly
pub(crate) const FONT_FAMILY: &str = "monospace";
pub(crate) const FONT_SIZE: i32 = 512 - 48;
// the lowest hanging parts of characters should be above text starting point
pub(crate) const FONT_ADJUST_Y: i32 = -192;
pub(crate) const INPUT_PAD: i32 = 0;
pub(crate) const INPUT_FONT_WX: i32 = 128;
pub(crate) const INPUT_FONT_WY: i32 = 256;
pub(crate) const INPUT_FONT_SIZE: i32 = 256 - 24;
pub(crate) const INPUT_FONT_ADJUST_Y: i32 = -48;
pub(crate) const RELATION_WIDTH: i32 = 48;
pub(crate) const NODE_PAD: i32 = 1024;
// Quaternion VScode color theme
pub(crate) const COLORS: [&str; 7] = [
    // the green-yellow clash is problematic, so remove green
    "a0a0a0", "00b2ff", "00cb9d", /* "2ab90f", */ "c49d00", "ff8080", "ff2adc", "a35bff",
];
pub(crate) const NODE_FILL: &str = "171717";
pub(crate) const TEXT_COLOR: &str = "a0a0a0";
//pub(crate) const DEBUG_WIDTH: i32 = 48;

/// Most kinds of graph representations have some notion of directionality,
/// which we term "source-to-sink" or "sink-to-source" edges. By convention,
/// renderers render in order from sources to sinks (and apply some kind of bias
/// or referential transform if there are cycles with no topological ordering).
/// For nodes that store "sink-to-source" edge pointers to other nodes,
/// `sources` should be filled out and `sinks` left empty, and vice-versa for
/// "source-to-sink" edges. Arbitrary combinations can also be chosen depending
/// on what ordering is preferred.
#[derive(Debug)]
pub struct DebugNode<P: PtrTrait> {
    /// Sources should be a tuple of `Ptr`s to source nodes in the graph and
    /// short one line strings that will be used for input annotations (or empty
    /// strings if no annotations are wanted).
    pub sources: Vec<(Ptr<P>, String)>,
    /// The center text can have multiple lines or be empty
    pub center: Vec<String>,
    /// Sinks should follow what sources do, except with `Ptr`s to sink nodes in
    /// the graph.
    pub sinks: Vec<(Ptr<P>, String)>,
}

impl<P: PtrTrait> Default for DebugNode<P> {
    /// Start with all parts empty
    fn default() -> Self {
        Self {
            sources: vec![],
            center: vec![],
            sinks: vec![],
        }
    }
}

/// A trait implemented for the `T` in `triple_arena::Arena<P, T>`, intended
/// where `T` is some kind of graph node element. `P` corresponds to the
/// `Ptr<P>` being used for the arena, and allows renderers to automatically
/// traverse the graph in the arena.
pub trait DebugNodeTrait<P: PtrTrait> {
    fn debug_node(this: &Self) -> DebugNode<P>;
}

#[derive(Debug)]
#[non_exhaustive]
pub enum RenderError<P: PtrTrait> {
    /// A pointer in one of the edges was invalid
    InvalidPtr(Ptr<P>),
    /// A `std::io` error
    IoError(std::io::Error),
}
