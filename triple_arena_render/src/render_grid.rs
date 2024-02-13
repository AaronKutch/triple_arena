use std::cmp::max;

use triple_arena::{Arena, Ptr};

use crate::{
    internal::{ANode, RenderNode},
    *,
};

/// Final grid of `RenderNodes`
#[derive(Debug)]
pub struct RenderGrid<P: Ptr> {
    pub dag: Arena<P, ANode<P>>,
    pub grid: Vec<Vec<Option<RenderNode<P>>>>,
    pub tot_wx: i32,
    pub tot_wy: i32,
}

impl<P: Ptr> RenderGrid<P> {
    /// Used by `grid_process`
    pub fn new(dag: Arena<P, ANode<P>>) -> Self {
        let mut rg = Self {
            dag,
            grid: vec![],
            tot_wx: 0,
            tot_wy: 0,
        };

        // overall max node dimensions
        let mut grid_max = (0, 0);

        for node in rg.dag.vals() {
            grid_max.0 = max(grid_max.0, node.grid_position.0);
            grid_max.1 = max(grid_max.1, node.grid_position.1);
        }
        grid_max.0 += 1;
        grid_max.1 += 1;
        for _ in 0..grid_max.0 {
            let mut column = vec![];
            for _ in 0..grid_max.1 {
                column.push(None);
            }
            rg.grid.push(column);
        }
        // max dimensions per column or row
        let mut grid_max_wx = vec![0; grid_max.0];
        let mut grid_max_wy = vec![0; grid_max.1];

        for (p, node) in &rg.dag {
            let render_node = RenderNode::new(&node.sources, &node.center, &node.sinks, p);
            grid_max_wx[node.grid_position.0] =
                max(grid_max_wx[node.grid_position.0], render_node.wx);
            grid_max_wy[node.grid_position.1] =
                max(grid_max_wy[node.grid_position.1], render_node.wy);
            let place = &mut rg.grid[node.grid_position.0][node.grid_position.1];
            assert!(place.is_none());
            *place = Some(render_node);
        }

        // `rg.grid` is now completely rectangular and the `_max_` values are
        // correct

        // create map for positions in grid
        for (i, vert) in rg.grid.iter().enumerate() {
            for (j, node) in vert.iter().enumerate() {
                // do not flatten, it messes up the indexing
                if let Some(node) = node {
                    rg.dag[node.ptr].grid_position = (i, j);
                }
            }
        }

        let mut cumulative_x = vec![];
        rg.tot_wx = PAD;
        for (i, wx) in grid_max_wx.iter().enumerate() {
            cumulative_x.push(rg.tot_wx);
            rg.tot_wx += wx;
            if i != (grid_max_wx.len() - 1) {
                rg.tot_wx += NODE_PAD;
            }
        }
        rg.tot_wx += PAD;
        let mut cumulative_y = vec![];
        rg.tot_wy = PAD;
        for (i, wy) in grid_max_wy.iter().enumerate() {
            cumulative_y.push(rg.tot_wy);
            rg.tot_wy += wy;
            if i != (grid_max_wy.len() - 1) {
                rg.tot_wy += NODE_PAD;
            }
        }
        rg.tot_wy += PAD;

        // translate to final places
        for (i, vert) in rg.grid.iter_mut().enumerate() {
            for (j, node) in vert.iter_mut().enumerate() {
                // do not flatten, it messes up the indexing
                if let Some(node) = node {
                    node.translate((cumulative_x[i], cumulative_y[j]));
                }
            }
        }

        rg
    }
}
