use std::cmp::max;

use crate::*;

#[derive(Debug)]
pub(crate) struct RenderGrid<P: PtrTrait> {
    pub dag: Arena<P, ANode<P>>,
    pub grid: Vec<Vec<Option<RenderNode<P>>>>,
    pub tot_wx: i32,
    pub tot_wy: i32,
}

impl<P: PtrTrait> RenderGrid<P> {
    pub fn new(dag: Arena<P, ANode<P>>, grid: Vec<Vec<(Ptr<P>, usize)>>) -> Self {
        let mut rg = Self {
            dag,
            grid: vec![],
            tot_wx: 0,
            tot_wy: 0,
        };

        // find maximum column and row widths, and cumulative positions
        let mut max_y_nodes = 0;
        for vert in &grid {
            for slot in &*vert {
                max_y_nodes = max(max_y_nodes, slot.1 + 1);
            }
        }
        let mut grid_max_wx = vec![0; grid.len()];
        let mut grid_max_wy = vec![0; max_y_nodes];
        for _ in 0..grid_max_wx.len() {
            let mut v = vec![];
            for _ in 0..grid_max_wy.len() {
                v.push(None);
            }
            rg.grid.push(v);
        }
        for (x_i, vertical) in grid.iter().enumerate() {
            for (ptr, pos) in &*vertical {
                let node = RenderNode::new(&rg.dag[ptr].debug_node, *ptr);
                let tmp = grid_max_wx[x_i];
                grid_max_wx[x_i] = max(tmp, node.wx);
                // y is reversed to make the data flow downwards graphically
                let tmp = grid_max_wy[max_y_nodes - 1 - *pos];
                grid_max_wy[max_y_nodes - 1 - *pos] = max(tmp, node.wy);
                rg.grid[x_i][max_y_nodes - 1 - *pos] = Some(node);
            }
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
