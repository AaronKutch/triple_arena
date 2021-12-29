#![allow(clippy::needless_range_loop)]

// TODO remove dependency
use std::collections::{hash_map::Entry::*, HashMap};

use triple_arena::prelude::*;

use crate::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum VisitState {
    Initial,
    Unelided,
    RootReachable,
    Prepared,
    OnStack0,
    DFSExplored0,
    OnStack1,
    DFSExplored1,
}

use VisitState::*;

impl Default for VisitState {
    fn default() -> Self {
        Initial
    }
}

/// Algorithmic node. Contains some additional information alongside the
/// `DebugNode` needed for fast processing
#[derive(Debug)]
pub(crate) struct ANode<P: PtrTrait> {
    pub debug_node: DebugNode<P>,
    pub state: VisitState,
    /// Used in initial topological sorting
    pub sort_position: usize,
    /// Used for grid positioning
    pub grid_position: (usize, usize),
}

impl<P: PtrTrait> Default for ANode<P> {
    fn default() -> Self {
        Self {
            debug_node: DebugNode::default(),
            state: VisitState::default(),
            sort_position: 0,
            grid_position: (0, 0),
        }
    }
}

pub(crate) fn grid_process<P: PtrTrait, T: DebugNodeTrait<P>>(
    arena: &Arena<P, T>,
    error_on_invalid_ptr: bool,
) -> Result<RenderGrid<P>, RenderError<P>> {
    // this is not guaranteed to be a DAG yet but will become one
    let mut dag: Arena<P, ANode<P>> = Arena::new();
    dag.clone_from_with(arena, |_, t| ANode {
        debug_node: DebugNodeTrait::debug_node(t),
        ..Default::default()
    });

    let mut ptrs = vec![];
    for (p, _) in &dag {
        ptrs.push(p);
    }

    // We need to unelide nonexistant sinks that have a corresponding source, and
    // vice versa. This also checks for invalid pointers.
    for p0 in &ptrs {
        if dag[p0].state == Initial {
            // check all sinks
            for i0 in 0..dag[p0].debug_node.sinks.len() {
                let p1 = dag[p0].debug_node.sinks[i0].0;
                // check for invalid pointers and if a source is elided
                if let Some(node) = dag.get(p1) {
                    if !node.debug_node.sources.iter().any(|(o, _)| *o == *p0) {
                        // unelide
                        dag[p1].debug_node.sources.push((*p0, String::new()));
                    }
                } else if error_on_invalid_ptr {
                    return Err(RenderError::InvalidPtr(p1))
                }
            }
            // check all sources
            for i0 in 0..dag[p0].debug_node.sources.len() {
                let p1 = dag[p0].debug_node.sources[i0].0;
                // check for invalid pointers and if a sink is elided
                if let Some(node) = dag.get(p1) {
                    if !node.debug_node.sinks.iter().any(|(o, _)| *o == *p0) {
                        // unelide
                        dag[p1].debug_node.sinks.push((*p0, String::new()));
                    }
                } else if error_on_invalid_ptr {
                    return Err(RenderError::InvalidPtr(p1))
                }
            }
            dag[p0].state = Unelided;
        } else {
            assert_eq!(dag[p0].state, Unelided);
        }
    }

    // fix invalid pointers
    if !error_on_invalid_ptr {
        let original_len = ptrs.len();
        for ptr_i in 0..original_len {
            let p0 = ptrs[ptr_i];
            for i0 in 0..dag[p0].debug_node.sinks.len() {
                let p1 = dag[p0].debug_node.sinks[i0].0;
                if !dag.contains(p1) {
                    let p1_prime = dag.insert(ANode {
                        debug_node: DebugNode {
                            sources: vec![(p0, String::new())],
                            center: vec![format!("{:?}(invalid)", p1)],
                            sinks: vec![],
                        },
                        state: Unelided,
                        ..Default::default()
                    });
                    dag[p0].debug_node.sinks[i0].0 = p1_prime;
                    ptrs.push(p1_prime);
                }
            }
            for i0 in 0..dag[p0].debug_node.sources.len() {
                let p1 = dag[p0].debug_node.sources[i0].0;
                if !dag.contains(p1) {
                    let p1_prime = dag.insert(ANode {
                        debug_node: DebugNode {
                            sources: vec![],
                            center: vec![format!("{:?}(invalid)", p1)],
                            sinks: vec![(p0, String::new())],
                        },
                        state: Unelided,
                        ..Default::default()
                    });
                    dag[p0].debug_node.sources[i0].0 = p1_prime;
                    ptrs.push(p1_prime);
                }
            }
        }
    }

    // nodes with no sources
    let mut roots = vec![];
    for p0 in &ptrs {
        if dag[p0].debug_node.sources.is_empty() {
            roots.push(*p0);
        }
    }

    // Some kinds of cycles will have no roots leading to them. Here, we find nodes
    // reachable from a root. DFS
    let mut path: Vec<(usize, Ptr<P>)> = vec![];
    for root in &roots {
        let root = *root;
        if dag[root].state == Unelided {
            path.push((0, root));
            loop {
                let current = path[path.len() - 1].1;
                dag[current].state = RootReachable;
                match dag[current].debug_node.sinks.get(path[path.len() - 1].0) {
                    Some((p0, _)) => {
                        let p0 = *p0;
                        match dag[p0].state {
                            Unelided => {
                                // explore further
                                path.push((0, p0));
                            }
                            RootReachable => {
                                // cross edge, check next
                                let len = path.len();
                                path[len - 1].0 += 1;
                            }
                            _ => unreachable!(),
                        }
                    }
                    None => {
                        // no more sinks, backtrack
                        path.pop().unwrap();
                        if path.is_empty() {
                            break
                        }
                        // check next dependency
                        let len = path.len();
                        path[len - 1].0 += 1;
                    }
                }
            }
        } else {
            unreachable!()
        }
    }

    // we could just loop over every pointer and all cycles would be broken with the
    // cycle breaking DFS, but we want to bias towards preexisting roots and then
    // check unreachable nodes
    let mut starts = roots.clone();
    for p in &ptrs {
        if dag[p].state == Unelided {
            starts.push(*p);
        } else {
            assert_eq!(dag[p].state, RootReachable);
        }
        dag[p].state = Prepared;
    }

    // DFS for conversion to DAG
    // path from root, with the `usize` indicating which sink was followed
    let mut path: Vec<(usize, Ptr<P>)> = vec![];
    for start in &starts {
        let start = *start;
        if dag[start].state == Prepared {
            path.push((0, start));
            loop {
                let current = path[path.len() - 1].1;
                // self-cycles are handled also if this is done first
                dag[current].state = OnStack0;
                match dag[current].debug_node.sinks.get(path[path.len() - 1].0) {
                    Some((p0, _)) => {
                        let p0 = *p0;
                        match dag[p0].state {
                            Prepared => {
                                // explore further
                                path.push((0, p0));
                            }
                            OnStack0 => {
                                // cycle found, break cycle by repointing `current`'s sink
                                // pointer to `p0_prime0` and repointing the corresponding
                                // source of `p0` to `p0_prime1`
                                let p0_prime0 = dag.insert(ANode {
                                    debug_node: DebugNode {
                                        sources: vec![(current, String::new())],
                                        center: vec![format!("{:?}", p0)],
                                        sinks: vec![],
                                    },
                                    state: DFSExplored0,
                                    ..Default::default()
                                });
                                dag[current].debug_node.sinks[path[path.len() - 1].0].0 = p0_prime0;
                                // special case explore
                                ptrs.push(p0_prime0);

                                let p0_prime1 = dag.insert(ANode {
                                    debug_node: DebugNode {
                                        sources: vec![],
                                        center: vec![format!("{:?}", p0)],
                                        sinks: vec![(p0, String::new())],
                                    },
                                    state: DFSExplored0,
                                    ..Default::default()
                                });
                                // find the corresponding source
                                for i1 in 0..dag[p0].debug_node.sources.len() {
                                    if dag[p0].debug_node.sources[i1].0 == current {
                                        dag[p0].debug_node.sources[i1].0 = p0_prime1;
                                    }
                                }
                                ptrs.push(p0_prime1);
                                // new root
                                roots.push(p0_prime1);

                                // do nothing so this node is restarted in case
                                // of more cycles in the same node
                            }
                            DFSExplored0 => {
                                // cross edge, check next
                                let len = path.len();
                                path[len - 1].0 += 1;
                            }
                            _ => unreachable!(),
                        }
                    }
                    None => {
                        // no more sinks, backtrack
                        dag[current].state = DFSExplored0;
                        path.pop().unwrap();
                        if path.is_empty() {
                            break
                        }
                        // check next dependency
                        let len = path.len();
                        path[len - 1].0 += 1;
                    }
                }
            }
        } else {
            assert_eq!(dag[start].state, DFSExplored0);
        }
    }

    // `dag` is now actually a DAG

    // topological sorting
    let mut sort_num = 0usize;
    // path from root, with the `usize` indicating which sink was followed
    let mut path: Vec<(usize, Ptr<P>)> = vec![];
    // we will be adding in more root nodes
    let original_root_len = roots.len();
    for root_i in 0..original_root_len {
        let root = roots[root_i];
        if dag[root].state == DFSExplored0 {
            path.push((0, root));
            loop {
                let current = path[path.len() - 1].1;
                dag[current].state = OnStack1;
                let tmp = if let Some((tmp, _)) =
                    dag[current].debug_node.sinks.get(path[path.len() - 1].0)
                {
                    Some(*tmp)
                } else {
                    None
                };
                match tmp {
                    Some(p0) => {
                        match dag[p0].state {
                            DFSExplored0 => {
                                // explore further
                                path.push((0, p0));
                            }
                            DFSExplored1 => {
                                // cross edge, check next
                                let len = path.len();
                                path[len - 1].0 += 1;
                            }
                            _ => unreachable!(),
                        }
                    }
                    None => {
                        // no more sinks, backtrack
                        dag[current].state = DFSExplored1;
                        dag[current].sort_position = sort_num;
                        sort_num += 1;
                        path.pop().unwrap();
                        if path.is_empty() {
                            break
                        }
                        // check next dependency
                        let len = path.len();
                        path[len - 1].0 += 1;
                    }
                }
            }
        } else {
            assert!(dag[root].state == DFSExplored1);
        }
    }

    // we structure the DAG by looking at the first operand of an operation and
    // constructing a "lineage" aligned with the first operand. We use a special
    // "lineage search" that constructs a vector of lineages. It works by
    // selecting any unexplored node, then adding on to the lineage all the way
    // until a root is reached. If the leafward parts of the lineage are not
    // touched on the first exploration, later explorations through
    // the same lineage will overwrite the lineage number.
    let mut n = 0;
    let mut lineage_map: HashMap<Ptr<P>, usize> = HashMap::new();
    let mut lineage_leaves: HashMap<usize, Ptr<P>> = HashMap::new();
    for p0 in &ptrs {
        if !lineage_map.contains_key(p0) {
            let mut next = *p0;
            lineage_map.insert(next, n);
            lineage_leaves.insert(n, next);
            while let Some((next_zeroeth, _)) = dag[next].debug_node.sources.get(0) {
                next = *next_zeroeth;
                match lineage_map.entry(next) {
                    Occupied(mut o) => {
                        // remove prior firsts
                        let _ = lineage_leaves.remove(o.get());
                        o.insert(n);
                    }
                    Vacant(v) => {
                        v.insert(n);
                    }
                }
            }
            n += 1;
        }
    }

    // get ordered lineages
    let mut lineages: Vec<Vec<Ptr<P>>> = vec![];
    for leaf in lineage_leaves {
        let mut next = leaf.1;
        let mut lineage = vec![next];
        while let Some((next_zeroeth, _)) = dag[next].debug_node.sources.get(0) {
            next = *next_zeroeth;
            lineage.push(next);
        }
        lineages.push(lineage);
    }

    // Finally, make a grid such that any dependency must flow one way. The second
    // element in the tuple says how far back from the leaf line the node should be
    // placed.
    let mut grid: Vec<Vec<(Ptr<P>, usize)>> = vec![];
    for lineage in &lineages {
        let mut vertical = vec![];
        for ptr in lineage {
            vertical.push((*ptr, dag[ptr].sort_position));
        }
        grid.push(vertical);
    }
    // compress vertically as much as possible
    let mut changed;
    loop {
        changed = false;
        for vertical in &mut grid {
            for slot in &mut *vertical {
                let mut pos = 0;
                for (sink, _) in &dag[slot.0].debug_node.sinks {
                    pos = std::cmp::max(pos, dag[sink].sort_position + 1);
                }
                if pos < slot.1 {
                    // There is room to slide down
                    (*slot).1 = pos;
                    dag[slot.0].sort_position = pos;
                    changed = true;
                }
            }
        }
        if !changed {
            break
        }
    }

    /*let mut leaves = vec![];
    for p0 in &ptrs {
        if dag[p0].debug_node.sinks.is_empty() {
            leaves.push(*p0);
        }
    }

    // Reordering columns to try and minimize dependency line crossings.
    // create some maps first.
    let mut ptr_to_x_i: HashMap<Ptr<P>, usize> = HashMap::new();
    let mut x_i_to_ptr: HashMap<usize, Ptr<P>> = HashMap::new();
    for (x_i, vertical) in grid.iter().enumerate() {
        for slot in vertical {
            ptr_to_x_i.insert(slot.0, x_i);
            x_i_to_ptr.insert(x_i, slot.0);
        }
    }
    let mut done_lineages: HashSet<usize> = HashSet::new();
    let mut sorted_lineages: Vec<usize> = vec![];
    // path from leaf, with the `usize` indicating which sink was followed
    let mut path: Vec<(usize, Ptr<P>)> = vec![];
    for leaf in &leaves {
        if dag[leaf].state == ElisionExplored {
            path.push((0, *leaf));
            loop {
                let current = path[path.len() - 1].1;
                dag[current].state = OnDFSStack;
                let tmp = if let Some((tmp, _)) =
                    dag[current].debug_node.sources.get(path[path.len() - 1].0)
                {
                    Some(*tmp)
                } else {
                    None
                };
                match tmp {
                    Some(p0) => {
                        match dag[p0].state {
                            DFSExplored => {
                                // explore further
                                path.push((0, p0));
                            }
                            LeafDFSExplored => {
                                let len = path.len();
                                path[len - 1].0 += 1;
                            }
                            _ => unreachable!(),
                        }
                    }
                    None => {
                        // no more sources, backtrack
                        dag[current].state = LeafDFSExplored;

                        let x_i = ptr_to_x_i[&current];
                        // push sorted like normal, except according to lineage
                        if !done_lineages.contains(&x_i) {
                            sorted_lineages.push(x_i);
                            done_lineages.insert(x_i);
                        }

                        path.pop().unwrap();
                        if path.is_empty() {
                            break
                        }
                        // check next dependency
                        let len = path.len();
                        path[len - 1].0 += 1;
                    }
                }
            }
        } else {
            assert!(dag[leaf] == );
        }
    }
    // do the sorting
    let mut new_grid = vec![];
    for x_i in sorted_lineages {
        new_grid.push(grid[x_i].clone());
    }
    let grid = new_grid;*/

    Ok(RenderGrid::new(dag, grid))
}
