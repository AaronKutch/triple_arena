#![allow(clippy::needless_range_loop)]

use std::cmp::Ordering;

/// For different node states used by algorithms
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VisitState {
    Initial,
    Unelided,
    RootReachable,
    Prepared,
    OnStack0,
    DFSExplored0,
    OnStack1,
    DFSExplored1,
    OnStack2,
    DFSExplored2,
    OnStack3,
    DFSExplored3,
}

use triple_arena::{Arena, Ptr, PtrTrait};
use VisitState::*;

use crate::{render_grid::RenderGrid, DebugNodeTrait, RenderError};

impl Default for VisitState {
    fn default() -> Self {
        Initial
    }
}

/// Algorithmic node. Contains some additional information alongside the
/// `DebugNode` information needed for fast processing
#[derive(Debug)]
pub struct ANode<P: PtrTrait> {
    // the additional `usize` enables pointing to a specific output in the source node
    pub sources: Vec<(Ptr<P>, String, Option<usize>)>,
    pub center: Vec<String>,
    pub sinks: Vec<(Ptr<P>, String)>,
    pub state: VisitState,
    /// Used in initial topological sorting
    pub sort_position: usize,
    /// Used for grid positioning
    pub grid_position: (usize, usize),
    pub lineage_num: Option<usize>,
    pub indep_num: Option<usize>,
    pub second_order_num: Option<usize>,
}

impl<P: PtrTrait> Default for ANode<P> {
    fn default() -> Self {
        Self {
            sources: vec![],
            center: vec![],
            sinks: vec![],
            state: VisitState::default(),
            sort_position: 0,
            grid_position: (0, 0),
            lineage_num: None,
            indep_num: None,
            second_order_num: None,
        }
    }
}

/// Processes an `Arena<P, T>` into a `RenderGrid<P>`
pub fn grid_process<P: PtrTrait, T: DebugNodeTrait<P>>(
    arena: &Arena<P, T>,
    error_on_invalid_ptr: bool,
) -> Result<RenderGrid<P>, RenderError<P>> {
    // this is not guaranteed to be a DAG yet but will become one
    let mut dag: Arena<P, ANode<P>> = Arena::new();
    dag.clone_from_with(arena, |_, t| {
        let debug_node = DebugNodeTrait::debug_node(t);
        ANode {
            sources: debug_node
                .sources
                .into_iter()
                .map(|(p, s)| (p, s, None))
                .collect(),
            center: debug_node.center,
            sinks: debug_node.sinks,
            ..Default::default()
        }
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
            for i0 in 0..dag[p0].sinks.len() {
                let p1 = dag[p0].sinks[i0].0;
                // check for invalid pointers and if a source is elided
                if let Some(node) = dag.get(p1) {
                    if !node
                        .sources
                        .iter()
                        .any(|(o, _, inx)| (*o == *p0) && (*inx == Some(i0)))
                    {
                        // unelide
                        dag[p1].sources.push((*p0, String::new(), Some(i0)));
                    }
                } else if error_on_invalid_ptr {
                    return Err(RenderError::InvalidPtr(p1))
                }
            }
            // check all sources
            for i0 in 0..dag[p0].sources.len() {
                let p1 = dag[p0].sources[i0].0;
                // check for invalid pointers and if a sink is elided
                if let Some(node) = dag.get(p1) {
                    if !node.sinks.iter().any(|(o, _)| *o == *p0) {
                        // unelide
                        dag[p0].sources[i0].2 = Some(node.sinks.len());
                        dag[p1].sinks.push((*p0, String::new()));
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
            for i0 in 0..dag[p0].sinks.len() {
                let p1 = dag[p0].sinks[i0].0;
                if !dag.contains(p1) {
                    let p1_prime = dag.insert(ANode {
                        sources: vec![(p0, String::new(), Some(i0))],
                        center: vec![format!("{:?}(invalid)", p1)],
                        state: Unelided,
                        ..Default::default()
                    });
                    dag[p0].sinks[i0].0 = p1_prime;
                    ptrs.push(p1_prime);
                }
            }
            for i0 in 0..dag[p0].sources.len() {
                let p1 = dag[p0].sources[i0].0;
                if !dag.contains(p1) {
                    let p1_prime = dag.insert(ANode {
                        center: vec![format!("{:?}(invalid)", p1)],
                        sinks: vec![(p0, String::new())],
                        state: Unelided,
                        ..Default::default()
                    });
                    dag[p0].sources[i0].0 = p1_prime;
                    ptrs.push(p1_prime);
                }
            }
        }
    }

    // nodes with no sources
    let mut roots = vec![];
    for p0 in &ptrs {
        if dag[p0].sources.is_empty() {
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
                match dag[current].sinks.get(path[path.len() - 1].0) {
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
                match dag[current].sinks.get(path[path.len() - 1].0) {
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
                                    sources: vec![(
                                        current,
                                        String::new(),
                                        Some(path[path.len() - 1].0),
                                    )],
                                    center: vec![format!("{:?}", p0)],
                                    state: DFSExplored0,
                                    ..Default::default()
                                });
                                dag[current].sinks[path[path.len() - 1].0].0 = p0_prime0;
                                // special case explore
                                ptrs.push(p0_prime0);

                                let p0_prime1 = dag.insert(ANode {
                                    center: vec![format!("{:?}", p0)],
                                    sinks: vec![(p0, String::new())],
                                    state: DFSExplored0,
                                    ..Default::default()
                                });
                                // find the corresponding source
                                for i1 in 0..dag[p0].sources.len() {
                                    if dag[p0].sources[i1].0 == current {
                                        dag[p0].sources[i1].0 = p0_prime1;
                                        dag[p0].sources[i1].2 = Some(0);
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
                let tmp = if let Some((tmp, _)) = dag[current].sinks.get(path[path.len() - 1].0) {
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
    let mut lineage_num = 0;
    let mut lineage_leaves: Vec<(usize, Ptr<P>)> = vec![];
    for p0 in &ptrs {
        let mut next = *p0;
        if dag[next].lineage_num.is_none() {
            dag[next].lineage_num = Some(lineage_num);
            // Record the leaf of this lineage
            lineage_leaves.push((lineage_num, next));
            while let Some((next_zeroeth, ..)) = dag[next].sources.get(0) {
                next = *next_zeroeth;
                dag[next].lineage_num = Some(lineage_num);
            }
            lineage_num += 1;
        }
    }

    // Do some more overwriting with lineages that go all the way from a root to a
    // leaf. This tends to reduce dependency line crossings and reduces the work the
    // main crossing reduction step needs to do
    for root in &roots {
        // go from root to leaf
        let mut next = *root;
        while let Some((next_zeroeth, _)) = dag[next].sinks.get(0) {
            next = *next_zeroeth;
        }
        // overwrite from leaf back to root
        dag[next].lineage_num = Some(lineage_num);
        lineage_leaves.push((lineage_num, next));
        while let Some((next_zeroeth, ..)) = dag[next].sources.get(0) {
            next = *next_zeroeth;
            dag[next].lineage_num = Some(lineage_num);
        }
        lineage_num += 1;
    }

    // remove overwritten lineage leaves
    let mut i = 0;
    while let Some((lineage_num, leaf)) = lineage_leaves.get(i) {
        if dag[leaf].lineage_num.unwrap() == *lineage_num {
            i += 1;
        } else {
            lineage_leaves.swap_remove(i);
        }
    }

    // get lineages
    let mut lineages: Vec<Vec<Ptr<P>>> = vec![];
    for (lineage_num, leaf) in lineage_leaves {
        let mut next = leaf;
        let mut lineage = vec![next];
        while let Some((next_zeroeth, ..)) = dag[next].sources.get(0) {
            next = *next_zeroeth;
            if dag[next].lineage_num.unwrap() != lineage_num {
                // another leaf will handle this
                break
            }
            lineage.push(next);
        }
        lineages.push(lineage);
    }

    // Separate sets of lineages that have no relations between each other.
    // DFS through relations (sinks and sources). The `bool` in `path`
    // differentiates between searching sources and sinks
    let mut path: Vec<(bool, usize, Ptr<P>)> = vec![];
    let mut indep_num = 0;
    for lineage in &lineages {
        let node = lineage[0];
        if dag[node].indep_num.is_none() {
            if dag[node].state == DFSExplored1 {
                path.push((false, 0, node));
                loop {
                    let current = path.last().unwrap().2;
                    dag[current].state = OnStack2;
                    dag[current].indep_num = Some(indep_num);
                    let relation = if path.last().unwrap().0 {
                        dag[current]
                            .sinks
                            .get(path.last().unwrap().1)
                            .map(|(p0, _)| p0)
                    } else {
                        dag[current]
                            .sources
                            .get(path.last().unwrap().1)
                            .map(|(p0, ..)| p0)
                    };
                    match relation {
                        Some(p0) => {
                            let p0 = *p0;
                            match dag[p0].state {
                                DFSExplored1 => {
                                    // explore further
                                    path.push((false, 0, p0));
                                }
                                // `DFSExplored2` needs to be included for multigraph conditions
                                OnStack2 | DFSExplored2 => {
                                    // cross edge, check next
                                    let len = path.len();
                                    path[len - 1].1 += 1;
                                }
                                _ => unreachable!(),
                            }
                        }
                        None => {
                            if path.last().unwrap().0 {
                                // no more relations, backtrack
                                dag[current].state = DFSExplored2;
                                path.pop().unwrap();
                                if path.is_empty() {
                                    break
                                }
                                // check next dependency
                                let len = path.len();
                                path[len - 1].1 += 1;
                            } else {
                                // change relation type
                                let len = path.len();
                                path[len - 1].0 = true;
                                path[len - 1].1 = 0;
                            }
                        }
                    }
                }
            } else {
                assert_eq!(dag[node].state, DFSExplored2);
            }
            indep_num += 1;
        }
        // else the lineage is connected to a known set
    }

    let mut leaves = vec![];
    for p in &ptrs {
        if dag[p].sinks.is_empty() {
            leaves.push(*p);
        }
    }

    // For reducing line crossings further.
    let mut path: Vec<(usize, Ptr<P>)> = vec![];
    let mut order_num = 0;
    for leaf in &leaves {
        let node = *leaf;
        if dag[node].state == DFSExplored2 {
            path.push((0, node));
            loop {
                let current = path.last().unwrap().1;
                dag[current].state = OnStack3;
                if dag[current].second_order_num.is_none() {
                    dag[current].second_order_num = Some(order_num);
                }
                match dag[current]
                    .sources
                    .get(path.last().unwrap().0)
                    .map(|(p0, ..)| p0)
                {
                    Some(p0) => {
                        let p0 = *p0;
                        match dag[p0].state {
                            DFSExplored2 => {
                                // explore further
                                path.push((0, p0));
                            }
                            // `DFSExplored3` needs to be included for multigraph conditions
                            OnStack3 | DFSExplored3 => {
                                // cross edge, check next
                                let len = path.len();
                                path[len - 1].0 += 1;
                            }
                            _ => unreachable!(),
                        }
                    }
                    None => {
                        // no more relations, backtrack
                        order_num += 1;
                        dag[current].state = DFSExplored3;
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
            assert_eq!(dag[node].state, DFSExplored3);
        }
    }

    // stable sort horizontally so that the lineage numbers are monotonically
    // increasing, followed in priority by the second_sort_num
    lineages.sort_by(|lhs, rhs| {
        let lhs0 = dag[lhs[0]].indep_num.unwrap();
        let rhs0 = dag[rhs[0]].indep_num.unwrap();
        match lhs0.cmp(&rhs0) {
            Ordering::Equal => {
                let lhs0 = dag[lhs[0]].second_order_num.unwrap();
                let rhs0 = dag[rhs[0]].second_order_num.unwrap();
                lhs0.cmp(&rhs0)
            }
            c => c,
        }
    });

    // Finally, make a grid such that any dependency must flow one way. The second
    // element in the tuple says how far back from the leaf line the node should be
    // placed.
    let mut grid: Vec<Vec<(Ptr<P>, usize)>> = vec![];
    for lineage in &lineages {
        let mut vertical = vec![];
        for ptr in lineage {
            // the topological ordering insures dependencies flow one way
            vertical.push((*ptr, dag[ptr].sort_position));
        }
        grid.push(vertical);
    }
    // Compress the `sort_position`s vertically as much as possible.
    let mut changed;
    loop {
        // may need multiple rounds
        changed = false;
        for vertical in &mut grid {
            for slot in &mut *vertical {
                let mut pos = 0;
                for (sink, _) in &dag[slot.0].sinks {
                    // find highest sinks position + 1
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

    // TODO we really need the square grid in `(Ptr<P>, usize)` form in this
    // function in order to exploit empty space. We should use a "rubber band"
    // based method to minimize more crossings and make large graphs more
    // compact.

    Ok(RenderGrid::new(dag, grid))
}
