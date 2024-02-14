#![allow(clippy::needless_range_loop)]

use std::{
    cmp::{max, min, Ordering, Reverse},
    collections::BinaryHeap,
    mem,
    num::NonZeroU64,
};

use triple_arena::{ptr_struct, Advancer, Arena, ChainArena, Link, OrdArena, Ptr};

use crate::{render_grid::RenderGrid, DebugNodeTrait, RenderError};

#[derive(Debug)]
pub struct Edge<P: Ptr> {
    // what the edge points to
    pub to: P,
    // for pointing to a specific part of the incident
    pub i: Option<usize>,
    // string associated with the edge
    pub s: String,
}

/// Algorithmic node. Contains some additional information alongside the
/// `DebugNode` information needed for fast processing
#[derive(Debug)]
pub struct ANode<P: Ptr> {
    pub sources: Vec<Edge<P>>,
    pub sinks: Vec<Edge<P>>,
    pub center: Vec<String>,
    pub visit: NonZeroU64,
    pub grid_position: (usize, usize),
}

impl<P: Ptr> Default for ANode<P> {
    fn default() -> Self {
        Self {
            sources: vec![],
            center: vec![],
            sinks: vec![],
            visit: NonZeroU64::new(1).unwrap(),
            grid_position: (0, 0),
        }
    }
}

// TODO this code could be improved and cleaned up more

/// Processes an `Arena<P, T>` into a `RenderGrid<P>`
pub fn grid_process<P: Ptr, T: DebugNodeTrait<P>>(
    arena: &Arena<P, T>,
    error_on_invalid_ptr: bool,
) -> Result<RenderGrid<P>, RenderError<P>> {
    let mut visit_counter = NonZeroU64::new(1).unwrap();
    let mut next_visit = || {
        visit_counter = NonZeroU64::new(visit_counter.get().checked_add(1).unwrap()).unwrap();
        visit_counter
    };
    // this is not guaranteed to be a DAG yet but will become one
    let mut dag: Arena<P, ANode<P>> = Arena::new();
    dag.clone_from_with(arena, |p, t| {
        let debug_node = DebugNodeTrait::debug_node(p, t);
        ANode {
            sources: debug_node
                .sources
                .into_iter()
                .map(|(p, s)| Edge { to: p, i: None, s })
                .collect(),
            center: debug_node.center,
            sinks: debug_node
                .sinks
                .into_iter()
                .map(|(p, s)| Edge { to: p, i: None, s })
                .collect(),
            ..Default::default()
        }
    });

    // We need to unelide nonexistant sinks that have a corresponding source, and
    // vice versa. This also checks for invalid pointers.
    let mut adv = dag.advancer();
    while let Some(p0) = adv.advance(&dag) {
        // check all sinks
        for i0 in 0..dag[p0].sinks.len() {
            let p1 = dag[p0].sinks[i0].to;
            // check for invalid pointers and if a source is elided
            if let Some(node) = dag.get(p1) {
                // don't elide more than once if it is repeated
                if !node
                    .sources
                    .iter()
                    .any(|Edge { to, i, s: _ }| (*to == p0) && (*i == Some(i0)))
                {
                    // unelide
                    dag[p1].sources.push(Edge {
                        to: p0,
                        i: Some(i0),
                        s: String::new(),
                    });
                }
            } else if error_on_invalid_ptr {
                return Err(RenderError::InvalidPtr(p1))
            }
        }
        // check all sources
        for i0 in 0..dag[p0].sources.len() {
            let p1 = dag[p0].sources[i0].to;
            // check for invalid pointers and if a sink is elided
            if let Some(node) = dag.get(p1) {
                if !node.sinks.iter().any(|Edge { to, i: _, s: _ }| *to == p0) {
                    // unelide
                    dag[p0].sources[i0].i = Some(node.sinks.len());
                    dag[p1].sinks.push(Edge {
                        to: p0,
                        i: Some(i0),
                        s: String::new(),
                    });
                }
            } else if error_on_invalid_ptr {
                return Err(RenderError::InvalidPtr(p1))
            }
        }
    }

    // fix invalid pointers
    let mut adv = dag.advancer();
    while let Some(p0) = adv.advance(&dag) {
        for i0 in 0..dag[p0].sinks.len() {
            let p1 = dag[p0].sinks[i0].to;
            if !dag.contains(p1) {
                let p1_prime = dag.insert(ANode {
                    sources: vec![Edge {
                        to: p0,
                        i: Some(i0),
                        s: String::new(),
                    }],
                    center: vec![format!("{:?}(invalid)", p1)],
                    ..Default::default()
                });
                dag[p0].sinks[i0].to = p1_prime;
            }
        }
        for i0 in 0..dag[p0].sources.len() {
            let p1 = dag[p0].sources[i0].to;
            if !dag.contains(p1) {
                let p1_prime = dag.insert(ANode {
                    center: vec![format!("{:?}(invalid)", p1)],
                    sinks: vec![Edge {
                        to: p0,
                        i: Some(i0),
                        s: String::new(),
                    }],
                    ..Default::default()
                });
                dag[p0].sources[i0].to = p1_prime;
            }
        }
    }

    // nodes with no sources
    let mut roots = vec![];
    for p0 in dag.ptrs() {
        if dag[p0].sources.is_empty() {
            roots.push(p0);
        }
    }

    // Some kinds of cycles will have no roots leading to them. Here, we find nodes
    // reachable from a root. DFS
    let root_reachable_visit = next_visit();
    let mut path: Vec<(usize, P)> = vec![];
    for root in &roots {
        let root = *root;
        if dag[root].visit != root_reachable_visit {
            path.push((0, root));
            loop {
                let len = path.len();
                let current = path[len - 1].1;
                dag[current].visit = root_reachable_visit;
                match dag[current].sinks.get(path[len - 1].0) {
                    Some(edge) => {
                        let p0 = edge.to;
                        if dag[p0].visit != root_reachable_visit {
                            // explore further
                            path.push((0, p0));
                        } else {
                            // cross edge, check next
                            path[len - 1].0 += 1;
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
        }
    }

    // we could just loop over every pointer and all cycles would be broken with the
    // cycle breaking DFS, but we want to bias towards preexisting roots and then
    // check unreachable nodes
    let mut starts = roots.clone();
    let mut adv = dag.advancer();
    while let Some(p) = adv.advance(&dag) {
        if dag[p].visit != root_reachable_visit {
            // push things that were not root reachable
            starts.push(p);
        }
    }

    // the initial visit number in this case
    let prev_visit = NonZeroU64::new(1).unwrap();

    // DFS for conversion to DAG
    // path from root, with the `usize` indicating which sink was followed
    let on_stack_visit = next_visit();
    let dfs_explored_visit = next_visit();
    let mut path: Vec<(usize, P)> = vec![];
    for start in &starts {
        let start = *start;
        if dag[start].visit == prev_visit {
            path.push((0, start));
            loop {
                let len = path.len();
                let current = path[len - 1].1;
                // self-cycles are handled also if this is done first
                dag[current].visit = on_stack_visit;
                match dag[current].sinks.get(path[len - 1].0) {
                    Some(edge) => {
                        let p0 = edge.to;
                        if dag[p0].visit == prev_visit {
                            // explore further
                            path.push((0, p0));
                        } else if dag[p0].visit == on_stack_visit {
                            // cycle found, break cycle by repointing `current`'s sink
                            // pointer to `p0_prime0` and repointing the corresponding
                            // source of `p0` to `p0_prime1`
                            let p0_prime0 = dag.insert(ANode {
                                sources: vec![Edge {
                                    to: current,
                                    i: Some(path[len - 1].0),
                                    s: String::new(),
                                }],
                                center: vec![format!("{:?}", p0)],
                                visit: dfs_explored_visit,
                                ..Default::default()
                            });
                            dag[current].sinks[path[len - 1].0].to = p0_prime0;

                            let p0_prime1 = dag.insert(ANode {
                                center: vec![format!("{:?}", p0)],
                                sinks: vec![Edge {
                                    to: p0,
                                    i: Some(path[len - 1].0),
                                    s: String::new(),
                                }],
                                visit: dfs_explored_visit,
                                ..Default::default()
                            });
                            // find the corresponding source
                            for i1 in 0..dag[p0].sources.len() {
                                if dag[p0].sources[i1].to == current {
                                    dag[p0].sources[i1].to = p0_prime1;
                                    dag[p0].sources[i1].i = Some(0);
                                }
                            }
                            // new root
                            roots.push(p0_prime1);

                            // do nothing so this node is restarted in case
                            // of more cycles in the same node
                        } else {
                            // cross edge, check next
                            let len = path.len();
                            path[len - 1].0 += 1;
                        }
                    }
                    None => {
                        // no more sinks, backtrack
                        dag[current].visit = dfs_explored_visit;
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
        }
    }

    // `dag` is now actually a DAG and we will no longer add any nodes, so a pointer
    // list can be made in case the arena is sparse
    let ptrs: Vec<P> = dag.ptrs().collect();

    // We want to eliminate crossovers for trees and approximate such a case
    // otherwise. When a node's sources or sinks specify a certain order, we can
    // make a record in an `OrdArena` that adds weight to favor that ordering. We
    // also consider the transitivity rule such that A < B and B < C implies more
    // weight for A < C. We keep track of the weight in both directions so that we
    // can measure the "conflict" between forces trying to push orderings both ways.

    let neighboring_incidents_weight = 1;
    let fork_incidents_weight = 1;

    // the `(P, P)` tuple is ordered for uniqueness, the first weight indicates `<`
    // preference and the second `>`. The bool allows only one extra layer of new
    // transitives to be made.
    let mut orderings = OrdArena::<P, (P, P), (u64, u64, bool)>::new();
    let mut f = |p0: P, p1: P, swap: bool, init_weight: u64| {
        let (pair, mut weight) = match p0.cmp(&p1) {
            Ordering::Less => ((p0, p1), (init_weight, 0)),
            Ordering::Equal => ((p0, p1), (0, 0)),
            Ordering::Greater => ((p1, p0), (0, init_weight)),
        };
        if swap {
            mem::swap(&mut weight.0, &mut weight.1);
        }
        if weight != (0, 0) {
            if let Some(p_ordering) = orderings.find_key(&pair) {
                let tmp = orderings.get_val_mut(p_ordering).unwrap();
                tmp.0 = tmp.0.saturating_add(weight.0);
                tmp.1 = tmp.1.saturating_add(weight.1);
            } else {
                let _ = orderings.insert(pair, (weight.0, weight.1, true));
            }
        }
    };
    // initial source and sink weight contributions
    for p in ptrs.iter().copied() {
        for i in 1..dag[p].sources.len() {
            let p0 = dag[p].sources[i - 1].to;
            let p1 = dag[p].sources[i].to;
            f(p0, p1, false, neighboring_incidents_weight);
        }
        for i in 0..dag[p].sources.len() {
            f(
                p,
                dag[p].sources[i].to,
                i > (dag[p].sources.len() / 2),
                fork_incidents_weight,
            );
        }
        for i in 1..dag[p].sinks.len() {
            let p0 = dag[p].sinks[i - 1].to;
            let p1 = dag[p].sinks[i].to;
            f(p0, p1, false, neighboring_incidents_weight);
        }
        for i in 0..dag[p].sinks.len() {
            f(
                p,
                dag[p].sinks[i].to,
                i >= (dag[p].sinks.len() / 2),
                fork_incidents_weight,
            );
        }
    }

    // now do the transitive propogations, for transitivity we do not need the
    // reversed orderings
    let mut buf = vec![];
    for _ in 0..2 {
        let mut adv = orderings.advancer();
        while let Some(p_ordering) = adv.advance(&orderings) {
            let ((p0, p1), weight) = orderings.get(p_ordering).unwrap();

            // find the start of a region with `p1`
            if let Some((p_region_start, ord)) =
                orderings.find_similar_with(|_, (p, _), _| match p1.cmp(p) {
                    Ordering::Less => Ordering::Less,
                    Ordering::Equal => Ordering::Less,
                    Ordering::Greater => Ordering::Greater,
                })
            {
                let mut adv_region = orderings.advancer_starting_from(p_region_start);
                if ord.is_gt() {
                    // advance by one to get into the region
                    adv_region.advance(&orderings);
                }
                while let Some(p_ordering) = adv_region.advance(&orderings) {
                    let ((p2, p3), weight1) = orderings.get(p_ordering).unwrap();
                    if *p2 != *p1 {
                        // reached the end of the region
                        break
                    }
                    let added_weight = (
                        weight.0.saturating_add(weight1.0),
                        weight.1.saturating_add(weight1.1),
                    );
                    if (added_weight != (0, 0)) && (*p0 != *p3) {
                        buf.push((
                            *p0,
                            *p3,
                            (added_weight.0, added_weight.1, weight.2 && weight1.2),
                        ));
                    }
                }
            }
        }

        for (p0, p1, weight0) in buf.drain(..) {
            let (p0, p1, weight) = if p0 < p1 {
                (p0, p1, (weight0.0, weight0.1))
            } else {
                (p1, p0, (weight0.1, weight0.0))
            };
            if let Some(p_ordering) = orderings.find_key(&(p0, p1)) {
                let tmp = orderings.get_val_mut(p_ordering).unwrap();
                tmp.0 = tmp.0.saturating_add(weight.0);
                tmp.1 = tmp.1.saturating_add(weight.1);
            } else if weight0.2 {
                let _ = orderings.insert((p0, p1), (weight.0, weight.1, false));
            }
            // else do not create new transitive edges
        }
    }

    // Now we will construct the total ordering. We want immediate relations to be
    // ordered close together primarily. What we will do is use a chain arena, and
    // when finding a relation A < B, the end of the chain containing A will be
    // attached to the start of the chain containing B. We will use the conflict of
    // the weights such that orderings with no conflicts are prioritized first.

    let mut prioritize = BinaryHeap::<Reverse<(u64, P, P)>>::new();
    let mut f = |p0: P, p1: P| {
        let (p0, p1) = if p0 < p1 { (p0, p1) } else { (p1, p0) };
        if let Some(p_ordering) = orderings.find_key(&(p0, p1)) {
            let weight = orderings.get_val(p_ordering).unwrap();
            if weight.0 < weight.1 {
                prioritize.push(Reverse((min(weight.0, weight.1), p1, p0)));
            } else {
                prioritize.push(Reverse((min(weight.0, weight.1), p0, p1)));
            }
        } else {
            prioritize.push(Reverse((0, p0, p1)));
        }
    };
    for p in ptrs.iter().copied() {
        for i in 1..dag[p].sources.len() {
            let p0 = dag[p].sources[i - 1].to;
            let p1 = dag[p].sources[i].to;
            f(p0, p1);
        }
        for i in 0..dag[p].sources.len() {
            f(p, dag[p].sources[i].to);
        }
        for i in 1..dag[p].sinks.len() {
            let p0 = dag[p].sinks[i - 1].to;
            let p1 = dag[p].sinks[i].to;
            f(p0, p1);
        }
        for i in 0..dag[p].sinks.len() {
            f(p, dag[p].sinks[i].to);
        }
    }

    // we are using a kind of acyclic surject arena here, the `Q` in the links are
    // colors and they point to sizes of the chains and are used to detect if `p0`
    // and `p1` are already part of the same chain

    ptr_struct!(Q());
    let mut chain_lens = Arena::<Q, usize>::new();
    let mut tmp = Arena::<P, Link<P, Q>>::new();
    tmp.clone_from_with(&dag, |_, _| Link::new((None, None), chain_lens.insert(0)));
    let mut total_ordering = ChainArena::<P, Q>::from_arena(tmp).unwrap();
    while let Some(Reverse((_, p0, p1))) = prioritize.pop() {
        let q0 = *total_ordering.get(p0).unwrap();
        let q1 = *total_ordering.get(p1).unwrap();
        if q0 != q1 {
            // find end of `q0` chain
            let mut p0_end = p0;
            while let Some(next) = total_ordering.get_link(p0_end).unwrap().next() {
                p0_end = next;
            }
            // find start of `q1` chain but also recolor
            let mut p1_start = Ptr::invalid();
            let mut adv = total_ordering.advancer_chain(p1);
            while let Some(p) = adv.advance(&total_ordering) {
                let link = total_ordering.get_link_mut(p).unwrap();
                if link.prev().is_none() {
                    p1_start = p;
                }
                *link.t = q0;
            }
            total_ordering.connect(p0_end, p1_start).unwrap();
            let q1_len = *chain_lens.get(q1).unwrap();
            // q1 is erased, but need to update the length of q0
            *chain_lens.get_mut(q0).unwrap() += q1_len;
            chain_lens.remove(q1).unwrap();
        }
    }

    // by the end, disconnected graphs will be in different chains, order from
    // biggest to smallest since in practices there are insignificant single node
    // subgraphs and stuff
    let mut chains = Vec::<Reverse<(usize, Vec<P>)>>::new();
    let mut adv = total_ordering.advancer();
    while let Some(mut p) = adv.advance(&total_ordering) {
        // move to the start of a chain as we encounter one
        while let Some(prev) = total_ordering.get_link(p).unwrap().prev() {
            p = prev;
        }
        // remove the chain and record it in order
        let mut chain = vec![];
        loop {
            if let Some(next) = total_ordering.get_link(p).unwrap().next() {
                chain.push(p);
                total_ordering.remove(p).unwrap();
                p = next;
            } else {
                chain.push(p);
                total_ordering.remove(p).unwrap();
                break
            }
        }
        chains.push(Reverse((chain.len(), chain)));
    }
    chains.sort();

    // assign the final total orderings to the grid positions
    let mut i = 0;
    for Reverse((_, chain)) in chains {
        for p in chain {
            dag[p].grid_position.0 = i;
            // give space for the next step
            i += 2;
        }
    }
    let max_x = i;

    // get grid heights from the DAG

    // for each disconnected part we want a full DFS through sinks and sources
    let height_visit = next_visit();
    let normalize_visit = next_visit();
    for p in ptrs.iter().copied() {
        if dag[p].visit != normalize_visit {
            // set initial vertical to half of `usize::MAX`
            let mut path = vec![];
            path.push((false, 0, p, usize::MAX / 2));
            let mut minimum_height = usize::MAX / 2;
            loop {
                let len = path.len();
                let current = path[len - 1].2;
                dag[current].visit = height_visit;

                let current_height = path[len - 1].3;
                if (!path[len - 1].0) && (path[len - 1].1 == 0) {
                    dag[current].grid_position.1 = current_height;
                    minimum_height = min(minimum_height, current_height);
                }

                if path[len - 1].0 {
                    match dag[current].sinks.get(path[len - 1].1) {
                        Some(edge) => {
                            let p0 = edge.to;
                            if dag[p0].visit != height_visit {
                                // explore further
                                path.push((false, 0, p0, current_height + 1));
                            } else {
                                // cross edge, check next
                                path[len - 1].1 += 1;
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
                            path[len - 1].1 += 1;
                        }
                    }
                } else {
                    match dag[current].sources.get(path[len - 1].1) {
                        Some(edge) => {
                            let p0 = edge.to;
                            if dag[p0].visit != height_visit {
                                // explore further
                                path.push((false, 0, p0, current_height - 1));
                            } else {
                                // cross edge, check next
                                path[len - 1].1 += 1;
                            }
                        }
                        None => {
                            // no more sources, change to sinks
                            path[len - 1].0 = true;
                            path[len - 1].1 = 0;
                        }
                    }
                }
            }
            // go back over and subtract by the overall minimum height
            let mut path = vec![];
            path.push((false, 0, p));
            loop {
                let len = path.len();
                let current = path[len - 1].2;
                dag[current].visit = normalize_visit;

                if (!path[len - 1].0) && (path[len - 1].1 == 0) {
                    dag[current].grid_position.1 -= minimum_height;
                }

                if path[len - 1].0 {
                    match dag[current].sinks.get(path[len - 1].1) {
                        Some(edge) => {
                            let p0 = edge.to;
                            if dag[p0].visit != normalize_visit {
                                // explore further
                                path.push((false, 0, p0));
                            } else {
                                // cross edge, check next
                                path[len - 1].1 += 1;
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
                            path[len - 1].1 += 1;
                        }
                    }
                } else {
                    match dag[current].sources.get(path[len - 1].1) {
                        Some(edge) => {
                            let p0 = edge.to;
                            if dag[p0].visit != normalize_visit {
                                // explore further
                                path.push((false, 0, p0));
                            } else {
                                // cross edge, check next
                                path[len - 1].1 += 1;
                            }
                        }
                        None => {
                            // no more sources, change to sinks
                            path[len - 1].0 = true;
                            path[len - 1].1 = 0;
                        }
                    }
                }
            }
        }
    }

    // everything has a grid position. Vertical positions are mostly good, but we
    // want to compress horizontally. The idea is that every node has a desired
    // location to be in, either the average horizontal positions of their sources
    // and sinks or some median of them. If a node would collide with another if it
    // would try to move, a "force" is propogated that says how many places it wants
    // to travel and the intensity.

    //let mut prioritize = BinaryHeap::<(usize, P)>::new();
    // initialize horizontals
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct HInfo<P: Ptr> {
        // needs to be ordered by grid position
        grid_pos0: usize,
        p: P,
    }
    let mut horizontals: Vec<OrdArena<P, HInfo<P>, ()>> = vec![];
    let mut max_y = 0;
    for p in ptrs.iter().copied() {
        max_y = max(max_y, dag[p].grid_position.1);
    }
    for _ in 0..(max_y + 1) {
        horizontals.push(OrdArena::new());
    }
    for p in ptrs.iter().copied() {
        let _ = horizontals[dag[p].grid_position.1].insert(
            HInfo {
                grid_pos0: dag[p].grid_position.0,
                p,
            },
            (),
        );
    }

    // The transitive ordering is very good but the priority of the chain merging
    // often leads to a situation where a node has all of its connections in one
    // direction in a way that should obviously be reordered. This gets rid of
    // crossovers immediate crossover reduction (the transitive ordering
    // sometimes put nodes in an obviously bad place due to priority ordering
    // turning out to be bad)
    for p0 in ptrs.iter().copied() {
        // detect if all connections are towards one direction
        let node0 = &dag[p0];
        if (node0.sources.len() + node0.sinks.len()) <= 1 {
            continue
        }
        let pos0 = node0.grid_position.0;
        let mut min_pos1 = usize::MAX;
        let mut max_pos1 = 0;
        for edge0 in &node0.sources {
            let p1 = edge0.to;
            let node1 = &dag[p1];
            let pos1 = node1.grid_position.0;
            min_pos1 = min(min_pos1, pos1);
            max_pos1 = max(max_pos1, pos1);
        }
        for edge0 in &node0.sinks {
            let p1 = edge0.to;
            let node1 = &dag[p1];
            let pos1 = node1.grid_position.0;
            min_pos1 = min(min_pos1, pos1);
            max_pos1 = max(max_pos1, pos1);
        }
        let new_pos = if (min_pos1 > (pos0 + 2)) && (max_pos1 > pos0) {
            min_pos1.saturating_add(1)
        } else if (min_pos1 < pos0) && (max_pos1 < (pos0 - 2)) {
            max_pos1.saturating_sub(1)
        } else {
            continue
        };
        // check the horizontal for collisions
        let horizontal = &mut horizontals[node0.grid_position.1];
        if horizontal
            .find_with(|_, hinfo, _| new_pos.cmp(&hinfo.grid_pos0))
            .is_none()
        {
            let p_h = horizontal
                .find_with(|_, hinfo, _| dag[p0].grid_position.0.cmp(&hinfo.grid_pos0))
                .unwrap();
            let mut hinfo = horizontal.remove(p_h).unwrap().0;
            dag[p0].grid_position.0 = new_pos;
            hinfo.grid_pos0 = new_pos;
            let _ = horizontal.insert(hinfo, ());
        }
    }

    // TODO we could have something more sophisticated that can push other nodes out
    // of the way, but for now we just iterate a fixed number of times and
    // prioritize on the number of incidents a node has

    for _ in 0..8 {
        // this won't entirely compress large graphs, but for large graphs we want to
        // purposely leave some extra space

        // bulk moving, if a single compression of a column can happen without any
        // collision then it should happen
        let mut f = |offset: bool| {
            let mut cumulative = vec![];
            if offset {
                cumulative.push(0);
            }
            let mut x = if offset { 1 } else { 0 };
            let mut shift = x;
            loop {
                if x >= max_x {
                    break
                }
                let mut collision = false;
                for horizontal in &horizontals {
                    if horizontal
                        .find_with(|_, hinfo, _| x.cmp(&hinfo.grid_pos0))
                        .is_some()
                        && horizontal
                            .find_with(|_, hinfo, _| (x + 1).cmp(&hinfo.grid_pos0))
                            .is_some()
                    {
                        collision = true;
                        break
                    }
                }
                cumulative.push(shift);
                if collision {
                    shift += 1;
                }
                cumulative.push(shift);
                shift += 1;
                x += 2;
            }
            // apply shifts
            let mut new = vec![];
            for horizontal in &mut horizontals {
                for (_, mut hinfo, _) in horizontal.drain() {
                    hinfo.grid_pos0 = cumulative[hinfo.grid_pos0];
                    dag[hinfo.p].grid_position.0 = hinfo.grid_pos0;
                    new.push(hinfo);
                }
                for hinfo in new.drain(..) {
                    let _ = horizontal.insert(hinfo, ());
                }
            }
        };
        // have to alternate
        f(false);
        f(true);

        // average moving
        for p in ptrs.iter().copied() {
            let node = &dag[p];
            // average seems to be better than median
            let mut sum = 0usize;
            for edge in &node.sources {
                sum = sum.saturating_add(dag[edge.to].grid_position.0);
            }
            for edge in &node.sinks {
                sum = sum.saturating_add(dag[edge.to].grid_position.0);
            }
            let wanted = sum
                .checked_div(node.sources.len() + node.sinks.len())
                .unwrap_or(0);
            // check the horizontals if we can move
            let horizontal = &mut horizontals[dag[p].grid_position.1];
            let pos = dag[p].grid_position.0;
            let p_h = horizontal
                .find_with(|_, hinfo, _| pos.cmp(&hinfo.grid_pos0))
                .unwrap();
            let maximal_movement = wanted.clamp(
                {
                    if let Some(p_h_sub1) = horizontal.get_link(p_h).unwrap().prev() {
                        horizontal.get(p_h_sub1).unwrap().0.grid_pos0 + 1
                    } else {
                        0
                    }
                },
                {
                    if let Some(p_h_add1) = horizontal.get_link(p_h).unwrap().next() {
                        horizontal.get(p_h_add1).unwrap().0.grid_pos0 - 1
                    } else {
                        horizontal.get(p_h).unwrap().0.grid_pos0
                    }
                },
            );
            let current = dag[p].grid_position.0;
            if maximal_movement != current {
                // move
                dag[p].grid_position.0 = maximal_movement;
                let mut hinfo = horizontal.remove(p_h).unwrap().0;
                hinfo.grid_pos0 = maximal_movement;
                let _ = horizontal.insert(hinfo, ());
                /*prioritize.push((
                    wanted
                        .abs_diff(current)
                        .saturating_mul(node.sources.len() + node.sinks.len()),
                    p,
                ));*/
            }
        }
    }

    /*
    for p in ptrs.iter().copied() {
        horizontals[dag[p].grid_position.1]
        .find_with(|_, hinfo, _|dag[p].grid_position.0.cmp(&hinfo.grid_pos0)).unwrap();
    }
    */

    Ok(RenderGrid::new(dag))
}
