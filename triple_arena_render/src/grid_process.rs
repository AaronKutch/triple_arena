#![allow(clippy::needless_range_loop)]

use std::{
    cmp::{min, Ordering, Reverse},
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

#[derive(Debug)]
pub struct BNode<P: Ptr> {
    pub sources: Vec<Edge<P>>,
    pub sinks: Vec<Edge<P>>,
    pub center: Vec<String>,
    pub new_visit: NonZeroU64,
}

/// Algorithmic node. Contains some additional information alongside the
/// `DebugNode` information needed for fast processing
#[derive(Debug)]
pub struct ANode<P: Ptr> {
    // the additional `usize` enables pointing to a specific output in the source node
    pub sources: Vec<(P, String, Option<usize>)>,
    pub center: Vec<String>,
    pub sinks: Vec<(P, String)>,
    /// Used in initial topological sorting
    pub sort_position: usize,
    /// Used for grid positioning
    pub grid_position: (usize, usize),
    pub lineage_num: Option<usize>,
    pub indep_num: Option<usize>,
    pub second_orders: Vec<isize>,
    pub color: Option<NonZeroU64>,
    pub total_ordering: usize,
    // visitation number
    pub visit: u64,
    pub new_visit: NonZeroU64,
}

impl<P: Ptr> Default for ANode<P> {
    fn default() -> Self {
        Self {
            sources: vec![],
            center: vec![],
            sinks: vec![],
            sort_position: 0,
            grid_position: (0, 0),
            lineage_num: None,
            indep_num: None,
            second_orders: vec![],
            color: None,
            total_ordering: 0,
            visit: 0,
            new_visit: NonZeroU64::new(1).unwrap(),
        }
    }
}

// used in the second order algorithm
fn colored_forest<P: Ptr, F: FnMut() -> (u64, u64)>(
    dag: &mut Arena<P, ANode<P>>,
    next_visit: &mut F,
    color_visit: &mut u64,
    p0: P,
    p1: P,
    weight: isize,
) {
    let base = (*color_visit as isize) << 15;
    let base_plus_weight = base + weight;
    match (dag[p0].color, dag[p1].color) {
        (None, None) => {
            // new tree
            let nonce = Some(NonZeroU64::new(*color_visit).unwrap());
            // increment for next tree
            *color_visit = next_visit().1;
            dag[p0].color = nonce;
            dag[p1].color = nonce;
            dag[p0].visit = *color_visit;
            dag[p1].visit = *color_visit;
            dag[p0].second_orders.push(base);
            dag[p1].second_orders.push(base_plus_weight);
        }
        (Some(color0), None) => {
            dag[p1].color = Some(color0);
            dag[p1].visit = *color_visit;
            let tmp = dag[p0].second_orders.last().unwrap() + weight;
            dag[p1].second_orders.push(tmp);
        }
        (None, Some(color1)) => {
            dag[p0].color = Some(color1);
            dag[p0].visit = *color_visit;
            let tmp = dag[p1].second_orders.last().unwrap() - weight;
            dag[p0].second_orders.push(tmp);
        }
        (Some(color0), Some(color1)) => {
            if color0 != color1 {
                // Different trees.

                // new color for combining the trees
                let combined_color = NonZeroU64::new(*color_visit).unwrap();
                // increment for next tree
                *color_visit = next_visit().1;

                // overwriting the tree of `p1` with the combined nonce and second order weight
                let mut path = vec![(p1, 0, false)];
                dag[p1].visit = combined_color.get();
                dag[p1].color = Some(combined_color);
                dag[p1].second_orders.push(base_plus_weight);
                loop {
                    let (p, i, r) = path[path.len() - 1];
                    let relation = if r {
                        dag[p].sinks.get(i).map(|(q, _)| *q)
                    } else {
                        dag[p].sources.get(i).map(|(q, ..)| *q)
                    };
                    match relation {
                        Some(q) => {
                            if dag[q].color == Some(color1) {
                                path.push((q, 0, false));
                                dag[q].visit = combined_color.get();
                                dag[q].color = Some(combined_color);
                                dag[q].second_orders.push(base_plus_weight);
                            } else {
                                path.last_mut().unwrap().1 += 1;
                            }
                        }
                        None => {
                            if r {
                                path.pop().unwrap();
                                if path.is_empty() {
                                    break
                                }
                                path.last_mut().unwrap().1 += 1;
                            } else {
                                path.last_mut().unwrap().1 = 0;
                                path.last_mut().unwrap().2 = true;
                            }
                        }
                    }
                }

                // overwriting the tree of `p0` with combined nonce to combine the trees, and 0
                // weight just to the `p0` tree
                let mut path = vec![(p0, 0, false)];
                dag[p0].visit = combined_color.get();
                dag[p0].color = Some(combined_color);
                dag[p0].second_orders.push(base);
                loop {
                    let (p, i, r) = path[path.len() - 1];
                    let relation = if r {
                        dag[p].sinks.get(i).map(|(q, _)| *q)
                    } else {
                        dag[p].sources.get(i).map(|(q, ..)| *q)
                    };
                    match relation {
                        Some(q) => {
                            if dag[q].color == Some(color0) {
                                path.push((q, 0, false));
                                dag[q].visit = combined_color.get();
                                dag[q].color = Some(combined_color);
                                dag[q].second_orders.push(base);
                            } else {
                                path.last_mut().unwrap().1 += 1;
                            }
                        }
                        None => {
                            if r {
                                path.pop().unwrap();
                                if path.is_empty() {
                                    break
                                }
                                path.last_mut().unwrap().1 += 1;
                            } else {
                                path.last_mut().unwrap().1 = 0;
                                path.last_mut().unwrap().2 = true;
                            }
                        }
                    }
                }
            } // else the same color
        }
    }
}

/// Processes an `Arena<P, T>` into a `RenderGrid<P>`
pub fn grid_process<P: Ptr, T: DebugNodeTrait<P>>(
    arena: &Arena<P, T>,
    error_on_invalid_ptr: bool,
) -> Result<RenderGrid<P>, RenderError<P>> {
    let mut visit_counter = 0u64;
    let mut next_visit = || {
        let prev = visit_counter;
        visit_counter = prev.checked_add(1).unwrap();
        (prev, visit_counter)
    };
    let mut new_visit_counter = NonZeroU64::new(1).unwrap();
    let mut new_next_visit = || {
        new_visit_counter =
            NonZeroU64::new(new_visit_counter.get().checked_add(1).unwrap()).unwrap();
        new_visit_counter
    };
    // this is not guaranteed to be a DAG yet but will become one
    let mut dag: Arena<P, ANode<P>> = Arena::new();
    dag.clone_from_with(arena, |p, t| {
        let debug_node = DebugNodeTrait::debug_node(p, t);
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

    // We need to unelide nonexistant sinks that have a corresponding source, and
    // vice versa. This also checks for invalid pointers.
    let unelide_visit = new_next_visit();
    let mut adv = dag.advancer();
    while let Some(p0) = adv.advance(&dag) {
        if dag[p0].new_visit != unelide_visit {
            // check all sinks
            for i0 in 0..dag[p0].sinks.len() {
                let p1 = dag[p0].sinks[i0].0;
                // check for invalid pointers and if a source is elided
                if let Some(node) = dag.get(p1) {
                    // don't elide more than once if it is repeated
                    if !node
                        .sources
                        .iter()
                        .any(|(o, _, inx)| (*o == p0) && (*inx == Some(i0)))
                    {
                        // unelide
                        dag[p1].sources.push((p0, String::new(), Some(i0)));
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
                    if !node.sinks.iter().any(|(o, _)| *o == p0) {
                        // unelide
                        dag[p0].sources[i0].2 = Some(node.sinks.len());
                        dag[p1].sinks.push((p0, String::new()));
                    }
                } else if error_on_invalid_ptr {
                    return Err(RenderError::InvalidPtr(p1))
                }
            }
            dag[p0].new_visit = unelide_visit;
        }
    }

    // fix invalid pointers
    if !error_on_invalid_ptr {
        let mut adv = dag.advancer();
        while let Some(p0) = adv.advance(&dag) {
            for i0 in 0..dag[p0].sinks.len() {
                let p1 = dag[p0].sinks[i0].0;
                if !dag.contains(p1) {
                    let p1_prime = dag.insert(ANode {
                        sources: vec![(p0, String::new(), Some(i0))],
                        center: vec![format!("{:?}(invalid)", p1)],
                        ..Default::default()
                    });
                    dag[p0].sinks[i0].0 = p1_prime;
                }
            }
            for i0 in 0..dag[p0].sources.len() {
                let p1 = dag[p0].sources[i0].0;
                if !dag.contains(p1) {
                    let p1_prime = dag.insert(ANode {
                        center: vec![format!("{:?}(invalid)", p1)],
                        sinks: vec![(p0, String::new())],
                        ..Default::default()
                    });
                    dag[p0].sources[i0].0 = p1_prime;
                }
            }
        }
    }

    // We want to eliminate crossovers for trees and approximate such a case
    // otherwise. When a node's sources or sinks specify a certain order, we can
    // make a record in an `OrdArena` that adds weight to favor that ordering. We
    // also consider the transitivity rule such that A < B and B < C implies more
    // weight for A < C. We keep track of the weight in both directions so that we
    // can measure the "conflict" between forces trying to push orderings both ways.

    let neighboring_incidents_weight = 1;
    let fork_incidents_weight = 1;

    // the `(P, P)` tuple is ordered for uniqueness, the first weight indicates `<`
    // preference and the second `>`.
    let mut orderings = OrdArena::<P, (P, P), (u64, u64)>::new();
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
                let _ = orderings.insert(pair, weight);
            }
        }
    };
    // initial source and sink weight contributions
    let mut adv = dag.advancer();
    while let Some(p) = adv.advance(&dag) {
        for i in 1..dag[p].sources.len() {
            let p0 = dag[p].sources[i - 1].0;
            let p1 = dag[p].sources[i].0;
            f(p0, p1, false, neighboring_incidents_weight);
        }
        for i in 0..dag[p].sources.len() {
            f(
                p,
                dag[p].sources[i].0,
                i > (dag[p].sources.len() / 2),
                fork_incidents_weight,
            );
        }
        for i in 1..dag[p].sinks.len() {
            let p0 = dag[p].sinks[i - 1].0;
            let p1 = dag[p].sinks[i].0;
            f(p0, p1, false, neighboring_incidents_weight);
        }
        for i in 0..dag[p].sinks.len() {
            f(
                p,
                dag[p].sinks[i].0,
                i >= (dag[p].sinks.len() / 2),
                fork_incidents_weight,
            );
        }
    }

    // now do the transitive propogations, for transitivity we do not need the
    // reversed orderings
    let mut buf = vec![];
    for _ in 0..4 {
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
                        buf.push((*p0, *p3, added_weight));
                    }
                }
            }
        }

        for (p0, p1, weight) in buf.drain(..) {
            let (p0, p1, weight) = if p0 < p1 {
                (p0, p1, (weight.0, weight.1))
            } else {
                (p1, p0, (weight.1, weight.0))
            };
            if let Some(p_ordering) = orderings.find_key(&(p0, p1)) {
                let tmp = orderings.get_val_mut(p_ordering).unwrap();
                tmp.0 = tmp.0.saturating_add(weight.0);
                tmp.1 = tmp.1.saturating_add(weight.1);
            } else {
                let _ = orderings.insert((p0, p1), weight);
            }
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
    let mut adv = dag.advancer();
    while let Some(p) = adv.advance(&dag) {
        for i in 1..dag[p].sources.len() {
            let p0 = dag[p].sources[i - 1].0;
            let p1 = dag[p].sources[i].0;
            f(p0, p1);
        }
        for i in 0..dag[p].sources.len() {
            f(p, dag[p].sources[i].0);
        }
        for i in 1..dag[p].sinks.len() {
            let p0 = dag[p].sinks[i - 1].0;
            let p1 = dag[p].sinks[i].0;
            f(p0, p1);
        }
        for i in 0..dag[p].sinks.len() {
            f(p, dag[p].sinks[i].0);
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

    dbg!(&chains);

    // assign the final total orderings
    let mut i = 0;
    for Reverse((_, chain)) in chains {
        for p in chain {
            dag[p].total_ordering = i;
            i += 0;
        }
    }

    let mut ptrs: Vec<P> = dag.ptrs().collect();

    // nodes with no sources
    let mut roots = vec![];
    for p0 in &ptrs {
        if dag[p0].sources.is_empty() {
            roots.push(*p0);
        }
    }

    // Some kinds of cycles will have no roots leading to them. Here, we find nodes
    // reachable from a root. DFS
    let (unelided_visit, root_reachable_visit) = next_visit();
    let mut path: Vec<(usize, P)> = vec![];
    for root in &roots {
        let root = *root;
        if dag[root].visit != root_reachable_visit {
            path.push((0, root));
            loop {
                let current = path[path.len() - 1].1;
                dag[current].visit = root_reachable_visit;
                match dag[current].sinks.get(path[path.len() - 1].0) {
                    Some((p0, _)) => {
                        let p0 = *p0;
                        if dag[p0].visit == unelided_visit {
                            // explore further
                            path.push((0, p0));
                        } else {
                            assert_eq!(dag[p0].visit, root_reachable_visit);
                            // cross edge, check next
                            let len = path.len();
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
        } else {
            //unreachable!()
        }
    }

    // we could just loop over every pointer and all cycles would be broken with the
    // cycle breaking DFS, but we want to bias towards preexisting roots and then
    // check unreachable nodes
    let mut starts = roots.clone();
    for p in &ptrs {
        if dag[p].visit == unelided_visit {
            starts.push(*p);
        } else {
            assert_eq!(dag[p].visit, root_reachable_visit);
        }
        dag[p].visit = root_reachable_visit;
    }

    // DFS for conversion to DAG
    // path from root, with the `usize` indicating which sink was followed
    let (prev_visit, on_stack_visit) = next_visit();
    let (_, dfs_explored_visit) = next_visit();
    let mut path: Vec<(usize, P)> = vec![];
    for start in &starts {
        let start = *start;
        if dag[start].visit == prev_visit {
            path.push((0, start));
            loop {
                let current = path[path.len() - 1].1;
                // self-cycles are handled also if this is done first
                dag[current].visit = on_stack_visit;
                match dag[current].sinks.get(path[path.len() - 1].0) {
                    Some((p0, _)) => {
                        let p0 = *p0;
                        if dag[p0].visit == prev_visit {
                            // explore further
                            path.push((0, p0));
                        } else if dag[p0].visit == on_stack_visit {
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
                                visit: dfs_explored_visit,
                                ..Default::default()
                            });
                            dag[current].sinks[path[path.len() - 1].0].0 = p0_prime0;
                            // special case explore
                            ptrs.push(p0_prime0);

                            let p0_prime1 = dag.insert(ANode {
                                center: vec![format!("{:?}", p0)],
                                sinks: vec![(p0, String::new())],
                                visit: dfs_explored_visit,
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
                        } else {
                            assert_eq!(dag[p0].visit, dfs_explored_visit);
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
        } else {
            assert_eq!(dag[start].visit, dfs_explored_visit);
        }
    }

    // `dag` is now actually a DAG

    // topological sorting
    let (prev_visit, on_stack_visit) = next_visit();
    let (_, dfs_explored_visit) = next_visit();
    let mut sort_num = 0usize;
    // path from root, with the `usize` indicating which sink was followed
    let mut path: Vec<(usize, P)> = vec![];
    let original_root_len = roots.len();
    for root_i in 0..original_root_len {
        let root = roots[root_i];
        if dag[root].visit == prev_visit {
            path.push((0, root));
            loop {
                let current = path[path.len() - 1].1;
                // reaching the `on_stack` state later should not be possible since this is a
                // DAG and the visiting is in the sink direction only
                dag[current].visit = on_stack_visit;
                let tmp = if let Some((tmp, _)) = dag[current].sinks.get(path[path.len() - 1].0) {
                    Some(*tmp)
                } else {
                    None
                };
                match tmp {
                    Some(p0) => {
                        if dag[p0].visit == prev_visit {
                            // explore further
                            path.push((0, p0));
                        } else {
                            assert_eq!(dag[p0].visit, dfs_explored_visit);
                            // cross edge, check next
                            let len = path.len();
                            path[len - 1].0 += 1;
                        }
                    }
                    None => {
                        // no more sinks, backtrack
                        dag[current].visit = dfs_explored_visit;
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
            assert_eq!(dag[root].visit, dfs_explored_visit);
        }
    }

    // beginning with the nodes with the most sources and sinks, `second_orders` are
    // pushed on that prioritize local orderings between nodes. A forest of
    // different colored trees is started, with a new color starting when a node
    // sees that none of its neighbors are already colored. When different colors
    // collide, a new lesser order is pushed on to supply progressively more global
    // orders.
    let mut ranked_nodes = BinaryHeap::<(usize, P)>::new();
    for (p_node, node) in &dag {
        ranked_nodes.push((node.sinks.len() + node.sources.len(), p_node))
    }

    // `color_visit` will be used as both a rolling visit value and a node coloring
    // value
    let (base_visit, mut color_visit) = next_visit();
    while let Some((_, p_node)) = ranked_nodes.pop() {
        // note the sink weights are even and the source weights are odd to even out
        // vertical columns
        for i_sink in 0..dag[p_node].sinks.len() {
            let p_sink = dag[p_node].sinks[i_sink].0;
            colored_forest(
                &mut dag,
                &mut next_visit,
                &mut color_visit,
                p_node,
                p_sink,
                isize::try_from(i_sink).unwrap() * 2,
            );
        }
        for i_source in 0..dag[p_node].sources.len() {
            let p_source = dag[p_node].sources[i_source].0;
            colored_forest(
                &mut dag,
                &mut next_visit,
                &mut color_visit,
                p_node,
                p_source,
                isize::try_from(i_source).unwrap() * 2 + 1,
            );
        }
        if dag[p_node].sinks.is_empty() && dag[p_node].sources.is_empty() {
            dag[p_node].visit = next_visit().1;
        }
    }
    let new_visit = next_visit().1;
    for (_, node) in &mut dag {
        assert!(node.visit > base_visit);
        node.visit = new_visit;
        //node.center.push(format!("{:?}", node.second_orders));
        //node.center.push(format!("{:?}", p));
    }

    // we structure the DAG by looking at the first operand of an operation and
    // constructing a "lineage" aligned with the first operand. We use a special
    // "lineage search" that constructs a vector of lineages. It works by
    // selecting any unexplored node, then adding on to the lineage all the way
    // until a root is reached. If the leafward parts of the lineage are not
    // touched on the first exploration, later explorations through
    // the same lineage will overwrite the lineage number.
    let mut lineage_num = 0;
    let mut lineage_leaves: Vec<(usize, P)> = vec![];
    for p0 in &ptrs {
        let mut next = *p0;
        if dag[next].lineage_num.is_none() {
            dag[next].lineage_num = Some(lineage_num);
            // Record the leaf of this lineage
            lineage_leaves.push((lineage_num, next));
            while let Some((next_zeroeth, ..)) = dag[next].sources.first() {
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
        while let Some((next_zeroeth, _)) = dag[next].sinks.first() {
            next = *next_zeroeth;
        }
        // overwrite from leaf back to root
        dag[next].lineage_num = Some(lineage_num);
        lineage_leaves.push((lineage_num, next));
        while let Some((next_zeroeth, ..)) = dag[next].sources.first() {
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
    let mut lineages: Vec<Vec<P>> = vec![];
    for (lineage_num, leaf) in lineage_leaves {
        let mut next = leaf;
        let mut lineage = vec![next];
        while let Some((next_zeroeth, ..)) = dag[next].sources.first() {
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
    let (prev_visit, on_stack_visit) = next_visit();
    let (_, dfs_explored_visit) = next_visit();
    let mut path: Vec<(bool, usize, P)> = vec![];
    let mut indep_num = 0;
    for lineage in &lineages {
        let node = lineage[0];
        if dag[node].indep_num.is_none() {
            if dag[node].visit == prev_visit {
                path.push((false, 0, node));
                loop {
                    let current = path.last().unwrap().2;
                    // reaching this visit is possible because we are going through both sinks and
                    // sources
                    dag[current].visit = on_stack_visit;
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
                            if dag[p0].visit == prev_visit {
                                // explore further
                                path.push((false, 0, p0));
                            } else {
                                // cross edge, check next
                                let len = path.len();
                                path[len - 1].1 += 1;
                            }
                        }
                        None => {
                            if path.last().unwrap().0 {
                                // no more relations, backtrack
                                dag[current].visit = dfs_explored_visit;
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
                assert_eq!(dag[node].visit, dfs_explored_visit);
            }
            indep_num += 1;
        }
        // else the lineage is connected to a known set
    }

    // stable sort horizontally so that the lineage numbers are monotonically
    // increasing, followed in priority by the second_orders
    lineages.sort_by(|lhs, rhs| {
        //dag[lhs[0]].total_ordering.cmp(&dag[rhs[0]].total_ordering)
        let lhs0 = dag[lhs[0]].indep_num.unwrap();
        let rhs0 = dag[rhs[0]].indep_num.unwrap();
        match lhs0.cmp(&rhs0) {
            Ordering::Equal => {
                let order0 = &dag[lhs[0]].second_orders;
                let order1 = &dag[rhs[0]].second_orders;
                let mut res = Ordering::Equal;
                for i in 0..min(order0.len(), order1.len()) {
                    match order0[order0.len() - 1 - i].cmp(&order1[order1.len() - 1 - i]) {
                        Ordering::Equal => continue,
                        ne => res = ne,
                    }
                    break
                }
                res
            }
            c => c,
        }
    });

    // Finally, make a grid such that any dependency must flow one way. The second
    // element in the tuple says how far back from the leaf line the node should be
    // placed.
    let mut grid: Vec<Vec<(P, usize)>> = vec![];
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
                    slot.1 = pos;
                    dag[slot.0].sort_position = pos;
                    changed = true;
                }
            }
        }
        if !changed {
            break
        }
    }

    // TODO we need a more general square grid processing to exploit empty
    // horizontal space

    Ok(RenderGrid::new(dag, grid))
}
