//! utils for graphs

use std::collections::VecDeque;

use rustc_data_structures::graph::{DirectedGraph, Successors, scc, vec_graph::VecGraph};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{Idx, IndexVec, bit_set::ChunkedBitSet};

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "scc{}"]
    /// A unique identifier for a strongly connected component (SCC).
    pub struct SccId {}
}

/// Strongly connected components (SCCs) of a directed graph.
pub struct Sccs<T, const BR: bool> {
    /// SCC to its successors
    graph: VecGraph<SccId, BR>,
    /// SCC to its element nodes
    pub scc_elems: IndexVec<SccId, FxHashSet<T>>,
    /// Node to SCC it belongs to
    pub indices: FxHashMap<T, SccId>,
}

impl<T: Eq + std::hash::Hash, const BR: bool> Sccs<T, BR> {
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.scc_elems.is_empty()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.scc_elems.len()
    }

    #[inline]
    pub fn successors(&self, scc_id: SccId) -> &[SccId] {
        self.graph.successors(scc_id)
    }

    #[inline]
    pub fn post_order(
        &self,
    ) -> impl DoubleEndedIterator<Item = SccId> + ExactSizeIterator + Clone + 'static {
        self.scc_elems.indices()
    }

    #[inline]
    pub fn scc(&self, t: &T) -> &FxHashSet<T> {
        &self.scc_elems[self.indices[t]]
    }
}

impl<T: Eq + std::hash::Hash> Sccs<T, true> {
    #[inline]
    pub fn predecessors(&self, scc_id: SccId) -> &[SccId] {
        self.graph.predecessors(scc_id)
    }
}

/// Computes the strongly connected components (SCCs) of a directed graph whose nodes are copyable.
pub fn sccs_copied<T: Copy + Eq + std::hash::Hash, const BR: bool>(
    graph: &FxHashMap<T, FxHashSet<T>>,
) -> Sccs<T, BR> {
    let mut id_to_node = vec![];
    let mut node_to_id = FxHashMap::default();
    for (i, node) in graph.keys().copied().enumerate() {
        id_to_node.push(node);
        node_to_id.insert(node, i);
    }
    let edges = graph
        .iter()
        .flat_map(|(node, succs)| {
            let node = node_to_id[node];
            let node_to_id = &node_to_id;
            succs.iter().map(move |succ| (node, node_to_id[succ]))
        })
        .collect();
    sccs_common(id_to_node, edges)
}

/// Computes the strongly connected components (SCCs) of a directed graph.
pub fn sccs<T: Eq + std::hash::Hash, const BR: bool>(
    graph: &FxHashMap<T, FxHashSet<T>>,
) -> Sccs<&T, BR> {
    let mut id_to_node = vec![];
    let mut node_to_id = FxHashMap::default();
    for (i, node) in graph.keys().enumerate() {
        id_to_node.push(node);
        node_to_id.insert(node, i);
    }
    let edges = graph
        .iter()
        .flat_map(|(node, succs)| {
            let node = node_to_id[node];
            let node_to_id = &node_to_id;
            succs.iter().map(move |succ| (node, node_to_id[succ]))
        })
        .collect();
    sccs_common(id_to_node, edges)
}

fn sccs_common<T: Copy + Eq + std::hash::Hash, const BR: bool>(
    id_to_node: Vec<T>,
    edges: Vec<(usize, usize)>,
) -> Sccs<T, BR> {
    let vec_graph: VecGraph<usize> = VecGraph::new(id_to_node.len(), edges);

    let sccs: scc::Sccs<usize, SccId> = scc::Sccs::new(&vec_graph);

    let mut scc_edges = vec![];
    let mut scc_elems: IndexVec<SccId, _> = IndexVec::new();
    let mut scc_indices = FxHashMap::default();
    for scc in sccs.all_sccs() {
        for succ in sccs.successors(scc) {
            scc_edges.push((scc, *succ));
        }
        scc_elems.push(FxHashSet::default());
    }
    for (i, node) in id_to_node.into_iter().enumerate() {
        let scc = sccs.scc(i);
        scc_elems[scc].insert(node);
        scc_indices.insert(node, scc);
    }
    let graph = VecGraph::new(sccs.num_sccs(), scc_edges);

    Sccs {
        graph,
        scc_elems,
        indices: scc_indices,
    }
}

#[repr(transparent)]
pub struct VecBitSet<'a, T: Idx>(pub &'a IndexVec<T, ChunkedBitSet<T>>);

impl<T: Idx> DirectedGraph for VecBitSet<'_, T> {
    type Node = T;

    fn num_nodes(&self) -> usize {
        self.0.len()
    }
}

impl<T: Idx> Successors for VecBitSet<'_, T> {
    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        self.0[node].iter()
    }
}

pub fn sccs_from_vec_bit_set<T: Idx, const BR: bool>(
    graph: &IndexVec<T, ChunkedBitSet<T>>,
) -> Sccs<T, BR> {
    let sccs: scc::Sccs<T, SccId> = scc::Sccs::new(&VecBitSet(graph));

    let mut scc_edges = vec![];
    let mut scc_elems: IndexVec<SccId, _> = IndexVec::new();
    let mut scc_indices = FxHashMap::default();
    for scc in sccs.all_sccs() {
        for succ in sccs.successors(scc) {
            scc_edges.push((scc, *succ));
        }
        scc_elems.push(FxHashSet::default());
    }
    for i in graph.indices() {
        let scc = sccs.scc(i);
        scc_elems[scc].insert(i);
        scc_indices.insert(i, scc);
    }
    let graph = VecGraph::new(sccs.num_sccs(), scc_edges);

    Sccs {
        graph,
        scc_elems,
        indices: scc_indices,
    }
}

pub fn transitive_closure<T: Copy + Eq + std::hash::Hash>(
    graph: &FxHashMap<T, FxHashSet<T>>,
) -> FxHashMap<T, FxHashSet<T>> {
    for succs in graph.values() {
        for succ in succs {
            assert!(graph.contains_key(succ));
        }
    }
    let id_to_v: Vec<_> = graph.keys().copied().collect();
    let v_to_id: FxHashMap<_, _> = id_to_v
        .iter()
        .copied()
        .enumerate()
        .map(|(k, v)| (v, k))
        .collect();
    let len = id_to_v.len();

    let mut reachability = IndexVec::from_raw(vec![ChunkedBitSet::new_empty(len); len]);
    for (v, succs) in graph.iter() {
        for succ in succs {
            reachability[v_to_id[v]].insert(v_to_id[succ]);
        }
    }

    bitset_transitive_closure(&mut reachability);

    let mut new_graph = FxHashMap::default();
    for (i, reachability) in reachability.iter().enumerate() {
        let neighbors = reachability.iter().map(|to| id_to_v[to]).collect();
        new_graph.insert(id_to_v[i], neighbors);
    }
    new_graph
}

pub fn bitset_transitive_closure<T: Idx>(graph: &mut IndexVec<T, ChunkedBitSet<T>>) {
    for k in graph.indices() {
        for i in graph.indices() {
            for j in graph.indices() {
                if graph[i].contains(k) && graph[k].contains(j) {
                    graph[i].insert(j);
                }
            }
        }
    }
}

pub fn reflexive_transitive_closure<T: Copy + Eq + std::hash::Hash>(
    graph: &FxHashMap<T, FxHashSet<T>>,
) -> FxHashMap<T, FxHashSet<T>> {
    let mut new_graph = transitive_closure(graph);
    for v in graph.keys() {
        new_graph.get_mut(v).unwrap().insert(v.clone());
    }
    new_graph
}

pub fn reachable_vertices<T: Copy + Eq + std::hash::Hash>(
    graph: &FxHashMap<T, FxHashSet<T>>,
    v: T,
) -> FxHashSet<T> {
    let mut visited = FxHashSet::default();
    let mut worklist = VecDeque::new();
    worklist.push_back(v);
    while let Some(u) = worklist.pop_front() {
        if visited.insert(u)
            && let Some(succs) = graph.get(&u)
        {
            for succ in succs {
                worklist.push_back(*succ);
            }
        }
    }
    visited
}

pub fn bitset_reachable_vertices<T: Idx>(
    graph: &IndexVec<T, ChunkedBitSet<T>>,
    v: T,
) -> ChunkedBitSet<T> {
    let mut visited = ChunkedBitSet::new_empty(graph.len());
    let mut worklist = VecDeque::new();
    worklist.push_back(v);
    while let Some(u) = worklist.pop_front() {
        if visited.insert(u) {
            for w in graph[u].iter() {
                worklist.push_back(w);
            }
        }
    }
    visited
}

pub fn inverse<T: Copy + Eq + std::hash::Hash>(
    map: &FxHashMap<T, FxHashSet<T>>,
) -> FxHashMap<T, FxHashSet<T>> {
    let mut inv = FxHashMap::default();
    for node in map.keys() {
        inv.insert(*node, FxHashSet::default());
    }
    for (node, succs) in map {
        for succ in succs {
            inv.get_mut(succ).unwrap().insert(*node);
        }
    }
    inv
}

pub fn bitset_inverse<T: Idx>(
    graph: &IndexVec<T, ChunkedBitSet<T>>,
) -> IndexVec<T, ChunkedBitSet<T>> {
    let mut inv = IndexVec::from_raw(vec![ChunkedBitSet::new_empty(graph.len()); graph.len()]);
    for (node, succs) in graph.iter_enumerated() {
        for succ in succs.iter() {
            inv[succ].insert(node);
        }
    }
    inv
}
