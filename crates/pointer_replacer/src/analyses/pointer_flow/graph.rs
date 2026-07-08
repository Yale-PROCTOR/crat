use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::mir::{Local, Location};

use crate::analyses::pointer_flow::slots::{SlotIdx, SlotTable};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PfgNode {
    Slot(SlotIdx),
    Base(BaseId),
    CallReturn(Location),
    CastResult(Location),
}

impl PfgNode {
    pub(crate) fn as_slot(&self) -> Option<SlotIdx> {
        if let PfgNode::Slot(slot) = self {
            Some(*slot)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BaseId {
    Param {
        local: Local,
        slot: SlotIdx,
    },
    LocalArray {
        local: Local,
    },
    LocalScalar {
        local: Local,
    },
    RawBorrow {
        target: Option<SlotIdx>,
        location: Location,
    },
    HeapAlloc {
        location: Location,
    },
    OpaqueReturn {
        location: Location,
    },
    IntToPtr {
        location: Location,
    },
    Unknown {
        location: Location,
        reason: UnknownReason,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum UnknownReason {
    NullLike,
    ConstantPointer,
    UnsupportedProjection,
    UnsupportedMemoryLoad,
    UnsupportedCall,
}

#[derive(Clone, Debug, Default)]
pub struct PointerFlowGraph {
    pub nodes: FxHashSet<PfgNode>,
    pub edges: FxHashMap<PfgNode, FxHashSet<PfgNode>>,
    pub bases: FxHashSet<BaseId>,
}

#[derive(Clone, Debug, Default)]
pub struct ProvenanceResult {
    pub reachable_bases: FxHashMap<PfgNode, FxHashSet<BaseId>>,
}

impl PointerFlowGraph {
    pub(crate) fn add_node(&mut self, node: PfgNode) {
        self.nodes.insert(node);
    }

    pub(crate) fn add_base(&mut self, base: BaseId) {
        self.bases.insert(base.clone());
        self.add_node(PfgNode::Base(base));
    }

    pub(crate) fn add_edge(&mut self, src: PfgNode, dst: PfgNode) {
        self.nodes.insert(src.clone());
        self.nodes.insert(dst.clone());
        self.edges.entry(src).or_default().insert(dst);
    }

    pub(crate) fn add_base_edge(&mut self, base: BaseId, dst: PfgNode) {
        self.add_base(base.clone());
        self.add_edge(PfgNode::Base(base), dst);
    }

    pub(crate) fn add_bidirectional_edge(&mut self, a: PfgNode, b: PfgNode) {
        self.add_edge(a.clone(), b.clone());
        self.add_edge(b, a);
    }
}

impl ProvenanceResult {
    pub fn unique_base(&self, node: &PfgNode) -> Option<BaseId> {
        let bases = self.reachable_bases.get(node)?;
        if bases.len() == 1 {
            bases.iter().next().cloned()
        } else {
            None
        }
    }

    /// Like `unique_base`, but treats `Unknown(NullLike)` entries as transparent.
    /// Used in `select_rewrite_groups` to include variables that are null-initialized
    /// before being assigned from a real base (e.g. `prev = null_mut(); prev = raw;`).
    pub fn unique_non_null_base(&self, node: &PfgNode) -> Option<BaseId> {
        let bases = self.reachable_bases.get(node)?;
        let mut iter = bases.iter().filter(|b| {
            !matches!(
                b,
                BaseId::Unknown {
                    reason: UnknownReason::NullLike,
                    ..
                }
            )
        });
        let unique = iter.next()?.clone();
        iter.next().is_none().then_some(unique)
    }
}

/// Returns `(base_local, slot_offset_within_local)` for `DirectlyRewriteable` bases.
/// Returns `None` for `RawBorrow { target: None }` (no trackable local).
pub(crate) fn base_local_of_base(base: &BaseId, slot_table: &SlotTable) -> Option<(Local, usize)> {
    match base {
        BaseId::Param { local, slot } => {
            let offset = slot - slot_table.local_slots(*local).start;
            Some((*local, offset))
        }
        BaseId::LocalArray { local } | BaseId::LocalScalar { local } => Some((*local, 0)),
        BaseId::RawBorrow {
            target: Some(slot), ..
        } => {
            let root = slot_table.slot_infos[*slot].root;
            let offset = slot - slot_table.local_slots(root).start;
            Some((root, offset))
        }
        BaseId::RawBorrow { target: None, .. } => None,
        _ => None,
    }
}

pub(crate) fn solve_reachable_bases(graph: &PointerFlowGraph) -> ProvenanceResult {
    let mut reachable_bases: FxHashMap<PfgNode, FxHashSet<BaseId>> = FxHashMap::default();
    let mut worklist = VecDeque::new();

    for base in &graph.bases {
        let node = PfgNode::Base(base.clone());
        reachable_bases
            .entry(node.clone())
            .or_default()
            .insert(base.clone());
        worklist.push_back(node);
    }

    while let Some(src) = worklist.pop_front() {
        let Some(src_bases) = reachable_bases.get(&src).cloned() else {
            continue;
        };
        let Some(dsts) = graph.edges.get(&src) else {
            continue;
        };
        for dst in dsts {
            let dst_bases = reachable_bases.entry(dst.clone()).or_default();
            let before_len = dst_bases.len();
            dst_bases.extend(src_bases.iter().cloned());
            if dst_bases.len() != before_len {
                worklist.push_back(dst.clone());
            }
        }
    }

    ProvenanceResult { reachable_bases }
}
