use std::collections::{VecDeque, hash_map::Entry};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::HirId;
use rustc_span::def_id::LocalDefId;

use super::decision::PtrKind;
use crate::analyses::{
    borrow::StructFieldSlot,
    offset_sign::sign::{CursorConstraints, CursorFieldNode, CursorLocalNode},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CursorOwner {
    Param {
        did: LocalDefId,
        index: usize,
        binding: HirId,
    },
    Binding {
        did: LocalDefId,
        hir_id: HirId,
    },
    Return(LocalDefId),
    Field(StructFieldSlot),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CursorFlow {
    Transparent,
    Cursor(CursorOwner),
    RawBarrier,
    UnsupportedBoundary,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FreezeReason {
    FieldConnected,
    FunctionPointerGroup,
    SignatureLocked,
    CursorReturn,
    UnmodeledCall,
    CursorFieldOffsetAlias,
    NotSignDerived,
    MissingMirMembers,
    UnresolvedMapping,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ProtectionSite {
    Node(CursorLocalNode),
    Owner(CursorOwner),
    Function(LocalDefId),
}

#[derive(Default)]
pub(crate) struct FinalCursorDecisionView {
    flows: FxHashMap<CursorLocalNode, CursorFlow>,
    owner_members: FxHashMap<CursorOwner, Vec<CursorLocalNode>>,
    cursor_kinds: FxHashMap<CursorOwner, PtrKind>,
    protections: Vec<(ProtectionSite, FreezeReason)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorDemotion {
    pub(crate) owner: CursorOwner,
    pub(crate) expected_old_kind: PtrKind,
    pub(crate) replacement_kind: PtrKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CursorRetention {
    Required { witness: Vec<CursorLocalNode> },
    Protected { reasons: Vec<FreezeReason> },
    Poisoned { boundary: CursorLocalNode },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorResolutionStats {
    pub(crate) candidates: usize,
    pub(crate) required: usize,
    pub(crate) protected: usize,
    pub(crate) poisoned: usize,
    pub(crate) demoted: usize,
    pub(crate) reached_raw_barriers: usize,
    pub(crate) protected_by_reason: Vec<(FreezeReason, usize)>,
}

pub(crate) struct CursorResolution {
    demotions: Vec<CursorDemotion>,
    retained: FxHashMap<CursorOwner, CursorRetention>,
    reached_raw_barriers: FxHashSet<CursorLocalNode>,
}

// This order is also the reporting order; it must not depend on hash iteration.
const FREEZE_REASONS: [FreezeReason; 9] = [
    FreezeReason::FieldConnected,
    FreezeReason::FunctionPointerGroup,
    FreezeReason::SignatureLocked,
    FreezeReason::CursorReturn,
    FreezeReason::UnmodeledCall,
    FreezeReason::CursorFieldOffsetAlias,
    FreezeReason::NotSignDerived,
    FreezeReason::MissingMirMembers,
    FreezeReason::UnresolvedMapping,
];

impl CursorResolution {
    pub(crate) fn demotions(&self) -> &[CursorDemotion] {
        &self.demotions
    }

    pub(crate) fn retention(&self, owner: CursorOwner) -> Option<&CursorRetention> {
        self.retained.get(&owner)
    }

    pub(crate) fn stats(&self) -> CursorResolutionStats {
        let mut stats = CursorResolutionStats {
            candidates: self.demotions.len() + self.retained.len(),
            required: 0,
            protected: 0,
            poisoned: 0,
            demoted: self.demotions.len(),
            reached_raw_barriers: self.reached_raw_barriers.len(),
            protected_by_reason: Vec::new(),
        };
        let mut counts = FxHashMap::<FreezeReason, usize>::default();
        for retention in self.retained.values() {
            match retention {
                CursorRetention::Required { .. } => stats.required += 1,
                CursorRetention::Protected { reasons } => {
                    stats.protected += 1;
                    for &reason in reasons {
                        *counts.entry(reason).or_default() += 1;
                    }
                }
                CursorRetention::Poisoned { .. } => stats.poisoned += 1,
            }
        }
        stats.protected_by_reason = FREEZE_REASONS
            .into_iter()
            .filter_map(|reason| counts.get(&reason).map(|&count| (reason, count)))
            .collect();
        stats
    }
}

fn node_key((did, local): CursorLocalNode) -> (u32, usize) {
    (did.local_def_index.as_u32(), local.as_usize())
}

fn owner_key(owner: CursorOwner) -> (u8, u32, usize, u32, u32) {
    match owner {
        CursorOwner::Param {
            did,
            index,
            binding,
        } => (
            0,
            did.local_def_index.as_u32(),
            index,
            binding.owner.def_id.local_def_index.as_u32(),
            binding.local_id.as_u32(),
        ),
        CursorOwner::Binding { did, hir_id } => (
            1,
            did.local_def_index.as_u32(),
            0,
            hir_id.owner.def_id.local_def_index.as_u32(),
            hir_id.local_id.as_u32(),
        ),
        CursorOwner::Return(did) => (2, did.local_def_index.as_u32(), 0, 0, 0),
        CursorOwner::Field(slot) => (
            3,
            slot.struct_did.local_def_index.as_u32(),
            slot.field_index,
            0,
            0,
        ),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum SafetyVertex {
    Local(CursorLocalNode),
    Owner(CursorOwner),
    Field(StructFieldSlot),
}

impl SafetyVertex {
    fn key(self) -> (u8, u8, u32, usize, u32, u32) {
        match self {
            Self::Local(node) => {
                let (did, local) = node_key(node);
                (0, 0, did, local, 0, 0)
            }
            Self::Owner(owner) => {
                let (variant, did, index, hir_owner, hir_local) = owner_key(owner);
                (1, variant, did, index, hir_owner, hir_local)
            }
            Self::Field(slot) => (
                2,
                0,
                slot.struct_did.local_def_index.as_u32(),
                slot.field_index,
                0,
                0,
            ),
        }
    }

    fn function(self) -> Option<LocalDefId> {
        match self {
            Self::Local((did, _))
            | Self::Owner(
                CursorOwner::Param { did, .. }
                | CursorOwner::Binding { did, .. }
                | CursorOwner::Return(did),
            ) => Some(did),
            Self::Field(_) | Self::Owner(CursorOwner::Field(_)) => None,
        }
    }
}

impl From<CursorFieldNode> for SafetyVertex {
    fn from(node: CursorFieldNode) -> Self {
        match node {
            CursorFieldNode::Local(did, local) => Self::Local((did, local)),
            CursorFieldNode::Field(slot) => Self::Field(slot),
        }
    }
}

type SafetyGraph = FxHashMap<SafetyVertex, FxHashSet<SafetyVertex>>;

fn connect(graph: &mut SafetyGraph, from: SafetyVertex, to: SafetyVertex) {
    graph.entry(from).or_default().insert(to);
    graph.entry(to).or_default().insert(from);
}

fn safety_graph(constraints: &CursorConstraints, view: &FinalCursorDecisionView) -> SafetyGraph {
    let mut graph = SafetyGraph::default();
    for edges in [&constraints.local_edges, &constraints.return_edges] {
        for (&from, successors) in edges {
            graph.entry(SafetyVertex::Local(from)).or_default();
            for &to in successors {
                connect(
                    &mut graph,
                    SafetyVertex::Local(from),
                    SafetyVertex::Local(to),
                );
            }
        }
    }
    for (&from, successors) in &constraints.field_edges {
        graph.entry(from.into()).or_default();
        for &to in successors {
            connect(&mut graph, from.into(), to.into());
        }
    }
    for &node in constraints
        .local_seeds
        .iter()
        .chain(&constraints.unmodeled_call_nodes)
        .chain(view.flows.keys())
    {
        graph.entry(SafetyVertex::Local(node)).or_default();
    }
    for &node in &constraints.field_seeds {
        graph.entry(node.into()).or_default();
    }
    for (&owner, members) in &view.owner_members {
        graph.entry(SafetyVertex::Owner(owner)).or_default();
        for &member in members {
            connect(
                &mut graph,
                SafetyVertex::Owner(owner),
                SafetyVertex::Local(member),
            );
        }
    }
    for &owner in view.cursor_kinds.keys() {
        graph.entry(SafetyVertex::Owner(owner)).or_default();
        if let CursorOwner::Field(slot) = owner {
            connect(
                &mut graph,
                SafetyVertex::Owner(owner),
                SafetyVertex::Field(slot),
            );
        }
    }
    for &(site, _) in &view.protections {
        match site {
            ProtectionSite::Node(node) => {
                graph.entry(SafetyVertex::Local(node)).or_default();
            }
            ProtectionSite::Owner(owner) => {
                graph.entry(SafetyVertex::Owner(owner)).or_default();
            }
            ProtectionSite::Function(_) => {}
        }
    }
    graph
}

fn successors(constraints: &CursorConstraints, node: CursorLocalNode) -> Vec<CursorLocalNode> {
    let mut successors: Vec<_> = [&constraints.local_edges, &constraints.return_edges]
        .into_iter()
        .flat_map(|edges| edges.get(&node).into_iter().flatten().copied())
        .collect();
    successors.sort_unstable_by_key(|&node| node_key(node));
    successors.dedup();
    successors
}

pub(crate) fn resolve_late_cursors(
    constraints: &CursorConstraints,
    view: &FinalCursorDecisionView,
) -> CursorResolution {
    let graph = safety_graph(constraints, view);
    let mut vertices: Vec<_> = graph.keys().copied().collect();
    vertices.sort_unstable_by_key(|v| v.key());
    let mut component = FxHashMap::default();
    let mut reasons = Vec::<FxHashSet<FreezeReason>>::new();
    for &root in &vertices {
        if component.contains_key(&root) {
            continue;
        }
        let index = reasons.len();
        reasons.push(FxHashSet::default());
        component.insert(root, index);
        let mut queue = VecDeque::from([root]);
        while let Some(vertex) = queue.pop_front() {
            if matches!(vertex, SafetyVertex::Field(_)) {
                reasons[index].insert(FreezeReason::FieldConnected);
            }
            let mut neighbors: Vec<_> = graph[&vertex].iter().copied().collect();
            neighbors.sort_unstable_by_key(|v| v.key());
            for next in neighbors {
                if let Entry::Vacant(entry) = component.entry(next) {
                    entry.insert(index);
                    queue.push_back(next);
                }
            }
        }
    }
    for &node in &constraints.unmodeled_call_nodes {
        reasons[component[&SafetyVertex::Local(node)]].insert(FreezeReason::UnmodeledCall);
    }
    for &(site, reason) in &view.protections {
        match site {
            ProtectionSite::Node(node) => {
                reasons[component[&SafetyVertex::Local(node)]].insert(reason);
            }
            ProtectionSite::Owner(owner) => {
                reasons[component[&SafetyVertex::Owner(owner)]].insert(reason);
            }
            ProtectionSite::Function(did) => {
                for &vertex in &vertices {
                    if vertex.function() == Some(did) {
                        reasons[component[&vertex]].insert(reason);
                    }
                }
            }
        }
    }

    let mut seeds: Vec<_> = constraints.local_seeds.iter().copied().collect();
    seeds.sort_unstable_by_key(|&node| node_key(node));
    let mut predecessor: FxHashMap<_, Option<CursorLocalNode>> =
        seeds.iter().map(|&n| (n, None)).collect();
    let mut queue = VecDeque::from(seeds);
    let mut required = FxHashMap::default();
    let mut poisoned = FxHashMap::<usize, CursorLocalNode>::default();
    let mut reached_raw_barriers = FxHashSet::default();
    while let Some(node) = queue.pop_front() {
        let members = match view
            .flows
            .get(&node)
            .copied()
            .unwrap_or(CursorFlow::UnsupportedBoundary)
        {
            CursorFlow::Transparent => vec![node],
            CursorFlow::Cursor(owner) => {
                if required.contains_key(&owner) {
                    continue;
                }
                required.insert(owner, node);
                let mut members = view.owner_members.get(&owner).cloned().unwrap_or_default();
                members.push(node);
                members.sort_unstable_by_key(|&n| node_key(n));
                members.dedup();
                members
            }
            CursorFlow::RawBarrier => {
                reached_raw_barriers.insert(node);
                continue;
            }
            CursorFlow::UnsupportedBoundary => {
                let index = component[&SafetyVertex::Local(node)];
                poisoned
                    .entry(index)
                    .and_modify(|boundary| {
                        if node_key(node) < node_key(*boundary) {
                            *boundary = node;
                        }
                    })
                    .or_insert(node);
                continue;
            }
        };
        for member in members {
            // A witness can cross the equality link between two MIR members
            // of one source owner, followed by a directed supplier edge.
            predecessor.entry(member).or_insert(Some(node));
            for next in successors(constraints, member) {
                if let Entry::Vacant(entry) = predecessor.entry(next) {
                    entry.insert(Some(member));
                    queue.push_back(next);
                }
            }
        }
    }

    let mut resolution = CursorResolution {
        demotions: Vec::new(),
        retained: FxHashMap::default(),
        reached_raw_barriers,
    };
    let mut owners: Vec<_> = view.cursor_kinds.keys().copied().collect();
    owners.sort_unstable_by_key(|&owner| owner_key(owner));
    for owner in owners {
        let index = component[&SafetyVertex::Owner(owner)];
        let retention = if let Some(&node) = required.get(&owner) {
            let mut witness = vec![node];
            let mut current = node;
            while let Some(previous) = predecessor[&current] {
                witness.push(previous);
                current = previous;
            }
            witness.reverse();
            CursorRetention::Required { witness }
        } else if !reasons[index].is_empty() {
            CursorRetention::Protected {
                reasons: FREEZE_REASONS
                    .into_iter()
                    .filter(|r| reasons[index].contains(r))
                    .collect(),
            }
        } else if let Some(&boundary) = poisoned.get(&index) {
            CursorRetention::Poisoned { boundary }
        } else {
            let expected_old_kind = view.cursor_kinds[&owner];
            let PtrKind::SliceCursor(mutable) = expected_old_kind else {
                unreachable!("cursor candidates must have a cursor representation");
            };
            resolution.demotions.push(CursorDemotion {
                owner,
                expected_old_kind,
                replacement_kind: PtrKind::Slice(mutable),
            });
            continue;
        };
        resolution.retained.insert(owner, retention);
    }
    resolution
}

#[cfg(test)]
mod tests {
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::mir::Local;

    use super::*;

    fn with_ids(test: impl FnOnce(LocalDefId, Vec<HirId>) + Send) {
        utils::compilation::run_compiler_on_str(
            "fn fixture(a: i32, b: i32, c: i32, d: i32, e: i32, f: i32, g: i32, h: i32) {}",
            |tcx| {
                let did = tcx
                    .hir_crate(())
                    .owners
                    .iter()
                    .find_map(|owner| {
                        let OwnerNode::Item(item) = owner.as_owner()?.node() else {
                            return None;
                        };
                        matches!(item.kind, ItemKind::Fn { .. }).then_some(item.owner_id.def_id)
                    })
                    .unwrap();
                let bindings = tcx
                    .hir_body_owned_by(did)
                    .params
                    .iter()
                    .map(|p| p.pat.hir_id)
                    .collect();
                test(did, bindings);
            },
        )
        .unwrap();
    }

    fn node(did: LocalDefId, index: usize) -> CursorLocalNode {
        (did, Local::from_usize(index))
    }

    fn candidate(
        view: &mut FinalCursorDecisionView,
        did: LocalDefId,
        binding: HirId,
        index: usize,
        mutable: bool,
    ) -> CursorOwner {
        let owner = CursorOwner::Param {
            did,
            index: index - 1,
            binding,
        };
        let member = node(did, index);
        view.cursor_kinds
            .insert(owner, PtrKind::SliceCursor(mutable));
        view.owner_members.insert(owner, vec![member]);
        view.flows.insert(member, CursorFlow::Cursor(owner));
        owner
    }

    fn edge(constraints: &mut CursorConstraints, from: CursorLocalNode, to: CursorLocalNode) {
        constraints.local_edges.entry(from).or_default().insert(to);
    }

    #[test]
    fn raw_seed_stops_and_demotes_unreached_cursor() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let owner = candidate(&mut view, did, ids[1], 2, true);
            constraints.local_seeds.insert(node(did, 1));
            edge(&mut constraints, node(did, 1), node(did, 2));
            view.flows.insert(node(did, 1), CursorFlow::RawBarrier);
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.demotions,
                vec![CursorDemotion {
                    owner,
                    expected_old_kind: PtrKind::SliceCursor(true),
                    replacement_kind: PtrKind::Slice(true),
                }]
            );
            assert_eq!(
                resolution.reached_raw_barriers,
                FxHashSet::from_iter([node(did, 1)])
            );
            assert!(resolution.retained.is_empty());
        });
    }

    #[test]
    fn cursor_seed_retains_cursor_suppliers() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let a = candidate(&mut view, did, ids[0], 1, true);
            let b = candidate(&mut view, did, ids[1], 2, false);
            constraints.local_seeds.insert(node(did, 1));
            edge(&mut constraints, node(did, 1), node(did, 2));
            let resolution = resolve_late_cursors(&constraints, &view);
            assert!(resolution.demotions.is_empty());
            assert_eq!(
                resolution.retained[&a],
                CursorRetention::Required {
                    witness: vec![node(did, 1)]
                }
            );
            assert_eq!(
                resolution.retained[&b],
                CursorRetention::Required {
                    witness: vec![node(did, 1), node(did, 2)]
                }
            );
        });
    }

    #[test]
    fn cursor_then_raw_stops_after_required_cursor() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let a = candidate(&mut view, did, ids[0], 1, true);
            let b = candidate(&mut view, did, ids[2], 3, true);
            constraints.local_seeds.insert(node(did, 1));
            edge(&mut constraints, node(did, 1), node(did, 2));
            edge(&mut constraints, node(did, 2), node(did, 3));
            view.flows.insert(node(did, 2), CursorFlow::RawBarrier);
            let resolution = resolve_late_cursors(&constraints, &view);
            assert!(matches!(
                resolution.retained[&a],
                CursorRetention::Required { .. }
            ));
            assert_eq!(resolution.demotions[0].owner, b);
            assert_eq!(resolution.demotions.len(), 1);
            assert_eq!(resolution.reached_raw_barriers.len(), 1);
        });
    }

    #[test]
    fn transparent_temporary_forwards_demand() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let owner = candidate(&mut view, did, ids[1], 2, true);
            constraints.local_seeds.insert(node(did, 1));
            constraints
                .return_edges
                .entry(node(did, 1))
                .or_default()
                .insert(node(did, 2));
            view.flows.insert(node(did, 1), CursorFlow::Transparent);
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.retained[&owner],
                CursorRetention::Required {
                    witness: vec![node(did, 1), node(did, 2)]
                }
            );
            assert!(resolution.demotions.is_empty());
        });
    }

    #[test]
    fn shared_and_mutable_demotions_preserve_mutability() {
        with_ids(|did, ids| {
            let mut view = FinalCursorDecisionView::default();
            let a = candidate(&mut view, did, ids[0], 1, false);
            let b = candidate(&mut view, did, ids[1], 2, true);
            let resolution = resolve_late_cursors(&CursorConstraints::default(), &view);
            assert_eq!(
                resolution.demotions,
                vec![
                    CursorDemotion {
                        owner: a,
                        expected_old_kind: PtrKind::SliceCursor(false),
                        replacement_kind: PtrKind::Slice(false)
                    },
                    CursorDemotion {
                        owner: b,
                        expected_old_kind: PtrKind::SliceCursor(true),
                        replacement_kind: PtrKind::Slice(true)
                    },
                ]
            );
        });
    }

    #[test]
    fn owner_fanout_enqueues_every_member_successor() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let a = candidate(&mut view, did, ids[0], 1, true);
            let b = candidate(&mut view, did, ids[2], 3, true);
            let c = candidate(&mut view, did, ids[3], 4, false);
            view.owner_members.get_mut(&a).unwrap().push(node(did, 2));
            view.flows.insert(node(did, 2), CursorFlow::Cursor(a));
            constraints.local_seeds.insert(node(did, 1));
            edge(&mut constraints, node(did, 1), node(did, 3));
            constraints
                .return_edges
                .entry(node(did, 2))
                .or_default()
                .insert(node(did, 4));
            let resolution = resolve_late_cursors(&constraints, &view);
            assert!(resolution.demotions().is_empty());
            assert_eq!(
                resolution.retention(b),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 1), node(did, 3)]
                })
            );
            assert_eq!(
                resolution.retention(c),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 1), node(did, 2), node(did, 4)]
                })
            );
        });
    }

    #[test]
    fn grouped_temporary_seed_stops_at_raw_parameter() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let raw_owner = CursorOwner::Param {
                did,
                index: 0,
                binding: ids[0],
            };
            view.owner_members
                .insert(raw_owner, vec![node(did, 1), node(did, 2)]);
            view.flows.insert(node(did, 1), CursorFlow::RawBarrier);
            view.flows.insert(node(did, 2), CursorFlow::Transparent);
            let cursor = candidate(&mut view, did, ids[2], 3, true);
            constraints.local_seeds.insert(node(did, 2));
            edge(&mut constraints, node(did, 2), node(did, 1));
            edge(&mut constraints, node(did, 1), node(did, 3));
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(resolution.demotions()[0].owner, cursor);
            assert_eq!(resolution.stats().demoted, 1);
            assert_eq!(
                resolution.reached_raw_barriers,
                FxHashSet::from_iter([node(did, 1)])
            );
        });
    }

    #[test]
    fn mixed_raw_cursor_cycle_does_not_cross_raw_barrier() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let a = candidate(&mut view, did, ids[0], 1, true);
            let b = candidate(&mut view, did, ids[2], 3, true);
            constraints.local_seeds.insert(node(did, 1));
            for (from, to) in [(1, 2), (2, 3), (3, 1)] {
                edge(&mut constraints, node(did, from), node(did, to));
            }
            view.flows.insert(node(did, 2), CursorFlow::RawBarrier);
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.retention(a),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 1)]
                })
            );
            assert_eq!(resolution.demotions()[0].owner, b);
            assert_eq!(resolution.stats().required, 1);
            assert_eq!(resolution.stats().demoted, 1);
        });
    }

    #[test]
    fn active_sibling_branch_retains_cursor_after_raw_branch_stops() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let cursor = candidate(&mut view, did, ids[3], 4, true);
            constraints.local_seeds.insert(node(did, 1));
            for (from, to) in [(1, 2), (1, 3), (2, 4), (3, 4)] {
                edge(&mut constraints, node(did, from), node(did, to));
            }
            view.flows.insert(node(did, 1), CursorFlow::Transparent);
            view.flows.insert(node(did, 2), CursorFlow::RawBarrier);
            view.flows.insert(node(did, 3), CursorFlow::Transparent);
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.retention(cursor),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 1), node(did, 3), node(did, 4)]
                })
            );
            assert_eq!(resolution.stats().reached_raw_barriers, 1);
            assert!(resolution.demotions().is_empty());
        });
    }

    #[test]
    fn field_protected_component_freezes_grouped_owner() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let a = candidate(&mut view, did, ids[0], 1, true);
            let b = candidate(&mut view, did, ids[2], 3, true);
            view.owner_members.get_mut(&a).unwrap().push(node(did, 2));
            view.flows.insert(node(did, 2), CursorFlow::Cursor(a));
            edge(&mut constraints, node(did, 1), node(did, 3));
            let field = CursorFieldNode::Field(StructFieldSlot {
                struct_did: did,
                field_index: 0,
            });
            constraints
                .field_edges
                .entry(field)
                .or_default()
                .insert(CursorFieldNode::Local(did, Local::from_usize(2)));
            constraints.field_seeds.insert(field);
            let resolution = resolve_late_cursors(&constraints, &view);
            for owner in [a, b] {
                assert_eq!(
                    resolution.retention(owner),
                    Some(&CursorRetention::Protected {
                        reasons: vec![FreezeReason::FieldConnected]
                    })
                );
            }
            assert_eq!(
                resolution.stats().required,
                0,
                "field seeds must not seed demand"
            );
            assert!(resolution.demotions().is_empty());
        });
    }

    #[test]
    fn frozen_cursor_still_propagates() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let a = candidate(&mut view, did, ids[0], 1, true);
            let b = candidate(&mut view, did, ids[1], 2, true);
            view.protections
                .push((ProtectionSite::Owner(a), FreezeReason::SignatureLocked));
            constraints.local_seeds.insert(node(did, 1));
            edge(&mut constraints, node(did, 1), node(did, 2));
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.retention(b),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 1), node(did, 2)]
                })
            );
            assert_eq!(resolution.stats().required, 2);
            assert_eq!(
                resolution.stats().protected,
                0,
                "required has precedence over protected"
            );
        });
    }

    #[test]
    fn protected_component_reasons_freeze_entire_component() {
        with_ids(|did, ids| {
            for reason in [
                FreezeReason::FieldConnected,
                FreezeReason::FunctionPointerGroup,
                FreezeReason::SignatureLocked,
                FreezeReason::CursorReturn,
                FreezeReason::UnmodeledCall,
                FreezeReason::CursorFieldOffsetAlias,
                FreezeReason::NotSignDerived,
                FreezeReason::MissingMirMembers,
                FreezeReason::UnresolvedMapping,
            ] {
                for site_index in 0..3 {
                    let mut constraints = CursorConstraints::default();
                    let mut view = FinalCursorDecisionView::default();
                    let a = candidate(&mut view, did, ids[0], 1, true);
                    let b = candidate(&mut view, did, ids[2], 3, true);
                    // Mix all three graph sources, with demand edges pointing
                    // away from the protected end to require undirected closure.
                    edge(&mut constraints, node(did, 1), node(did, 2));
                    constraints
                        .return_edges
                        .entry(node(did, 2))
                        .or_default()
                        .insert(node(did, 4));
                    constraints
                        .field_edges
                        .entry(CursorFieldNode::Local(did, Local::from_usize(4)))
                        .or_default()
                        .insert(CursorFieldNode::Local(did, Local::from_usize(3)));
                    let site = match site_index {
                        0 => ProtectionSite::Node(node(did, 3)),
                        1 => ProtectionSite::Owner(b),
                        _ => ProtectionSite::Function(did),
                    };
                    view.protections.push((site, reason));
                    // Duplicate input facts must not duplicate output reasons.
                    view.protections.push((site, reason));
                    let resolution = resolve_late_cursors(&constraints, &view);
                    for owner in [a, b] {
                        assert_eq!(
                            resolution.retention(owner),
                            Some(&CursorRetention::Protected {
                                reasons: vec![reason]
                            }),
                            "{site:?} {reason:?}"
                        );
                    }
                    assert!(resolution.demotions().is_empty());
                }
            }
        });
    }

    fn check_poisoned_boundary(explicit: bool) {
        with_ids(move |did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let owner = candidate(&mut view, did, ids[1], 2, true);
            constraints.local_seeds.insert(node(did, 1));
            // The candidate points into the boundary; demand must not reverse
            // this edge, but poisoning must cross it in the safety graph.
            edge(&mut constraints, node(did, 2), node(did, 1));
            if explicit {
                view.flows
                    .insert(node(did, 1), CursorFlow::UnsupportedBoundary);
            }
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.retention(owner),
                Some(&CursorRetention::Poisoned {
                    boundary: node(did, 1)
                })
            );
            assert!(resolution.demotions().is_empty());
        });
    }

    #[test]
    fn unsupported_boundary_poisons_component() {
        check_poisoned_boundary(true);
    }

    #[test]
    fn unresolved_boundary_poisons_component() {
        check_poisoned_boundary(false);
    }

    #[test]
    fn resolver_accounts_for_every_cursor_owner() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let param = candidate(&mut view, did, ids[0], 1, true);
            let binding = CursorOwner::Binding {
                did,
                hir_id: ids[1],
            };
            let returned = CursorOwner::Return(did);
            let field = CursorOwner::Field(StructFieldSlot {
                struct_did: did,
                field_index: 0,
            });
            for owner in [binding, returned, field] {
                view.cursor_kinds.insert(owner, PtrKind::SliceCursor(false));
            }
            view.protections.push((
                ProtectionSite::Owner(binding),
                FreezeReason::MissingMirMembers,
            ));
            view.protections
                .push((ProtectionSite::Owner(returned), FreezeReason::CursorReturn));
            // Isolated seeds, empty adjacency keys, field seeds and boundaries
            // must all have components, despite having no graph edge.
            constraints.local_seeds.extend([node(did, 2), node(did, 3)]);
            view.flows.insert(node(did, 2), CursorFlow::RawBarrier);
            constraints.local_edges.entry(node(did, 4)).or_default();
            constraints.return_edges.entry(node(did, 5)).or_default();
            constraints
                .field_edges
                .entry(CursorFieldNode::Local(did, Local::from_usize(6)))
                .or_default();
            constraints
                .field_seeds
                .insert(CursorFieldNode::Local(did, Local::from_usize(7)));
            constraints.unmodeled_call_nodes.insert(node(did, 1));
            constraints.unmodeled_call_nodes.insert(node(did, 8));
            let isolated_field_seed = CursorFieldNode::Field(StructFieldSlot {
                struct_did: did,
                field_index: 1,
            });
            let isolated_field_key = CursorFieldNode::Field(StructFieldSlot {
                struct_did: did,
                field_index: 2,
            });
            constraints.field_seeds.insert(isolated_field_seed);
            constraints
                .field_edges
                .entry(isolated_field_key)
                .or_default();
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.retention(param),
                Some(&CursorRetention::Protected {
                    reasons: vec![FreezeReason::UnmodeledCall]
                })
            );
            assert_eq!(
                resolution.retention(binding),
                Some(&CursorRetention::Protected {
                    reasons: vec![FreezeReason::MissingMirMembers]
                })
            );
            assert_eq!(
                resolution.retention(returned),
                Some(&CursorRetention::Protected {
                    reasons: vec![FreezeReason::CursorReturn]
                })
            );
            assert_eq!(
                resolution.retention(field),
                Some(&CursorRetention::Protected {
                    reasons: vec![FreezeReason::FieldConnected]
                })
            );
            assert_eq!(resolution.stats().candidates, 4);
            assert_eq!(resolution.stats().protected, 4);
            assert_eq!(resolution.stats().reached_raw_barriers, 1);
            assert!(resolution.demotions().is_empty());
            let graph = safety_graph(&constraints, &view);
            for i in 1..=8 {
                assert!(graph.contains_key(&SafetyVertex::Local(node(did, i))));
            }
            assert!(graph.contains_key(&isolated_field_seed.into()));
            assert!(graph.contains_key(&isolated_field_key.into()));
        });
    }

    #[test]
    fn resolution_stats_count_every_outcome_by_reason() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let owners: Vec<_> = (1..=6)
                .map(|i| candidate(&mut view, did, ids[i - 1], i, i % 2 == 0))
                .collect();
            constraints
                .local_seeds
                .extend([node(did, 1), node(did, 2), node(did, 8)]);
            edge(&mut constraints, node(did, 1), node(did, 7));
            edge(&mut constraints, node(did, 2), node(did, 3));
            edge(&mut constraints, node(did, 8), node(did, 4));
            view.flows
                .insert(node(did, 2), CursorFlow::UnsupportedBoundary);
            view.flows.insert(node(did, 7), CursorFlow::RawBarrier);
            view.protections.extend([
                (
                    ProtectionSite::Owner(owners[0]),
                    FreezeReason::NotSignDerived,
                ),
                (
                    ProtectionSite::Owner(owners[1]),
                    FreezeReason::UnresolvedMapping,
                ),
                (
                    ProtectionSite::Node(node(did, 3)),
                    FreezeReason::SignatureLocked,
                ),
                (
                    ProtectionSite::Node(node(did, 3)),
                    FreezeReason::SignatureLocked,
                ),
            ]);
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.stats(),
                CursorResolutionStats {
                    candidates: 6,
                    required: 1,
                    protected: 2,
                    poisoned: 1,
                    demoted: 2,
                    reached_raw_barriers: 1,
                    protected_by_reason: vec![
                        (FreezeReason::SignatureLocked, 2),
                        (FreezeReason::UnresolvedMapping, 2)
                    ],
                }
            );
            assert!(matches!(
                resolution.retention(owners[0]),
                Some(CursorRetention::Required { .. })
            ));
            assert!(matches!(
                resolution.retention(owners[1]),
                Some(CursorRetention::Protected { .. })
            ));
            assert_eq!(
                resolution.retention(owners[3]),
                Some(&CursorRetention::Poisoned {
                    boundary: node(did, 8)
                })
            );
            assert_eq!(
                resolution
                    .demotions()
                    .iter()
                    .map(|d| d.owner)
                    .collect::<Vec<_>>(),
                owners[4..]
            );
        });
    }

    #[test]
    fn results_and_witnesses_ignore_hash_insertion_order() {
        with_ids(|did, ids| {
            let build = |reverse: bool| {
                let mut constraints = CursorConstraints::default();
                let mut view = FinalCursorDecisionView::default();
                let mut indexes: Vec<_> = (1..=8).collect();
                if reverse {
                    indexes.reverse();
                }
                for i in indexes {
                    candidate(&mut view, did, ids[i - 1], i, i % 2 == 0);
                }
                let owners: Vec<_> = (1..=8)
                    .map(|i| CursorOwner::Param {
                        did,
                        index: i - 1,
                        binding: ids[i - 1],
                    })
                    .collect();
                for i in [9, 10, 15] {
                    view.flows.insert(node(did, i), CursorFlow::Transparent);
                }
                view.flows
                    .insert(node(did, 11), CursorFlow::Cursor(owners[1]));
                view.owner_members.insert(
                    owners[1],
                    if reverse {
                        vec![node(did, 11), node(did, 2)]
                    } else {
                        vec![node(did, 2), node(did, 11)]
                    },
                );
                view.flows.insert(node(did, 14), CursorFlow::RawBarrier);
                let mut edges = vec![
                    (9, 1),
                    (9, 2),
                    (10, 1),
                    (10, 2),
                    (1, 2),
                    (2, 9),
                    (11, 14),
                    (14, 5),
                    (12, 3),
                    (13, 3),
                    (15, 12),
                ];
                // Boundary 13 is reached before 12; the stable minimum is 12.
                let mut seeds = vec![node(did, 9), node(did, 10), node(did, 13), node(did, 15)];
                let mut protections = vec![
                    (
                        ProtectionSite::Owner(owners[3]),
                        FreezeReason::SignatureLocked,
                    ),
                    (
                        ProtectionSite::Owner(owners[3]),
                        FreezeReason::FunctionPointerGroup,
                    ),
                ];
                let field = CursorFieldNode::Field(StructFieldSlot {
                    struct_did: did,
                    field_index: 0,
                });
                constraints
                    .field_edges
                    .entry(field)
                    .or_default()
                    .insert(CursorFieldNode::Local(did, Local::from_usize(7)));
                constraints.field_seeds.insert(field);
                if reverse {
                    edges.reverse();
                    seeds.reverse();
                    protections.reverse();
                }
                for (from, to) in edges {
                    edge(&mut constraints, node(did, from), node(did, to));
                }
                constraints.local_seeds.extend(seeds);
                view.protections = protections;
                (constraints, view, owners)
            };
            let (constraints_a, view_a, owners) = build(false);
            let (constraints_b, view_b, _) = build(true);
            let first = resolve_late_cursors(&constraints_a, &view_a);
            let second = resolve_late_cursors(&constraints_b, &view_b);
            assert_eq!(first.demotions(), second.demotions());
            assert_eq!(first.retained, second.retained);
            assert_eq!(first.reached_raw_barriers, second.reached_raw_barriers);
            assert_eq!(first.stats(), second.stats());
            assert_eq!(
                first.retention(owners[0]),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 9), node(did, 1)]
                })
            );
            assert_eq!(
                first.retention(owners[1]),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 9), node(did, 2)]
                })
            );
            assert_eq!(
                first.retention(owners[2]),
                Some(&CursorRetention::Poisoned {
                    boundary: node(did, 12)
                })
            );
            assert_eq!(
                first.retention(owners[3]),
                Some(&CursorRetention::Protected {
                    reasons: vec![
                        FreezeReason::FunctionPointerGroup,
                        FreezeReason::SignatureLocked
                    ]
                })
            );
            assert_eq!(
                first
                    .demotions()
                    .iter()
                    .map(|d| d.owner)
                    .collect::<Vec<_>>(),
                vec![owners[4], owners[5], owners[7]]
            );
            assert_eq!(
                first.stats(),
                CursorResolutionStats {
                    candidates: 8,
                    required: 2,
                    protected: 2,
                    poisoned: 1,
                    demoted: 3,
                    reached_raw_barriers: 1,
                    protected_by_reason: vec![
                        (FreezeReason::FieldConnected, 1),
                        (FreezeReason::FunctionPointerGroup, 1),
                        (FreezeReason::SignatureLocked, 1)
                    ],
                }
            );
        });
    }

    #[test]
    fn resolver_is_idempotent_after_delta() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let demoted = candidate(&mut view, did, ids[1], 2, true);
            let required = candidate(&mut view, did, ids[2], 3, false);
            constraints.local_seeds.extend([node(did, 1), node(did, 3)]);
            view.flows.insert(node(did, 1), CursorFlow::RawBarrier);
            edge(&mut constraints, node(did, 1), node(did, 2));
            let first = resolve_late_cursors(&constraints, &view);
            assert_eq!(first.demotions().len(), 1);
            assert_eq!(first.demotions()[0].owner, demoted);
            for delta in first.demotions() {
                view.cursor_kinds.remove(&delta.owner);
                for &member in &view.owner_members[&delta.owner] {
                    view.flows.insert(member, CursorFlow::UnsupportedBoundary);
                }
            }
            let second = resolve_late_cursors(&constraints, &view);
            assert!(second.demotions().is_empty());
            assert_eq!(second.retention(required), first.retention(required));
            assert_eq!(second.stats().candidates, 1);
            assert_eq!(second.reached_raw_barriers, first.reached_raw_barriers);
        });
    }

    #[test]
    fn function_protection_covers_disconnected_owners_and_cross_function_edges() {
        utils::compilation::run_compiler_on_str(
            "fn f(a: i32, b: i32) {} fn g(a: i32, b: i32) {}",
            |tcx| {
                let mut functions: Vec<_> = tcx
                    .hir_crate(())
                    .owners
                    .iter()
                    .filter_map(|owner| {
                        let OwnerNode::Item(item) = owner.as_owner()?.node() else {
                            return None;
                        };
                        matches!(item.kind, ItemKind::Fn { .. }).then_some(item.owner_id.def_id)
                    })
                    .collect();
                functions.sort_unstable_by_key(|did| did.local_def_index.as_u32());
                let (f, g) = (functions[0], functions[1]);
                let mut constraints = CursorConstraints::default();
                let mut view = FinalCursorDecisionView::default();
                let a = candidate(
                    &mut view,
                    f,
                    tcx.hir_body_owned_by(f).params[0].pat.hir_id,
                    1,
                    true,
                );
                let b = candidate(
                    &mut view,
                    g,
                    tcx.hir_body_owned_by(g).params[0].pat.hir_id,
                    1,
                    true,
                );
                let c = candidate(
                    &mut view,
                    g,
                    tcx.hir_body_owned_by(g).params[1].pat.hir_id,
                    2,
                    true,
                );
                let orphan = CursorOwner::Return(f);
                view.cursor_kinds
                    .insert(orphan, PtrKind::SliceCursor(false));
                view.protections
                    .push((ProtectionSite::Function(f), FreezeReason::SignatureLocked));
                edge(&mut constraints, node(g, 1), node(f, 1));
                let resolution = resolve_late_cursors(&constraints, &view);
                for owner in [a, b, orphan] {
                    assert_eq!(
                        resolution.retention(owner),
                        Some(&CursorRetention::Protected {
                            reasons: vec![FreezeReason::SignatureLocked]
                        })
                    );
                }
                assert_eq!(
                    resolution
                        .demotions()
                        .iter()
                        .map(|d| d.owner)
                        .collect::<Vec<_>>(),
                    vec![c]
                );
                assert_eq!(resolution.stats().protected, 3);
            },
        )
        .unwrap();
    }

    #[test]
    fn required_cursor_precedes_poisoned_component() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let a = candidate(&mut view, did, ids[0], 1, true);
            let b = candidate(&mut view, did, ids[1], 2, true);
            constraints.local_seeds.insert(node(did, 1));
            edge(&mut constraints, node(did, 1), node(did, 3));
            edge(&mut constraints, node(did, 3), node(did, 2));
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.retention(a),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 1)]
                })
            );
            assert_eq!(
                resolution.retention(b),
                Some(&CursorRetention::Poisoned {
                    boundary: node(did, 3)
                })
            );
            assert!(resolution.demotions().is_empty());
        });
    }
}
