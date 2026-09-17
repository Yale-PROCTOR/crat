use std::collections::{VecDeque, hash_map::Entry};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::HirId;
use rustc_middle::{
    mir::{Local, VarDebugInfoContents},
    ty,
};
use rustc_span::def_id::LocalDefId;

use super::{
    Analysis,
    decision::{PtrKind, SigDecisions},
};
use crate::{
    analyses::{
        borrow::StructFieldSlot,
        fn_ptr_groups::FnPtrGroups,
        offset_sign::sign::{CursorConstraints, CursorFieldNode, CursorLocalNode},
    },
    utils::rustc::RustProgram,
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

impl FinalCursorDecisionView {
    pub(crate) fn new<'tcx>(
        rust_program: &RustProgram<'tcx>,
        analysis: &Analysis,
        sig_decs: &SigDecisions,
        ptr_kinds: &FxHashMap<HirId, PtrKind>,
        forced_raw_bindings: &FxHashSet<HirId>,
        cursor_field_offset_alias_bindings: &FxHashSet<HirId>,
        fn_ptr_groups: &FnPtrGroups,
    ) -> Self {
        let mut view = Self::default();
        let tcx = rust_program.tcx;
        let mut binding_owners = FxHashMap::default();
        let mut functions = rust_program.functions.clone();
        functions.sort_unstable_by_key(|did| did.local_def_index);
        for did in functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            let hir_body = tcx.hir_body_owned_by(did);
            let mapping = utils::ir::map_thir_to_mir(did, false, tcx);
            let mut bindings = FxHashMap::<_, Vec<HirId>>::default();
            for (&binding, &local) in &mapping.binding_to_local {
                bindings.entry(local).or_default().push(binding);
            }
            for ids in bindings.values_mut() {
                ids.sort_unstable_by_key(|id| (id.owner.def_id.local_def_index, id.local_id));
            }
            let debug_locals: FxHashSet<_> = body
                .var_debug_info
                .iter()
                .filter_map(|info| match info.value {
                    VarDebugInfoContents::Place(place) => Some(place.local),
                    _ => None,
                })
                .collect();
            let signature = sig_decs.data.get(&did);
            if fn_ptr_groups.fn_to_group.contains_key(&did) {
                view.protections.push((
                    ProtectionSite::Function(did),
                    FreezeReason::FunctionPointerGroup,
                ));
            }
            if signature.is_some_and(|sig| sig.signature_locked) {
                view.protections
                    .push((ProtectionSite::Function(did), FreezeReason::SignatureLocked));
            }
            let original_kind = |local: Local| match body.local_decls[local].ty.kind() {
                ty::RawPtr(_, mutability) => Some(PtrKind::Raw(mutability.is_mut())),
                _ => None,
            };
            let effective_kind = |binding, local| {
                let kind = ptr_kinds
                    .get(&binding)
                    .copied()
                    .or_else(|| original_kind(local));
                if forced_raw_bindings.contains(&binding) {
                    original_kind(local).or_else(|| kind.map(|kind| PtrKind::Raw(kind.is_mut())))
                } else {
                    kind
                }
            };
            for (local, _) in body.local_decls.iter_enumerated() {
                let node = (did, local);
                let representative = analysis.source_var_groups.representative(did, local);
                let source = if local.as_usize() <= body.arg_count {
                    local
                } else {
                    representative.unwrap_or(local)
                };
                let ids = bindings.get(&source).map(Vec::as_slice).unwrap_or(&[]);
                let (owner, kind) = if source.as_usize() > 0 && source.as_usize() <= body.arg_count
                {
                    let index = source.as_usize() - 1;
                    // The pattern id only accounts for an unresolved input; it is
                    // never evidence of a unique binding or permission to demote.
                    let binding = if let [binding] = ids {
                        *binding
                    } else {
                        hir_body.params[index].pat.hir_id
                    };
                    let owner = CursorOwner::Param {
                        did,
                        index,
                        binding,
                    };
                    binding_owners.insert(hir_body.params[index].pat.hir_id, owner);
                    hir_body.params[index].pat.each_binding(|_, id, _, _| {
                        binding_owners.insert(id, owner);
                    });
                    for &id in ids {
                        binding_owners.insert(id, owner);
                    }
                    let kind = signature
                        .and_then(|sig| sig.input_decs.get(index).copied().flatten())
                        .or_else(|| original_kind(source));
                    let binding_kind = effective_kind(binding, source);
                    if ids.len() != 1 || kind != binding_kind {
                        view.protections.push((
                            ProtectionSite::Owner(owner),
                            FreezeReason::UnresolvedMapping,
                        ));
                        view.protections
                            .push((ProtectionSite::Node(node), FreezeReason::UnresolvedMapping));
                        view.flows.insert(node, CursorFlow::UnsupportedBoundary);
                        if ids.len() == 1 {
                            view.owner_members.entry(owner).or_default().push(node);
                        }
                        if let Some(kind @ PtrKind::SliceCursor(_)) = kind
                            .into_iter()
                            .chain(binding_kind)
                            .find(|kind| matches!(kind, PtrKind::SliceCursor(_)))
                        {
                            view.cursor_kinds.insert(owner, kind);
                        }
                        continue;
                    }
                    (owner, kind)
                } else if local.as_usize() == 0 {
                    let owner = CursorOwner::Return(did);
                    for &id in ids {
                        binding_owners.insert(id, owner);
                    }
                    (
                        owner,
                        signature
                            .and_then(|sig| sig.output_dec)
                            .or_else(|| original_kind(local)),
                    )
                } else if let [hir_id] = ids {
                    if let Some(&owner @ CursorOwner::Param { .. }) = binding_owners.get(hir_id) {
                        // A destructured/ref parameter binding may live outside
                        // the input's source group. Its identity is still Param,
                        // but this is not a complete mapping of that input.
                        view.flows.insert(node, CursorFlow::UnsupportedBoundary);
                        view.protections
                            .push((ProtectionSite::Node(node), FreezeReason::UnresolvedMapping));
                        view.protections.push((
                            ProtectionSite::Owner(owner),
                            FreezeReason::UnresolvedMapping,
                        ));
                        continue;
                    }
                    let owner = CursorOwner::Binding {
                        did,
                        hir_id: *hir_id,
                    };
                    binding_owners.insert(*hir_id, owner);
                    (owner, effective_kind(*hir_id, source))
                } else {
                    let unresolved = representative.is_some()
                        || debug_locals.contains(&local)
                        || !ids.is_empty();
                    view.flows.insert(
                        node,
                        if unresolved {
                            CursorFlow::UnsupportedBoundary
                        } else {
                            CursorFlow::Transparent
                        },
                    );
                    if unresolved {
                        view.protections
                            .push((ProtectionSite::Node(node), FreezeReason::UnresolvedMapping));
                    }
                    continue;
                };
                view.owner_members.entry(owner).or_default().push(node);
                view.flows.insert(
                    node,
                    match kind {
                        Some(kind @ PtrKind::SliceCursor(_)) => {
                            view.cursor_kinds.insert(owner, kind);
                            CursorFlow::Cursor(owner)
                        }
                        Some(PtrKind::Raw(_)) => CursorFlow::RawBarrier,
                        _ => CursorFlow::UnsupportedBoundary,
                    },
                );
            }
        }
        // Collector cursors can outlive their MIR mapping. Account for each
        // emitted owner, including those with no usable members.
        let mut bindings: Vec<_> = ptr_kinds.iter().collect();
        bindings.sort_unstable_by_key(|(id, _)| (id.owner.def_id.local_def_index, id.local_id));
        for (&hir_id, &kind) in bindings {
            if !matches!(kind, PtrKind::SliceCursor(_)) || forced_raw_bindings.contains(&hir_id) {
                continue;
            }
            let owner = *binding_owners
                .entry(hir_id)
                .or_insert(CursorOwner::Binding {
                    did: hir_id.owner.def_id,
                    hir_id,
                });
            view.cursor_kinds.entry(owner).or_insert(kind);
        }
        for &binding in cursor_field_offset_alias_bindings {
            if let Some(&owner) = binding_owners.get(&binding)
                && view.cursor_kinds.contains_key(&owner)
            {
                view.protections.push((
                    ProtectionSite::Owner(owner),
                    FreezeReason::CursorFieldOffsetAlias,
                ));
            }
        }
        for &owner in view.cursor_kinds.keys() {
            if matches!(owner, CursorOwner::Return(_)) {
                view.protections
                    .push((ProtectionSite::Owner(owner), FreezeReason::CursorReturn));
            }
            let members = view.owner_members.entry(owner).or_default();
            if members.is_empty() {
                view.protections.push((
                    ProtectionSite::Owner(owner),
                    FreezeReason::MissingMirMembers,
                ));
            }
            if !members.iter().any(|&(did, local)| {
                analysis
                    .offset_sign_result
                    .access_signs
                    .get(&did)
                    .is_some_and(|signs| signs.contains(local))
            }) {
                view.protections
                    .push((ProtectionSite::Owner(owner), FreezeReason::NotSignDerived));
            }
        }
        for members in view.owner_members.values_mut() {
            members.sort_unstable_by_key(|&node| node_key(node));
            members.dedup();
        }
        view.protections.sort_unstable_by_key(|&(site, reason)| {
            let key = match site {
                ProtectionSite::Node(node) => SafetyVertex::Local(node).key(),
                ProtectionSite::Owner(owner) => SafetyVertex::Owner(owner).key(),
                ProtectionSite::Function(did) => (3, 0, did.local_def_index.as_u32(), 0, 0, 0),
            };
            (key, reason as u8)
        });
        view.protections.dedup();
        view
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorDemotion {
    pub(crate) owner: CursorOwner,
    pub(crate) expected_old_kind: PtrKind,
    pub(crate) replacement_kind: PtrKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CursorDemotionValidationError {
    InvalidTransition(CursorOwner, PtrKind, PtrKind),
    DuplicateOwner(CursorOwner),
    MissingSignature(LocalDefId),
    SignatureMismatch(CursorOwner, Option<PtrKind>),
    BindingMismatch(CursorOwner, Option<PtrKind>),
    UnsupportedOwner(CursorOwner),
}

pub(crate) fn validate_cursor_demotions(
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    demotions: &[CursorDemotion],
) -> Result<(), CursorDemotionValidationError> {
    use CursorDemotionValidationError::*;

    let mut owners = FxHashSet::default();
    let mut bindings = FxHashSet::default();
    let mut inputs = FxHashSet::default();
    for demotion in demotions {
        let owner = demotion.owner;
        if !owners.insert(owner) {
            return Err(DuplicateOwner(owner));
        }
        if !matches!(
            (demotion.expected_old_kind, demotion.replacement_kind),
            (PtrKind::SliceCursor(old), PtrKind::Slice(new)) if old == new
        ) {
            return Err(InvalidTransition(
                owner,
                demotion.expected_old_kind,
                demotion.replacement_kind,
            ));
        }
        let (did, binding) = match owner {
            CursorOwner::Param { did, binding, .. } => (did, binding),
            CursorOwner::Binding { did, hir_id } => (did, hir_id),
            CursorOwner::Return(_) | CursorOwner::Field(_) => {
                return Err(UnsupportedOwner(owner));
            }
        };
        // Distinct owners must not alias either physical write target.
        if did != binding.owner.def_id || !bindings.insert(binding) {
            return Err(UnsupportedOwner(owner));
        }
        if let CursorOwner::Param { index, .. } = owner {
            if !inputs.insert((did, index)) {
                return Err(UnsupportedOwner(owner));
            }
            let signature = sig_decs.data.get(&did).ok_or(MissingSignature(did))?;
            let actual = signature.input_decs.get(index).copied().flatten();
            if actual != Some(demotion.expected_old_kind) {
                return Err(SignatureMismatch(owner, actual));
            }
        }
        let actual = ptr_kinds.get(&binding).copied();
        if actual != Some(demotion.expected_old_kind) {
            return Err(BindingMismatch(owner, actual));
        }
    }
    Ok(())
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

fn merged_owner_members(
    view: &FinalCursorDecisionView,
) -> FxHashMap<CursorOwner, Vec<CursorLocalNode>> {
    let mut owner_members = view.owner_members.clone();
    // A sparse member list must not discard ownership already known by a flow.
    for (&node, &flow) in &view.flows {
        if let CursorFlow::Cursor(owner) = flow {
            owner_members.entry(owner).or_default().push(node);
        }
    }
    for members in owner_members.values_mut() {
        members.sort_unstable_by_key(|&node| node_key(node));
        members.dedup();
    }
    owner_members
}

fn safety_graph(
    constraints: &CursorConstraints,
    view: &FinalCursorDecisionView,
    owner_members: &FxHashMap<CursorOwner, Vec<CursorLocalNode>>,
) -> SafetyGraph {
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
    for (&owner, members) in owner_members {
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
    let owner_members = merged_owner_members(view);
    let graph = safety_graph(constraints, view, &owner_members);
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
    // Equality witnesses do not schedule a member's flow for classification.
    // Only seeds and actual directed successors enter this set and the queue.
    let mut scheduled: FxHashSet<_> = seeds.iter().copied().collect();
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
                if let Entry::Vacant(entry) = required.entry(owner) {
                    entry.insert(node);
                    owner_members[&owner].clone()
                } else {
                    // Even after owner fan-out, every reached cursor node must
                    // forward its own directed demand.
                    vec![node]
                }
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
                if scheduled.insert(next) {
                    predecessor.entry(next).or_insert(Some(member));
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
    use crate::{
        analyses::{self, fn_ptr_groups::FnPtrGroups, mir_variable_grouping::SourceVarGroups},
        rewriter::{
            Analysis, collect_input,
            decision::{SigDecision, SigDecisions},
        },
        utils::rustc::RustProgram,
    };

    fn with_program(code: &str, test: impl FnOnce(RustProgram<'_>, Analysis) + Send) {
        utils::compilation::run_compiler_on_str(code, |tcx| {
            let input = collect_input(tcx);
            let aliases = FxHashMap::default();
            let mutability_result =
                analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
            let output_params = analyses::output_params::compute_output_params(
                &input,
                &mutability_result,
                &aliases,
            );
            let source_var_groups = SourceVarGroups::new(&input);
            let mutables = source_var_groups.postprocess_mut_res(&input, &mutability_result);
            let borrow_promotion_result =
                analyses::borrow::mutable_references_no_guarantee(&input, &mutables);
            let borrow_lifetime_flows = borrow_promotion_result.lifetime_flows.clone();
            let struct_copy_result =
                analyses::struct_copy::analyze(&input, &borrow_promotion_result.mutable_fields);
            let promoted_mut_ref_result = source_var_groups
                .postprocess_promoted_mut_refs(borrow_promotion_result.mutable_locals.clone());
            let promoted_shared_ref_result = source_var_groups
                .postprocess_promoted_mut_refs(borrow_promotion_result.shared_locals.clone());
            let fatness_result =
                analyses::type_qualifier::foster::fatness::fatness_analysis(&input);
            let mut offset_sign_result = analyses::offset_sign::sign::offset_sign_analysis(&input);
            offset_sign_result.access_signs =
                source_var_groups.postprocess_offset_signs(offset_sign_result.access_signs);
            let analysis = Analysis {
                borrow_promotion_result,
                borrow_lifetime_flows,
                promoted_mut_ref_result,
                promoted_shared_ref_result,
                mutability_result,
                fatness_result,
                aliases,
                output_params,
                ownership_schemes: None,
                offset_sign_result,
                nullity_result: Default::default(),
                struct_copy_result,
                source_var_groups,
            };
            test(input, analysis);
        })
        .unwrap();
    }

    fn signatures(
        did: LocalDefId,
        inputs: Vec<Option<PtrKind>>,
        output: Option<PtrKind>,
    ) -> SigDecisions {
        SigDecisions {
            data: FxHashMap::from_iter([(
                did,
                SigDecision {
                    input_lifetimes: vec![None; inputs.len()],
                    input_decs: inputs,
                    output_dec: output,
                    output_lifetime: None,
                    signature_locked: false,
                },
            )]),
        }
    }

    fn final_view(
        input: &RustProgram<'_>,
        analysis: &Analysis,
        sigs: &SigDecisions,
        kinds: &FxHashMap<HirId, PtrKind>,
    ) -> FinalCursorDecisionView {
        FinalCursorDecisionView::new(
            input,
            analysis,
            sigs,
            kinds,
            &FxHashSet::default(),
            &FxHashSet::default(),
            &FnPtrGroups::default(),
        )
    }

    #[test]
    fn final_view_maps_parameter_before_binding() {
        with_program(
            "pub unsafe fn f(mut p: *mut i32) { p = p.offset(-1); consume(p); } fn consume(_: *mut i32) {}",
            |input, analysis| {
                let did = input.functions[0];
                let binding = input.tcx.hir_body_owned_by(did).params[0].pat.hir_id;
                let owner = CursorOwner::Param {
                    did,
                    index: 0,
                    binding,
                };
                let kinds = FxHashMap::from_iter([(binding, PtrKind::SliceCursor(true))]);
                let sigs = signatures(did, vec![Some(PtrKind::SliceCursor(true))], None);
                let view = final_view(&input, &analysis, &sigs, &kinds);
                assert_eq!(view.cursor_kinds.len(), 1);
                assert_eq!(view.cursor_kinds[&owner], PtrKind::SliceCursor(true));
                let members = analysis
                    .source_var_groups
                    .members(did, Local::from_usize(1));
                assert!(
                    members.len() > 1,
                    "fixture must include grouped parameter temporaries"
                );
                for &local in members {
                    assert_eq!(view.flows[&(did, local)], CursorFlow::Cursor(owner));
                    assert!(view.owner_members[&owner].contains(&(did, local)));
                }
                assert!(
                    !view
                        .protections
                        .iter()
                        .any(|(site, _)| *site == ProtectionSite::Owner(owner))
                );
            },
        );
    }

    #[test]
    fn final_view_maps_return_and_freezes_it() {
        with_program(
            "pub unsafe fn f(p: *mut i32) -> *mut i32 { p.offset(-1) }",
            |input, analysis| {
                let did = input.functions[0];
                let sigs = signatures(did, vec![None], Some(PtrKind::SliceCursor(true)));
                let view = final_view(&input, &analysis, &sigs, &FxHashMap::default());
                let owner = CursorOwner::Return(did);
                assert_eq!(view.flows[&node(did, 0)], CursorFlow::Cursor(owner));
                assert_eq!(view.owner_members[&owner], vec![node(did, 0)]);
                assert!(
                    view.protections
                        .contains(&(ProtectionSite::Owner(owner), FreezeReason::CursorReturn))
                );
                assert_eq!(view.flows[&node(did, 1)], CursorFlow::RawBarrier);
            },
        );
    }

    #[test]
    fn final_view_maps_source_group_to_one_binding_owner() {
        with_program(
            "pub unsafe fn f(p: *mut i32) { let mut q = p; q = q.offset(-1); consume(q); } fn consume(_: *mut i32) {}",
            |input, analysis| {
                let did = input.functions[0];
                let map = utils::ir::map_thir_to_mir(did, false, input.tcx);
                let (&hir_id, &local) = map
                    .binding_to_local
                    .iter()
                    .find(|(id, _)| input.tcx.hir_name(**id).as_str() == "q")
                    .unwrap();
                let owner = CursorOwner::Binding { did, hir_id };
                let kinds = FxHashMap::from_iter([(hir_id, PtrKind::SliceCursor(true))]);
                let view = final_view(
                    &input,
                    &analysis,
                    &signatures(did, vec![None], None),
                    &kinds,
                );
                let members = analysis.source_var_groups.members(did, local);
                assert!(members.len() > 1);
                assert_eq!(view.cursor_kinds.len(), 1);
                for &local in members {
                    assert_eq!(view.flows[&(did, local)], CursorFlow::Cursor(owner));
                }
                let result = resolve_late_cursors(&CursorConstraints::default(), &view);
                assert_eq!(result.demotions().len(), 1);
                assert_eq!(result.demotions()[0].owner, owner);
            },
        );
    }

    #[test]
    fn final_view_distinguishes_transparent_and_source_visible_unmapped_locals() {
        with_program(
            "pub fn f(_: *mut i32, n: i32) -> i32 { n + 1 }",
            |input, analysis| {
                let did = input.functions[0];
                let view = final_view(
                    &input,
                    &analysis,
                    &signatures(did, vec![None], None),
                    &FxHashMap::default(),
                );
                assert_eq!(view.flows[&node(did, 1)], CursorFlow::UnsupportedBoundary);
                assert!(view.protections.contains(&(
                    ProtectionSite::Node(node(did, 1)),
                    FreezeReason::UnresolvedMapping
                )));
                assert!(
                    view.flows
                        .values()
                        .any(|&flow| flow == CursorFlow::Transparent)
                );
            },
        );
    }

    fn assert_protected(view: &FinalCursorDecisionView, owner: CursorOwner, reason: FreezeReason) {
        let result = resolve_late_cursors(&CursorConstraints::default(), view);
        let Some(CursorRetention::Protected { reasons }) = result.retention(owner) else {
            panic!(
                "expected protected owner {owner:?}, got {:?}",
                result.retention(owner)
            );
        };
        assert!(reasons.contains(&reason), "missing {reason:?}: {reasons:?}");
        assert!(!result.demotions().iter().any(|delta| delta.owner == owner));
    }

    #[test]
    fn final_view_freezes_signature_binding_disagreement() {
        with_program(
            "pub unsafe fn f(p: *mut i32) { let _ = p.offset(-1); }",
            |input, analysis| {
                let did = input.functions[0];
                let binding = input.tcx.hir_body_owned_by(did).params[0].pat.hir_id;
                let owner = CursorOwner::Param {
                    did,
                    index: 0,
                    binding,
                };
                for (signature, body) in [
                    (Some(PtrKind::SliceCursor(true)), Some(PtrKind::Raw(true))),
                    (
                        Some(PtrKind::SliceCursor(true)),
                        Some(PtrKind::SliceCursor(false)),
                    ),
                    (None, Some(PtrKind::SliceCursor(true))),
                    (Some(PtrKind::SliceCursor(true)), None),
                ] {
                    let kinds = body.map(|kind| (binding, kind)).into_iter().collect();
                    let view = final_view(
                        &input,
                        &analysis,
                        &signatures(did, vec![signature], None),
                        &kinds,
                    );
                    assert_eq!(view.cursor_kinds.len(), 1);
                    assert_eq!(view.flows[&node(did, 1)], CursorFlow::UnsupportedBoundary);
                    assert_protected(&view, owner, FreezeReason::UnresolvedMapping);
                }
            },
        );
    }

    #[test]
    fn final_view_freezes_forced_raw_disagreement() {
        with_program(
            "pub unsafe fn f(p: *mut i32) { let _ = p.offset(-1); }",
            |input, analysis| {
                let did = input.functions[0];
                let binding = input.tcx.hir_body_owned_by(did).params[0].pat.hir_id;
                let owner = CursorOwner::Param {
                    did,
                    index: 0,
                    binding,
                };
                let forced = FxHashSet::from_iter([binding]);
                let view = FinalCursorDecisionView::new(
                    &input,
                    &analysis,
                    &signatures(did, vec![Some(PtrKind::SliceCursor(true))], None),
                    &FxHashMap::default(),
                    &forced,
                    &FxHashSet::default(),
                    &FnPtrGroups::default(),
                );
                assert_eq!(view.flows[&node(did, 1)], CursorFlow::UnsupportedBoundary);
                assert_protected(&view, owner, FreezeReason::UnresolvedMapping);
            },
        );
    }

    #[test]
    fn final_view_freezes_missing_or_ambiguous_parameter_binding() {
        for code in [
            "pub fn f(_: *mut i32) {}",
            "pub fn f((p, q): (*mut i32, *mut i32)) { let _ = (p, q); }",
            "pub fn f(ref p: *mut i32) { let _ = p; }",
        ] {
            with_program(code, |input, analysis| {
                let did = input.functions[0];
                let binding = input.tcx.hir_body_owned_by(did).params[0].pat.hir_id;
                assert!(
                    !utils::ir::map_thir_to_mir(did, false, input.tcx)
                        .binding_to_local
                        .values()
                        .any(|&local| local == Local::from_usize(1))
                );
                let owner = CursorOwner::Param {
                    did,
                    index: 0,
                    binding,
                };
                let view = final_view(
                    &input,
                    &analysis,
                    &signatures(did, vec![Some(PtrKind::SliceCursor(true))], None),
                    &FxHashMap::from_iter([(binding, PtrKind::SliceCursor(true))]),
                );
                assert_eq!(
                    view.cursor_kinds.len(),
                    1,
                    "fallback input identity must not create a Binding candidate"
                );
                assert_eq!(view.flows[&node(did, 1)], CursorFlow::UnsupportedBoundary);
                for &local in utils::ir::map_thir_to_mir(did, false, input.tcx)
                    .binding_to_local
                    .values()
                {
                    assert!(!matches!(
                        view.flows[&(did, local)],
                        CursorFlow::Cursor(CursorOwner::Binding { .. })
                    ));
                }
                assert_protected(&view, owner, FreezeReason::UnresolvedMapping);
                assert_protected(&view, owner, FreezeReason::MissingMirMembers);
            });
        }
    }

    #[test]
    fn final_view_accounts_for_orphan_cursor() {
        with_program("pub fn f(p: *mut i32) {}", |mut input, analysis| {
            let did = input.functions[0];
            let hir_id = input.tcx.hir_body_owned_by(did).params[0].pat.hir_id;
            // Preserve a real binding decision after its function is absent
            // from the program being mapped. The constructor must account for it.
            input.functions.clear();
            let owner = CursorOwner::Binding { did, hir_id };
            let view = final_view(
                &input,
                &analysis,
                &signatures(did, vec![], None),
                &FxHashMap::from_iter([(hir_id, PtrKind::SliceCursor(false))]),
            );
            assert_eq!(view.cursor_kinds.len(), 1);
            assert!(view.owner_members[&owner].is_empty());
            assert_protected(&view, owner, FreezeReason::MissingMirMembers);
            assert_protected(&view, owner, FreezeReason::NotSignDerived);
            let view = FinalCursorDecisionView::new(
                &input,
                &analysis,
                &signatures(did, vec![], None),
                &FxHashMap::from_iter([(hir_id, PtrKind::SliceCursor(false))]),
                &FxHashSet::default(),
                &FxHashSet::from_iter([hir_id]),
                &FnPtrGroups::default(),
            );
            assert_protected(&view, owner, FreezeReason::CursorFieldOffsetAlias);
        });
    }

    #[test]
    fn final_view_protects_function_pointer_and_signature_lock() {
        with_program(
            "pub unsafe fn f(p: *mut i32) { let _ = p.offset(-1); }",
            |input, analysis| {
                let did = input.functions[0];
                let binding = input.tcx.hir_body_owned_by(did).params[0].pat.hir_id;
                let owner = CursorOwner::Param {
                    did,
                    index: 0,
                    binding,
                };
                let kinds = FxHashMap::from_iter([(binding, PtrKind::SliceCursor(true))]);
                for (grouped, locked) in [(true, false), (false, true), (true, true)] {
                    let mut sigs = signatures(did, vec![Some(PtrKind::SliceCursor(true))], None);
                    sigs.data.get_mut(&did).unwrap().signature_locked = locked;
                    let mut groups = FnPtrGroups::default();
                    if grouped {
                        groups.fn_to_group.insert(did, did);
                    }
                    let view = FinalCursorDecisionView::new(
                        &input,
                        &analysis,
                        &sigs,
                        &kinds,
                        &FxHashSet::default(),
                        &FxHashSet::default(),
                        &groups,
                    );
                    assert_eq!(view.flows[&node(did, 1)], CursorFlow::Cursor(owner));
                    if grouped {
                        assert_protected(&view, owner, FreezeReason::FunctionPointerGroup);
                    }
                    if locked {
                        assert_protected(&view, owner, FreezeReason::SignatureLocked);
                    }
                }
            },
        );
    }

    #[test]
    fn final_view_protects_cursor_field_alias() {
        with_program("pub fn f(p: *mut i32) {}", |input, analysis| {
            let did = input.functions[0];
            let binding = input.tcx.hir_body_owned_by(did).params[0].pat.hir_id;
            let owner = CursorOwner::Param {
                did,
                index: 0,
                binding,
            };
            let view = FinalCursorDecisionView::new(
                &input,
                &analysis,
                &signatures(did, vec![Some(PtrKind::SliceCursor(true))], None),
                &FxHashMap::from_iter([(binding, PtrKind::SliceCursor(true))]),
                &FxHashSet::default(),
                &FxHashSet::from_iter([binding]),
                &FnPtrGroups::default(),
            );
            assert_eq!(view.flows[&node(did, 1)], CursorFlow::Cursor(owner));
            assert_protected(&view, owner, FreezeReason::CursorFieldOffsetAlias);
            assert_protected(&view, owner, FreezeReason::NotSignDerived);
        });
    }

    #[test]
    fn final_view_does_not_model_c_exposure_as_a_freeze_reason() {
        for attributes in ["#[no_mangle]", "#[export_name = \"exported_f\"]"] {
            with_program(
                &format!(
                    "{attributes} pub unsafe extern \"C\" fn f(p: *mut i32) {{ let _ = p.offset(-1); }}"
                ),
                |input, analysis| {
                    let did = input.functions[0];
                    let binding = input.tcx.hir_body_owned_by(did).params[0].pat.hir_id;
                    let view = final_view(
                        &input,
                        &analysis,
                        &signatures(did, vec![Some(PtrKind::SliceCursor(true))], None),
                        &FxHashMap::from_iter([(binding, PtrKind::SliceCursor(true))]),
                    );
                    let result = resolve_late_cursors(&CursorConstraints::default(), &view);
                    assert_eq!(result.demotions().len(), 1);
                    assert_eq!(
                        result.demotions()[0].owner,
                        CursorOwner::Param {
                            did,
                            index: 0,
                            binding
                        }
                    );
                    assert!(result.retained.is_empty());
                },
            );
        }
    }

    #[test]
    fn final_view_classifies_all_final_pointer_kinds_and_unchanged_raw() {
        with_program("pub fn f(p: *const i32) {}", |input, analysis| {
            let did = input.functions[0];
            let binding = input.tcx.hir_body_owned_by(did).params[0].pat.hir_id;
            for kind in [
                None,
                Some(PtrKind::Raw(false)),
                Some(PtrKind::Ref(false)),
                Some(PtrKind::OptRef(false)),
                Some(PtrKind::Box),
                Some(PtrKind::OptBox),
                Some(PtrKind::BoxedSlice),
                Some(PtrKind::OptBoxedSlice),
                Some(PtrKind::Slice(false)),
            ] {
                let kinds = kind.map(|kind| (binding, kind)).into_iter().collect();
                let view = final_view(
                    &input,
                    &analysis,
                    &signatures(did, vec![kind], None),
                    &kinds,
                );
                let expected = if matches!(kind, None | Some(PtrKind::Raw(_))) {
                    CursorFlow::RawBarrier
                } else {
                    CursorFlow::UnsupportedBoundary
                };
                assert_eq!(view.flows[&node(did, 1)], expected, "{kind:?}");
                assert!(view.cursor_kinds.is_empty());
                assert!(view.protections.is_empty());
            }
            let view = FinalCursorDecisionView::new(
                &input,
                &analysis,
                &signatures(did, vec![None], None),
                &FxHashMap::default(),
                &FxHashSet::from_iter([binding]),
                &FxHashSet::default(),
                &FnPtrGroups::default(),
            );
            assert_eq!(view.flows[&node(did, 1)], CursorFlow::RawBarrier);
            assert!(view.protections.is_empty());
        });
    }

    #[test]
    fn final_view_accepts_sign_provenance_on_nonrepresentative_member() {
        with_program(
            "pub unsafe fn f(p: *mut i32) { consume(p); } fn consume(_: *mut i32) {}",
            |input, mut analysis| {
                let did = input.functions[0];
                let binding = input.tcx.hir_body_owned_by(did).params[0].pat.hir_id;
                let owner = CursorOwner::Param {
                    did,
                    index: 0,
                    binding,
                };
                let member = *analysis
                    .source_var_groups
                    .members(did, Local::from_usize(1))
                    .iter()
                    .find(|local| local.as_usize() != 1)
                    .unwrap();
                let body = input
                    .tcx
                    .mir_drops_elaborated_and_const_checked(did)
                    .borrow();
                let mut signs =
                    rustc_index::bit_set::DenseBitSet::new_empty(body.local_decls.len());
                signs.insert(member);
                analysis.offset_sign_result.access_signs.insert(did, signs);
                let view = final_view(
                    &input,
                    &analysis,
                    &signatures(did, vec![Some(PtrKind::SliceCursor(true))], None),
                    &FxHashMap::from_iter([(binding, PtrKind::SliceCursor(true))]),
                );
                let result = resolve_late_cursors(&CursorConstraints::default(), &view);
                assert_eq!(result.demotions().len(), 1);
                assert_eq!(result.demotions()[0].owner, owner);
            },
        );
    }

    #[test]
    fn final_view_maps_direct_binding_without_a_source_group() {
        with_program(
            "pub fn f(p: *mut i32) { let q = p; }",
            |input, mut analysis| {
                let did = input.functions[0];
                let mapping = utils::ir::map_thir_to_mir(did, false, input.tcx);
                let (&hir_id, &local) = mapping
                    .binding_to_local
                    .iter()
                    .find(|(id, _)| input.tcx.hir_name(**id).as_str() == "q")
                    .unwrap();
                analysis.source_var_groups = SourceVarGroups::new(&RustProgram {
                    tcx: input.tcx,
                    functions: vec![],
                    structs: vec![],
                });
                let owner = CursorOwner::Binding { did, hir_id };
                let view = final_view(
                    &input,
                    &analysis,
                    &signatures(did, vec![None], None),
                    &FxHashMap::from_iter([(hir_id, PtrKind::SliceCursor(true))]),
                );
                assert_eq!(view.flows[&(did, local)], CursorFlow::Cursor(owner));
                assert_eq!(view.owner_members[&owner], vec![(did, local)]);
                assert_protected(&view, owner, FreezeReason::NotSignDerived);
            },
        );
    }

    #[test]
    fn final_view_leaves_ownerless_raw_temporaries_transparent() {
        with_program(
            "pub fn f() { let _ = core::ptr::null_mut::<i32>(); }",
            |input, analysis| {
                let did = input.functions[0];
                let view = final_view(
                    &input,
                    &analysis,
                    &signatures(did, vec![], None),
                    &FxHashMap::default(),
                );
                let body = input
                    .tcx
                    .mir_drops_elaborated_and_const_checked(did)
                    .borrow();
                let raw_locals: Vec<_> = body
                    .local_decls
                    .iter_enumerated()
                    .filter(|(_, decl)| decl.ty.is_raw_ptr())
                    .map(|(local, _)| local)
                    .collect();
                assert!(!raw_locals.is_empty());
                for local in raw_locals {
                    assert_eq!(view.flows[&(did, local)], CursorFlow::Transparent);
                }
            },
        );
    }

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
    fn final_view_does_not_freeze_final_raw_field_alias() {
        with_program(
            "pub unsafe fn f(p: *mut i32, q: *mut i32) { let _ = q.offset(-1); }",
            |input, analysis| {
                let did = input.functions[0];
                let params = input.tcx.hir_body_owned_by(did).params;
                let (p, q) = (params[0].pat.hir_id, params[1].pat.hir_id);
                let view = FinalCursorDecisionView::new(
                    &input,
                    &analysis,
                    &signatures(did, vec![None, Some(PtrKind::SliceCursor(true))], None),
                    &FxHashMap::from_iter([
                        (p, PtrKind::SliceCursor(true)),
                        (q, PtrKind::SliceCursor(true)),
                    ]),
                    &FxHashSet::from_iter([p]),
                    &FxHashSet::from_iter([p]),
                    &FnPtrGroups::default(),
                );
                assert_eq!(view.flows[&node(did, 1)], CursorFlow::RawBarrier);
                assert_eq!(view.cursor_kinds.len(), 1);
                let mut constraints = CursorConstraints::default();
                edge(&mut constraints, node(did, 2), node(did, 1));
                let result = resolve_late_cursors(&constraints, &view);
                assert_eq!(result.demotions().len(), 1);
                assert_eq!(
                    result.demotions()[0].owner,
                    CursorOwner::Param {
                        did,
                        index: 1,
                        binding: q
                    }
                );
            },
        );
    }

    #[test]
    fn final_view_data_ignores_input_insertion_order() {
        with_program(
            "pub fn f(p: *mut i32) {} pub fn g(q: *const i32) {}",
            |mut input, analysis| {
                let mut kinds = FxHashMap::default();
                let mut sigs = SigDecisions {
                    data: FxHashMap::default(),
                };
                for &did in &input.functions {
                    let binding = input.tcx.hir_body_owned_by(did).params[0].pat.hir_id;
                    let kind =
                        PtrKind::SliceCursor(input.tcx.item_name(did.to_def_id()).as_str() == "f");
                    kinds.insert(binding, kind);
                    sigs.data
                        .extend(signatures(did, vec![Some(kind)], None).data);
                }
                let first = final_view(&input, &analysis, &sigs, &kinds);
                input.functions.reverse();
                let mut entries: Vec<_> = kinds.into_iter().collect();
                entries.reverse();
                let second = final_view(&input, &analysis, &sigs, &entries.into_iter().collect());
                assert_eq!(first.flows, second.flows);
                assert_eq!(first.owner_members, second.owner_members);
                assert_eq!(first.cursor_kinds, second.cursor_kinds);
                assert_eq!(first.protections, second.protections);
            },
        );
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
            let graph = safety_graph(&constraints, &view, &merged_owner_members(&view));
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

    fn check_directed_boundary_after_fanout(flow: Option<CursorFlow>) {
        with_ids(move |did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let a = candidate(&mut view, did, ids[0], 1, true);
            let c = candidate(&mut view, did, ids[3], 4, true);
            view.owner_members.get_mut(&a).unwrap().push(node(did, 2));
            if let Some(flow) = flow {
                view.flows.insert(node(did, 2), flow);
            }
            view.flows.insert(node(did, 3), CursorFlow::Transparent);
            constraints.local_seeds.extend([node(did, 1), node(did, 3)]);
            edge(&mut constraints, node(did, 3), node(did, 2));
            edge(&mut constraints, node(did, 4), node(did, 2));
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.retention(a),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 1)]
                })
            );
            if flow == Some(CursorFlow::RawBarrier) {
                assert_eq!(
                    resolution.reached_raw_barriers,
                    FxHashSet::from_iter([node(did, 2)])
                );
                assert_eq!(resolution.stats().reached_raw_barriers, 1);
                assert_eq!(
                    resolution
                        .demotions()
                        .iter()
                        .map(|delta| delta.owner)
                        .collect::<Vec<_>>(),
                    vec![c]
                );
            } else {
                assert_eq!(
                    resolution.retention(c),
                    Some(&CursorRetention::Poisoned {
                        boundary: node(did, 2)
                    })
                );
                assert!(resolution.demotions().is_empty());
            }
        });
    }

    #[test]
    fn directed_missing_flow_after_fanout_poisons_component() {
        check_directed_boundary_after_fanout(None);
    }

    #[test]
    fn directed_unsupported_flow_after_fanout_poisons_component() {
        check_directed_boundary_after_fanout(Some(CursorFlow::UnsupportedBoundary));
    }

    #[test]
    fn directed_raw_flow_after_fanout_records_barrier() {
        check_directed_boundary_after_fanout(Some(CursorFlow::RawBarrier));
    }

    #[test]
    fn sparse_membership_propagates_owner_protection() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let a = candidate(&mut view, did, ids[0], 1, true);
            let c = candidate(&mut view, did, ids[3], 4, true);
            view.flows.insert(node(did, 2), CursorFlow::Cursor(a));
            view.protections
                .push((ProtectionSite::Owner(a), FreezeReason::MissingMirMembers));
            edge(&mut constraints, node(did, 4), node(did, 2));
            let resolution = resolve_late_cursors(&constraints, &view);
            for owner in [a, c] {
                assert_eq!(
                    resolution.retention(owner),
                    Some(&CursorRetention::Protected {
                        reasons: vec![FreezeReason::MissingMirMembers]
                    })
                );
            }
            assert!(resolution.demotions().is_empty());
        });
    }

    #[test]
    fn sparse_membership_seed_propagates_after_owner_is_required() {
        with_ids(|did, ids| {
            let mut constraints = CursorConstraints::default();
            let mut view = FinalCursorDecisionView::default();
            let a = candidate(&mut view, did, ids[0], 1, true);
            let c = candidate(&mut view, did, ids[3], 4, true);
            view.flows.insert(node(did, 2), CursorFlow::Cursor(a));
            constraints.local_seeds.extend([node(did, 1), node(did, 2)]);
            edge(&mut constraints, node(did, 2), node(did, 4));
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.retention(a),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 1)]
                })
            );
            assert_eq!(
                resolution.retention(c),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 2), node(did, 4)]
                })
            );
            assert!(resolution.demotions().is_empty());

            // Known flow membership must also participate in owner fan-out
            // when the omitted member has no independent seed.
            constraints.local_seeds.remove(&node(did, 2));
            let resolution = resolve_late_cursors(&constraints, &view);
            assert_eq!(
                resolution.retention(c),
                Some(&CursorRetention::Required {
                    witness: vec![node(did, 1), node(did, 2), node(did, 4)],
                })
            );
            assert!(resolution.demotions().is_empty());
        });
    }
}
