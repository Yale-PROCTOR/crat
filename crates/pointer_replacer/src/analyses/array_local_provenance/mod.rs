//! MIR raw-array local provenance graph to find base pointers.
//!
//! This analysis is intentionally not location-sensitive yet: each MIR local is
//! represented by one graph node for the whole body. This may merge separate
//! definitions of the same local and conservatively reject rewriteable regions.

use std::{collections::VecDeque, fmt::Write as _, ops::Range};

use points_to::andersen;
use rustc_abi::FieldIdx;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::{
    mir::{
        self, BasicBlock, Body, CastKind, Local, Location, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    ty::{self, Ty, TyCtxt},
};
use rustc_mir_dataflow::Analysis;
use rustc_span::{def_id::DefId, source_map::Spanned};

use crate::{
    analyses::{
        liveness::MaybeLiveLocals,
        mir::CallGraphPostOrder,
        mir_variable_grouping::SourceVarGroups,
        type_qualifier::foster::mutability::{Mutability as PtrMut, MutabilityResult},
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PfgNode {
    Slot(SlotIdx),
    Base(BaseId),
    CallReturn(Location),
    CastResult(Location),
}

impl PfgNode {
    fn as_slot(&self) -> Option<SlotIdx> {
        if let PfgNode::Slot(slot) = self {
            Some(*slot)
        } else {
            None
        }
    }
}

pub type SlotIdx = usize;

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BaseAdmissibility {
    DirectlyRewriteable,
    RewriteableWithOwnershipTransform,
    TrackOnly,
    Reject,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BaseClassification {
    pub base: BaseId,
    pub admissibility: BaseAdmissibility,
    pub reason: String,
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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct FunctionSummary {
    completeness: SummaryCompleteness,
    return_flows: Vec<SummaryFlow>,
    arg_write_flows: Vec<ArgWriteFlow>,
    unknown_return_slots: Vec<Vec<SlotPathElem>>,
    unknown_arg_writes: Vec<ArgWriteTarget>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum SummaryCompleteness {
    Complete,
    #[default]
    Incomplete,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct SummaryFlow {
    dst_return_path: Vec<SlotPathElem>,
    src: SummarySource,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ArgWriteFlow {
    dst_arg_index: usize,
    dst_path: Vec<SlotPathElem>,
    src: SummarySource,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ArgWriteTarget {
    arg_index: usize,
    path: Vec<SlotPathElem>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SummarySource {
    ParamSlot {
        arg_index: usize,
        path: Vec<SlotPathElem>,
    },
    Unknown(UnknownReason),
    OpaqueReturn,
    HeapAlloc,
}

#[derive(Clone, Debug)]
pub struct ArrayLocalProvenance {
    pub slot_table: SlotTable,
    #[allow(dead_code)]
    pub graph: PointerFlowGraph,
    pub provenance: ProvenanceResult,
    pub base_classifications: FxHashMap<BaseId, BaseClassification>,
    pub(crate) call_effects: FxHashMap<Location, CallEffects>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct InstantiatedArgWrite {
    pub(crate) dst_arg_index: usize,
    pub(crate) destination: SlotIdx,
    pub(crate) sources: Vec<PfgNode>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct InstantiatedUnknownArgWrite {
    pub(crate) dst_arg_index: usize,
    pub(crate) destination: SlotIdx,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct CallEffects {
    pub(crate) complete: bool,
    pub(crate) writes: Vec<InstantiatedArgWrite>,
    pub(crate) unknown_writes: Vec<InstantiatedUnknownArgWrite>,
}

pub struct RewriteGroup {
    #[allow(dead_code)]
    pub base: BaseId,
    /// MIR local that holds the base pointer.
    pub base_local: Local,
    /// offset of the base slot within `base_local`'s qualifier slice.
    pub base_slot_offset: usize,
    /// all `SlotIdx`s across any local whose unique reachable base is `base`.
    pub members: Vec<SlotIdx>,
    /// true when the base slot is written via direct (trackable) assignments only
    /// while members are live; the rewriter must use index-tracking for this group.
    pub index_tracked: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PreservedBaseCall {
    pub(crate) location: Location,
    pub(crate) affected_arguments: Vec<usize>,
    pub(crate) writes_base_binding: bool,
}

pub(crate) enum RewriteGroupStatus {
    Ready(RewriteGroup),
    #[allow(dead_code)]
    PreservedAcrossCalls {
        group: RewriteGroup,
        calls: Vec<PreservedBaseCall>,
    },
}

#[derive(Clone, Debug, Default)]
pub struct SlotTable {
    local_slots: Vec<Range<SlotIdx>>,
    pub slot_infos: Vec<SlotInfo>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotInfo {
    pub root: Local,
    pub path: Vec<SlotPathElem>,
    pub depth: usize,
    pub qualifier_key: Option<QualifierKey>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QualifierKey {
    Local {
        offset: usize,
    },
    StructField {
        def_id: LocalDefId,
        field: FieldIdx,
        offset: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SlotPathElem {
    Pointee,
    Field(FieldIdx),
    Element,
}

// pre-computed assignment right-hand sides used by `array_source_for_local`
enum AssignRhs<'tcx> {
    // rvalue is Ref/RawPtr of this place; if place.local is an array type or
    // has an array projection, the local is a direct array source
    ArrayBorrow(Place<'tcx>),
    // rvalue is Use/Cast/CopyForDeref of this local; follow it recursively
    Follow(Local),
}

impl PointerFlowGraph {
    fn add_node(&mut self, node: PfgNode) {
        self.nodes.insert(node);
    }

    fn add_base(&mut self, base: BaseId) {
        self.bases.insert(base.clone());
        self.add_node(PfgNode::Base(base));
    }

    fn add_edge(&mut self, src: PfgNode, dst: PfgNode) {
        self.nodes.insert(src.clone());
        self.nodes.insert(dst.clone());
        self.edges.entry(src).or_default().insert(dst);
    }

    fn add_base_edge(&mut self, base: BaseId, dst: PfgNode) {
        self.add_base(base.clone());
        self.add_edge(PfgNode::Base(base), dst);
    }

    fn add_bidirectional_edge(&mut self, a: PfgNode, b: PfgNode) {
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

impl FunctionSummary {
    fn is_complete(&self) -> bool {
        self.completeness == SummaryCompleteness::Complete
    }

    fn normalize(&mut self) {
        self.return_flows.sort();
        self.return_flows.dedup();
        self.arg_write_flows.sort();
        self.arg_write_flows.dedup();
        self.unknown_return_slots.sort();
        self.unknown_return_slots.dedup();
        self.unknown_arg_writes.sort();
        self.unknown_arg_writes.dedup();
    }
}

#[allow(dead_code)]
impl ArrayLocalProvenance {
    pub fn unique_base(&self, node: &PfgNode) -> Option<BaseId> {
        self.provenance.unique_base(node)
    }

    pub fn unique_base_of_local(&self, local: Local) -> Option<BaseId> {
        let slot = self.slot_table.local_head_slot(local)?;
        self.unique_base(&PfgNode::Slot(slot))
    }

    pub fn admissibility_of_base(&self, base: &BaseId) -> BaseAdmissibility {
        self.base_classifications
            .get(base)
            .map(|classification| classification.admissibility.clone())
            .unwrap_or(BaseAdmissibility::Reject)
    }

    pub fn is_potential_rewrite_base(&self, base: &BaseId) -> bool {
        matches!(
            self.admissibility_of_base(base),
            BaseAdmissibility::DirectlyRewriteable
                | BaseAdmissibility::RewriteableWithOwnershipTransform
        )
    }

    pub fn debug_body(&self, tcx: TyCtxt<'_>, def_id: LocalDefId, body: &Body<'_>) -> String {
        let mut out = String::new();
        let _ = writeln!(
            out,
            "array local provenance for {}",
            tcx.def_path_str(def_id.to_def_id())
        );

        for (local, decl) in body.local_decls.iter_enumerated() {
            let Some(slot) = self.slot_table.local_head_slot(local) else {
                continue;
            };
            let node = PfgNode::Slot(slot);
            let bases = self
                .provenance
                .reachable_bases
                .get(&node)
                .cloned()
                .unwrap_or_default();
            let unique = self.unique_base(&node);
            let _ = write!(out, "  {local:?}: ty = {:?}, bases = {:?}", decl.ty, bases);
            match unique {
                Some(base) => {
                    let classification = self.base_classifications.get(&base);
                    let _ = write!(out, ", unique = yes");
                    if let Some(classification) = classification {
                        let _ = write!(
                            out,
                            ", admissibility = {:?}, reason = {}",
                            classification.admissibility, classification.reason
                        );
                    }
                }
                None => {
                    let _ = write!(out, ", unique = no");
                }
            }
            let _ = writeln!(out);
        }

        out
    }
}

pub fn array_local_provenance_analysis(
    input: &RustProgram<'_>,
    alloc_fns: &FxHashSet<LocalDefId>,
) -> FxHashMap<LocalDefId, ArrayLocalProvenance> {
    let call_graph = CallGraphPostOrder::new(input);
    let function_set: FxHashSet<LocalDefId> = input.functions.iter().copied().collect();
    let mut summaries: FxHashMap<LocalDefId, FunctionSummary> = FxHashMap::default();
    let mut results: FxHashMap<LocalDefId, ArrayLocalProvenance> = FxHashMap::default();

    for scc in call_graph.sccs() {
        let local_scc: Vec<LocalDefId> = scc
            .iter()
            .filter_map(|def_id| def_id.as_local())
            .filter(|def_id| function_set.contains(def_id))
            .collect();
        if local_scc.is_empty() {
            continue;
        }

        for &def_id in &local_scc {
            summaries.entry(def_id).or_default();
        }

        let mut stabilized = false;
        for _ in 0..32 {
            let mut changed = false;
            for &def_id in &local_scc {
                let body = input
                    .tcx
                    .mir_drops_elaborated_and_const_checked(def_id)
                    .borrow();
                let result = analyze_body_with_summaries(
                    input.tcx,
                    def_id,
                    &body,
                    alloc_fns,
                    Some(&summaries),
                );
                let mut summary = build_function_summary(input.tcx, def_id, &body, &result);
                summary.normalize();
                changed |= summaries.get(&def_id) != Some(&summary);
                summaries.insert(def_id, summary);
                results.insert(def_id, result);
            }
            if !changed {
                stabilized = true;
                break;
            }
        }

        if !stabilized {
            for &def_id in &local_scc {
                summaries.remove(&def_id);
            }
            for &def_id in &local_scc {
                let body = input
                    .tcx
                    .mir_drops_elaborated_and_const_checked(def_id)
                    .borrow();
                let result = analyze_body_with_summaries(
                    input.tcx,
                    def_id,
                    &body,
                    alloc_fns,
                    Some(&summaries),
                );
                results.insert(def_id, result);
            }
        }
    }

    results
}

#[cfg(test)]
pub fn analyze_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
    alloc_fns: &FxHashSet<LocalDefId>,
) -> ArrayLocalProvenance {
    analyze_body_with_summaries(tcx, def_id, body, alloc_fns, None)
}

fn analyze_body_with_summaries<'tcx>(
    tcx: TyCtxt<'tcx>,
    _def_id: LocalDefId,
    body: &Body<'tcx>,
    alloc_fns: &FxHashSet<LocalDefId>,
    callee_summaries: Option<&FxHashMap<LocalDefId, FunctionSummary>>,
) -> ArrayLocalProvenance {
    let slot_table = SlotTable::new(body, tcx);
    let rhs_map = build_rhs_map(body, tcx);
    let mut collector = Collector {
        tcx,
        body,
        alloc_fns,
        callee_summaries,
        slot_table: &slot_table,
        graph: PointerFlowGraph::default(),
        rhs_map,
        direct_param_slots: FxHashSet::default(),
        call_effects: FxHashMap::default(),
    };
    collector.collect();
    let graph = collector.graph;
    let call_effects = collector.call_effects;
    let provenance = solve_reachable_bases(&graph);
    let base_classifications = graph
        .bases
        .iter()
        .map(|base| (base.clone(), classify_base(base)))
        .collect();

    ArrayLocalProvenance {
        slot_table,
        graph,
        provenance,
        base_classifications,
        call_effects,
    }
}

/// Returns the pointer-type qualifier for a specific local qualifier offset.
fn qualifier_at_local(
    mutability_result: &MutabilityResult,
    def_id: LocalDefId,
    local: Local,
    slot_offset: usize,
) -> Option<PtrMut> {
    mutability_result.function_body_fact(def_id, local.index(), slot_offset)
}

#[allow(dead_code)]
fn qualifier_at_slot(
    mutability_result: &MutabilityResult,
    def_id: LocalDefId,
    info: &SlotInfo,
) -> Option<PtrMut> {
    match info.qualifier_key {
        Some(QualifierKey::Local { offset }) => {
            mutability_result.function_body_fact(def_id, info.root.index(), offset)
        }
        Some(QualifierKey::StructField {
            def_id: struct_def_id,
            field,
            offset,
        }) => mutability_result.struct_field_fact(struct_def_id, field.index(), offset),
        None => None,
    }
}

fn slot_ty<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>, info: &SlotInfo) -> Option<Ty<'tcx>> {
    let mut ty = body.local_decls[info.root].ty;

    for elem in &info.path {
        match elem {
            SlotPathElem::Pointee => {
                ty = ty.builtin_deref(true)?;
            }
            SlotPathElem::Field(field) => {
                ty = match ty.kind() {
                    ty::TyKind::Adt(adt_def, args) => {
                        if !adt_def.is_struct() || adt_def.is_union() {
                            return None;
                        }
                        adt_def.all_fields().nth(field.index())?.ty(tcx, args)
                    }
                    ty::TyKind::Tuple(tys) => tys.iter().nth(field.index())?,
                    _ => return None,
                };
            }
            SlotPathElem::Element => {
                ty = ty.builtin_index()?;
            }
        }
    }

    Some(ty)
}

fn slot_is_mutable_pointer_source<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    info: &SlotInfo,
) -> bool {
    match slot_ty(body, tcx, info).map(Ty::kind) {
        Some(ty::TyKind::RawPtr(_, mutability) | ty::TyKind::Ref(_, _, mutability)) => {
            mutability.is_mut()
        }
        _ => false,
    }
}

fn source_var_identity_for_slot<'tcx, S: AsRef<str>>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local_names: &FxHashMap<Local, S>,
    info: &SlotInfo,
) -> Option<String> {
    let root_name = local_names.get(&info.root)?;
    if info.path.is_empty() {
        return Some(root_name.as_ref().to_string());
    }

    let mut ty = body.local_decls[info.root].ty;
    let mut identity = root_name.as_ref().to_string();
    let mut saw_named_field = false;

    for elem in &info.path {
        match elem {
            SlotPathElem::Pointee => {
                ty = ty.builtin_deref(true)?;
            }
            SlotPathElem::Field(field) => {
                let (field_name, field_ty) = named_struct_field(tcx, ty, *field)?;
                identity.push('.');
                identity.push_str(&field_name);
                ty = field_ty;
                saw_named_field = true;
            }
            SlotPathElem::Element => return None,
        }
    }

    saw_named_field.then_some(identity)
}

pub(crate) fn named_struct_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    field: FieldIdx,
) -> Option<(String, Ty<'tcx>)> {
    let ty::TyKind::Adt(adt_def, args) = ty.kind() else {
        return None;
    };
    if !adt_def.is_struct() || adt_def.is_union() {
        return None;
    }

    let field_def = adt_def.all_fields().nth(field.index())?;
    let field_name = field_def.name.as_str();
    if field_name.parse::<usize>().is_ok() {
        return None;
    }

    Some((field_name.to_string(), field_def.ty(tcx, args)))
}

/// Selects groups of slots eligible for rewriting from a single function body.
///
/// A group is selected when:
/// 1. The base has `DirectlyRewriteable` admissibility.
/// 2. The base storage is stable for the lifetime of all non-base group members:
///    - LocalArray and LocalScalar bases are considered stable stack objects.
///    - RawBorrow bases use the existing pointer mutability qualifier check.
///    - Param bases are rejected only if their storage may be written while a
///      non-base group member is live after that write.
/// 3. The group contains either ≥ 2 distinct mutable pointer source-variable
///    identities, or ≥ 1 mutable AND ≥ 1 immutable identity (allowing *const
///    aliases to participate). Direct locals and named struct-field slots count;
///    unnamed temporaries, tuple fields, arrays, and unions do not.
pub struct RewriteSelectionContext<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub points_to: &'a andersen::AnalysisResult,
}

// only used by the analysis test harness now; the rewriter pass calls
// `classify_rewrite_groups` directly so it can also trace discarded statuses.
#[cfg(test)]
pub fn select_rewrite_groups<'a, 'tcx>(
    provenance: &ArrayLocalProvenance,
    body: &Body<'tcx>,
    mutability_result: &MutabilityResult,
    def_id: LocalDefId,
    context: RewriteSelectionContext<'a, 'tcx>,
) -> Vec<RewriteGroup> {
    classify_rewrite_groups(provenance, body, mutability_result, def_id, context)
        .into_iter()
        .filter_map(|status| match status {
            RewriteGroupStatus::Ready(group) => Some(group),
            RewriteGroupStatus::PreservedAcrossCalls { .. } => None,
        })
        .collect()
}

pub(crate) fn classify_rewrite_groups<'a, 'tcx>(
    provenance: &ArrayLocalProvenance,
    body: &Body<'tcx>,
    mutability_result: &MutabilityResult,
    def_id: LocalDefId,
    context: RewriteSelectionContext<'a, 'tcx>,
) -> Vec<RewriteGroupStatus> {
    let mut groups = vec![];
    let live_after = compute_live_after_by_location(context.tcx, body);

    // build local → source-variable name from VarDebugInfo
    let mut local_name: FxHashMap<Local, &str> = FxHashMap::default();
    for dbg in &body.var_debug_info {
        if let mir::VarDebugInfoContents::Place(place) = &dbg.value
            && let Some(local) = place.as_local()
        {
            local_name.entry(local).or_insert(dbg.name.as_str());
        }
    }

    for (base, classification) in &provenance.base_classifications {
        if classification.admissibility != BaseAdmissibility::DirectlyRewriteable {
            continue;
        }

        let Some((base_local, base_slot_offset)) = base_local_of_base(base, &provenance.slot_table)
        else {
            continue;
        };

        // collect all slots whose unique reachable base is this base
        let members: Vec<SlotIdx> = provenance
            .slot_table
            .slot_infos
            .iter()
            .enumerate()
            .filter_map(|(slot_idx, _)| {
                let node = PfgNode::Slot(slot_idx);
                if provenance.provenance.unique_non_null_base(&node).as_ref() == Some(base) {
                    Some(slot_idx)
                } else {
                    None
                }
            })
            .collect();
        // condition 3: either ≥ 2 distinct mutable pointer source-variable identities,
        // or ≥ 1 mutable AND ≥ 1 immutable — lets *const aliases participate.
        // additionally, those qualifying members must be simultaneously live at some
        // MIR location; non-overlapping live ranges imply no borrow conflict and the
        // pointers can be promoted independently.
        let mut mut_source_vars: FxHashSet<String> = FxHashSet::default();
        let mut has_any_imm = false;
        let mut member_roots: FxHashSet<Local> = FxHashSet::default();
        let mut local_mut_roots: FxHashSet<Local> = FxHashSet::default();
        let mut local_imm_roots: FxHashSet<Local> = FxHashSet::default();
        for &slot_idx in &members {
            let info = &provenance.slot_table.slot_infos[slot_idx];
            if local_name.contains_key(&info.root) {
                member_roots.insert(info.root);
            }
            if let Some(name) = source_var_identity_for_slot(context.tcx, body, &local_name, info) {
                if slot_is_mutable_pointer_source(body, context.tcx, info) {
                    mut_source_vars.insert(name);
                    local_mut_roots.insert(info.root);
                } else {
                    has_any_imm = true;
                    local_imm_roots.insert(info.root);
                }
            }
        }
        // fast global pre-filter: if no named mutable identity exists at all,
        // the liveness check below cannot pass either.
        let has_multi_mut = mut_source_vars.len() >= 2;
        let has_mixed = !mut_source_vars.is_empty() && has_any_imm;
        if !has_multi_mut && !has_mixed {
            continue;
        }
        // simultaneous-liveness gate: require at least one MIR location where the
        // mutability condition holds for the subset of member locals that are live there.
        // `live_after` tracks MIR locals (not slots), so a struct root being live means
        // all its fields are considered potentially live
        let has_conflict = live_after.values().any(|live| {
            let live_mut_count = local_mut_roots
                .iter()
                .filter(|l| live.contains(**l))
                .count();
            if live_mut_count >= 2 {
                return true;
            }
            if live_mut_count >= 1 {
                return local_imm_roots.iter().any(|l| live.contains(*l));
            }
            false
        });
        if !has_conflict {
            continue;
        }
        if !member_pointer_elements_match_base_element(
            body,
            context.tcx,
            base_local,
            base_slot_offset,
            &local_name,
            &members,
            provenance,
        ) {
            continue;
        }

        // condition 2: the base variable binding must be stable for selection
        let stability_context = BaseStabilityContext {
            provenance,
            body,
            mutability_result,
            def_id,
            live_after: &live_after,
            tcx: context.tcx,
            points_to: context.points_to,
        };
        let stability = is_base_stable_for_selection(
            base,
            base_local,
            base_slot_offset,
            &members,
            &member_roots,
            &stability_context,
        );
        let (index_tracked, preserved_calls) = match stability {
            SelectionStability::Stable => (false, vec![]),
            SelectionStability::IndexTracked => (true, vec![]),
            SelectionStability::PreservedAcrossCalls {
                index_tracked,
                calls,
            } => (index_tracked, calls),
            SelectionStability::Unstable => continue,
        };

        let group = RewriteGroup {
            base: base.clone(),
            base_local,
            base_slot_offset,
            members,
            index_tracked,
        };
        if preserved_calls.is_empty() {
            groups.push(RewriteGroupStatus::Ready(group));
        } else {
            groups.push(RewriteGroupStatus::PreservedAcrossCalls {
                group,
                calls: preserved_calls,
            });
        }
    }

    groups
}

fn member_pointer_elements_match_base_element<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    base_local: Local,
    base_slot_offset: usize,
    local_name: &FxHashMap<Local, &str>,
    members: &[SlotIdx],
    provenance: &ArrayLocalProvenance,
) -> bool {
    let Some(base_element_ty) =
        slot_element_ty(body, tcx, provenance, base_local, base_slot_offset)
    else {
        return true;
    };
    members.iter().all(|&slot_idx| {
        let Some(info) = provenance.slot_table.slot_infos.get(slot_idx) else {
            return true;
        };
        if info.root == base_local || !info.path.is_empty() {
            return true;
        }
        if !local_name.contains_key(&info.root) {
            return true;
        }
        slot_ty(body, tcx, info)
            .and_then(pointer_element_ty)
            .is_none_or(|member_element_ty| {
                if member_element_ty == base_element_ty {
                    return true;
                }
                if matches!(
                    base_element_ty.kind(),
                    ty::TyKind::Adt(adt_def, _) if adt_def.is_struct()
                ) {
                    return local_origin_uses_pointer_arithmetic(body, tcx, info.root);
                }
                local_origin_uses_pointer_arithmetic(body, tcx, info.root)
                    || element_tys_same_size_align(body, tcx, base_element_ty, member_element_ty)
            })
    })
}

fn element_tys_same_size_align<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    base_element_ty: Ty<'tcx>,
    member_element_ty: Ty<'tcx>,
) -> bool {
    let typing_env = ty::TypingEnv::post_analysis(tcx, body.source.def_id());
    let (Ok(base_layout), Ok(member_layout)) = (
        tcx.layout_of(typing_env.as_query_input(base_element_ty)),
        tcx.layout_of(typing_env.as_query_input(member_element_ty)),
    ) else {
        return false;
    };
    base_layout.size == member_layout.size && base_layout.align.abi == member_layout.align.abi
}

#[derive(Clone, Copy)]
struct PointerOrigin {
    source: Local,
    uses_pointer_arithmetic: bool,
}

fn local_origin_uses_pointer_arithmetic<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    local: Local,
) -> bool {
    let origins = pointer_origin_map(body, tcx);
    let mut visited = FxHashSet::default();
    local_origin_uses_pointer_arithmetic_inner(local, &origins, &mut visited)
}

fn local_origin_uses_pointer_arithmetic_inner(
    local: Local,
    origins: &FxHashMap<Local, Vec<PointerOrigin>>,
    visited: &mut FxHashSet<Local>,
) -> bool {
    if !visited.insert(local) {
        return false;
    }
    origins.get(&local).is_some_and(|edges| {
        edges.iter().any(|edge| {
            edge.uses_pointer_arithmetic
                || local_origin_uses_pointer_arithmetic_inner(edge.source, origins, visited)
        })
    })
}

fn pointer_origin_map<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> FxHashMap<Local, Vec<PointerOrigin>> {
    let mut origins: FxHashMap<Local, Vec<PointerOrigin>> = FxHashMap::default();
    for block_data in body.basic_blocks.iter() {
        for statement in &block_data.statements {
            let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                continue;
            };
            let Some(dst) = lhs.as_local() else { continue };
            let source = match rvalue {
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => Some(PointerOrigin {
                    source: place.local,
                    uses_pointer_arithmetic: false,
                }),
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                | Rvalue::CopyForDeref(place) => Some(PointerOrigin {
                    source: place.local,
                    uses_pointer_arithmetic: false,
                }),
                // casts still create a source edge so arithmetic is found through a cast chain
                Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
                    Some(PointerOrigin {
                        source: place.local,
                        uses_pointer_arithmetic: false,
                    })
                }
                _ => None,
            };
            if let Some(source) = source {
                origins.entry(dst).or_default().push(source);
            }
        }

        let Some(terminator) = &block_data.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        let Some(dst) = destination.as_local() else {
            continue;
        };
        if let Some((def_id, name)) = call_name(tcx, func)
            && (is_pointer_arithmetic(tcx, def_id, &name) || is_as_ptr(tcx, def_id, &name))
            && let Some(arg) = args.first()
            && let Some(place) = operand_place(&arg.node)
        {
            origins.entry(dst).or_default().push(PointerOrigin {
                source: place.local,
                uses_pointer_arithmetic: is_pointer_arithmetic(tcx, def_id, &name),
            });
        }
    }
    origins
}

fn slot_element_ty<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    provenance: &ArrayLocalProvenance,
    local: Local,
    slot_offset: usize,
) -> Option<Ty<'tcx>> {
    let slots = provenance.slot_table.local_slots(local);
    let slot = slots.start.checked_add(slot_offset)?;
    let info = provenance.slot_table.slot_infos.get(slot)?;
    slot_ty(body, tcx, info).and_then(cursor_element_ty)
}

fn cursor_element_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        ty::TyKind::RawPtr(pointee, _) => Some(*pointee),
        ty::TyKind::Ref(_, referent, _) => sequence_element_ty(*referent),
        ty::TyKind::Array(element, _) | ty::TyKind::Slice(element) => Some(*element),
        _ => None,
    }
}

fn pointer_element_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        ty::TyKind::RawPtr(pointee, _) => Some(*pointee),
        _ => None,
    }
}

fn sequence_element_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        ty::TyKind::Array(element, _) | ty::TyKind::Slice(element) => Some(*element),
        _ => None,
    }
}

fn compute_live_after_by_location<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> FxHashMap<Location, DenseBitSet<Local>> {
    let mut cursor = MaybeLiveLocals
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);
    let mut live_after = FxHashMap::default();

    for (block, block_data) in body.basic_blocks.iter_enumerated() {
        for statement_index in 0..block_data.statements.len() {
            let location = Location {
                block,
                statement_index,
            };
            cursor.seek_after_primary_effect(location);
            live_after.insert(location, cursor.get().clone());
        }

        if block_data.terminator.is_some() {
            let location = Location {
                block,
                statement_index: block_data.statements.len(),
            };
            cursor.seek_after_primary_effect(location);
            live_after.insert(location, cursor.get().clone());
        }
    }

    live_after
}

enum SelectionStability {
    /// no mutation concern — select normally with `index_tracked = false`.
    Stable,
    /// base slot written only via direct (trackable) assignments while members live
    /// — select with `index_tracked = true`.
    IndexTracked,
    /// all relevant summarized calls preserve the group's base.
    PreservedAcrossCalls {
        index_tracked: bool,
        calls: Vec<PreservedBaseCall>,
    },
    /// aliased or call-based writes present — reject.
    Unstable,
}

struct BaseStabilityContext<'a, 'tcx> {
    provenance: &'a ArrayLocalProvenance,
    body: &'a Body<'tcx>,
    mutability_result: &'a MutabilityResult,
    def_id: LocalDefId,
    live_after: &'a FxHashMap<Location, DenseBitSet<Local>>,
    tcx: TyCtxt<'tcx>,
    points_to: &'a andersen::AnalysisResult,
}

fn is_base_stable_for_selection(
    base: &BaseId,
    base_local: Local,
    base_slot_offset: usize,
    members: &[SlotIdx],
    member_roots: &FxHashSet<Local>,
    context: &BaseStabilityContext<'_, '_>,
) -> SelectionStability {
    match base {
        BaseId::LocalArray { .. } | BaseId::LocalScalar { .. } => SelectionStability::Stable,
        BaseId::RawBorrow { .. } => {
            if qualifier_at_local(
                context.mutability_result,
                context.def_id,
                base_local,
                base_slot_offset,
            ) != Some(PtrMut::Mut)
            {
                SelectionStability::Stable
            } else {
                SelectionStability::Unstable
            }
        }
        BaseId::Param { slot, .. } => is_param_base_stable_for_selection(
            base,
            base_local,
            *slot,
            members,
            member_roots,
            context,
        ),
        _ => SelectionStability::Unstable,
    }
}

fn preserved_base_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    location: Location,
    base: &BaseId,
    base_local: Local,
    member_roots: &FxHashSet<Local>,
    body: &Body<'tcx>,
    provenance: &ArrayLocalProvenance,
) -> Option<Option<PreservedBaseCall>> {
    let effects = provenance.call_effects.get(&location)?;
    if !effects.complete {
        return None;
    }

    let block_data = &body.basic_blocks[location.block];
    if location.statement_index != block_data.statements.len() {
        return None;
    }
    let TerminatorKind::Call { args, .. } = &block_data.terminator.as_ref()?.kind else {
        return None;
    };

    let target_root = |arg_index: usize| -> Option<Local> {
        let place = operand_place(&args.get(arg_index)?.node)?;
        let head_slot = provenance
            .slot_table
            .place_slots(place, body, tcx)?
            .next()?;
        let bases = provenance
            .provenance
            .reachable_bases
            .get(&PfgNode::Slot(head_slot))?;
        let mut roots = FxHashSet::default();
        for base in bases {
            let BaseId::RawBorrow {
                target: Some(target),
                ..
            } = base
            else {
                return None;
            };
            roots.insert(provenance.slot_table.slot_infos.get(*target)?.root);
        }
        (roots.len() == 1)
            .then(|| roots.into_iter().next())
            .flatten()
    };

    let mut affected_arguments = FxHashSet::default();
    let mut writes_base_binding = false;
    for write in &effects.writes {
        let root = target_root(write.dst_arg_index)?;
        let relevant = root == base_local || member_roots.contains(&root);
        if !relevant {
            continue;
        }
        if write.sources.is_empty()
            || write.sources.iter().any(|source| {
                let source_base = match source {
                    PfgNode::Base(source_base) => Some(source_base.clone()),
                    _ => provenance.provenance.unique_non_null_base(source),
                };
                source_base.as_ref() != Some(base)
            })
        {
            return None;
        }
        affected_arguments.insert(write.dst_arg_index);
        writes_base_binding |= root == base_local;
    }

    for write in &effects.unknown_writes {
        let root = target_root(write.dst_arg_index)?;
        if root == base_local || member_roots.contains(&root) {
            return None;
        }
    }

    if affected_arguments.is_empty() {
        return Some(None);
    }
    let mut affected_arguments: Vec<_> = affected_arguments.into_iter().collect();
    affected_arguments.sort_unstable();
    Some(Some(PreservedBaseCall {
        location,
        affected_arguments,
        writes_base_binding,
    }))
}

fn is_param_base_stable_for_selection(
    base: &BaseId,
    base_local: Local,
    base_slot: SlotIdx,
    members: &[SlotIdx],
    member_roots: &FxHashSet<Local>,
    context: &BaseStabilityContext<'_, '_>,
) -> SelectionStability {
    let dependent_locals =
        dependent_member_locals(members, member_roots, context.provenance, base_local);
    if dependent_locals.is_empty() {
        return SelectionStability::Stable;
    }
    let all_member_roots: FxHashSet<Local> = members
        .iter()
        .filter_map(|slot| context.provenance.slot_table.slot_infos.get(*slot))
        .map(|info| info.root)
        .collect();

    let base_path_contains_pointee = slot_path_contains_pointee(context.provenance, base_slot);

    let locs = param_base_storage_locs(
        context.points_to,
        context.def_id,
        base_local,
        base_slot,
        context.provenance,
    );
    let base_locs = if base_path_contains_pointee && locs.as_ref().is_none_or(FxHashSet::is_empty) {
        None
    } else {
        locs
    };

    let mut has_direct_write = false;
    let mut preserved_calls = vec![];

    for (block, block_data) in context.body.basic_blocks.iter_enumerated() {
        for statement_index in 0..=block_data.statements.len() {
            if statement_index == block_data.statements.len() && block_data.terminator.is_none() {
                continue;
            }
            let location = Location {
                block,
                statement_index,
            };
            let any_member_live = context
                .live_after
                .get(&location)
                .is_some_and(|live| dependent_locals.iter().any(|local| live.contains(*local)));
            if any_member_live {
                let is_direct = direct_write_overlaps_slot(
                    context.body,
                    context.tcx,
                    context.provenance,
                    location,
                    base_slot,
                );
                if is_direct {
                    has_direct_write = true;
                } else if location_writes_through_dependent_member(
                    context.body,
                    context.tcx,
                    location,
                    &dependent_locals,
                ) {
                    continue;
                } else {
                    if context.provenance.call_effects.contains_key(&location) {
                        match preserved_base_call(
                            context.tcx,
                            location,
                            base,
                            base_local,
                            &all_member_roots,
                            context.body,
                            context.provenance,
                        ) {
                            None => return SelectionStability::Unstable,
                            Some(None) => continue,
                            Some(Some(call)) => {
                                preserved_calls.push(call);
                                continue;
                            }
                        }
                    }
                    // only run alias/call sub-checks when the direct check did not
                    // already account for the write; Andersen's all_writes includes
                    // return-value assignments so it would double-count direct writes.
                    let is_alias = base_locs.as_ref().is_some_and(|base_locs| {
                        location_writes_base_storage(
                            context.points_to,
                            context.def_id,
                            location,
                            base_locs,
                        )
                    });
                    let is_call = base_locs.as_ref().is_some_and(|base_locs| {
                        call_may_write_base_storage(
                            context.points_to,
                            context.body,
                            context.tcx,
                            context.provenance,
                            context.def_id,
                            location,
                            base_locs,
                        )
                    });
                    if is_alias || is_call {
                        return SelectionStability::Unstable;
                    }
                }
            }
        }
    }

    if !preserved_calls.is_empty() {
        SelectionStability::PreservedAcrossCalls {
            index_tracked: has_direct_write,
            calls: preserved_calls,
        }
    } else if has_direct_write {
        SelectionStability::IndexTracked
    } else {
        SelectionStability::Stable
    }
}

fn slot_path_contains_pointee(provenance: &ArrayLocalProvenance, slot: SlotIdx) -> bool {
    provenance
        .slot_table
        .slot_infos
        .get(slot)
        .is_some_and(|info| info.path.contains(&SlotPathElem::Pointee))
}

fn param_base_storage_locs(
    points_to: &andersen::AnalysisResult,
    def_id: LocalDefId,
    local: Local,
    slot: SlotIdx,
    provenance: &ArrayLocalProvenance,
) -> Option<FxHashSet<andersen::Loc>> {
    let info = provenance.slot_table.slot_infos.get(slot)?;
    let mut nodes = FxHashSet::default();
    nodes.insert(*points_to.var_nodes.get(&(def_id, local))?);

    for elem in &info.path {
        let mut next_nodes = FxHashSet::default();
        match elem {
            SlotPathElem::Pointee => {
                for node in &nodes {
                    for loc in points_to.solutions[node.index].iter() {
                        next_nodes.insert(andersen::LocNode {
                            prefix: 0,
                            index: loc,
                        });
                    }
                }
            }
            SlotPathElem::Element => {
                for node in &nodes {
                    let andersen::LocEdges::Index(succ) = points_to.graph.get(node)? else {
                        return None;
                    };
                    next_nodes.insert(*succ);
                }
            }
            SlotPathElem::Field(field) => {
                for node in &nodes {
                    let andersen::LocEdges::Fields(succs) = points_to.graph.get(node)? else {
                        return None;
                    };
                    next_nodes.insert(*succs.get(*field)?);
                }
            }
        }
        if next_nodes.is_empty() {
            return None;
        }
        nodes = next_nodes;
    }

    Some(nodes.into_iter().map(|node| node.index).collect())
}

fn location_writes_base_storage(
    points_to: &andersen::AnalysisResult,
    def_id: LocalDefId,
    location: Location,
    base_locs: &FxHashSet<andersen::Loc>,
) -> bool {
    points_to
        .all_writes
        .get(&def_id)
        .and_then(|writes| writes.get(&location))
        .is_some_and(|writes| base_locs.iter().any(|base_loc| writes.contains(*base_loc)))
}

fn call_may_write_base_storage<'tcx>(
    points_to: &andersen::AnalysisResult,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    provenance: &ArrayLocalProvenance,
    def_id: LocalDefId,
    location: Location,
    base_locs: &FxHashSet<andersen::Loc>,
) -> bool {
    let block_data = &body.basic_blocks[location.block];
    if location.statement_index != block_data.statements.len() {
        return false;
    }
    let Some(terminator) = &block_data.terminator else {
        return false;
    };
    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return false;
    };
    if call_name(tcx, func)
        .as_ref()
        .is_some_and(|(def_id, name)| call_no_writes(tcx, *def_id, name))
    {
        return false;
    }

    args.iter().any(|arg| {
        let Some(place) = operand_place(&arg.node) else {
            return false;
        };
        let arg_ty = place.ty(body, tcx).ty;
        match place_value_points_to_locs(points_to, def_id, place) {
            Some(arg_locs)
                if arg_locs.iter().any(|arg_loc| {
                    loc_range_overlaps_base_locs(points_to, *arg_loc, base_locs)
                }) =>
            {
                return true;
            }
            Some(_) => {}
            None if arg_ty.builtin_deref(true).is_some() => return true,
            None => {}
        }

        arg_ty.builtin_deref(true).is_none()
            && count_slots(arg_ty, tcx, &mut FxHashSet::default()) > 0
            && aggregate_arg_may_write_base_storage(
                points_to, body, tcx, provenance, def_id, place, base_locs,
            )
    })
}

fn aggregate_arg_may_write_base_storage<'tcx>(
    points_to: &andersen::AnalysisResult,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    provenance: &ArrayLocalProvenance,
    def_id: LocalDefId,
    place: Place<'tcx>,
    base_locs: &FxHashSet<andersen::Loc>,
) -> bool {
    let Some(place_path) = slot_path_from_place(place) else {
        return true;
    };
    let Some(slots) = provenance.slot_table.place_slots(place, body, tcx) else {
        return true;
    };

    for slot in slots {
        let Some(info) = provenance.slot_table.slot_infos.get(slot) else {
            return true;
        };
        let Some(relative_path) = info.path.strip_prefix(place_path.as_slice()) else {
            return true;
        };
        if relative_path.contains(&SlotPathElem::Pointee) {
            continue;
        }

        let Some(arg_locs) = slot_value_points_to_locs(points_to, def_id, info) else {
            return true;
        };
        if arg_locs
            .iter()
            .any(|arg_loc| loc_range_overlaps_base_locs(points_to, *arg_loc, base_locs))
        {
            return true;
        }
    }

    false
}

fn location_writes_through_dependent_member<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    location: Location,
    dependent_locals: &FxHashSet<Local>,
) -> bool {
    let Some(place) = written_place_at(body, location) else {
        return false;
    };
    dependent_locals.contains(&place.local)
        && slot_path_from_place(place).is_some_and(|path| path.contains(&SlotPathElem::Pointee))
        && place.ty(body, tcx).ty.builtin_deref(true).is_none()
}

fn slot_path_from_place<'tcx>(place: Place<'tcx>) -> Option<Vec<SlotPathElem>> {
    slot_path_from_projection(place.projection.as_ref())
}

fn loc_range_overlaps_base_locs(
    points_to: &andersen::AnalysisResult,
    arg_loc: andersen::Loc,
    base_locs: &FxHashSet<andersen::Loc>,
) -> bool {
    let end = points_to.ends[arg_loc];
    base_locs
        .iter()
        .any(|base_loc| arg_loc <= *base_loc && *base_loc <= end)
}

fn place_value_points_to_locs<'tcx>(
    points_to: &andersen::AnalysisResult,
    def_id: LocalDefId,
    place: Place<'tcx>,
) -> Option<FxHashSet<andersen::Loc>> {
    let nodes = points_to_nodes_for_place(points_to, def_id, place)?;
    let mut locs = FxHashSet::default();
    for node in nodes {
        locs.extend(points_to.solutions[node.index].iter());
    }
    Some(locs)
}

fn slot_value_points_to_locs(
    points_to: &andersen::AnalysisResult,
    def_id: LocalDefId,
    info: &SlotInfo,
) -> Option<FxHashSet<andersen::Loc>> {
    let nodes = points_to_nodes_for_slot_path(points_to, def_id, info.root, &info.path)?;
    let mut locs = FxHashSet::default();
    for node in nodes {
        locs.extend(points_to.solutions[node.index].iter());
    }
    Some(locs)
}

fn points_to_nodes_for_place<'tcx>(
    points_to: &andersen::AnalysisResult,
    def_id: LocalDefId,
    place: Place<'tcx>,
) -> Option<FxHashSet<andersen::LocNode>> {
    let path = slot_path_from_place(place)?;
    points_to_nodes_for_slot_path(points_to, def_id, place.local, &path)
}

fn points_to_nodes_for_slot_path(
    points_to: &andersen::AnalysisResult,
    def_id: LocalDefId,
    root: Local,
    path: &[SlotPathElem],
) -> Option<FxHashSet<andersen::LocNode>> {
    let mut nodes = FxHashSet::default();
    nodes.insert(*points_to.var_nodes.get(&(def_id, root))?);

    for elem in path {
        let mut next_nodes = FxHashSet::default();
        match elem {
            SlotPathElem::Pointee => {
                for node in &nodes {
                    for loc in points_to.solutions[node.index].iter() {
                        next_nodes.insert(andersen::LocNode {
                            prefix: 0,
                            index: loc,
                        });
                    }
                }
            }
            SlotPathElem::Field(field) => {
                for node in &nodes {
                    let andersen::LocEdges::Fields(succs) = points_to.graph.get(node)? else {
                        return None;
                    };
                    next_nodes.insert(*succs.get(*field)?);
                }
            }
            SlotPathElem::Element => {
                for node in &nodes {
                    let andersen::LocEdges::Index(succ) = points_to.graph.get(node)? else {
                        return None;
                    };
                    next_nodes.insert(*succ);
                }
            }
        }
        if next_nodes.is_empty() {
            return None;
        }
        nodes = next_nodes;
    }

    Some(nodes)
}

fn written_place_at<'tcx>(body: &Body<'tcx>, location: Location) -> Option<Place<'tcx>> {
    let block_data = &body.basic_blocks[location.block];
    if let Some(statement) = block_data.statements.get(location.statement_index) {
        if let StatementKind::Assign(box (place, _)) = &statement.kind {
            return Some(*place);
        }
        return None;
    }

    if location.statement_index == block_data.statements.len()
        && let Some(terminator) = &block_data.terminator
        && let TerminatorKind::Call { destination, .. } = terminator.kind
    {
        return Some(destination);
    }

    None
}

fn direct_write_overlaps_slot<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    provenance: &ArrayLocalProvenance,
    location: Location,
    base_slot: SlotIdx,
) -> bool {
    let Some(place) = written_place_at(body, location) else {
        return false;
    };
    provenance
        .slot_table
        .place_slots(place, body, tcx)
        .is_some_and(|slots| slots.contains(&base_slot))
}

fn dependent_member_locals(
    members: &[SlotIdx],
    member_roots: &FxHashSet<Local>,
    provenance: &ArrayLocalProvenance,
    base_local: Local,
) -> FxHashSet<Local> {
    members
        .iter()
        .filter_map(|slot| provenance.slot_table.slot_infos.get(*slot))
        .map(|info| info.root)
        .filter(|local| member_roots.contains(local))
        .filter(|local| *local != base_local)
        .collect()
}

pub(crate) fn base_slot_info<'a>(
    provenance: &'a ArrayLocalProvenance,
    group: &RewriteGroup,
) -> Option<&'a SlotInfo> {
    let slots = provenance.slot_table.local_slots(group.base_local);
    let base_slot = slots.start.checked_add(group.base_slot_offset)?;
    if base_slot >= slots.end {
        return None;
    }
    provenance.slot_table.slot_infos.get(base_slot)
}

/// last-segment names of external calls whose arg 0 is a base-preserving
/// pointer cursor that can be inline-materialised at the call site.
pub(crate) fn is_inlineable_pointer_arg(name: &str, arg_index: usize) -> bool {
    matches!(
        name,
        "memchr" | "memset" | "strstr" | "strchr" | "strrchr" | "strpbrk"
    ) && arg_index == 0
}

pub(crate) fn is_inlineable_call(name: &str) -> bool {
    // every inlineable call's pointer arg is arg 0, so reuse the single list.
    is_inlineable_pointer_arg(name, 0)
}

#[allow(dead_code)]
pub fn debug_rewrite_groups<'tcx>(
    groups: &[RewriteGroup],
    body: &Body<'tcx>,
    provenance: &ArrayLocalProvenance,
    mutability_result: &MutabilityResult,
    def_id: LocalDefId,
    tcx: TyCtxt<'tcx>,
    source_var_groups: Option<&SourceVarGroups>,
) -> String {
    // build a map from Local → first debug name found (direct locals only)
    let mut local_names: FxHashMap<Local, &str> = FxHashMap::default();
    for info in &body.var_debug_info {
        if let mir::VarDebugInfoContents::Place(place) = &info.value
            && let Some(local) = place.as_local()
        {
            local_names.entry(local).or_insert(info.name.as_str());
        }
    }

    // build a reverse map (root, path) → slot_idx for projection-based name lookup
    let mut slot_by_place: FxHashMap<(Local, Vec<SlotPathElem>), SlotIdx> = FxHashMap::default();
    for (slot_idx, info) in provenance.slot_table.slot_infos.iter().enumerate() {
        slot_by_place
            .entry((info.root, info.path.clone()))
            .or_insert(slot_idx);
    }

    // extend with names from projection-based var_debug_info entries
    let mut slot_names: FxHashMap<SlotIdx, &str> = FxHashMap::default();
    for dbg in &body.var_debug_info {
        if let mir::VarDebugInfoContents::Place(place) = &dbg.value {
            let path: Option<Vec<SlotPathElem>> = place
                .projection
                .iter()
                .map(|elem| match elem {
                    ProjectionElem::Deref => Some(SlotPathElem::Pointee),
                    ProjectionElem::Field(f, _) => Some(SlotPathElem::Field(f)),
                    _ => None,
                })
                .collect();
            if let Some(path) = path
                && let Some(&slot_idx) = slot_by_place.get(&(place.local, path))
            {
                slot_names.entry(slot_idx).or_insert(dbg.name.as_str());
            }
        }
    }

    let mut grouped_local_names: FxHashMap<Local, &str> = FxHashMap::default();
    if let Some(source_var_groups) = source_var_groups {
        let local_count = body.local_decls.len();
        for target_index in 0..local_count {
            let target = Local::from_usize(target_index);
            let mut promoted = DenseBitSet::new_empty(local_count);
            for index in 0..local_count {
                if index != target_index {
                    promoted.insert(Local::from_usize(index));
                }
            }

            let mut promoted_by_fn = FxHashMap::default();
            promoted_by_fn.insert(def_id, promoted);
            let postprocessed = source_var_groups.postprocess_promoted_mut_refs(promoted_by_fn);
            let Some(group_complete_locals) = postprocessed.get(&def_id) else {
                continue;
            };
            for (&source_local, &name) in &local_names {
                if !group_complete_locals.contains(source_local) {
                    grouped_local_names.entry(target).or_insert(name);
                    break;
                }
            }
        }
    }

    let local_label = |local: Local| -> String {
        match local_names.get(&local) {
            Some(name) => format!("{local:?} \"{name}\""),
            None => grouped_local_names
                .get(&local)
                .map(|name| format!("{local:?} \"{name}\""))
                .unwrap_or_else(|| format!("{local:?}")),
        }
    };

    let slot_label = |local: Local, slot_idx: SlotIdx| -> String {
        if let Some(name) = slot_names.get(&slot_idx) {
            return format!("{local:?} \"{name}\"");
        }
        let info = &provenance.slot_table.slot_infos[slot_idx];
        if let Some(name) = source_var_identity_for_slot(tcx, body, &local_names, info) {
            return format!("{local:?} \"{name}\"");
        }
        local_label(local)
    };

    let ptr_mut_label = |local: Local, offset: usize| -> &'static str {
        match qualifier_at_local(mutability_result, def_id, local, offset) {
            Some(PtrMut::Mut) => "*mut",
            Some(PtrMut::Imm) => "*const",
            None => "?",
        }
    };

    let path_label = |slot_idx: SlotIdx| -> String {
        let info = &provenance.slot_table.slot_infos[slot_idx];
        if info.path.is_empty() {
            return String::new();
        }
        let parts: Vec<String> = info
            .path
            .iter()
            .map(|elem| match elem {
                SlotPathElem::Pointee => "Pointee".to_string(),
                SlotPathElem::Field(f) => format!("Field({})", f.index()),
                SlotPathElem::Element => "Element".to_string(),
            })
            .collect();
        format!("[{}]", parts.join(", "))
    };

    let mut out = String::new();
    for group in groups {
        let base_label = base_slot_info(provenance, group)
            .and_then(|info| source_var_identity_for_slot(tcx, body, &local_names, info))
            .map(|name| format!("{:?} \"{name}\"", group.base_local))
            .unwrap_or_else(|| local_label(group.base_local));
        let var_mut = if body.local_decls[group.base_local].mutability == mir::Mutability::Mut {
            "mut"
        } else {
            "let"
        };
        let ptr_mut = ptr_mut_label(group.base_local, group.base_slot_offset);
        let _ = writeln!(
            out,
            "  group base: {} [{var_mut}] offset={} ({ptr_mut}) base={:?}",
            base_label, group.base_slot_offset, group.base,
        );
        for &slot_idx in &group.members {
            let info = &provenance.slot_table.slot_infos[slot_idx];
            let pm = match qualifier_at_slot(mutability_result, def_id, info) {
                Some(PtrMut::Mut) => "*mut",
                Some(PtrMut::Imm) => "*const",
                None => "?",
            };
            let _ = writeln!(
                out,
                "    member: slot {slot_idx} → {} {} ({pm})",
                slot_label(info.root, slot_idx),
                path_label(slot_idx),
            );
        }
    }
    out
}

fn build_rhs_map<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> FxHashMap<Local, Vec<AssignRhs<'tcx>>> {
    let mut map: FxHashMap<Local, Vec<AssignRhs<'tcx>>> = FxHashMap::default();
    for block_data in body.basic_blocks.iter() {
        for statement in &block_data.statements {
            let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                continue;
            };
            let Some(local) = lhs.as_local() else { continue };
            match rvalue {
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                    map.entry(local)
                        .or_default()
                        .push(AssignRhs::ArrayBorrow(*place));
                }
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                | Rvalue::CopyForDeref(place) => {
                    map.entry(local)
                        .or_default()
                        .push(AssignRhs::Follow(place.local));
                }
                _ => {}
            }
        }

        // for pointer-arithmetic and as_ptr/as_mut_ptr call terminators, record the
        // first argument as a Follow entry so that array_source_for_local can trace
        // back through chains like:  _tmp3 = offset(_tmp2, i)
        //                            _tmp2 = as_mut_ptr(move _tmp1)
        //                            _tmp1 = &mut (*arr).data   ← ArrayBorrow already recorded
        let Some(terminator) = &block_data.terminator else { continue };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        let Some(dest_local) = destination.as_local() else {
            continue;
        };
        if let Some((def_id, name)) = call_name(tcx, func)
            && (is_pointer_arithmetic(tcx, def_id, &name) || is_as_ptr(tcx, def_id, &name))
            && let Some(arg) = args.first()
            && let Some(place) = operand_place(&arg.node)
        {
            map.entry(dest_local)
                .or_default()
                .push(AssignRhs::Follow(place.local));
        }
    }
    map
}

impl SlotTable {
    fn new<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        let mut local_slots = Vec::with_capacity(body.local_decls.len());
        let mut slot_infos = vec![];

        for (local, decl) in body.local_decls.iter_enumerated() {
            let start = slot_infos.len();
            collect_slot_infos(
                local,
                decl.ty,
                tcx,
                &mut vec![],
                0,
                &mut QualifierContext::Local { next_offset: 0 },
                &mut FxHashSet::default(),
                &mut slot_infos,
            );
            let end = slot_infos.len();
            local_slots.push(start..end);
        }

        Self {
            local_slots,
            slot_infos,
        }
    }

    fn local_slots(&self, local: Local) -> Range<SlotIdx> {
        self.local_slots[local.index()].clone()
    }

    fn local_head_slot(&self, local: Local) -> Option<SlotIdx> {
        self.local_slots(local).next()
    }

    fn place_slots<'tcx>(
        &self,
        place: Place<'tcx>,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<Range<SlotIdx>> {
        let mut offset = 0;
        let mut base_ty = body.local_decls[place.local].ty;

        for elem in place.projection {
            match elem {
                ProjectionElem::Deref => {
                    base_ty = base_ty.builtin_deref(true)?;
                    offset += 1;
                }
                ProjectionElem::Field(field, ty) => {
                    offset += field_slot_offset(base_ty, field, tcx)?;
                    base_ty = ty;
                }
                ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                    base_ty = base_ty.builtin_index()?;
                }
                _ => return None,
            }
        }

        let local_slots = self.local_slots(place.local);
        let width = count_slots(base_ty, tcx, &mut FxHashSet::default());
        let start = local_slots.start + offset;
        let end = start + width;
        if end <= local_slots.end {
            Some(start..end)
        } else {
            None
        }
    }

    fn place_head_slot<'tcx>(
        &self,
        place: Place<'tcx>,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<SlotIdx> {
        if !place.ty(body, tcx).ty.is_raw_ptr() {
            return None;
        }

        self.place_slots(place, body, tcx)?.next()
    }
}

struct Collector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    alloc_fns: &'a FxHashSet<LocalDefId>,
    callee_summaries: Option<&'a FxHashMap<LocalDefId, FunctionSummary>>,
    slot_table: &'a SlotTable,
    graph: PointerFlowGraph,
    rhs_map: FxHashMap<Local, Vec<AssignRhs<'tcx>>>,
    direct_param_slots: FxHashSet<SlotIdx>,
    call_effects: FxHashMap<Location, CallEffects>,
}

impl<'tcx> Collector<'_, 'tcx> {
    fn collect(&mut self) {
        for arg in self.body.args_iter() {
            for slot in self.slot_table.local_slots(arg) {
                self.direct_param_slots.insert(slot);
                self.graph
                    .add_base_edge(BaseId::Param { local: arg, slot }, PfgNode::Slot(slot));
            }
        }

        for (block, block_data) in self.body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in block_data.statements.iter().enumerate() {
                let location = Location {
                    block,
                    statement_index,
                };
                self.collect_statement(statement, location);
            }
            let location = Location {
                block,
                statement_index: block_data.statements.len(),
            };
            self.collect_terminator(block, location);
        }
    }

    fn collect_statement(&mut self, statement: &mir::Statement<'tcx>, location: Location) {
        let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
            return;
        };
        // iterate all pointer slots in the destination via place_slots; no longer
        // restricted to destinations whose top-level type is itself a raw pointer
        let Some(dst_slots) = self.slot_table.place_slots(*lhs, self.body, self.tcx) else {
            return;
        };
        if dst_slots.is_empty() {
            return;
        }
        let dst = PfgNode::Slot(dst_slots.start);

        match rvalue {
            Rvalue::Use(operand) => {
                // slot pairing: head slot (i=0) gets a unidirectional add_edge;
                // tail slots (i>0) get add_bidirectional_edge so that pointer
                // fields nested inside the source/destination stay linked in
                // both directions (copy does not establish ownership).
                match operand {
                    Operand::Copy(src_place) | Operand::Move(src_place) => {
                        if let Some(src_slots) =
                            self.slot_table.place_slots(*src_place, self.body, self.tcx)
                        {
                            for (i, (src_slot, dst_slot)) in
                                src_slots.zip(dst_slots.clone()).enumerate()
                            {
                                let src_node = PfgNode::Slot(src_slot);
                                let dst_node = PfgNode::Slot(dst_slot);
                                if i == 0 {
                                    self.graph.add_edge(src_node, dst_node);
                                } else {
                                    // propagate direct-param status across bidirectional copy
                                    // edges so that UML suppression in add_unknown_pointee_slots
                                    // also covers slots of param copies
                                    if self.direct_param_slots.contains(&src_slot) {
                                        self.direct_param_slots.insert(dst_slot);
                                    } else if self.direct_param_slots.contains(&dst_slot) {
                                        self.direct_param_slots.insert(src_slot);
                                    }
                                    self.graph.add_bidirectional_edge(src_node, dst_node);
                                }
                            }
                        } else {
                            self.graph.add_base_edge(
                                BaseId::Unknown {
                                    location,
                                    reason: UnknownReason::UnsupportedProjection,
                                },
                                dst,
                            );
                        }
                    }
                    Operand::Constant(_) => {
                        self.collect_operand_flow(operand, dst, location);
                    }
                }
            }
            Rvalue::CopyForDeref(place) => {
                // when the source can be resolved, collect_place_flow links tail
                // slots via link_tail_slots (bidirectional); only when it cannot be
                // resolved does slot[0] get Unknown and tail slots need it too.
                if self.source_node(*place).is_none() {
                    for slot in dst_slots.clone().skip(1) {
                        self.graph.add_base_edge(
                            BaseId::Unknown {
                                location,
                                reason: UnknownReason::UnsupportedProjection,
                            },
                            PfgNode::Slot(slot),
                        );
                    }
                }
                self.collect_place_flow(*place, dst, true, location);
            }
            Rvalue::Cast(kind, operand, _) => {
                self.collect_cast(*kind, operand, dst, location);
                // collect_cast only models slot[0]; emit Unknown conservatively for
                // any nested pointer slots in the destination (e.g. *mut *mut T)
                for slot in dst_slots.clone().skip(1) {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::UnsupportedProjection,
                        },
                        PfgNode::Slot(slot),
                    );
                }
            }
            Rvalue::RawPtr(_, place) => {
                self.collect_raw_borrow_flow(*lhs, *place, dst.clone(), &dst_slots, location);
            }
            Rvalue::Ref(_, _, place) => {
                self.collect_raw_borrow_flow(*lhs, *place, dst.clone(), &dst_slots, location);
            }
            _ => {
                // only emit a conservative Unknown edge when the rvalue is itself
                // a raw-pointer value we do not specifically handle.  Non-pointer
                // rvalues (e.g. Aggregate/Repeat used to initialise structs or
                // arrays that contain pointer fields) must not pollute those slots.
                if rvalue.ty(self.body, self.tcx).is_raw_ptr() {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::UnsupportedProjection,
                        },
                        dst,
                    );
                }
            }
        }
    }

    fn instantiate_summary_source_node(
        &self,
        source: &SummarySource,
        args: &[Spanned<Operand<'tcx>>],
        location: Location,
    ) -> Option<PfgNode> {
        match source {
            SummarySource::ParamSlot { arg_index, path } => {
                let arg = args.get(*arg_index)?;
                let place = operand_place(&arg.node)?;
                self.place_path_node(place, path)
            }
            SummarySource::Unknown(reason) => {
                let base = BaseId::Unknown {
                    location,
                    reason: reason.clone(),
                };
                Some(PfgNode::Base(base))
            }
            SummarySource::OpaqueReturn => Some(PfgNode::Base(BaseId::OpaqueReturn { location })),
            SummarySource::HeapAlloc => Some(PfgNode::Base(BaseId::HeapAlloc { location })),
        }
    }

    fn place_path_node(&self, place: Place<'tcx>, path: &[SlotPathElem]) -> Option<PfgNode> {
        let slots = self.slot_table.place_slots(place, self.body, self.tcx)?;
        for slot in slots {
            let info = self.slot_table.slot_infos.get(slot)?;
            if info.path.ends_with(path) {
                return Some(PfgNode::Slot(slot));
            }
        }
        None
    }

    fn argument_path_node(
        &self,
        args: &[Spanned<Operand<'tcx>>],
        arg_index: usize,
        path: &[SlotPathElem],
    ) -> Option<PfgNode> {
        let arg = args.get(arg_index)?;
        let place = operand_place(&arg.node)?;
        self.place_path_node(place, path)
    }

    fn destination_path_node(
        &self,
        destination: Place<'tcx>,
        path: &[SlotPathElem],
    ) -> Option<PfgNode> {
        self.place_path_node(destination, path)
    }

    fn should_skip_unknown_memory_load_on_node(&self, dst: &PfgNode) -> bool {
        matches!(dst, PfgNode::Slot(slot) if self.direct_param_slots.contains(slot))
    }

    fn collect_summary_call(
        &mut self,
        callee: LocalDefId,
        args: &[Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        location: Location,
    ) -> bool {
        let Some(summary) = self
            .callee_summaries
            .and_then(|summaries| summaries.get(&callee))
            .cloned()
        else {
            return false;
        };
        if !summary.is_complete() {
            return false;
        }

        self.apply_summary(&summary, args, destination, location)
    }

    fn apply_summary(
        &mut self,
        summary: &FunctionSummary,
        args: &[Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        location: Location,
    ) -> bool {
        let mut return_edges = Vec::new();
        let mut arg_write_edges: FxHashMap<(usize, SlotIdx), Vec<PfgNode>> = FxHashMap::default();
        let mut unknown_returns = Vec::new();
        let mut unknown_arg_writes = Vec::new();

        for flow in &summary.return_flows {
            let Some(src) = self.instantiate_summary_source_node(&flow.src, args, location) else {
                return false;
            };
            let Some(dst) = self.destination_path_node(destination, &flow.dst_return_path) else {
                return false;
            };
            return_edges.push((src, dst));
        }

        for flow in &summary.arg_write_flows {
            let Some(src) = self.instantiate_summary_source_node(&flow.src, args, location) else {
                return false;
            };
            let Some(dst) = self.argument_path_node(args, flow.dst_arg_index, &flow.dst_path)
            else {
                return false;
            };
            let PfgNode::Slot(destination) = dst else {
                return false;
            };
            arg_write_edges
                .entry((flow.dst_arg_index, destination))
                .or_default()
                .push(src);
        }

        for path in &summary.unknown_return_slots {
            let Some(dst) = self.destination_path_node(destination, path) else {
                return false;
            };
            unknown_returns.push(dst);
        }

        for target in &summary.unknown_arg_writes {
            let Some(dst) = self.argument_path_node(args, target.arg_index, &target.path) else {
                return false;
            };
            let PfgNode::Slot(destination) = dst else {
                return false;
            };
            unknown_arg_writes.push(InstantiatedUnknownArgWrite {
                dst_arg_index: target.arg_index,
                destination,
            });
        }

        for (src, dst) in return_edges {
            if let PfgNode::Base(base) = &src {
                self.graph.add_base(base.clone());
            }
            self.graph.add_edge(src, dst);
        }

        let mut writes = Vec::with_capacity(arg_write_edges.len());
        for ((dst_arg_index, destination), sources) in arg_write_edges {
            for src in &sources {
                if let PfgNode::Base(base) = src {
                    self.graph.add_base(base.clone());
                }
                self.graph.add_edge(src.clone(), PfgNode::Slot(destination));
            }
            writes.push(InstantiatedArgWrite {
                dst_arg_index,
                destination,
                sources,
            });
        }
        writes.sort_by_key(|write| (write.dst_arg_index, write.destination));
        unknown_arg_writes.sort_by_key(|write| (write.dst_arg_index, write.destination));

        for dst in unknown_returns {
            self.graph
                .add_base_edge(BaseId::OpaqueReturn { location }, dst);
        }

        for write in &unknown_arg_writes {
            let dst = PfgNode::Slot(write.destination);
            if self.should_skip_unknown_memory_load_on_node(&dst) {
                continue;
            }
            self.graph.add_base_edge(
                BaseId::Unknown {
                    location,
                    reason: UnknownReason::UnsupportedMemoryLoad,
                },
                dst,
            );
        }

        self.call_effects.insert(
            location,
            CallEffects {
                complete: true,
                writes,
                unknown_writes: unknown_arg_writes,
            },
        );

        true
    }

    fn collect_terminator(&mut self, block: BasicBlock, location: Location) {
        let terminator = self.body.basic_blocks[block].terminator();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            return;
        };

        let call = call_name(self.tcx, func);

        if let Some((def_id, _name)) = call.as_ref()
            && let Some(local_def_id) = def_id.as_local()
            && self.collect_summary_call(local_def_id, args, *destination, location)
        {
            return;
        }

        if let Some((def_id, name)) = call.as_ref()
            && let Some(summary) =
                builtin_summary(self.tcx, *def_id, name, args, *destination, self.body)
            && self.apply_summary(&summary, args, *destination, location)
        {
            return;
        }

        if !call
            .as_ref()
            .is_some_and(|(def_id, name)| call_no_writes(self.tcx, *def_id, name))
        {
            // a *mut *mut T argument lets the callee overwrite the pointed-to
            // pointer through the double-pointer, changing its base in the caller
            for arg in args.iter() {
                if let Some(place) = operand_place(&arg.node) {
                    let arg_ty = place.ty(self.body, self.tcx).ty;
                    if let Some(inner) = arg_ty.builtin_deref(true)
                        && count_slots(inner, self.tcx, &mut FxHashSet::default()) > 0
                    {
                        self.add_unknown_pointee_slots(place, location);
                    }
                }
            }
        }

        if let Some((def_id, name)) = call {
            if is_pointer_arithmetic(self.tcx, def_id, &name) {
                let Some(dst) = self.destination_node(*destination, location) else {
                    return;
                };
                if let Some(arg) = args.first() {
                    self.collect_operand_head_flow(&arg.node, dst, location);
                } else {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::UnsupportedCall,
                        },
                        dst,
                    );
                }
                return;
            }

            if call_propagates_first_arg(self.tcx, def_id, &name, args, *destination, self.body) {
                let Some(dst) = self.destination_node(*destination, location) else {
                    return;
                };
                if let Some(arg) = args.first() {
                    self.collect_operand_head_flow(&arg.node, dst, location);
                } else {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::UnsupportedCall,
                        },
                        dst,
                    );
                }
                return;
            }

            if is_as_ptr(self.tcx, def_id, &name)
                && let Some(arg) = args.first()
                && let Some(place) = operand_place(&arg.node)
            {
                if let Some(dst) = self.destination_node(*destination, location) {
                    if let Some(base) = self.local_array_base_from_place(place, location) {
                        self.graph.add_base_edge(base, dst);
                    } else if self.source_node(place).is_some() {
                        self.collect_place_flow(place, dst, false, location);
                    } else {
                        let base = self.base_for_raw_borrow(place, location);
                        self.graph.add_base_edge(base, dst);
                    }
                }
                return;
            }

            if is_heap_alloc_call(self.tcx, def_id, self.alloc_fns) {
                let Some(dst) = self.destination_node(*destination, location) else {
                    return;
                };
                let return_node = PfgNode::CallReturn(location);
                self.graph
                    .add_base_edge(BaseId::HeapAlloc { location }, return_node.clone());
                self.graph.add_edge(return_node, dst.clone());
                self.add_unknown_pointee_slots(*destination, location);
                return;
            }

            if is_null_ptr_call(self.tcx, def_id, &name) {
                if let Some(dst) = self.destination_node(*destination, location) {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::NullLike,
                        },
                        dst,
                    );
                }
                return;
            }
        }

        // generic: one CallReturn node with an add_edge to every slot in the destination range
        let return_node = PfgNode::CallReturn(location);
        self.graph
            .add_base_edge(BaseId::OpaqueReturn { location }, return_node.clone());
        if let Some(slots) = self
            .slot_table
            .place_slots(*destination, self.body, self.tcx)
        {
            for slot in slots {
                self.graph
                    .add_edge(return_node.clone(), PfgNode::Slot(slot));
            }
        }
        self.add_unknown_pointee_slots(*destination, location);
    }

    fn collect_cast(
        &mut self,
        kind: CastKind,
        operand: &Operand<'tcx>,
        dst: PfgNode,
        location: Location,
    ) {
        match kind {
            CastKind::PointerWithExposedProvenance => {
                // `0 as *mut T` is a null pointer sentinel — treat as NullLike so that
                // variables null-initialized via integer cast can participate in groups.
                if is_zero_int_operand(operand, self.tcx) {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::NullLike,
                        },
                        dst,
                    );
                } else {
                    let cast_node = PfgNode::CastResult(location);
                    self.graph
                        .add_base_edge(BaseId::IntToPtr { location }, cast_node.clone());
                    self.graph.add_edge(cast_node, dst);
                }
            }
            CastKind::PointerCoercion(ty::adjustment::PointerCoercion::ArrayToPointer, _) => {
                if let Some(place) = operand_place(operand)
                    && let Some(base) = self.local_array_base_from_place(place, location)
                {
                    let cast_node = PfgNode::CastResult(location);
                    self.graph.add_base_edge(base, cast_node.clone());
                    self.graph.add_edge(cast_node, dst);
                } else {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::UnsupportedProjection,
                        },
                        dst,
                    );
                }
            }
            CastKind::PtrToPtr
            | CastKind::PointerCoercion(ty::adjustment::PointerCoercion::MutToConstPointer, _)
            | CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, _) => {
                self.collect_operand_head_flow(operand, dst, location);
            }
            _ => {
                if operand.constant().is_some() {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::ConstantPointer,
                        },
                        dst,
                    );
                } else {
                    self.collect_operand_head_flow(operand, dst, location);
                }
            }
        }
    }

    fn collect_operand_flow(&mut self, operand: &Operand<'tcx>, dst: PfgNode, location: Location) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.collect_place_flow(*place, dst, true, location);
            }
            Operand::Constant(_) => {
                if is_empty_array_ref_ty(operand.ty(self.body, self.tcx), self.tcx) {
                    return;
                }
                self.graph.add_base_edge(
                    BaseId::Unknown {
                        location,
                        reason: constant_pointer_reason(operand, self.tcx),
                    },
                    dst,
                );
            }
        }
    }

    fn collect_operand_head_flow(
        &mut self,
        operand: &Operand<'tcx>,
        dst: PfgNode,
        location: Location,
    ) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.collect_place_flow(*place, dst, false, location);
            }
            Operand::Constant(_) => {
                if is_empty_array_ref_ty(operand.ty(self.body, self.tcx), self.tcx) {
                    return;
                }
                self.graph.add_base_edge(
                    BaseId::Unknown {
                        location,
                        reason: constant_pointer_reason(operand, self.tcx),
                    },
                    dst,
                );
            }
        }
    }

    fn collect_place_flow(
        &mut self,
        place: Place<'tcx>,
        dst: PfgNode,
        link_tail_slots: bool,
        location: Location,
    ) {
        if let Some(src) = self.source_node(place) {
            self.graph.add_edge(src.clone(), dst.clone());
            if link_tail_slots {
                self.link_tail_slots(place, dst);
            }
        } else {
            self.graph.add_base_edge(
                BaseId::Unknown {
                    location,
                    reason: UnknownReason::UnsupportedProjection,
                },
                dst,
            );
        }
    }

    fn source_slots(&self, place: Place<'tcx>) -> Option<Range<SlotIdx>> {
        let slots = self.slot_table.place_slots(place, self.body, self.tcx)?;
        if slots.is_empty() { None } else { Some(slots) }
    }

    fn destination_slots(&self, place: Place<'tcx>) -> Option<Range<SlotIdx>> {
        let slots = self.slot_table.place_slots(place, self.body, self.tcx)?;
        if slots.is_empty() { None } else { Some(slots) }
    }

    fn source_node(&self, place: Place<'tcx>) -> Option<PfgNode> {
        self.source_slots(place)?.next().map(PfgNode::Slot)
    }

    fn destination_node(&mut self, place: Place<'tcx>, location: Location) -> Option<PfgNode> {
        if let Some(mut slots) = self.destination_slots(place) {
            slots.next().map(PfgNode::Slot)
        } else {
            self.graph.add_base(BaseId::Unknown {
                location,
                reason: UnknownReason::UnsupportedProjection,
            });
            None
        }
    }

    fn add_unknown_pointee_slots(&mut self, place: Place<'tcx>, location: Location) {
        let Some(slots) = self.slot_table.place_slots(place, self.body, self.tcx) else {
            return;
        };
        // Only mark true pointee slots (depth > 0) as unknown; sibling field
        // slots in a struct destination (depth = 0) are NOT pointees and must
        // not be polluted here.
        for slot in slots.skip(1) {
            if self.slot_table.slot_infos[slot].depth == 0 {
                continue;
            }
            if self.should_skip_unknown_memory_load_on_node(&PfgNode::Slot(slot)) {
                continue;
            }
            self.graph.add_base_edge(
                BaseId::Unknown {
                    location,
                    reason: UnknownReason::UnsupportedMemoryLoad,
                },
                PfgNode::Slot(slot),
            );
        }
    }

    fn collect_address_links(
        &mut self,
        destination: Place<'tcx>,
        borrowed: Place<'tcx>,
        _location: Location,
    ) {
        let Some(borrowed_slots) = self.slot_table.place_slots(borrowed, self.body, self.tcx)
        else {
            return;
        };
        let Some(pointee_slots) = self
            .slot_table
            .place_slots(destination, self.body, self.tcx)
            .map(|slots| slots.start + 1..slots.end)
        else {
            return;
        };

        for (borrowed_slot, pointee_slot) in borrowed_slots.zip(pointee_slots) {
            self.graph
                .add_bidirectional_edge(PfgNode::Slot(borrowed_slot), PfgNode::Slot(pointee_slot));
        }
    }

    /// Shared implementation for `Rvalue::Ref` and `Rvalue::RawPtr`.
    ///
    /// When the borrowed place is a simple `*local_ptr` (deref of a raw pointer),
    /// propagate provenance from `local_ptr`'s slot rather than minting a fresh
    /// `RawBorrow` base.
    fn collect_raw_borrow_flow(
        &mut self,
        lhs: Place<'tcx>,
        place: Place<'tcx>,
        dst: PfgNode,
        dst_slots: &std::ops::Range<SlotIdx>,
        location: Location,
    ) {
        // The reborrow pattern `&mut *(_5: *mut T)` gives `_4: &mut T`,
        // and `&raw mut *(_4: &mut T)` gives `_3: *mut T`.
        let propagated = if let [ProjectionElem::Deref] = place.projection.as_ref()
            && (self.local_ty(place.local).is_raw_ptr() || self.local_ty(place.local).is_ref())
            && let Some(slot) = self.slot_table.local_head_slot(place.local)
        {
            self.graph.add_edge(PfgNode::Slot(slot), dst.clone());
            true
        } else {
            false
        };

        if !propagated {
            let base = self.base_for_raw_borrow(place, location);
            self.graph.add_base_edge(base, dst.clone());
        }

        self.collect_address_links(lhs, place, location);

        if self
            .slot_table
            .place_slots(place, self.body, self.tcx)
            .is_none()
        {
            for slot in dst_slots.clone().skip(1) {
                self.graph.add_base_edge(
                    BaseId::Unknown {
                        location,
                        reason: UnknownReason::UnsupportedProjection,
                    },
                    PfgNode::Slot(slot),
                );
            }
        }
    }

    fn link_tail_slots(&mut self, src: Place<'tcx>, dst_head: PfgNode) {
        let Some(dst_slot) = dst_head.as_slot() else {
            return;
        };
        let Some(src_slots) = self.slot_table.place_slots(src, self.body, self.tcx) else {
            return;
        };
        let dst_slots = dst_slot..dst_slot + src_slots.len();

        for (src_slot, dst_slot) in src_slots.skip(1).zip(dst_slots.skip(1)) {
            // propagate direct-param status across copy edges so that UML suppression
            // in add_unknown_pointee_slots also covers slots of param copies
            if self.direct_param_slots.contains(&src_slot) {
                self.direct_param_slots.insert(dst_slot);
            } else if self.direct_param_slots.contains(&dst_slot) {
                self.direct_param_slots.insert(src_slot);
            }
            self.graph
                .add_bidirectional_edge(PfgNode::Slot(src_slot), PfgNode::Slot(dst_slot));
        }
    }

    fn base_for_raw_borrow(&self, place: Place<'tcx>, location: Location) -> BaseId {
        if let Some(base) = self.local_array_base_from_place(place, location) {
            return base;
        }

        if place.projection.is_empty() && !self.local_ty(place.local).is_raw_ptr() {
            return BaseId::LocalScalar { local: place.local };
        }

        BaseId::RawBorrow {
            target: self.slot_table.place_head_slot(place, self.body, self.tcx),
            location,
        }
    }

    fn local_array_base_from_place(
        &self,
        place: Place<'tcx>,
        _location: Location,
    ) -> Option<BaseId> {
        if place.projection.iter().any(is_array_projection) {
            return Some(BaseId::LocalArray { local: place.local });
        }

        self.array_source_for_local(place.local, &mut FxHashSet::default())
            .map(|local| BaseId::LocalArray { local })
    }

    fn array_source_for_local(
        &self,
        local: Local,
        visited: &mut FxHashSet<Local>,
    ) -> Option<Local> {
        if !visited.insert(local) {
            return None;
        }

        if matches!(self.local_ty(local).kind(), ty::TyKind::Array(..)) {
            return Some(local);
        }

        for rhs in self.rhs_map.get(&local).into_iter().flatten() {
            match rhs {
                AssignRhs::ArrayBorrow(place) => {
                    if matches!(self.local_ty(place.local).kind(), ty::TyKind::Array(..))
                        || place.projection.iter().any(is_array_projection)
                        || matches!(
                            place.ty(self.body, self.tcx).ty.kind(),
                            ty::TyKind::Array(..)
                        )
                    {
                        return Some(place.local);
                    }
                }
                AssignRhs::Follow(src_local) => {
                    if let Some(array_local) = self.array_source_for_local(*src_local, visited) {
                        return Some(array_local);
                    }
                }
            }
        }

        None
    }

    fn local_ty(&self, local: Local) -> Ty<'tcx> {
        self.body.local_decls[local].ty
    }
}

#[allow(clippy::too_many_arguments)]
fn collect_slot_infos<'tcx>(
    root: Local,
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    path: &mut Vec<SlotPathElem>,
    depth: usize,
    qualifier_context: &mut QualifierContext,
    seen_adts: &mut FxHashSet<DefId>,
    out: &mut Vec<SlotInfo>,
) {
    if let Some(inner_ty) = ty.builtin_deref(true) {
        let qualifier_key = qualifier_context.next_key();
        out.push(SlotInfo {
            root,
            path: path.clone(),
            depth,
            qualifier_key,
        });
        path.push(SlotPathElem::Pointee);
        collect_slot_infos(
            root,
            inner_ty,
            tcx,
            path,
            depth + 1,
            qualifier_context,
            seen_adts,
            out,
        );
        path.pop();
        return;
    }

    if let Some(inner_ty) = ty.builtin_index() {
        path.push(SlotPathElem::Element);
        collect_slot_infos(
            root,
            inner_ty,
            tcx,
            path,
            depth,
            qualifier_context,
            seen_adts,
            out,
        );
        path.pop();
        return;
    }

    match ty.kind() {
        ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() && !adt_def.is_union() => {
            let def_id = adt_def.did();
            if !seen_adts.insert(def_id) {
                return;
            }
            for (idx, field) in adt_def.all_fields().enumerate() {
                let mut field_qualifier_context =
                    match def_id
                        .as_local()
                        .map(|local_def_id| QualifierContext::StructField {
                            def_id: local_def_id,
                            field: FieldIdx::from_usize(idx),
                            next_offset: 0,
                        }) {
                        Some(context) => context,
                        None => QualifierContext::None,
                    };
                path.push(SlotPathElem::Field(FieldIdx::from_usize(idx)));
                collect_slot_infos(
                    root,
                    field.ty(tcx, substs),
                    tcx,
                    path,
                    depth,
                    &mut field_qualifier_context,
                    seen_adts,
                    out,
                );
                path.pop();
            }
            seen_adts.remove(&def_id);
        }
        ty::TyKind::Tuple(tys) => {
            for (idx, field_ty) in tys.iter().enumerate() {
                path.push(SlotPathElem::Field(FieldIdx::from_usize(idx)));
                collect_slot_infos(
                    root,
                    field_ty,
                    tcx,
                    path,
                    depth,
                    qualifier_context,
                    seen_adts,
                    out,
                );
                path.pop();
            }
        }
        _ => {}
    }
}

#[derive(Clone, Debug)]
enum QualifierContext {
    Local {
        next_offset: usize,
    },
    StructField {
        def_id: LocalDefId,
        field: FieldIdx,
        next_offset: usize,
    },
    None,
}

impl QualifierContext {
    fn next_key(&mut self) -> Option<QualifierKey> {
        match self {
            QualifierContext::Local { next_offset } => {
                let offset = *next_offset;
                *next_offset += 1;
                Some(QualifierKey::Local { offset })
            }
            QualifierContext::StructField {
                def_id,
                field,
                next_offset,
            } => {
                let offset = *next_offset;
                *next_offset += 1;
                Some(QualifierKey::StructField {
                    def_id: *def_id,
                    field: *field,
                    offset,
                })
            }
            QualifierContext::None => None,
        }
    }
}

fn count_slots<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>, seen_adts: &mut FxHashSet<DefId>) -> usize {
    if let Some(inner_ty) = ty.builtin_deref(true) {
        return 1 + count_slots(inner_ty, tcx, seen_adts);
    }

    if let Some(inner_ty) = ty.builtin_index() {
        return count_slots(inner_ty, tcx, seen_adts);
    }

    match ty.kind() {
        ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() && !adt_def.is_union() => {
            let def_id = adt_def.did();
            if !seen_adts.insert(def_id) {
                return 0;
            }
            let count = adt_def
                .all_fields()
                .map(|field| count_slots(field.ty(tcx, substs), tcx, seen_adts))
                .sum();
            seen_adts.remove(&def_id);
            count
        }
        ty::TyKind::Tuple(tys) => tys
            .iter()
            .map(|field_ty| count_slots(field_ty, tcx, seen_adts))
            .sum(),
        _ => 0,
    }
}

fn field_slot_offset<'tcx>(base_ty: Ty<'tcx>, field: FieldIdx, tcx: TyCtxt<'tcx>) -> Option<usize> {
    match base_ty.kind() {
        ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() && !adt_def.is_union() => {
            let mut offset = 0;
            let mut seen = FxHashSet::default();
            for field_def in adt_def.all_fields().take(field.index()) {
                seen.clear();
                offset += count_slots(field_def.ty(tcx, substs), tcx, &mut seen);
            }
            Some(offset)
        }
        ty::TyKind::Tuple(tys) => {
            let mut seen = FxHashSet::default();
            Some(
                tys.iter()
                    .take(field.index())
                    .map(|field_ty| {
                        seen.clear();
                        count_slots(field_ty, tcx, &mut seen)
                    })
                    .sum(),
            )
        }
        _ => None,
    }
}

fn is_array_projection(elem: ProjectionElem<Local, Ty<'_>>) -> bool {
    matches!(
        elem,
        ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
    )
}

fn operand_place<'tcx>(operand: &Operand<'tcx>) -> Option<Place<'tcx>> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(*place),
        Operand::Constant(_) => None,
    }
}

fn call_name(tcx: TyCtxt<'_>, func: &Operand<'_>) -> Option<(DefId, String)> {
    let constant = func.constant()?;
    let ty = constant.ty();
    let ty::TyKind::FnDef(def_id, _) = ty.kind() else {
        return None;
    };
    Some((*def_id, tcx.def_path_str(*def_id)))
}

/// Returns true only for the core/std inherent raw-pointer arithmetic
/// methods. The crate and `::ptr::` path checks keep user-defined functions
/// that merely share these names (common in translated C code, e.g. a free
/// function `add`) from being granted base-preserving semantics.
fn is_pointer_arithmetic(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std")
        && name.contains("::ptr::")
        && matches!(
            name.rsplit("::").next(),
            Some(
                "offset"
                    | "wrapping_offset"
                    | "byte_offset"
                    | "wrapping_byte_offset"
                    | "add"
                    | "wrapping_add"
                    | "sub"
                    | "wrapping_sub"
            )
        )
}

fn is_as_ptr(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std")
        && (name.contains("::slice::") || name.contains("::array::"))
        && matches!(name.rsplit("::").next(), Some("as_ptr" | "as_mut_ptr"))
}

fn call_no_writes(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std")
        && name.contains("::ptr::")
        && matches!(name.rsplit("::").next(), Some("is_null"))
}

fn is_null_ptr_call(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std")
        && matches!(name.rsplit("::").next(), Some("null" | "null_mut"))
}

/// Returns true when `operand` is the integer constant zero, i.e. `0 as *mut T`.
fn is_zero_int_operand<'tcx>(operand: &Operand<'tcx>, _tcx: TyCtxt<'tcx>) -> bool {
    let Some(const_op) = operand.constant() else {
        return false;
    };
    let Some(scalar) = const_op.const_.try_to_scalar() else {
        return false;
    };
    let Ok(int_val) = scalar.try_to_scalar_int() else {
        return false;
    };
    int_val.to_bits(int_val.size()) == 0
}

fn constant_pointer_reason<'tcx>(operand: &Operand<'tcx>, tcx: TyCtxt<'tcx>) -> UnknownReason {
    if is_zero_int_operand(operand, tcx) {
        UnknownReason::NullLike
    } else {
        UnknownReason::ConstantPointer
    }
}

fn builtin_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
    args: &[Spanned<Operand<'tcx>>],
    destination: Place<'tcx>,
    body: &Body<'tcx>,
) -> Option<FunctionSummary> {
    if !tcx.is_foreign_item(def_id) {
        return None;
    }
    let last = name.rsplit("::").next()?;
    let arg0_is_ptr = args
        .first()
        .is_some_and(|arg| arg.node.ty(body, tcx).is_raw_ptr());
    let dst_is_ptr = destination.ty(body, tcx).ty.is_raw_ptr();
    let base_preserving = || FunctionSummary {
        completeness: SummaryCompleteness::Complete,
        return_flows: vec![
            SummaryFlow {
                dst_return_path: vec![],
                src: SummarySource::ParamSlot {
                    arg_index: 0,
                    path: vec![],
                },
            },
            SummaryFlow {
                dst_return_path: vec![],
                src: SummarySource::Unknown(UnknownReason::NullLike),
            },
        ],
        ..FunctionSummary::default()
    };
    let empty_complete = || FunctionSummary {
        completeness: SummaryCompleteness::Complete,
        ..FunctionSummary::default()
    };
    match last {
        // base-preserving, null-on-miss: returns a cursor into arg0 or null.
        "strstr" | "strchr" | "strrchr" | "strpbrk"
            if args.len() == 2 && arg0_is_ptr && dst_is_ptr =>
        {
            Some(base_preserving())
        }
        "memchr" if args.len() == 3 && arg0_is_ptr && dst_is_ptr => Some(base_preserving()),
        // read-only: no pointer return, no pointer-changing arg writes.
        "strlen" if args.len() == 1 && arg0_is_ptr => Some(empty_complete()),
        "strcmp" if args.len() == 2 && arg0_is_ptr => Some(empty_complete()),
        "strncmp" | "memcmp" if args.len() == 3 && arg0_is_ptr => Some(empty_complete()),
        _ => None,
    }
}

fn call_propagates_first_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
    args: &[Spanned<Operand<'tcx>>],
    destination: Place<'tcx>,
    body: &Body<'tcx>,
) -> bool {
    is_from_raw_parts_mut_call(tcx, def_id, name, args, destination, body)
        || is_slice_index_mut_call(tcx, def_id, name, args, destination, body)
}

fn is_from_raw_parts_mut_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
    args: &[Spanned<Operand<'tcx>>],
    destination: Place<'tcx>,
    body: &Body<'tcx>,
) -> bool {
    matches!(name.rsplit("::").next(), Some("from_raw_parts_mut"))
        && is_core_or_std_from_raw_parts_mut_path(tcx, def_id, name)
        && args
            .first()
            .is_some_and(|arg| arg.node.ty(body, tcx).is_raw_ptr())
        && is_mut_slice_ref_ty(destination.ty(body, tcx).ty)
}

fn is_slice_index_mut_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
    args: &[Spanned<Operand<'tcx>>],
    destination: Place<'tcx>,
    body: &Body<'tcx>,
) -> bool {
    matches!(name.rsplit("::").next(), Some("index_mut"))
        && is_core_or_std_slice_index_mut_path(tcx, def_id, name)
        && args
            .first()
            .and_then(|arg| operand_place(&arg.node))
            .is_some_and(|place| is_mut_slice_ref_ty(place.ty(body, tcx).ty))
        && is_mut_slice_ref_ty(destination.ty(body, tcx).ty)
}

fn is_core_or_std_from_raw_parts_mut_path(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std")
        && name.contains("::slice::")
        && name.ends_with("::from_raw_parts_mut")
}

fn is_core_or_std_slice_index_mut_path(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std") && name.ends_with("::ops::IndexMut::index_mut")
}

fn is_mut_slice_ref_ty(ty: Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::Ref(_, inner_ty, mutability)
            if mutability.is_mut() && matches!(inner_ty.kind(), ty::TyKind::Slice(_))
    )
}

fn is_empty_array_ref_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let ty::TyKind::Ref(_, inner_ty, _) = ty.kind() else {
        return false;
    };
    let ty::TyKind::Array(_, len) = inner_ty.kind() else {
        return false;
    };
    len.try_to_target_usize(tcx) == Some(0)
}

/// Returns true for allocator shims found by Andersen pre-analysis and for
/// the foreign libc allocators. A local Rust function that merely shares an
/// allocator name gets no heap-alloc provenance.
fn is_heap_alloc_call(tcx: TyCtxt<'_>, def_id: DefId, alloc_fns: &FxHashSet<LocalDefId>) -> bool {
    def_id
        .as_local()
        .is_some_and(|local_def_id| alloc_fns.contains(&local_def_id))
        || tcx.is_foreign_item(def_id)
            && matches!(
                tcx.item_name(def_id).as_str(),
                "malloc" | "calloc" | "realloc"
            )
}

/// Returns `(base_local, slot_offset_within_local)` for `DirectlyRewriteable` bases.
/// Returns `None` for `RawBorrow { target: None }` (no trackable local).
fn base_local_of_base(base: &BaseId, slot_table: &SlotTable) -> Option<(Local, usize)> {
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

fn solve_reachable_bases(graph: &PointerFlowGraph) -> ProvenanceResult {
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

fn summary_source_for_base(base: &BaseId, result: &ArrayLocalProvenance) -> SummarySource {
    match base {
        BaseId::Param { local, slot } => {
            let arg_index = param_index_for_local(*local).unwrap_or(0);
            let path = result
                .slot_table
                .slot_infos
                .get(*slot)
                .map(|info| info.path.clone())
                .unwrap_or_default();
            SummarySource::ParamSlot { arg_index, path }
        }
        BaseId::HeapAlloc { .. } => SummarySource::HeapAlloc,
        BaseId::OpaqueReturn { .. } => SummarySource::OpaqueReturn,
        BaseId::Unknown { reason, .. } => SummarySource::Unknown(reason.clone()),
        BaseId::IntToPtr { .. } => SummarySource::Unknown(UnknownReason::ConstantPointer),
        BaseId::LocalArray { .. } | BaseId::LocalScalar { .. } | BaseId::RawBorrow { .. } => {
            SummarySource::Unknown(UnknownReason::UnsupportedMemoryLoad)
        }
    }
}

fn param_index_for_local(local: Local) -> Option<usize> {
    let index = local.index();
    (index > 0).then_some(index - 1)
}

fn slot_path_from_projection<V, T>(
    projection: &[ProjectionElem<V, T>],
) -> Option<Vec<SlotPathElem>> {
    projection
        .iter()
        .map(|elem| match elem {
            ProjectionElem::Deref => Some(SlotPathElem::Pointee),
            ProjectionElem::Field(field, _) => Some(SlotPathElem::Field(*field)),
            ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. } => Some(SlotPathElem::Element),
            _ => None,
        })
        .collect()
}

fn is_arg_target_initial_base(
    base: &BaseId,
    target: &ArgWriteTarget,
    result: &ArrayLocalProvenance,
) -> bool {
    matches!(
        base,
        BaseId::Param {
            local,
            slot,
        } if param_index_for_local(*local) == Some(target.arg_index)
            && result
                .slot_table
                .slot_infos
                .get(*slot)
                .is_some_and(|info| info.path == target.path)
    )
}

fn return_slot_paths<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    result: &ArrayLocalProvenance,
) -> Vec<(SlotIdx, Vec<SlotPathElem>)> {
    result
        .slot_table
        .place_slots(Place::return_place(), body, tcx)
        .map(|slots| {
            slots
                .filter_map(|slot| {
                    result
                        .slot_table
                        .slot_infos
                        .get(slot)
                        .map(|info| (slot, info.path.clone()))
                })
                .collect()
        })
        .unwrap_or_default()
}

enum BoundaryWriteDiscovery {
    NotBoundary,
    Complete(Vec<(ArgWriteTarget, SlotIdx)>),
    Incomplete,
}

struct BoundaryArgWrites {
    targets: Vec<(ArgWriteTarget, SlotIdx)>,
    complete: bool,
}

fn boundary_arg_write_targets_for_place<'tcx>(
    place: Place<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    result: &ArrayLocalProvenance,
) -> BoundaryWriteDiscovery {
    let Some(deref_index) = place
        .projection
        .iter()
        .position(|elem| matches!(elem, ProjectionElem::Deref))
    else {
        return BoundaryWriteDiscovery::NotBoundary;
    };

    let prefix_projection = &place.projection[..deref_index];
    if slot_path_from_projection(prefix_projection).is_none() {
        return BoundaryWriteDiscovery::Incomplete;
    }

    let prefix_place = Place::from(place.local).project_deeper(prefix_projection, tcx);
    let Some(prefix_slot) = result
        .slot_table
        .place_slots(prefix_place, body, tcx)
        .and_then(|mut slots| slots.next())
    else {
        return BoundaryWriteDiscovery::Incomplete;
    };

    let Some(written_slots) = result.slot_table.place_slots(place, body, tcx) else {
        return BoundaryWriteDiscovery::Incomplete;
    };

    let writes = boundary_param_write_targets_for_slots(prefix_slot, written_slots, result);
    if !writes.complete {
        BoundaryWriteDiscovery::Incomplete
    } else if writes.targets.is_empty() {
        BoundaryWriteDiscovery::NotBoundary
    } else {
        BoundaryWriteDiscovery::Complete(writes.targets)
    }
}

fn boundary_param_write_targets_for_slots(
    prefix_slot: SlotIdx,
    written_slots: impl IntoIterator<Item = SlotIdx>,
    result: &ArrayLocalProvenance,
) -> BoundaryArgWrites {
    let Some(prefix_path) = result
        .slot_table
        .slot_infos
        .get(prefix_slot)
        .map(|info| info.path.clone())
    else {
        return BoundaryArgWrites {
            targets: vec![],
            complete: false,
        };
    };
    let Some(bases) = result
        .provenance
        .reachable_bases
        .get(&PfgNode::Slot(prefix_slot))
    else {
        return BoundaryArgWrites {
            targets: vec![],
            complete: false,
        };
    };

    let param_bases: Vec<_> = bases
        .iter()
        .filter_map(|base| {
            let BaseId::Param { local, slot } = base else {
                return None;
            };
            Some((*local, *slot))
        })
        .collect();
    if param_bases.is_empty() {
        return BoundaryArgWrites {
            targets: vec![],
            complete: true,
        };
    }

    let mut targets = vec![];
    for slot in written_slots {
        let Some(info) = result.slot_table.slot_infos.get(slot) else {
            return BoundaryArgWrites {
                targets,
                complete: false,
            };
        };
        let Some(relative_path) = info.path.as_slice().strip_prefix(prefix_path.as_slice()) else {
            return BoundaryArgWrites {
                targets,
                complete: false,
            };
        };
        if relative_path.is_empty() {
            return BoundaryArgWrites {
                targets,
                complete: false,
            };
        }
        for (local, base_slot) in &param_bases {
            let Some(arg_index) = param_index_for_local(*local) else {
                return BoundaryArgWrites {
                    targets,
                    complete: false,
                };
            };
            let Some(base_path) = result
                .slot_table
                .slot_infos
                .get(*base_slot)
                .map(|info| info.path.clone())
            else {
                return BoundaryArgWrites {
                    targets,
                    complete: false,
                };
            };
            let mut target_path = base_path;
            target_path.extend(relative_path.iter().cloned());
            targets.push((
                ArgWriteTarget {
                    arg_index,
                    path: target_path,
                },
                slot,
            ));
        }
    }

    BoundaryArgWrites {
        targets,
        complete: true,
    }
}

fn boundary_unknown_call_arg_write_targets_for_place<'tcx>(
    place: Place<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    result: &ArrayLocalProvenance,
) -> Vec<ArgWriteTarget> {
    let Some(place_slots) = result.slot_table.place_slots(place, body, tcx) else {
        return vec![];
    };
    let Some(prefix_slot) = place_slots.clone().next() else {
        return vec![];
    };

    boundary_param_write_targets_for_slots(
        prefix_slot,
        place_slots.skip(1).filter(|slot| {
            result
                .slot_table
                .slot_infos
                .get(*slot)
                .is_some_and(|info| info.depth > 0)
        }),
        result,
    )
    .targets
    .into_iter()
    .map(|(target, _slot)| target)
    .collect()
}

fn boundary_arg_write_targets<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    result: &ArrayLocalProvenance,
) -> BoundaryArgWrites {
    let mut targets = vec![];
    let mut complete = true;

    for (_block, block_data) in body.basic_blocks.iter_enumerated() {
        for statement in &block_data.statements {
            let StatementKind::Assign(box (place, _)) = &statement.kind else {
                continue;
            };
            match boundary_arg_write_targets_for_place(*place, body, tcx, result) {
                BoundaryWriteDiscovery::NotBoundary => {}
                BoundaryWriteDiscovery::Complete(discovered) => targets.extend(discovered),
                BoundaryWriteDiscovery::Incomplete => complete = false,
            }
        }
    }

    BoundaryArgWrites { targets, complete }
}

fn boundary_unknown_arg_write_targets<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    result: &ArrayLocalProvenance,
) -> Vec<ArgWriteTarget> {
    let mut targets = vec![];

    for (_block, block_data) in body.basic_blocks.iter_enumerated() {
        let Some(terminator) = &block_data.terminator else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            continue;
        };
        if call_name(tcx, func)
            .as_ref()
            .is_some_and(|(def_id, name)| call_no_writes(tcx, *def_id, name))
        {
            continue;
        }

        for arg in args {
            let Some(place) = operand_place(&arg.node) else {
                continue;
            };
            let arg_ty = place.ty(body, tcx).ty;
            if let Some(inner) = arg_ty.builtin_deref(true)
                && count_slots(inner, tcx, &mut FxHashSet::default()) > 0
            {
                targets.extend(boundary_unknown_call_arg_write_targets_for_place(
                    place, body, tcx, result,
                ));
            }
        }
    }

    targets
}

fn build_function_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    _def_id: LocalDefId,
    body: &Body<'tcx>,
    result: &ArrayLocalProvenance,
) -> FunctionSummary {
    let mut summary = FunctionSummary {
        completeness: SummaryCompleteness::Complete,
        ..FunctionSummary::default()
    };

    for (slot, path) in return_slot_paths(body, tcx, result) {
        let node = PfgNode::Slot(slot);
        let Some(bases) = result.provenance.reachable_bases.get(&node) else {
            summary.unknown_return_slots.push(path);
            continue;
        };
        let mut emitted = false;
        for base in bases {
            let src = summary_source_for_base(base, result);
            summary.return_flows.push(SummaryFlow {
                dst_return_path: path.clone(),
                src,
            });
            emitted = true;
        }
        if !emitted {
            summary.unknown_return_slots.push(path);
        }
    }

    let boundary_writes = boundary_arg_write_targets(body, tcx, result);
    if !boundary_writes.complete {
        summary.completeness = SummaryCompleteness::Incomplete;
    }
    for (target, written_slot) in boundary_writes.targets {
        let Some(bases) = result
            .provenance
            .reachable_bases
            .get(&PfgNode::Slot(written_slot))
        else {
            summary.unknown_arg_writes.push(target);
            continue;
        };

        let mut emitted = false;
        let has_non_initial_base = bases
            .iter()
            .any(|base| !is_arg_target_initial_base(base, &target, result));
        for base in bases {
            if has_non_initial_base && is_arg_target_initial_base(base, &target, result) {
                continue;
            }
            let src = summary_source_for_base(base, result);
            summary.arg_write_flows.push(ArgWriteFlow {
                dst_arg_index: target.arg_index,
                dst_path: target.path.clone(),
                src,
            });
            emitted = true;
        }

        if !emitted {
            summary.unknown_arg_writes.push(target);
        }
    }

    for target in boundary_unknown_arg_write_targets(body, tcx, result) {
        summary.unknown_arg_writes.push(target);
    }

    summary.normalize();
    summary
}

fn classify_base(base: &BaseId) -> BaseClassification {
    let (admissibility, reason) = match base {
        BaseId::Param { .. } => (
            BaseAdmissibility::DirectlyRewriteable,
            "raw pointer parameter; later rewrite must provide length/bounds evidence",
        ),
        BaseId::LocalArray { .. } => (
            BaseAdmissibility::DirectlyRewriteable,
            "local array pointer can later become array/slice indexing",
        ),
        BaseId::LocalScalar { .. } => (
            BaseAdmissibility::DirectlyRewriteable,
            "local scalar raw borrow can later become direct local access",
        ),
        BaseId::RawBorrow { target, .. } => (
            BaseAdmissibility::DirectlyRewriteable,
            if target.is_none() {
                "raw borrow has unique provenance but unresolved target must be validated before rewrite"
            } else {
                "raw borrow has a known local slot"
            },
        ),
        BaseId::HeapAlloc { .. } => (
            BaseAdmissibility::RewriteableWithOwnershipTransform,
            "heap allocation requires consistent allocation/free ownership transform",
        ),
        BaseId::OpaqueReturn { .. } => (
            BaseAdmissibility::TrackOnly,
            "opaque pointer return has unknown size, ownership, validity, nullability, and aliasing",
        ),
        BaseId::IntToPtr { .. } => (
            BaseAdmissibility::Reject,
            "integer-to-pointer cast has no known safe Rust allocation object",
        ),
        BaseId::Unknown { reason, .. } => (
            BaseAdmissibility::Reject,
            match reason {
                UnknownReason::NullLike => "null-like pointer constant has no rewriteable base",
                UnknownReason::ConstantPointer => "constant pointer value has unknown provenance",
                UnknownReason::UnsupportedProjection => {
                    "unsupported projection prevents precise provenance"
                }
                UnknownReason::UnsupportedMemoryLoad => {
                    "unsupported memory load prevents precise provenance"
                }
                UnknownReason::UnsupportedCall => "unsupported call prevents precise provenance",
            },
        ),
    };

    BaseClassification {
        base: base.clone(),
        admissibility,
        reason: reason.to_string(),
    }
}

#[cfg(test)]
mod tests;
