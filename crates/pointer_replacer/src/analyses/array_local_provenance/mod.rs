//! MIR raw-array local provenance graph to find base pointers.
//!
//! This analysis is intentionally not location-sensitive yet: each MIR local is
//! represented by one graph node for the whole body. This may merge separate
//! definitions of the same local and conservatively reject rewriteable regions.

use std::fmt::Write as _;

use points_to::andersen;
use rustc_abi::FieldIdx;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::{
    mir::{
        self, Body, Local, Location, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{self, Ty, TyCtxt},
};
use rustc_mir_dataflow::Analysis;

pub(crate) use crate::analyses::pointer_flow::summary::CallEffects;
pub use crate::analyses::pointer_flow::{
    PointerFlowResult,
    graph::{BaseId, PfgNode, PointerFlowGraph, ProvenanceResult, UnknownReason},
    slots::{QualifierKey, SlotIdx, SlotInfo, SlotPathElem, SlotTable},
};
use crate::{
    analyses::{
        liveness::MaybeLiveLocals,
        mir_variable_grouping::SourceVarGroups,
        pointer_flow::{
            builtin::{call_name, call_no_writes, is_as_ptr, is_pointer_arithmetic},
            collector::operand_place,
            graph::base_local_of_base,
            slots::{count_slots, slot_path_from_place, slot_ty},
        },
        type_qualifier::foster::mutability::{Mutability as PtrMut, MutabilityResult},
    },
    utils::rustc::RustProgram,
};

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

#[derive(Clone, Debug)]
pub struct ArrayLocalProvenance {
    pub flow: PointerFlowResult,
    pub base_classifications: FxHashMap<BaseId, BaseClassification>,
}

impl ArrayLocalProvenance {
    pub fn slot_table(&self) -> &SlotTable {
        &self.flow.slot_table
    }

    #[allow(dead_code)]
    pub fn graph(&self) -> &PointerFlowGraph {
        &self.flow.graph
    }

    pub fn provenance(&self) -> &ProvenanceResult {
        &self.flow.provenance
    }

    pub(crate) fn call_effects(&self) -> &FxHashMap<Location, CallEffects> {
        &self.flow.call_effects
    }
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

#[allow(dead_code)]
impl ArrayLocalProvenance {
    pub fn unique_base(&self, node: &PfgNode) -> Option<BaseId> {
        self.provenance().unique_base(node)
    }

    pub fn unique_base_of_local(&self, local: Local) -> Option<BaseId> {
        let slot = self.slot_table().local_head_slot(local)?;
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
            let Some(slot) = self.slot_table().local_head_slot(local) else {
                continue;
            };
            let node = PfgNode::Slot(slot);
            let bases = self
                .provenance()
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
    crate::analyses::pointer_flow::pointer_flow_analysis(input, alloc_fns)
        .into_iter()
        .map(|(def_id, flow)| (def_id, wrap_flow(flow)))
        .collect()
}

#[cfg(test)]
pub fn analyze_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
    alloc_fns: &FxHashSet<LocalDefId>,
) -> ArrayLocalProvenance {
    let flow = crate::analyses::pointer_flow::collector::analyze_body_with_summaries(
        tcx, def_id, body, alloc_fns, None,
    );
    wrap_flow(flow)
}

fn wrap_flow(flow: crate::analyses::pointer_flow::PointerFlowResult) -> ArrayLocalProvenance {
    let base_classifications = flow
        .graph
        .bases
        .iter()
        .map(|base| (base.clone(), classify_base(base)))
        .collect();
    ArrayLocalProvenance {
        flow,
        base_classifications,
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

        let Some((base_local, base_slot_offset)) =
            base_local_of_base(base, provenance.slot_table())
        else {
            continue;
        };

        // collect all slots whose unique reachable base is this base
        let members: Vec<SlotIdx> = provenance
            .slot_table()
            .slot_infos
            .iter()
            .enumerate()
            .filter_map(|(slot_idx, _)| {
                let node = PfgNode::Slot(slot_idx);
                if provenance.provenance().unique_non_null_base(&node).as_ref() == Some(base) {
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
            let info = &provenance.slot_table().slot_infos[slot_idx];
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
        let Some(info) = provenance.slot_table().slot_infos.get(slot_idx) else {
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
    let slots = provenance.slot_table().local_slots(local);
    let slot = slots.start.checked_add(slot_offset)?;
    let info = provenance.slot_table().slot_infos.get(slot)?;
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
    let effects = provenance.call_effects().get(&location)?;
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
            .slot_table()
            .place_slots(place, body, tcx)?
            .next()?;
        let bases = provenance
            .provenance()
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
            roots.insert(provenance.slot_table().slot_infos.get(*target)?.root);
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
                    _ => provenance.provenance().unique_non_null_base(source),
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
        .filter_map(|slot| context.provenance.slot_table().slot_infos.get(*slot))
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
                    if context.provenance.call_effects().contains_key(&location) {
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
        .slot_table()
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
    let info = provenance.slot_table().slot_infos.get(slot)?;
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
    let Some(slots) = provenance.slot_table().place_slots(place, body, tcx) else {
        return true;
    };

    for slot in slots {
        let Some(info) = provenance.slot_table().slot_infos.get(slot) else {
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
        .slot_table()
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
        .filter_map(|slot| provenance.slot_table().slot_infos.get(*slot))
        .map(|info| info.root)
        .filter(|local| member_roots.contains(local))
        .filter(|local| *local != base_local)
        .collect()
}

pub(crate) fn base_slot_info<'a>(
    provenance: &'a ArrayLocalProvenance,
    group: &RewriteGroup,
) -> Option<&'a SlotInfo> {
    let slots = provenance.slot_table().local_slots(group.base_local);
    let base_slot = slots.start.checked_add(group.base_slot_offset)?;
    if base_slot >= slots.end {
        return None;
    }
    provenance.slot_table().slot_infos.get(base_slot)
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
    for (slot_idx, info) in provenance.slot_table().slot_infos.iter().enumerate() {
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
        let info = &provenance.slot_table().slot_infos[slot_idx];
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
        let info = &provenance.slot_table().slot_infos[slot_idx];
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
            let info = &provenance.slot_table().slot_infos[slot_idx];
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
