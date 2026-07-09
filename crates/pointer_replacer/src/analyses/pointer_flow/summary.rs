use rustc_abi::FieldIdx;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{Body, Local, Place, ProjectionElem, StatementKind, TerminatorKind},
    ty::TyCtxt,
};

use crate::analyses::pointer_flow::{
    PointerFlowResult,
    builtin::{call_name, call_no_writes},
    collector::operand_place,
    field_access::{FieldAccessKind, FieldAccessRejectKind},
    graph::{BaseId, PfgNode, UnknownReason},
    slots::{SlotIdx, SlotPathElem, count_slots, slot_path_from_projection},
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FunctionSummary {
    pub(crate) completeness: SummaryCompleteness,
    pub(crate) return_flows: Vec<SummaryFlow>,
    pub(crate) arg_write_flows: Vec<ArgWriteFlow>,
    pub(crate) unknown_return_slots: Vec<Vec<SlotPathElem>>,
    pub(crate) unknown_arg_writes: Vec<ArgWriteTarget>,
    pub(crate) param_field_accesses: Vec<ParamFieldAccessFlow>,
    pub(crate) param_field_rejects: Vec<ParamFieldRejectFlow>,
}

impl FunctionSummary {
    pub(crate) fn is_complete(&self) -> bool {
        self.completeness == SummaryCompleteness::Complete
    }

    pub(crate) fn normalize(&mut self) {
        self.return_flows.sort();
        self.return_flows.dedup();
        self.arg_write_flows.sort();
        self.arg_write_flows.dedup();
        self.unknown_return_slots.sort();
        self.unknown_return_slots.dedup();
        self.unknown_arg_writes.sort();
        self.unknown_arg_writes.dedup();
        self.param_field_accesses.sort();
        self.param_field_accesses.dedup();
        self.param_field_rejects.sort();
        self.param_field_rejects.dedup();
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum SummaryCompleteness {
    Complete,
    #[default]
    Incomplete,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct SummaryFlow {
    pub(crate) dst_return_path: Vec<SlotPathElem>,
    pub(crate) src: SummarySource,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ArgWriteFlow {
    pub(crate) dst_arg_index: usize,
    pub(crate) dst_path: Vec<SlotPathElem>,
    pub(crate) src: SummarySource,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ArgWriteTarget {
    pub(crate) arg_index: usize,
    pub(crate) path: Vec<SlotPathElem>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SummarySource {
    ParamSlot {
        arg_index: usize,
        path: Vec<SlotPathElem>,
    },
    Unknown(UnknownReason),
    OpaqueReturn,
    HeapAlloc,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ParamFieldAccessFlow {
    pub(crate) src: SummarySource,
    pub(crate) field: FieldIdx,
    pub(crate) kind: FieldAccessKind,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ParamFieldRejectFlow {
    pub(crate) src: SummarySource,
    pub(crate) kind: FieldAccessRejectKind,
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

fn summary_source_for_base(base: &BaseId, result: &PointerFlowResult) -> SummarySource {
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

fn is_arg_target_initial_base(
    base: &BaseId,
    target: &ArgWriteTarget,
    result: &PointerFlowResult,
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
    result: &PointerFlowResult,
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
    result: &PointerFlowResult,
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
    result: &PointerFlowResult,
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
    result: &PointerFlowResult,
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
    result: &PointerFlowResult,
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
    result: &PointerFlowResult,
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

pub(crate) fn build_function_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    _def_id: LocalDefId,
    body: &Body<'tcx>,
    result: &PointerFlowResult,
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

    // field events on nodes that reach a param base cross the function boundary;
    // events on unknown/non-param bases stay visible in this body's own result
    for access in &result.field_accesses {
        let Some(bases) = result.provenance.reachable_bases.get(&access.node) else {
            continue;
        };
        for base in bases {
            if matches!(base, BaseId::Param { .. }) {
                summary.param_field_accesses.push(ParamFieldAccessFlow {
                    src: summary_source_for_base(base, result),
                    field: access.field,
                    kind: access.kind,
                });
            }
        }
    }
    for reject in &result.field_rejects {
        let Some(bases) = result.provenance.reachable_bases.get(&reject.node) else {
            continue;
        };
        for base in bases {
            if matches!(base, BaseId::Param { .. }) {
                summary.param_field_rejects.push(ParamFieldRejectFlow {
                    src: summary_source_for_base(base, result),
                    kind: reject.kind,
                });
            }
        }
    }

    summary.normalize();
    summary
}
