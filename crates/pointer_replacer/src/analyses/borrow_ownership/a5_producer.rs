//! Rustc-facing producer for A5 parameter-overlap plans.

use std::collections::{BTreeMap, BTreeSet};

use points_to::andersen::{self, Var};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, TerminatorKind},
    ty::{TyCtxt, TyKind},
};

use super::{
    SlotKind,
    a5_overlap::{
        A5Mode, A5SummaryArtifact, A5World, AbiBoundaryFacts, AbiGuardDisposition,
        AllWitnessesGate, C9MarkKey, CallSiteWitnessKey, CallTransfer, FunctionPairKey, PairClass,
        PairFacts, SetPairEvidence, WholeProgramAttestation, WitnessMarkability, WitnessMutability,
        a5_abi_guard, all_witnesses_gate, classify_pair, join_witness_mutability,
        render_summary_artifact, solve_may_overlap,
    },
    a5_snapshot_effects::snapshot_verdict_for_target,
    borrow_engine::{AccessDepth, ParameterOverlap, PlaceConflictBias, places_conflict},
    crate_slots::CrateSlots,
    l2::{MirLocationKey, SlotKey},
    mutability_facts::MutFacts,
    origin_flow::OriginFlowResults,
    resolve::{ResolvedSlot, resolve_place},
    solver::SlotRef,
};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Debug)]
pub(crate) struct PlannedC9Mark {
    pub(crate) key: C9MarkKey,
    pub(crate) endpoint_slots: BTreeSet<SlotKey>,
    pub(crate) call_span: rustc_span::Span,
    pub(crate) caller_did: LocalDefId,
    pub(crate) owner_did: LocalDefId,
    pub(crate) owner_fn: String,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct A5ProducerStats {
    pub(crate) calls: usize,
    pub(crate) unresolved_calls: usize,
    pub(crate) raw_pairs: usize,
    pub(crate) raw_site_pairs: usize,
    pub(crate) raw_site_mut_mut: usize,
    pub(crate) raw_site_mut_read_only: usize,
    pub(crate) raw_site_shared_shared: usize,
    pub(crate) effective_pairs: usize,
    pub(crate) planned_marks: usize,
    pub(crate) missing_mutability_defaults: usize,
}

#[derive(Clone, Debug)]
pub(crate) struct A5Plan {
    pub(crate) mode: A5Mode,
    pub(crate) world: A5World,
    pub(crate) abi_guard: AbiGuardDisposition,
    pub(crate) effective_overlaps: FxHashMap<LocalDefId, ParameterOverlap>,
    pub(crate) coarse_pairs: Vec<(SlotRef, SlotRef)>,
    pub(crate) planned_marks: Vec<PlannedC9Mark>,
    pub(crate) site_ledger: Vec<A5ProductionSiteRow>,
    pub(crate) summary_artifact: A5SummaryArtifact,
    pub(crate) stats: A5ProducerStats,
}

impl A5Plan {
    pub(crate) fn baseline() -> Self {
        Self::baseline_with_guard(AbiGuardDisposition::Permitted { attested: false })
    }

    pub(crate) fn baseline_attested() -> Self {
        Self::baseline_with_guard(AbiGuardDisposition::Permitted { attested: true })
    }

    fn baseline_with_guard(guard: AbiGuardDisposition) -> Self {
        let fixpoint = solve_may_overlap(std::iter::empty());
        Self {
            mode: A5Mode::Baseline,
            world: A5World::ClosedWorldFrozenGraph,
            abi_guard: guard.clone(),
            effective_overlaps: FxHashMap::default(),
            coarse_pairs: Vec::new(),
            planned_marks: Vec::new(),
            site_ledger: Vec::new(),
            summary_artifact: render_summary_artifact(&fixpoint, A5Mode::Baseline, &guard),
            stats: A5ProducerStats::default(),
        }
    }

    pub(crate) fn retained_marks(
        &self,
        model: &FxHashMap<SlotRef, SlotKind>,
    ) -> BTreeSet<C9MarkKey> {
        self.planned_marks
            .iter()
            .filter(|mark| {
                mark.endpoint_slots.iter().all(|slot| {
                    model
                        .iter()
                        .find(|(candidate, _)| SlotKey::of(**candidate) == *slot)
                        .is_some_and(|(_, kind)| *kind == SlotKind::Ref)
                })
            })
            .map(|mark| mark.key.clone())
            .collect()
    }

    pub(crate) fn retained_mark_plans(
        &self,
        model: &FxHashMap<SlotRef, SlotKind>,
    ) -> Vec<PlannedC9Mark> {
        let mut retained = self
            .planned_marks
            .iter()
            .filter(|mark| {
                mark.endpoint_slots.iter().all(|slot| {
                    model
                        .iter()
                        .find(|(candidate, _)| SlotKey::of(**candidate) == *slot)
                        .is_some_and(|(_, kind)| *kind == SlotKind::Ref)
                })
            })
            .cloned()
            .collect::<Vec<_>>();
        retained.sort_by(|left, right| left.key.cmp(&right.key));
        retained.dedup_by(|left, right| {
            let shared_actual = |mark: &PlannedC9Mark| match mark.key.shared_side {
                super::a5_overlap::PairSide::Left => mark.key.actuals.0,
                super::a5_overlap::PairSide::Right => mark.key.actuals.1,
            };
            left.caller_did == right.caller_did
                && left.call_span.lo() == right.call_span.lo()
                && left.call_span.hi() == right.call_span.hi()
                && shared_actual(left) == shared_actual(right)
                && left.key.pointee_type == right.key.pointee_type
        });
        retained
    }
}

#[derive(Clone, Debug)]
pub(crate) struct A5ProductionSiteRow {
    pub(crate) caller: u32,
    pub(crate) location: MirLocationKey,
    pub(crate) target: u32,
    pub(crate) left_parameter: u32,
    pub(crate) right_parameter: u32,
    pub(crate) left_actual: SlotKey,
    pub(crate) right_actual: SlotKey,
    pub(crate) class: WitnessMutability,
}

#[derive(Clone)]
struct WitnessRecord {
    key: CallSiteWitnessKey,
    target: LocalDefId,
    pair: FunctionPairKey,
    class: WitnessMutability,
    markability: WitnessMarkability,
    mark: Option<PlannedC9Mark>,
    endpoints: (SlotRef, SlotRef),
    registered_site: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct A5SiteBranchAudit {
    pub(crate) caller: u32,
    pub(crate) caller_path: String,
    pub(crate) block: u32,
    pub(crate) target: u32,
    pub(crate) target_path: String,
    pub(crate) left_parameter: u32,
    pub(crate) right_parameter: u32,
    pub(crate) left_operand: String,
    pub(crate) right_operand: String,
    pub(crate) left_actual: Option<SlotKey>,
    pub(crate) right_actual: Option<SlotKey>,
    pub(crate) classifier: Option<PairClass>,
    pub(crate) dependencies: usize,
    pub(crate) family: &'static str,
    pub(crate) terminator: String,
}

pub(crate) fn audit_a5_site_branches(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    flows: &OriginFlowResults,
) -> Vec<A5SiteBranchAudit> {
    let tcx = program.tcx;
    let local_functions = program.functions.iter().copied().collect::<FxHashSet<_>>();
    let arena = typed_arena::Arena::new();
    let type_shapes = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: program
            .functions
            .iter()
            .filter(|did| tcx.visibility(did.to_def_id()).is_public())
            .map(|did| tcx.item_name(did.to_def_id()).to_string())
            .collect(),
    };
    let pre = andersen::pre_analyze(&config, &type_shapes, tcx);
    let solutions = andersen::analyze(&config, &pre, &type_shapes, tcx);
    let mut unknown_locations = BTreeSet::new();
    for variable in &pre.exposed_fn_arg_vars {
        let start = pre.vars[variable];
        let end = pre.index_info.get_end(start);
        unknown_locations.extend(start.index()..=end.index());
    }
    let mut resolved = FxHashMap::<(LocalDefId, BasicBlock), Vec<LocalDefId>>::default();
    for &caller in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let function = match &data.terminator().kind {
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => func,
                _ => continue,
            };
            let mut targets = if let Some(function) = function.constant() {
                let TyKind::FnDef(target, _) = *function.ty().kind() else {
                    continue;
                };
                let Some(target) = target.as_local() else {
                    continue;
                };
                vec![target]
            } else {
                indirect_targets(&pre, &solutions, caller, block).unwrap_or_default()
            };
            targets.retain(|target| local_functions.contains(target));
            targets.sort_unstable_by_key(|did| did.local_def_index.as_u32());
            targets.dedup();
            if !targets.is_empty() {
                resolved.insert((caller, block), targets);
            }
        }
    }
    let address_taken = crate::rewriter::collector::collect_fn_ptrs(program);
    let unknown_reachable = closed_world_unknown_reachable(program, &resolved, &address_taken);

    let mut answer = Vec::new();
    for &caller in &program.functions {
        let caller_path = tcx.def_path_str(caller.to_def_id());
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let flow = &flows[&caller].body;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let args = match &data.terminator().kind {
                TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
                    &args[..]
                }
                _ => continue,
            };
            let Some(targets) = resolved.get(&(caller, block)) else {
                continue;
            };
            for left in 0..args.len() {
                for right in left + 1..args.len() {
                    let left_actual = actual_slot(slots, caller, &body, &args[left].node);
                    let right_actual = actual_slot(slots, caller, &body, &args[right].node);
                    let mut classifier = None;
                    let mut dependencies = 0usize;
                    let family = if targets.iter().any(|target| {
                        let target_body =
                            tcx.mir_drops_elaborated_and_const_checked(*target).borrow();
                        left >= target_body.arg_count || right >= target_body.arg_count
                    }) {
                        "target-arity"
                    } else if left_actual.is_none() && right_actual.is_none() {
                        "both-actual-slots-missing"
                    } else if left_actual.is_none() {
                        "left-actual-slot-missing"
                    } else if right_actual.is_none() {
                        "right-actual-slot-missing"
                    } else {
                        let facts = pair_facts(
                            tcx,
                            &body,
                            flow,
                            unknown_reachable.contains(&caller),
                            &pre,
                            &solutions,
                            &unknown_locations,
                            caller,
                            &args[left].node,
                            &args[right].node,
                        );
                        if facts.projection_disjoint {
                            "projection-disjoint"
                        } else {
                            let (dependency_rows, _, _) = caller_pair_dependencies(
                                &body,
                                flow,
                                caller,
                                &args[left].node,
                                &args[right].node,
                            );
                            dependencies = dependency_rows.len();
                            let verdict = classify_pair(&facts);
                            classifier = Some(verdict);
                            match site_seed_disposition(verdict, dependency_rows.is_empty()) {
                                SiteSeedDisposition::DirectAndRecord => {
                                    if targets.iter().all(|target| {
                                        formal_slot(slots, *target, left).is_some()
                                            && formal_slot(slots, *target, right).is_some()
                                    }) {
                                        "recorded-risky"
                                    } else {
                                        "target-formal-slot-missing"
                                    }
                                }
                                SiteSeedDisposition::ForwardOnly => "forward-only-proven-disjoint",
                                SiteSeedDisposition::Excluded => "excluded-proven-disjoint",
                            }
                        }
                    };
                    for &target in targets {
                        answer.push(A5SiteBranchAudit {
                            caller: caller.local_def_index.as_u32(),
                            caller_path: caller_path.clone(),
                            block: block.as_u32(),
                            target: target.local_def_index.as_u32(),
                            target_path: tcx.def_path_str(target.to_def_id()),
                            left_parameter: left as u32 + 1,
                            right_parameter: right as u32 + 1,
                            left_operand: format!("{:?}", args[left].node),
                            right_operand: format!("{:?}", args[right].node),
                            left_actual: left_actual.map(SlotKey::of),
                            right_actual: right_actual.map(SlotKey::of),
                            classifier,
                            dependencies,
                            family,
                            terminator: format!("{:?}", data.terminator().kind),
                        });
                    }
                }
            }
        }
    }
    answer.sort_by(|left, right| {
        (
            left.caller,
            left.block,
            left.target,
            left.left_parameter,
            left.right_parameter,
        )
            .cmp(&(
                right.caller,
                right.block,
                right.target,
                right.left_parameter,
                right.right_parameter,
            ))
    });
    answer
}

fn indirect_targets(
    pre: &andersen::PreAnalysisData<'_>,
    solutions: &andersen::Solutions,
    caller: LocalDefId,
    block: BasicBlock,
) -> Option<Vec<LocalDefId>> {
    let location = pre.indirect_calls.get(&caller)?.get(&block)?;
    let mut targets = solutions[*location]
        .iter()
        .filter_map(|location| pre.inv_fns.get(&location).copied())
        .collect::<Vec<_>>();
    targets.sort_unstable_by_key(|did| did.local_def_index.as_u32());
    targets.dedup();
    Some(targets)
}

fn operand_points(
    pre: &andersen::PreAnalysisData<'_>,
    solutions: &andersen::Solutions,
    unknown_locations: &BTreeSet<usize>,
    caller: LocalDefId,
    operand: &Operand<'_>,
) -> Option<(BTreeSet<String>, bool)> {
    let place = operand.place()?;
    if !place.projection.is_empty() {
        return None;
    }
    let location = *pre.vars.get(&Var::Local(caller, place.local))?;
    let points = solutions[location]
        .iter()
        .map(|target| target.index())
        .collect::<BTreeSet<_>>();
    let complete = points.is_disjoint(unknown_locations);
    Some((
        points.into_iter().map(|index| index.to_string()).collect(),
        complete,
    ))
}

fn pair_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    flow: &super::origin_flow::BodyOriginFlow,
    caller_unknown: bool,
    pre: &andersen::PreAnalysisData<'tcx>,
    solutions: &andersen::Solutions,
    unknown_locations: &BTreeSet<usize>,
    caller: LocalDefId,
    left: &Operand<'tcx>,
    right: &Operand<'tcx>,
) -> PairFacts<String> {
    let (left_place, right_place) = (left.place(), right.place());
    let storage_alias = match (left_place, right_place) {
        (Some(left), Some(right)) if left == right => true,
        (Some(left), Some(right)) if left.projection.is_empty() && right.projection.is_empty() => {
            flow.depth0_storage_alias(left.local, right.local)
        }
        _ => false,
    };
    let origins = match (left_place, right_place) {
        (Some(left), Some(right)) if left.projection.is_empty() && right.projection.is_empty() => {
            match (
                flow.depth0_origin_indices(body, left.local, caller_unknown),
                flow.depth0_origin_indices(body, right.local, caller_unknown),
            ) {
                (Some((left, true)), Some((right, true))) => SetPairEvidence::Complete {
                    left: left.into_iter().map(|index| index.to_string()).collect(),
                    right: right.into_iter().map(|index| index.to_string()).collect(),
                },
                (Some((left, _)), Some((right, _))) => SetPairEvidence::Incomplete {
                    left: left.into_iter().map(|index| index.to_string()).collect(),
                    right: right.into_iter().map(|index| index.to_string()).collect(),
                },
                _ => SetPairEvidence::Unknown,
            }
        }
        _ => SetPairEvidence::Unknown,
    };
    let projection_disjoint = matches!((left_place, right_place), (Some(left), Some(right))
    if left.local == right.local
        && !places_conflict(
            tcx,
            body,
            left,
            right,
            AccessDepth::Deep,
            PlaceConflictBias::Overlap,
        ));
    let points_to = match (
        operand_points(pre, solutions, unknown_locations, caller, left),
        operand_points(pre, solutions, unknown_locations, caller, right),
    ) {
        (Some((left, true)), Some((right, true))) => SetPairEvidence::Complete { left, right },
        (Some((left, _)), Some((right, _))) => SetPairEvidence::Incomplete { left, right },
        _ => SetPairEvidence::Unknown,
    };
    PairFacts {
        storage_alias,
        projection_disjoint,
        origins,
        points_to,
    }
}

fn caller_pair_dependencies(
    body: &Body<'_>,
    flow: &super::origin_flow::BodyOriginFlow,
    caller: LocalDefId,
    left: &Operand<'_>,
    right: &Operand<'_>,
) -> (BTreeSet<FunctionPairKey>, bool, bool) {
    let left = left
        .place()
        .and_then(|place| flow.depth0_argument_origins(body, place.local));
    let right = right
        .place()
        .and_then(|place| flow.depth0_argument_origins(body, place.local));
    let (Some((left, left_complete)), Some((right, right_complete))) = (left, right) else {
        return (BTreeSet::new(), false, false);
    };
    let shares_argument_origin = !left.is_disjoint(&right);
    let dependencies = left
        .iter()
        .flat_map(|&left| {
            right.iter().filter_map(move |&right| {
                FunctionPairKey::new(caller.local_def_index.as_u32(), left as u32, right as u32)
            })
        })
        .collect();
    (
        dependencies,
        left_complete && right_complete,
        shares_argument_origin,
    )
}

fn join_record_classes(records: &[WitnessRecord]) -> WitnessMutability {
    join_classes(records.iter().map(|record| record.class))
}

fn join_classes(classes: impl IntoIterator<Item = WitnessMutability>) -> WitnessMutability {
    let mut left_mutable = false;
    let mut right_mutable = false;
    for class in classes {
        match class {
            WitnessMutability::MutMut => {
                left_mutable = true;
                right_mutable = true;
            }
            WitnessMutability::MutReadOnly {
                read_only: super::a5_overlap::PairSide::Left,
            } => right_mutable = true,
            WitnessMutability::MutReadOnly {
                read_only: super::a5_overlap::PairSide::Right,
            } => left_mutable = true,
            WitnessMutability::SharedShared => {}
        }
    }
    match (left_mutable, right_mutable) {
        (true, true) => WitnessMutability::MutMut,
        (true, false) => WitnessMutability::MutReadOnly {
            read_only: super::a5_overlap::PairSide::Right,
        },
        (false, true) => WitnessMutability::MutReadOnly {
            read_only: super::a5_overlap::PairSide::Left,
        },
        (false, false) => WitnessMutability::SharedShared,
    }
}

fn merge_abi_guard(current: &mut AbiGuardDisposition, next: AbiGuardDisposition) {
    match next {
        AbiGuardDisposition::Refused { reasons } => match current {
            AbiGuardDisposition::Refused {
                reasons: current_reasons,
            } => current_reasons.extend(reasons),
            AbiGuardDisposition::Permitted { .. } => {
                *current = AbiGuardDisposition::Refused { reasons };
            }
        },
        AbiGuardDisposition::Permitted { attested } => {
            if let AbiGuardDisposition::Permitted {
                attested: current_attested,
            } = current
            {
                *current_attested |= attested;
            }
        }
    }
}

/// The O2 frozen-call-world product shared by production A5 and read-only
/// measurement consumers. Construction is a pure extraction of A5's former
/// inline call-target block; it does not seed unknown callers.
#[derive(Clone, Debug)]
pub(crate) struct ClosedWorldCallWorld {
    pub(crate) resolved: FxHashMap<(LocalDefId, BasicBlock), Vec<LocalDefId>>,
    pub(crate) unknown_reachable: FxHashSet<LocalDefId>,
    pub(crate) calls: usize,
    pub(crate) unresolved_calls: usize,
    indirect_function_targets: FxHashSet<LocalDefId>,
    indirect_sites: FxHashSet<(LocalDefId, BasicBlock)>,
    aggregate_guard: AbiGuardDisposition,
}

impl ClosedWorldCallWorld {
    pub(crate) fn artifact(&self, tcx: TyCtxt<'_>) -> String {
        let mut rows = self
            .resolved
            .iter()
            .flat_map(|(&(caller_did, block), targets)| {
                let caller = tcx.item_name(caller_did.to_def_id()).to_string();
                let kind = if self.indirect_sites.contains(&(caller_did, block)) {
                    "indirect"
                } else {
                    "direct"
                };
                targets.iter().map(move |target| {
                    format!(
                        "{}\t{}\t{}\n",
                        caller,
                        tcx.item_name(target.to_def_id()),
                        kind
                    )
                })
            })
            .collect::<Vec<_>>();
        rows.sort();
        let mut output = rows.concat();
        let mut unknown = self
            .unknown_reachable
            .iter()
            .map(|function| {
                format!(
                    "unknown-reachable\t{}\n",
                    tcx.item_name(function.to_def_id())
                )
            })
            .collect::<Vec<_>>();
        unknown.sort();
        output.push_str(&unknown.concat());
        output
    }
}

fn resolve_closed_world_call_world_from_analysis(
    program: &RustProgram<'_>,
    pre: &andersen::PreAnalysisData<'_>,
    solutions: &andersen::Solutions,
    address_taken_functions: &FxHashSet<LocalDefId>,
    attestation: Option<WholeProgramAttestation>,
) -> ClosedWorldCallWorld {
    let tcx = program.tcx;
    let local_functions = program.functions.iter().copied().collect::<FxHashSet<_>>();
    let mut indirect_function_targets = FxHashSet::default();
    let mut indirect_sites = FxHashSet::default();
    let mut resolved = FxHashMap::<(LocalDefId, BasicBlock), Vec<LocalDefId>>::default();
    let mut calls = 0usize;
    let mut unresolved_calls = 0usize;
    let mut aggregate_guard = AbiGuardDisposition::Permitted {
        attested: attestation == Some(WholeProgramAttestation::FrozenBenchmarkGraph),
    };
    for &caller in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let function = match &data.terminator().kind {
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => func,
                _ => continue,
            };
            calls += 1;
            let indirect = function.constant().is_none();
            let mut targets = if let Some(function) = function.constant() {
                let TyKind::FnDef(target, _) = *function.ty().kind() else {
                    continue;
                };
                let Some(target) = target.as_local() else {
                    continue;
                };
                vec![target]
            } else {
                indirect_targets(pre, solutions, caller, block).unwrap_or_default()
            };
            targets.retain(|target| local_functions.contains(target));
            targets.sort_unstable_by_key(|did| did.local_def_index.as_u32());
            targets.dedup();
            if targets.is_empty() {
                unresolved_calls += 1;
                merge_abi_guard(
                    &mut aggregate_guard,
                    a5_abi_guard(
                        &AbiBoundaryFacts {
                            unresolved_target: true,
                            ..AbiBoundaryFacts::default()
                        },
                        attestation,
                    ),
                );
                continue;
            }
            if indirect {
                indirect_sites.insert((caller, block));
                indirect_function_targets.extend(targets.iter().copied());
            }
            resolved.insert((caller, block), targets);
        }
    }
    let unknown_reachable =
        closed_world_unknown_reachable(program, &resolved, address_taken_functions);
    ClosedWorldCallWorld {
        resolved,
        unknown_reachable,
        calls,
        unresolved_calls,
        indirect_function_targets,
        indirect_sites,
        aggregate_guard,
    }
}

pub(crate) fn resolve_closed_world_call_world(
    program: &RustProgram<'_>,
    attestation: Option<WholeProgramAttestation>,
) -> ClosedWorldCallWorld {
    let tcx = program.tcx;
    let arena = typed_arena::Arena::new();
    let type_shapes = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: program
            .functions
            .iter()
            .filter(|did| tcx.visibility(did.to_def_id()).is_public())
            .map(|did| tcx.item_name(did.to_def_id()).to_string())
            .collect(),
    };
    let pre = andersen::pre_analyze(&config, &type_shapes, tcx);
    let solutions = andersen::analyze(&config, &pre, &type_shapes, tcx);
    let address_taken_functions = crate::rewriter::collector::collect_fn_ptrs(program);
    resolve_closed_world_call_world_from_analysis(
        program,
        &pre,
        &solutions,
        &address_taken_functions,
        attestation,
    )
}

fn closed_world_unknown_reachable(
    program: &RustProgram<'_>,
    resolved: &FxHashMap<(LocalDefId, BasicBlock), Vec<LocalDefId>>,
    address_taken: &FxHashSet<LocalDefId>,
) -> FxHashSet<LocalDefId> {
    let mut pending = program
        .functions
        .iter()
        .copied()
        .filter(|did| {
            program.tcx.visibility(did.to_def_id()).is_public() || address_taken.contains(did)
        })
        .collect::<Vec<_>>();
    pending.sort_unstable_by_key(|did| did.local_def_index.as_u32());
    let mut reachable = FxHashSet::default();
    while let Some(function) = pending.pop() {
        if !reachable.insert(function) {
            continue;
        }
        let mut callees = resolved
            .iter()
            .filter(|((caller, _), _)| *caller == function)
            .flat_map(|(_, targets)| targets.iter().copied())
            .collect::<Vec<_>>();
        callees.sort_unstable_by_key(|did| did.local_def_index.as_u32());
        callees.dedup();
        pending.extend(callees);
    }
    reachable
}

fn formal_slot(slots: &CrateSlots, target: LocalDefId, parameter: usize) -> Option<SlotRef> {
    let slot = slots
        .fn_local_slots
        .get(&target)?
        .slot_for_local_depth(Local::from_usize(parameter + 1), 0)?;
    Some(SlotRef::Local(target, slot))
}

fn actual_slot<'tcx>(
    slots: &CrateSlots,
    caller: LocalDefId,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<SlotRef> {
    let place = operand.place()?;
    match resolve_place(slots, caller, body, place, 0, None)? {
        ResolvedSlot::Local(slot) => Some(SlotRef::Local(caller, slot)),
        ResolvedSlot::Field(slot) => Some(SlotRef::Field(slot)),
    }
}

fn type_filters(
    tcx: TyCtxt<'_>,
    targets: &[LocalDefId],
    left: usize,
    right: usize,
) -> (bool, bool, Option<String>) {
    let mut expected = None;
    let mut agree = !targets.is_empty();
    let mut copy_scalar = !targets.is_empty();
    for &target in targets {
        let body = tcx.mir_drops_elaborated_and_const_checked(target).borrow();
        let Some(left_ty) = body.local_decls[Local::from_usize(left + 1)]
            .ty
            .builtin_deref(true)
        else {
            return (false, false, None);
        };
        let Some(right_ty) = body.local_decls[Local::from_usize(right + 1)]
            .ty
            .builtin_deref(true)
        else {
            return (false, false, None);
        };
        agree &= left_ty == right_ty && expected.is_none_or(|ty| ty == left_ty);
        expected = Some(left_ty);
        let scalar = matches!(
            left_ty.kind(),
            TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Uint(_)
                | TyKind::Float(_)
                | TyKind::RawPtr(..)
                | TyKind::Ref(..)
                | TyKind::FnPtr(..)
        );
        copy_scalar &= scalar
            && tcx.type_is_copy_modulo_regions(
                rustc_middle::ty::TypingEnv::post_analysis(tcx, target),
                left_ty,
            );
    }
    (agree, copy_scalar, expected.map(|ty| ty.to_string()))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SiteSeedDisposition {
    DirectAndRecord,
    ForwardOnly,
    Excluded,
}

fn site_seed_disposition(verdict: PairClass, dependencies_empty: bool) -> SiteSeedDisposition {
    match verdict {
        PairClass::NotProvenDisjoint => SiteSeedDisposition::DirectAndRecord,
        PairClass::ProvenDisjoint if !dependencies_empty => SiteSeedDisposition::ForwardOnly,
        PairClass::ProvenDisjoint => SiteSeedDisposition::Excluded,
    }
}

pub(crate) fn produce_a5_plan(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    flows: &OriginFlowResults,
    mut_facts: &MutFacts,
    baseline_model: &FxHashMap<SlotRef, SlotKind>,
    mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
) -> Result<A5Plan, String> {
    if mode == A5Mode::Baseline {
        return Ok(
            if attestation == Some(WholeProgramAttestation::FrozenBenchmarkGraph) {
                A5Plan::baseline_attested()
            } else {
                A5Plan::baseline()
            },
        );
    }
    let tcx = program.tcx;
    let arena = typed_arena::Arena::new();
    let type_shapes = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: program
            .functions
            .iter()
            .filter(|did| tcx.visibility(did.to_def_id()).is_public())
            .map(|did| tcx.item_name(did.to_def_id()).to_string())
            .collect(),
    };
    let pre = andersen::pre_analyze(&config, &type_shapes, tcx);
    let solutions = andersen::analyze(&config, &pre, &type_shapes, tcx);
    let address_taken_functions = crate::rewriter::collector::collect_fn_ptrs(program);
    let mut unknown_locations = BTreeSet::new();
    for variable in &pre.exposed_fn_arg_vars {
        let start = pre.vars[variable];
        let end = pre.index_info.get_end(start);
        unknown_locations.extend(start.index()..=end.index());
    }
    let call_world = resolve_closed_world_call_world_from_analysis(
        program,
        &pre,
        &solutions,
        &address_taken_functions,
        attestation,
    );
    let resolved = &call_world.resolved;
    let indirect_function_targets = &call_world.indirect_function_targets;
    let unknown_reachable = &call_world.unknown_reachable;
    let mut stats = A5ProducerStats {
        calls: call_world.calls,
        unresolved_calls: call_world.unresolved_calls,
        ..A5ProducerStats::default()
    };
    let mut aggregate_guard = call_world.aggregate_guard.clone();

    let mut transfers = Vec::new();
    let mut records = BTreeMap::<FunctionPairKey, Vec<WitnessRecord>>::new();
    for &caller in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let flow = &flows[&caller].body;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let args = match &data.terminator().kind {
                TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
                    &args[..]
                }
                _ => continue,
            };
            let Some(targets) = resolved.get(&(caller, block)) else {
                continue;
            };
            for &target in targets {
                let facts = AbiBoundaryFacts {
                    externally_visible: tcx.visibility(target.to_def_id()).is_public(),
                    address_taken: address_taken_functions.contains(&target),
                    function_target: indirect_function_targets.contains(&target),
                    ..AbiBoundaryFacts::default()
                };
                let guard = a5_abi_guard(&facts, attestation);
                merge_abi_guard(&mut aggregate_guard, guard);
            }
            for left in 0..args.len() {
                for right in left + 1..args.len() {
                    if targets.iter().any(|target| {
                        let target_body =
                            tcx.mir_drops_elaborated_and_const_checked(*target).borrow();
                        left >= target_body.arg_count || right >= target_body.arg_count
                    }) {
                        continue;
                    }
                    let Some(left_actual) = actual_slot(slots, caller, &body, &args[left].node)
                    else {
                        continue;
                    };
                    let Some(right_actual) = actual_slot(slots, caller, &body, &args[right].node)
                    else {
                        continue;
                    };
                    let facts = pair_facts(
                        tcx,
                        &body,
                        flow,
                        unknown_reachable.contains(&caller),
                        &pre,
                        &solutions,
                        &unknown_locations,
                        caller,
                        &args[left].node,
                        &args[right].node,
                    );
                    if facts.projection_disjoint {
                        continue;
                    }
                    let (dependencies, _dependencies_complete, _shares_argument_origin) =
                        caller_pair_dependencies(
                            &body,
                            flow,
                            caller,
                            &args[left].node,
                            &args[right].node,
                        );
                    let disposition =
                        site_seed_disposition(classify_pair(&facts), dependencies.is_empty());
                    if disposition == SiteSeedDisposition::Excluded {
                        continue;
                    }
                    // Summary transfer is a value-flow fact, not a selected-
                    // model fact. Register it before the current-model Ref
                    // market filter so a Raw intermediate caller pair can
                    // still carry an overlap witness to a downstream pair.
                    for &target in targets {
                        let key = CallSiteWitnessKey::new(
                            target.local_def_index.as_u32(),
                            left as u32 + 1,
                            SlotKey::of(left_actual),
                            right as u32 + 1,
                            SlotKey::of(right_actual),
                            caller.local_def_index.as_u32(),
                            MirLocationKey::new(block.as_u32(), data.statements.len()),
                        )
                        .expect("distinct params");
                        if disposition == SiteSeedDisposition::DirectAndRecord {
                            transfers.push(CallTransfer::direct(key));
                        }
                        for &dependency in &dependencies {
                            transfers.push(CallTransfer::forwarded(key, dependency)?);
                        }
                    }
                    let left_slots = targets
                        .iter()
                        .map(|target| formal_slot(slots, *target, left))
                        .collect::<Option<Vec<_>>>();
                    let right_slots = targets
                        .iter()
                        .map(|target| formal_slot(slots, *target, right))
                        .collect::<Option<Vec<_>>>();
                    let (Some(left_slots), Some(right_slots)) = (left_slots, right_slots) else {
                        continue;
                    };
                    if left_slots
                        .iter()
                        .chain(&right_slots)
                        .any(|slot| baseline_model.get(slot) != Some(&SlotKind::Ref))
                    {
                        continue;
                    }
                    let mutability = join_witness_mutability(
                        targets.iter().map(|target| {
                            let local = Local::from_usize(left + 1);
                            (!mut_facts.is_defaulted(*target, local))
                                .then(|| mut_facts.is_mutable(*target, local))
                        }),
                        targets.iter().map(|target| {
                            let local = Local::from_usize(right + 1);
                            (!mut_facts.is_defaulted(*target, local))
                                .then(|| mut_facts.is_mutable(*target, local))
                        }),
                    );
                    stats.missing_mutability_defaults += mutability.missing_defaults;
                    let (agree, copy_scalar, pointee) = type_filters(tcx, targets, left, right);
                    for (&target, (&left_slot, &right_slot)) in
                        targets.iter().zip(left_slots.iter().zip(&right_slots))
                    {
                        let pair = FunctionPairKey::new(
                            target.local_def_index.as_u32(),
                            left as u32 + 1,
                            right as u32 + 1,
                        )
                        .expect("distinct params");
                        let key = CallSiteWitnessKey::new(
                            target.local_def_index.as_u32(),
                            left as u32 + 1,
                            SlotKey::of(left_actual),
                            right as u32 + 1,
                            SlotKey::of(right_actual),
                            caller.local_def_index.as_u32(),
                            MirLocationKey::new(block.as_u32(), data.statements.len()),
                        )
                        .expect("distinct params");
                        let (read_only, effect) = match mutability.class {
                            WitnessMutability::MutReadOnly { read_only } => (
                                Some(read_only),
                                snapshot_verdict_for_target(tcx, target, left, right, read_only),
                            ),
                            _ => (None, super::a5_overlap::SnapshotVerdict::OpaqueEscape),
                        };
                        let markability = WitnessMarkability {
                            effect,
                            target_types_agree: agree,
                            copy_scalar,
                            unknown_caller: false,
                        };
                        let mark = read_only.and_then(|read_only| {
                            Some(PlannedC9Mark {
                                key: C9MarkKey::new(
                                    caller.local_def_index.as_u32(),
                                    MirLocationKey::new(block.as_u32(), data.statements.len()),
                                    targets.iter().map(|target| target.local_def_index.as_u32()),
                                    target.local_def_index.as_u32(),
                                    left as u32 + 1,
                                    SlotKey::of(left_actual),
                                    right as u32 + 1,
                                    SlotKey::of(right_actual),
                                    read_only,
                                    pointee.clone()?,
                                )?,
                                endpoint_slots: BTreeSet::from([
                                    SlotKey::of(left_slot),
                                    SlotKey::of(right_slot),
                                ]),
                                call_span: data.terminator().source_info.span,
                                caller_did: caller,
                                owner_did: target,
                                owner_fn: tcx.def_path_str(target.to_def_id()),
                            })
                        });
                        records.entry(pair).or_default().push(WitnessRecord {
                            key,
                            target,
                            pair,
                            class: mutability.class,
                            markability,
                            mark,
                            endpoints: (left_slot, right_slot),
                            registered_site: disposition == SiteSeedDisposition::DirectAndRecord,
                        });
                    }
                }
            }
        }
    }

    let fixpoint = solve_may_overlap(transfers);
    let mut overlap_pairs = FxHashMap::<LocalDefId, Vec<(Local, Local)>>::default();
    let mut coarse = BTreeMap::<(SlotKey, SlotKey), (SlotRef, SlotRef)>::new();
    let mut planned = Vec::new();
    let mut site_classes = BTreeMap::<
        (u32, MirLocationKey, u32, u32, u32, SlotKey, SlotKey),
        Vec<WitnessMutability>,
    >::new();
    for (pair, witnesses) in records {
        if !fixpoint.summary().contains(pair) {
            continue;
        }
        let active_keys = fixpoint.summary().witnesses(pair);
        let witnesses = witnesses
            .into_iter()
            .filter(|witness| active_keys.contains(&witness.key))
            .collect::<Vec<_>>();
        if witnesses.is_empty() {
            continue;
        }
        for witness in &witnesses {
            if !witness.registered_site {
                continue;
            }
            let params = pair.params();
            let actuals = witness.key.actuals();
            site_classes
                .entry((
                    witness.key.caller(),
                    witness.key.location(),
                    pair.function(),
                    params.first(),
                    params.second(),
                    actuals.0,
                    actuals.1,
                ))
                .or_default()
                .push(witness.class);
        }
        stats.raw_pairs += 1;
        let class = join_record_classes(&witnesses);
        let discharged = matches!(class, WitnessMutability::MutReadOnly { .. })
            && witnesses.iter().all(|witness| witness.class == class)
            && matches!(
                all_witnesses_gate(witnesses.iter().map(|witness| witness.markability)),
                AllWitnessesGate::Discharged
            );
        if discharged {
            planned.extend(witnesses.iter().filter_map(|witness| witness.mark.clone()));
        } else {
            let first = &witnesses[0];
            overlap_pairs.entry(first.target).or_default().push((
                Local::from_usize(pair.params().first() as usize),
                Local::from_usize(pair.params().second() as usize),
            ));
            stats.effective_pairs += 1;
        }
        if !matches!(class, WitnessMutability::SharedShared) {
            let (left, right) = witnesses[0].endpoints;
            let keys = (SlotKey::of(left), SlotKey::of(right));
            coarse.insert(keys, (left, right));
        }
    }
    planned.sort_by(|left, right| left.key.cmp(&right.key));
    planned.dedup_by(|left, right| left.key == right.key);
    stats.planned_marks = planned.len();
    stats.raw_site_pairs = site_classes.len();
    let site_ledger = site_classes
        .into_iter()
        .map(
            |(
                (
                    caller,
                    location,
                    target,
                    left_parameter,
                    right_parameter,
                    left_actual,
                    right_actual,
                ),
                classes,
            )| A5ProductionSiteRow {
                caller,
                location,
                target,
                left_parameter,
                right_parameter,
                left_actual,
                right_actual,
                class: join_classes(classes),
            },
        )
        .collect::<Vec<_>>();
    for site in &site_ledger {
        match site.class {
            WitnessMutability::MutMut => stats.raw_site_mut_mut += 1,
            WitnessMutability::MutReadOnly { .. } => stats.raw_site_mut_read_only += 1,
            WitnessMutability::SharedShared => stats.raw_site_shared_shared += 1,
        }
    }
    let effective_overlaps = overlap_pairs
        .into_iter()
        .map(|(target, pairs)| (target, ParameterOverlap::from_pairs(pairs)))
        .collect();
    let summary_artifact = render_summary_artifact(&fixpoint, mode, &aggregate_guard);
    Ok(A5Plan {
        mode,
        world: A5World::ClosedWorldFrozenGraph,
        abi_guard: aggregate_guard,
        effective_overlaps,
        coarse_pairs: coarse.into_values().collect(),
        planned_marks: planned,
        site_ledger,
        summary_artifact,
        stats,
    })
}

#[cfg(test)]
mod tests {
    use rustc_hir::{ItemKind, OwnerNode};

    use super::*;
    use crate::analyses::borrow_ownership::{
        construction::{
            CopyLendMode, construct_bo_into, solve_bo_a5_config, verify_bo_construction,
        },
        origins::compute_origins,
        solver::KindSolver,
    };

    fn program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for owner in tcx
            .hir_crate(())
            .owners
            .iter()
            .filter_map(|owner| owner.as_owner())
        {
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    fn baseline(
        program: &RustProgram<'_>,
        slots: &CrateSlots,
        origins: &super::super::origin_summary::OriginSummaries,
        mutability: &MutFacts,
    ) -> FxHashMap<SlotRef, SlotKind> {
        let solver = KindSolver::new(slots);
        let construction = construct_bo_into(
            program,
            slots,
            origins,
            mutability,
            &solver,
            CopyLendMode::Baseline,
        )
        .expect("baseline construction");
        verify_bo_construction(program, slots, origins, &solver, &construction, mutability)
            .expect("baseline model")
    }

    #[test]
    fn shared_classifier_alone_decides_production_site_scope() {
        assert_eq!(
            site_seed_disposition(PairClass::NotProvenDisjoint, false),
            SiteSeedDisposition::DirectAndRecord,
            "a registered risky site must not be demoted to forwarded-only by dependency shape"
        );
        assert_eq!(
            site_seed_disposition(PairClass::NotProvenDisjoint, true),
            SiteSeedDisposition::DirectAndRecord,
            "a registered risky site with no dependencies is still direct"
        );
        assert_eq!(
            site_seed_disposition(PairClass::ProvenDisjoint, true),
            SiteSeedDisposition::Excluded,
            "the empty-dependency flag is not inverted"
        );
        assert_eq!(
            site_seed_disposition(PairClass::ProvenDisjoint, false),
            SiteSeedDisposition::ForwardOnly,
            "a proven-disjoint site may transfer dependencies without entering the site ledger"
        );
    }

    #[test]
    fn unknown_reachable_caller_keeps_ht_set_shaped_site_conservative() {
        let code = r#"
            unsafe fn ht_set_entry(x: *mut i32, y: *mut i32) {}
            pub unsafe fn ht_set(x: *mut i32, y: *mut i32) {
                ht_set_entry(x, y);
            }
        "#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = program(tcx);
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let audit = audit_a5_site_branches(&program, &slots, origins.native_flows());
            let site = audit
                .iter()
                .find(|row| {
                    row.caller_path.ends_with("ht_set")
                        && row.target_path.ends_with("ht_set_entry")
                        && (row.left_parameter, row.right_parameter) == (1, 2)
                })
                .expect("ht_set-shaped site audit");
            assert_eq!(site.classifier, Some(PairClass::NotProvenDisjoint));
            assert_eq!(site.family, "recorded-risky");
        })
        .unwrap();
    }

    #[test]
    fn production_plan_reaches_precise_overlap_and_mark_seams() {
        let code = r#"
            unsafe fn two(x: *mut i32, y: *const i32) {
                let snapshot = *y;
                *x = snapshot + 1;
            }
            unsafe fn entry(p: *mut i32) { two(p, p); }
        "#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = program(tcx);
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let mutability = MutFacts::from_program(&program);
            let model = baseline(&program, &slots, &origins, &mutability);

            let precise = produce_a5_plan(
                &program,
                &slots,
                origins.native_flows(),
                &mutability,
                &model,
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )
            .expect("precise plan");
            assert!(precise.stats.raw_pairs > 0);
            assert!(precise.stats.planned_marks > 0);
            assert_eq!(precise.mode, A5Mode::PreciseReplay);
            assert_eq!(precise.world, A5World::ClosedWorldFrozenGraph);

            let baseline = produce_a5_plan(
                &program,
                &slots,
                origins.native_flows(),
                &mutability,
                &model,
                A5Mode::Baseline,
                None,
            )
            .expect("baseline plan");
            assert_eq!(baseline.stats, A5ProducerStats::default());
            assert!(baseline.effective_overlaps.is_empty());
            assert!(baseline.planned_marks.is_empty());
        })
        .unwrap();
    }

    #[test]
    fn production_plan_consumes_the_caller_to_callee_fixpoint() {
        let code = r#"
            unsafe fn sink(x: *mut i32, y: *mut i32) { *x += 1; *y += 1; }
            unsafe fn forward(x: *mut i32, y: *mut i32) { sink(x, y); }
            unsafe fn entry(p: *mut i32) { forward(p, p); }
        "#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = program(tcx);
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let mutability = MutFacts::from_program(&program);
            let model = baseline(&program, &slots, &origins, &mutability);
            let sink = program
                .functions
                .iter()
                .copied()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == "sink")
                .expect("sink function");

            let plan = produce_a5_plan(
                &program,
                &slots,
                origins.native_flows(),
                &mutability,
                &model,
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )
            .expect("precise plan");
            assert!(
                plan.effective_overlaps
                    .get(&sink)
                    .is_some_and(|pairs| pairs.contains(Local::from_usize(1), Local::from_usize(2))),
                "the direct entry(p,p) witness must propagate through forward's parameter pair"
            );
        })
        .unwrap();
    }

    #[test]
    fn shared_call_world_preserves_direct_indirect_and_o2_roots() {
        let code = r#"
            unsafe fn sink(x: *mut i32, y: *mut i32) { *x += 1; *y += 1; }
            unsafe fn direct(x: *mut i32, y: *mut i32) { sink(x, y); }
            pub unsafe fn entry(p: *mut i32) {
                let target: unsafe fn(*mut i32, *mut i32) = sink;
                direct(p, p);
                target(p, p);
            }
        "#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = program(tcx);
            let world = resolve_closed_world_call_world(
                &program,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            );
            let artifact = world.artifact(tcx);
            assert!(artifact.contains("entry\tdirect\tdirect\n"), "{artifact}");
            assert!(artifact.contains("entry\tsink\tindirect\n"), "{artifact}");
            assert!(artifact.contains("direct\tsink\tdirect\n"), "{artifact}");
            assert!(
                artifact.contains("unknown-reachable\tentry\n"),
                "{artifact}"
            );
            assert!(
                artifact.contains("unknown-reachable\tdirect\n"),
                "{artifact}"
            );
            assert!(artifact.contains("unknown-reachable\tsink\n"), "{artifact}");
            assert_eq!(world.calls, 3);
            assert_eq!(world.unresolved_calls, 0);
        })
        .unwrap();
    }

    #[test]
    fn production_construction_resolves_and_stamps_all_three_modes() {
        let code = r#"
            unsafe fn two(x: *mut i32, y: *const i32) {
                let snapshot = *y;
                *x = snapshot + 1;
            }
            unsafe fn entry(p: *mut i32) { two(p, p); }
        "#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = program(tcx);
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let mutability = MutFacts::from_program(&program);
            let baseline_model = baseline(&program, &slots, &origins, &mutability);

            let baseline = solve_bo_a5_config(
                &program,
                &slots,
                &origins,
                &mutability,
                A5Mode::Baseline,
                None,
            )
            .expect("baseline config");
            assert_eq!(baseline.model, baseline_model);
            assert!(baseline.retained_c9_marks.is_empty());

            let precise = solve_bo_a5_config(
                &program,
                &slots,
                &origins,
                &mutability,
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )
            .expect("precise config");
            let coarse = solve_bo_a5_config(
                &program,
                &slots,
                &origins,
                &mutability,
                A5Mode::CoarseConstraint,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )
            .expect("coarse config");
            for (mode, verified) in [
                ("baseline", &baseline),
                ("precise_replay", &precise),
                ("coarse_constraint", &coarse),
            ] {
                assert!(verified.receipt.contains(&format!("a5_mode={mode}\n")));
                assert!(verified.receipt.contains("copy_lend_mode=baseline\n"));
                assert!(verified.receipt.contains("a2_mode=off\n"));
                assert!(
                    verified
                        .receipt
                        .contains("a5_world=closed_world_frozen_graph\n")
                );
                assert!(verified.receipt.contains("selected_model_sha256="));
                assert!(verified.receipt.contains("replay_safe_definition="));
                assert!(
                    verified
                        .summary_artifact
                        .receipt
                        .contains(&format!("a5_mode={mode}\n"))
                );
                assert!(
                    verified
                        .mark_artifact
                        .contains(&format!("# a5_mode={mode}\n"))
                );
            }
            assert!(coarse.retained_c9_marks.is_empty());
        })
        .unwrap();
    }

    #[test]
    fn production_driver_emits_the_retained_c9_mark_only_in_precise_mode() {
        let code = r#"
            struct H { symbol: i32, previous: i32 }
            unsafe fn two(x: *mut i32, y: *const i32) {
                let snapshot = *y;
                *x = snapshot + 1;
            }
            unsafe fn caller(h: *mut H) {
                let q: *const i32 = &(*h).symbol;
                two(&mut (*h).symbol, q);
            }
        "#;
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let fixture = std::env::temp_dir().join(format!(
            "crat-a5-production-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&fixture).expect("create production fixture directory");
        let root = fixture.join("lib.rs");
        std::fs::write(&root, code).expect("write production fixture");
        let precise = crate::bo_rewriter::rewrite_m1_path_a5_injected(
            &root,
            A5Mode::PreciseReplay,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            &|_| {},
        );
        let baseline =
            crate::bo_rewriter::rewrite_m1_path_a5_injected(&root, A5Mode::Baseline, None, &|_| {});
        let production = crate::bo_rewriter::rewrite_m1_path(&root);
        std::fs::remove_dir_all(&fixture).expect("remove production fixture directory");
        assert!(precise.a5_receipt().contains("a5_mode=precise_replay\n"));
        assert!(baseline.a5_receipt().contains("a5_mode=baseline\n"));
        let precise_receipt = precise.a5_receipt().to_owned();
        let source = |outcome: crate::bo_rewriter::RewriteOutcome| match outcome {
            crate::bo_rewriter::RewriteOutcome::Emitted { source, .. } => source,
            crate::bo_rewriter::RewriteOutcome::Degraded { reason, .. } => {
                panic!("production driver declined: {reason}")
            }
        };
        let precise = source(precise);
        let baseline = source(baseline);
        let production = source(production);
        assert!(
            precise.contains("__crat_c9_"),
            "the precise production entry must materialize its retained mark: {precise}\n{precise_receipt}"
        );
        assert!(
            precise.contains("x: &mut i32") && precise.contains("y: &i32"),
            "the marked production entry must actually promote both callee endpoints: {precise}"
        );
        assert!(
            !baseline.contains("__crat_c9_"),
            "baseline must carry no C-9 mark: {baseline}"
        );
        assert_eq!(
            precise, production,
            "the accepted precise configuration and the single production path must be byte-identical"
        );
    }

    #[test]
    fn w13_production_suppression_forces_the_verify_loop_to_take_back_the_model() {
        let code = r#"
            struct H { symbol: i32, previous: i32 }
            unsafe fn two(x: *mut i32, y: *const i32) {
                let snapshot = *y;
                *x = snapshot + 1;
            }
            unsafe fn caller(h: *mut H) {
                let q: *const i32 = &(*h).symbol;
                two(&mut (*h).symbol, q);
            }
        "#;
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let fixture = std::env::temp_dir().join(format!(
            "crat-a5-w13-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&fixture).expect("create W13 fixture directory");
        let root = fixture.join("lib.rs");
        std::fs::write(&root, code).expect("write W13 fixture");
        let suppressed = crate::bo_rewriter::rewrite_m1_path_a5_injected(
            &root,
            A5Mode::PreciseReplay,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            &|table| table.c9_marks.clear(),
        );
        std::fs::remove_dir_all(&fixture).expect("remove W13 fixture directory");
        assert!(
            suppressed.a5_receipt().contains("a5_retained_marks=1\n"),
            "the accepted model must still require the mark"
        );
        assert!(
            suppressed.reverted_count() > 0,
            "suppressing the selected mark must make production verification take back at least one conversion: {suppressed:#?}"
        );
    }

    #[test]
    fn production_drops_a_model_retained_mark_when_rewriter_endpoints_do_not_convert() {
        let code = r#"
            unsafe fn two(x: *mut i32, y: *const i32) {
                let snapshot = *y;
                *x = snapshot + 1;
            }
            unsafe fn caller(p: *mut i32) { two(p, p); }
        "#;
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let fixture = std::env::temp_dir().join(format!(
            "crat-a5-orphan-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&fixture).expect("create orphan-mark fixture directory");
        let root = fixture.join("lib.rs");
        std::fs::write(&root, code).expect("write orphan-mark fixture");
        let outcome = crate::bo_rewriter::rewrite_m1_path_a5_injected(
            &root,
            A5Mode::PreciseReplay,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            &|_| {},
        );
        std::fs::remove_dir_all(&fixture).expect("remove orphan-mark fixture directory");
        assert!(outcome.a5_receipt().contains("a5_retained_marks=1\n"));
        let crate::bo_rewriter::RewriteOutcome::Emitted { source, .. } = outcome else {
            panic!("fixture must emit its conservative fallback")
        };
        assert!(
            !source.contains("__crat_c9_"),
            "a mark whose rewriter endpoints stayed raw must not ride as orphan glue: {source}"
        );
    }
}
