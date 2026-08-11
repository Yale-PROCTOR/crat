//! Test-only A4 force-SAT exception and allocation-source census.
//!
//! This module is reachable only through the `bo_c1` test harness. Production
//! analysis and rewriter behavior do not depend on it.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};

use rustc_hash::FxHashSet;
use rustc_middle::{
    mir::{
        AggregateKind, Body, Local, Location, Operand, Place, ProjectionElem, RETURN_PLACE, Rvalue,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{TyCtxt, TyKind},
};
use rustc_span::{
    def_id::{DefId, LocalDefId},
    source_map::Spanned,
};
use z3::SatResult;

use super::{collect_program, report::Row};
use crate::analyses::borrow_ownership::{
    CrateCtxt, SlotKind,
    borrow_verify::{verify_to_fixpoint_counting_with_flows, with_mode_a_commit_trace},
    coherence::{add_coherence, constrain_field_ownership},
    crate_slots::CrateSlots,
    emit_crate_ownership_constraints,
    export::{BoExport, SelectorSite, location_key, with_bo_export},
    mutability_facts::{MutFacts, MutFactsMode},
    origins::compute_origins,
    resolve::{ResolvedSlot, resolve_place},
    slots::{SlotId, SlotOwner},
    solver::{KindSolver, Selectors, SlotRef},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum CauseFlag {
    InterproceduralAllocation,
    FieldMediatedAllocation,
    ReallocAllocation,
    SameFunctionScannerGap,
    StaticOrInteriorRoot,
    ExternallySuppliedParameter,
    OpaqueExternalCallResult,
    StackOrLocalAddress,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PrimaryClass {
    Invisible,
    Absent,
    Mixed,
    Unresolved,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RootEvidence {
    flags: BTreeSet<CauseFlag>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TerminalKind {
    RecognizedAllocation,
    StaticOrInterior,
    ExternalParameter,
    OpaqueExternalCall,
    StackOrLocalAddress,
    Unsupported,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SyntheticPath {
    terminal: TerminalKind,
    crosses_call: bool,
    crosses_field: bool,
    realloc: bool,
    same_function_scanner_gap: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Identity {
    program: String,
    field_key: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ShardGate {
    data: bool,
    completed: bool,
    manifested: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExceptionSpec {
    program: &'static str,
    field_key: &'static str,
    ordinary_kind: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FlowEdgeKind {
    Local,
    Call,
    Field,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FlowEdge {
    source: String,
    target: String,
    kind: FlowEdgeKind,
    label: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TerminalRoot {
    id: String,
    node: String,
    kind: TerminalKind,
    label: String,
    realloc: bool,
}

#[derive(Clone, Debug, Default)]
struct SourceGraph {
    incoming: BTreeMap<String, Vec<FlowEdge>>,
    terminals: BTreeMap<String, Vec<TerminalRoot>>,
}

impl SourceGraph {
    fn add_edge(&mut self, edge: FlowEdge) {
        self.incoming
            .entry(edge.target.clone())
            .or_default()
            .push(edge);
    }

    fn add_terminal(&mut self, terminal: TerminalRoot) {
        self.terminals
            .entry(terminal.node.clone())
            .or_default()
            .push(terminal);
    }

    fn canonicalize(&mut self) {
        for edges in self.incoming.values_mut() {
            edges.sort_by(|a, b| {
                (&a.source, &a.target, &a.label).cmp(&(&b.source, &b.target, &b.label))
            });
            edges.dedup();
        }
        for terminals in self.terminals.values_mut() {
            terminals.sort_by(|a, b| a.id.cmp(&b.id));
            terminals.dedup();
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RootTrace {
    store_site: String,
    root_id: String,
    root_label: String,
    evidence: RootEvidence,
    path: Vec<String>,
}

fn flags_for_path(path: SyntheticPath) -> BTreeSet<CauseFlag> {
    let mut flags = BTreeSet::new();
    match path.terminal {
        TerminalKind::RecognizedAllocation => {
            if path.crosses_call {
                flags.insert(CauseFlag::InterproceduralAllocation);
            }
            if path.crosses_field {
                flags.insert(CauseFlag::FieldMediatedAllocation);
            }
            if path.realloc {
                flags.insert(CauseFlag::ReallocAllocation);
            }
            if path.same_function_scanner_gap {
                flags.insert(CauseFlag::SameFunctionScannerGap);
            }
        }
        TerminalKind::StaticOrInterior => {
            flags.insert(CauseFlag::StaticOrInteriorRoot);
        }
        TerminalKind::ExternalParameter => {
            flags.insert(CauseFlag::ExternallySuppliedParameter);
        }
        TerminalKind::OpaqueExternalCall => {
            flags.insert(CauseFlag::OpaqueExternalCallResult);
        }
        TerminalKind::StackOrLocalAddress => {
            flags.insert(CauseFlag::StackOrLocalAddress);
        }
        TerminalKind::Unsupported => {}
    }
    flags
}

fn classify_roots(roots: &[RootEvidence]) -> PrimaryClass {
    if roots.is_empty() || roots.iter().any(|root| root.flags.is_empty()) {
        return PrimaryClass::Unresolved;
    }
    let invisible = roots.iter().any(|root| {
        root.flags.iter().any(|flag| {
            matches!(
                flag,
                CauseFlag::InterproceduralAllocation
                    | CauseFlag::FieldMediatedAllocation
                    | CauseFlag::ReallocAllocation
                    | CauseFlag::SameFunctionScannerGap
            )
        })
    });
    let absent = roots.iter().any(|root| {
        root.flags.iter().any(|flag| {
            matches!(
                flag,
                CauseFlag::StaticOrInteriorRoot
                    | CauseFlag::ExternallySuppliedParameter
                    | CauseFlag::OpaqueExternalCallResult
                    | CauseFlag::StackOrLocalAddress
            )
        })
    });
    match (invisible, absent) {
        (true, true) => PrimaryClass::Mixed,
        (true, false) => PrimaryClass::Invisible,
        (false, true) => PrimaryClass::Absent,
        (false, false) => PrimaryClass::Unresolved,
    }
}

fn validate_trace_shape(roots: &[RootTrace]) -> Result<(), String> {
    if roots.is_empty() {
        return Err("trace has no roots".to_owned());
    }
    for root in roots {
        if root.store_site.is_empty() || root.path.is_empty() {
            return Err(format!("malformed root path: {}", root.root_id));
        }
    }
    Ok(())
}

fn validate_exact_identities(expected: &[Identity], actual: &[Identity]) -> Result<(), String> {
    let expected_set = expected.iter().collect::<BTreeSet<_>>();
    let actual_set = actual.iter().collect::<BTreeSet<_>>();
    if expected_set.len() != expected.len() {
        return Err("expected identities contain duplicates".to_owned());
    }
    if actual_set.len() != actual.len() {
        return Err("actual identities contain duplicates".to_owned());
    }
    if expected_set != actual_set {
        return Err(format!(
            "identity mismatch: missing={:?} extra={:?}",
            expected_set.difference(&actual_set).collect::<Vec<_>>(),
            actual_set.difference(&expected_set).collect::<Vec<_>>()
        ));
    }
    Ok(())
}

fn validate_completed_shard(gate: ShardGate) -> Result<(), String> {
    if gate.data && gate.completed && gate.manifested {
        Ok(())
    } else {
        Err(format!("incomplete shard: {gate:?}"))
    }
}

fn parse_cause_flag(value: &str) -> Result<CauseFlag, String> {
    match value {
        "interprocedural-allocation" => Ok(CauseFlag::InterproceduralAllocation),
        "field-mediated-allocation" => Ok(CauseFlag::FieldMediatedAllocation),
        "realloc-allocation" => Ok(CauseFlag::ReallocAllocation),
        "same-function-scanner-gap" => Ok(CauseFlag::SameFunctionScannerGap),
        "static-or-interior-root" => Ok(CauseFlag::StaticOrInteriorRoot),
        "externally-supplied-parameter" => Ok(CauseFlag::ExternallySuppliedParameter),
        "opaque-external-call-result" => Ok(CauseFlag::OpaqueExternalCallResult),
        "stack-or-local-address" => Ok(CauseFlag::StackOrLocalAddress),
        _ => Err(format!("unknown cause flag {value:?}")),
    }
}

fn exception_specs() -> Vec<ExceptionSpec> {
    vec![
        ExceptionSpec {
            program: "brotli",
            field_key: "src::enc::backward_references::H35::field4@d0",
            ordinary_kind: "raw",
        },
        ExceptionSpec {
            program: "brotli",
            field_key: "src::enc::backward_references::H55::field4@d0",
            ordinary_kind: "raw",
        },
        ExceptionSpec {
            program: "brotli",
            field_key: "src::enc::backward_references::H65::field4@d0",
            ordinary_kind: "raw",
        },
        ExceptionSpec {
            program: "lil",
            field_key: "src::lil::_lil_t::field20@d0",
            ordinary_kind: "ref",
        },
    ]
}

fn phase_line(phase: &str, candidate: Option<&str>, completed: usize) -> String {
    format!(
        "BOC1PHASE a4-source-census phase={phase} candidate={} completed={completed}",
        candidate.unwrap_or("none")
    )
}

fn write_atomic_checkpoint(path: &Path, contents: &str) -> Result<(), String> {
    let temp = path.with_extension("tsv.tmp");
    fs::write(&temp, contents).map_err(|error| format!("write {}: {error}", temp.display()))?;
    fs::rename(&temp, path).map_err(|error| {
        format!(
            "publish checkpoint {} from {}: {error}",
            path.display(),
            temp.display()
        )
    })
}

fn trace_candidate(graph: &SourceGraph, target: &str) -> Vec<RootTrace> {
    #[derive(Clone)]
    struct Work {
        node: String,
        store_site: String,
        crosses_call: bool,
        crosses_field: bool,
        path: Vec<String>,
    }

    let mut roots = BTreeMap::<(String, String, BTreeSet<CauseFlag>), RootTrace>::new();
    for terminal in graph.terminals.get(target).into_iter().flatten() {
        let flags = flags_for_path(SyntheticPath {
            terminal: terminal.kind,
            crosses_call: false,
            crosses_field: false,
            realloc: terminal.realloc,
            same_function_scanner_gap: terminal.kind == TerminalKind::RecognizedAllocation
                && !terminal.realloc,
        });
        roots.insert(
            (terminal.label.clone(), terminal.id.clone(), flags.clone()),
            RootTrace {
                store_site: terminal.label.clone(),
                root_id: terminal.id.clone(),
                root_label: terminal.label.clone(),
                evidence: RootEvidence { flags },
                path: vec![terminal.label.clone()],
            },
        );
    }

    let mut work = VecDeque::new();
    for edge in graph.incoming.get(target).into_iter().flatten() {
        work.push_back(Work {
            node: edge.source.clone(),
            store_site: edge.label.clone(),
            crosses_call: edge.kind == FlowEdgeKind::Call,
            // The first edge is the target field's own store and does not make
            // the source field-mediated.
            crosses_field: false,
            path: vec![edge.label.clone()],
        });
    }
    if work.is_empty() && roots.is_empty() {
        return vec![RootTrace {
            store_site: "none".to_owned(),
            root_id: format!("unresolved:{target}"),
            root_label: "candidate has no relevant store input".to_owned(),
            evidence: RootEvidence {
                flags: BTreeSet::new(),
            },
            path: Vec::new(),
        }];
    }

    let mut seen = BTreeSet::new();
    while let Some(state) = work.pop_front() {
        if !seen.insert((
            state.store_site.clone(),
            state.node.clone(),
            state.crosses_call,
            state.crosses_field,
        )) {
            continue;
        }
        let mut found_terminal = false;
        for terminal in graph.terminals.get(&state.node).into_iter().flatten() {
            found_terminal = true;
            let flags = flags_for_path(SyntheticPath {
                terminal: terminal.kind,
                crosses_call: state.crosses_call,
                crosses_field: state.crosses_field,
                realloc: terminal.realloc,
                same_function_scanner_gap: terminal.kind == TerminalKind::RecognizedAllocation
                    && !terminal.realloc
                    && !state.crosses_call
                    && !state.crosses_field,
            });
            let mut path = state.path.clone();
            path.push(terminal.label.clone());
            path.reverse();
            roots
                .entry((state.store_site.clone(), terminal.id.clone(), flags.clone()))
                .and_modify(|root| {
                    if path.len() < root.path.len()
                        || (path.len() == root.path.len() && path < root.path)
                    {
                        root.path = path.clone();
                    }
                })
                .or_insert_with(|| RootTrace {
                    store_site: state.store_site.clone(),
                    root_id: terminal.id.clone(),
                    root_label: terminal.label.clone(),
                    evidence: RootEvidence { flags },
                    path,
                });
        }

        let incoming = graph.incoming.get(&state.node);
        if incoming.is_none_or(Vec::is_empty) && !found_terminal {
            roots
                .entry((
                    state.store_site.clone(),
                    format!("unresolved:{}", state.node),
                    BTreeSet::new(),
                ))
                .or_insert_with(|| {
                    let mut path = state.path.clone();
                    path.reverse();
                    RootTrace {
                        store_site: state.store_site.clone(),
                        root_id: format!("unresolved:{}", state.node),
                        root_label: format!("unclassified terminal {}", state.node),
                        evidence: RootEvidence {
                            flags: BTreeSet::new(),
                        },
                        path,
                    }
                });
        }
        for edge in incoming.into_iter().flatten() {
            let mut path = state.path.clone();
            path.push(edge.label.clone());
            work.push_back(Work {
                node: edge.source.clone(),
                store_site: state.store_site.clone(),
                crosses_call: state.crosses_call || edge.kind == FlowEdgeKind::Call,
                crosses_field: state.crosses_field || edge.kind == FlowEdgeKind::Field,
                path,
            });
        }
    }
    roots.into_values().collect()
}

fn field_key(tcx: TyCtxt<'_>, slots: &CrateSlots, field: SlotId) -> String {
    let slot = slots.field_slots.slot(field);
    let SlotOwner::Field(owner) = slot.owner else {
        unreachable!("field universe contains a local owner")
    };
    format!(
        "{}::field{}@d{}",
        tcx.def_path_str(owner.struct_did.to_def_id()),
        owner.field_index,
        slot.depth
    )
}

fn node_for_resolved(
    tcx: TyCtxt<'_>,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    resolved: ResolvedSlot,
) -> String {
    match resolved {
        ResolvedSlot::Local(slot) => {
            format!("local:{}:slot{}", tcx.def_path_str(fn_did), slot.index())
        }
        ResolvedSlot::Field(field) => field_key(tcx, slots, field),
    }
}

fn node_for_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    place: Place<'tcx>,
) -> Option<String> {
    resolve_place(slots, fn_did, body, place, 0, None)
        .map(|resolved| node_for_resolved(tcx, slots, fn_did, resolved))
}

fn node_for_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<String> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            node_for_place(tcx, slots, fn_did, body, *place)
        }
        Operand::Constant(_) => None,
    }
}

fn edge_kind(source: &str, target: &str) -> FlowEdgeKind {
    if source.starts_with("src::") || target.starts_with("src::") {
        FlowEdgeKind::Field
    } else {
        FlowEdgeKind::Local
    }
}

fn add_value_edge(graph: &mut SourceGraph, source: Option<String>, target: String, label: String) {
    if let Some(source) = source {
        graph.add_edge(FlowEdge {
            kind: edge_kind(&source, &target),
            source,
            target,
            label,
        });
    }
}

fn terminal_id(kind: TerminalKind, node: &str, label: &str) -> String {
    format!("{kind:?}:{node}:{label}")
}

fn add_terminal(
    graph: &mut SourceGraph,
    node: String,
    kind: TerminalKind,
    label: String,
    realloc: bool,
) {
    graph.add_terminal(TerminalRoot {
        id: terminal_id(kind, &node, &label),
        node,
        kind,
        label,
        realloc,
    });
}

fn roles_for_name(name: &str) -> Vec<crate::analyses::borrow_ownership::boundary_table::Role> {
    use crate::analyses::borrow_ownership::boundary_table::TABLE;
    TABLE
        .iter()
        .filter(|entry| entry.name == name)
        .flat_map(|entry| entry.roles.iter().copied())
        .collect()
}

#[derive(Clone, Debug)]
enum HarnessCallKind {
    Local(LocalDefId),
    LibC(String),
    RustLib(DefId),
    Unresolved,
}

struct HarnessCall<'call, 'tcx> {
    kind: HarnessCallKind,
    args: &'call [Spanned<Operand<'tcx>>],
    destination: Place<'tcx>,
}

fn harness_call_kind(tcx: TyCtxt<'_>, function: &Operand<'_>) -> HarnessCallKind {
    let Some(constant) = function.constant() else {
        return HarnessCallKind::Unresolved;
    };
    let TyKind::FnDef(callee, _) = constant.ty().kind() else {
        return HarnessCallKind::Unresolved;
    };
    let Some(local) = callee.as_local() else {
        return HarnessCallKind::RustLib(*callee);
    };
    match tcx.hir_node_by_def_id(local) {
        rustc_hir::Node::Item(_) | rustc_hir::Node::ImplItem(_) => HarnessCallKind::Local(local),
        rustc_hir::Node::ForeignItem(item) => {
            HarnessCallKind::LibC(item.ident.name.as_str().to_owned())
        }
        _ => HarnessCallKind::Unresolved,
    }
}

fn harness_call<'call, 'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &'call Terminator<'tcx>,
) -> Option<HarnessCall<'call, 'tcx>> {
    match &terminator.kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => Some(HarnessCall {
            kind: harness_call_kind(tcx, func),
            args,
            destination: *destination,
        }),
        TerminatorKind::TailCall { func, args, .. } => Some(HarnessCall {
            kind: harness_call_kind(tcx, func),
            args,
            destination: Place::return_place(),
        }),
        _ => None,
    }
}

fn build_source_graph(tcx: TyCtxt<'_>, slots: &CrateSlots, export: &BoExport) -> SourceGraph {
    use crate::analyses::borrow_ownership::boundary_table::Role;

    let program = collect_program(tcx);
    let program_functions = program.functions.iter().copied().collect::<FxHashSet<_>>();
    let mut graph = SourceGraph::default();
    let mut parameter_nodes = Vec::<(LocalDefId, Local, String)>::new();
    let mut called_parameters = BTreeSet::<String>::new();
    let mut has_unresolved_indirect_call = false;

    for &fn_did in &program.functions {
        let body_ref = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        let body = &*body_ref;
        for local in body.args_iter() {
            if let Some(node) = node_for_place(tcx, slots, fn_did, body, Place::from(local)) {
                parameter_nodes.push((fn_did, local, node));
            }
        }

        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                    continue;
                };
                let location = format!(
                    "{}:bb{}[{}]",
                    tcx.def_path_str(fn_did),
                    bb.index(),
                    statement_index
                );

                if let Rvalue::Aggregate(kind, operands) = rvalue
                    && let AggregateKind::Adt(def_id, _, _, _, _) = kind.as_ref()
                    && let Some(struct_did) = def_id.as_local()
                {
                    for (field_index, operand) in operands.iter_enumerated() {
                        let Some(field) = slots.field_slots.slot_for_field_depth(
                            crate::analyses::borrow_ownership::slots::StructFieldSlot {
                                struct_did,
                                field_index: field_index.index(),
                            },
                            0,
                        ) else {
                            continue;
                        };
                        let target = field_key(tcx, slots, field);
                        let label =
                            format!("aggregate-store:{location}:field{}", field_index.index());
                        if let Some(source) = node_for_operand(tcx, slots, fn_did, body, operand) {
                            add_value_edge(&mut graph, Some(source), target, label);
                        } else {
                            add_terminal(
                                &mut graph,
                                target,
                                TerminalKind::Unsupported,
                                format!("constant-{label}"),
                                false,
                            );
                        }
                    }
                    continue;
                }

                let Some(target) = node_for_place(tcx, slots, fn_did, body, *lhs) else {
                    continue;
                };
                match rvalue {
                    Rvalue::Use(Operand::Constant(_))
                    | Rvalue::Cast(_, Operand::Constant(_), _) => add_terminal(
                        &mut graph,
                        target,
                        TerminalKind::Unsupported,
                        format!("constant-pointer:{location}"),
                        false,
                    ),
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => add_value_edge(
                        &mut graph,
                        node_for_operand(tcx, slots, fn_did, body, operand),
                        target,
                        format!("transfer:{location}"),
                    ),
                    Rvalue::CopyForDeref(place) => add_value_edge(
                        &mut graph,
                        node_for_place(tcx, slots, fn_did, body, *place),
                        target,
                        format!("copy-for-deref:{location}"),
                    ),
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        if place
                            .projection
                            .iter()
                            .any(|projection| matches!(projection, ProjectionElem::Deref))
                        {
                            add_value_edge(
                                &mut graph,
                                node_for_place(tcx, slots, fn_did, body, Place::from(place.local)),
                                target,
                                format!("address-through-pointer:{location}:{place:?}"),
                            );
                        } else {
                            add_terminal(
                                &mut graph,
                                target,
                                TerminalKind::StackOrLocalAddress,
                                format!("address-of-local:{location}:{place:?}"),
                                false,
                            );
                        }
                    }
                    Rvalue::ThreadLocalRef(def_id) => add_terminal(
                        &mut graph,
                        target,
                        TerminalKind::StaticOrInterior,
                        format!("thread-local:{location}:{}", tcx.def_path_str(*def_id)),
                        false,
                    ),
                    Rvalue::BinaryOp(_, operands) => {
                        for operand in [&operands.0, &operands.1] {
                            add_value_edge(
                                &mut graph,
                                node_for_operand(tcx, slots, fn_did, body, operand),
                                target.clone(),
                                format!("binary-transfer:{location}"),
                            );
                        }
                    }
                    other => add_terminal(
                        &mut graph,
                        target,
                        TerminalKind::Unsupported,
                        format!("unsupported-rvalue:{location}:{other:?}"),
                        false,
                    ),
                }
            }

            let Some(call) = harness_call(tcx, data.terminator()) else {
                continue;
            };
            let call_location = format!("{}:bb{}:call", tcx.def_path_str(fn_did), bb.index());
            let call_key = location_key(Location {
                block: bb,
                statement_index: data.statements.len(),
            });
            let destination = node_for_place(tcx, slots, fn_did, body, call.destination);
            match call.kind {
                HarnessCallKind::Local(callee) if program_functions.contains(&callee) => {
                    let callee_body_ref =
                        tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
                    let callee_body = &*callee_body_ref;
                    for (index, argument) in call.args.iter().enumerate() {
                        let parameter = Local::from_usize(index + 1);
                        let Some(target) =
                            node_for_place(tcx, slots, callee, callee_body, Place::from(parameter))
                        else {
                            continue;
                        };
                        if let Some(source) =
                            node_for_operand(tcx, slots, fn_did, body, &argument.node)
                        {
                            called_parameters.insert(target.clone());
                            graph.add_edge(FlowEdge {
                                source,
                                target,
                                kind: FlowEdgeKind::Call,
                                label: format!(
                                    "call-arg:{call_location}->{}:arg{}",
                                    tcx.def_path_str(callee),
                                    index + 1
                                ),
                            });
                        }
                    }
                    if let Some(target) = destination
                        && let Some(source) = node_for_place(
                            tcx,
                            slots,
                            callee,
                            callee_body,
                            Place::from(RETURN_PLACE),
                        )
                    {
                        graph.add_edge(FlowEdge {
                            source,
                            target,
                            kind: FlowEdgeKind::Call,
                            label: format!(
                                "call-return:{}->{call_location}",
                                tcx.def_path_str(callee)
                            ),
                        });
                    }
                }
                HarnessCallKind::Local(callee) => {
                    if let Some(target) = destination {
                        add_terminal(
                            &mut graph,
                            target,
                            TerminalKind::Unsupported,
                            format!(
                                "unresolved-local-call:{call_location}:{}",
                                tcx.def_path_str(callee)
                            ),
                            false,
                        );
                    }
                }
                HarnessCallKind::LibC(name) => {
                    let roles = roles_for_name(&name);
                    if let Some(target) = destination {
                        if roles.contains(&Role::Source) {
                            let exported = export.source_sites.iter().any(|site| {
                                site.call.as_ref().is_some_and(|site| {
                                    site.fn_did == fn_did
                                        && site.location == call_key
                                        && site.callee == name
                                })
                            });
                            add_terminal(
                                &mut graph,
                                target,
                                if exported {
                                    TerminalKind::RecognizedAllocation
                                } else {
                                    TerminalKind::Unsupported
                                },
                                format!("allocator:{call_location}:{name}:exported={exported}"),
                                name == "realloc",
                            );
                        } else if roles.iter().any(|role| {
                            matches!(
                                role,
                                Role::ProvenanceFlow | Role::LoanCreating | Role::FlowTransfer
                            )
                        }) {
                            add_value_edge(
                                &mut graph,
                                call.args.first().and_then(|arg| {
                                    node_for_operand(tcx, slots, fn_did, body, &arg.node)
                                }),
                                target,
                                format!("foreign-flow:{call_location}:{name}"),
                            );
                        } else {
                            add_terminal(
                                &mut graph,
                                target,
                                TerminalKind::OpaqueExternalCall,
                                format!("foreign-result:{call_location}:{name}"),
                                false,
                            );
                        }
                    }
                }
                HarnessCallKind::RustLib(callee) => {
                    if let Some(target) = destination {
                        let item_name = tcx.item_name(callee);
                        let name = item_name.as_str();
                        let roles = roles_for_name(name);
                        if roles
                            .iter()
                            .any(|role| matches!(role, Role::ProvenanceFlow | Role::LoanCreating))
                        {
                            add_value_edge(
                                &mut graph,
                                call.args.first().and_then(|arg| {
                                    node_for_operand(tcx, slots, fn_did, body, &arg.node)
                                }),
                                target,
                                format!("rust-flow:{call_location}:{name}"),
                            );
                        } else if roles.contains(&Role::NullConstructor) {
                            add_terminal(
                                &mut graph,
                                target,
                                TerminalKind::Unsupported,
                                format!("null-constructor:{call_location}:{name}"),
                                false,
                            );
                        } else {
                            add_terminal(
                                &mut graph,
                                target,
                                TerminalKind::OpaqueExternalCall,
                                format!("rust-result:{call_location}:{name}"),
                                false,
                            );
                        }
                    }
                }
                HarnessCallKind::Unresolved => {
                    has_unresolved_indirect_call = true;
                    if let Some(target) = destination {
                        add_terminal(
                            &mut graph,
                            target,
                            TerminalKind::Unsupported,
                            format!("unresolved-indirect-call:{call_location}"),
                            false,
                        );
                    }
                }
            }
        }
    }

    for (fn_did, local, node) in parameter_nodes {
        let public = tcx.visibility(fn_did.to_def_id()).is_public();
        if public || !called_parameters.contains(&node) {
            add_terminal(
                &mut graph,
                node,
                if public || !has_unresolved_indirect_call {
                    TerminalKind::ExternalParameter
                } else {
                    TerminalKind::Unsupported
                },
                format!(
                    "external-parameter:{}:{local:?}:unresolved-indirect={has_unresolved_indirect_call}",
                    tcx.def_path_str(fn_did)
                ),
                false,
            );
        }
    }
    graph.canonicalize();
    graph
}

const A4_INPUT_HEADER: &str = "program\tfield_key\tfield_slot\tbaseline_kind\tbaseline_force\tbaseline_core_families\tproof_eligible\tproof_reason\tselected_own_assumes\tsource_selector_indices\tnecessary_labels\trelaxed_force\trelaxed_kind\trelaxed_core_families\trelaxed_core_labels";

#[derive(Clone, Debug, PartialEq, Eq)]
struct A4InputRow {
    program: String,
    field_key: String,
    field_slot: usize,
    baseline_kind: SlotKind,
    baseline_force: String,
    proof_reason: String,
}

fn parse_kind(value: &str) -> Result<SlotKind, String> {
    match value {
        "raw" => Ok(SlotKind::Raw),
        "ref" => Ok(SlotKind::Ref),
        "owning" => Ok(SlotKind::Owning),
        _ => Err(format!("unknown kind {value:?}")),
    }
}

fn kind_label(kind: SlotKind) -> &'static str {
    match kind {
        SlotKind::Raw => "raw",
        SlotKind::Ref => "ref",
        SlotKind::Owning => "owning",
    }
}

fn parse_a4_input(path: &Path) -> Result<Vec<A4InputRow>, String> {
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read A4 input {}: {error}", path.display()))?;
    let mut lines = input.lines();
    if lines.next() != Some(A4_INPUT_HEADER) {
        return Err(format!("A4 input header drift: {}", path.display()));
    }
    let mut identities = BTreeSet::new();
    let mut rows = Vec::new();
    for (offset, line) in lines.enumerate() {
        let columns = line.split('\t').collect::<Vec<_>>();
        if columns.len() != 15 {
            return Err(format!(
                "A4 input line {} has {} columns",
                offset + 2,
                columns.len()
            ));
        }
        let identity = Identity {
            program: columns[0].to_owned(),
            field_key: columns[1].to_owned(),
        };
        if !identities.insert(identity.clone()) {
            return Err(format!(
                "duplicate A4 identity {} {}",
                identity.program, identity.field_key
            ));
        }
        if !matches!(columns[4], "sat" | "unsat") {
            return Err(format!(
                "A4 input line {} has unsupported baseline force {:?}",
                offset + 2,
                columns[4]
            ));
        }
        rows.push(A4InputRow {
            program: identity.program,
            field_key: identity.field_key,
            field_slot: columns[2]
                .parse()
                .map_err(|error| format!("A4 input line {} slot: {error}", offset + 2))?,
            baseline_kind: parse_kind(columns[3])?,
            baseline_force: columns[4].to_owned(),
            proof_reason: columns[7].to_owned(),
        });
    }
    if rows.len() != 261 {
        return Err(format!("A4 input expected 261 rows, got {}", rows.len()));
    }
    Ok(rows)
}

fn candidate_fields(tcx: TyCtxt<'_>, slots: &CrateSlots) -> BTreeMap<String, SlotId> {
    (0..slots.field_slots.len())
        .filter_map(|index| {
            let slot = SlotId::from_usize(index);
            (slots.field_slots.slot(slot).depth == 0).then(|| (field_key(tcx, slots, slot), slot))
        })
        .collect()
}

fn flag_label(flag: CauseFlag) -> &'static str {
    match flag {
        CauseFlag::InterproceduralAllocation => "interprocedural-allocation",
        CauseFlag::FieldMediatedAllocation => "field-mediated-allocation",
        CauseFlag::ReallocAllocation => "realloc-allocation",
        CauseFlag::SameFunctionScannerGap => "same-function-scanner-gap",
        CauseFlag::StaticOrInteriorRoot => "static-or-interior-root",
        CauseFlag::ExternallySuppliedParameter => "externally-supplied-parameter",
        CauseFlag::OpaqueExternalCallResult => "opaque-external-call-result",
        CauseFlag::StackOrLocalAddress => "stack-or-local-address",
    }
}

fn class_label(class: PrimaryClass) -> &'static str {
    match class {
        PrimaryClass::Invisible => "invisible",
        PrimaryClass::Absent => "absent",
        PrimaryClass::Mixed => "mixed",
        PrimaryClass::Unresolved => "unresolved",
    }
}

fn clean_cell(value: &str) -> String {
    value.replace(['\t', '\n', '\r'], "_")
}

#[derive(Clone, Debug)]
struct CandidateRecord {
    input: A4InputRow,
    class: PrimaryClass,
    flags: BTreeSet<CauseFlag>,
    roots: Vec<RootTrace>,
}

fn render_candidates(records: &[CandidateRecord]) -> String {
    let mut out = String::from(
        "program\tfield_key\tfield_slot\tordinary_kind\tprimary_class\tcause_flags\troot_count\n",
    );
    for record in records {
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            clean_cell(&record.input.program),
            clean_cell(&record.input.field_key),
            record.input.field_slot,
            kind_label(record.input.baseline_kind),
            class_label(record.class),
            record
                .flags
                .iter()
                .map(|flag| flag_label(*flag))
                .collect::<Vec<_>>()
                .join("|"),
            record.roots.len(),
        ));
    }
    out
}

fn render_roots(records: &[CandidateRecord], exceptions: &[ExceptionRecord]) -> String {
    let mut out = String::from(
        "population\tprogram\tfield_key\tstore_site\troot_id\troot_label\tcause_flags\tordered_path\n",
    );
    for record in records {
        for root in &record.roots {
            out.push_str(&format!(
                "census\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                clean_cell(&record.input.program),
                clean_cell(&record.input.field_key),
                clean_cell(&root.store_site),
                clean_cell(&root.root_id),
                clean_cell(&root.root_label),
                root.evidence
                    .flags
                    .iter()
                    .map(|flag| flag_label(*flag))
                    .collect::<Vec<_>>()
                    .join("|"),
                clean_cell(&root.path.join(" -> ")),
            ));
        }
    }
    for record in exceptions {
        for root in &record.roots {
            out.push_str(&format!(
                "exception\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                clean_cell(&record.input.program),
                clean_cell(&record.input.field_key),
                clean_cell(&root.store_site),
                clean_cell(&root.root_id),
                clean_cell(&root.root_label),
                root.evidence
                    .flags
                    .iter()
                    .map(|flag| flag_label(*flag))
                    .collect::<Vec<_>>()
                    .join("|"),
                clean_cell(&root.path.join(" -> ")),
            ));
        }
    }
    out
}

fn selector_state(solver: &KindSolver, selectors: &Selectors) -> (Vec<usize>, Vec<usize>) {
    let model = solver
        .optimize()
        .get_model()
        .expect("accepted solver has a model");
    let states = |values: &[z3::ast::Bool]| {
        values
            .iter()
            .enumerate()
            .filter_map(|(index, selector)| {
                (!model
                    .eval(selector, true)
                    .and_then(|value| value.as_bool())
                    .unwrap_or(false))
                .then_some(index)
            })
            .collect::<Vec<_>>()
    };
    (states(selectors.sources()), states(selectors.sinks()))
}

fn render_slot(slot: SlotRef) -> String {
    match slot {
        SlotRef::Local(fn_did, slot) => format!("local:{fn_did:?}:{}", slot.index()),
        SlotRef::Field(slot) => format!("field:{}", slot.index()),
    }
}

#[derive(Clone, Debug)]
struct ExceptionRecord {
    input: A4InputRow,
    force_result: String,
    replay_result: String,
    replay_kind: Option<SlotKind>,
    causal_outcome: String,
    ordinary_dropped_sources: Vec<usize>,
    ordinary_dropped_sinks: Vec<usize>,
    forced_dropped_sources: Vec<usize>,
    forced_dropped_sinks: Vec<usize>,
    replay_dropped_sources: Vec<usize>,
    replay_dropped_sinks: Vec<usize>,
    model_changes: Vec<String>,
    ordinary_commits: Vec<String>,
    forced_commits: Vec<String>,
    source_count: usize,
    sink_count: usize,
    source_inventory: Vec<String>,
    sink_inventory: Vec<String>,
    graph_root_count: usize,
    graph_flags: BTreeSet<CauseFlag>,
    allocation_token_path: bool,
    unsupported_realloc: bool,
    roots: Vec<RootTrace>,
}

fn render_exceptions(records: &[ExceptionRecord]) -> String {
    let mut out = String::from(
        "program\tfield_key\tfield_slot\tordinary_kind\tforce_result\treplay_result\treplay_kind\tcausal_outcome\tsource_selectors\tsink_selectors\tsource_inventory\tsink_inventory\tordinary_dropped_sources\tordinary_dropped_sinks\tforced_dropped_sources\tforced_dropped_sinks\treplay_dropped_sources\treplay_dropped_sinks\tmodel_changes\tordinary_commits\tforced_commits\tgraph_root_count\tgraph_flags\tallocation_token_path\tunsupported_realloc\tcopy_clone_gate\tabi_gate\tfn_pointer_gate\n",
    );
    for record in records {
        let indices = |values: &[usize]| {
            values
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join("|")
        };
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            clean_cell(&record.input.program),
            clean_cell(&record.input.field_key),
            record.input.field_slot,
            kind_label(record.input.baseline_kind),
            record.force_result,
            record.replay_result,
            record.replay_kind.map(kind_label).unwrap_or("-"),
            record.causal_outcome,
            record.source_count,
            record.sink_count,
            clean_cell(&record.source_inventory.join("|")),
            clean_cell(&record.sink_inventory.join("|")),
            indices(&record.ordinary_dropped_sources),
            indices(&record.ordinary_dropped_sinks),
            indices(&record.forced_dropped_sources),
            indices(&record.forced_dropped_sinks),
            indices(&record.replay_dropped_sources),
            indices(&record.replay_dropped_sinks),
            clean_cell(&record.model_changes.join("|")),
            clean_cell(&record.ordinary_commits.join("|")),
            clean_cell(&record.forced_commits.join("|")),
            record.graph_root_count,
            record
                .graph_flags
                .iter()
                .map(|flag| flag_label(*flag))
                .collect::<Vec<_>>()
                .join("|"),
            record.allocation_token_path,
            record.unsupported_realloc,
            "not-reached:ordinary-kind-not-owning",
            "not-reached:ordinary-kind-not-owning",
            "not-reached:ordinary-kind-not-owning",
        ));
    }
    out
}

fn render_checkpoint(
    phase: &str,
    candidate: &str,
    elapsed_s: f64,
    candidates: &[CandidateRecord],
    exceptions: &[ExceptionRecord],
) -> String {
    format!(
        "data=false\nphase={}\ncandidate={}\nelapsed_s={elapsed_s:.3}\ncandidates_completed={}\nexceptions_completed={}\n\n{}\n{}",
        clean_cell(phase),
        clean_cell(candidate),
        candidates.len(),
        exceptions.len(),
        render_candidates(candidates),
        render_exceptions(exceptions),
    )
}

fn emit_phase(started: Instant, phase: &str, candidate: Option<&str>, completed: usize) {
    eprintln!(
        "{} t_s={:.3}",
        phase_line(phase, candidate, completed),
        started.elapsed().as_secs_f64()
    );
}

fn commit_lines(
    commits: &[crate::analyses::borrow_ownership::borrow_verify::ModeACommitTrace],
) -> Vec<String> {
    commits
        .iter()
        .map(|commit| {
            format!(
                "round{}:{}:issuer={}:requirers={}",
                commit.round,
                render_slot(commit.target),
                commit
                    .conflict
                    .issuer
                    .map(render_slot)
                    .unwrap_or_else(|| "none".to_owned()),
                commit
                    .conflict
                    .requirers
                    .iter()
                    .copied()
                    .map(render_slot)
                    .collect::<Vec<_>>()
                    .join(",")
            )
        })
        .collect()
}

fn selector_inventory(tcx: TyCtxt<'_>, sites: &[SelectorSite], dropped: &[usize]) -> Vec<String> {
    sites
        .iter()
        .enumerate()
        .map(|(index, site)| {
            let status = if dropped.contains(&index) {
                "dropped"
            } else {
                "retained"
            };
            match &site.call {
                Some(call) => format!(
                    "{index}:{}@{}:{:?}:{status}",
                    call.callee,
                    tcx.def_path_str(call.fn_did),
                    call.location
                ),
                None => format!("{index}:no-call-site:{status}"),
            }
        })
        .collect()
}

fn replay_none_disposition(reason_unknown: Option<String>) -> Result<&'static str, String> {
    match reason_unknown {
        Some(reason) => Err(format!("solver Unknown: {reason}")),
        None => Ok("declined"),
    }
}

pub(super) fn run_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
    let started = Instant::now();
    let program_name = std::env::var("CRAT_BOC1_NAME").expect("source-census worker program name");
    let input_path =
        PathBuf::from(std::env::var_os("CRAT_A4_SOURCE_INPUT").expect("source-census A4 input"));
    let candidates_path = PathBuf::from(
        std::env::var_os("CRAT_A4_SOURCE_CANDIDATES").expect("source-census candidates output"),
    );
    let roots_path = PathBuf::from(
        std::env::var_os("CRAT_A4_SOURCE_ROOTS").expect("source-census roots output"),
    );
    let exceptions_path = PathBuf::from(
        std::env::var_os("CRAT_A4_SOURCE_EXCEPTIONS").expect("source-census exceptions output"),
    );
    let checkpoint_path = PathBuf::from(
        std::env::var_os("CRAT_A4_SOURCE_CHECKPOINT").expect("source-census checkpoint"),
    );

    emit_phase(started, "input-parse", None, 0);
    let input = parse_a4_input(&input_path)
        .unwrap_or_else(|error| panic!("A4C STOP phase=input-parse candidate=none: {error}"));
    let census_input = input
        .iter()
        .filter(|row| {
            row.program == program_name && row.proof_reason == "allocation-source-count-0"
        })
        .cloned()
        .collect::<Vec<_>>();
    let exception_input = input
        .iter()
        .filter(|row| row.program == program_name && row.baseline_force == "sat")
        .cloned()
        .collect::<Vec<_>>();
    assert!(
        census_input.iter().all(|row| row.baseline_force == "unsat"),
        "A4C STOP phase=input-partition candidate={program_name}: census row is not hard-UNSAT"
    );
    let expected_exceptions = exception_specs()
        .into_iter()
        .filter(|spec| spec.program == program_name)
        .map(|spec| (spec.field_key, spec.ordinary_kind))
        .collect::<BTreeSet<_>>();
    let actual_exceptions = exception_input
        .iter()
        .map(|row| (row.field_key.as_str(), kind_label(row.baseline_kind)))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        actual_exceptions, expected_exceptions,
        "A4C STOP phase=exception-identity candidate={program_name}: exact exception drift"
    );

    emit_phase(started, "analysis-start", None, 0);
    let program = collect_program(tcx);
    let origins = compute_origins(&program);
    let slots = CrateSlots::build(&program);
    let crate_ctxt = CrateCtxt::new(&program);
    let mutability = match MutFactsMode::current() {
        MutFactsMode::Off => MutFacts::all_mut(),
        MutFactsMode::On => MutFacts::from_program(&program),
    };
    let ordinary = KindSolver::new(&slots);
    let (
        (((ordinary_model, _ordinary_stats), ordinary_commits), ordinary_selectors),
        _ordinary_export,
    ) = with_bo_export(|| {
        let (_stats, selectors) =
            emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &ordinary)
                .expect("A4C ordinary ownership emission");
        for &fn_did in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
            add_coherence(&ordinary, &slots, fn_did, &body);
        }
        let ((model, stats), commits) = with_mode_a_commit_trace(|| {
            verify_to_fixpoint_counting_with_flows(
                &program,
                &slots,
                origins.native_flows(),
                &ordinary,
                &selectors,
                &mutability,
            )
        });
        (((model, stats), commits), selectors)
    });
    let ordinary_model = ordinary_model.unwrap_or_else(|| {
        panic!("A4C STOP phase=ordinary candidate=none: selector-off baseline declined")
    });
    let (ordinary_dropped_sources, ordinary_dropped_sinks) =
        selector_state(&ordinary, &ordinary_selectors);
    emit_phase(started, "graph-construction", None, 0);
    let graph = build_source_graph(tcx, &slots, &_ordinary_export);
    let fields = candidate_fields(tcx, &slots);

    let mut candidate_records = Vec::with_capacity(census_input.len());
    let mut exception_records = Vec::with_capacity(exception_input.len());
    write_atomic_checkpoint(
        &checkpoint_path,
        &render_checkpoint(
            "graph-construction",
            "none",
            started.elapsed().as_secs_f64(),
            &candidate_records,
            &exception_records,
        ),
    )
    .unwrap_or_else(|error| panic!("A4C STOP phase=checkpoint candidate=none: {error}"));
    emit_phase(started, "checkpoint-written", None, 0);
    for input_row in census_input {
        let key = input_row.field_key.clone();
        emit_phase(
            started,
            "source-traversal",
            Some(&key),
            candidate_records.len(),
        );
        let field = *fields.get(&key).unwrap_or_else(|| {
            panic!("A4C STOP phase=field-identity candidate={key}: field not re-derived")
        });
        assert_eq!(
            field.index(),
            input_row.field_slot,
            "A4C STOP phase=field-identity candidate={key}: slot drift"
        );
        assert_eq!(
            ordinary_model.get(&SlotRef::Field(field)).copied(),
            Some(input_row.baseline_kind),
            "A4C STOP phase=ordinary-identity candidate={key}: kind drift"
        );
        let roots = trace_candidate(&graph, &key);
        validate_trace_shape(&roots).unwrap_or_else(|error| {
            panic!("A4C STOP phase=source-traversal candidate={key}: {error}")
        });
        let evidence = roots
            .iter()
            .map(|root| root.evidence.clone())
            .collect::<Vec<_>>();
        let class = classify_roots(&evidence);
        assert_ne!(
            class,
            PrimaryClass::Unresolved,
            "A4C STOP phase=source-traversal candidate={key}: unclassified root(s) {:?}",
            roots
                .iter()
                .filter(|root| root.evidence.flags.is_empty())
                .map(|root| (&root.root_id, &root.path))
                .collect::<Vec<_>>()
        );
        let flags = roots
            .iter()
            .flat_map(|root| root.evidence.flags.iter().copied())
            .collect();
        candidate_records.push(CandidateRecord {
            input: input_row,
            class,
            flags,
            roots,
        });
        write_atomic_checkpoint(
            &checkpoint_path,
            &render_checkpoint(
                "source-traversal",
                &key,
                started.elapsed().as_secs_f64(),
                &candidate_records,
                &exception_records,
            ),
        )
        .unwrap_or_else(|error| panic!("A4C STOP phase=checkpoint candidate={key}: {error}"));
        emit_phase(
            started,
            "checkpoint-written",
            Some(&key),
            candidate_records.len(),
        );
    }

    for input_row in exception_input {
        let key = input_row.field_key.clone();
        emit_phase(
            started,
            "exception-force",
            Some(&key),
            exception_records.len(),
        );
        let field = *fields.get(&key).unwrap_or_else(|| {
            panic!("A4C STOP phase=exception-identity candidate={key}: field not re-derived")
        });
        assert_eq!(field.index(), input_row.field_slot);
        let field_ref = SlotRef::Field(field);
        assert_eq!(
            ordinary_model.get(&field_ref).copied(),
            Some(input_row.baseline_kind),
            "A4C STOP phase=exception-ordinary candidate={key}: ordinary kind drift"
        );

        let forced = KindSolver::new(&slots);
        let (_stats, forced_selectors) =
            emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &forced)
                .expect("A4C forced ownership emission");
        for &fn_did in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
            add_coherence(&forced, &slots, fn_did, &body);
        }
        constrain_field_ownership(&forced, &slots, &program);
        for commit in &ordinary_commits {
            forced.add_borrow_exclusion(Some(commit.target), &[]);
        }
        forced.assert_owning(field_ref);
        match forced.optimize().check(&[]) {
            SatResult::Sat => {}
            SatResult::Unsat => {
                panic!("A4C STOP phase=exception-force candidate={key}: force verdict drift")
            }
            SatResult::Unknown => {
                panic!("A4C STOP phase=exception-force candidate={key}: solver Unknown")
            }
        }
        let forced_model = forced.model_kinds().unwrap_or_else(|| {
            panic!("A4C STOP phase=exception-force candidate={key}: model unavailable")
        });
        assert_eq!(forced_model.get(&field_ref), Some(&SlotKind::Owning));
        let (forced_dropped_sources, forced_dropped_sinks) =
            selector_state(&forced, &forced_selectors);

        emit_phase(
            started,
            "exception-replay",
            Some(&key),
            exception_records.len(),
        );
        let replay = KindSolver::new(&slots);
        let (_stats, replay_selectors) =
            emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &replay)
                .expect("A4C replay ownership emission");
        for &fn_did in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
            add_coherence(&replay, &slots, fn_did, &body);
        }
        replay.assert_owning(field_ref);
        let ((replay_model, _replay_stats), replay_commits) = with_mode_a_commit_trace(|| {
            verify_to_fixpoint_counting_with_flows(
                &program,
                &slots,
                origins.native_flows(),
                &replay,
                &replay_selectors,
                &mutability,
            )
        });
        let (replay_result, replay_kind, replay_drop_sources, replay_drop_sinks) =
            if let Some(model) = replay_model {
                let kind = model.get(&field_ref).copied().unwrap_or_else(|| {
                    panic!("A4C STOP phase=exception-replay candidate={key}: field absent")
                });
                assert_eq!(
                    kind,
                    SlotKind::Owning,
                    "A4C STOP phase=exception-replay candidate={key}: force lost"
                );
                let (sources, sinks) = selector_state(&replay, &replay_selectors);
                ("accepted".to_owned(), Some(kind), sources, sinks)
            } else {
                let disposition = replay_none_disposition(replay.optimize().get_reason_unknown())
                    .unwrap_or_else(|error| {
                        panic!("A4C STOP phase=exception-replay candidate={key}: {error}")
                    });
                (disposition.to_owned(), None, Vec::new(), Vec::new())
            };
        let mut model_changes = ordinary_model
            .iter()
            .filter_map(|(slot, ordinary_kind)| {
                let forced_kind = forced_model.get(slot)?;
                (ordinary_kind != forced_kind).then(|| {
                    format!(
                        "{}:{}->{}",
                        render_slot(*slot),
                        kind_label(*ordinary_kind),
                        kind_label(*forced_kind)
                    )
                })
            })
            .collect::<Vec<_>>();
        model_changes.sort();
        let roots = trace_candidate(&graph, &key);
        validate_trace_shape(&roots).unwrap_or_else(|error| {
            panic!("A4C STOP phase=exception-source candidate={key}: {error}")
        });
        assert!(
            roots.iter().all(|root| !root.evidence.flags.is_empty()),
            "A4C STOP phase=exception-source candidate={key}: unclassified root"
        );
        let graph_flags = roots
            .iter()
            .flat_map(|root| root.evidence.flags.iter().copied())
            .collect::<BTreeSet<_>>();
        let allocation_token_path = graph_flags.iter().any(|flag| {
            matches!(
                flag,
                CauseFlag::InterproceduralAllocation
                    | CauseFlag::FieldMediatedAllocation
                    | CauseFlag::ReallocAllocation
                    | CauseFlag::SameFunctionScannerGap
            )
        });
        let unsupported_realloc = graph_flags.contains(&CauseFlag::ReallocAllocation);
        exception_records.push(ExceptionRecord {
            input: input_row,
            force_result: "sat".to_owned(),
            causal_outcome: if replay_result == "accepted" {
                "objective-choice".to_owned()
            } else {
                "borrow-replay-decline".to_owned()
            },
            replay_result,
            replay_kind,
            ordinary_dropped_sources: ordinary_dropped_sources.clone(),
            ordinary_dropped_sinks: ordinary_dropped_sinks.clone(),
            forced_dropped_sources,
            forced_dropped_sinks,
            replay_dropped_sources: replay_drop_sources,
            replay_dropped_sinks: replay_drop_sinks,
            model_changes,
            ordinary_commits: commit_lines(&ordinary_commits),
            forced_commits: commit_lines(&replay_commits),
            source_count: forced_selectors.sources().len(),
            sink_count: forced_selectors.sinks().len(),
            source_inventory: selector_inventory(
                tcx,
                &_ordinary_export.source_sites,
                &ordinary_dropped_sources,
            ),
            sink_inventory: selector_inventory(
                tcx,
                &_ordinary_export.sink_sites,
                &ordinary_dropped_sinks,
            ),
            graph_root_count: roots.len(),
            graph_flags,
            allocation_token_path,
            unsupported_realloc,
            roots,
        });
        write_atomic_checkpoint(
            &checkpoint_path,
            &render_checkpoint(
                "exception-replay",
                &key,
                started.elapsed().as_secs_f64(),
                &candidate_records,
                &exception_records,
            ),
        )
        .unwrap_or_else(|error| panic!("A4C STOP phase=checkpoint candidate={key}: {error}"));
        emit_phase(
            started,
            "checkpoint-written",
            Some(&key),
            exception_records.len(),
        );
    }

    emit_phase(started, "finalize", None, candidate_records.len());
    write_atomic_checkpoint(&candidates_path, &render_candidates(&candidate_records))
        .unwrap_or_else(|error| panic!("A4C STOP phase=finalize candidate=candidates: {error}"));
    write_atomic_checkpoint(
        &roots_path,
        &render_roots(&candidate_records, &exception_records),
    )
    .unwrap_or_else(|error| panic!("A4C STOP phase=finalize candidate=roots: {error}"));
    write_atomic_checkpoint(&exceptions_path, &render_exceptions(&exception_records))
        .unwrap_or_else(|error| panic!("A4C STOP phase=finalize candidate=exceptions: {error}"));
    emit_phase(started, "complete", None, candidate_records.len());

    let mut row = Row::default();
    row.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    row.set("candidates", candidate_records.len());
    row.set("exceptions", exception_records.len());
    row.set(
        "roots",
        candidate_records
            .iter()
            .map(|record| record.roots.len())
            .sum::<usize>(),
    );
    row.set("status", "ok");
    row.set(
        "t_total_s",
        format!("{:.3}", started.elapsed().as_secs_f64()),
    );
    row
}

const MACHINE_ID: &str = "lambda7";
const PLATFORM: &str = "linux-x86_64";
const LIVENESS_BOUND_S: u64 = 14_400;
const A4_AGGREGATE_MANIFEST_SHA256: &str =
    "66f85f5a30b77ba7e26c66fda0cccb0becdff13b4a8a03da74bb8d08e34e7c71";
const A4_COMBINED_SHA256: &str = "d89d69fd3c6d1e10e565d13a680e7e3af42bf3465851e31c0ceafa7dbbf6dcae";
const CENSUS_IDENTITY_SHA256: &str =
    "02a0c1761188fa7483a6c6b57e0ac0e636fecd16e247ef8879ee0af32268c466";
const EXCEPTION_IDENTITY_SHA256: &str =
    "af909da0025f3e89de4c6de0f0dd6e6783ca52d7323c29676c8bee880f2c1904";
const RAW_CORPUS_DIGEST: &str = "9fc912af10fd3b235fe4d444d2fbac0bc521509b1c9447fc551acd0130e0e621";
const DERIVED_SUBSTRATE_DIGEST: &str =
    "db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6";
const SNAPSHOT_PATH: &str = "/home/p51lee/dev/agent-worktrees/m1-artifact-snapshots/3b26a0ff";

fn command_stdout(mut command: Command, description: &str) -> String {
    let output = command
        .output()
        .unwrap_or_else(|error| panic!("{description}: {error}"));
    assert!(
        output.status.success(),
        "{description}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).trim().to_owned()
}

fn sha256(path: &Path) -> String {
    try_sha256(path).unwrap_or_else(|error| panic!("sha256 {}: {error}", path.display()))
}

fn sha256_text(input: &str) -> String {
    try_sha256_text(input).expect("sha256sum text failed")
}

fn try_sha256(path: &Path) -> Result<String, String> {
    let output = Command::new("sha256sum")
        .arg(path)
        .output()
        .map_err(|error| format!("spawn sha256sum: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "sha256sum failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .next()
        .map(str::to_owned)
        .ok_or_else(|| "sha256sum emitted no digest".to_owned())
}

fn try_sha256_text(input: &str) -> Result<String, String> {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|error| format!("spawn sha256sum: {error}"))?;
    child
        .stdin
        .take()
        .ok_or_else(|| "sha256sum stdin unavailable".to_owned())?
        .write_all(input.as_bytes())
        .map_err(|error| format!("write sha256sum input: {error}"))?;
    let output = child
        .wait_with_output()
        .map_err(|error| format!("wait for sha256sum: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "sha256sum text failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .next()
        .map(str::to_owned)
        .ok_or_else(|| "sha256sum text emitted no digest".to_owned())
}

fn collect_digest_files(
    root: &Path,
    current: &Path,
    files: &mut Vec<(String, String)>,
) -> Result<(), String> {
    let mut entries = fs::read_dir(current)
        .map_err(|error| format!("read digest directory {}: {error}", current.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("read digest entry in {}: {error}", current.display()))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let metadata = fs::symlink_metadata(&path)
            .map_err(|error| format!("inspect digest path {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink() {
            continue;
        }
        if metadata.is_dir() {
            if entry.file_name() != "target" {
                collect_digest_files(root, &path, files)?;
            }
        } else if metadata.is_file() {
            let relative = path
                .strip_prefix(root)
                .map_err(|error| format!("relativize {}: {error}", path.display()))?
                .to_str()
                .ok_or_else(|| format!("non-UTF-8 digest path: {}", path.display()))?
                .to_owned();
            files.push((relative, try_sha256(&path)?));
        }
    }
    Ok(())
}

fn tree_digest(root: &Path) -> Result<String, String> {
    let mut files = Vec::new();
    collect_digest_files(root, root, &mut files)?;
    files.sort();
    let mut input = String::new();
    for (relative, digest) in files {
        input.push_str(&relative);
        input.push('\0');
        input.push_str(&digest);
        input.push('\n');
    }
    try_sha256_text(&input)
}

fn derived_substrate_digest(root: &Path) -> Result<String, String> {
    let mut programs = fs::read_dir(root)
        .map_err(|error| format!("read substrate root {}: {error}", root.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("read substrate entry in {}: {error}", root.display()))?;
    programs.sort_by_key(|entry| entry.file_name());
    let mut input = String::new();
    for program in programs {
        let path = program.path();
        let metadata = fs::symlink_metadata(&path)
            .map_err(|error| format!("inspect substrate path {}: {error}", path.display()))?;
        if program.file_name() == "_logs" || metadata.file_type().is_symlink() || !metadata.is_dir()
        {
            continue;
        }
        let name = program
            .file_name()
            .into_string()
            .map_err(|_| format!("non-UTF-8 program path: {}", path.display()))?;
        input.push_str(&name);
        input.push('\0');
        input.push_str(&tree_digest(&path)?);
        input.push('\n');
    }
    try_sha256_text(&input)
}

fn write_manifest(dir: &Path, files: &[&str]) -> Result<String, String> {
    let mut files = files.to_vec();
    files.sort_unstable();
    let mut contents = String::new();
    for file in files {
        let path = dir.join(file);
        if !path.is_file() {
            return Err(format!("manifest input missing: {}", path.display()));
        }
        contents.push_str(&format!("{}  ./{}\n", sha256(&path), file));
    }
    let manifest = dir.join("artifact-manifest.sha256");
    fs::write(&manifest, contents)
        .map_err(|error| format!("write {}: {error}", manifest.display()))?;
    Ok(sha256(&manifest))
}

fn verify_manifest(dir: &Path) -> Result<String, String> {
    let manifest = dir.join("artifact-manifest.sha256");
    let output = Command::new("sha256sum")
        .args(["-c", "artifact-manifest.sha256"])
        .current_dir(dir)
        .output()
        .map_err(|error| format!("verify {}: {error}", manifest.display()))?;
    if !output.status.success() {
        return Err(format!(
            "manifest verification failed in {}: {} {}",
            dir.display(),
            String::from_utf8_lossy(&output.stdout).trim(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(sha256(&manifest))
}

fn parse_table(path: &Path, header: &str, columns: usize) -> Result<Vec<Vec<String>>, String> {
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read table {}: {error}", path.display()))?;
    let mut lines = input.lines();
    if lines.next() != Some(header) {
        return Err(format!("header drift: {}", path.display()));
    }
    lines
        .enumerate()
        .map(|(offset, line)| {
            let row = line.split('\t').map(str::to_owned).collect::<Vec<_>>();
            if row.len() != columns {
                return Err(format!(
                    "{} line {} has {} columns, expected {columns}",
                    path.display(),
                    offset + 2,
                    row.len()
                ));
            }
            Ok(row)
        })
        .collect()
}

const CANDIDATE_HEADER: &str =
    "program\tfield_key\tfield_slot\tordinary_kind\tprimary_class\tcause_flags\troot_count";
const ROOT_HEADER: &str =
    "population\tprogram\tfield_key\tstore_site\troot_id\troot_label\tcause_flags\tordered_path";
const EXCEPTION_HEADER: &str = "program\tfield_key\tfield_slot\tordinary_kind\tforce_result\treplay_result\treplay_kind\tcausal_outcome\tsource_selectors\tsink_selectors\tsource_inventory\tsink_inventory\tordinary_dropped_sources\tordinary_dropped_sinks\tforced_dropped_sources\tforced_dropped_sinks\treplay_dropped_sources\treplay_dropped_sinks\tmodel_changes\tordinary_commits\tforced_commits\tgraph_root_count\tgraph_flags\tallocation_token_path\tunsupported_realloc\tcopy_clone_gate\tabi_gate\tfn_pointer_gate";

fn identity_text(rows: impl Iterator<Item = Identity>) -> String {
    let mut rows = rows.collect::<Vec<_>>();
    rows.sort();
    rows.into_iter()
        .map(|row| format!("{}\t{}\n", row.program, row.field_key))
        .collect()
}

fn parse_receipt(path: &Path) -> Result<BTreeMap<String, String>, String> {
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read receipt {}: {error}", path.display()))?;
    let mut receipt = BTreeMap::new();
    for (offset, line) in input.lines().enumerate() {
        let (key, value) = line.split_once('=').ok_or_else(|| {
            format!(
                "receipt {} line {} is not key=value",
                path.display(),
                offset + 1
            )
        })?;
        if receipt.insert(key.to_owned(), value.to_owned()).is_some() {
            return Err(format!("receipt {} duplicates {key}", path.display()));
        }
    }
    Ok(receipt)
}

fn validate_completed_receipt(
    receipt: &BTreeMap<String, String>,
    contract: &MeasurementContract,
    program: &str,
) -> Result<(), String> {
    for (key, expected) in [
        ("status", "ok"),
        ("data", "true"),
        ("checkpoint_data", "false"),
        ("machine_id", MACHINE_ID),
        ("platform", PLATFORM),
        ("memory_limit", "uncapped"),
        ("wall_cap_s", "14400"),
    ] {
        let actual = receipt.get(key).map(String::as_str);
        if actual != Some(expected) {
            return Err(format!(
                "receipt {key}: expected {expected:?}, got {actual:?}"
            ));
        }
    }
    for (key, expected) in [
        ("program", program),
        ("analysis_head", contract.head.as_str()),
        ("a4_aggregate_manifest_sha256", A4_AGGREGATE_MANIFEST_SHA256),
        ("a4_combined_sha256", A4_COMBINED_SHA256),
        ("census_identity_sha256", CENSUS_IDENTITY_SHA256),
        ("exception_identity_sha256", EXCEPTION_IDENTITY_SHA256),
        ("raw_corpus_digest", RAW_CORPUS_DIGEST),
        ("derived_substrate_digest", DERIVED_SUBSTRATE_DIGEST),
        ("snapshot", SNAPSHOT_PATH),
    ] {
        let actual = receipt.get(key).map(String::as_str);
        if actual != Some(expected) {
            return Err(format!(
                "receipt {key}: expected {expected:?}, got {actual:?}"
            ));
        }
    }
    Ok(())
}

fn last_phase(stderr: &str) -> (String, String) {
    let Some(line) = stderr
        .lines()
        .filter(|line| line.starts_with("BOC1PHASE a4-source-census "))
        .next_back()
    else {
        return ("none".to_owned(), "none".to_owned());
    };
    let fields = line
        .split_whitespace()
        .filter_map(|token| token.split_once('='))
        .collect::<BTreeMap<_, _>>();
    (
        fields.get("phase").copied().unwrap_or("none").to_owned(),
        fields
            .get("candidate")
            .copied()
            .unwrap_or("none")
            .to_owned(),
    )
}

struct MeasurementContract {
    run_root: PathBuf,
    input_root: PathBuf,
    input_path: PathBuf,
    input: Vec<A4InputRow>,
    programs: Vec<super::CorpusProgram>,
    head: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SubstratePreflightStatus {
    Ok,
    LinkMissing,
    LinkNotSymlink,
    TargetUnreadable,
    InputUnreadable,
    DigestUnreadable,
    DigestMismatch,
}

impl SubstratePreflightStatus {
    fn as_str(self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::LinkMissing => "substrate-link-missing",
            Self::LinkNotSymlink => "substrate-link-not-symlink",
            Self::TargetUnreadable => "substrate-target-unreadable",
            Self::InputUnreadable => "substrate-input-unreadable",
            Self::DigestUnreadable => "substrate-digest-unreadable",
            Self::DigestMismatch => "substrate-digest-mismatch",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SubstratePreflight {
    status: SubstratePreflightStatus,
    link_path: PathBuf,
    target_path: Option<PathBuf>,
    expected_digest: String,
    actual_digest: Option<String>,
    inputs_verified: usize,
    detail: String,
}

fn preflight_failure(
    status: SubstratePreflightStatus,
    link_path: PathBuf,
    target_path: Option<PathBuf>,
    expected_digest: &str,
    actual_digest: Option<String>,
    inputs_verified: usize,
    detail: String,
) -> SubstratePreflight {
    SubstratePreflight {
        status,
        link_path,
        target_path,
        expected_digest: expected_digest.to_owned(),
        actual_digest,
        inputs_verified,
        detail,
    }
}

fn inspect_substrate(
    workspace: &Path,
    inputs: &[(&str, &str)],
    expected_digest: &str,
) -> SubstratePreflight {
    let link_path = workspace.join("benchmarks/rs-crown-derived");
    let metadata = match fs::symlink_metadata(&link_path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return preflight_failure(
                SubstratePreflightStatus::LinkMissing,
                link_path,
                None,
                expected_digest,
                None,
                0,
                error.to_string(),
            );
        }
        Err(error) => {
            return preflight_failure(
                SubstratePreflightStatus::TargetUnreadable,
                link_path,
                None,
                expected_digest,
                None,
                0,
                error.to_string(),
            );
        }
    };
    if !metadata.file_type().is_symlink() {
        return preflight_failure(
            SubstratePreflightStatus::LinkNotSymlink,
            link_path,
            None,
            expected_digest,
            None,
            0,
            "substrate path exists but is not a symlink".to_owned(),
        );
    }
    let target_path = match fs::canonicalize(&link_path) {
        Ok(target) if target.is_dir() => target,
        Ok(target) => {
            return preflight_failure(
                SubstratePreflightStatus::TargetUnreadable,
                link_path,
                Some(target.clone()),
                expected_digest,
                None,
                0,
                format!("substrate target is not a directory: {}", target.display()),
            );
        }
        Err(error) => {
            return preflight_failure(
                SubstratePreflightStatus::TargetUnreadable,
                link_path,
                None,
                expected_digest,
                None,
                0,
                error.to_string(),
            );
        }
    };
    let mut inputs_verified = 0;
    for &(program, lib_root) in inputs {
        let input = link_path.join(program).join(lib_root);
        let readable = fs::metadata(&input).is_ok_and(|metadata| metadata.is_file())
            && fs::File::open(&input).is_ok();
        if !readable {
            return preflight_failure(
                SubstratePreflightStatus::InputUnreadable,
                link_path,
                Some(target_path),
                expected_digest,
                None,
                inputs_verified,
                format!("input is not a readable file: {}", input.display()),
            );
        }
        inputs_verified += 1;
    }
    let actual_digest = match derived_substrate_digest(&target_path) {
        Ok(digest) => digest,
        Err(error) => {
            return preflight_failure(
                SubstratePreflightStatus::DigestUnreadable,
                link_path,
                Some(target_path),
                expected_digest,
                None,
                inputs_verified,
                error,
            );
        }
    };
    if actual_digest != expected_digest {
        return preflight_failure(
            SubstratePreflightStatus::DigestMismatch,
            link_path,
            Some(target_path),
            expected_digest,
            Some(actual_digest),
            inputs_verified,
            "derived substrate digest does not match the pinned digest".to_owned(),
        );
    }
    SubstratePreflight {
        status: SubstratePreflightStatus::Ok,
        link_path,
        target_path: Some(target_path),
        expected_digest: expected_digest.to_owned(),
        actual_digest: Some(actual_digest),
        inputs_verified,
        detail: "link, inputs, and digest verified".to_owned(),
    }
}

fn receipt_value(value: &str) -> String {
    value.replace(['\n', '\r', '\t'], " ")
}

fn write_substrate_preflight(
    run_root: &Path,
    head: &str,
    result: &SubstratePreflight,
) -> Result<String, String> {
    fs::create_dir_all(run_root)
        .map_err(|error| format!("create run root {}: {error}", run_root.display()))?;
    let dir = run_root.join("preflight");
    fs::create_dir_all(&dir)
        .map_err(|error| format!("create preflight directory {}: {error}", dir.display()))?;
    let target = result
        .target_path
        .as_deref()
        .map(|path| path.display().to_string())
        .unwrap_or_else(|| "none".to_owned());
    let actual = result.actual_digest.as_deref().unwrap_or("none");
    let receipt = format!(
        "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nphase=substrate-preflight\nstatus={}\nmeasurement_started=false\nanalysis_head={head}\nsubstrate_link={}\nsubstrate_target={}\nexpected_digest={}\nactual_digest={}\ninputs_verified={}\ndetail={}\n",
        result.status.as_str(),
        result.link_path.display(),
        target,
        result.expected_digest,
        actual,
        result.inputs_verified,
        receipt_value(&result.detail),
    );
    write_atomic_checkpoint(&dir.join("receipt.txt"), &receipt)
        .map_err(|error| format!("write substrate preflight receipt: {error}"))?;
    let manifest = write_manifest(&dir, &["receipt.txt"])?;
    let verified = verify_manifest(&dir)?;
    if manifest != verified {
        return Err("substrate preflight manifest digest drift".to_owned());
    }
    Ok(manifest)
}

fn enforce_substrate_preflight(contract: &MeasurementContract) {
    use super::orchestrate::workspace_root;

    let inputs = super::CORPUS
        .iter()
        .map(|program| (program.name, program.lib_root))
        .collect::<Vec<_>>();
    let result = inspect_substrate(&workspace_root(), &inputs, DERIVED_SUBSTRATE_DIGEST);
    let manifest = write_substrate_preflight(&contract.run_root, &contract.head, &result)
        .unwrap_or_else(|error| {
            panic!(
                "A4C STOP phase=substrate-preflight candidate=none status=preflight-receipt-error measurement_started=false: {error}"
            )
        });
    assert_eq!(
        result.status,
        SubstratePreflightStatus::Ok,
        "A4C STOP phase=substrate-preflight candidate=none status={} measurement_started=false manifest={manifest} detail={}",
        result.status.as_str(),
        result.detail,
    );
    eprintln!(
        "A4C preflight complete status=ok inputs={} digest={} manifest={manifest}",
        result.inputs_verified,
        result.actual_digest.as_deref().unwrap_or("none"),
    );
}

fn measurement_contract() -> MeasurementContract {
    use super::orchestrate::{git_dirty, git_sha, out_dir, workspace_root};

    assert_eq!(std::env::var("CRAT_BO_REPAIR").as_deref(), Ok("mode_a"));
    assert_eq!(
        std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
        Ok("0")
    );
    assert_eq!(
        std::env::var("CRAT_BOC1_SUBSTRATE").as_deref(),
        Ok("derived")
    );
    assert_eq!(std::env::var("CRAT_BOC1_MEM_MB").as_deref(), Ok("uncapped"));
    assert_eq!(
        command_stdout(Command::new("hostname"), "hostname"),
        MACHINE_ID
    );
    assert_eq!(
        format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH),
        PLATFORM
    );
    assert!(!git_dirty(), "source-census harness tree must be clean");
    let head = git_sha();
    let mut contains = Command::new("git");
    contains
        .args(["branch", "-r", "--contains", &head])
        .current_dir(workspace_root());
    let published = command_stdout(contains, "locate published source-census head");
    assert!(
        published
            .lines()
            .any(|line| line.trim() == "origin/codex/a4-source-census"),
        "source-census head {head} is not published on its task branch"
    );

    let run_root = PathBuf::from(
        std::env::var_os("CRAT_A4_SOURCE_RUN_ROOT").expect("CRAT_A4_SOURCE_RUN_ROOT"),
    );
    assert!(run_root.is_absolute());
    assert!(!run_root.starts_with(workspace_root()));
    assert_eq!(out_dir(), run_root);
    let input_root = PathBuf::from(
        std::env::var_os("CRAT_A4_SOURCE_ACCEPTED_ROOT").expect("CRAT_A4_SOURCE_ACCEPTED_ROOT"),
    );
    let input_manifest = verify_manifest(&input_root)
        .unwrap_or_else(|error| panic!("A4C STOP phase=input-manifest candidate=none: {error}"));
    assert_eq!(input_manifest, A4_AGGREGATE_MANIFEST_SHA256);
    let input_path = input_root.join("combined.tsv");
    assert_eq!(sha256(&input_path), A4_COMBINED_SHA256);
    let input = parse_a4_input(&input_path)
        .unwrap_or_else(|error| panic!("A4C STOP phase=input-schema candidate=none: {error}"));
    let census_identity = identity_text(input.iter().filter_map(|row| {
        (row.proof_reason == "allocation-source-count-0").then(|| Identity {
            program: row.program.clone(),
            field_key: row.field_key.clone(),
        })
    }));
    assert_eq!(census_identity.lines().count(), 237);
    assert_eq!(sha256_text(&census_identity), CENSUS_IDENTITY_SHA256);
    let exception_identity = identity_text(input.iter().filter_map(|row| {
        (row.baseline_force == "sat").then(|| Identity {
            program: row.program.clone(),
            field_key: row.field_key.clone(),
        })
    }));
    assert_eq!(exception_identity.lines().count(), 4);
    assert_eq!(sha256_text(&exception_identity), EXCEPTION_IDENTITY_SHA256);
    let mut program_names = input
        .iter()
        .filter(|row| {
            row.proof_reason == "allocation-source-count-0" || row.baseline_force == "sat"
        })
        .map(|row| row.program.as_str())
        .collect::<BTreeSet<_>>();
    program_names.insert("heman");
    let programs = super::CORPUS
        .iter()
        .copied()
        .filter(|program| program_names.contains(program.name))
        .collect::<Vec<_>>();
    assert_eq!(programs.len(), 18);
    assert_eq!(
        programs
            .iter()
            .map(|program| program.name)
            .collect::<BTreeSet<_>>(),
        program_names
    );
    assert!(Path::new(SNAPSHOT_PATH).is_dir());
    assert!(
        workspace_root()
            .join("deps_crate/target/debug/deps")
            .is_dir()
    );
    MeasurementContract {
        run_root,
        input_root,
        input_path,
        input,
        programs,
        head,
    }
}

fn expected_identities(
    contract: &MeasurementContract,
    program: &str,
    census: bool,
) -> Vec<Identity> {
    contract
        .input
        .iter()
        .filter(|row| row.program == program)
        .filter(|row| {
            if census {
                row.proof_reason == "allocation-source-count-0"
            } else {
                row.baseline_force == "sat"
            }
        })
        .map(|row| Identity {
            program: row.program.clone(),
            field_key: row.field_key.clone(),
        })
        .collect()
}

fn validate_shard(contract: &MeasurementContract, program: &str, dir: &Path) -> Result<(), String> {
    let candidates = parse_table(&dir.join("candidates.tsv"), CANDIDATE_HEADER, 7)?;
    let roots = parse_table(&dir.join("roots.tsv"), ROOT_HEADER, 8)?;
    let exceptions = parse_table(&dir.join("exceptions.tsv"), EXCEPTION_HEADER, 28)?;
    let candidate_ids = candidates
        .iter()
        .map(|row| Identity {
            program: row[0].clone(),
            field_key: row[1].clone(),
        })
        .collect::<Vec<_>>();
    validate_exact_identities(
        &expected_identities(contract, program, true),
        &candidate_ids,
    )?;
    let exception_ids = exceptions
        .iter()
        .map(|row| Identity {
            program: row[0].clone(),
            field_key: row[1].clone(),
        })
        .collect::<Vec<_>>();
    validate_exact_identities(
        &expected_identities(contract, program, false),
        &exception_ids,
    )?;
    let candidate_id_set = candidate_ids.iter().cloned().collect::<BTreeSet<_>>();
    let exception_id_set = exception_ids.iter().cloned().collect::<BTreeSet<_>>();
    let mut seen_roots = BTreeSet::new();
    let mut root_counts = BTreeMap::<(String, String), usize>::new();
    let mut root_evidence = BTreeMap::<(String, String), Vec<RootEvidence>>::new();
    for row in &roots {
        let identity = Identity {
            program: row[1].clone(),
            field_key: row[2].clone(),
        };
        let expected = match row[0].as_str() {
            "census" => &candidate_id_set,
            "exception" => &exception_id_set,
            other => return Err(format!("unknown root population {other:?}")),
        };
        if !expected.contains(&identity) {
            return Err(format!(
                "root outside {0} identity: {1} {2}",
                row[0], identity.program, identity.field_key
            ));
        }
        if row[3].is_empty() || row[7].is_empty() {
            return Err(format!("root lacks store/path at {}: {}", row[2], row[4]));
        }
        if row[6].is_empty() {
            return Err(format!("root lacks cause flag at {}: {}", row[2], row[4]));
        }
        let flags = row[6]
            .split('|')
            .map(parse_cause_flag)
            .collect::<Result<BTreeSet<_>, _>>()?;
        if !seen_roots.insert((
            row[0].clone(),
            identity.program.clone(),
            identity.field_key.clone(),
            row[3].clone(),
            row[4].clone(),
        )) {
            return Err(format!("duplicate root identity at {} {}", row[2], row[4]));
        }
        *root_counts
            .entry((identity.program.clone(), identity.field_key.clone()))
            .or_default() += 1;
        root_evidence
            .entry((identity.program, identity.field_key))
            .or_default()
            .push(RootEvidence { flags });
    }
    for row in &candidates {
        if !matches!(row[4].as_str(), "invisible" | "absent" | "mixed") {
            return Err(format!("invalid primary class at {}: {}", row[1], row[4]));
        }
        if row[5].is_empty() || row[6].parse::<usize>().unwrap_or(0) == 0 {
            return Err(format!("candidate lacks classified roots: {}", row[1]));
        }
        let reported = row[6]
            .parse::<usize>()
            .map_err(|error| format!("candidate root count {}: {error}", row[1]))?;
        if root_counts.get(&(row[0].clone(), row[1].clone())) != Some(&reported) {
            return Err(format!("candidate root inventory drift: {}", row[1]));
        }
        let evidence = &root_evidence[&(row[0].clone(), row[1].clone())];
        if class_label(classify_roots(evidence)) != row[4] {
            return Err(format!("candidate primary class drift: {}", row[1]));
        }
        let flags = evidence
            .iter()
            .flat_map(|root| root.flags.iter().copied())
            .collect::<BTreeSet<_>>()
            .iter()
            .copied()
            .map(flag_label)
            .collect::<Vec<_>>()
            .join("|");
        if flags != row[5] {
            return Err(format!("candidate cause-flag drift: {}", row[1]));
        }
    }
    for row in &exceptions {
        if row[4] != "sat" {
            return Err(format!("exception force drift: {}", row[1]));
        }
        if !matches!(row[5].as_str(), "accepted" | "declined") {
            return Err(format!("exception replay schema drift: {}", row[1]));
        }
        let expected_cause = if row[5] == "accepted" {
            "objective-choice"
        } else {
            "borrow-replay-decline"
        };
        if row[7] != expected_cause {
            return Err(format!("exception causal-outcome drift: {}", row[1]));
        }
        for (count_index, inventory_index, label) in
            [(8usize, 10usize, "source"), (9usize, 11usize, "sink")]
        {
            let count = row[count_index]
                .parse::<usize>()
                .map_err(|error| format!("exception {label} count {}: {error}", row[1]))?;
            if (count == 0) != row[inventory_index].is_empty() {
                return Err(format!("exception {label} inventory drift: {}", row[1]));
            }
        }
        let reported = row[21]
            .parse::<usize>()
            .map_err(|error| format!("exception root count {}: {error}", row[1]))?;
        if reported == 0 || root_counts.get(&(row[0].clone(), row[1].clone())) != Some(&reported) {
            return Err(format!("exception root inventory drift: {}", row[1]));
        }
        let input = contract
            .input
            .iter()
            .find(|input| input.program == row[0] && input.field_key == row[1])
            .ok_or_else(|| format!("exception input identity missing: {}", row[1]))?;
        if kind_label(input.baseline_kind) != row[3] {
            return Err(format!("exception ordinary-kind drift: {}", row[1]));
        }
        let evidence = &root_evidence[&(row[0].clone(), row[1].clone())];
        let flags = evidence
            .iter()
            .flat_map(|root| root.flags.iter().copied())
            .collect::<BTreeSet<_>>();
        let rendered_flags = flags
            .iter()
            .copied()
            .map(flag_label)
            .collect::<Vec<_>>()
            .join("|");
        if rendered_flags != row[22] {
            return Err(format!("exception graph-flag drift: {}", row[1]));
        }
        let has_allocation = flags.iter().any(|flag| {
            matches!(
                flag,
                CauseFlag::InterproceduralAllocation
                    | CauseFlag::FieldMediatedAllocation
                    | CauseFlag::ReallocAllocation
                    | CauseFlag::SameFunctionScannerGap
            )
        });
        if row[23] != has_allocation.to_string()
            || row[24] != flags.contains(&CauseFlag::ReallocAllocation).to_string()
        {
            return Err(format!("exception admission evidence drift: {}", row[1]));
        }
    }
    Ok(())
}

fn validate_receipt_counts(receipt: &BTreeMap<String, String>, dir: &Path) -> Result<(), String> {
    let actual = [
        (
            "candidates",
            parse_table(&dir.join("candidates.tsv"), CANDIDATE_HEADER, 7)?.len(),
        ),
        (
            "roots",
            parse_table(&dir.join("roots.tsv"), ROOT_HEADER, 8)?.len(),
        ),
        (
            "exceptions",
            parse_table(&dir.join("exceptions.tsv"), EXCEPTION_HEADER, 28)?.len(),
        ),
    ];
    for (key, count) in actual {
        let expected = count.to_string();
        if receipt.get(key).map(String::as_str) != Some(expected.as_str()) {
            return Err(format!("receipt {key} count drift: expected {count}"));
        }
    }
    Ok(())
}

fn failed_receipt(
    contract: &MeasurementContract,
    dir: &Path,
    program: &str,
    status: &str,
    phase: &str,
    candidate: &str,
    wall_s: f64,
    peak_rss_kb: u64,
) -> String {
    let receipt = format!(
        "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nmemory_limit=uncapped\nwall_bound_kind=liveness\nwall_cap_s={LIVENESS_BOUND_S}\nprogram={program}\nstatus={status}\ndata=false\ncheckpoint_data=false\nanalysis_head={}\nlast_phase={phase}\nlast_candidate={candidate}\nwall_s={wall_s:.3}\npeak_rss_kb={peak_rss_kb}\n",
        contract.head
    );
    fs::write(dir.join("receipt.txt"), receipt).expect("write failed receipt");
    let mut files = vec!["receipt.txt"];
    for file in [
        "candidates.tsv",
        "roots.tsv",
        "exceptions.tsv",
        "partial.tsv",
        "partial.tsv.tmp",
        "worker.out",
        "worker.err",
    ] {
        if dir.join(file).is_file() {
            files.push(file);
        }
    }
    write_manifest(dir, &files).expect("manifest failed shard")
}

fn run_shard(contract: &MeasurementContract, program: super::CorpusProgram) {
    use super::orchestrate::{run_child_env, workspace_root};

    let dir = contract.run_root.join("shards").join(program.name);
    if dir.is_dir() {
        let manifest = verify_manifest(&dir).unwrap_or_else(|error| {
            panic!(
                "A4C STOP phase=verified-skip candidate={}: {error}",
                program.name
            )
        });
        let receipt = parse_receipt(&dir.join("receipt.txt")).expect("parse skipped receipt");
        validate_completed_receipt(&receipt, contract, program.name).unwrap_or_else(|error| {
            panic!(
                "A4C STOP phase=verified-skip candidate={}: {error}",
                program.name
            )
        });
        validate_shard(contract, program.name, &dir).unwrap_or_else(|error| {
            panic!(
                "A4C STOP phase=verified-skip candidate={}: {error}",
                program.name
            )
        });
        validate_receipt_counts(&receipt, &dir).unwrap_or_else(|error| {
            panic!(
                "A4C STOP phase=verified-skip candidate={}: {error}",
                program.name
            )
        });
        eprintln!(
            "A4C verified-skip program={} manifest={manifest}",
            program.name
        );
        return;
    }
    fs::create_dir_all(dir.parent().expect("shard parent")).expect("create shard parent");
    fs::create_dir(&dir).expect("create fresh shard");
    let input = workspace_root()
        .join("benchmarks/rs-crown-derived")
        .join(program.name)
        .join(program.lib_root);
    let outcome = run_child_env(
        program.name,
        &input,
        "a4-source-census",
        Duration::from_secs(LIVENESS_BOUND_S),
        &[
            (
                "CRAT_A4_SOURCE_INPUT",
                contract.input_path.display().to_string(),
            ),
            (
                "CRAT_A4_SOURCE_CANDIDATES",
                dir.join("candidates.tsv").display().to_string(),
            ),
            (
                "CRAT_A4_SOURCE_ROOTS",
                dir.join("roots.tsv").display().to_string(),
            ),
            (
                "CRAT_A4_SOURCE_EXCEPTIONS",
                dir.join("exceptions.tsv").display().to_string(),
            ),
            (
                "CRAT_A4_SOURCE_CHECKPOINT",
                dir.join("partial.tsv").display().to_string(),
            ),
        ],
    );
    fs::write(dir.join("worker.out"), &outcome.stdout).expect("preserve worker stdout");
    fs::write(dir.join("worker.err"), &outcome.stderr).expect("preserve worker stderr");
    let (phase, candidate) = last_phase(&outcome.stderr);
    if outcome.status != "ok" {
        let manifest = failed_receipt(
            contract,
            &dir,
            program.name,
            &outcome.status,
            &phase,
            &candidate,
            outcome.wall_s,
            outcome.peak_rss_kb,
        );
        panic!(
            "A4C STOP phase={phase} candidate={candidate} program={} status={} wall_s={:.3} peak_rss_kb={} manifest={manifest}",
            program.name, outcome.status, outcome.wall_s, outcome.peak_rss_kb
        );
    }
    validate_shard(contract, program.name, &dir).unwrap_or_else(|error| {
        failed_receipt(
            contract,
            &dir,
            program.name,
            "schema-or-identity",
            "result-validation",
            program.name,
            outcome.wall_s,
            outcome.peak_rss_kb,
        );
        panic!(
            "A4C STOP phase=result-validation candidate={}: {error}",
            program.name
        )
    });
    let candidates = parse_table(&dir.join("candidates.tsv"), CANDIDATE_HEADER, 7)
        .expect("parse completed candidates");
    let roots = parse_table(&dir.join("roots.tsv"), ROOT_HEADER, 8).expect("parse completed roots");
    let exceptions = parse_table(&dir.join("exceptions.tsv"), EXCEPTION_HEADER, 28)
        .expect("parse completed exceptions");
    let receipt = format!(
        "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nmemory_limit=uncapped\nwall_bound_kind=liveness\nwall_cap_s={LIVENESS_BOUND_S}\nprogram={}\nstatus=ok\ndata=true\ncheckpoint_data=false\nanalysis_head={}\na4_aggregate_manifest_sha256={A4_AGGREGATE_MANIFEST_SHA256}\na4_combined_sha256={A4_COMBINED_SHA256}\ncensus_identity_sha256={CENSUS_IDENTITY_SHA256}\nexception_identity_sha256={EXCEPTION_IDENTITY_SHA256}\nraw_corpus_digest={RAW_CORPUS_DIGEST}\nderived_substrate_digest={DERIVED_SUBSTRATE_DIGEST}\nsnapshot={SNAPSHOT_PATH}\ncandidates={}\nroots={}\nexceptions={}\nlast_phase={phase}\nlast_candidate={candidate}\nwall_s={:.3}\npeak_rss_kb={}\n",
        program.name,
        contract.head,
        candidates.len(),
        roots.len(),
        exceptions.len(),
        outcome.wall_s,
        outcome.peak_rss_kb,
    );
    fs::write(dir.join("receipt.txt"), receipt).expect("write completed receipt");
    let manifest = write_manifest(
        &dir,
        &[
            "candidates.tsv",
            "roots.tsv",
            "exceptions.tsv",
            "partial.tsv",
            "receipt.txt",
            "worker.out",
            "worker.err",
        ],
    )
    .expect("manifest completed shard");
    let verified = verify_manifest(&dir).expect("verify newly completed shard manifest");
    assert_eq!(verified, manifest, "completed shard manifest digest drift");
    let receipt = parse_receipt(&dir.join("receipt.txt")).expect("reparse completed receipt");
    validate_completed_receipt(&receipt, contract, program.name)
        .expect("validate newly completed receipt");
    validate_receipt_counts(&receipt, &dir).expect("validate newly completed receipt counts");
    eprintln!(
        "A4C completed program={} candidates={} roots={} exceptions={} wall_s={:.3} peak_rss_kb={} manifest={manifest}",
        program.name,
        candidates.len(),
        roots.len(),
        exceptions.len(),
        outcome.wall_s,
        outcome.peak_rss_kb
    );
}

fn append_table(combined: &mut String, input: &str, expected_header: &str) {
    let mut lines = input.lines();
    assert_eq!(lines.next(), Some(expected_header));
    if combined.is_empty() {
        combined.push_str(expected_header);
        combined.push('\n');
    }
    for line in lines {
        combined.push_str(line);
        combined.push('\n');
    }
}

fn aggregate(contract: &MeasurementContract) {
    let aggregate_dir = contract.run_root.join("aggregate");
    assert!(!aggregate_dir.exists(), "completed aggregate is immutable");
    fs::create_dir(&aggregate_dir).expect("create aggregate directory");
    let mut combined_candidates = String::new();
    let mut combined_roots = String::new();
    let mut combined_exceptions = String::new();
    let mut receipts = Vec::new();
    let mut shard_manifests = Vec::new();
    for program in &contract.programs {
        let dir = contract.run_root.join("shards").join(program.name);
        let manifest = verify_manifest(&dir).expect("verify completed shard");
        shard_manifests.push((program.name, manifest));
        let receipt = parse_receipt(&dir.join("receipt.txt")).expect("parse completed receipt");
        validate_completed_receipt(&receipt, contract, program.name)
            .expect("aggregate only completed data=true shards");
        validate_receipt_counts(&receipt, &dir).expect("aggregate receipt counts");
        receipts.push(receipt);
        append_table(
            &mut combined_candidates,
            &fs::read_to_string(dir.join("candidates.tsv")).expect("read candidate shard"),
            CANDIDATE_HEADER,
        );
        append_table(
            &mut combined_roots,
            &fs::read_to_string(dir.join("roots.tsv")).expect("read root shard"),
            ROOT_HEADER,
        );
        append_table(
            &mut combined_exceptions,
            &fs::read_to_string(dir.join("exceptions.tsv")).expect("read exception shard"),
            EXCEPTION_HEADER,
        );
    }
    let candidates_path = aggregate_dir.join("candidates.tsv");
    let roots_path = aggregate_dir.join("roots.tsv");
    let exceptions_path = aggregate_dir.join("exceptions.tsv");
    fs::write(&candidates_path, combined_candidates).expect("write aggregate candidates");
    fs::write(&roots_path, combined_roots).expect("write aggregate roots");
    fs::write(&exceptions_path, combined_exceptions).expect("write aggregate exceptions");
    let candidates =
        parse_table(&candidates_path, CANDIDATE_HEADER, 7).expect("parse aggregate candidates");
    let roots = parse_table(&roots_path, ROOT_HEADER, 8).expect("parse aggregate roots");
    let exceptions =
        parse_table(&exceptions_path, EXCEPTION_HEADER, 28).expect("parse aggregate exceptions");
    assert_eq!(candidates.len(), 237);
    assert_eq!(exceptions.len(), 4);
    let candidate_ids = candidates
        .iter()
        .map(|row| Identity {
            program: row[0].clone(),
            field_key: row[1].clone(),
        })
        .collect::<Vec<_>>();
    let expected_candidates = contract
        .programs
        .iter()
        .flat_map(|program| expected_identities(contract, program.name, true))
        .collect::<Vec<_>>();
    validate_exact_identities(&expected_candidates, &candidate_ids)
        .expect("aggregate exact 237 identity");
    let exception_ids = exceptions
        .iter()
        .map(|row| Identity {
            program: row[0].clone(),
            field_key: row[1].clone(),
        })
        .collect::<Vec<_>>();
    let expected_exceptions = contract
        .programs
        .iter()
        .flat_map(|program| expected_identities(contract, program.name, false))
        .collect::<Vec<_>>();
    validate_exact_identities(&expected_exceptions, &exception_ids)
        .expect("aggregate exact four-exception identity");

    let mut class_counts = BTreeMap::<String, usize>::new();
    let mut flag_counts = BTreeMap::<String, usize>::new();
    let mut class_witness = BTreeMap::<String, String>::new();
    let mut flag_witness = BTreeMap::<String, String>::new();
    for row in &candidates {
        *class_counts.entry(row[4].clone()).or_default() += 1;
        class_witness
            .entry(row[4].clone())
            .or_insert_with(|| format!("{}::{}", row[0], row[1]));
        for flag in row[5].split('|') {
            *flag_counts.entry(flag.to_owned()).or_default() += 1;
        }
    }
    for row in &roots {
        for flag in row[6].split('|') {
            flag_witness.entry(flag.to_owned()).or_insert_with(|| {
                format!(
                    "{}::{} store={} root={} path={}",
                    row[1], row[2], row[3], row[4], row[7]
                )
            });
        }
    }
    assert_eq!(class_counts.values().sum::<usize>(), 237);
    for flag in flag_counts.keys() {
        assert!(flag_witness.contains_key(flag));
    }
    let total_wall = receipts
        .iter()
        .map(|receipt| receipt["wall_s"].parse::<f64>().expect("wall float"))
        .sum::<f64>();
    let peak_rss = receipts
        .iter()
        .map(|receipt| receipt["peak_rss_kb"].parse::<u64>().expect("RSS integer"))
        .max()
        .unwrap_or(0);
    let mut per_program = String::from(
        "program\tcandidates\troots\texceptions\tinvisible\tabsent\tmixed\twall_s\tpeak_rss_kb\n",
    );
    for (program, receipt) in contract.programs.iter().zip(&receipts) {
        let program_rows = candidates
            .iter()
            .filter(|row| row[0] == program.name)
            .collect::<Vec<_>>();
        let count_class = |class: &str| program_rows.iter().filter(|row| row[4] == class).count();
        per_program.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            program.name,
            program_rows.len(),
            roots.iter().filter(|row| row[1] == program.name).count(),
            exceptions
                .iter()
                .filter(|row| row[0] == program.name)
                .count(),
            count_class("invisible"),
            count_class("absent"),
            count_class("mixed"),
            receipt["wall_s"],
            receipt["peak_rss_kb"],
        ));
    }
    let class_summary = class_counts
        .iter()
        .map(|(class, count)| {
            format!(
                "- `{class}`: **{count}**, witness `{}`",
                class_witness[class]
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let flag_summary = flag_counts
        .iter()
        .map(|(flag, count)| format!("- `{flag}`: **{count}**, witness `{}`", flag_witness[flag]))
        .collect::<Vec<_>>()
        .join("\n");
    let exception_summary = exceptions
        .iter()
        .map(|row| {
            format!(
                "- `{}::{}`: ordinary `{}`, force `{}`, replay `{}`, model changes `{}`",
                row[0], row[1], row[3], row[4], row[5], row[18]
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let report = format!(
        "# A4 force-SAT exceptions and no-allocation-source census\n\nMachine `{MACHINE_ID}`, platform `{PLATFORM}`; RAM/CPU uncapped with a {LIVENESS_BOUND_S}-second per-program liveness bound. Wall/RSS values are machine-local and never compared across machines.\n\nExact identity: **237/237** preregistered no-allocation-source candidates and **4/4** force-SAT exceptions. No unresolved root entered the aggregate.\n\n## Deterministic primary partition\n\n{class_summary}\n\n## Overlapping cause flags\n\n{flag_summary}\n\n## Force-SAT exceptions\n\n{exception_summary}\n\nSequential shard wall sum: **{total_wall:.3}s**. Maximum observed worker RSS: **{peak_rss} KiB**. Only SHA-manifested, completed `data=true` shards feed this report; atomic `data=false` checkpoints are excluded. Production analysis and rewriter behavior remained untouched.\n"
    );
    let provenance = format!(
        "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nanalysis_head={}\nanalysis_branch=codex/a4-source-census\nbaseline_branch=analysis-lane\nbaseline_head=67bcd3cb67c1ae6f74463050033370b108854411\na4_input_root={}\na4_aggregate_manifest_sha256={A4_AGGREGATE_MANIFEST_SHA256}\na4_combined_sha256={A4_COMBINED_SHA256}\ncensus_identity_sha256={CENSUS_IDENTITY_SHA256}\nexception_identity_sha256={EXCEPTION_IDENTITY_SHA256}\nraw_corpus_digest={RAW_CORPUS_DIGEST}\nderived_substrate_digest={DERIVED_SUBSTRATE_DIGEST}\nsnapshot={SNAPSHOT_PATH}\nmemory_limit=uncapped\nwall_bound_kind=liveness\nwall_cap_s={LIVENESS_BOUND_S}\nprograms={}\ncandidates=237\nexceptions=4\nroots={}\nwall_sum_s={total_wall:.3}\npeak_rss_kb={peak_rss}\nshard_manifests={}\naggregation_input_policy=manifested-published-completed-data-true-only\ntiming_comparison=forbidden-across-machines\n",
        contract.head,
        contract.input_root.display(),
        contract.programs.len(),
        roots.len(),
        shard_manifests
            .iter()
            .map(|(program, digest)| format!("{program}:{digest}"))
            .collect::<Vec<_>>()
            .join(","),
    );
    fs::write(aggregate_dir.join("per-program.tsv"), per_program).expect("write per-program table");
    fs::write(aggregate_dir.join("report.md"), report).expect("write report");
    fs::write(aggregate_dir.join("provenance.txt"), provenance).expect("write provenance");
    let manifest = write_manifest(
        &aggregate_dir,
        &[
            "candidates.tsv",
            "roots.tsv",
            "exceptions.tsv",
            "per-program.tsv",
            "report.md",
            "provenance.txt",
        ],
    )
    .expect("manifest aggregate");
    eprintln!(
        "A4C aggregate complete manifest={manifest} candidates=237 exceptions=4 roots={} classes={class_counts:?} flags={flag_counts:?}",
        roots.len()
    );
}

#[test]
#[ignore = "A4 source census; run sequentially on the dedicated Linux lane"]
fn a4_source_census() {
    let contract = measurement_contract();
    enforce_substrate_preflight(&contract);
    for &program in &contract.programs {
        run_shard(&contract, program);
    }
    aggregate(&contract);
}

#[cfg(test)]
mod tests {
    use std::{fs, process};

    use super::*;

    fn singleton(flag: CauseFlag) -> RootEvidence {
        RootEvidence {
            flags: BTreeSet::from([flag]),
        }
    }

    #[test]
    fn every_preregistered_path_sets_its_exact_flag() {
        let cases = [
            (
                SyntheticPath {
                    terminal: TerminalKind::RecognizedAllocation,
                    crosses_call: true,
                    crosses_field: false,
                    realloc: false,
                    same_function_scanner_gap: false,
                },
                CauseFlag::InterproceduralAllocation,
            ),
            (
                SyntheticPath {
                    terminal: TerminalKind::RecognizedAllocation,
                    crosses_call: false,
                    crosses_field: true,
                    realloc: false,
                    same_function_scanner_gap: false,
                },
                CauseFlag::FieldMediatedAllocation,
            ),
            (
                SyntheticPath {
                    terminal: TerminalKind::RecognizedAllocation,
                    crosses_call: false,
                    crosses_field: false,
                    realloc: true,
                    same_function_scanner_gap: false,
                },
                CauseFlag::ReallocAllocation,
            ),
            (
                SyntheticPath {
                    terminal: TerminalKind::RecognizedAllocation,
                    crosses_call: false,
                    crosses_field: false,
                    realloc: false,
                    same_function_scanner_gap: true,
                },
                CauseFlag::SameFunctionScannerGap,
            ),
            (
                SyntheticPath {
                    terminal: TerminalKind::StaticOrInterior,
                    crosses_call: false,
                    crosses_field: false,
                    realloc: false,
                    same_function_scanner_gap: false,
                },
                CauseFlag::StaticOrInteriorRoot,
            ),
            (
                SyntheticPath {
                    terminal: TerminalKind::ExternalParameter,
                    crosses_call: false,
                    crosses_field: false,
                    realloc: false,
                    same_function_scanner_gap: false,
                },
                CauseFlag::ExternallySuppliedParameter,
            ),
            (
                SyntheticPath {
                    terminal: TerminalKind::OpaqueExternalCall,
                    crosses_call: false,
                    crosses_field: false,
                    realloc: false,
                    same_function_scanner_gap: false,
                },
                CauseFlag::OpaqueExternalCallResult,
            ),
            (
                SyntheticPath {
                    terminal: TerminalKind::StackOrLocalAddress,
                    crosses_call: false,
                    crosses_field: false,
                    realloc: false,
                    same_function_scanner_gap: false,
                },
                CauseFlag::StackOrLocalAddress,
            ),
        ];

        for (path, expected) in cases {
            assert_eq!(flags_for_path(path), BTreeSet::from([expected]));
        }
    }

    #[test]
    fn four_way_partition_is_computed_from_root_flags() {
        assert_eq!(
            classify_roots(&[singleton(CauseFlag::InterproceduralAllocation)]),
            PrimaryClass::Invisible
        );
        assert_eq!(
            classify_roots(&[singleton(CauseFlag::ExternallySuppliedParameter)]),
            PrimaryClass::Absent
        );
        assert_eq!(
            classify_roots(&[
                singleton(CauseFlag::FieldMediatedAllocation),
                singleton(CauseFlag::StaticOrInteriorRoot),
            ]),
            PrimaryClass::Mixed
        );
        assert_eq!(classify_roots(&[]), PrimaryClass::Unresolved);
        assert_eq!(
            classify_roots(&[RootEvidence {
                flags: BTreeSet::new(),
            }]),
            PrimaryClass::Unresolved
        );
    }

    #[test]
    fn identity_gate_has_two_sided_witness() {
        let expected = vec![
            Identity {
                program: "brotli".to_owned(),
                field_key: "H35::field4@d0".to_owned(),
            },
            Identity {
                program: "lil".to_owned(),
                field_key: "_lil_t::field20@d0".to_owned(),
            },
        ];
        assert!(validate_exact_identities(&expected, &expected[..1]).is_err());
        assert!(
            validate_exact_identities(&expected, &[expected[0].clone(), expected[0].clone()])
                .is_err()
        );
        assert!(validate_exact_identities(&expected, &expected).is_ok());
    }

    #[test]
    fn completed_data_gate_has_two_sided_witness() {
        assert!(
            validate_completed_shard(ShardGate {
                data: false,
                completed: false,
                manifested: true,
            })
            .is_err()
        );
        assert!(
            validate_completed_shard(ShardGate {
                data: true,
                completed: true,
                manifested: true,
            })
            .is_ok()
        );
    }

    #[test]
    fn strict_flag_parser_accepts_only_registered_schema() {
        assert_eq!(
            parse_cause_flag("interprocedural-allocation"),
            Ok(CauseFlag::InterproceduralAllocation)
        );
        assert!(parse_cause_flag("analyst-judgment").is_err());
    }

    #[test]
    fn malformed_path_unknown_and_table_schema_are_rejected() {
        assert!(
            validate_trace_shape(&[RootTrace {
                store_site: "store".to_owned(),
                root_id: "root".to_owned(),
                root_label: "root".to_owned(),
                evidence: singleton(CauseFlag::StackOrLocalAddress),
                path: Vec::new(),
            }])
            .is_err()
        );
        assert!(replay_none_disposition(Some("fixture-unknown".to_owned())).is_err());
        assert_eq!(replay_none_disposition(None), Ok("declined"));

        let path = std::env::temp_dir().join(format!(
            "crat-a4-source-census-schema-{}.tsv",
            process::id()
        ));
        fs::write(&path, "wrong\theader\n").unwrap();
        assert!(parse_table(&path, CANDIDATE_HEADER, 7).is_err());
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn exact_four_exception_inventory_is_pinned() {
        assert_eq!(
            exception_specs(),
            vec![
                ExceptionSpec {
                    program: "brotli",
                    field_key: "src::enc::backward_references::H35::field4@d0",
                    ordinary_kind: "raw",
                },
                ExceptionSpec {
                    program: "brotli",
                    field_key: "src::enc::backward_references::H55::field4@d0",
                    ordinary_kind: "raw",
                },
                ExceptionSpec {
                    program: "brotli",
                    field_key: "src::enc::backward_references::H65::field4@d0",
                    ordinary_kind: "raw",
                },
                ExceptionSpec {
                    program: "lil",
                    field_key: "src::lil::_lil_t::field20@d0",
                    ordinary_kind: "ref",
                },
            ]
        );
    }

    #[test]
    fn phase_marker_and_atomic_checkpoint_fire() {
        let phase = phase_line("source-traversal", Some("field@d0"), 7);
        assert!(phase.contains("phase=source-traversal"));
        assert!(phase.contains("candidate=field@d0"));
        assert!(phase.contains("completed=7"));

        let path = std::env::temp_dir().join(format!(
            "crat-a4-source-census-checkpoint-{}.tsv",
            process::id()
        ));
        write_atomic_checkpoint(&path, "data=false\nrow\n").unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), "data=false\nrow\n");
        assert!(!path.with_extension("tsv.tmp").exists());
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn graph_walk_derives_invisible_flags_from_path_edges() {
        let mut graph = SourceGraph::default();
        graph.add_terminal(TerminalRoot {
            id: "alloc-0".to_owned(),
            node: "alloc-result".to_owned(),
            kind: TerminalKind::RecognizedAllocation,
            label: "malloc@bb0".to_owned(),
            realloc: false,
        });
        graph.add_edge(FlowEdge {
            source: "alloc-result".to_owned(),
            target: "callee-return".to_owned(),
            kind: FlowEdgeKind::Call,
            label: "return-edge".to_owned(),
        });
        graph.add_edge(FlowEdge {
            source: "callee-return".to_owned(),
            target: "other-field".to_owned(),
            kind: FlowEdgeKind::Field,
            label: "store-other-field".to_owned(),
        });
        graph.add_edge(FlowEdge {
            source: "other-field".to_owned(),
            target: "candidate".to_owned(),
            kind: FlowEdgeKind::Field,
            label: "store-candidate".to_owned(),
        });

        let roots = trace_candidate(&graph, "candidate");
        assert_eq!(roots.len(), 1);
        assert_eq!(
            roots[0].evidence.flags,
            BTreeSet::from([
                CauseFlag::InterproceduralAllocation,
                CauseFlag::FieldMediatedAllocation,
            ])
        );
        assert_eq!(
            classify_roots(
                &roots
                    .iter()
                    .map(|root| root.evidence.clone())
                    .collect::<Vec<_>>()
            ),
            PrimaryClass::Invisible
        );
    }

    #[test]
    fn graph_walk_makes_mixed_a_computation_and_dead_ends_unresolved() {
        let mut graph = SourceGraph::default();
        graph.add_terminal(TerminalRoot {
            id: "alloc-0".to_owned(),
            node: "alloc-result".to_owned(),
            kind: TerminalKind::RecognizedAllocation,
            label: "malloc@bb0".to_owned(),
            realloc: true,
        });
        graph.add_terminal(TerminalRoot {
            id: "param-0".to_owned(),
            node: "external-param".to_owned(),
            kind: TerminalKind::ExternalParameter,
            label: "public::arg1".to_owned(),
            realloc: false,
        });
        for source in ["alloc-result", "external-param", "dead-end"] {
            graph.add_edge(FlowEdge {
                source: source.to_owned(),
                target: "candidate".to_owned(),
                kind: FlowEdgeKind::Local,
                label: format!("{source}->candidate"),
            });
        }

        let roots = trace_candidate(&graph, "candidate");
        assert_eq!(roots.len(), 3);
        assert_eq!(
            classify_roots(
                &roots
                    .iter()
                    .map(|root| root.evidence.clone())
                    .collect::<Vec<_>>()
            ),
            PrimaryClass::Unresolved,
            "the unclassified dead-end has precedence over the otherwise mixed roots"
        );

        graph.incoming.get_mut("candidate").unwrap().pop();
        let roots = trace_candidate(&graph, "candidate");
        assert_eq!(
            classify_roots(
                &roots
                    .iter()
                    .map(|root| root.evidence.clone())
                    .collect::<Vec<_>>()
            ),
            PrimaryClass::Mixed
        );
    }

    #[test]
    fn graph_walk_retains_terminal_attached_directly_to_candidate() {
        let mut graph = SourceGraph::default();
        graph.add_terminal(TerminalRoot {
            id: "direct-stack".to_owned(),
            node: "candidate".to_owned(),
            kind: TerminalKind::StackOrLocalAddress,
            label: "address-of-local".to_owned(),
            realloc: false,
        });
        graph.add_edge(FlowEdge {
            source: "external-param".to_owned(),
            target: "candidate".to_owned(),
            kind: FlowEdgeKind::Local,
            label: "param-store".to_owned(),
        });
        graph.add_terminal(TerminalRoot {
            id: "external".to_owned(),
            node: "external-param".to_owned(),
            kind: TerminalKind::ExternalParameter,
            label: "public-arg".to_owned(),
            realloc: false,
        });

        let roots = trace_candidate(&graph, "candidate");
        assert_eq!(roots.len(), 2);
        assert!(roots.iter().any(|root| root.root_id == "direct-stack"));
        assert_eq!(
            classify_roots(
                &roots
                    .iter()
                    .map(|root| root.evidence.clone())
                    .collect::<Vec<_>>()
            ),
            PrimaryClass::Absent
        );
    }

    fn preflight_fixture(label: &str) -> (PathBuf, PathBuf) {
        let root = std::env::temp_dir().join(format!(
            "crat-a4-source-preflight-{label}-{}",
            process::id()
        ));
        if root.exists() {
            fs::remove_dir_all(&root).unwrap();
        }
        let workspace = root.join("worktree");
        let substrate = root.join("substrate");
        fs::create_dir_all(workspace.join("benchmarks")).unwrap();
        fs::create_dir_all(substrate.join("bst")).unwrap();
        fs::write(substrate.join("bst/lib.rs"), "pub fn fixture() {}\n").unwrap();
        (workspace, substrate)
    }

    #[test]
    fn substrate_preflight_missing_link_is_setup_not_shard_data() {
        let (workspace, _substrate) = preflight_fixture("missing-link");
        let run_root = workspace.parent().unwrap().join("run");
        let result = inspect_substrate(&workspace, &[("bst", "lib.rs")], "unused");
        assert_eq!(result.status, SubstratePreflightStatus::LinkMissing);

        let manifest = write_substrate_preflight(&run_root, "fixture-head", &result).unwrap();
        assert_eq!(
            verify_manifest(&run_root.join("preflight")).unwrap(),
            manifest
        );
        let receipt = fs::read_to_string(run_root.join("preflight/receipt.txt")).unwrap();
        assert!(receipt.contains("status=substrate-link-missing\n"));
        assert!(receipt.contains("measurement_started=false\n"));
        assert!(!receipt.contains("data=false"));
        assert!(!run_root.join("shards").exists());

        fs::remove_dir_all(workspace.parent().unwrap()).unwrap();
    }

    #[test]
    fn substrate_preflight_digest_gate_has_two_sided_witness() {
        let (workspace, substrate) = preflight_fixture("digest");
        std::os::unix::fs::symlink(&substrate, workspace.join("benchmarks/rs-crown-derived"))
            .unwrap();

        let actual = derived_substrate_digest(&substrate).unwrap();
        let mismatch = inspect_substrate(&workspace, &[("bst", "lib.rs")], &"0".repeat(64));
        assert_eq!(mismatch.status, SubstratePreflightStatus::DigestMismatch);
        assert_eq!(mismatch.actual_digest.as_deref(), Some(actual.as_str()));

        let valid = inspect_substrate(&workspace, &[("bst", "lib.rs")], &actual);
        assert_eq!(valid.status, SubstratePreflightStatus::Ok);
        assert_eq!(valid.inputs_verified, 1);

        fs::remove_file(substrate.join("bst/lib.rs")).unwrap();
        let unreadable = inspect_substrate(&workspace, &[("bst", "lib.rs")], &actual);
        assert_eq!(unreadable.status, SubstratePreflightStatus::InputUnreadable);

        fs::remove_dir_all(workspace.parent().unwrap()).unwrap();
    }

    #[test]
    #[ignore = "lambda7 real-substrate preflight positive control"]
    fn substrate_preflight_real_link_and_digest_match() {
        let inputs = super::super::CORPUS
            .iter()
            .map(|program| (program.name, program.lib_root))
            .collect::<Vec<_>>();
        let result = inspect_substrate(
            &super::super::orchestrate::workspace_root(),
            &inputs,
            DERIVED_SUBSTRATE_DIGEST,
        );
        assert_eq!(result.status, SubstratePreflightStatus::Ok, "{result:?}");
        assert_eq!(result.inputs_verified, 20);
        assert_eq!(
            result.actual_digest.as_deref(),
            Some(DERIVED_SUBSTRATE_DIGEST)
        );
    }
}
