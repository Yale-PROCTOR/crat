//! Test-only A4 force-SAT exception and allocation-source census.
//!
//! This module is reachable only through the `bo_c1` test harness. Production
//! analysis and rewriter behavior do not depend on it.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    ffi::OsString,
    fs,
    io::{BufRead, BufReader, BufWriter, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use rustc_const_eval::interpret::{GlobalAlloc, Scalar};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        AggregateKind, Body, Const, ConstValue, Local, Location, Operand, Place, PlaceRef,
        ProjectionElem, RETURN_PLACE, Rvalue, StatementKind, Terminator, TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind, UintTy},
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
    NullLiteralRoot,
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
    provenance_tags: BTreeSet<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TerminalKind {
    RecognizedAllocation,
    StaticOrInterior,
    ExternalParameter,
    OpaqueExternalCall,
    StackOrLocalAddress,
    NullLiteral,
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
    provenance_tags: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TerminalRoot {
    id: String,
    node: String,
    kind: TerminalKind,
    label: String,
    realloc: bool,
    provenance_tags: BTreeSet<String>,
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
                (&a.source, &a.target, &a.label, &a.provenance_tags).cmp(&(
                    &b.source,
                    &b.target,
                    &b.label,
                    &b.provenance_tags,
                ))
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
        TerminalKind::NullLiteral => {
            flags.insert(CauseFlag::NullLiteralRoot);
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
                    | CauseFlag::NullLiteralRoot
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
        "null-literal-root" => Ok(CauseFlag::NullLiteralRoot),
        _ => Err(format!("unknown cause flag {value:?}")),
    }
}

fn parse_provenance_tag(value: &str) -> Result<String, String> {
    if matches!(
        value,
        "string-literal-root"
            | "external-parameter-pointee-load"
            | "indirect-external-parameter-callback"
            | "public-setter-reachable"
    ) {
        return Ok(value.to_owned());
    }
    let Some(target) = value
        .strip_prefix("indirect-resolved-target(")
        .and_then(|value| value.strip_suffix(')'))
    else {
        return Err(format!("unknown evidence flag {value:?}"));
    };
    if target.is_empty() || target.contains(['|', '\t', '\n', '\r']) {
        return Err(format!("malformed indirect-target provenance {value:?}"));
    }
    Ok(value.to_owned())
}

fn parse_root_evidence(value: &str) -> Result<RootEvidence, String> {
    let mut flags = BTreeSet::new();
    let mut provenance_tags = BTreeSet::new();
    for token in value.split('|') {
        if matches!(
            token,
            "string-literal-root"
                | "external-parameter-pointee-load"
                | "indirect-external-parameter-callback"
                | "public-setter-reachable"
        ) || token.starts_with("indirect-resolved-target(")
        {
            provenance_tags.insert(parse_provenance_tag(token)?);
        } else {
            flags.insert(parse_cause_flag(token)?);
        }
    }
    Ok(RootEvidence {
        flags,
        provenance_tags,
    })
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
        provenance_tags: BTreeSet<String>,
        path: Vec<String>,
    }

    let mut roots =
        BTreeMap::<(String, String, BTreeSet<CauseFlag>, BTreeSet<String>), RootTrace>::new();
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
            (
                terminal.label.clone(),
                terminal.id.clone(),
                flags.clone(),
                terminal.provenance_tags.clone(),
            ),
            RootTrace {
                store_site: terminal.label.clone(),
                root_id: terminal.id.clone(),
                root_label: terminal.label.clone(),
                evidence: RootEvidence {
                    flags,
                    provenance_tags: terminal.provenance_tags.clone(),
                },
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
            provenance_tags: edge.provenance_tags.clone(),
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
                provenance_tags: BTreeSet::new(),
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
            state.provenance_tags.clone(),
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
            let mut provenance_tags = state.provenance_tags.clone();
            provenance_tags.extend(terminal.provenance_tags.iter().cloned());
            roots
                .entry((
                    state.store_site.clone(),
                    terminal.id.clone(),
                    flags.clone(),
                    provenance_tags.clone(),
                ))
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
                    evidence: RootEvidence {
                        flags,
                        provenance_tags,
                    },
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
                    state.provenance_tags.clone(),
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
                            provenance_tags: state.provenance_tags.clone(),
                        },
                        path,
                    }
                });
        }
        for edge in incoming.into_iter().flatten() {
            let mut path = state.path.clone();
            path.push(edge.label.clone());
            let mut provenance_tags = state.provenance_tags.clone();
            provenance_tags.extend(edge.provenance_tags.iter().cloned());
            work.push_back(Work {
                node: edge.source.clone(),
                store_site: state.store_site.clone(),
                crosses_call: state.crosses_call || edge.kind == FlowEdgeKind::Call,
                crosses_field: state.crosses_field || edge.kind == FlowEdgeKind::Field,
                provenance_tags,
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
    node_for_place_depth(tcx, slots, fn_did, body, place, 0)
}

fn node_for_place_depth<'tcx>(
    tcx: TyCtxt<'tcx>,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    place: Place<'tcx>,
    depth: u8,
) -> Option<String> {
    resolve_place(slots, fn_did, body, place, depth, None)
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

fn pointer_constant_terminal(is_literal_zero: bool) -> TerminalKind {
    if is_literal_zero {
        TerminalKind::NullLiteral
    } else {
        TerminalKind::Unsupported
    }
}

fn is_byte_string_static_constant(tcx: TyCtxt<'_>, operand: &Operand<'_>) -> bool {
    let Some(constant) = operand.constant() else {
        return false;
    };
    let Const::Val(ConstValue::Scalar(Scalar::Ptr(pointer, _)), ty) = constant.const_ else {
        return false;
    };
    let TyKind::Ref(_, pointee, _) = ty.kind() else {
        return false;
    };
    let TyKind::Array(element, _) = pointee.kind() else {
        return false;
    };
    if !matches!(element.kind(), TyKind::Uint(UintTy::U8)) {
        return false;
    }
    matches!(
        tcx.try_get_global_alloc(pointer.provenance.alloc_id()),
        Some(GlobalAlloc::Memory(_) | GlobalAlloc::Static(_))
    )
}

fn constant_root(tcx: TyCtxt<'_>, operand: &Operand<'_>) -> (TerminalKind, BTreeSet<String>) {
    let Some(constant) = operand.constant() else {
        return (TerminalKind::Unsupported, BTreeSet::new());
    };
    let is_literal_zero = constant
        .const_
        .try_to_scalar()
        .and_then(|scalar| scalar.try_to_scalar_int().ok())
        .is_some_and(|value| value.to_bits(value.size()) == 0);
    if is_literal_zero {
        (TerminalKind::NullLiteral, BTreeSet::new())
    } else if is_byte_string_static_constant(tcx, operand) {
        (
            TerminalKind::StaticOrInterior,
            BTreeSet::from(["string-literal-root".to_owned()]),
        )
    } else {
        (TerminalKind::Unsupported, BTreeSet::new())
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
            provenance_tags: BTreeSet::new(),
        });
    }
}

#[allow(clippy::too_many_arguments)]
fn add_nested_exact_type_place_edges<'tcx>(
    graph: &mut SourceGraph,
    tcx: TyCtxt<'tcx>,
    slots: &CrateSlots,
    source_fn: LocalDefId,
    source_body: &Body<'tcx>,
    source_place: Place<'tcx>,
    target_fn: LocalDefId,
    target_body: &Body<'tcx>,
    target_place: Place<'tcx>,
    fixed_kind: Option<FlowEdgeKind>,
    label: &str,
    provenance_tags: &BTreeSet<String>,
) {
    if source_place.ty(source_body, tcx).ty != target_place.ty(target_body, tcx).ty {
        return;
    }
    for depth in 1..=u8::MAX {
        let Some(source) =
            node_for_place_depth(tcx, slots, source_fn, source_body, source_place, depth)
        else {
            break;
        };
        let Some(target) =
            node_for_place_depth(tcx, slots, target_fn, target_body, target_place, depth)
        else {
            break;
        };
        graph.add_edge(FlowEdge {
            kind: fixed_kind.unwrap_or_else(|| edge_kind(&source, &target)),
            source,
            target,
            label: format!("{label}:depth{depth}"),
            provenance_tags: provenance_tags.clone(),
        });
    }
}

#[allow(clippy::too_many_arguments)]
fn add_nested_exact_type_operand_edges<'tcx>(
    graph: &mut SourceGraph,
    tcx: TyCtxt<'tcx>,
    slots: &CrateSlots,
    source_fn: LocalDefId,
    source_body: &Body<'tcx>,
    source_operand: &Operand<'tcx>,
    target_fn: LocalDefId,
    target_body: &Body<'tcx>,
    target_place: Place<'tcx>,
    fixed_kind: Option<FlowEdgeKind>,
    label: &str,
    provenance_tags: &BTreeSet<String>,
) {
    let (Operand::Copy(source_place) | Operand::Move(source_place)) = source_operand else {
        return;
    };
    add_nested_exact_type_place_edges(
        graph,
        tcx,
        slots,
        source_fn,
        source_body,
        *source_place,
        target_fn,
        target_body,
        target_place,
        fixed_kind,
        label,
        provenance_tags,
    );
}

fn add_indirect_value_edge(
    graph: &mut SourceGraph,
    source: Option<String>,
    target: String,
    label: String,
    provenance_tags: BTreeSet<String>,
) {
    match source {
        Some(source) => graph.add_edge(FlowEdge {
            kind: edge_kind(&source, &target),
            source,
            target,
            label,
            provenance_tags,
        }),
        None => add_terminal_with_tags(
            graph,
            target,
            TerminalKind::Unsupported,
            format!("indirect-resolved-flow-source-unavailable:{label}"),
            false,
            provenance_tags,
        ),
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
    add_terminal_with_tags(graph, node, kind, label, realloc, BTreeSet::new());
}

fn add_terminal_with_tags(
    graph: &mut SourceGraph,
    node: String,
    kind: TerminalKind,
    label: String,
    realloc: bool,
    provenance_tags: BTreeSet<String>,
) {
    graph.add_terminal(TerminalRoot {
        id: terminal_id(kind, &node, &label),
        node,
        kind,
        label,
        realloc,
        provenance_tags,
    });
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct IndirectTargetSpec {
    canonical_path: String,
    kind: TerminalKind,
    realloc: bool,
}

fn indirect_target_tag(canonical_path: &str) -> String {
    format!("indirect-resolved-target({canonical_path})")
}

fn add_external_parameter_callback_root(
    graph: &mut SourceGraph,
    node: String,
    call_location: &str,
) {
    add_terminal_with_tags(
        graph,
        node,
        TerminalKind::OpaqueExternalCall,
        format!("indirect-external-parameter-callback:{call_location}"),
        false,
        BTreeSet::from(["indirect-external-parameter-callback".to_owned()]),
    );
}

fn add_public_setter_remainder_root(graph: &mut SourceGraph, node: String, call_location: &str) {
    add_terminal_with_tags(
        graph,
        node,
        TerminalKind::OpaqueExternalCall,
        format!("public-setter-reachable:{call_location}"),
        false,
        BTreeSet::from(["public-setter-reachable".to_owned()]),
    );
}

fn require_visible_targets<'a, T>(
    targets: &'a [T],
    call_location: &str,
) -> Result<&'a [T], String> {
    if targets.is_empty() {
        return Err(format!(
            "in-crate-visible target set is empty at {call_location}"
        ));
    }
    Ok(targets)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum IndirectCallArm {
    OutOfPopulation,
    VisibleTargets,
    VisibleTargetsAndExternalRemainder,
    ExternalParameterCallback,
}

fn indirect_call_arm(
    result_is_data_pointer: bool,
    visible_target_count: usize,
    has_external_parameter: bool,
    exclusively_external_parameter: bool,
    public_setter_reachable: bool,
    has_unexplained_predecessor: bool,
    call_location: &str,
) -> Result<IndirectCallArm, String> {
    if !result_is_data_pointer {
        Ok(IndirectCallArm::OutOfPopulation)
    } else if has_unexplained_predecessor {
        Err(format!(
            "unexplained predecessor in indirect-call target flow at {call_location}"
        ))
    } else if visible_target_count > 0 && public_setter_reachable {
        Ok(IndirectCallArm::VisibleTargetsAndExternalRemainder)
    } else if visible_target_count > 0 && !has_external_parameter {
        Ok(IndirectCallArm::VisibleTargets)
    } else if visible_target_count == 0
        && exclusively_external_parameter
        && !public_setter_reachable
    {
        Ok(IndirectCallArm::ExternalParameterCallback)
    } else {
        Err(format!(
            "unclassified empty-target indirect call at {call_location}"
        ))
    }
}

fn data_pointer_destination<'a>(
    result_is_data_pointer: bool,
    destination: Option<&'a str>,
    call_location: &str,
) -> Result<Option<&'a str>, String> {
    if !result_is_data_pointer {
        return Ok(None);
    }
    destination
        .map(Some)
        .ok_or_else(|| format!("data-pointer result has no source-graph node at {call_location}"))
}

fn expand_indirect_target_roots(
    node: &str,
    call_location: &str,
    targets: &[IndirectTargetSpec],
) -> Result<Vec<TerminalRoot>, String> {
    Ok(require_visible_targets(targets, call_location)?
        .iter()
        .map(|target| {
            let tag = indirect_target_tag(&target.canonical_path);
            let label = format!("{tag}:{call_location}");
            TerminalRoot {
                id: terminal_id(target.kind, node, &label),
                node: node.to_owned(),
                kind: target.kind,
                label,
                realloc: target.realloc,
                provenance_tags: BTreeSet::from([tag]),
            }
        })
        .collect())
}

fn roles_for_name(name: &str) -> Vec<crate::analyses::borrow_ownership::boundary_table::Role> {
    use crate::analyses::borrow_ownership::boundary_table::TABLE;
    TABLE
        .iter()
        .filter(|entry| entry.name == name)
        .flat_map(|entry| entry.roles.iter().copied())
        .collect()
}

fn boundary_matcher_applies(
    tcx: TyCtxt<'_>,
    callee: DefId,
    matcher: crate::analyses::borrow_ownership::boundary_table::Matcher,
    name: &str,
) -> bool {
    use rustc_hir::{def::DefKind, definitions::DefPathData};

    use crate::analyses::borrow_ownership::boundary_table::Matcher;

    match matcher {
        Matcher::ForeignC => false,
        Matcher::RustLibAssoc => !callee.is_local() && tcx.def_kind(callee) == DefKind::AssocFn,
        Matcher::RustLibNonLocal => !callee.is_local(),
        Matcher::AnyName => true,
        Matcher::RustPtrPath => {
            if callee.is_local() {
                return false;
            }
            let def_path = tcx.def_path(callee);
            matches!(
                def_path.data.first().map(|element| &element.data),
                Some(DefPathData::TypeNs(namespace)) if namespace.as_str() == "ptr"
            ) && matches!(
                def_path.data.get(3).map(|element| &element.data),
                Some(DefPathData::ValueNs(value)) if value.as_str() == name
            )
        }
    }
}

fn is_static_data_pointer_flow_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    source_ty: Ty<'tcx>,
    destination_ty: Ty<'tcx>,
) -> bool {
    use crate::analyses::borrow_ownership::boundary_table::{Role, TABLE};

    if source_ty != destination_ty || !source_ty.is_raw_ptr() {
        return false;
    }
    let item_name = tcx.item_name(callee);
    let name = item_name.as_str();
    TABLE.iter().any(|entry| {
        entry.name == name
            && boundary_matcher_applies(tcx, callee, entry.matcher, name)
            && entry
                .roles
                .iter()
                .any(|role| matches!(role, Role::ProvenanceFlow | Role::LoanCreating))
    })
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
    harness_call_kind_for_def(tcx, *callee)
}

fn harness_call_kind_for_def(tcx: TyCtxt<'_>, callee: DefId) -> HarnessCallKind {
    let Some(local) = callee.as_local() else {
        return HarnessCallKind::RustLib(callee);
    };
    match tcx.hir_node_by_def_id(local) {
        rustc_hir::Node::Item(_) | rustc_hir::Node::ImplItem(_) => HarnessCallKind::Local(local),
        rustc_hir::Node::ForeignItem(item) => {
            HarnessCallKind::LibC(item.ident.name.as_str().to_owned())
        }
        _ => HarnessCallKind::Unresolved,
    }
}

#[derive(Clone, Debug, Default)]
struct IndirectTargetFlow {
    incoming: BTreeMap<String, BTreeSet<String>>,
    seeds: FxHashMap<String, FxHashSet<DefId>>,
    empty_value_seeds: BTreeSet<String>,
    external_parameter_seeds: BTreeSet<String>,
    static_nodes: BTreeSet<String>,
    #[cfg(test)]
    parameter_remainders: BTreeMap<String, (bool, bool, bool)>,
    call_nodes: FxHashMap<(LocalDefId, usize), String>,
}

impl IndirectTargetFlow {
    fn add_edge(&mut self, source: String, target: String) {
        self.incoming.entry(target).or_default().insert(source);
    }

    fn add_seed(&mut self, node: String, target: DefId) {
        self.seeds.entry(node).or_default().insert(target);
    }

    fn add_external_parameter_seed(&mut self, node: String) {
        self.external_parameter_seeds.insert(node);
    }

    fn add_empty_value_seed(&mut self, node: String) {
        self.empty_value_seeds.insert(node);
    }

    fn add_static_node(&mut self, node: String) {
        self.static_nodes.insert(node);
    }

    #[cfg(test)]
    fn record_parameter_remainder(
        &mut self,
        node: String,
        public: bool,
        called: bool,
        external: bool,
    ) {
        self.parameter_remainders
            .insert(node, (public, called, external));
    }

    fn targets(&self, node: &str) -> FxHashSet<DefId> {
        let mut work = VecDeque::from([node.to_owned()]);
        let mut seen = BTreeSet::new();
        let mut targets = FxHashSet::default();
        while let Some(node) = work.pop_front() {
            if !seen.insert(node.clone()) {
                continue;
            }
            targets.extend(self.seeds.get(&node).into_iter().flatten().copied());
            work.extend(self.incoming.get(&node).into_iter().flatten().cloned());
        }
        targets
    }

    fn summary(&self, node: &str) -> IndirectTargetSummary {
        let mut work = VecDeque::from([(node.to_owned(), false)]);
        let mut seen = BTreeSet::new();
        let mut summary = IndirectTargetSummary::default();
        while let Some((node, crossed_static)) = work.pop_front() {
            let crossed_static = crossed_static || self.static_nodes.contains(&node);
            if !seen.insert((node.clone(), crossed_static)) {
                continue;
            }
            summary
                .targets
                .extend(self.seeds.get(&node).into_iter().flatten().copied());
            let is_external_parameter = self.external_parameter_seeds.contains(&node);
            let is_empty_value = self.empty_value_seeds.contains(&node);
            summary.has_external_parameter |= is_external_parameter;
            summary.public_setter_reachable |= is_external_parameter && crossed_static;
            match self.incoming.get(&node) {
                Some(incoming) if !incoming.is_empty() => work.extend(
                    incoming
                        .iter()
                        .cloned()
                        .map(|predecessor| (predecessor, crossed_static)),
                ),
                _ if !is_external_parameter
                    && !is_empty_value
                    && !self
                        .seeds
                        .get(&node)
                        .is_some_and(|targets| !targets.is_empty()) =>
                {
                    summary.unexplained_predecessors.insert(node);
                }
                _ => {}
            }
        }
        summary
    }

    fn exclusively_external_parameter(&self, node: &str) -> bool {
        let summary = self.summary(node);
        summary.targets.is_empty()
            && summary.has_external_parameter
            && summary.unexplained_predecessors.is_empty()
    }

    #[cfg(test)]
    fn diagnostic(&self, tcx: TyCtxt<'_>, node: &str) -> Vec<String> {
        let mut work = VecDeque::from([node.to_owned()]);
        let mut seen = BTreeSet::new();
        let mut rows = Vec::new();
        while let Some(node) = work.pop_front() {
            if !seen.insert(node.clone()) {
                continue;
            }
            let incoming = self.incoming.get(&node).cloned().unwrap_or_default();
            work.extend(incoming.iter().cloned());
            let mut targets = self
                .seeds
                .get(&node)
                .into_iter()
                .flatten()
                .map(|target| tcx.def_path_str(*target))
                .collect::<Vec<_>>();
            targets.sort();
            rows.push(format!(
                "node={node} incoming={incoming:?} target_seeds={targets:?} empty_value_seed={} external_seed={} parameter_remainder={:?}",
                self.empty_value_seeds.contains(&node),
                self.external_parameter_seeds.contains(&node),
                self.parameter_remainders.get(&node),
            ));
        }
        rows
    }
}

#[derive(Clone, Debug, Default)]
struct IndirectTargetSummary {
    targets: FxHashSet<DefId>,
    has_external_parameter: bool,
    public_setter_reachable: bool,
    unexplained_predecessors: BTreeSet<String>,
}

fn indirect_target_signature_compatible<'tcx>(
    tcx: TyCtxt<'tcx>,
    call_ty: Ty<'tcx>,
    target: DefId,
) -> Result<bool, String> {
    let TyKind::FnPtr(call_sig, call_header) = call_ty.kind() else {
        return Err(format!(
            "indirect call operand is not a function pointer: {call_ty}"
        ));
    };
    let call_sig = call_sig.with(*call_header).skip_binder();
    let target_sig = tcx.fn_sig(target).instantiate_identity().skip_binder();
    if call_sig.inputs().len() != target_sig.inputs().len() {
        return Ok(false);
    }
    let compatible_ty =
        |left: Ty<'tcx>, right: Ty<'tcx>| tcx.erase_regions(left) == tcx.erase_regions(right);
    Ok(call_sig
        .inputs()
        .iter()
        .copied()
        .zip(target_sig.inputs().iter().copied())
        .all(|(call, target)| compatible_ty(call, target))
        && compatible_ty(call_sig.output(), target_sig.output()))
}

fn target_field_node(tcx: TyCtxt<'_>, owner: DefId, field: usize) -> String {
    format!("fn-hook:{}::field{field}", tcx.def_path_str(owner))
}

fn target_static_node(tcx: TyCtxt<'_>, static_did: DefId) -> String {
    format!("fn-static:{}", tcx.def_path_str(static_did))
}

fn is_callback_storage_ty(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::FnPtr(..) => true,
        TyKind::Adt(def, args) if tcx.is_diagnostic_item(rustc_span::sym::Option, def.did()) => {
            args.types().any(|inner| is_callback_storage_ty(tcx, inner))
        }
        TyKind::Array(element, _) => is_callback_storage_ty(tcx, *element),
        _ => false,
    }
}

fn insert_target_reference_alias(
    aliases: &mut FxHashMap<Local, String>,
    local: Local,
    node: String,
) -> Result<(), String> {
    if let Some(previous) = aliases.insert(local, node.clone())
        && previous != node
    {
        return Err(format!(
            "callback reference local {local:?} has conflicting referents: {previous} {node}"
        ));
    }
    Ok(())
}

fn target_reference_aliases<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    static_pointers: &FxHashMap<Local, DefId>,
) -> Result<FxHashMap<Local, String>, String> {
    let mut aliases = FxHashMap::default();
    for statement in body.basic_blocks.iter().flat_map(|data| &data.statements) {
        let StatementKind::Assign(box (lhs, Rvalue::Ref(_, _, referent))) = &statement.kind else {
            continue;
        };
        let Some(local) = lhs.as_local() else {
            continue;
        };
        if !is_callback_storage_ty(tcx, referent.ty(body, tcx).ty) {
            continue;
        }
        let node = target_flow_node(tcx, fn_did, body, static_pointers, *referent);
        insert_target_reference_alias(&mut aliases, local, node)?;
    }
    Ok(aliases)
}

fn target_assignment_node<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    static_pointers: &FxHashMap<Local, DefId>,
    reference_aliases: &FxHashMap<Local, String>,
    lhs: Place<'tcx>,
) -> Result<String, String> {
    let Some(alias) = reference_aliases.get(&lhs.local) else {
        return Ok(target_flow_node(tcx, fn_did, body, static_pointers, lhs));
    };
    match lhs.projection.as_ref() {
        [ProjectionElem::Deref] => Ok(alias.clone()),
        [] => Ok(target_flow_node(tcx, fn_did, body, static_pointers, lhs)),
        projections if matches!(projections.first(), Some(ProjectionElem::Deref)) => Err(format!(
            "unsupported projected callback-reference store {lhs:?} via {alias}"
        )),
        _ => Ok(target_flow_node(tcx, fn_did, body, static_pointers, lhs)),
    }
}

fn constant_static_target(tcx: TyCtxt<'_>, operand: &Operand<'_>) -> Option<DefId> {
    let constant = operand.constant()?;
    let Const::Val(ConstValue::Scalar(Scalar::Ptr(pointer, _)), _) = constant.const_ else {
        return None;
    };
    match tcx.try_get_global_alloc(pointer.provenance.alloc_id()) {
        Some(GlobalAlloc::Static(static_did)) => Some(static_did),
        _ => None,
    }
}

fn static_pointer_locals(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
) -> Result<FxHashMap<Local, DefId>, String> {
    let mut statics = FxHashMap::default();
    for statement in body.basic_blocks.iter().flat_map(|data| &data.statements) {
        let Some((local, static_did)) = (|| {
            let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                return None;
            };
            let local = lhs.as_local()?;
            let operand = match rvalue {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand,
                _ => return None,
            };
            constant_static_target(tcx, operand).map(|static_did| (local, static_did))
        })() else {
            continue;
        };
        if let Some(previous) = statics.insert(local, static_did)
            && previous != static_did
        {
            return Err(format!(
                "one MIR local carries multiple static identities: {local:?} {} {}",
                tcx.def_path_str(previous),
                tcx.def_path_str(static_did)
            ));
        }
    }
    Ok(statics)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct StaticDataDerivation {
    static_did: DefId,
    depth_offset: i16,
}

fn static_data_derivation_for_place(
    derivations: &FxHashMap<Local, StaticDataDerivation>,
    place: Place<'_>,
) -> Result<Option<StaticDataDerivation>, String> {
    let Some(mut derivation) = derivations.get(&place.local).copied() else {
        return Ok(None);
    };
    for projection in place.projection.iter() {
        match projection {
            ProjectionElem::Deref => derivation.depth_offset += 1,
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {}
            _ => {
                return Err(format!(
                    "unsupported static-data projection {projection:?} in {place:?}"
                ));
            }
        }
    }
    Ok(Some(derivation))
}

fn insert_static_data_derivation(
    derivations: &mut FxHashMap<Local, StaticDataDerivation>,
    local: Local,
    derivation: StaticDataDerivation,
) -> Result<bool, String> {
    match derivations.get(&local) {
        Some(previous) if *previous == derivation => Ok(false),
        Some(previous) => Err(format!(
            "one MIR local has conflicting static-data derivations: {local:?} {previous:?} {derivation:?}"
        )),
        None => {
            derivations.insert(local, derivation);
            Ok(true)
        }
    }
}

fn derive_static_data_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
) -> Result<FxHashMap<Local, StaticDataDerivation>, String> {
    let mut derivations = static_pointer_locals(tcx, body)?
        .into_iter()
        .map(|(local, static_did)| {
            (
                local,
                StaticDataDerivation {
                    static_did,
                    depth_offset: -1,
                },
            )
        })
        .collect::<FxHashMap<_, _>>();
    loop {
        let mut changed = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                    continue;
                };
                let Some(target_local) = lhs.as_local() else {
                    continue;
                };
                let source = match rvalue {
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                    | Rvalue::CopyForDeref(place) => Some((*place, false)),
                    Rvalue::Cast(_, operand, _)
                        if operand.ty(&body.local_decls, tcx) == lhs.ty(body, tcx).ty =>
                    {
                        operand.place().map(|place| (place, false))
                    }
                    Rvalue::RawPtr(_, place) => Some((*place, true)),
                    _ => None,
                };
                let Some((source_place, creates_pointer_to_place)) = source else {
                    continue;
                };
                let Some(mut derivation) =
                    static_data_derivation_for_place(&derivations, source_place)?
                else {
                    continue;
                };
                if creates_pointer_to_place {
                    derivation.depth_offset -= 1;
                } else if source_place.ty(body, tcx).ty != lhs.ty(body, tcx).ty {
                    continue;
                }
                changed |=
                    insert_static_data_derivation(&mut derivations, target_local, derivation)?;
            }

            let Some(call) = harness_call(tcx, data.terminator()) else {
                continue;
            };
            let HarnessCallKind::RustLib(callee) = call.kind else {
                continue;
            };
            let Some(target_local) = call.destination.as_local() else {
                continue;
            };
            let Some(source_operand) = call.args.first().map(|argument| &argument.node) else {
                continue;
            };
            let Some(source_place) = source_operand.place() else {
                continue;
            };
            if !is_static_data_pointer_flow_call(
                tcx,
                callee,
                source_operand.ty(body, tcx),
                call.destination.ty(body, tcx).ty,
            ) {
                continue;
            }
            let Some(derivation) = static_data_derivation_for_place(&derivations, source_place)?
            else {
                continue;
            };
            changed |= insert_static_data_derivation(&mut derivations, target_local, derivation)?;
        }
        if !changed {
            break;
        }
    }
    if derivations
        .values()
        .any(|derivation| derivation.depth_offset < -1)
    {
        return Err(format!(
            "invalid static-data depth offset in {}",
            tcx.def_path_str(fn_did)
        ));
    }
    Ok(derivations)
}

fn static_data_node(
    tcx: TyCtxt<'_>,
    derivation: StaticDataDerivation,
    depth: u8,
) -> Option<String> {
    let static_depth = i16::from(depth) + derivation.depth_offset;
    (static_depth >= 0).then(|| {
        format!(
            "data-static:{}@d{static_depth}",
            tcx.def_path_str(derivation.static_did)
        )
    })
}

fn add_static_data_alias_edges<'tcx>(
    graph: &mut SourceGraph,
    tcx: TyCtxt<'tcx>,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    derivations: &FxHashMap<Local, StaticDataDerivation>,
) {
    for (&local, &derivation) in derivations {
        for depth in 0..=u8::MAX {
            let Some(local_node) =
                node_for_place_depth(tcx, slots, fn_did, body, Place::from(local), depth)
            else {
                break;
            };
            let Some(static_node) = static_data_node(tcx, derivation, depth) else {
                continue;
            };
            let label = format!(
                "static-data-alias:{}:{local:?}:depth{depth}",
                tcx.def_path_str(fn_did)
            );
            graph.add_edge(FlowEdge {
                source: static_node,
                target: local_node,
                kind: FlowEdgeKind::Local,
                label,
                provenance_tags: BTreeSet::new(),
            });
        }
    }
}

fn add_static_data_store_edges<'tcx>(
    graph: &mut SourceGraph,
    tcx: TyCtxt<'tcx>,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    derivations: &FxHashMap<Local, StaticDataDerivation>,
) -> Result<(), String> {
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let StatementKind::Assign(box (lhs, _)) = &statement.kind else {
                continue;
            };
            if !lhs
                .projection
                .iter()
                .any(|projection| matches!(projection, ProjectionElem::Deref))
            {
                continue;
            }
            let Some(derivation) = static_data_derivation_for_place(derivations, *lhs)? else {
                continue;
            };
            let Some(local_node) = node_for_place(tcx, slots, fn_did, body, *lhs) else {
                continue;
            };
            let Some(static_node) = static_data_node(tcx, derivation, 0) else {
                continue;
            };
            graph.add_edge(FlowEdge {
                source: local_node,
                target: static_node,
                kind: FlowEdgeKind::Local,
                label: format!(
                    "static-data-store:{}:bb{}[{}]",
                    tcx.def_path_str(fn_did),
                    bb.index(),
                    statement_index
                ),
                provenance_tags: BTreeSet::new(),
            });
        }
    }
    Ok(())
}

fn exact_raw_pointer_aliases<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> BTreeMap<Local, BTreeSet<Local>> {
    let mut aliases = BTreeMap::<Local, BTreeSet<Local>>::new();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                continue;
            };
            let Some(target) = lhs.as_local() else {
                continue;
            };
            let Rvalue::Use(Operand::Copy(source) | Operand::Move(source)) = rvalue else {
                continue;
            };
            let Some(source) = source.as_local() else {
                continue;
            };
            let source_ty = body.local_decls[source].ty;
            if source_ty == body.local_decls[target].ty && source_ty.is_raw_ptr() {
                aliases.entry(target).or_default().insert(source);
            }
        }

        let Some(call) = harness_call(tcx, data.terminator()) else {
            continue;
        };
        let HarnessCallKind::RustLib(callee) = call.kind else {
            continue;
        };
        let Some(target) = call.destination.as_local() else {
            continue;
        };
        let Some(source_operand) = call.args.first().map(|argument| &argument.node) else {
            continue;
        };
        let Some(source) = source_operand.place().and_then(|place| place.as_local()) else {
            continue;
        };
        if is_static_data_pointer_flow_call(
            tcx,
            callee,
            source_operand.ty(body, tcx),
            call.destination.ty(body, tcx).ty,
        ) {
            aliases.entry(target).or_default().insert(source);
        }
    }
    aliases
}

fn add_realized_pointer_alias_store_edges<'tcx>(
    graph: &mut SourceGraph,
    tcx: TyCtxt<'tcx>,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
) -> Result<(), String> {
    let aliases = exact_raw_pointer_aliases(tcx, body);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let StatementKind::Assign(box (lhs, _)) = &statement.kind else {
                continue;
            };
            let projections = lhs.projection.as_ref();
            if !matches!(projections.first(), Some(ProjectionElem::Deref)) {
                continue;
            }
            if projections != [ProjectionElem::Deref] {
                if aliases.contains_key(&lhs.local)
                    && node_for_place(tcx, slots, fn_did, body, *lhs).is_none()
                {
                    return Err(format!(
                        "unsupported projected realized pointer-alias store {lhs:?}"
                    ));
                }
                continue;
            }
            if !aliases.contains_key(&lhs.local) {
                continue;
            }
            if !lhs.ty(body, tcx).ty.is_raw_ptr() {
                continue;
            }
            let store_node = node_for_place(tcx, slots, fn_did, body, *lhs).ok_or_else(|| {
                format!("realized pointer-alias store has no graph node: {lhs:?}")
            })?;
            let mut work = VecDeque::from([lhs.local]);
            let mut seen = BTreeSet::new();
            while let Some(local) = work.pop_front() {
                if !seen.insert(local) {
                    continue;
                }
                work.extend(aliases.get(&local).into_iter().flatten().copied());
            }
            seen.remove(&lhs.local);
            for base in seen {
                let base_node =
                    node_for_place_depth(tcx, slots, fn_did, body, Place::from(base), 1)
                        .ok_or_else(|| {
                            format!("pointer-alias base has no depth-one graph node: {base:?}")
                        })?;
                graph.add_edge(FlowEdge {
                    source: store_node.clone(),
                    target: base_node,
                    kind: FlowEdgeKind::Local,
                    label: format!(
                        "realized-pointer-alias-store:{}:bb{}[{}]:{base:?}",
                        tcx.def_path_str(fn_did),
                        bb.index(),
                        statement_index
                    ),
                    provenance_tags: BTreeSet::new(),
                });
            }
        }
    }
    Ok(())
}

fn target_flow_node<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    static_pointers: &FxHashMap<Local, DefId>,
    place: Place<'tcx>,
) -> String {
    if matches!(place.projection.first(), Some(ProjectionElem::Deref))
        && let Some(static_did) = static_pointers.get(&place.local)
    {
        return target_static_node(tcx, *static_did);
    }
    let mut field_node = None;
    for (index, projection) in place.projection.iter().enumerate() {
        let ProjectionElem::Field(field, _) = projection else {
            continue;
        };
        let prefix = PlaceRef {
            local: place.local,
            projection: &place.projection[..index],
        };
        let base_ty = prefix.ty(&body.local_decls, tcx).ty;
        if let TyKind::Adt(def, _) = base_ty.kind() {
            field_node = Some(target_field_node(tcx, def.did(), field.index()));
        }
    }
    field_node.unwrap_or_else(|| {
        format!(
            "fn-local:{}:slot{}",
            tcx.def_path_str(fn_did),
            place.local.index()
        )
    })
}

fn constant_function_target(operand: &Operand<'_>) -> Option<DefId> {
    let constant = operand.constant()?;
    let TyKind::FnDef(target, _) = constant.ty().kind() else {
        return None;
    };
    Some(*target)
}

fn add_target_operand_flow<'tcx>(
    flow: &mut IndirectTargetFlow,
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    static_pointers: &FxHashMap<Local, DefId>,
    operand: &Operand<'tcx>,
    target: String,
) {
    if let Some(function) = constant_function_target(operand) {
        flow.add_seed(target, function);
    } else if let Some(place) = operand.place() {
        flow.add_edge(
            target_flow_node(tcx, fn_did, body, static_pointers, place),
            target,
        );
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct IndirectCallResolution {
    visible_targets: Vec<DefId>,
    has_external_parameter: bool,
    exclusively_external_parameter: bool,
    public_setter_reachable: bool,
    has_unexplained_predecessor: bool,
    #[cfg(test)]
    diagnostic: Vec<String>,
}

fn collect_indirect_call_resolutions<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
) -> FxHashMap<(LocalDefId, usize), IndirectCallResolution> {
    let function_set = functions.iter().copied().collect::<FxHashSet<_>>();
    let static_pointers = functions
        .iter()
        .copied()
        .map(|function| {
            let body_ref = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let statics = static_pointer_locals(tcx, &body_ref).unwrap_or_else(|error| {
                panic!(
                    "A4C STOP phase=graph-construction candidate=none: static target identity in {}: {error}",
                    tcx.def_path_str(function)
                )
            });
            (function, statics)
        })
        .collect::<FxHashMap<_, _>>();
    let mut flow = IndirectTargetFlow::default();
    for static_did in static_pointers
        .values()
        .flat_map(|statics| statics.values())
    {
        flow.add_static_node(target_static_node(tcx, *static_did));
    }
    let mut parameter_nodes = Vec::new();
    let mut called_parameters = FxHashSet::default();
    let mut call_types = FxHashMap::<(LocalDefId, usize), Ty<'tcx>>::default();
    for &fn_did in functions {
        let body_ref = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        let body = &*body_ref;
        let body_static_pointers = &static_pointers[&fn_did];
        let reference_aliases =
            target_reference_aliases(tcx, fn_did, body, body_static_pointers).unwrap_or_else(
                |error| {
                    panic!(
                        "A4C STOP phase=graph-construction candidate=none: callback reference aliases in {}: {error}",
                        tcx.def_path_str(fn_did)
                    )
                },
            );
        for local in body.args_iter() {
            parameter_nodes.push((
                fn_did,
                local.index(),
                target_flow_node(tcx, fn_did, body, body_static_pointers, Place::from(local)),
            ));
        }
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for statement in &data.statements {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                    continue;
                };
                if let Rvalue::Aggregate(kind, operands) = rvalue
                    && let AggregateKind::Adt(def_id, _, _, _, _) = kind.as_ref()
                    && def_id.as_local().is_some()
                {
                    for (field, operand) in operands.iter_enumerated() {
                        add_target_operand_flow(
                            &mut flow,
                            tcx,
                            fn_did,
                            body,
                            body_static_pointers,
                            operand,
                            target_field_node(tcx, *def_id, field.index()),
                        );
                    }
                    continue;
                }
                let target = target_assignment_node(
                    tcx,
                    fn_did,
                    body,
                    body_static_pointers,
                    &reference_aliases,
                    *lhs,
                )
                .unwrap_or_else(|error| {
                    panic!(
                        "A4C STOP phase=graph-construction candidate=none: callback reference store in {}: {error}",
                        tcx.def_path_str(fn_did)
                    )
                });
                if let Rvalue::Aggregate(kind, operands) = rvalue
                    && let AggregateKind::Adt(def_id, variant, _, _, _) = kind.as_ref()
                    && tcx.is_diagnostic_item(rustc_span::sym::Option, *def_id)
                    && variant.as_usize() == 0
                    && operands.is_empty()
                {
                    flow.add_empty_value_seed(target);
                    continue;
                }
                match rvalue {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                        add_target_operand_flow(
                            &mut flow,
                            tcx,
                            fn_did,
                            body,
                            body_static_pointers,
                            operand,
                            target,
                        );
                    }
                    Rvalue::Aggregate(_, operands) => {
                        for operand in operands {
                            add_target_operand_flow(
                                &mut flow,
                                tcx,
                                fn_did,
                                body,
                                body_static_pointers,
                                operand,
                                target.clone(),
                            );
                        }
                    }
                    Rvalue::CopyForDeref(place) => flow.add_edge(
                        target_flow_node(tcx, fn_did, body, body_static_pointers, *place),
                        target,
                    ),
                    _ => {}
                }
            }

            let terminator = data.terminator();
            let (func, args, destination) = match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => (func, args.as_ref(), *destination),
                TerminatorKind::TailCall { func, args, .. } => {
                    (func, args.as_ref(), Place::return_place())
                }
                _ => continue,
            };
            let Some(direct) = constant_function_target(func) else {
                if let Some(place) = func.place() {
                    let call = (fn_did, bb.index());
                    flow.call_nodes.insert(
                        call,
                        target_flow_node(tcx, fn_did, body, body_static_pointers, place),
                    );
                    call_types.insert(call, func.ty(body, tcx));
                }
                continue;
            };
            match harness_call_kind_for_def(tcx, direct) {
                HarnessCallKind::Local(callee) if function_set.contains(&callee) => {
                    let callee_body_ref =
                        tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
                    let callee_body = &*callee_body_ref;
                    let callee_static_pointers = &static_pointers[&callee];
                    for (index, argument) in args.iter().enumerate() {
                        let parameter = Local::from_usize(index + 1);
                        called_parameters.insert((callee, parameter.index()));
                        add_target_operand_flow(
                            &mut flow,
                            tcx,
                            fn_did,
                            body,
                            body_static_pointers,
                            &argument.node,
                            target_flow_node(
                                tcx,
                                callee,
                                callee_body,
                                callee_static_pointers,
                                Place::from(parameter),
                            ),
                        );
                    }
                    flow.add_edge(
                        target_flow_node(
                            tcx,
                            callee,
                            callee_body,
                            callee_static_pointers,
                            Place::from(RETURN_PLACE),
                        ),
                        target_flow_node(tcx, fn_did, body, body_static_pointers, destination),
                    );
                }
                HarnessCallKind::RustLib(callee)
                    if matches!(
                        tcx.item_name(callee).as_str(),
                        "expect" | "unwrap" | "unwrap_unchecked"
                    ) =>
                {
                    if let Some(argument) = args.first() {
                        add_target_operand_flow(
                            &mut flow,
                            tcx,
                            fn_did,
                            body,
                            body_static_pointers,
                            &argument.node,
                            target_flow_node(tcx, fn_did, body, body_static_pointers, destination),
                        );
                    }
                }
                _ => {}
            }
        }
    }
    for (call, node) in &flow.call_nodes {
        let call_ty = call_types[call];
        for target in flow.targets(node) {
            let compatible = indirect_target_signature_compatible(tcx, call_ty, target)
                .unwrap_or_else(|error| {
                    panic!(
                        "A4C STOP phase=graph-construction candidate=none: signature filter at {}:bb{}: {error}",
                        tcx.def_path_str(call.0),
                        call.1,
                    )
                });
            if !compatible {
                continue;
            }
            let Some(callee) = target.as_local() else {
                continue;
            };
            if !function_set.contains(&callee) {
                continue;
            }
            let callee_body_ref = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
            for parameter in callee_body_ref.args_iter() {
                called_parameters.insert((callee, parameter.index()));
            }
        }
    }
    for (fn_did, parameter, node) in parameter_nodes {
        let public = tcx.visibility(fn_did.to_def_id()).is_public();
        let called = called_parameters.contains(&(fn_did, parameter));
        let external = parameter_has_external_remainder(public, called);
        #[cfg(test)]
        flow.record_parameter_remainder(node.clone(), public, called, external);
        if external {
            flow.add_external_parameter_seed(node);
        }
    }
    flow.call_nodes
        .iter()
        .map(|(call, node)| {
            let summary = flow.summary(node);
            let call_ty = call_types[call];
            let mut targets = summary
                .targets
                .into_iter()
                .filter(|target| {
                    indirect_target_signature_compatible(tcx, call_ty, *target).unwrap_or_else(
                        |error| {
                            panic!(
                                "A4C STOP phase=graph-construction candidate=none: signature filter at {}:bb{}: {error}",
                                tcx.def_path_str(call.0),
                                call.1,
                            )
                        },
                    )
                })
                .collect::<Vec<_>>();
            targets.sort_by_key(|target| tcx.def_path_str(*target));
            let public_setter_reachable = summary.public_setter_reachable
                || (summary.has_external_parameter && !targets.is_empty());
            let exclusively_external_parameter = targets.is_empty()
                && summary.has_external_parameter
                && summary.unexplained_predecessors.is_empty();
            (
                *call,
                IndirectCallResolution {
                    visible_targets: targets,
                    has_external_parameter: summary.has_external_parameter,
                    exclusively_external_parameter,
                    public_setter_reachable,
                    has_unexplained_predecessor: !summary.unexplained_predecessors.is_empty(),
                    #[cfg(test)]
                    diagnostic: flow.diagnostic(tcx, node),
                },
            )
        })
        .collect()
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

fn parameter_has_external_remainder(public: bool, receives_in_crate_arguments: bool) -> bool {
    public || !receives_in_crate_arguments
}

fn build_source_graph(tcx: TyCtxt<'_>, slots: &CrateSlots, export: &BoExport) -> SourceGraph {
    use crate::analyses::borrow_ownership::boundary_table::Role;

    let program = collect_program(tcx);
    let program_functions = program.functions.iter().copied().collect::<FxHashSet<_>>();
    let indirect_call_resolutions = collect_indirect_call_resolutions(tcx, &program.functions);
    let static_data_derivations = program
        .functions
        .iter()
        .copied()
        .map(|function| {
            let body_ref = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let derivations = derive_static_data_locals(tcx, function, &body_ref).unwrap_or_else(
                |error| {
                    panic!(
                        "A4C STOP phase=graph-construction candidate=none: static data aliases in {}: {error}",
                        tcx.def_path_str(function)
                    )
                },
            );
            (function, derivations)
        })
        .collect::<FxHashMap<_, _>>();
    let mut graph = SourceGraph::default();
    let mut parameter_nodes = Vec::<(LocalDefId, Local, String)>::new();
    let mut nested_parameter_nodes = Vec::<(LocalDefId, Local, u8, String)>::new();
    let mut called_parameters = FxHashSet::<(LocalDefId, usize)>::default();

    for &fn_did in &program.functions {
        let body_ref = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        let body = &*body_ref;
        add_static_data_alias_edges(
            &mut graph,
            tcx,
            slots,
            fn_did,
            body,
            &static_data_derivations[&fn_did],
        );
        add_static_data_store_edges(
            &mut graph,
            tcx,
            slots,
            fn_did,
            body,
            &static_data_derivations[&fn_did],
        )
        .unwrap_or_else(|error| {
            panic!(
                "A4C STOP phase=graph-construction candidate=none: static data stores in {}: {error}",
                tcx.def_path_str(fn_did)
            )
        });
        add_realized_pointer_alias_store_edges(&mut graph, tcx, slots, fn_did, body)
            .unwrap_or_else(|error| {
                panic!(
                    "A4C STOP phase=graph-construction candidate=none: realized pointer-alias stores in {}: {error}",
                    tcx.def_path_str(fn_did)
                )
            });
        for local in body.args_iter() {
            if let Some(node) = node_for_place(tcx, slots, fn_did, body, Place::from(local)) {
                parameter_nodes.push((fn_did, local, node));
            }
            for depth in 1..=u8::MAX {
                let Some(node) =
                    node_for_place_depth(tcx, slots, fn_did, body, Place::from(local), depth)
                else {
                    break;
                };
                nested_parameter_nodes.push((fn_did, local, depth, node));
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
                            let (terminal, provenance_tags) = constant_root(tcx, operand);
                            add_terminal_with_tags(
                                &mut graph,
                                target,
                                terminal,
                                format!("constant-{label}"),
                                false,
                                provenance_tags,
                            );
                        }
                    }
                    continue;
                }

                let Some(target) = node_for_place(tcx, slots, fn_did, body, *lhs) else {
                    continue;
                };
                match rvalue {
                    Rvalue::Use(operand @ Operand::Constant(_))
                    | Rvalue::Cast(_, operand @ Operand::Constant(_), _) => {
                        let (terminal, provenance_tags) = constant_root(tcx, operand);
                        add_terminal_with_tags(
                            &mut graph,
                            target,
                            terminal,
                            format!(
                                "{}:{location}",
                                if terminal == TerminalKind::NullLiteral {
                                    "null-literal"
                                } else if terminal == TerminalKind::StaticOrInterior {
                                    "string-literal"
                                } else {
                                    "constant-pointer"
                                }
                            ),
                            false,
                            provenance_tags,
                        );
                    }
                    Rvalue::Use(operand) => {
                        add_value_edge(
                            &mut graph,
                            node_for_operand(tcx, slots, fn_did, body, operand),
                            target,
                            format!("transfer:{location}"),
                        );
                        add_nested_exact_type_operand_edges(
                            &mut graph,
                            tcx,
                            slots,
                            fn_did,
                            body,
                            operand,
                            fn_did,
                            body,
                            *lhs,
                            None,
                            &format!("depth-transfer:{location}"),
                            &BTreeSet::new(),
                        );
                    }
                    Rvalue::Cast(_, operand, _) => add_value_edge(
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
                        called_parameters.insert((callee, parameter.index()));
                        if let Some(source) =
                            node_for_operand(tcx, slots, fn_did, body, &argument.node)
                        {
                            let label = format!(
                                "call-arg:{call_location}->{}:arg{}",
                                tcx.def_path_str(callee),
                                index + 1
                            );
                            graph.add_edge(FlowEdge {
                                source,
                                target,
                                kind: FlowEdgeKind::Call,
                                label: label.clone(),
                                provenance_tags: BTreeSet::new(),
                            });
                            add_nested_exact_type_operand_edges(
                                &mut graph,
                                tcx,
                                slots,
                                fn_did,
                                body,
                                &argument.node,
                                callee,
                                callee_body,
                                Place::from(parameter),
                                Some(FlowEdgeKind::Call),
                                &label,
                                &BTreeSet::new(),
                            );
                        } else if matches!(&argument.node, Operand::Constant(_)) {
                            let (terminal, provenance_tags) = constant_root(tcx, &argument.node);
                            add_terminal_with_tags(
                                &mut graph,
                                target,
                                terminal,
                                format!(
                                    "constant-call-arg:{call_location}->{}:arg{}",
                                    tcx.def_path_str(callee),
                                    index + 1
                                ),
                                false,
                                provenance_tags,
                            );
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
                            target: target.clone(),
                            kind: FlowEdgeKind::Call,
                            label: format!(
                                "call-return:{}->{call_location}",
                                tcx.def_path_str(callee)
                            ),
                            provenance_tags: BTreeSet::new(),
                        });
                        add_nested_exact_type_place_edges(
                            &mut graph,
                            tcx,
                            slots,
                            callee,
                            callee_body,
                            Place::from(RETURN_PLACE),
                            fn_did,
                            body,
                            call.destination,
                            Some(FlowEdgeKind::Call),
                            &format!("call-return:{}->{call_location}", tcx.def_path_str(callee)),
                            &BTreeSet::new(),
                        );
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
                            let label = format!("foreign-flow:{call_location}:{name}");
                            add_value_edge(
                                &mut graph,
                                call.args.first().and_then(|arg| {
                                    node_for_operand(tcx, slots, fn_did, body, &arg.node)
                                }),
                                target,
                                label.clone(),
                            );
                            if let Some(argument) = call.args.first() {
                                add_nested_exact_type_operand_edges(
                                    &mut graph,
                                    tcx,
                                    slots,
                                    fn_did,
                                    body,
                                    &argument.node,
                                    fn_did,
                                    body,
                                    call.destination,
                                    None,
                                    &label,
                                    &BTreeSet::new(),
                                );
                            }
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
                            let label = format!("rust-flow:{call_location}:{name}");
                            add_value_edge(
                                &mut graph,
                                call.args.first().and_then(|arg| {
                                    node_for_operand(tcx, slots, fn_did, body, &arg.node)
                                }),
                                target,
                                label.clone(),
                            );
                            if let Some(argument) = call.args.first() {
                                add_nested_exact_type_operand_edges(
                                    &mut graph,
                                    tcx,
                                    slots,
                                    fn_did,
                                    body,
                                    &argument.node,
                                    fn_did,
                                    body,
                                    call.destination,
                                    None,
                                    &label,
                                    &BTreeSet::new(),
                                );
                            }
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
                    let result_is_data_pointer = call.destination.ty(body, tcx).ty.is_raw_ptr();
                    let resolution = indirect_call_resolutions
                        .get(&(fn_did, bb.index()))
                        .cloned()
                        .unwrap_or_default();
                    let arm = indirect_call_arm(
                        result_is_data_pointer,
                        resolution.visible_targets.len(),
                        resolution.has_external_parameter,
                        resolution.exclusively_external_parameter,
                        resolution.public_setter_reachable,
                        resolution.has_unexplained_predecessor,
                        &call_location,
                    )
                    .unwrap_or_else(|error| {
                        panic!(
                            "A4C STOP phase=graph-construction candidate=none: {error}; target-flow diagnostic:\n{}",
                            resolution.diagnostic.join("\n")
                        )
                    });
                    if arm == IndirectCallArm::OutOfPopulation {
                        continue;
                    }
                    let destination = data_pointer_destination(
                        result_is_data_pointer,
                        destination.as_deref(),
                        &call_location,
                    )
                    .unwrap_or_else(|error| {
                        panic!("A4C STOP phase=graph-construction candidate=none: {error}")
                    })
                    .expect("a classified data-pointer call has a destination");
                    if arm == IndirectCallArm::ExternalParameterCallback {
                        add_external_parameter_callback_root(
                            &mut graph,
                            destination.to_owned(),
                            &call_location,
                        );
                        continue;
                    }
                    if arm == IndirectCallArm::VisibleTargetsAndExternalRemainder {
                        add_public_setter_remainder_root(
                            &mut graph,
                            destination.to_owned(),
                            &call_location,
                        );
                    }
                    for &resolved_target in &resolution.visible_targets {
                        let canonical_path = tcx.def_path_str(resolved_target);
                        let provenance_tags =
                            BTreeSet::from([indirect_target_tag(&canonical_path)]);
                        match harness_call_kind_for_def(tcx, resolved_target) {
                            HarnessCallKind::Local(callee)
                                if program_functions.contains(&callee) =>
                            {
                                let callee_body_ref =
                                    tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
                                let callee_body = &*callee_body_ref;
                                for (index, argument) in call.args.iter().enumerate() {
                                    let parameter = Local::from_usize(index + 1);
                                    let Some(parameter_target) = node_for_place(
                                        tcx,
                                        slots,
                                        callee,
                                        callee_body,
                                        Place::from(parameter),
                                    ) else {
                                        continue;
                                    };
                                    called_parameters.insert((callee, parameter.index()));
                                    if let Some(source) =
                                        node_for_operand(tcx, slots, fn_did, body, &argument.node)
                                    {
                                        let label = format!(
                                            "indirect-call-arg:{call_location}->{canonical_path}:arg{}",
                                            index + 1
                                        );
                                        graph.add_edge(FlowEdge {
                                            source,
                                            target: parameter_target,
                                            kind: FlowEdgeKind::Call,
                                            label: label.clone(),
                                            provenance_tags: BTreeSet::new(),
                                        });
                                        add_nested_exact_type_operand_edges(
                                            &mut graph,
                                            tcx,
                                            slots,
                                            fn_did,
                                            body,
                                            &argument.node,
                                            callee,
                                            callee_body,
                                            Place::from(parameter),
                                            Some(FlowEdgeKind::Call),
                                            &label,
                                            &BTreeSet::new(),
                                        );
                                    } else if matches!(&argument.node, Operand::Constant(_)) {
                                        let (terminal, mut constant_tags) =
                                            constant_root(tcx, &argument.node);
                                        constant_tags.extend(provenance_tags.iter().cloned());
                                        add_terminal_with_tags(
                                            &mut graph,
                                            parameter_target,
                                            terminal,
                                            format!(
                                                "constant-indirect-call-arg:{call_location}->{canonical_path}:arg{}",
                                                index + 1
                                            ),
                                            false,
                                            constant_tags,
                                        );
                                    }
                                }
                                add_nested_exact_type_place_edges(
                                    &mut graph,
                                    tcx,
                                    slots,
                                    callee,
                                    callee_body,
                                    Place::from(RETURN_PLACE),
                                    fn_did,
                                    body,
                                    call.destination,
                                    Some(FlowEdgeKind::Call),
                                    &format!(
                                        "indirect-call-return:{canonical_path}->{call_location}"
                                    ),
                                    &provenance_tags,
                                );
                                add_indirect_value_edge(
                                    &mut graph,
                                    node_for_place(
                                        tcx,
                                        slots,
                                        callee,
                                        callee_body,
                                        Place::from(RETURN_PLACE),
                                    ),
                                    destination.to_owned(),
                                    format!(
                                        "indirect-call-return:{canonical_path}->{call_location}"
                                    ),
                                    provenance_tags,
                                );
                            }
                            HarnessCallKind::Local(_) => {
                                add_terminal_with_tags(
                                    &mut graph,
                                    destination.to_owned(),
                                    TerminalKind::Unsupported,
                                    format!(
                                        "indirect-resolved-local-outside-program:{call_location}:{canonical_path}"
                                    ),
                                    false,
                                    provenance_tags,
                                );
                            }
                            HarnessCallKind::LibC(name) => {
                                let target = destination.to_owned();
                                let roles = roles_for_name(&name);
                                if roles.contains(&Role::Source) {
                                    for root in expand_indirect_target_roots(
                                        &target,
                                        &call_location,
                                        &[IndirectTargetSpec {
                                            canonical_path,
                                            kind: TerminalKind::RecognizedAllocation,
                                            realloc: name == "realloc",
                                        }],
                                    )
                                    .expect("non-empty resolved target")
                                    {
                                        graph.add_terminal(root);
                                    }
                                } else if roles.iter().any(|role| {
                                    matches!(
                                        role,
                                        Role::ProvenanceFlow
                                            | Role::LoanCreating
                                            | Role::FlowTransfer
                                    )
                                }) {
                                    let source = call.args.first().and_then(|arg| {
                                        node_for_operand(tcx, slots, fn_did, body, &arg.node)
                                    });
                                    let label = format!(
                                        "indirect-foreign-flow:{call_location}:{canonical_path}"
                                    );
                                    if let Some(argument) = call.args.first() {
                                        add_nested_exact_type_operand_edges(
                                            &mut graph,
                                            tcx,
                                            slots,
                                            fn_did,
                                            body,
                                            &argument.node,
                                            fn_did,
                                            body,
                                            call.destination,
                                            None,
                                            &label,
                                            &provenance_tags,
                                        );
                                    }
                                    add_indirect_value_edge(
                                        &mut graph,
                                        source,
                                        target,
                                        label,
                                        provenance_tags,
                                    );
                                } else {
                                    add_terminal_with_tags(
                                        &mut graph,
                                        target,
                                        TerminalKind::OpaqueExternalCall,
                                        format!(
                                            "indirect-foreign-result:{call_location}:{canonical_path}"
                                        ),
                                        false,
                                        provenance_tags,
                                    );
                                }
                            }
                            HarnessCallKind::RustLib(callee) => {
                                let target = destination.to_owned();
                                let item_name = tcx.item_name(callee);
                                let name = item_name.as_str();
                                let roles = roles_for_name(name);
                                if roles.iter().any(|role| {
                                    matches!(role, Role::ProvenanceFlow | Role::LoanCreating)
                                }) {
                                    let source = call.args.first().and_then(|arg| {
                                        node_for_operand(tcx, slots, fn_did, body, &arg.node)
                                    });
                                    let label = format!(
                                        "indirect-rust-flow:{call_location}:{canonical_path}"
                                    );
                                    if let Some(argument) = call.args.first() {
                                        add_nested_exact_type_operand_edges(
                                            &mut graph,
                                            tcx,
                                            slots,
                                            fn_did,
                                            body,
                                            &argument.node,
                                            fn_did,
                                            body,
                                            call.destination,
                                            None,
                                            &label,
                                            &provenance_tags,
                                        );
                                    }
                                    add_indirect_value_edge(
                                        &mut graph,
                                        source,
                                        target,
                                        label,
                                        provenance_tags,
                                    );
                                } else if roles.contains(&Role::NullConstructor) {
                                    add_terminal_with_tags(
                                        &mut graph,
                                        target,
                                        TerminalKind::Unsupported,
                                        format!(
                                            "indirect-null-constructor:{call_location}:{canonical_path}"
                                        ),
                                        false,
                                        provenance_tags,
                                    );
                                } else {
                                    add_terminal_with_tags(
                                        &mut graph,
                                        target,
                                        TerminalKind::OpaqueExternalCall,
                                        format!(
                                            "indirect-rust-result:{call_location}:{canonical_path}"
                                        ),
                                        false,
                                        provenance_tags,
                                    );
                                }
                            }
                            HarnessCallKind::Unresolved => unreachable!(
                                "a concrete visible target cannot remain an unresolved call kind"
                            ),
                        }
                    }
                }
            }
        }
    }

    for (fn_did, local, node) in parameter_nodes {
        let public = tcx.visibility(fn_did.to_def_id()).is_public();
        if parameter_has_external_remainder(
            public,
            called_parameters.contains(&(fn_did, local.index())),
        ) {
            add_terminal(
                &mut graph,
                node,
                TerminalKind::ExternalParameter,
                format!("external-parameter:{}:{local:?}", tcx.def_path_str(fn_did)),
                false,
            );
        }
    }
    for (fn_did, local, depth, node) in nested_parameter_nodes {
        let public = tcx.visibility(fn_did.to_def_id()).is_public();
        if parameter_has_external_remainder(
            public,
            called_parameters.contains(&(fn_did, local.index())),
        ) {
            add_terminal_with_tags(
                &mut graph,
                node,
                TerminalKind::ExternalParameter,
                format!(
                    "external-parameter:{}:{local:?}:depth{depth}",
                    tcx.def_path_str(fn_did)
                ),
                false,
                BTreeSet::from(["external-parameter-pointee-load".to_owned()]),
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

fn select_isolated_input(
    input: &[A4InputRow],
    program: &str,
    field_key: &str,
) -> Result<(Vec<A4InputRow>, Vec<A4InputRow>), String> {
    let census = input
        .iter()
        .filter(|row| {
            row.program == program
                && row.field_key == field_key
                && row.proof_reason == "allocation-source-count-0"
        })
        .cloned()
        .collect::<Vec<_>>();
    let exceptions = input
        .iter()
        .filter(|row| {
            row.program == program && row.field_key == field_key && row.baseline_force == "sat"
        })
        .cloned()
        .collect::<Vec<_>>();
    if census.len() + exceptions.len() != 1 {
        return Err(format!(
            "isolated identity must select exactly one population row: program={program} candidate={field_key} census={} exceptions={}",
            census.len(),
            exceptions.len()
        ));
    }
    Ok((census, exceptions))
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
        CauseFlag::NullLiteralRoot => "null-literal-root",
    }
}

fn evidence_tokens(evidence: &RootEvidence) -> Vec<String> {
    evidence
        .flags
        .iter()
        .map(|flag| flag_label(*flag).to_owned())
        .chain(evidence.provenance_tags.iter().cloned())
        .collect()
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
    provenance_tags: BTreeSet<String>,
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
            evidence_tokens(&RootEvidence {
                flags: record.flags.clone(),
                provenance_tags: record.provenance_tags.clone(),
            })
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
                evidence_tokens(&root.evidence).join("|"),
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
                evidence_tokens(&root.evidence).join("|"),
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
    graph_provenance_tags: BTreeSet<String>,
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
            evidence_tokens(&RootEvidence {
                flags: record.graph_flags.clone(),
                provenance_tags: record.graph_provenance_tags.clone(),
            })
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
    let isolated_candidate = std::env::var("CRAT_A4_SOURCE_CANDIDATE")
        .expect("source-census isolated candidate identity");

    emit_phase(started, "input-parse", None, 0);
    let input = parse_a4_input(&input_path)
        .unwrap_or_else(|error| panic!("A4C STOP phase=input-parse candidate=none: {error}"));
    let program_census_input = input
        .iter()
        .filter(|row| {
            row.program == program_name && row.proof_reason == "allocation-source-count-0"
        })
        .cloned()
        .collect::<Vec<_>>();
    let program_exception_input = input
        .iter()
        .filter(|row| row.program == program_name && row.baseline_force == "sat")
        .cloned()
        .collect::<Vec<_>>();
    assert!(
        program_census_input
            .iter()
            .all(|row| row.baseline_force == "unsat"),
        "A4C STOP phase=input-partition candidate={program_name}: census row is not hard-UNSAT"
    );
    let expected_exceptions = exception_specs()
        .into_iter()
        .filter(|spec| spec.program == program_name)
        .map(|spec| (spec.field_key, spec.ordinary_kind))
        .collect::<BTreeSet<_>>();
    let actual_exceptions = program_exception_input
        .iter()
        .map(|row| (row.field_key.as_str(), kind_label(row.baseline_kind)))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        actual_exceptions, expected_exceptions,
        "A4C STOP phase=exception-identity candidate={program_name}: exact exception drift"
    );
    let (census_input, exception_input) =
        select_isolated_input(&input, &program_name, &isolated_candidate).unwrap_or_else(|error| {
            panic!("A4C STOP phase=input-partition candidate={isolated_candidate}: {error}")
        });

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
        let provenance_tags = roots
            .iter()
            .flat_map(|root| root.evidence.provenance_tags.iter().cloned())
            .collect();
        candidate_records.push(CandidateRecord {
            input: input_row,
            class,
            flags,
            provenance_tags,
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
        let graph_provenance_tags = roots
            .iter()
            .flat_map(|root| root.evidence.provenance_tags.iter().cloned())
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
            graph_provenance_tags,
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
const CANDIDATE_MEMORY_MAX_BYTES: u64 = 100 * 1024 * 1024 * 1024;
const HOST_MEMORY_MARGIN_BYTES: u64 = 8 * 1024 * 1024 * 1024;
const LIL_ORACLE_PARTIAL_SHA256: &str =
    "86c9e73d0e419a08e04c6ff3ac91531d948cbc31a8acb80d9c5f7cd238587feb";
const LIL_RESUME9_HEAD: &str = "e87be067d4717d3ea74dd5192f210b6de4170bac";
const LIL_RESUME9_UNITS: [(&str, &str); 19] = [
    (
        "src::lil::_expreval_t::field0@d0",
        "938b30fa2b20fcd987f4bef32163c6354545a6f451c44d4942445dd3dd0fbaa7",
    ),
    (
        "src::lil::_lil_env_t::field0@d0",
        "356b95b1049dce7b4dc436c2a42ad57e904df1b1bad9f1c027416367608474fc",
    ),
    (
        "src::lil::_lil_env_t::field1@d0",
        "c5255d927f6e2d55cc8a4938bd6c4b616871182c75bfa26efc2b0381314f5ff9",
    ),
    (
        "src::lil::_lil_env_t::field2@d0",
        "0bd5509d95a365c8f3a355b26ae292695158e3806a76b592857421ab5b5e0519",
    ),
    (
        "src::lil::_lil_env_t::field5@d0",
        "c55369f57d9f70388801e0bc0c146a1c4f6c990b6d2317331d85d3b8526969d7",
    ),
    (
        "src::lil::_lil_func_t::field0@d0",
        "ba0ece0a776e6d83d344ce0b31d382b182c8138036c7cb846c0a754e4593a921",
    ),
    (
        "src::lil::_lil_func_t::field1@d0",
        "8de2876076591d7a7c1f7de900020b30460566fdbf5f61d47271f374bdefea84",
    ),
    (
        "src::lil::_lil_func_t::field2@d0",
        "d2e24c6d2b5d7c2d607872a1f1e1c68afe367c7bab91600955a684e402f05c73",
    ),
    (
        "src::lil::_lil_t::field0@d0",
        "86dfad5c0349ba38251adbaf11afef156c14bd928c1e52ead464b06842f3f1ec",
    ),
    (
        "src::lil::_lil_t::field10@d0",
        "28dcc516054ef777481306efaf02db9498b43bb05892ad4e12c19d96a3698a10",
    ),
    (
        "src::lil::_lil_t::field11@d0",
        "213c5ba9f2e479b96f8ee1961f44a5e082673c775ce2241454923c401bfd4236",
    ),
    (
        "src::lil::_lil_t::field12@d0",
        "aeeae156107501ba3448c9b41f4d1a0e0e73e01ab89e8d7d49c7d74110103aa4",
    ),
    (
        "src::lil::_lil_t::field13@d0",
        "014f532cfe2452a5915038f06cca0b0498a4c3f09d8e2542e5bd7662d0946d6d",
    ),
    (
        "src::lil::_lil_t::field14@d0",
        "91908441e42079a1b285beeba3643f449a9ef7a797375c7127f7dfbd34693291",
    ),
    (
        "src::lil::_lil_t::field17@d0",
        "ffef0bd35f41d68ab1a5b5c631567d65a98cc4408cb777a9d865a4a9b41eb488",
    ),
    (
        "src::lil::_lil_t::field1@d0",
        "3171e05055e4bb4eff535426f07d8a9c6c62fc10a413bd0dcf514456af7d7a03",
    ),
    (
        "src::lil::_lil_t::field8@d0",
        "47228de7d4f258abd954b026a406c6e5dad43a822565ea255fa0f05ca180de8d",
    ),
    (
        "src::lil::_lil_var_t::field0@d0",
        "3ba326983ebe9d0d7a5f5680f2ed60a47ba429b01f533bd8257392478637d1ff",
    ),
    (
        "src::lil::_lil_var_t::field1@d0",
        "79c12c0bee945ea2ac565d5b7ebfafa6794cc16ff1ba250289e8c9766684804c",
    ),
];
const RESOURCE_EXHAUSTED_HEADER: &str =
    "program\tfield_key\tstatus\tmemory_max_bytes\tpeak_rss_kb\tcgroup_peak_memory_kb\tphase\tdata";
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
const RETRY3_PREDECESSOR_SHARDS: [(&str, &str, &str); 13] = [
    (
        "bst",
        "ce11b3459c6fa46965e4cbe23ce11dffbdc7bf01",
        "f9c23eddb3b9da283a2ebf82a4839f9f0e28c4d535f69923d38531ad397b90dd",
    ),
    (
        "avl",
        "ce11b3459c6fa46965e4cbe23ce11dffbdc7bf01",
        "fa50b850af80fa56893fbcd1c2c6c7b57df5107df2ba661b0452ef63a41bac82",
    ),
    (
        "ht",
        "ce11b3459c6fa46965e4cbe23ce11dffbdc7bf01",
        "01a6483456126ee0621cb133a009fae49edc768dda577ddb83c8d6ed27f4c72c",
    ),
    (
        "libcsv",
        "efd8e51df8f8ce5ba4edd2655f8b5b5bc9c0c6b8",
        "b56635fec4f001702a2cb84ba2d1af63f2c5bba2bb20db695c0d7cf6471459b3",
    ),
    (
        "buffer",
        "efd8e51df8f8ce5ba4edd2655f8b5b5bc9c0c6b8",
        "14c3c43e78d2e6818b2261e6e7738e7fe38065528a0c0ee4b6f639050f008286",
    ),
    (
        "quadtree",
        "efd8e51df8f8ce5ba4edd2655f8b5b5bc9c0c6b8",
        "fe04dddb4495ad0824bab4a2756aa829c4d12c1cab29b99e5a6de44641cadc4a",
    ),
    (
        "urlparser",
        "37b0fd5c043dcae653ff87ca343841cb6f45922a",
        "4a11d1081783ec4e4c79d57311c8e7affbd3324233b4ba9f83ee9cb3a9d7eec3",
    ),
    (
        "rgba",
        "37b0fd5c043dcae653ff87ca343841cb6f45922a",
        "4afdfffa3f05da0ff864be0fa283898200e3e0093ff38e35ee4e7763262d5419",
    ),
    (
        "genann",
        "37b0fd5c043dcae653ff87ca343841cb6f45922a",
        "822cebcc9f43707f57e5d87149fbf103884e95be2b6eb0f0152fb58b88c46b53",
    ),
    (
        "libtree",
        "1bd19c6a90082b87c82eb3bd35f5155db712fcf9",
        "f510473a443d12dd4c09964ed8290cc82e2255288a7ed9e3c96e48f080d7eb45",
    ),
    (
        "json.h",
        "bb8cead3695b42f5ef20a574000c51ba5dc5ebc6",
        "fcb2a562d385483ebf7f1b65841e38a3cf3609339cc216a6da6989954d4de693",
    ),
    (
        "binn",
        "93f0bdf4f2e361743e651abf3c1884e70a4d4b19",
        "b516c79fd1b65f6805a3767713e9331cc86024d80c9c4467546c831fbf8ac1bd",
    ),
    (
        "libzahl",
        "d07bf0ad177b46d60d0aba975d7b830b3bb3007f",
        "241ea04355b5a9f469d3d8f75d8ac70f98ff797bfb8e50e694fce13b90e8bd2a",
    ),
];

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
    parse_table_text(&input, header, columns, &path.display().to_string())
}

fn parse_table_text(
    input: &str,
    header: &str,
    columns: usize,
    label: &str,
) -> Result<Vec<Vec<String>>, String> {
    let mut lines = input.lines();
    if lines.next() != Some(header) {
        return Err(format!("header drift: {label}"));
    }
    lines
        .enumerate()
        .map(|(offset, line)| {
            let row = line.split('\t').map(str::to_owned).collect::<Vec<_>>();
            if row.len() != columns {
                return Err(format!(
                    "{label} line {} has {} columns, expected {columns}",
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
const CANDIDATE_READINGS_HEADER: &str = "program\tfield_key\tfield_slot\tordinary_kind\tclosed_world_class\topen_class\tclosed_world_evidence\topen_evidence\tclosed_world_root_count\topen_root_count";
const FULL_IDENTITY_HEADER: &str =
    "program\tfield_key\tfield_slot\tordinary_kind\tbaseline_force\tproof_reason";
const PUBLIC_SETTER_REACHABLE_TAG: &str = "public-setter-reachable";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CandidateMemoryPeaks {
    process_peak_rss_kb: u64,
    cgroup_peak_memory_kb: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CandidateMemoryReceipt {
    process_peak_rss_kb: Option<u64>,
    cgroup_peak_memory_kb: Option<u64>,
    errors: Vec<String>,
}

impl CandidateMemoryReceipt {
    fn require_complete(&self) -> Result<CandidateMemoryPeaks, String> {
        if !self.errors.is_empty() {
            return Err(self.errors.join("; "));
        }
        Ok(CandidateMemoryPeaks {
            process_peak_rss_kb: self
                .process_peak_rss_kb
                .ok_or_else(|| "GNU-time peak RSS is unavailable".to_owned())?,
            cgroup_peak_memory_kb: self
                .cgroup_peak_memory_kb
                .ok_or_else(|| "cgroup peak charged memory is unavailable".to_owned())?,
        })
    }

    fn render(&self) -> String {
        fn value(value: Option<u64>) -> String {
            value.map_or_else(|| "unavailable".to_owned(), |value| value.to_string())
        }
        format!(
            "peak_rss_kb={}\ncgroup_peak_memory_kb={}\n",
            value(self.process_peak_rss_kb),
            value(self.cgroup_peak_memory_kb),
        )
    }
}

impl From<CandidateMemoryPeaks> for CandidateMemoryReceipt {
    fn from(peaks: CandidateMemoryPeaks) -> Self {
        Self {
            process_peak_rss_kb: Some(peaks.process_peak_rss_kb),
            cgroup_peak_memory_kb: Some(peaks.cgroup_peak_memory_kb),
            errors: Vec::new(),
        }
    }
}

fn parse_gnu_time_peak_rss_kb(receipt: &str) -> Result<u64, String> {
    const PREFIX: &str = "Maximum resident set size (kbytes):";
    let mut values = receipt
        .lines()
        .filter_map(|line| line.trim().strip_prefix(PREFIX));
    let value = values
        .next()
        .ok_or_else(|| "GNU-time receipt is missing peak RSS".to_owned())?;
    if values.next().is_some() {
        return Err("GNU-time receipt has duplicate peak RSS entries".to_owned());
    }
    let value = value
        .trim()
        .parse::<u64>()
        .map_err(|error| format!("GNU-time peak RSS is not an integer: {error}"))?;
    if value == 0 {
        return Err("GNU-time peak RSS is zero".to_owned());
    }
    Ok(value)
}

fn collect_candidate_memory_receipt(
    gnu_time_receipt: Option<&str>,
    cgroup_peak_memory_bytes: Option<u64>,
) -> CandidateMemoryReceipt {
    let process_peak_rss = gnu_time_receipt
        .ok_or_else(|| "GNU-time receipt is unavailable".to_owned())
        .and_then(parse_gnu_time_peak_rss_kb);
    let cgroup_peak_memory = cgroup_peak_memory_bytes
        .filter(|peak| *peak > 0)
        .ok_or_else(|| "cgroup peak charged memory is unavailable".to_owned())
        .map(|bytes| bytes.div_ceil(1024));
    let errors = process_peak_rss
        .as_ref()
        .err()
        .into_iter()
        .chain(cgroup_peak_memory.as_ref().err())
        .cloned()
        .collect();
    CandidateMemoryReceipt {
        process_peak_rss_kb: process_peak_rss.ok(),
        cgroup_peak_memory_kb: cgroup_peak_memory.ok(),
        errors,
    }
}

fn render_candidate_memory_receipt(peaks: CandidateMemoryPeaks) -> String {
    CandidateMemoryReceipt::from(peaks).render()
}

fn classify_capped_candidate(
    cap_verified: bool,
    oom_kills: u64,
    memory_max_events: u64,
    worker_ok: bool,
) -> Result<&'static str, String> {
    if !cap_verified {
        return Err("candidate cgroup MemoryMax cap was not verified".to_owned());
    }
    if oom_kills > 0 && memory_max_events > 0 {
        return Ok("resource-exhausted");
    }
    if oom_kills > 0 {
        return Ok("environment-oom-kill");
    }
    Ok(if worker_ok { "ok" } else { "failed" })
}

fn render_resource_exhausted(
    program: &str,
    field_key: &str,
    memory_max_bytes: u64,
    peak_rss_kb: u64,
    cgroup_peak_memory_kb: u64,
    phase: &str,
) -> String {
    format!(
        "{RESOURCE_EXHAUSTED_HEADER}\n{}\t{}\tresource-exhausted\t{memory_max_bytes}\t{peak_rss_kb}\t{cgroup_peak_memory_kb}\t{}\tfalse\n",
        clean_cell(program),
        clean_cell(field_key),
        clean_cell(phase),
    )
}

fn validate_reusable_candidate_artifact(
    program: &str,
    field_key: &str,
    candidates: &str,
    roots: &str,
) -> Result<(), String> {
    let candidates = parse_table_text(candidates, CANDIDATE_HEADER, 7, "checkpoint candidates")?;
    if candidates.len() != 1 || candidates[0][0] != program || candidates[0][1] != field_key {
        return Err(format!(
            "checkpoint candidate identity mismatch: program={program} candidate={field_key} rows={candidates:?}"
        ));
    }
    let roots = parse_table_text(roots, ROOT_HEADER, 8, "checkpoint roots")?;
    let matching = roots
        .iter()
        .filter(|row| row[1] == program && row[2] == field_key)
        .count();
    let expected = candidates[0][6]
        .parse::<usize>()
        .map_err(|error| format!("checkpoint candidate root count: {error}"))?;
    if matching != expected || matching == 0 {
        return Err(format!(
            "checkpoint root inventory mismatch: program={program} candidate={field_key} expected={expected} actual={matching}"
        ));
    }
    Ok(())
}

fn validate_oracle_candidate_byte_match(
    oracle_partial: &str,
    actual_candidates: &str,
    program: &str,
    field_key: &str,
) -> Result<bool, String> {
    let marker = format!("{CANDIDATE_HEADER}\n");
    if oracle_partial.match_indices(&marker).count() != 1 {
        return Err("oracle partial must contain exactly one candidate header".to_owned());
    }
    let oracle_table = oracle_partial
        .split_once(&marker)
        .expect("exactly one oracle header")
        .1;
    let mut oracle_rows = oracle_table
        .lines()
        .take_while(|line| !line.is_empty())
        .filter(|line| {
            let mut columns = line.split('\t');
            columns.next() == Some(program) && columns.next() == Some(field_key)
        });
    let Some(oracle_row) = oracle_rows.next() else {
        return Ok(false);
    };
    if oracle_rows.next().is_some() {
        return Err(format!(
            "oracle duplicates candidate: program={program} candidate={field_key}"
        ));
    }

    let actual = parse_table_text(
        actual_candidates,
        CANDIDATE_HEADER,
        7,
        "isolated oracle candidate",
    )?;
    if actual.len() != 1 || actual[0][0] != program || actual[0][1] != field_key {
        return Err(format!(
            "isolated oracle identity mismatch: program={program} candidate={field_key} rows={actual:?}"
        ));
    }
    let actual_row = actual_candidates
        .lines()
        .nth(1)
        .ok_or_else(|| "isolated oracle candidate row is missing".to_owned())?;
    if actual_row != oracle_row {
        return Err(format!(
            "candidate summary byte mismatch: program={program} candidate={field_key}"
        ));
    }
    Ok(true)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DualReading {
    closed_world_class: PrimaryClass,
    open_class: PrimaryClass,
    closed_world_evidence: RootEvidence,
    open_evidence: RootEvidence,
    closed_world_root_count: usize,
    open_root_count: usize,
}

fn union_evidence(roots: &[RootEvidence]) -> RootEvidence {
    RootEvidence {
        flags: roots
            .iter()
            .flat_map(|root| root.flags.iter().copied())
            .collect(),
        provenance_tags: roots
            .iter()
            .flat_map(|root| root.provenance_tags.iter().cloned())
            .collect(),
    }
}

fn dual_reading(roots: &[RootEvidence]) -> Result<DualReading, String> {
    let closed_world_roots = roots
        .iter()
        .filter(|root| !root.provenance_tags.contains(PUBLIC_SETTER_REACHABLE_TAG))
        .cloned()
        .collect::<Vec<_>>();
    let closed_world_class = classify_roots(&closed_world_roots);
    let open_class = classify_roots(roots);
    if closed_world_class == PrimaryClass::Unresolved {
        return Err("closed-world reading has no classified visible root".to_owned());
    }
    if open_class == PrimaryClass::Unresolved {
        return Err("open reading contains an unclassified root".to_owned());
    }
    Ok(DualReading {
        closed_world_class,
        open_class,
        closed_world_evidence: union_evidence(&closed_world_roots),
        open_evidence: union_evidence(roots),
        closed_world_root_count: closed_world_roots.len(),
        open_root_count: roots.len(),
    })
}

fn render_candidate_readings(
    candidates: &[Vec<String>],
    roots: &[Vec<String>],
) -> Result<String, String> {
    let mut root_evidence = BTreeMap::<(String, String), Vec<RootEvidence>>::new();
    for row in roots.iter().filter(|row| row[0] == "census") {
        root_evidence
            .entry((row[1].clone(), row[2].clone()))
            .or_default()
            .push(parse_root_evidence(&row[6])?);
    }
    let mut rendered = format!("{CANDIDATE_READINGS_HEADER}\n");
    for row in candidates {
        let identity = (row[0].clone(), row[1].clone());
        let roots = root_evidence
            .get(&identity)
            .ok_or_else(|| format!("candidate reading lacks roots: {} {}", row[0], row[1]))?;
        let reading = dual_reading(roots)?;
        let open_evidence = evidence_tokens(&reading.open_evidence).join("|");
        if class_label(reading.open_class) != row[4]
            || open_evidence != row[5]
            || reading.open_root_count.to_string() != row[6]
        {
            return Err(format!(
                "open reading does not reproduce manifested candidate row: {} {}",
                row[0], row[1]
            ));
        }
        rendered.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            row[0],
            row[1],
            row[2],
            row[3],
            class_label(reading.closed_world_class),
            class_label(reading.open_class),
            evidence_tokens(&reading.closed_world_evidence).join("|"),
            open_evidence,
            reading.closed_world_root_count,
            reading.open_root_count,
        ));
    }
    Ok(rendered)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct StreamingEvidenceSummary {
    evidence: RootEvidence,
    has_unclassified: bool,
    count: usize,
}

impl Default for StreamingEvidenceSummary {
    fn default() -> Self {
        Self {
            evidence: RootEvidence {
                flags: BTreeSet::new(),
                provenance_tags: BTreeSet::new(),
            },
            has_unclassified: false,
            count: 0,
        }
    }
}

impl StreamingEvidenceSummary {
    fn add(&mut self, evidence: &RootEvidence) {
        self.has_unclassified |= evidence.flags.is_empty();
        self.evidence.flags.extend(evidence.flags.iter().copied());
        self.evidence
            .provenance_tags
            .extend(evidence.provenance_tags.iter().cloned());
        self.count += 1;
    }

    fn class(&self) -> PrimaryClass {
        if self.count == 0 || self.has_unclassified {
            PrimaryClass::Unresolved
        } else {
            classify_roots(std::slice::from_ref(&self.evidence))
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct StreamingIdentitySummary {
    population: String,
    open: StreamingEvidenceSummary,
    closed: StreamingEvidenceSummary,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct StreamingRootSummary {
    row_count: usize,
    identities: BTreeMap<(String, String), StreamingIdentitySummary>,
    program_counts: BTreeMap<String, usize>,
    flag_witnesses: BTreeMap<String, String>,
    provenance_tag_witnesses: BTreeMap<String, String>,
}

fn strip_table_line_ending(line: &mut String) {
    if line.ends_with('\n') {
        line.pop();
    }
    if line.ends_with('\r') {
        line.pop();
    }
}

fn scan_root_table<R: BufRead>(mut reader: R, label: &str) -> Result<StreamingRootSummary, String> {
    let mut line = String::new();
    reader
        .read_line(&mut line)
        .map_err(|error| format!("read {label} header: {error}"))?;
    strip_table_line_ending(&mut line);
    if line != ROOT_HEADER {
        return Err(format!("header drift: {label}"));
    }

    let mut summary = StreamingRootSummary::default();
    let mut previous_row = None::<String>;
    loop {
        line.clear();
        if reader
            .read_line(&mut line)
            .map_err(|error| format!("read {label} row: {error}"))?
            == 0
        {
            break;
        }
        strip_table_line_ending(&mut line);
        // trace_candidate emits canonical BTreeMap order, so exact duplicates are adjacent.
        if previous_row.as_deref() == Some(line.as_str()) {
            return Err(format!("duplicate adjacent root row in {label}"));
        }
        let columns = line.split('\t').collect::<Vec<_>>();
        if columns.len() != 8 {
            return Err(format!(
                "{label} line {} has {} columns, expected 8",
                summary.row_count + 2,
                columns.len()
            ));
        }
        if !matches!(columns[0], "census" | "exception") {
            return Err(format!("unknown root population {:?}", columns[0]));
        }
        if columns[1].is_empty() || columns[2].is_empty() {
            return Err(format!("root lacks program/candidate in {label}"));
        }
        if columns[3].is_empty() || columns[7].is_empty() {
            return Err(format!(
                "root lacks store/path at {}: {}",
                columns[2], columns[4]
            ));
        }
        if columns[6].is_empty() {
            return Err(format!(
                "root lacks cause flag at {}: {}",
                columns[2], columns[4]
            ));
        }
        let evidence = parse_root_evidence(columns[6])?;
        let identity = (columns[1].to_owned(), columns[2].to_owned());
        let entry = summary
            .identities
            .entry(identity.clone())
            .or_insert_with(|| StreamingIdentitySummary {
                population: columns[0].to_owned(),
                open: StreamingEvidenceSummary::default(),
                closed: StreamingEvidenceSummary::default(),
            });
        if entry.population != columns[0] {
            return Err(format!(
                "root identity crosses populations: {} {}",
                columns[1], columns[2]
            ));
        }
        entry.open.add(&evidence);
        if !evidence
            .provenance_tags
            .contains(PUBLIC_SETTER_REACHABLE_TAG)
        {
            entry.closed.add(&evidence);
        }
        *summary
            .program_counts
            .entry(columns[1].to_owned())
            .or_default() += 1;
        let witness = || {
            format!(
                "{}::{} store={} root={} path={}",
                columns[1], columns[2], columns[3], columns[4], columns[7]
            )
        };
        for flag in &evidence.flags {
            summary
                .flag_witnesses
                .entry(flag_label(*flag).to_owned())
                .or_insert_with(&witness);
        }
        for tag in &evidence.provenance_tags {
            summary
                .provenance_tag_witnesses
                .entry(tag.clone())
                .or_insert_with(&witness);
        }
        summary.row_count += 1;
        previous_row = Some(line.clone());
    }
    Ok(summary)
}

fn scan_root_path(path: &Path) -> Result<StreamingRootSummary, String> {
    let file = fs::File::open(path)
        .map_err(|error| format!("open root table {}: {error}", path.display()))?;
    scan_root_table(BufReader::new(file), &path.display().to_string())
}

fn validate_isolated_root_summary(
    summary: &StreamingRootSummary,
    population: &str,
    program: &str,
    field_key: &str,
    reported: usize,
) -> Result<(), String> {
    let expected_identity = (program.to_owned(), field_key.to_owned());
    let Some(identity) = summary.identities.get(&expected_identity) else {
        return Err(format!(
            "isolated root identity mismatch: {program} {field_key}"
        ));
    };
    if summary.identities.len() != 1 || identity.population != population {
        return Err(format!(
            "isolated root identity mismatch: {program} {field_key} population={population}"
        ));
    }
    if summary.row_count != reported || reported == 0 {
        return Err(format!(
            "isolated root count mismatch: {program} {field_key} expected={reported} actual={}",
            summary.row_count
        ));
    }
    Ok(())
}

fn dual_reading_from_summary(summary: &StreamingIdentitySummary) -> Result<DualReading, String> {
    let closed_world_class = summary.closed.class();
    let open_class = summary.open.class();
    if closed_world_class == PrimaryClass::Unresolved {
        return Err("closed-world reading has no classified visible root".to_owned());
    }
    if open_class == PrimaryClass::Unresolved {
        return Err("open reading contains an unclassified root".to_owned());
    }
    Ok(DualReading {
        closed_world_class,
        open_class,
        closed_world_evidence: summary.closed.evidence.clone(),
        open_evidence: summary.open.evidence.clone(),
        closed_world_root_count: summary.closed.count,
        open_root_count: summary.open.count,
    })
}

fn render_candidate_readings_from_summary(
    candidates: &[Vec<String>],
    roots: &StreamingRootSummary,
) -> Result<String, String> {
    let mut rendered = format!("{CANDIDATE_READINGS_HEADER}\n");
    for row in candidates {
        let identity = (row[0].clone(), row[1].clone());
        let roots = roots
            .identities
            .get(&identity)
            .filter(|summary| summary.population == "census")
            .ok_or_else(|| format!("candidate reading lacks roots: {} {}", row[0], row[1]))?;
        let reading = dual_reading_from_summary(roots)?;
        let open_evidence = evidence_tokens(&reading.open_evidence).join("|");
        if class_label(reading.open_class) != row[4]
            || open_evidence != row[5]
            || reading.open_root_count.to_string() != row[6]
        {
            return Err(format!(
                "open reading does not reproduce manifested candidate row: {} {}",
                row[0], row[1]
            ));
        }
        rendered.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            row[0],
            row[1],
            row[2],
            row[3],
            class_label(reading.closed_world_class),
            class_label(reading.open_class),
            evidence_tokens(&reading.closed_world_evidence).join("|"),
            open_evidence,
            reading.closed_world_root_count,
            reading.open_root_count,
        ));
    }
    Ok(rendered)
}

fn append_table_streaming<R: BufRead, W: Write>(
    mut reader: R,
    writer: &mut W,
    expected_header: &str,
    write_header: bool,
) -> Result<(), String> {
    let mut line = String::new();
    reader
        .read_line(&mut line)
        .map_err(|error| format!("read streaming table header: {error}"))?;
    strip_table_line_ending(&mut line);
    if line != expected_header {
        return Err("streaming table header drift".to_owned());
    }
    if write_header {
        writeln!(writer, "{expected_header}")
            .map_err(|error| format!("write streaming table header: {error}"))?;
    }
    loop {
        line.clear();
        if reader
            .read_line(&mut line)
            .map_err(|error| format!("read streaming table row: {error}"))?
            == 0
        {
            break;
        }
        strip_table_line_ending(&mut line);
        writeln!(writer, "{line}")
            .map_err(|error| format!("write streaming table row: {error}"))?;
    }
    Ok(())
}

fn render_full_identity(input: &[A4InputRow]) -> Result<String, String> {
    let expected_counts = BTreeMap::from([
        ("allocation-source-count-0", 237usize),
        ("competing-live-use", 13),
        ("ownership-erasing-cast", 6),
        ("realloc-origin", 1),
        ("baseline-force-sat-exception", 4),
    ]);
    let mut actual_counts = BTreeMap::<&str, usize>::new();
    let mut identities = BTreeSet::new();
    let mut rendered = format!("{FULL_IDENTITY_HEADER}\n");
    for row in input {
        if !identities.insert((row.program.as_str(), row.field_key.as_str())) {
            return Err(format!(
                "duplicate full identity: {} {}",
                row.program, row.field_key
            ));
        }
        *actual_counts.entry(row.proof_reason.as_str()).or_default() += 1;
        rendered.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\n",
            row.program,
            row.field_key,
            row.field_slot,
            kind_label(row.baseline_kind),
            row.baseline_force,
            row.proof_reason,
        ));
    }
    if input.len() != 261 || actual_counts != expected_counts {
        return Err(format!(
            "full identity partition drift: rows={} counts={actual_counts:?}",
            input.len()
        ));
    }
    Ok(rendered)
}

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
    manifest: &str,
) -> Result<(), String> {
    for (key, expected) in [
        ("status", "ok"),
        ("data", "true"),
        ("checkpoint_data", "false"),
        ("machine_id", MACHINE_ID),
        ("platform", PLATFORM),
        ("wall_cap_s", "14400"),
    ] {
        let actual = receipt.get(key).map(String::as_str);
        if actual != Some(expected) {
            return Err(format!(
                "receipt {key}: expected {expected:?}, got {actual:?}"
            ));
        }
    }
    let receipt_head = receipt
        .get("analysis_head")
        .ok_or_else(|| "receipt lacks analysis_head".to_owned())?;
    validate_receipt_head(program, receipt_head, manifest, &contract.head)?;
    let expected_memory_limit = if receipt_head == &contract.head {
        "cgroup-100GiB"
    } else {
        "uncapped"
    };
    if receipt.get("memory_limit").map(String::as_str) != Some(expected_memory_limit) {
        return Err(format!(
            "receipt memory_limit: expected {expected_memory_limit:?}, got {:?}",
            receipt.get("memory_limit")
        ));
    }
    if receipt_head == &contract.head
        && (receipt.get("memory_max_bytes").map(String::as_str) != Some("107374182400")
            || receipt.get("candidate_isolation").map(String::as_str) != Some("true"))
    {
        return Err("current-head receipt lacks candidate-isolation/cgroup contract".to_owned());
    }
    if receipt_head == &contract.head {
        for key in ["peak_rss_kb", "cgroup_peak_memory_kb"] {
            let value = receipt
                .get(key)
                .ok_or_else(|| format!("current-head receipt lacks {key}"))?
                .parse::<u64>()
                .map_err(|error| format!("current-head receipt {key} is invalid: {error}"))?;
            if value == 0 {
                return Err(format!("current-head receipt {key} is zero"));
            }
        }
        let expected_oracle_matches = (usize::from(program == "lil") * 19).to_string();
        if receipt.get("oracle_partial_sha256").map(String::as_str)
            != Some(LIL_ORACLE_PARTIAL_SHA256)
            || receipt.get("oracle_byte_matches").map(String::as_str)
                != Some(expected_oracle_matches.as_str())
            || receipt.get("oracle_expected_matches").map(String::as_str)
                != Some(expected_oracle_matches.as_str())
        {
            return Err(format!(
                "current-head receipt oracle contract drift: program={program}"
            ));
        }
    }
    for (key, expected) in [
        ("program", program),
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

fn validate_receipt_head(
    program: &str,
    receipt_head: &str,
    manifest: &str,
    current_head: &str,
) -> Result<(), String> {
    if receipt_head == current_head {
        return Ok(());
    }
    if RETRY3_PREDECESSOR_SHARDS
        .iter()
        .any(|(allowed_program, allowed_head, allowed_manifest)| {
            program == *allowed_program
                && receipt_head == *allowed_head
                && manifest == *allowed_manifest
        })
    {
        return Ok(());
    }
    Err(format!(
        "receipt analysis_head/manifest is not an approved verified-skip tuple: program={program} head={receipt_head} manifest={manifest} current={current_head}"
    ))
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

#[derive(Debug)]
struct CappedCandidateOutcome {
    status: String,
    wall_s: f64,
    memory_receipt: CandidateMemoryReceipt,
    memory_receipt_error: Option<String>,
    stderr: String,
    cap_verified: bool,
    oom_kills: u64,
    memory_max_events: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct HostMemoryPreflight {
    mem_available_bytes: Option<u64>,
    required_bytes: u64,
    status: &'static str,
    error: Option<String>,
}

impl HostMemoryPreflight {
    fn launch_allowed(&self) -> bool {
        self.status == "ready"
    }

    fn render(&self, program: &str, candidate: &str, timestamp_unix_s: u64) -> String {
        let available = self.mem_available_bytes.map_or_else(
            || "unavailable".to_owned(),
            |available| available.to_string(),
        );
        format!(
            "machine_id={MACHINE_ID}\nplatform={PLATFORM}\ntimestamp_unix_s={timestamp_unix_s}\nprogram={}\ncandidate={}\nstatus={}\nmeasurement_started=false\nmemory_max_bytes={CANDIDATE_MEMORY_MAX_BYTES}\nmargin_bytes={HOST_MEMORY_MARGIN_BYTES}\nrequired_bytes={}\nmem_available_bytes={available}\nerror={}\n",
            clean_cell(program),
            clean_cell(candidate),
            self.status,
            self.required_bytes,
            clean_cell(self.error.as_deref().unwrap_or("none")),
        )
    }
}

fn evaluate_host_memory_preflight(meminfo: &str) -> HostMemoryPreflight {
    let required_bytes = CANDIDATE_MEMORY_MAX_BYTES + HOST_MEMORY_MARGIN_BYTES;
    let mut values = meminfo.lines().filter_map(|line| {
        line.strip_prefix("MemAvailable:")
            .map(|value| value.trim().to_owned())
    });
    let parsed = match (values.next(), values.next()) {
        (None, _) => Err("/proc/meminfo lacks MemAvailable".to_owned()),
        (Some(_), Some(_)) => Err("/proc/meminfo duplicates MemAvailable".to_owned()),
        (Some(value), None) => {
            let mut fields = value.split_whitespace();
            let kib = fields
                .next()
                .ok_or_else(|| "MemAvailable has no value".to_owned())
                .and_then(|value| {
                    value
                        .parse::<u64>()
                        .map_err(|error| format!("MemAvailable is not an integer: {error}"))
                });
            match (kib, fields.next(), fields.next()) {
                (Ok(kib), Some("kB"), None) => kib
                    .checked_mul(1024)
                    .ok_or_else(|| "MemAvailable overflows bytes".to_owned()),
                (Err(error), _, _) => Err(error),
                _ => Err("MemAvailable must have exactly a kB value".to_owned()),
            }
        }
    };
    match parsed {
        Ok(available) if available > required_bytes => HostMemoryPreflight {
            mem_available_bytes: Some(available),
            required_bytes,
            status: "ready",
            error: None,
        },
        Ok(available) => HostMemoryPreflight {
            mem_available_bytes: Some(available),
            required_bytes,
            status: "host-memory-insufficient",
            error: Some("MemAvailable is not strictly greater than cap plus margin".to_owned()),
        },
        Err(error) => HostMemoryPreflight {
            mem_available_bytes: None,
            required_bytes,
            status: "host-memory-unavailable",
            error: Some(error),
        },
    }
}

fn candidate_systemd_properties(memory_max_bytes: u64) -> Vec<String> {
    vec![
        "Type=exec".to_owned(),
        "MemoryAccounting=yes".to_owned(),
        format!("MemoryMax={memory_max_bytes}"),
        "OOMPolicy=continue".to_owned(),
    ]
}

fn resume9_lil_unit_is_authorized(index: usize, field_key: &str, manifest: &str) -> bool {
    LIL_RESUME9_UNITS
        .get(index)
        .is_some_and(|(expected_field, expected_manifest)| {
            field_key == *expected_field && manifest == *expected_manifest
        })
}

static CANDIDATE_UNIT_SEQUENCE: AtomicU64 = AtomicU64::new(0);

fn systemd_user_property(unit: &str, property: &str) -> Option<String> {
    let output = Command::new("systemctl")
        .args(["--user", "show", unit, "--property", property, "--value"])
        .output()
        .ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn read_u64_file(path: &Path) -> Option<u64> {
    fs::read_to_string(path).ok()?.trim().parse().ok()
}

fn read_memory_event(path: &Path, key: &str) -> Option<u64> {
    fs::read_to_string(path)
        .ok()?
        .lines()
        .find_map(|line| line.split_once(' ').filter(|(name, _)| *name == key))?
        .1
        .parse()
        .ok()
}

fn kill_systemd_unit(unit: &str) {
    let _ = Command::new("systemctl")
        .args(["--user", "kill", "--kill-whom=all", "--signal=KILL", unit])
        .status();
}

fn run_capped_candidate_child(
    program: &str,
    input: &Path,
    unit_dir: &Path,
    extra: &[(&str, String)],
) -> CappedCandidateOutcome {
    use super::orchestrate::workspace_root;

    let sequence = CANDIDATE_UNIT_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let unit = format!("crat-a4-{}-{sequence}.service", std::process::id());
    let out_path = unit_dir.join("worker.out");
    let err_path = unit_dir.join("worker.err");
    let time_path = unit_dir.join("time.txt");
    let out_file = fs::File::create(&out_path).expect("create candidate worker stdout");
    let err_file = fs::File::create(&err_path).expect("create candidate worker stderr");
    let exe = std::env::current_exe().expect("current test executable");

    let mut environment = std::env::vars_os().collect::<BTreeMap<OsString, OsString>>();
    for (key, value) in [
        ("CRAT_BOC1_INPUT", input.display().to_string()),
        ("CRAT_BOC1_MODE", "a4-source-census".to_owned()),
        ("CRAT_BOC1_NAME", program.to_owned()),
        ("DIR", workspace_root().display().to_string()),
    ]
    .into_iter()
    .chain(extra.iter().map(|(key, value)| (*key, value.clone())))
    {
        environment.insert(OsString::from(key), OsString::from(value));
    }

    let mut command = Command::new("systemd-run");
    command.args([
        "--user",
        "--wait",
        "--pipe",
        "--quiet",
        "--same-dir",
        "--unit",
        &unit,
    ]);
    for property in candidate_systemd_properties(CANDIDATE_MEMORY_MAX_BYTES) {
        command.arg("--property").arg(property);
    }
    for (key, value) in environment {
        let mut assignment = key;
        assignment.push("=");
        assignment.push(value);
        command.arg("--setenv").arg(assignment);
    }
    command
        .arg("/usr/bin/time")
        .args(["--verbose", "--output"])
        .arg(&time_path)
        .arg(exe)
        .args(["bo_c1::boc1_run_one", "--exact", "--ignored", "--nocapture"])
        .stdin(Stdio::null())
        .stdout(Stdio::from(out_file))
        .stderr(Stdio::from(err_file));

    let started = Instant::now();
    let mut child = command.spawn().expect("spawn capped candidate worker");
    let mut cgroup_path = None;
    let mut cap_verified = false;
    let mut peak_bytes = 0;
    let mut oom_kills = 0;
    let mut memory_max_events = 0;
    let mut timed_out = false;
    let status = loop {
        if cgroup_path.is_none()
            && let Some(control_group) = systemd_user_property(&unit, "ControlGroup")
            && !control_group.is_empty()
        {
            cgroup_path = Some(
                PathBuf::from("/sys/fs/cgroup").join(
                    control_group
                        .strip_prefix('/')
                        .unwrap_or(control_group.as_str()),
                ),
            );
        }
        if let Some(cgroup) = &cgroup_path {
            if read_u64_file(&cgroup.join("memory.max")) == Some(CANDIDATE_MEMORY_MAX_BYTES) {
                cap_verified = true;
            }
            peak_bytes = peak_bytes.max(read_u64_file(&cgroup.join("memory.peak")).unwrap_or(0));
            let events = cgroup.join("memory.events");
            oom_kills = oom_kills.max(read_memory_event(&events, "oom_kill").unwrap_or(0));
            memory_max_events =
                memory_max_events.max(read_memory_event(&events, "max").unwrap_or(0));
        }
        match child.try_wait().expect("poll capped candidate worker") {
            Some(status) => break status,
            None if started.elapsed() >= Duration::from_secs(LIVENESS_BOUND_S) => {
                timed_out = true;
                kill_systemd_unit(&unit);
                let _ = child.kill();
            }
            None => std::thread::sleep(Duration::from_millis(100)),
        }
    };
    if systemd_user_property(&unit, "Result").as_deref() == Some("oom-kill") {
        oom_kills = oom_kills.max(1);
    }
    peak_bytes = peak_bytes.max(
        systemd_user_property(&unit, "MemoryPeak")
            .and_then(|value| value.parse().ok())
            .unwrap_or(0),
    );
    let wall_s = started.elapsed().as_secs_f64();
    let stdout = fs::read_to_string(&out_path).unwrap_or_default();
    let stderr = fs::read_to_string(&err_path).unwrap_or_default();
    let gnu_time_receipt = fs::read_to_string(&time_path).ok();
    let memory_receipt = collect_candidate_memory_receipt(
        gnu_time_receipt.as_deref(),
        (peak_bytes > 0).then_some(peak_bytes),
    );
    let memory_receipt_error = memory_receipt.require_complete().err();
    let row = stdout.lines().rev().find_map(super::report::parse_kv_line);
    let worker_ok = status.success()
        && row
            .as_ref()
            .and_then(|row| row.get("status"))
            .is_some_and(|status| status == "ok");
    let classification = if timed_out {
        "timeout".to_owned()
    } else {
        match classify_capped_candidate(cap_verified, oom_kills, memory_max_events, worker_ok) {
            Ok("failed") => row
                .as_ref()
                .and_then(|row| row.get("status"))
                .unwrap_or(if status.success() {
                    "no-output"
                } else {
                    "crash"
                })
                .to_owned(),
            Ok("ok") if memory_receipt_error.is_some() => "metric-receipt-failure".to_owned(),
            Ok(status) => status.to_owned(),
            Err(_) => "cap-setup-failure".to_owned(),
        }
    };
    CappedCandidateOutcome {
        status: classification,
        wall_s,
        memory_receipt,
        memory_receipt_error,
        stderr,
        cap_verified,
        oom_kills,
        memory_max_events,
    }
}

struct MeasurementContract {
    run_root: PathBuf,
    input_root: PathBuf,
    input_path: PathBuf,
    input: Vec<A4InputRow>,
    programs: Vec<super::CorpusProgram>,
    head: String,
    lil_oracle_partial: String,
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
    let oracle_path = PathBuf::from(
        std::env::var_os("CRAT_A4_SOURCE_ORACLE_PARTIAL").expect("CRAT_A4_SOURCE_ORACLE_PARTIAL"),
    );
    assert!(oracle_path.is_absolute());
    assert_eq!(sha256(&oracle_path), LIL_ORACLE_PARTIAL_SHA256);
    let lil_oracle_partial = fs::read_to_string(&oracle_path).expect("read lil summary oracle");
    let marker = format!("{CANDIDATE_HEADER}\n");
    let oracle_rows = lil_oracle_partial
        .split_once(&marker)
        .expect("lil oracle candidate header")
        .1
        .lines()
        .take_while(|line| !line.is_empty())
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .collect::<Vec<_>>();
    assert_eq!(oracle_rows.len(), 19);
    let expected_lil = expected_identities_from_input(&input, "lil", true)
        .into_iter()
        .map(|identity| identity.field_key)
        .collect::<BTreeSet<_>>();
    let oracle_lil = oracle_rows
        .iter()
        .map(|row| {
            assert_eq!(row.len(), 7);
            assert_eq!(row[0], "lil");
            row[1].to_owned()
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(oracle_lil.len(), 19);
    assert!(oracle_lil.is_subset(&expected_lil));
    assert_eq!(
        expected_lil
            .difference(&oracle_lil)
            .map(String::as_str)
            .collect::<Vec<_>>(),
        vec!["src::lil::_lil_var_t::field2@d0"]
    );
    MeasurementContract {
        run_root,
        input_root,
        input_path,
        input,
        programs,
        head,
        lil_oracle_partial,
    }
}

fn expected_identities_from_input(
    input: &[A4InputRow],
    program: &str,
    census: bool,
) -> Vec<Identity> {
    input
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

fn expected_identities(
    contract: &MeasurementContract,
    program: &str,
    census: bool,
) -> Vec<Identity> {
    expected_identities_from_input(&contract.input, program, census)
}

fn validate_unique_root_rows(roots: &[Vec<String>]) -> Result<(), String> {
    let mut seen = BTreeSet::new();
    for row in roots {
        let identity = (
            row[0].clone(),
            row[1].clone(),
            row[2].clone(),
            row[3].clone(),
            row[4].clone(),
            row[7].clone(),
        );
        if !seen.insert(identity) {
            return Err(format!(
                "duplicate root-path identity at {} {} path={}",
                row[2], row[4], row[7]
            ));
        }
    }
    Ok(())
}

fn validate_shard(contract: &MeasurementContract, program: &str, dir: &Path) -> Result<(), String> {
    let candidates = parse_table(&dir.join("candidates.tsv"), CANDIDATE_HEADER, 7)?;
    let roots = scan_root_path(&dir.join("roots.tsv"))?;
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
    for ((root_program, field_key), root) in &roots.identities {
        let identity = Identity {
            program: root_program.clone(),
            field_key: field_key.clone(),
        };
        let expected = match root.population.as_str() {
            "census" => &candidate_id_set,
            "exception" => &exception_id_set,
            other => return Err(format!("unknown root population {other:?}")),
        };
        if !expected.contains(&identity) {
            return Err(format!(
                "root outside {0} identity: {1} {2}",
                root.population, identity.program, identity.field_key
            ));
        }
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
        let evidence = roots
            .identities
            .get(&(row[0].clone(), row[1].clone()))
            .filter(|summary| summary.population == "census")
            .ok_or_else(|| format!("candidate root inventory missing: {}", row[1]))?;
        if evidence.open.count != reported {
            return Err(format!("candidate root inventory drift: {}", row[1]));
        }
        if class_label(evidence.open.class()) != row[4] {
            return Err(format!("candidate primary class drift: {}", row[1]));
        }
        let flags = evidence_tokens(&evidence.open.evidence).join("|");
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
        let evidence = roots
            .identities
            .get(&(row[0].clone(), row[1].clone()))
            .filter(|summary| summary.population == "exception")
            .ok_or_else(|| format!("exception root inventory missing: {}", row[1]))?;
        if reported == 0 || evidence.open.count != reported {
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
        let flags = &evidence.open.evidence.flags;
        let rendered_flags = evidence_tokens(&evidence.open.evidence).join("|");
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
        ("roots", scan_root_path(&dir.join("roots.tsv"))?.row_count),
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

#[derive(Clone, Debug, PartialEq, Eq)]
struct IsolatedIdentity {
    identity: Identity,
    population: &'static str,
}

fn isolated_identities(contract: &MeasurementContract, program: &str) -> Vec<IsolatedIdentity> {
    expected_identities(contract, program, true)
        .into_iter()
        .map(|identity| IsolatedIdentity {
            identity,
            population: "census",
        })
        .chain(
            expected_identities(contract, program, false)
                .into_iter()
                .map(|identity| IsolatedIdentity {
                    identity,
                    population: "exception",
                }),
        )
        .collect()
}

fn validate_isolated_unit(
    contract: &MeasurementContract,
    index: usize,
    expected: &IsolatedIdentity,
    dir: &Path,
    manifest: &str,
) -> Result<(), String> {
    let candidates = parse_table(&dir.join("candidates.tsv"), CANDIDATE_HEADER, 7)?;
    let roots = scan_root_path(&dir.join("roots.tsv"))?;
    let exceptions = parse_table(&dir.join("exceptions.tsv"), EXCEPTION_HEADER, 28)?;
    let expected_candidate_count = usize::from(expected.population == "census");
    let expected_exception_count = usize::from(expected.population == "exception");
    if candidates.len() != expected_candidate_count || exceptions.len() != expected_exception_count
    {
        return Err(format!(
            "isolated population count mismatch for {}: population={} candidates={} exceptions={}",
            expected.identity.field_key,
            expected.population,
            candidates.len(),
            exceptions.len()
        ));
    }
    let identity_row = candidates
        .first()
        .or_else(|| exceptions.first())
        .ok_or_else(|| {
            format!(
                "isolated unit has no semantic row: {}",
                expected.identity.field_key
            )
        })?;
    if identity_row[0] != expected.identity.program
        || identity_row[1] != expected.identity.field_key
    {
        return Err(format!(
            "isolated semantic identity mismatch: expected={:?} row={identity_row:?}",
            expected.identity
        ));
    }
    let reported = if expected.population == "census" {
        identity_row[6].parse::<usize>()
    } else {
        identity_row[21].parse::<usize>()
    }
    .map_err(|error| format!("isolated root count: {error}"))?;
    validate_isolated_root_summary(
        &roots,
        expected.population,
        &expected.identity.program,
        &expected.identity.field_key,
        reported,
    )?;
    let receipt = parse_receipt(&dir.join("receipt.txt"))?;
    let receipt_head = receipt
        .get("analysis_head")
        .ok_or_else(|| "isolated receipt lacks analysis_head".to_owned())?;
    let current_head = receipt_head == &contract.head;
    let resume9_unit = receipt_head == LIL_RESUME9_HEAD
        && expected.identity.program == "lil"
        && resume9_lil_unit_is_authorized(index, &expected.identity.field_key, manifest);
    if !current_head && !resume9_unit {
        return Err(format!(
            "isolated receipt head is not authorized for index={index} candidate={} manifest={manifest}",
            expected.identity.field_key
        ));
    }
    for (key, value) in [
        ("status", "ok"),
        ("data", "true"),
        ("checkpoint_data", "false"),
        ("program", expected.identity.program.as_str()),
        ("candidate", expected.identity.field_key.as_str()),
        ("population", expected.population),
        ("memory_limit", "cgroup-100GiB"),
        ("memory_max_bytes", "107374182400"),
        ("cap_verified", "true"),
    ] {
        if receipt.get(key).map(String::as_str) != Some(value) {
            return Err(format!(
                "isolated receipt {key} mismatch for {}",
                expected.identity.field_key
            ));
        }
    }
    for key in ["peak_rss_kb", "cgroup_peak_memory_kb"] {
        let value = receipt
            .get(key)
            .ok_or_else(|| format!("isolated receipt lacks {key}"))?
            .parse::<u64>()
            .map_err(|error| format!("isolated receipt {key} is invalid: {error}"))?;
        if value == 0 {
            return Err(format!("isolated receipt {key} is zero"));
        }
    }
    if current_head {
        let preflight = parse_receipt(&dir.join("memory-preflight.txt"))?;
        for (key, expected_value) in [
            ("status", "ready"),
            ("measurement_started", "false"),
            ("machine_id", MACHINE_ID),
            ("platform", PLATFORM),
            ("program", expected.identity.program.as_str()),
            ("candidate", expected.identity.field_key.as_str()),
            ("memory_max_bytes", "107374182400"),
            ("margin_bytes", "8589934592"),
            ("required_bytes", "115964116992"),
        ] {
            if preflight.get(key).map(String::as_str) != Some(expected_value) {
                return Err(format!(
                    "isolated memory preflight {key} mismatch for {}",
                    expected.identity.field_key
                ));
            }
        }
    }
    let candidates_text = fs::read_to_string(dir.join("candidates.tsv"))
        .map_err(|error| format!("read isolated oracle candidate: {error}"))?;
    let oracle_byte_match = validate_oracle_candidate_byte_match(
        &contract.lil_oracle_partial,
        &candidates_text,
        &expected.identity.program,
        &expected.identity.field_key,
    )?;
    let expected_oracle_label = if oracle_byte_match {
        "true"
    } else {
        "not-applicable"
    };
    if receipt.get("oracle_byte_match").map(String::as_str) != Some(expected_oracle_label)
        || receipt.get("oracle_partial_sha256").map(String::as_str)
            != Some(LIL_ORACLE_PARTIAL_SHA256)
    {
        return Err(format!(
            "isolated oracle receipt mismatch for {}",
            expected.identity.field_key
        ));
    }
    Ok(())
}

fn render_isolated_checkpoint(
    program: &str,
    units: &[(usize, IsolatedIdentity, String, f64, CandidateMemoryPeaks)],
) -> String {
    let mut out = format!(
        "data=false\nprogram={}\nunits_completed={}\n\nindex\tpopulation\tfield_key\tmanifest_sha256\twall_s\tpeak_rss_kb\tcgroup_peak_memory_kb\n",
        clean_cell(program),
        units.len()
    );
    for (index, identity, manifest, wall_s, memory_peaks) in units {
        out.push_str(&format!(
            "{index}\t{}\t{}\t{manifest}\t{wall_s:.3}\t{}\t{}\n",
            identity.population,
            clean_cell(&identity.identity.field_key),
            memory_peaks.process_peak_rss_kb,
            memory_peaks.cgroup_peak_memory_kb,
        ));
    }
    out
}

fn run_shard(contract: &MeasurementContract, program: super::CorpusProgram) {
    use super::orchestrate::workspace_root;

    let dir = contract.run_root.join("shards").join(program.name);
    if dir.join("receipt.txt").is_file() {
        let manifest = verify_manifest(&dir).unwrap_or_else(|error| {
            panic!(
                "A4C STOP phase=verified-skip candidate={}: {error}",
                program.name
            )
        });
        let receipt = parse_receipt(&dir.join("receipt.txt")).expect("parse skipped receipt");
        validate_completed_receipt(&receipt, contract, program.name, &manifest).unwrap_or_else(
            |error| {
                panic!(
                    "A4C STOP phase=verified-skip candidate={}: {error}",
                    program.name
                )
            },
        );
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
    if !dir.exists() {
        fs::create_dir(&dir).expect("create fresh shard");
    }
    let units_dir = dir.join("units");
    fs::create_dir_all(&units_dir).expect("create candidate-unit directory");
    let input = workspace_root()
        .join("benchmarks/rs-crown-derived")
        .join(program.name)
        .join(program.lib_root);
    let identities = isolated_identities(contract, program.name);
    let mut completed = Vec::<(usize, IsolatedIdentity, String, f64, CandidateMemoryPeaks)>::new();
    for (index, identity) in identities.iter().cloned().enumerate() {
        let unit_dir = units_dir.join(format!("{index:03}"));
        if unit_dir.is_dir() {
            let manifest = verify_manifest(&unit_dir).unwrap_or_else(|error| {
                panic!(
                    "A4C STOP phase=candidate-verified-skip candidate={}: {error}",
                    identity.identity.field_key
                )
            });
            validate_isolated_unit(contract, index, &identity, &unit_dir, &manifest)
                .unwrap_or_else(|error| {
                    panic!(
                        "A4C STOP phase=candidate-verified-skip candidate={}: {error}",
                        identity.identity.field_key
                    )
                });
            let receipt =
                parse_receipt(&unit_dir.join("receipt.txt")).expect("parse candidate receipt");
            completed.push((
                index,
                identity,
                manifest,
                receipt["wall_s"].parse().expect("candidate wall"),
                CandidateMemoryPeaks {
                    process_peak_rss_kb: receipt["peak_rss_kb"].parse().expect("candidate RSS"),
                    cgroup_peak_memory_kb: receipt["cgroup_peak_memory_kb"]
                        .parse()
                        .expect("candidate cgroup peak"),
                },
            ));
            continue;
        }
        fs::create_dir(&unit_dir).expect("create fresh candidate unit");
        let preflight = fs::read_to_string("/proc/meminfo")
            .map(|meminfo| evaluate_host_memory_preflight(&meminfo))
            .unwrap_or_else(|error| HostMemoryPreflight {
                mem_available_bytes: None,
                required_bytes: CANDIDATE_MEMORY_MAX_BYTES + HOST_MEMORY_MARGIN_BYTES,
                status: "host-memory-unavailable",
                error: Some(format!("read /proc/meminfo: {error}")),
            });
        let timestamp_unix_s = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock before Unix epoch")
            .as_secs();
        fs::write(
            unit_dir.join("memory-preflight.txt"),
            preflight.render(program.name, &identity.identity.field_key, timestamp_unix_s),
        )
        .expect("write candidate memory preflight");
        if !preflight.launch_allowed() {
            let manifest = write_manifest(&unit_dir, &["memory-preflight.txt"])
                .expect("manifest failed memory preflight");
            panic!(
                "A4C STOP phase=candidate-memory-preflight candidate={} program={} status={} mem_available_bytes={} required_bytes={} measurement_started=false manifest={manifest}",
                identity.identity.field_key,
                program.name,
                preflight.status,
                preflight.mem_available_bytes.unwrap_or(0),
                preflight.required_bytes,
            );
        }
        let outcome = run_capped_candidate_child(
            program.name,
            &input,
            &unit_dir,
            &[
                (
                    "CRAT_A4_SOURCE_INPUT",
                    contract.input_path.display().to_string(),
                ),
                (
                    "CRAT_A4_SOURCE_CANDIDATE",
                    identity.identity.field_key.clone(),
                ),
                (
                    "CRAT_A4_SOURCE_CANDIDATES",
                    unit_dir.join("candidates.tsv").display().to_string(),
                ),
                (
                    "CRAT_A4_SOURCE_ROOTS",
                    unit_dir.join("roots.tsv").display().to_string(),
                ),
                (
                    "CRAT_A4_SOURCE_EXCEPTIONS",
                    unit_dir.join("exceptions.tsv").display().to_string(),
                ),
                (
                    "CRAT_A4_SOURCE_CHECKPOINT",
                    unit_dir.join("partial.tsv").display().to_string(),
                ),
            ],
        );
        let (phase, marker_candidate) = last_phase(&outcome.stderr);
        if outcome.status != "ok" {
            let memory_peaks = outcome.memory_receipt.require_complete().ok();
            if outcome.status == "resource-exhausted" {
                let memory_peaks = memory_peaks
                    .expect("resource-exhausted classification requires both memory metrics");
                let resource = render_resource_exhausted(
                    program.name,
                    &identity.identity.field_key,
                    CANDIDATE_MEMORY_MAX_BYTES,
                    memory_peaks.process_peak_rss_kb,
                    memory_peaks.cgroup_peak_memory_kb,
                    &phase,
                );
                fs::write(unit_dir.join("resource-exhausted.tsv"), &resource)
                    .expect("write candidate resource exception");
                write_atomic_checkpoint(&dir.join("resource-exhausted.tsv"), &resource)
                    .expect("write program resource exception");
            }
            let memory_receipt = outcome.memory_receipt.render();
            let memory_receipt_error =
                clean_cell(outcome.memory_receipt_error.as_deref().unwrap_or("none"));
            let oom_killer = if outcome.oom_kills > 0 {
                "kernel-oom-killer"
            } else {
                "none"
            };
            let receipt = format!(
                "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nmemory_limit=cgroup-100GiB\nmemory_max_bytes={CANDIDATE_MEMORY_MAX_BYTES}\ncap_verified={}\noom_kills={}\nmemory_max_events={}\noom_killer={oom_killer}\nwall_bound_kind=liveness\nwall_cap_s={LIVENESS_BOUND_S}\nprogram={}\ncandidate={}\npopulation={}\nstatus={}\ndata=false\ncheckpoint_data=false\nanalysis_head={}\nlast_phase={phase}\nlast_candidate={marker_candidate}\nwall_s={:.3}\n{memory_receipt}memory_receipt_error={memory_receipt_error}\n",
                outcome.cap_verified,
                outcome.oom_kills,
                outcome.memory_max_events,
                program.name,
                clean_cell(&identity.identity.field_key),
                identity.population,
                outcome.status,
                contract.head,
                outcome.wall_s,
            );
            fs::write(unit_dir.join("receipt.txt"), receipt).expect("write failed unit receipt");
            let mut files = vec![
                "memory-preflight.txt",
                "receipt.txt",
                "worker.out",
                "worker.err",
            ];
            for file in [
                "candidates.tsv",
                "roots.tsv",
                "exceptions.tsv",
                "partial.tsv",
                "resource-exhausted.tsv",
                "time.txt",
            ] {
                if unit_dir.join(file).is_file() {
                    files.push(file);
                }
            }
            let manifest = write_manifest(&unit_dir, &files).expect("manifest failed unit");
            write_atomic_checkpoint(
                &dir.join("partial.tsv"),
                &render_isolated_checkpoint(program.name, &completed),
            )
            .expect("write program checkpoint after failed unit");
            panic!(
                "A4C STOP phase={phase} candidate={} program={} status={} killer={oom_killer} cap_bytes={} max_events={} wall_s={:.3} peak_rss_kb={} cgroup_peak_memory_kb={} memory_receipt_error={} manifest={manifest}",
                identity.identity.field_key,
                program.name,
                outcome.status,
                CANDIDATE_MEMORY_MAX_BYTES,
                outcome.memory_max_events,
                outcome.wall_s,
                outcome.memory_receipt.process_peak_rss_kb.unwrap_or(0),
                outcome.memory_receipt.cgroup_peak_memory_kb.unwrap_or(0),
                memory_receipt_error,
            );
        }
        let memory_peaks = outcome
            .memory_receipt
            .require_complete()
            .expect("ok candidate requires both memory metrics");
        let candidates = parse_table(&unit_dir.join("candidates.tsv"), CANDIDATE_HEADER, 7)
            .expect("parse isolated candidates");
        let roots = scan_root_path(&unit_dir.join("roots.tsv")).expect("scan isolated roots");
        let exceptions = parse_table(&unit_dir.join("exceptions.tsv"), EXCEPTION_HEADER, 28)
            .expect("parse isolated exceptions");
        let candidates_text = fs::read_to_string(unit_dir.join("candidates.tsv"))
            .expect("read isolated oracle candidate");
        let oracle_byte_match = match validate_oracle_candidate_byte_match(
            &contract.lil_oracle_partial,
            &candidates_text,
            program.name,
            &identity.identity.field_key,
        ) {
            Ok(matched) => matched,
            Err(error) => {
                let memory_receipt = render_candidate_memory_receipt(memory_peaks);
                let receipt = format!(
                    "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nmemory_limit=cgroup-100GiB\nmemory_max_bytes={CANDIDATE_MEMORY_MAX_BYTES}\ncap_verified={}\noom_kills={}\nmemory_max_events={}\noom_killer=none\nwall_bound_kind=liveness\nwall_cap_s={LIVENESS_BOUND_S}\nprogram={}\ncandidate={}\npopulation={}\nstatus=oracle-byte-mismatch\ndata=false\ncheckpoint_data=false\nanalysis_head={}\nlast_phase=oracle-byte-compare\nlast_candidate={}\nwall_s={:.3}\n{memory_receipt}memory_receipt_error=none\noracle_byte_match=false\noracle_partial_sha256={LIL_ORACLE_PARTIAL_SHA256}\n",
                    outcome.cap_verified,
                    outcome.oom_kills,
                    outcome.memory_max_events,
                    program.name,
                    clean_cell(&identity.identity.field_key),
                    identity.population,
                    contract.head,
                    clean_cell(&identity.identity.field_key),
                    outcome.wall_s,
                );
                fs::write(unit_dir.join("receipt.txt"), receipt)
                    .expect("write oracle mismatch receipt");
                let manifest = write_manifest(
                    &unit_dir,
                    &[
                        "memory-preflight.txt",
                        "candidates.tsv",
                        "roots.tsv",
                        "exceptions.tsv",
                        "partial.tsv",
                        "receipt.txt",
                        "worker.out",
                        "worker.err",
                        "time.txt",
                    ],
                )
                .expect("manifest oracle mismatch");
                write_atomic_checkpoint(
                    &dir.join("partial.tsv"),
                    &render_isolated_checkpoint(program.name, &completed),
                )
                .expect("write program checkpoint after oracle mismatch");
                panic!(
                    "A4C STOP phase=oracle-byte-compare candidate={} program={} status=oracle-byte-mismatch manifest={manifest}: {error}",
                    identity.identity.field_key, program.name
                );
            }
        };
        let oracle_label = if oracle_byte_match {
            "true"
        } else {
            "not-applicable"
        };
        let memory_receipt = render_candidate_memory_receipt(memory_peaks);
        let receipt = format!(
            "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nmemory_limit=cgroup-100GiB\nmemory_max_bytes={CANDIDATE_MEMORY_MAX_BYTES}\ncap_verified={}\noom_kills={}\nmemory_max_events={}\noom_killer=none\nwall_bound_kind=liveness\nwall_cap_s={LIVENESS_BOUND_S}\nprogram={}\ncandidate={}\npopulation={}\nstatus=ok\ndata=true\ncheckpoint_data=false\nanalysis_head={}\ncandidates={}\nroots={}\nexceptions={}\nlast_phase={phase}\nlast_candidate={marker_candidate}\nwall_s={:.3}\n{memory_receipt}memory_receipt_error=none\noracle_byte_match={oracle_label}\noracle_partial_sha256={LIL_ORACLE_PARTIAL_SHA256}\n",
            outcome.cap_verified,
            outcome.oom_kills,
            outcome.memory_max_events,
            program.name,
            clean_cell(&identity.identity.field_key),
            identity.population,
            contract.head,
            candidates.len(),
            roots.row_count,
            exceptions.len(),
            outcome.wall_s,
        );
        fs::write(unit_dir.join("receipt.txt"), receipt).expect("write completed unit receipt");
        let manifest = write_manifest(
            &unit_dir,
            &[
                "memory-preflight.txt",
                "candidates.tsv",
                "roots.tsv",
                "exceptions.tsv",
                "partial.tsv",
                "receipt.txt",
                "worker.out",
                "worker.err",
                "time.txt",
            ],
        )
        .expect("manifest completed unit");
        assert_eq!(
            verify_manifest(&unit_dir).expect("verify completed unit manifest"),
            manifest
        );
        validate_isolated_unit(contract, index, &identity, &unit_dir, &manifest)
            .expect("validate newly completed isolated unit");
        completed.push((index, identity, manifest, outcome.wall_s, memory_peaks));
        write_atomic_checkpoint(
            &dir.join("partial.tsv"),
            &render_isolated_checkpoint(program.name, &completed),
        )
        .expect("write program isolated checkpoint");
    }

    let mut combined_candidates = format!("{CANDIDATE_HEADER}\n");
    let mut combined_exceptions = format!("{EXCEPTION_HEADER}\n");
    let mut root_inputs = Vec::new();
    for (index, identity, manifest, _, _) in &completed {
        let unit_dir = units_dir.join(format!("{index:03}"));
        validate_isolated_unit(contract, *index, identity, &unit_dir, manifest)
            .expect("revalidate isolated unit before program finalization");
        append_table(
            &mut combined_candidates,
            &fs::read_to_string(unit_dir.join("candidates.tsv")).expect("read unit candidates"),
            CANDIDATE_HEADER,
        );
        root_inputs.push(unit_dir.join("roots.tsv"));
        append_table(
            &mut combined_exceptions,
            &fs::read_to_string(unit_dir.join("exceptions.tsv")).expect("read unit exceptions"),
            EXCEPTION_HEADER,
        );
    }
    write_atomic_checkpoint(&dir.join("candidates.tsv"), &combined_candidates)
        .expect("write program candidates");
    write_combined_table_streaming(&root_inputs, &dir.join("roots.tsv"), ROOT_HEADER)
        .expect("write program roots");
    write_atomic_checkpoint(&dir.join("exceptions.tsv"), &combined_exceptions)
        .expect("write program exceptions");
    let units_index = render_isolated_checkpoint(program.name, &completed).replacen(
        "data=false\n",
        "data=true\n",
        1,
    );
    write_atomic_checkpoint(&dir.join("units.tsv"), &units_index).expect("write unit index");
    validate_shard(contract, program.name, &dir).unwrap_or_else(|error| {
        panic!(
            "A4C STOP phase=result-validation candidate={}: {error}",
            program.name
        )
    });
    let candidates = parse_table(&dir.join("candidates.tsv"), CANDIDATE_HEADER, 7)
        .expect("parse completed candidates");
    let roots = scan_root_path(&dir.join("roots.tsv")).expect("scan completed roots");
    let exceptions = parse_table(&dir.join("exceptions.tsv"), EXCEPTION_HEADER, 28)
        .expect("parse completed exceptions");
    let wall_s = completed.iter().map(|unit| unit.3).sum::<f64>();
    let peak_rss_kb = completed
        .iter()
        .map(|unit| unit.4.process_peak_rss_kb)
        .max()
        .unwrap_or(0);
    let cgroup_peak_memory_kb = completed
        .iter()
        .map(|unit| unit.4.cgroup_peak_memory_kb)
        .max()
        .unwrap_or(0);
    let oracle_byte_matches = completed
        .iter()
        .filter(|(index, _, _, _, _)| {
            parse_receipt(&units_dir.join(format!("{index:03}")).join("receipt.txt"))
                .expect("read finalized candidate oracle receipt")["oracle_byte_match"]
                == "true"
        })
        .count();
    let expected_oracle_matches = usize::from(program.name == "lil") * 19;
    assert_eq!(
        oracle_byte_matches, expected_oracle_matches,
        "A4C STOP phase=oracle-byte-compare candidate={}: oracle match count drift",
        program.name
    );
    let receipt = format!(
        "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nmemory_limit=cgroup-100GiB\nmemory_max_bytes={CANDIDATE_MEMORY_MAX_BYTES}\ncandidate_isolation=true\nwall_bound_kind=liveness\nwall_cap_s={LIVENESS_BOUND_S}\nprogram={}\nstatus=ok\ndata=true\ncheckpoint_data=false\nanalysis_head={}\na4_aggregate_manifest_sha256={A4_AGGREGATE_MANIFEST_SHA256}\na4_combined_sha256={A4_COMBINED_SHA256}\ncensus_identity_sha256={CENSUS_IDENTITY_SHA256}\nexception_identity_sha256={EXCEPTION_IDENTITY_SHA256}\nraw_corpus_digest={RAW_CORPUS_DIGEST}\nderived_substrate_digest={DERIVED_SUBSTRATE_DIGEST}\nsnapshot={SNAPSHOT_PATH}\ncandidates={}\nroots={}\nexceptions={}\noracle_partial_sha256={LIL_ORACLE_PARTIAL_SHA256}\noracle_byte_matches={oracle_byte_matches}\noracle_expected_matches={expected_oracle_matches}\nlast_phase=complete\nlast_candidate=none\nwall_s={wall_s:.3}\npeak_rss_kb={peak_rss_kb}\ncgroup_peak_memory_kb={cgroup_peak_memory_kb}\n",
        program.name,
        contract.head,
        candidates.len(),
        roots.row_count,
        exceptions.len(),
    );
    fs::write(dir.join("receipt.txt"), receipt).expect("write completed receipt");
    let manifest = write_manifest(
        &dir,
        &[
            "candidates.tsv",
            "roots.tsv",
            "exceptions.tsv",
            "partial.tsv",
            "units.tsv",
            "receipt.txt",
        ],
    )
    .expect("manifest completed shard");
    let verified = verify_manifest(&dir).expect("verify newly completed shard manifest");
    assert_eq!(verified, manifest, "completed shard manifest digest drift");
    let receipt = parse_receipt(&dir.join("receipt.txt")).expect("reparse completed receipt");
    validate_completed_receipt(&receipt, contract, program.name, &manifest)
        .expect("validate newly completed receipt");
    validate_receipt_counts(&receipt, &dir).expect("validate newly completed receipt counts");
    eprintln!(
        "A4C completed program={} candidates={} roots={} exceptions={} wall_s={:.3} peak_rss_kb={} cgroup_peak_memory_kb={} manifest={manifest}",
        program.name,
        candidates.len(),
        roots.row_count,
        exceptions.len(),
        wall_s,
        peak_rss_kb,
        cgroup_peak_memory_kb,
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

fn write_combined_table_streaming(
    inputs: &[PathBuf],
    output: &Path,
    expected_header: &str,
) -> Result<(), String> {
    let temporary = output.with_extension("tsv.tmp");
    let file = fs::File::create(&temporary)
        .map_err(|error| format!("create {}: {error}", temporary.display()))?;
    let mut writer = BufWriter::new(file);
    if inputs.is_empty() {
        writeln!(writer, "{expected_header}")
            .map_err(|error| format!("write empty table {}: {error}", temporary.display()))?;
    } else {
        for (index, input) in inputs.iter().enumerate() {
            let file = fs::File::open(input)
                .map_err(|error| format!("open table {}: {error}", input.display()))?;
            append_table_streaming(
                BufReader::new(file),
                &mut writer,
                expected_header,
                index == 0,
            )?;
        }
    }
    writer
        .flush()
        .map_err(|error| format!("flush {}: {error}", temporary.display()))?;
    drop(writer);
    fs::rename(&temporary, output).map_err(|error| {
        format!(
            "publish streaming table {} from {}: {error}",
            output.display(),
            temporary.display()
        )
    })
}

fn aggregate(contract: &MeasurementContract) {
    let aggregate_dir = contract.run_root.join("aggregate");
    assert!(!aggregate_dir.exists(), "completed aggregate is immutable");
    fs::create_dir(&aggregate_dir).expect("create aggregate directory");
    let mut combined_candidates = format!("{CANDIDATE_HEADER}\n");
    let mut combined_exceptions = format!("{EXCEPTION_HEADER}\n");
    let mut root_inputs = Vec::new();
    let mut receipts = Vec::new();
    let mut shard_manifests = Vec::new();
    for program in &contract.programs {
        let dir = contract.run_root.join("shards").join(program.name);
        let manifest = verify_manifest(&dir).expect("verify completed shard");
        let receipt = parse_receipt(&dir.join("receipt.txt")).expect("parse completed receipt");
        validate_completed_receipt(&receipt, contract, program.name, &manifest)
            .expect("aggregate only completed data=true shards");
        shard_manifests.push((program.name, manifest));
        validate_receipt_counts(&receipt, &dir).expect("aggregate receipt counts");
        receipts.push(receipt);
        append_table(
            &mut combined_candidates,
            &fs::read_to_string(dir.join("candidates.tsv")).expect("read candidate shard"),
            CANDIDATE_HEADER,
        );
        root_inputs.push(dir.join("roots.tsv"));
        append_table(
            &mut combined_exceptions,
            &fs::read_to_string(dir.join("exceptions.tsv")).expect("read exception shard"),
            EXCEPTION_HEADER,
        );
    }
    let candidates_path = aggregate_dir.join("candidates.tsv");
    let roots_path = aggregate_dir.join("roots.tsv");
    let exceptions_path = aggregate_dir.join("exceptions.tsv");
    let candidate_readings_path = aggregate_dir.join("candidate-readings.tsv");
    let identity_path = aggregate_dir.join("identity.tsv");
    fs::write(&candidates_path, combined_candidates).expect("write aggregate candidates");
    write_combined_table_streaming(&root_inputs, &roots_path, ROOT_HEADER)
        .expect("write aggregate roots");
    fs::write(&exceptions_path, combined_exceptions).expect("write aggregate exceptions");
    let candidates =
        parse_table(&candidates_path, CANDIDATE_HEADER, 7).expect("parse aggregate candidates");
    let roots = scan_root_path(&roots_path).expect("scan aggregate roots");
    let exceptions =
        parse_table(&exceptions_path, EXCEPTION_HEADER, 28).expect("parse aggregate exceptions");
    fs::write(
        &candidate_readings_path,
        render_candidate_readings_from_summary(&candidates, &roots)
            .expect("derive closed/open candidate readings"),
    )
    .expect("write aggregate candidate readings");
    fs::write(
        &identity_path,
        render_full_identity(&contract.input).expect("derive exact 261-row identity"),
    )
    .expect("write aggregate full identity");
    let candidate_readings = parse_table(&candidate_readings_path, CANDIDATE_READINGS_HEADER, 10)
        .expect("parse aggregate candidate readings");
    let full_identity = parse_table(&identity_path, FULL_IDENTITY_HEADER, 6)
        .expect("parse aggregate full identity");
    assert_eq!(candidates.len(), 237);
    assert_eq!(candidate_readings.len(), 237);
    assert_eq!(full_identity.len(), 261);
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

    let mut closed_class_counts = BTreeMap::<String, usize>::new();
    let mut open_class_counts = BTreeMap::<String, usize>::new();
    let mut flag_counts = BTreeMap::<String, usize>::new();
    let mut provenance_tag_counts = BTreeMap::<String, usize>::new();
    let mut closed_class_witness = BTreeMap::<String, String>::new();
    let mut open_class_witness = BTreeMap::<String, String>::new();
    let flag_witness = &roots.flag_witnesses;
    let provenance_tag_witness = &roots.provenance_tag_witnesses;
    for row in &candidate_readings {
        *closed_class_counts.entry(row[4].clone()).or_default() += 1;
        *open_class_counts.entry(row[5].clone()).or_default() += 1;
        closed_class_witness
            .entry(row[4].clone())
            .or_insert_with(|| format!("{}::{}", row[0], row[1]));
        open_class_witness
            .entry(row[5].clone())
            .or_insert_with(|| format!("{}::{}", row[0], row[1]));
        let evidence = parse_root_evidence(&row[7]).expect("validated open candidate evidence");
        for flag in evidence.flags {
            *flag_counts.entry(flag_label(flag).to_owned()).or_default() += 1;
        }
        for tag in evidence.provenance_tags {
            *provenance_tag_counts.entry(tag).or_default() += 1;
        }
    }
    assert_eq!(closed_class_counts.values().sum::<usize>(), 237);
    assert_eq!(open_class_counts.values().sum::<usize>(), 237);
    for flag in flag_counts.keys() {
        assert!(flag_witness.contains_key(flag));
    }
    for tag in provenance_tag_counts.keys() {
        assert!(provenance_tag_witness.contains_key(tag));
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
    let cgroup_peak_memory = receipts
        .iter()
        .filter_map(|receipt| receipt.get("cgroup_peak_memory_kb"))
        .map(|peak| peak.parse::<u64>().expect("cgroup peak integer"))
        .max()
        .unwrap_or(0);
    let shard_analysis_heads = contract
        .programs
        .iter()
        .zip(&receipts)
        .map(|(program, receipt)| format!("{}:{}", program.name, receipt["analysis_head"]))
        .collect::<Vec<_>>()
        .join(",");
    let mut per_program = String::from(
        "program\tcandidates\troots\texceptions\tclosed_invisible\tclosed_absent\tclosed_mixed\topen_invisible\topen_absent\topen_mixed\tstance_divergences\twall_s\tpeak_rss_kb\tcgroup_peak_memory_kb\n",
    );
    for (program, receipt) in contract.programs.iter().zip(&receipts) {
        let program_rows = candidate_readings
            .iter()
            .filter(|row| row[0] == program.name)
            .collect::<Vec<_>>();
        let count_closed = |class: &str| program_rows.iter().filter(|row| row[4] == class).count();
        let count_open = |class: &str| program_rows.iter().filter(|row| row[5] == class).count();
        let cgroup_peak = receipt
            .get("cgroup_peak_memory_kb")
            .map(String::as_str)
            .unwrap_or("not-recorded-pre-isolation");
        per_program.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            program.name,
            program_rows.len(),
            roots.program_counts.get(program.name).copied().unwrap_or(0),
            exceptions
                .iter()
                .filter(|row| row[0] == program.name)
                .count(),
            count_closed("invisible"),
            count_closed("absent"),
            count_closed("mixed"),
            count_open("invisible"),
            count_open("absent"),
            count_open("mixed"),
            program_rows.iter().filter(|row| row[4] != row[5]).count(),
            receipt["wall_s"],
            receipt["peak_rss_kb"],
            cgroup_peak,
        ));
    }
    let closed_class_summary = closed_class_counts
        .iter()
        .map(|(class, count)| {
            format!(
                "- `{class}`: **{count}**, witness `{}`",
                closed_class_witness[class]
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let open_class_summary = open_class_counts
        .iter()
        .map(|(class, count)| {
            format!(
                "- `{class}`: **{count}**, witness `{}`",
                open_class_witness[class]
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let flag_summary = flag_counts
        .iter()
        .map(|(flag, count)| format!("- `{flag}`: **{count}**, witness `{}`", flag_witness[flag]))
        .collect::<Vec<_>>()
        .join("\n");
    let provenance_tag_summary = provenance_tag_counts
        .iter()
        .map(|(tag, count)| {
            format!(
                "- `{tag}`: **{count}**, witness `{}`",
                provenance_tag_witness[tag]
            )
        })
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
    let stance_divergences = candidate_readings
        .iter()
        .filter(|row| row[4] != row[5])
        .count();
    let report = format!(
        "# A4 force-SAT exceptions and no-allocation-source census\n\nMachine `{MACHINE_ID}`, platform `{PLATFORM}`. Pre-isolation predecessor shards were uncapped; current-head candidates ran sequentially in fresh processes under a 100 GiB cgroup host-protection cap and a {LIVENESS_BOUND_S}-second liveness bound. Wall/RSS values are machine-local and never compared across machines.\n\nExact identity: **261/261** A4/P2 candidates plus **4/4** separately re-checked force-SAT exception rows (**261+4**), with **237/237** no-allocation-source candidates characterized. Unknown/unexplained: **0**.\n\n## Closed-world partition\n\nThe closed-world reading excludes only `public-setter-reachable` external-remainder rows.\n\n{closed_class_summary}\n\n## Open partition\n\nThe open reading includes every manifested path row and treats the public-setter remainder as opaque/absent.\n\n{open_class_summary}\n\nClosed/open class divergences: **{stance_divergences}**.\n\n## Overlapping cause flags (open reading)\n\n{flag_summary}\n\n## Indirect-target provenance tags\n\n{provenance_tag_summary}\n\nTags remain outside the invisible/absent predicates. `public-setter-reachable` controls only which manifested row enters the closed versus open reading.\n\n## Force-SAT exceptions\n\n{exception_summary}\n\nSequential shard wall sum: **{total_wall:.3}s**. Maximum process peak RSS: **{peak_rss} KiB**. Maximum current-head candidate cgroup peak charged memory: **{cgroup_peak_memory} KiB**. Only SHA-manifested, completed `data=true` shards feed this report; atomic `data=false` checkpoints are excluded. Production analysis and rewriter behavior remained untouched.\n"
    );
    let provenance = format!(
        "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nanalysis_head={}\nanalysis_branch=codex/a4-source-census\nbaseline_branch=analysis-lane\nbaseline_head=67bcd3cb67c1ae6f74463050033370b108854411\na4_input_root={}\na4_aggregate_manifest_sha256={A4_AGGREGATE_MANIFEST_SHA256}\na4_combined_sha256={A4_COMBINED_SHA256}\ncensus_identity_sha256={CENSUS_IDENTITY_SHA256}\nexception_identity_sha256={EXCEPTION_IDENTITY_SHA256}\nraw_corpus_digest={RAW_CORPUS_DIGEST}\nderived_substrate_digest={DERIVED_SUBSTRATE_DIGEST}\nsnapshot={SNAPSHOT_PATH}\nmemory_policy=predecessor-shards-uncapped,current-head-candidates-cgroup-100GiB\nwall_bound_kind=liveness\nwall_cap_s={LIVENESS_BOUND_S}\nprograms={}\nfull_identity_rows=261\ncensus_candidates=237\nexception_rechecks=4\nidentity_accounting=261+4\nunknown=0\nunexplained=0\nclosed_open_divergences={stance_divergences}\nroots={}\nwall_sum_s={total_wall:.3}\npeak_rss_kb={peak_rss}\ncgroup_peak_memory_kb={cgroup_peak_memory}\ncgroup_peak_scope=current-head-candidate-isolated-shards-only\nshard_analysis_heads={shard_analysis_heads}\nshard_manifests={}\naggregation_input_policy=manifested-published-completed-data-true-only\ntiming_comparison=forbidden-across-machines\n",
        contract.head,
        contract.input_root.display(),
        contract.programs.len(),
        roots.row_count,
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
            "candidate-readings.tsv",
            "roots.tsv",
            "exceptions.tsv",
            "identity.tsv",
            "per-program.tsv",
            "report.md",
            "provenance.txt",
        ],
    )
    .expect("manifest aggregate");
    eprintln!(
        "A4C aggregate complete manifest={manifest} identity=261+4 candidates=237 exceptions=4 roots={} closed_classes={closed_class_counts:?} open_classes={open_class_counts:?} divergences={stance_divergences} flags={flag_counts:?}",
        roots.row_count
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
    use std::{fs, io::Cursor, process};

    use super::*;

    fn singleton(flag: CauseFlag) -> RootEvidence {
        RootEvidence {
            flags: BTreeSet::from([flag]),
            provenance_tags: BTreeSet::new(),
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
            (
                SyntheticPath {
                    terminal: TerminalKind::NullLiteral,
                    crosses_call: false,
                    crosses_field: false,
                    realloc: false,
                    same_function_scanner_gap: false,
                },
                CauseFlag::NullLiteralRoot,
            ),
        ];

        for (path, expected) in cases {
            assert_eq!(flags_for_path(path), BTreeSet::from([expected]));
        }
    }

    #[test]
    fn candidate_isolation_selects_exactly_one_population_row() {
        let row = |field_key: &str, baseline_force: &str, proof_reason: &str| A4InputRow {
            program: "fixture".to_owned(),
            field_key: field_key.to_owned(),
            field_slot: 0,
            baseline_kind: SlotKind::Raw,
            baseline_force: baseline_force.to_owned(),
            proof_reason: proof_reason.to_owned(),
        };
        let input = vec![
            row("Fixture::field0@d0", "unsat", "allocation-source-count-0"),
            row("Fixture::field1@d0", "sat", "force-sat-exception"),
        ];

        let census = select_isolated_input(&input, "fixture", "Fixture::field0@d0").unwrap();
        assert_eq!(census.0.len(), 1);
        assert!(census.1.is_empty());

        let exception = select_isolated_input(&input, "fixture", "Fixture::field1@d0").unwrap();
        assert!(exception.0.is_empty());
        assert_eq!(exception.1.len(), 1);

        assert!(select_isolated_input(&input, "fixture", "missing").is_err());
    }

    #[test]
    fn capped_candidate_classification_is_fail_closed() {
        assert_eq!(classify_capped_candidate(true, 0, 0, true), Ok("ok"));
        assert_eq!(
            classify_capped_candidate(true, 1, 1, false),
            Ok("resource-exhausted")
        );
        assert_eq!(
            classify_capped_candidate(true, 1, 0, false),
            Ok("environment-oom-kill")
        );
        assert!(
            classify_capped_candidate(false, 0, 0, false)
                .expect_err("an unverified cgroup cap must fail setup")
                .contains("cap was not verified")
        );

        let row = render_resource_exhausted(
            "fixture",
            "Fixture::field0@d0",
            CANDIDATE_MEMORY_MAX_BYTES,
            104_857_600,
            104_900_000,
            "source-traversal",
        );
        assert!(row.starts_with(RESOURCE_EXHAUSTED_HEADER));
        assert!(row.contains("\tresource-exhausted\t107374182400\t104857600\t104900000\t"));
        assert!(row.ends_with("\tfalse\n"));
    }

    #[test]
    fn gnu_time_peak_rss_parser_is_strict() {
        let receipt = concat!(
            "Command being timed: fixture\n",
            "\tMaximum resident set size (kbytes): 333660\n",
            "\tExit status: 0\n",
        );
        assert_eq!(parse_gnu_time_peak_rss_kb(receipt), Ok(333_660));
        assert!(
            parse_gnu_time_peak_rss_kb("Exit status: 0\n")
                .expect_err("missing GNU-time RSS must fail closed")
                .contains("missing")
        );
        assert!(
            parse_gnu_time_peak_rss_kb(concat!(
                "Maximum resident set size (kbytes): 1\n",
                "Maximum resident set size (kbytes): 2\n",
            ))
            .expect_err("duplicate GNU-time RSS must fail closed")
            .contains("duplicate")
        );
    }

    #[test]
    fn candidate_memory_receipt_preserves_each_available_metric() {
        let receipt = collect_candidate_memory_receipt(
            Some("Maximum resident set size (kbytes): 333660\n"),
            Some(205_209_600),
        );
        let peaks = receipt.require_complete().unwrap();
        assert_eq!(peaks.process_peak_rss_kb, 333_660);
        assert_eq!(peaks.cgroup_peak_memory_kb, 200_400);
        assert_eq!(
            receipt.render(),
            "peak_rss_kb=333660\ncgroup_peak_memory_kb=200400\n"
        );
        let cgroup_only = collect_candidate_memory_receipt(None, Some(205_209_600));
        assert_eq!(
            cgroup_only.render(),
            "peak_rss_kb=unavailable\ncgroup_peak_memory_kb=200400\n"
        );
        assert!(cgroup_only.require_complete().is_err());
        let rss_only = collect_candidate_memory_receipt(
            Some("Maximum resident set size (kbytes): 333660\n"),
            None,
        );
        assert_eq!(
            rss_only.render(),
            "peak_rss_kb=333660\ncgroup_peak_memory_kb=unavailable\n"
        );
        assert!(rss_only.require_complete().is_err());
    }

    #[test]
    fn candidate_systemd_policy_keeps_the_wrapper_alive_after_child_oom() {
        let properties = candidate_systemd_properties(CANDIDATE_MEMORY_MAX_BYTES);
        assert!(
            properties
                .iter()
                .any(|property| property == "OOMPolicy=continue")
        );
        assert!(
            !properties
                .iter()
                .any(|property| property == "OOMPolicy=stop")
        );
    }

    #[test]
    fn host_memory_preflight_is_typed_and_strictly_above_cap_plus_margin() {
        let threshold = CANDIDATE_MEMORY_MAX_BYTES + HOST_MEMORY_MARGIN_BYTES;
        let ready = evaluate_host_memory_preflight(&format!(
            "MemTotal: 200000000 kB\nMemAvailable: {} kB\n",
            threshold / 1024 + 1
        ));
        assert_eq!(ready.status, "ready");
        assert!(ready.launch_allowed());
        assert_eq!(ready.required_bytes, threshold);
        assert!(
            ready
                .render("fixture", "Fixture::field0@d0", 123)
                .contains("status=ready\nmeasurement_started=false\n")
        );

        let equal =
            evaluate_host_memory_preflight(&format!("MemAvailable: {} kB\n", threshold / 1024));
        assert_eq!(equal.status, "host-memory-insufficient");
        assert!(!equal.launch_allowed());
        assert!(
            evaluate_host_memory_preflight("MemTotal: 1 kB\n")
                .render("fixture", "Fixture::field0@d0", 123)
                .contains("mem_available_bytes=unavailable")
        );
    }

    #[test]
    fn resume9_unit_reuse_is_exactly_manifest_and_identity_scoped() {
        assert!(resume9_lil_unit_is_authorized(
            0,
            "src::lil::_expreval_t::field0@d0",
            "938b30fa2b20fcd987f4bef32163c6354545a6f451c44d4942445dd3dd0fbaa7",
        ));
        assert!(!resume9_lil_unit_is_authorized(
            0,
            "src::lil::_expreval_t::field0@d0",
            "0000000000000000000000000000000000000000000000000000000000000000",
        ));
        assert!(!resume9_lil_unit_is_authorized(
            19,
            "src::lil::_lil_var_t::field2@d0",
            "938b30fa2b20fcd987f4bef32163c6354545a6f451c44d4942445dd3dd0fbaa7",
        ));
    }

    #[test]
    fn checkpoint_reuse_requires_candidate_and_ordered_root_rows() {
        let candidate = concat!(
            "program\tfield_key\tfield_slot\tordinary_kind\tprimary_class\tcause_flags\troot_count\n",
            "fixture\tFixture::field0@d0\t0\traw\tabsent\tnull-literal-root\t1\n",
        );
        let roots = concat!(
            "population\tprogram\tfield_key\tstore_site\troot_id\troot_label\tcause_flags\tordered_path\n",
            "census\tfixture\tFixture::field0@d0\tstore\troot\tnull\tnull-literal-root\troot>store\n",
        );
        assert!(validate_reusable_candidate_artifact(
            "fixture",
            "Fixture::field0@d0",
            candidate,
            roots,
        )
        .is_ok());
        assert!(
            validate_reusable_candidate_artifact(
                "fixture",
                "Fixture::field0@d0",
                candidate,
                ROOT_HEADER.to_owned().as_str(),
            )
            .expect_err("candidate summary without ordered roots must not be reusable")
            .contains("root inventory")
        );
    }

    #[test]
    fn preserved_summary_is_a_byte_oracle_not_a_skip_artifact() {
        let oracle = concat!(
            "data=false\n",
            "candidates_completed=1\n\n",
            "program\tfield_key\tfield_slot\tordinary_kind\tprimary_class\tcause_flags\troot_count\n",
            "fixture\tFixture::field0@d0\t0\traw\tabsent\tnull-literal-root\t1\n",
        );
        let matching = concat!(
            "program\tfield_key\tfield_slot\tordinary_kind\tprimary_class\tcause_flags\troot_count\n",
            "fixture\tFixture::field0@d0\t0\traw\tabsent\tnull-literal-root\t1\n",
        );
        let drifted = matching.replace("\tabsent\t", "\tmixed\t");

        assert_eq!(
            validate_oracle_candidate_byte_match(oracle, matching, "fixture", "Fixture::field0@d0"),
            Ok(true)
        );
        assert!(
            validate_oracle_candidate_byte_match(oracle, &drifted, "fixture", "Fixture::field0@d0")
                .expect_err("semantic drift must STOP")
                .contains("byte mismatch")
        );
        assert_eq!(
            validate_oracle_candidate_byte_match(oracle, matching, "fixture", "Fixture::field1@d0"),
            Ok(false)
        );
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
            classify_roots(&[singleton(CauseFlag::NullLiteralRoot)]),
            PrimaryClass::Absent
        );
        assert_eq!(
            classify_roots(&[
                singleton(CauseFlag::FieldMediatedAllocation),
                singleton(CauseFlag::NullLiteralRoot),
            ]),
            PrimaryClass::Mixed
        );
        assert_eq!(classify_roots(&[]), PrimaryClass::Unresolved);
        assert_eq!(
            classify_roots(&[RootEvidence {
                flags: BTreeSet::new(),
                provenance_tags: BTreeSet::new(),
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
    fn closed_world_parameter_remainder_is_identity_based() {
        assert!(!parameter_has_external_remainder(false, true));
        assert!(parameter_has_external_remainder(false, false));
        assert!(parameter_has_external_remainder(true, true));
    }

    #[test]
    fn strict_flag_parser_accepts_only_registered_schema() {
        assert_eq!(
            parse_cause_flag("interprocedural-allocation"),
            Ok(CauseFlag::InterproceduralAllocation)
        );
        assert_eq!(
            parse_cause_flag("null-literal-root"),
            Ok(CauseFlag::NullLiteralRoot)
        );
        assert!(parse_cause_flag("analyst-judgment").is_err());
        assert_eq!(
            parse_provenance_tag("string-literal-root"),
            Ok("string-literal-root".to_owned())
        );
        assert_eq!(
            parse_provenance_tag("external-parameter-pointee-load"),
            Ok("external-parameter-pointee-load".to_owned())
        );
        assert_eq!(
            parse_provenance_tag("indirect-external-parameter-callback"),
            Ok("indirect-external-parameter-callback".to_owned())
        );
        assert_eq!(
            parse_provenance_tag("public-setter-reachable"),
            Ok("public-setter-reachable".to_owned())
        );
        assert_eq!(
            parse_root_evidence("static-or-interior-root|string-literal-root"),
            Ok(RootEvidence {
                flags: BTreeSet::from([CauseFlag::StaticOrInteriorRoot]),
                provenance_tags: BTreeSet::from(["string-literal-root".to_owned()]),
            })
        );
        assert_eq!(
            parse_root_evidence("externally-supplied-parameter|external-parameter-pointee-load"),
            Ok(RootEvidence {
                flags: BTreeSet::from([CauseFlag::ExternallySuppliedParameter]),
                provenance_tags: BTreeSet::from(["external-parameter-pointee-load".to_owned()]),
            })
        );
    }

    #[test]
    fn null_literal_is_distinct_from_other_pointer_constants() {
        assert_eq!(pointer_constant_terminal(true), TerminalKind::NullLiteral);
        assert_eq!(pointer_constant_terminal(false), TerminalKind::Unsupported);
    }

    #[test]
    fn byte_string_constant_is_absent_but_integer_pointer_stops() {
        let source = r#"
            unsafe fn byte_string_root() -> *mut i8 {
                b"fixture\0" as *const u8 as *mut i8
            }
            unsafe fn integer_pointer_root() -> *mut i8 {
                1usize as *mut i8
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let roots_for = |suffix: &str| {
                program
                    .functions
                    .iter()
                    .copied()
                    .filter(|function| tcx.def_path_str(*function).ends_with(suffix))
                    .flat_map(|function| {
                        let body_ref = tcx
                            .mir_drops_elaborated_and_const_checked(function)
                            .borrow();
                        let body = &*body_ref;
                        body.basic_blocks
                            .iter()
                            .flat_map(|data| data.statements.iter())
                            .filter_map(|statement| {
                                let StatementKind::Assign(box (_, rvalue)) = &statement.kind else {
                                    return None;
                                };
                                let operand = match rvalue {
                                    Rvalue::Use(operand @ Operand::Constant(_))
                                    | Rvalue::Cast(_, operand @ Operand::Constant(_), _) => operand,
                                    _ => return None,
                                };
                                Some(constant_root(tcx, operand))
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            };

            let byte_string = roots_for("byte_string_root");
            assert_eq!(
                byte_string,
                vec![(
                    TerminalKind::StaticOrInterior,
                    BTreeSet::from(["string-literal-root".to_owned()]),
                )]
            );
            assert_eq!(
                flags_for_path(SyntheticPath {
                    terminal: byte_string[0].0,
                    crosses_call: false,
                    crosses_field: false,
                    realloc: false,
                    same_function_scanner_gap: false,
                }),
                BTreeSet::from([CauseFlag::StaticOrInteriorRoot])
            );
            assert_eq!(
                classify_roots(&[RootEvidence {
                    flags: BTreeSet::from([CauseFlag::StaticOrInteriorRoot]),
                    provenance_tags: byte_string[0].1.clone(),
                }]),
                PrimaryClass::Absent
            );

            assert_eq!(
                roots_for("integer_pointer_root"),
                vec![(TerminalKind::Unsupported, BTreeSet::new())],
                "a nonzero integer-to-pointer constant must remain a STOP root"
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn nested_external_parameter_flow_is_depth_sensitive_without_cast_expansion() {
        let source = r#"
            pub unsafe fn external_nested(
                argv: *mut *mut i8,
                index: isize,
            ) -> *mut i8 {
                let copied = argv;
                *copied.offset(index)
            }

            unsafe fn private_nested(argv: *mut *mut i8) -> *mut i8 {
                *argv
            }

            pub unsafe fn external_caller(argv: *mut *mut i8) -> *mut i8 {
                private_nested(argv)
            }

            pub unsafe fn public_nested(argv: *mut *mut i8) -> *mut i8 {
                *argv
            }

            pub unsafe fn external_calls_public(argv: *mut *mut i8) -> *mut i8 {
                public_nested(argv)
            }

            unsafe fn private_constant(value: *mut i8) -> *mut i8 {
                value
            }

            pub unsafe fn call_private_constant() -> *mut i8 {
                private_constant(0 as *mut i8)
            }

            pub unsafe fn depth_changing_cast(argv: *mut *mut i8) -> *mut i8 {
                let erased = argv as *mut i8;
                let rebuilt = erased as *mut *mut i8;
                *rebuilt
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let graph = build_source_graph(tcx, &slots, &BoExport::default());
            let function = |suffix: &str| {
                program
                    .functions
                    .iter()
                    .copied()
                    .find(|function| tcx.def_path_str(*function).ends_with(suffix))
                    .unwrap_or_else(|| panic!("missing fixture function {suffix}"))
            };
            let return_roots = |suffix: &str| {
                let fn_did = function(suffix);
                let body_ref = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
                let body = &*body_ref;
                let target = node_for_place(tcx, &slots, fn_did, body, Place::from(RETURN_PLACE))
                    .expect("pointer return must have a source-graph node");
                trace_candidate(&graph, &target)
            };

            let external = return_roots("external_nested");
            assert_eq!(
                classify_roots(
                    &external
                        .iter()
                        .map(|root| root.evidence.clone())
                        .collect::<Vec<_>>()
                ),
                PrimaryClass::Absent
            );
            assert!(external.iter().any(|root| {
                root.evidence
                    .provenance_tags
                    .contains("external-parameter-pointee-load")
            }));
            assert!(external.iter().any(|root| {
                root.path
                    .iter()
                    .any(|label| label.contains("depth-transfer") && label.contains("depth1"))
            }));
            assert!(external.iter().any(|root| {
                root.path
                    .iter()
                    .any(|label| label.contains("rust-flow") && label.contains("depth1"))
            }));

            let private = function("private_nested");
            let private_body_ref = tcx.mir_drops_elaborated_and_const_checked(private).borrow();
            let private_body = &*private_body_ref;
            let private_parameter = resolve_place(
                &slots,
                private,
                private_body,
                Place::from(Local::from_usize(1)),
                1,
                None,
            )
            .map(|resolved| node_for_resolved(tcx, &slots, private, resolved))
            .expect("nested private parameter slot");
            assert!(
                graph.terminals.get(&private_parameter).is_none(),
                "an in-crate-supplied private parameter has no direct external terminal"
            );
            assert_eq!(
                classify_roots(
                    &return_roots("external_caller")
                        .iter()
                        .map(|root| root.evidence.clone())
                        .collect::<Vec<_>>()
                ),
                PrimaryClass::Absent,
                "the in-crate argument path must reach the caller's external remainder"
            );

            let public = function("public_nested");
            let public_body_ref = tcx.mir_drops_elaborated_and_const_checked(public).borrow();
            let public_body = &*public_body_ref;
            let public_parameter = resolve_place(
                &slots,
                public,
                public_body,
                Place::from(Local::from_usize(1)),
                1,
                None,
            )
            .map(|resolved| node_for_resolved(tcx, &slots, public, resolved))
            .expect("nested public parameter slot");
            assert!(
                graph.terminals.get(&public_parameter).is_some(),
                "a public parameter retains its externally reachable remainder"
            );
            assert!(
                graph.incoming.get(&public_parameter).is_some(),
                "the in-crate path into a public parameter remains distinct"
            );

            let constant = return_roots("call_private_constant");
            assert!(constant.iter().all(|root| {
                root.evidence.flags == BTreeSet::from([CauseFlag::NullLiteralRoot])
            }));
            assert!(constant.iter().all(|root| {
                !root
                    .evidence
                    .flags
                    .contains(&CauseFlag::ExternallySuppliedParameter)
            }));

            assert_eq!(
                classify_roots(
                    &return_roots("depth_changing_cast")
                        .iter()
                        .map(|root| root.evidence.clone())
                        .collect::<Vec<_>>()
                ),
                PrimaryClass::Unresolved,
                "a depth-changing cast must not synthesize nested provenance"
            );
        })
        .unwrap_or_else(|error| error.raise());
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
    fn root_row_identity_distinguishes_paths_and_rejects_exact_duplicates() {
        let root = vec![
            "census".to_owned(),
            "bst".to_owned(),
            "src::bst::node::field1@d0".to_owned(),
            "transfer:src::bst::insert:bb7[2]".to_owned(),
            "RecognizedAllocation:newNode:malloc".to_owned(),
            "allocator:newNode:malloc".to_owned(),
            "interprocedural-allocation".to_owned(),
            "malloc -> insert-return -> field-store".to_owned(),
        ];
        let mut distinct_path = root.clone();
        distinct_path[7] = "malloc -> insert-return -> recursive-arg -> field-store".to_owned();
        assert!(validate_unique_root_rows(&[root.clone(), distinct_path]).is_ok());
        assert!(validate_unique_root_rows(&[root.clone(), root]).is_err());
    }

    #[test]
    fn streaming_root_validation_preserves_schema_identity_count_and_duplicates() {
        let row = "census\tfixture\tFixture::field0@d0\tstore\troot\tlabel\tstatic-or-interior-root\troot -> store\n";
        let distinct_path = row.replace("root -> store", "root -> copy -> store");
        let valid = format!("{ROOT_HEADER}\n{row}{distinct_path}");
        let summary = scan_root_table(Cursor::new(valid), "streaming fixture").unwrap();
        assert_eq!(summary.row_count, 2);
        assert!(
            validate_isolated_root_summary(&summary, "census", "fixture", "Fixture::field0@d0", 2,)
                .is_ok()
        );
        assert!(
            validate_isolated_root_summary(&summary, "census", "fixture", "Fixture::field0@d0", 1,)
                .expect_err("count drift must fail")
                .contains("count")
        );
        assert!(
            validate_isolated_root_summary(&summary, "census", "fixture", "Fixture::field1@d0", 2,)
                .expect_err("identity drift must fail")
                .contains("identity")
        );

        let duplicate = format!("{ROOT_HEADER}\n{row}{row}");
        assert!(
            scan_root_table(Cursor::new(duplicate), "duplicate fixture")
                .expect_err("an adjacent exact duplicate must fail")
                .contains("duplicate")
        );
        let malformed = format!("{ROOT_HEADER}\ncensus\tfixture\ttoo-few\n");
        assert!(
            scan_root_table(Cursor::new(malformed), "malformed fixture")
                .expect_err("column drift must fail")
                .contains("columns")
        );
    }

    #[test]
    fn streaming_readings_and_concatenation_are_byte_identical() {
        let candidates_text = concat!(
            "program\tfield_key\tfield_slot\tordinary_kind\tprimary_class\tcause_flags\troot_count\n",
            "fixture\tFixture::field0@d0\t0\traw\tmixed\tfield-mediated-allocation|static-or-interior-root|public-setter-reachable\t2\n",
        );
        let roots_text = concat!(
            "population\tprogram\tfield_key\tstore_site\troot_id\troot_label\tcause_flags\tordered_path\n",
            "census\tfixture\tFixture::field0@d0\tstore0\troot0\talloc\tfield-mediated-allocation\talloc -> store0\n",
            "census\tfixture\tFixture::field0@d0\tstore1\troot1\tstatic\tstatic-or-interior-root|public-setter-reachable\tstatic -> store1\n",
        );
        let candidates =
            parse_table_text(candidates_text, CANDIDATE_HEADER, 7, "candidate fixture").unwrap();
        let roots = parse_table_text(roots_text, ROOT_HEADER, 8, "root fixture").unwrap();
        let in_memory = render_candidate_readings(&candidates, &roots).unwrap();
        let summary = scan_root_table(Cursor::new(roots_text), "root fixture").unwrap();
        let streaming = render_candidate_readings_from_summary(&candidates, &summary).unwrap();
        assert_eq!(streaming.as_bytes(), in_memory.as_bytes());

        let mut expected = String::new();
        append_table(&mut expected, roots_text, ROOT_HEADER);
        append_table(&mut expected, roots_text, ROOT_HEADER);
        let mut actual = Vec::new();
        append_table_streaming(Cursor::new(roots_text), &mut actual, ROOT_HEADER, true).unwrap();
        append_table_streaming(Cursor::new(roots_text), &mut actual, ROOT_HEADER, false).unwrap();
        assert_eq!(actual, expected.as_bytes());
    }

    #[test]
    #[ignore = "lambda7 byte/digest witness against manifested resume9 BST shard"]
    fn streaming_matches_manifested_bst_artifact_byte_for_byte() {
        let dir = Path::new(
            "/home/p51lee/dev/agent-worktrees/crat-a4-source-census-run-20260813-retry3-resume9/shards/bst",
        );
        assert_eq!(
            verify_manifest(dir).unwrap(),
            "f9c23eddb3b9da283a2ebf82a4839f9f0e28c4d535f69923d38531ad397b90dd"
        );
        let candidates = parse_table(&dir.join("candidates.tsv"), CANDIDATE_HEADER, 7).unwrap();
        let roots_text = fs::read_to_string(dir.join("roots.tsv")).unwrap();
        let roots = parse_table_text(&roots_text, ROOT_HEADER, 8, "manifested BST roots").unwrap();
        let in_memory = render_candidate_readings(&candidates, &roots).unwrap();
        let summary = scan_root_path(&dir.join("roots.tsv")).unwrap();
        let streaming = render_candidate_readings_from_summary(&candidates, &summary).unwrap();
        assert_eq!(streaming.as_bytes(), in_memory.as_bytes());

        let mut copied = Vec::new();
        append_table_streaming(Cursor::new(&roots_text), &mut copied, ROOT_HEADER, true).unwrap();
        assert_eq!(copied, roots_text.as_bytes());
        assert_eq!(
            sha256_text(std::str::from_utf8(&copied).unwrap()),
            sha256(&dir.join("roots.tsv"))
        );
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
            provenance_tags: BTreeSet::new(),
        });
        graph.add_edge(FlowEdge {
            source: "alloc-result".to_owned(),
            target: "callee-return".to_owned(),
            kind: FlowEdgeKind::Call,
            label: "return-edge".to_owned(),
            provenance_tags: BTreeSet::new(),
        });
        graph.add_edge(FlowEdge {
            source: "callee-return".to_owned(),
            target: "other-field".to_owned(),
            kind: FlowEdgeKind::Field,
            label: "store-other-field".to_owned(),
            provenance_tags: BTreeSet::new(),
        });
        graph.add_edge(FlowEdge {
            source: "other-field".to_owned(),
            target: "candidate".to_owned(),
            kind: FlowEdgeKind::Field,
            label: "store-candidate".to_owned(),
            provenance_tags: BTreeSet::new(),
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
            provenance_tags: BTreeSet::new(),
        });
        graph.add_terminal(TerminalRoot {
            id: "param-0".to_owned(),
            node: "external-param".to_owned(),
            kind: TerminalKind::ExternalParameter,
            label: "public::arg1".to_owned(),
            realloc: false,
            provenance_tags: BTreeSet::new(),
        });
        for source in ["alloc-result", "external-param", "dead-end"] {
            graph.add_edge(FlowEdge {
                source: source.to_owned(),
                target: "candidate".to_owned(),
                kind: FlowEdgeKind::Local,
                label: format!("{source}->candidate"),
                provenance_tags: BTreeSet::new(),
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
            provenance_tags: BTreeSet::new(),
        });
        graph.add_edge(FlowEdge {
            source: "external-param".to_owned(),
            target: "candidate".to_owned(),
            kind: FlowEdgeKind::Local,
            label: "param-store".to_owned(),
            provenance_tags: BTreeSet::new(),
        });
        graph.add_terminal(TerminalRoot {
            id: "external".to_owned(),
            node: "external-param".to_owned(),
            kind: TerminalKind::ExternalParameter,
            label: "public-arg".to_owned(),
            realloc: false,
            provenance_tags: BTreeSet::new(),
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

    #[test]
    fn indirect_hook_visible_default_expands_and_empty_target_stops() {
        let targets = [IndirectTargetSpec {
            canonical_path: "src::fixture::realloc".to_owned(),
            kind: TerminalKind::RecognizedAllocation,
            realloc: true,
        }];
        let roots = expand_indirect_target_roots("result", "fixture:bb4:call", &targets)
            .expect("visible default target must expand");
        assert_eq!(roots.len(), 1);
        assert_eq!(
            roots[0].provenance_tags,
            BTreeSet::from(["indirect-resolved-target(src::fixture::realloc)".to_owned()])
        );

        let mut graph = SourceGraph::default();
        for root in roots {
            graph.add_terminal(root);
        }
        graph.add_edge(FlowEdge {
            source: "result".to_owned(),
            target: "candidate".to_owned(),
            kind: FlowEdgeKind::Local,
            label: "field-store".to_owned(),
            provenance_tags: BTreeSet::new(),
        });
        let traced = trace_candidate(&graph, "candidate");
        assert_eq!(
            traced[0].evidence.flags,
            BTreeSet::from([CauseFlag::ReallocAllocation])
        );
        assert_eq!(
            traced[0].evidence.provenance_tags,
            BTreeSet::from(["indirect-resolved-target(src::fixture::realloc)".to_owned()])
        );
        let rendered = evidence_tokens(&traced[0].evidence).join("|");
        assert_eq!(
            parse_root_evidence(&rendered),
            Ok(traced[0].evidence.clone())
        );
        assert_eq!(
            classify_roots(
                &traced
                    .iter()
                    .map(|root| root.evidence.clone())
                    .collect::<Vec<_>>()
            ),
            PrimaryClass::Invisible,
            "the neutral target tag must not enter either R3 predicate"
        );

        assert!(
            expand_indirect_target_roots("result", "fixture:bb5:call", &[])
                .expect_err("an empty visible target set must STOP")
                .contains("visible target set is empty")
        );
        assert!(
            require_visible_targets::<u8>(&[], "fixture:bb5:call")
                .expect_err("the production target-set gate must STOP")
                .contains("visible target set is empty")
        );
    }

    #[test]
    fn indirect_empty_target_scope_is_data_pointer_sensitive() {
        assert_eq!(
            data_pointer_destination(false, None, "fixture:unit-callback:bb1:call"),
            Ok(None),
            "a unit-returning callback is outside the provenance-root population"
        );

        let unresolved_error =
            data_pointer_destination(true, None, "fixture:pointer-hook:bb2:call")
                .expect_err("a pointer result without a graph node must STOP");
        assert!(unresolved_error.contains("data-pointer result has no source-graph node"));

        assert_eq!(
            data_pointer_destination(
                true,
                Some("pointer-result"),
                "fixture:pointer-hook:bb3:call"
            ),
            Ok(Some("pointer-result"))
        );

        assert!(
            require_visible_targets::<u8>(&[], "fixture:pointer-hook:bb3:call")
                .expect_err("a pointer-returning empty hook must still STOP")
                .contains("visible target set is empty")
        );
    }

    #[test]
    fn indirect_call_taxonomy_is_a_closed_composition() {
        assert_eq!(
            indirect_call_arm(false, 0, false, false, false, false, "fixture:unit"),
            Ok(IndirectCallArm::OutOfPopulation)
        );
        assert_eq!(
            indirect_call_arm(true, 1, false, false, false, false, "fixture:visible"),
            Ok(IndirectCallArm::VisibleTargets)
        );
        assert_eq!(
            indirect_call_arm(true, 0, true, true, false, false, "fixture:external"),
            Ok(IndirectCallArm::ExternalParameterCallback)
        );
        assert_eq!(
            indirect_call_arm(true, 1, true, false, true, false, "fixture:both"),
            Ok(IndirectCallArm::VisibleTargetsAndExternalRemainder)
        );
        assert!(
            indirect_call_arm(true, 0, false, false, false, false, "fixture:fourth")
                .expect_err("a fourth shape must STOP")
                .contains("unclassified empty-target indirect call")
        );
        assert!(
            indirect_call_arm(true, 0, true, true, true, false, "fixture:external-static")
                .expect_err("a public-setter static without a visible target must STOP")
                .contains("unclassified empty-target indirect call")
        );
        assert!(
            indirect_call_arm(true, 1, false, false, false, true, "fixture:unexplained")
                .expect_err("an unexplained predecessor must STOP")
                .contains("unexplained predecessor")
        );

        let mut graph = SourceGraph::default();
        add_external_parameter_callback_root(
            &mut graph,
            "callback-result".to_owned(),
            "fixture:external",
        );
        let roots = trace_candidate(&graph, "callback-result");
        assert_eq!(
            roots[0].evidence.flags,
            BTreeSet::from([CauseFlag::OpaqueExternalCallResult])
        );
        assert_eq!(
            roots[0].evidence.provenance_tags,
            BTreeSet::from(["indirect-external-parameter-callback".to_owned()])
        );
        assert_eq!(
            classify_roots(
                &roots
                    .iter()
                    .map(|root| root.evidence.clone())
                    .collect::<Vec<_>>()
            ),
            PrimaryClass::Absent
        );

        let mut empty_only = IndirectTargetFlow::default();
        empty_only.add_empty_value_seed("none".to_owned());
        assert!(
            !empty_only.exclusively_external_parameter("none"),
            "a neutral empty value cannot make a non-external path external"
        );

        let mut external_with_none = IndirectTargetFlow::default();
        external_with_none.add_external_parameter_seed("external".to_owned());
        external_with_none.add_empty_value_seed("none".to_owned());
        external_with_none.add_edge("external".to_owned(), "call".to_owned());
        external_with_none.add_edge("none".to_owned(), "call".to_owned());
        assert!(external_with_none.exclusively_external_parameter("call"));

        let mut mixed_unresolved = external_with_none;
        mixed_unresolved.add_edge("unresolved".to_owned(), "call".to_owned());
        assert!(
            !mixed_unresolved.exclusively_external_parameter("call"),
            "a neutral empty path cannot conceal an unexplained predecessor"
        );
    }

    #[test]
    fn public_setter_remainder_has_mechanical_closed_and_open_readings() {
        let allocation = RootEvidence {
            flags: BTreeSet::from([CauseFlag::InterproceduralAllocation]),
            provenance_tags: BTreeSet::from(["indirect-resolved-target(malloc)".to_owned()]),
        };
        let external_remainder = RootEvidence {
            flags: BTreeSet::from([CauseFlag::OpaqueExternalCallResult]),
            provenance_tags: BTreeSet::from([PUBLIC_SETTER_REACHABLE_TAG.to_owned()]),
        };
        let reading = dual_reading(&[allocation.clone(), external_remainder.clone()]).unwrap();
        assert_eq!(reading.closed_world_class, PrimaryClass::Invisible);
        assert_eq!(reading.open_class, PrimaryClass::Mixed);
        assert_eq!(reading.closed_world_root_count, 1);
        assert_eq!(reading.open_root_count, 2);
        assert_eq!(reading.closed_world_evidence, allocation);
        assert!(
            reading
                .open_evidence
                .provenance_tags
                .contains(PUBLIC_SETTER_REACHABLE_TAG)
        );

        let visible_only = dual_reading(&[reading.closed_world_evidence.clone()]).unwrap();
        assert_eq!(visible_only.closed_world_class, visible_only.open_class);
        assert_eq!(visible_only.closed_world_root_count, 1);
        assert_eq!(visible_only.open_root_count, 1);

        assert!(
            dual_reading(&[external_remainder])
                .expect_err("external-only mutable static must STOP")
                .contains("no classified visible root")
        );

        let candidates = vec![vec![
            "binn".to_owned(),
            "src::fixture::Field@d0".to_owned(),
            "1".to_owned(),
            "ref".to_owned(),
            "mixed".to_owned(),
            "interprocedural-allocation|opaque-external-call-result|indirect-resolved-target(malloc)|public-setter-reachable".to_owned(),
            "2".to_owned(),
        ]];
        let roots = vec![
            vec![
                "census".to_owned(),
                "binn".to_owned(),
                "src::fixture::Field@d0".to_owned(),
                "store-1".to_owned(),
                "allocation".to_owned(),
                "malloc".to_owned(),
                "interprocedural-allocation|indirect-resolved-target(malloc)".to_owned(),
                "allocation -> store".to_owned(),
            ],
            vec![
                "census".to_owned(),
                "binn".to_owned(),
                "src::fixture::Field@d0".to_owned(),
                "store-1".to_owned(),
                "external".to_owned(),
                "setter".to_owned(),
                "opaque-external-call-result|public-setter-reachable".to_owned(),
                "external -> store".to_owned(),
            ],
        ];
        let rendered = render_candidate_readings(&candidates, &roots).unwrap();
        let cells = rendered
            .lines()
            .nth(1)
            .unwrap()
            .split('\t')
            .collect::<Vec<_>>();
        assert_eq!(cells[4], "invisible");
        assert_eq!(cells[5], "mixed");
        assert_eq!(cells[8], "1");
        assert_eq!(cells[9], "2");
    }

    #[test]
    fn indirect_resolved_flow_target_cannot_disappear() {
        let mut graph = SourceGraph::default();
        let tags = BTreeSet::from(["indirect-resolved-target(src::fixture::flow)".to_owned()]);
        add_indirect_value_edge(
            &mut graph,
            None,
            "candidate".to_owned(),
            "fixture:bb6:call".to_owned(),
            tags.clone(),
        );
        let roots = trace_candidate(&graph, "candidate");
        assert_eq!(roots.len(), 1);
        assert!(roots[0].evidence.flags.is_empty());
        assert_eq!(roots[0].evidence.provenance_tags, tags);
        assert_eq!(
            classify_roots(
                &roots
                    .iter()
                    .map(|root| root.evidence.clone())
                    .collect::<Vec<_>>()
            ),
            PrimaryClass::Unresolved,
            "a missing resolved flow source must STOP rather than vanish"
        );
    }

    #[test]
    fn mir_hook_target_collection_has_two_sided_witness() {
        let source = r#"
            unsafe extern "C" {
                fn realloc(p: *mut core::ffi::c_void, n: usize) -> *mut core::ffi::c_void;
            }
            struct Hook {
                call: Option<unsafe extern "C" fn(*mut core::ffi::c_void, usize) -> *mut core::ffi::c_void>,
            }
            unsafe fn init(hook: *mut Hook) {
                (*hook).call = Some(realloc as unsafe extern "C" fn(*mut core::ffi::c_void, usize) -> *mut core::ffi::c_void);
            }
            unsafe fn visible_default(hook: *mut Hook, p: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
                ((*hook).call).expect("visible default")(p, 8)
            }
            struct EmptyHook {
                call: Option<unsafe extern "C" fn(*mut core::ffi::c_void, usize) -> *mut core::ffi::c_void>,
            }
            unsafe fn empty_target(hook: *mut EmptyHook, p: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
                ((*hook).call).expect("no visible target")(p, 8)
            }
            struct UnitHook {
                call: Option<unsafe extern "C" fn(i32)>,
            }
            unsafe fn unit_callback(hook: *mut UnitHook) {
                ((*hook).call).expect("no visible unit target")(1)
            }
            pub unsafe fn external_callback(
                callback: Option<unsafe extern "C" fn(*mut core::ffi::c_void, usize) -> *mut core::ffi::c_void>,
                p: *mut core::ffi::c_void,
            ) -> *mut core::ffi::c_void {
                callback.expect("external callback")(p, 8)
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let resolutions = collect_indirect_call_resolutions(tcx, &program.functions);
            let by_function = |suffix: &str| {
                resolutions
                    .iter()
                    .filter(|((function, _), _)| tcx.def_path_str(*function).ends_with(suffix))
                    .map(|(_, resolution)| {
                        resolution
                            .visible_targets
                            .iter()
                            .map(|target| tcx.def_path_str(*target))
                            .collect::<BTreeSet<_>>()
                    })
                    .collect::<Vec<_>>()
            };
            let external_by_function = |suffix: &str| {
                resolutions
                    .iter()
                    .filter(|((function, _), _)| tcx.def_path_str(*function).ends_with(suffix))
                    .map(|(_, resolution)| resolution.exclusively_external_parameter)
                    .collect::<Vec<_>>()
            };
            assert_eq!(
                by_function("visible_default"),
                vec![BTreeSet::from(["realloc".to_owned()])]
            );
            assert_eq!(by_function("empty_target"), vec![BTreeSet::new()]);
            assert_eq!(by_function("unit_callback"), vec![BTreeSet::new()]);
            assert_eq!(by_function("external_callback"), vec![BTreeSet::new()]);
            assert_eq!(external_by_function("visible_default"), vec![false]);
            assert_eq!(external_by_function("empty_target"), vec![false]);
            assert_eq!(external_by_function("unit_callback"), vec![false]);
            assert_eq!(external_by_function("external_callback"), vec![true]);

            let call_scopes = |suffix: &str| {
                program
                    .functions
                    .iter()
                    .copied()
                    .filter(|function| tcx.def_path_str(*function).ends_with(suffix))
                    .flat_map(|function| {
                        let body_ref = tcx
                            .mir_drops_elaborated_and_const_checked(function)
                            .borrow();
                        let body = &*body_ref;
                        body.basic_blocks
                            .iter()
                            .filter_map(|data| harness_call(tcx, data.terminator()))
                            .filter(|call| matches!(call.kind, HarnessCallKind::Unresolved))
                            .map(|call| {
                                (
                                    call.destination.ty(body, tcx).ty.is_raw_ptr(),
                                    node_for_place(tcx, &slots, function, body, call.destination)
                                        .is_some(),
                                )
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            };
            assert_eq!(call_scopes("empty_target"), vec![(true, true)]);
            assert_eq!(call_scopes("unit_callback"), vec![(false, false)]);
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn mutable_static_hook_resolution_has_visible_external_and_stop_controls() {
        let source = r#"
            use core::ffi::c_void;

            extern "C" {
                fn malloc(size: usize) -> *mut c_void;
            }

            type Alloc = unsafe extern "C" fn(usize) -> *mut c_void;

            static mut VISIBLE_ONLY: Option<Alloc> = None;
            static mut PUBLIC_SETTER: Option<Alloc> = None;
            static mut NEITHER: Option<Alloc> = None;

            unsafe fn install_visible_only() {
                VISIBLE_ONLY = Some(malloc);
            }

            unsafe fn install_public_default() {
                if PUBLIC_SETTER.is_none() {
                    PUBLIC_SETTER = Some(malloc);
                }
            }

            pub unsafe extern "C" fn set_public_hook(hook: Option<Alloc>) {
                PUBLIC_SETTER = hook;
            }

            unsafe fn call_visible_only(size: usize) -> *mut c_void {
                install_visible_only();
                VISIBLE_ONLY.expect("visible only")(size)
            }

            unsafe fn call_public_setter(size: usize) -> *mut c_void {
                install_public_default();
                PUBLIC_SETTER.expect("visible plus external")(size)
            }

            unsafe fn call_neither(size: usize) -> *mut c_void {
                NEITHER.expect("unclassified")(size)
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let resolutions = collect_indirect_call_resolutions(tcx, &program.functions);
            let visible_targets = |suffix: &str| {
                resolutions
                    .iter()
                    .filter(|((function, _), _)| tcx.def_path_str(*function).ends_with(suffix))
                    .map(|(_, resolution)| {
                        resolution
                            .visible_targets
                            .iter()
                            .map(|target| tcx.def_path_str(*target))
                            .collect::<BTreeSet<_>>()
                    })
                    .collect::<Vec<_>>()
            };
            let resolution_for = |suffix: &str| {
                let mut matching = resolutions
                    .iter()
                    .filter(|((function, _), _)| tcx.def_path_str(*function).ends_with(suffix))
                    .map(|(_, resolution)| resolution)
                    .collect::<Vec<_>>();
                assert_eq!(matching.len(), 1, "one indirect call in {suffix}");
                matching.pop().unwrap()
            };

            assert_eq!(
                visible_targets("call_visible_only"),
                vec![BTreeSet::from(["malloc".to_owned()])],
                "a visible-only mutable global must expand its installed target"
            );
            assert_eq!(
                visible_targets("call_public_setter"),
                vec![BTreeSet::from(["malloc".to_owned()])],
                "a public-setter global must retain its visible default"
            );
            assert_eq!(
                visible_targets("call_neither"),
                vec![BTreeSet::new()],
                "the neither control must remain target-empty and later STOP"
            );

            let visible_only = resolution_for("call_visible_only");
            assert!(!visible_only.has_external_parameter);
            assert!(!visible_only.public_setter_reachable);
            assert!(!visible_only.has_unexplained_predecessor);
            assert_eq!(
                indirect_call_arm(true, 1, false, false, false, false, "visible-only"),
                Ok(IndirectCallArm::VisibleTargets)
            );

            let public_setter = resolution_for("call_public_setter");
            assert!(
                public_setter.has_external_parameter,
                "the public setter's external parameter must reach the static"
            );
            assert!(public_setter.public_setter_reachable);
            assert!(!public_setter.has_unexplained_predecessor);
            assert_eq!(
                indirect_call_arm(true, 1, true, false, true, false, "public-setter"),
                Ok(IndirectCallArm::VisibleTargetsAndExternalRemainder)
            );

            let neither = resolution_for("call_neither");
            assert!(!neither.has_external_parameter);
            assert!(!neither.public_setter_reachable);
            assert!(neither.has_unexplained_predecessor);
            assert!(
                indirect_call_arm(true, 0, false, false, false, true, "neither")
                    .expect_err("a static with neither source must STOP")
                    .contains("unexplained predecessor")
            );

            let mut dual_graph = SourceGraph::default();
            for root in expand_indirect_target_roots(
                "result",
                "fixture:public-setter",
                &[IndirectTargetSpec {
                    canonical_path: "malloc".to_owned(),
                    kind: TerminalKind::RecognizedAllocation,
                    realloc: false,
                }],
            )
            .unwrap()
            {
                dual_graph.add_terminal(root);
            }
            add_public_setter_remainder_root(
                &mut dual_graph,
                "result".to_owned(),
                "fixture:public-setter",
            );
            let dual_roots = trace_candidate(&dual_graph, "result");
            assert_eq!(dual_roots.len(), 2, "both path rows must be emitted");
            assert!(dual_roots.iter().any(|root| {
                root.evidence
                    .provenance_tags
                    .contains("public-setter-reachable")
                    && root
                        .evidence
                        .flags
                        .contains(&CauseFlag::OpaqueExternalCallResult)
            }));
            let reading = dual_reading(
                &dual_roots
                    .iter()
                    .map(|root| root.evidence.clone())
                    .collect::<Vec<_>>(),
            )
            .unwrap();
            assert_eq!(reading.closed_world_class, PrimaryClass::Invisible);
            assert_eq!(reading.open_class, PrimaryClass::Mixed);
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn field_stored_hook_resolution_reuses_visible_external_arm() {
        let source = r#"
            use core::ffi::c_void;

            extern "C" {
                fn malloc(size: usize) -> *mut c_void;
            }

            type Alloc = unsafe extern "C" fn(usize) -> *mut c_void;

            struct DualHook {
                alloc: Option<Alloc>,
            }

            struct VisibleHook {
                alloc: Option<Alloc>,
            }

            struct EmptyHook {
                alloc: Option<Alloc>,
            }

            unsafe extern "C" fn local_alloc(size: usize) -> *mut c_void {
                malloc(size)
            }

            unsafe fn install_dual_default(hook: *mut DualHook) {
                (*hook).alloc = Some(local_alloc);
            }

            pub unsafe extern "C" fn install_dual_external(
                hook: *mut DualHook,
                alloc: Option<Alloc>,
            ) {
                (*hook).alloc = alloc;
            }

            unsafe fn install_visible(hook: *mut VisibleHook) {
                (*hook).alloc = Some(local_alloc);
            }

            unsafe fn call_dual(hook: *mut DualHook) -> *mut c_void {
                install_dual_default(hook);
                (*hook).alloc.expect("dual")(8)
            }

            unsafe fn call_visible(hook: *mut VisibleHook) -> *mut c_void {
                install_visible(hook);
                (*hook).alloc.expect("visible")(8)
            }

            unsafe fn call_empty(hook: *mut EmptyHook) -> *mut c_void {
                (*hook).alloc.expect("empty")(8)
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let resolutions = collect_indirect_call_resolutions(tcx, &program.functions);
            let resolution_for = |suffix: &str| {
                let mut matching = resolutions
                    .iter()
                    .filter(|((function, _), _)| tcx.def_path_str(*function).ends_with(suffix))
                    .map(|(_, resolution)| resolution)
                    .collect::<Vec<_>>();
                assert_eq!(matching.len(), 1, "one indirect call in {suffix}");
                matching.pop().unwrap()
            };
            let target_paths = |resolution: &IndirectCallResolution| {
                resolution
                    .visible_targets
                    .iter()
                    .map(|target| tcx.def_path_str(*target))
                    .collect::<BTreeSet<_>>()
            };

            let dual = resolution_for("call_dual");
            assert_eq!(target_paths(dual), BTreeSet::from(["local_alloc".to_owned()]));
            assert!(dual.has_external_parameter);
            assert!(
                dual.public_setter_reachable,
                "a public parameter reaching the same field is the existing external remainder: {:#?}",
                dual.diagnostic
            );
            assert!(!dual.has_unexplained_predecessor);
            assert_eq!(
                indirect_call_arm(
                    true,
                    dual.visible_targets.len(),
                    dual.has_external_parameter,
                    dual.exclusively_external_parameter,
                    dual.public_setter_reachable,
                    dual.has_unexplained_predecessor,
                    "field-dual",
                ),
                Ok(IndirectCallArm::VisibleTargetsAndExternalRemainder)
            );

            let visible = resolution_for("call_visible");
            assert_eq!(
                target_paths(visible),
                BTreeSet::from(["local_alloc".to_owned()])
            );
            assert!(!visible.has_external_parameter);
            assert!(!visible.public_setter_reachable);
            assert!(!visible.has_unexplained_predecessor);
            assert_eq!(
                indirect_call_arm(true, 1, false, false, false, false, "field-visible"),
                Ok(IndirectCallArm::VisibleTargets)
            );

            let empty = resolution_for("call_empty");
            assert!(empty.visible_targets.is_empty());
            assert!(!empty.has_external_parameter);
            assert!(empty.has_unexplained_predecessor);
            assert!(
                indirect_call_arm(true, 0, false, false, false, true, "field-empty")
                    .expect_err("the field with neither source must STOP")
                    .contains("unexplained predecessor")
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn indirect_targets_are_filtered_by_call_site_signature_without_choosing() {
        let source = r#"
            type Erased = Option<unsafe extern "C" fn()>;
            type PointerHook = Option<unsafe extern "C" fn(usize) -> *mut u8>;
            type UnitHook = Option<unsafe extern "C" fn(usize)>;

            struct Hooks {
                callback: Erased,
            }

            unsafe extern "C" fn unit_target(_size: usize) {}

            unsafe extern "C" fn pointer_target_a(_size: usize) -> *mut u8 {
                core::ptr::null_mut()
            }

            unsafe extern "C" fn pointer_target_b(_size: usize) -> *mut u8 {
                core::ptr::null_mut()
            }

            unsafe fn install_all(hooks: *mut Hooks) {
                (*hooks).callback = core::mem::transmute::<UnitHook, Erased>(Some(unit_target));
                (*hooks).callback =
                    core::mem::transmute::<PointerHook, Erased>(Some(pointer_target_a));
                (*hooks).callback =
                    core::mem::transmute::<PointerHook, Erased>(Some(pointer_target_b));
            }

            unsafe fn call_pointer(hooks: *mut Hooks) -> *mut u8 {
                install_all(hooks);
                let callback = core::mem::transmute::<Erased, PointerHook>((*hooks).callback);
                callback.expect("pointer callback")(1)
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let resolutions = collect_indirect_call_resolutions(tcx, &program.functions);
            let mut matching = resolutions
                .iter()
                .filter(|((function, _), _)| {
                    tcx.def_path_str(*function).ends_with("call_pointer")
                })
                .map(|(_, resolution)| resolution)
                .collect::<Vec<_>>();
            assert_eq!(matching.len(), 1, "one indirect pointer call");
            let targets = matching
                .pop()
                .unwrap()
                .visible_targets
                .iter()
                .map(|target| tcx.def_path_str(*target))
                .collect::<BTreeSet<_>>();

            assert!(
                !targets.contains("unit_target"),
                "RED-exclude: a unit-returning target is incompatible with a pointer result: {targets:?}"
            );
            assert!(
                targets.contains("pointer_target_a"),
                "RED-include: a signature-compatible target must remain: {targets:?}"
            );
            assert_eq!(
                targets,
                BTreeSet::from([
                    "pointer_target_a".to_owned(),
                    "pointer_target_b".to_owned(),
                ]),
                "ambiguity control: all compatible targets must remain"
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn reference_mediated_callback_store_is_external_only() {
        let source = r#"
            use core::ffi::c_void;

            type Callback = Option<unsafe extern "C" fn() -> *mut c_void>;

            struct Registered {
                callbacks: [Callback; 2],
            }

            struct Empty {
                callbacks: [Callback; 2],
            }

            pub unsafe extern "C" fn register(
                hooks: *mut Registered,
                index: usize,
                callback: Callback,
            ) {
                let ref mut slot = (*hooks).callbacks[index];
                *slot = callback;
            }

            unsafe fn call_registered(hooks: *mut Registered) -> *mut c_void {
                (*hooks).callbacks[0].expect("registered")()
            }

            unsafe fn call_empty(hooks: *mut Empty) -> *mut c_void {
                (*hooks).callbacks[0].expect("empty")()
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let resolutions = collect_indirect_call_resolutions(tcx, &program.functions);
            let resolution_for = |suffix: &str| {
                let mut matching = resolutions
                    .iter()
                    .filter(|((function, _), _)| tcx.def_path_str(*function).ends_with(suffix))
                    .map(|(_, resolution)| resolution)
                    .collect::<Vec<_>>();
                assert_eq!(matching.len(), 1, "one indirect call in {suffix}");
                matching.pop().unwrap()
            };

            let registered = resolution_for("call_registered");
            assert!(registered.visible_targets.is_empty());
            assert!(
                registered.has_external_parameter,
                "the reference-mediated public setter must reach the callback field: {:#?}",
                registered.diagnostic
            );
            assert!(registered.exclusively_external_parameter);
            assert!(!registered.public_setter_reachable);
            assert!(!registered.has_unexplained_predecessor);
            assert_eq!(
                indirect_call_arm(true, 0, true, true, false, false, "reference-store"),
                Ok(IndirectCallArm::ExternalParameterCallback)
            );

            let empty = resolution_for("call_empty");
            assert!(empty.visible_targets.is_empty());
            assert!(!empty.has_external_parameter);
            assert!(empty.has_unexplained_predecessor);
            assert!(
                indirect_call_arm(true, 0, false, false, false, true, "empty-reference")
                    .expect_err("a callback field with no realized store must STOP")
                    .contains("unexplained predecessor")
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn callback_reference_alias_conflicts_and_projected_stores_stop() {
        let mut aliases = FxHashMap::default();
        let local = Local::from_usize(1);
        insert_target_reference_alias(&mut aliases, local, "field-a".to_owned()).unwrap();
        assert!(
            insert_target_reference_alias(&mut aliases, local, "field-b".to_owned())
                .expect_err("one reference local cannot select two callback fields")
                .contains("conflicting referents")
        );

        let source = r#"
            use core::ffi::c_void;

            type Callback = Option<unsafe extern "C" fn() -> *mut c_void>;

            struct Hooks {
                callbacks: [Callback; 2],
            }

            unsafe fn projected_store(hooks: *mut Hooks, callback: Callback) {
                let slot = &mut (*hooks).callbacks;
                (*slot)[0] = callback;
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let function = program
                .functions
                .iter()
                .copied()
                .find(|function| tcx.def_path_str(*function).ends_with("projected_store"))
                .expect("projected-store fixture function");
            let body_ref = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let static_pointers = static_pointer_locals(tcx, &body_ref).unwrap();
            let aliases =
                target_reference_aliases(tcx, function, &body_ref, &static_pointers).unwrap();
            let lhs = body_ref
                .basic_blocks
                .iter()
                .flat_map(|data| &data.statements)
                .find_map(|statement| {
                    let StatementKind::Assign(box (lhs, _)) = &statement.kind else {
                        return None;
                    };
                    (lhs.projection.len() > 1
                        && matches!(lhs.projection.first(), Some(ProjectionElem::Deref)))
                    .then_some(*lhs)
                })
                .expect("projected dereference store");
            assert!(
                target_assignment_node(tcx, function, &body_ref, &static_pointers, &aliases, lhs,)
                    .expect_err("an additional projection on a callback alias must STOP")
                    .contains("unsupported projected callback-reference store")
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn realized_same_type_alias_store_reaches_later_base_load() {
        let source = r#"
            use core::ffi::c_void;

            extern "C" {
                fn calloc(count: usize, size: usize) -> *mut c_void;
                fn realloc(pointer: *mut c_void, size: usize) -> *mut c_void;
            }

            struct Item {
                value: i32,
            }

            struct LiveContainer {
                entries: *mut *mut Item,
            }

            struct EmptyContainer {
                entries: *mut *mut Item,
            }

            struct LiveHolder {
                current: *mut Item,
            }

            struct EmptyHolder {
                current: *mut Item,
            }

            unsafe fn install_live(container: *mut LiveContainer) {
                let item = calloc(1, core::mem::size_of::<Item>()) as *mut Item;
                let entries = realloc(
                    (*container).entries as *mut c_void,
                    core::mem::size_of::<*mut Item>(),
                ) as *mut *mut Item;
                (*container).entries = entries;
                *entries.offset(0) = item;
            }

            unsafe fn find_live(container: *mut LiveContainer) -> *mut Item {
                *(*container).entries.offset(0)
            }

            unsafe fn find_empty(container: *mut EmptyContainer) -> *mut Item {
                *(*container).entries.offset(0)
            }

            unsafe fn restore_live(holder: *mut LiveHolder, container: *mut LiveContainer) {
                (*holder).current = find_live(container);
            }

            unsafe fn restore_empty(holder: *mut EmptyHolder, container: *mut EmptyContainer) {
                (*holder).current = find_empty(container);
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_, captured_export) = with_bo_export(|| {
                emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("fixture ownership emission")
            });
            let graph = build_source_graph(tcx, &slots, &captured_export);
            let fields = candidate_fields(tcx, &slots);
            let field = |suffix: &str| {
                fields
                    .keys()
                    .find(|key| key.ends_with(suffix))
                    .unwrap_or_else(|| panic!("fixture field missing: {suffix}"))
                    .clone()
            };

            let live = trace_candidate(&graph, &field("LiveHolder::field0@d0"));
            assert!(
                !live.is_empty() && live.iter().all(|root| !root.evidence.flags.is_empty()),
                "the realized offset-alias store must reach only existing terminals: {live:#?}"
            );
            assert_ne!(
                classify_roots(
                    &live
                        .iter()
                        .map(|root| root.evidence.clone())
                        .collect::<Vec<_>>()
                ),
                PrimaryClass::Unresolved
            );

            let empty = trace_candidate(&graph, &field("EmptyHolder::field0@d0"));
            assert!(
                empty.iter().any(|root| root.evidence.flags.is_empty()),
                "the base with no realized element store must stay unresolved"
            );
            assert_eq!(
                classify_roots(
                    &empty
                        .iter()
                        .map(|root| root.evidence.clone())
                        .collect::<Vec<_>>()
                ),
                PrimaryClass::Unresolved
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn non_pointer_alias_payload_store_is_out_of_pointer_graph() {
        let source = r#"
            use core::ffi::c_void;

            extern "C" {
                fn realloc(pointer: *mut c_void, size: usize) -> *mut c_void;
            }

            unsafe fn write_byte(buffer: *mut u8, byte: u8) -> *mut u8 {
                let resized = realloc(buffer.cast(), 2).cast::<u8>();
                let alias = resized.offset(1);
                *alias = byte;
                resized
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let slots = CrateSlots::build(&program);
            build_source_graph(tcx, &slots, &BoExport::default());
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn projected_pointer_alias_store_uses_only_existing_graph_places() {
        let represented = r#"
            struct Holder {
                pointer: *mut u8,
            }

            pub unsafe fn store(holder: *mut Holder, source: *mut u8) {
                let alias = holder;
                (*alias).pointer = source;
            }
        "#;
        ::utils::compilation::run_compiler_on_str(represented, |tcx| {
            let program = super::super::collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let graph = build_source_graph(tcx, &slots, &BoExport::default());
            let field = candidate_fields(tcx, &slots)
                .keys()
                .find(|key| key.ends_with("Holder::field0@d0"))
                .expect("fixture pointer field")
                .clone();
            let roots = trace_candidate(&graph, &field);
            assert!(roots.iter().any(|root| {
                root.evidence
                    .flags
                    .contains(&CauseFlag::ExternallySuppliedParameter)
            }));
        })
        .unwrap_or_else(|error| error.raise());

        let unsupported = r#"
            struct ScalarHolder {
                value: u8,
            }

            pub unsafe fn store(holder: *mut ScalarHolder, value: u8) {
                let alias = holder;
                (*alias).value = value;
            }
        "#;
        ::utils::compilation::run_compiler_on_str(unsupported, |tcx| {
            let program = super::super::collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let function = program
                .functions
                .iter()
                .copied()
                .find(|function| tcx.def_path_str(*function).ends_with("store"))
                .expect("fixture store function");
            let body_ref = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            assert!(
                add_realized_pointer_alias_store_edges(
                    &mut SourceGraph::default(),
                    tcx,
                    &slots,
                    function,
                    &body_ref,
                )
                .expect_err("a projected alias store without a pointer node must STOP")
                .contains("unsupported projected realized pointer-alias store")
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn static_cached_data_pointer_alias_has_source_and_empty_controls() {
        let source = r#"
            struct Live {
                pointer: *mut u32,
            }

            struct Empty {
                pointer: *mut u32,
            }

            struct LocalPointer(*mut u32);

            impl LocalPointer {
                unsafe fn offset(self, _amount: isize) -> *mut u32 {
                    self.0
                }
            }

            static mut LIVE_POOL: [*mut *mut u32; 1] = [core::ptr::null_mut(); 1];
            static mut EMPTY_POOL: [*mut *mut u32; 1] = [core::ptr::null_mut(); 1];
            static mut SCALAR: u32 = 0;

            pub unsafe fn seed_live(value: *mut Live, source: *mut u32) {
                (*value).pointer = source;
            }

            pub unsafe fn install_live_pool(pool: *mut *mut u32) {
                LIVE_POOL[0] = pool;
            }

            pub unsafe fn cache_live(value: *mut Live) {
                let pool = LIVE_POOL[0];
                *pool.offset(0) = (*value).pointer;
            }

            pub unsafe fn restore_live(value: *mut Live) {
                let pool = LIVE_POOL[0];
                (*value).pointer = *pool.offset(0);
            }

            pub unsafe fn restore_empty(value: *mut Empty) {
                let pool = EMPTY_POOL[0];
                (*value).pointer = *pool.offset(0);
            }

            pub unsafe fn call_local_offset(source: *mut u32) -> *mut u32 {
                LocalPointer(source).offset(0)
            }

            pub unsafe fn raw_address_roundtrip() -> *mut u32 {
                let pointer = &raw mut SCALAR;
                &raw mut *pointer
            }

            pub unsafe fn depth_changing_cast() -> *mut u8 {
                let pointer = &raw mut SCALAR;
                pointer as *mut u8
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let graph = build_source_graph(tcx, &slots, &BoExport::default());
            let function = |suffix: &str| {
                program
                    .functions
                    .iter()
                    .copied()
                    .find(|function| tcx.def_path_str(*function).ends_with(suffix))
                    .unwrap_or_else(|| panic!("fixture function missing: {suffix}"))
            };
            let core_offset = function("cache_live");
            let core_body_ref = tcx
                .mir_drops_elaborated_and_const_checked(core_offset)
                .borrow();
            let core_call = core_body_ref
                .basic_blocks
                .iter()
                .filter_map(|data| harness_call(tcx, data.terminator()))
                .find_map(|call| match call.kind {
                    HarnessCallKind::RustLib(callee)
                        if tcx.item_name(callee).as_str() == "offset" =>
                    {
                        Some((callee, call))
                    }
                    _ => None,
                })
                .expect("core pointer offset call missing");
            assert!(is_static_data_pointer_flow_call(
                tcx,
                core_call.0,
                core_call.1.args[0].node.ty(&*core_body_ref, tcx),
                core_call.1.destination.ty(&*core_body_ref, tcx).ty,
            ));

            let local_offset = function("call_local_offset");
            let local_body_ref = tcx
                .mir_drops_elaborated_and_const_checked(local_offset)
                .borrow();
            let local_callee = local_body_ref
                .basic_blocks
                .iter()
                .filter_map(|data| harness_call(tcx, data.terminator()))
                .find_map(|call| match call.kind {
                    HarnessCallKind::Local(callee)
                        if tcx.item_name(callee.to_def_id()).as_str() == "offset" =>
                    {
                        Some(callee.to_def_id())
                    }
                    _ => None,
                })
                .expect("same-named local offset call missing");
            let pointer_ty = local_body_ref.return_ty();
            assert!(
                !is_static_data_pointer_flow_call(tcx, local_callee, pointer_ty, pointer_ty),
                "a same-named local method must not match the Rust library boundary"
            );

            let derive = |suffix: &str| {
                let function = function(suffix);
                let body_ref = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let seeds = static_pointer_locals(tcx, &body_ref).unwrap();
                let derivations = derive_static_data_locals(tcx, function, &body_ref).unwrap();
                (seeds, derivations)
            };
            let (roundtrip_seeds, roundtrip_derivations) = derive("raw_address_roundtrip");
            assert_eq!(roundtrip_seeds.len(), 1);
            let (&seed_local, &static_did) = roundtrip_seeds.iter().next().unwrap();
            assert_eq!(
                roundtrip_derivations.get(&seed_local),
                Some(&StaticDataDerivation {
                    static_did,
                    depth_offset: -1,
                })
            );
            assert_eq!(
                roundtrip_derivations.get(&RETURN_PLACE),
                roundtrip_derivations.get(&seed_local),
                "one deref plus one raw-address step must preserve static identity and depth"
            );

            let (cast_seeds, cast_derivations) = derive("depth_changing_cast");
            assert_eq!(cast_seeds.len(), 1);
            assert!(
                !cast_derivations.contains_key(&RETURN_PLACE),
                "a depth-changing cast must not enter the static-data derivation"
            );
            let fields = candidate_fields(tcx, &slots);
            let field = |suffix: &str| {
                fields
                    .keys()
                    .find(|key| key.ends_with(suffix))
                    .unwrap_or_else(|| panic!("fixture field missing: {suffix}"))
                    .clone()
            };

            let live = trace_candidate(&graph, &field("Live::field0@d0"));
            assert!(
                !live.is_empty() && live.iter().all(|root| !root.evidence.flags.is_empty()),
                "the static cache path must reach only existing terminals: {live:#?}"
            );
            assert_ne!(
                classify_roots(
                    &live
                        .iter()
                        .map(|root| root.evidence.clone())
                        .collect::<Vec<_>>()
                ),
                PrimaryClass::Unresolved
            );

            let empty = trace_candidate(&graph, &field("Empty::field0@d0"));
            assert!(
                empty.iter().any(|root| root.evidence.flags.is_empty()),
                "a static-loaded pointer with no visible store must remain unresolved"
            );
            assert_eq!(
                classify_roots(
                    &empty
                        .iter()
                        .map(|root| root.evidence.clone())
                        .collect::<Vec<_>>()
                ),
                PrimaryClass::Unresolved
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn unsupported_static_data_projection_stops() {
        let source = r#"
            struct Holder {
                pointer: *mut u32,
            }

            static mut HOLDER: Holder = Holder {
                pointer: core::ptr::null_mut(),
            };

            pub unsafe fn unsupported_projection() -> *mut u32 {
                let holder = &raw mut HOLDER;
                (*holder).pointer
            }

            pub unsafe fn unrelated_projection(holder: *mut Holder) -> *mut u32 {
                (*holder).pointer
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let derive = |suffix: &str| {
                let function = program
                    .functions
                    .iter()
                    .copied()
                    .find(|function| tcx.def_path_str(*function).ends_with(suffix))
                    .unwrap_or_else(|| panic!("fixture function missing: {suffix}"));
                let body_ref = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let seeds = static_pointer_locals(tcx, &body_ref).unwrap();
                let mut assignments = Vec::new();
                for (bb, data) in body_ref.basic_blocks.iter_enumerated() {
                    for (statement_index, statement) in data.statements.iter().enumerate() {
                        let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                            continue;
                        };
                        assignments.push(format!(
                            "bb{}[{statement_index}] lhs={lhs:?} rvalue={rvalue:?} seed={:?}",
                            bb.index(),
                            seeds.get(&lhs.local)
                        ));
                    }
                }
                (
                    derive_static_data_locals(tcx, function, &body_ref),
                    assignments,
                )
            };

            let (result, assignments) = derive("unsupported_projection");
            let error = match result {
                Err(error) => error,
                Ok(derived) => panic!(
                    "a field projection on a known static-derived base must STOP; derived={derived:?}; MIR assignments:\n{}",
                    assignments.join("\n")
                ),
            };
            assert!(
                error.contains("unsupported static-data projection"),
                "unexpected STOP: {error}"
            );
            assert!(
                derive("unrelated_projection").0.is_ok(),
                "a field projection on a non-derived base is outside the static-data bridge"
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn exact_json_callback_shape_is_externally_rooted() {
        let source = r#"
            pub mod src {
                pub mod json {
                    use core::ffi::c_void;

                    extern "C" {
                        fn malloc(size: usize) -> *mut c_void;
                    }

                    #[no_mangle]
                    pub unsafe extern "C" fn json_parse_ex(
                        mut src: *const c_void,
                        mut src_size: usize,
                        mut flags_bitset: usize,
                        mut alloc_func_ptr: Option<
                            unsafe extern "C" fn(*mut c_void, usize) -> *mut c_void,
                        >,
                        mut user_data: *mut c_void,
                        mut result: *mut c_void,
                    ) -> *mut c_void {
                        let _ = (&mut src, &mut src_size, &mut flags_bitset, &mut result);
                        let allocation;
                        if alloc_func_ptr.is_none() {
                            allocation = malloc(src_size);
                        } else {
                            allocation = alloc_func_ptr
                                .expect("non-null function pointer")(user_data, src_size);
                        }
                        allocation
                    }

                    #[no_mangle]
                    pub unsafe extern "C" fn json_parse(
                        src: *const c_void,
                        src_size: usize,
                    ) -> *mut c_void {
                        json_parse_ex(
                            src,
                            src_size,
                            0,
                            None,
                            core::ptr::null_mut(),
                            core::ptr::null_mut(),
                        )
                    }
                }
            }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let resolutions = collect_indirect_call_resolutions(tcx, &program.functions);
            let mut callback_resolutions = resolutions
                .iter()
                .filter(|((function, _), _)| {
                    tcx.def_path_str(*function)
                        .ends_with("src::json::json_parse_ex")
                })
                .map(|(_, resolution)| resolution)
                .collect::<Vec<_>>();
            assert_eq!(
                callback_resolutions.len(),
                1,
                "the exact fixture must contain one indirect callback"
            );
            let resolution = callback_resolutions.pop().unwrap();
            assert!(
                resolution.visible_targets.is_empty(),
                "the external callback must not acquire a visible target: {:?}",
                resolution.diagnostic
            );
            assert!(
                resolution.exclusively_external_parameter,
                "the exact callback must be externally rooted:\n{}",
                resolution.diagnostic.join("\n")
            );
            assert!(
                resolution
                    .diagnostic
                    .iter()
                    .any(|row| row.contains("src::json::json_parse:slot5")
                        && row.contains("empty_value_seed=true")),
                "the wrapper's literal None must be the diagnosed neutral edge:\n{}",
                resolution.diagnostic.join("\n")
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn verified_skip_predecessor_is_exactly_manifest_pinned() {
        let current = "new-head";
        for &(program, head, manifest) in &RETRY3_PREDECESSOR_SHARDS {
            assert!(validate_receipt_head(program, head, manifest, current).is_ok());
            assert!(validate_receipt_head("wrong-program", head, manifest, current).is_err());
            assert!(validate_receipt_head(program, "wrong-head", manifest, current).is_err());
            assert!(validate_receipt_head(program, head, "wrong-manifest", current).is_err());
        }
        assert!(validate_receipt_head("bst", current, "any-current-manifest", current).is_ok());
        assert!(
            validate_receipt_head(
                "libcsv",
                "ce11b3459c6fa46965e4cbe23ce11dffbdc7bf01",
                "668568ac540b2114f0b4f19728daaa82c69b5d4d7de88130ee77ba86531ff3bf",
                current,
            )
            .is_err(),
            "the data=false predecessor shard is never skippable"
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
