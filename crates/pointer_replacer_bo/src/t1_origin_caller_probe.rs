//! T1 closed-world origin/caller market probe (measurement-only).

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
    path::Path,
    time::{Duration, Instant},
};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{Body, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::TyCtxt,
};

use crate::{
    analyses::borrow_ownership::{
        a5_overlap::WholeProgramAttestation,
        a5_producer::{ClosedWorldCallWorld, resolve_closed_world_call_world},
        boundary_table,
        construction::{CopyLendMode, construct_bo_into},
        crate_slots::CrateSlots,
        export::with_bo_export,
        l2::SlotKey,
        mutability_facts::MutFacts,
        origin_flow::OriginFlowResults,
        origin_summary::OriginSummaries,
        resolve::{ResolvedSlot, resolve_place},
        slots::SlotOwner,
        solver::{KindSolver, SlotRef},
        sources::collect_malloc_source_slots,
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct LicP1Key {
    program: String,
    function: String,
    lhs: SlotKey,
    rhs: SlotKey,
}

impl LicP1Key {
    fn slot_text(slot: SlotKey) -> String {
        match slot.variant {
            0 => format!("field:{}", slot.slot),
            1 => format!("local:{}:{}", slot.owner, slot.slot),
            variant => format!("invalid:{variant}:{}:{}", slot.owner, slot.slot),
        }
    }

    fn diagnostic(&self) -> String {
        format!(
            "{}|{}|{}|{}",
            self.program,
            self.function,
            Self::slot_text(self.lhs),
            Self::slot_text(self.rhs)
        )
    }
}

#[derive(Clone, Debug)]
struct LicP1Target {
    key: LicP1Key,
}

fn parse_slot_key(text: &str) -> Result<SlotKey, String> {
    let parts = text.split(':').collect::<Vec<_>>();
    match parts.as_slice() {
        ["field", slot] => Ok(SlotKey {
            variant: 0,
            owner: 0,
            slot: slot
                .parse()
                .map_err(|_| format!("invalid field slot {text}"))?,
        }),
        ["local", owner, slot] => Ok(SlotKey {
            variant: 1,
            owner: owner
                .parse()
                .map_err(|_| format!("invalid local owner {text}"))?,
            slot: slot
                .parse()
                .map_err(|_| format!("invalid local slot {text}"))?,
        }),
        _ => Err(format!("invalid LIC-P1 slot key {text}")),
    }
}

fn parse_lic_p1_targets(text: &str, program: &str) -> Result<Vec<LicP1Target>, String> {
    let mut lines = text.lines();
    let header = lines.next().ok_or("missing LIC-P1 header")?;
    let columns = header
        .split('\t')
        .enumerate()
        .map(|(index, name)| (name, index))
        .collect::<BTreeMap<_, _>>();
    let get = |fields: &[&str], name: &str| -> Result<String, String> {
        let index = columns
            .get(name)
            .ok_or_else(|| format!("missing LIC-P1 column {name}"))?;
        fields
            .get(*index)
            .map(|value| (*value).to_owned())
            .ok_or_else(|| format!("short LIC-P1 row at {name}"))
    };
    let mut keys = BTreeSet::new();
    let mut answer = Vec::new();
    for line in lines.filter(|line| !line.is_empty()) {
        let fields = line.split('\t').collect::<Vec<_>>();
        if get(&fields, "program")? != program
            || get(&fields, "bucket")? != "token-cannot-exist"
            || get(&fields, "subbucket")? != "unknown-origin"
        {
            continue;
        }
        let key = LicP1Key {
            program: program.to_owned(),
            function: get(&fields, "function")?,
            lhs: parse_slot_key(&get(&fields, "lhs")?)?,
            rhs: parse_slot_key(&get(&fields, "rhs")?)?,
        };
        if !keys.insert(key.clone()) {
            return Err(format!("duplicate LIC-P1 key {}", key.diagnostic()));
        }
        answer.push(LicP1Target { key });
    }
    answer.sort_by(|left, right| left.key.cmp(&right.key));
    Ok(answer)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EndpointDisposition {
    Unique,
    Indeterminate,
}

fn endpoint_disposition(matches: usize) -> EndpointDisposition {
    if matches == 1 {
        EndpointDisposition::Unique
    } else {
        EndpointDisposition::Indeterminate
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Inflow {
    Alloc,
    NonAlloc,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Verdict {
    Yes,
    No,
    Indeterminate,
}

fn join_inflows(inflows: &[Inflow]) -> Verdict {
    if inflows.is_empty() || inflows.iter().any(|inflow| *inflow == Inflow::Unknown) {
        Verdict::Indeterminate
    } else if inflows.iter().any(|inflow| *inflow == Inflow::NonAlloc) {
        Verdict::No
    } else {
        Verdict::Yes
    }
}

const LOCAL_CHAIN_LIMIT: usize = 32;

struct LocalDefChain {
    definitions: FxHashMap<Local, Vec<Option<Local>>>,
    allocator_destinations: FxHashSet<Local>,
}

impl LocalDefChain {
    fn new(tcx: rustc_middle::ty::TyCtxt<'_>, body: &Body<'_>) -> Self {
        let mut definitions: FxHashMap<Local, Vec<Option<Local>>> = FxHashMap::default();
        let mut allocator_destinations = FxHashSet::default();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let Some(destination) = assign.0.as_local() else {
                    continue;
                };
                let source = match &assign.1 {
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                    | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                        if place.projection.is_empty() =>
                    {
                        Some(place.local)
                    }
                    _ => None,
                };
                definitions.entry(destination).or_default().push(source);
            }
            let TerminatorKind::Call {
                func, destination, ..
            } = &data.terminator().kind
            else {
                continue;
            };
            let Some(destination) = destination.as_local() else {
                continue;
            };
            let Some((callee, _)) = func.const_fn_def() else {
                continue;
            };
            let Some(callee) = callee.as_local() else {
                continue;
            };
            let rustc_hir::Node::ForeignItem(item) = tcx.hir_node_by_def_id(callee) else {
                continue;
            };
            if boundary_table::sources_foreign().any(|name| name == item.ident.as_str()) {
                allocator_destinations.insert(destination);
            }
        }
        Self {
            definitions,
            allocator_destinations,
        }
    }

    fn terminal(&self, mut local: Local) -> Option<(Local, bool)> {
        self.trace(local).1
    }

    fn trace(&self, mut local: Local) -> (Vec<Local>, Option<(Local, bool)>) {
        let mut seen = FxHashSet::default();
        let mut chain = vec![local];
        for _ in 0..LOCAL_CHAIN_LIMIT {
            if !seen.insert(local) {
                return (chain, None);
            }
            if self.allocator_destinations.contains(&local) {
                return (chain, Some((local, true)));
            }
            let Some(definitions) = self.definitions.get(&local) else {
                return (chain, Some((local, false)));
            };
            if definitions.len() != 1 {
                return (chain, None);
            }
            let Some(next) = definitions[0] else {
                return (chain, Some((local, false)));
            };
            local = next;
            chain.push(local);
        }
        (chain, None)
    }
}

fn resolved_actual_slot(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    slots: &CrateSlots,
    caller: rustc_span::def_id::LocalDefId,
    body: &Body<'_>,
    operand: &Operand<'_>,
) -> Option<SlotRef> {
    let place = operand.place()?;
    if !place.projection.is_empty() {
        return None;
    }
    let (local, _allocator_rooted) = LocalDefChain::new(tcx, body).terminal(place.local)?;
    let slot = slots
        .fn_local_slots
        .get(&caller)?
        .slot_for_local_depth(local, 0)?;
    Some(SlotRef::Local(caller, slot))
}

#[derive(Clone, Debug)]
struct SinkEndpoint {
    function: rustc_span::def_id::LocalDefId,
    location: crate::analyses::borrow_ownership::l2::MirLocationKey,
    callee: String,
    operand_local: Local,
    chain: Vec<Local>,
    local: Local,
    load_slot: Option<SlotRef>,
}

fn single_load_slot(
    slots: &CrateSlots,
    function: rustc_span::def_id::LocalDefId,
    body: &Body<'_>,
    local: Local,
) -> Option<SlotRef> {
    let mut definitions = 0usize;
    let mut loaded = None;
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            if assign.0.as_local() != Some(local) {
                continue;
            }
            definitions += 1;
            let place = match &assign.1 {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                | Rvalue::CopyForDeref(place)
                    if !place.projection.is_empty() =>
                {
                    *place
                }
                _ => continue,
            };
            loaded = match resolve_place(slots, function, body, place, 0, None)? {
                ResolvedSlot::Local(slot) => Some(SlotRef::Local(function, slot)),
                ResolvedSlot::Field(slot) => Some(SlotRef::Field(slot)),
            };
        }
    }
    (definitions == 1).then_some(loaded).flatten()
}

fn capture_sink_endpoints(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    facts: &MutFacts,
) -> Result<FxHashMap<SlotRef, Vec<SinkEndpoint>>, String> {
    let solver = KindSolver::new(slots);
    let (construction, export) = with_bo_export(|| {
        construct_bo_into(
            program,
            slots,
            origins,
            facts,
            &solver,
            CopyLendMode::Baseline,
        )
    });
    construction.map_err(|error| format!("T1 endpoint construction: {error:#}"))?;
    let mut answer: FxHashMap<SlotRef, Vec<SinkEndpoint>> = FxHashMap::default();
    for sink in export.sink_sites {
        let Some(call) = sink.call else {
            continue;
        };
        let locals = export
            .version_sites
            .iter()
            .filter(|site| site.fn_did == call.fn_did && site.use_var == Some(sink.var))
            .map(|site| site.local)
            .collect::<BTreeSet<_>>();
        for local in locals {
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(call.fn_did)
                .borrow();
            let operand_local = local;
            let (chain, terminal) = LocalDefChain::new(program.tcx, &body).trace(local);
            let Some((local, _allocator_rooted)) = terminal else {
                continue;
            };
            let load_slot = single_load_slot(slots, call.fn_did, &body, local);
            let Some(slot) = slots
                .fn_local_slots
                .get(&call.fn_did)
                .and_then(|universe| universe.slot_for_local_depth(local, 0))
            else {
                continue;
            };
            answer
                .entry(SlotRef::Local(call.fn_did, slot))
                .or_default()
                .push(SinkEndpoint {
                    function: call.fn_did,
                    location: call.location,
                    callee: call.callee.clone(),
                    operand_local,
                    chain,
                    local,
                    load_slot,
                });
        }
    }
    for endpoints in answer.values_mut() {
        endpoints.sort_by_key(|endpoint| {
            (
                endpoint.function.local_def_index.as_u32(),
                endpoint.location,
                endpoint.local.as_u32(),
                endpoint.callee.clone(),
            )
        });
        endpoints.dedup_by(|left, right| {
            left.function == right.function
                && left.location == right.location
                && left.local == right.local
                && left.callee == right.callee
        });
    }
    Ok(answer)
}

#[derive(Clone, Debug)]
struct ProbeRow {
    key: LicP1Key,
    endpoint_matches: usize,
    endpoint: Option<SinkEndpoint>,
    may_set: BTreeSet<usize>,
    origin_complete: bool,
    callers: BTreeSet<String>,
    terminals: BTreeSet<String>,
    reasons: BTreeSet<String>,
    verdict: Verdict,
}

struct ProbeOutput {
    rows: Vec<ProbeRow>,
    call_world_calls: usize,
    call_world_unresolved: usize,
    endpoint_slots: usize,
    endpoint_sites: usize,
    endpoint_diagnostic: String,
}

fn slot_from_key(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    function_path: &str,
    key: SlotKey,
) -> Result<SlotRef, String> {
    if key.variant != 1 {
        return Err(format!(
            "T1 requires a local slot, got {}",
            LicP1Key::slot_text(key)
        ));
    }
    let function = program
        .functions
        .iter()
        .copied()
        .find(|function| function.local_def_index.as_u32() == key.owner)
        .ok_or_else(|| format!("missing current function owner {}", key.owner))?;
    let actual_path = program.tcx.def_path_str(function.to_def_id());
    if actual_path != function_path {
        return Err(format!(
            "function path drift for owner {}: stored={function_path} current={actual_path}",
            key.owner
        ));
    }
    let universe = slots
        .fn_local_slots
        .get(&function)
        .ok_or_else(|| format!("missing slot universe for {function_path}"))?;
    if key.slot >= universe.len() {
        return Err(format!(
            "slot index drift for {function_path}: {} >= {}",
            key.slot,
            universe.len()
        ));
    }
    Ok(SlotRef::Local(
        function,
        crate::analyses::borrow_ownership::slots::SlotId::from_usize(key.slot),
    ))
}

fn probe_targets(
    program_name: &str,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    facts: &MutFacts,
    targets: &[LicP1Target],
) -> Result<ProbeOutput, String> {
    let endpoints = capture_sink_endpoints(program, slots, origins, facts)?;
    let endpoint_diagnostic = endpoint_diagnostics_tsv(program, slots, targets, &endpoints)?;
    let endpoint_slots = endpoints.len();
    let endpoint_sites = endpoints.values().map(Vec::len).sum();
    let world = resolve_closed_world_call_world(
        program,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
    );
    let fresh = collect_malloc_source_slots(program.tcx, &program.functions, slots);
    let mut classifier = SlotClassifier {
        program,
        slots,
        flows: origins.native_flows(),
        world: &world,
        fresh: &fresh,
        cache: FxHashMap::default(),
    };
    let mut rows = Vec::with_capacity(targets.len());
    for target in targets {
        if target.key.program != program_name {
            return Err(format!(
                "T1 program drift: target={} worker={program_name}",
                target.key.program
            ));
        }
        let _lhs = slot_from_key(program, slots, &target.key.function, target.key.lhs)?;
        let rhs = slot_from_key(program, slots, &target.key.function, target.key.rhs)?;
        let matched = endpoints.get(&rhs).cloned().unwrap_or_default();
        let endpoint_matches = matched.len();
        let endpoint = (endpoint_matches == 1).then(|| matched[0].clone());
        let evidence = if endpoint.is_some() {
            classifier.classify(rhs)
        } else {
            SlotEvidence::terminal(
                Inflow::Unknown,
                slot_text(rhs),
                if endpoint_matches == 0 {
                    "no-exact-free-endpoint"
                } else {
                    "multiple-exact-free-endpoints"
                },
            )
        };
        let verdict = match evidence.inflow {
            Inflow::Alloc if endpoint.is_some() => Verdict::Yes,
            Inflow::NonAlloc if endpoint.is_some() => Verdict::No,
            _ => Verdict::Indeterminate,
        };
        rows.push(ProbeRow {
            key: target.key.clone(),
            endpoint_matches,
            endpoint,
            may_set: evidence.may_set,
            origin_complete: evidence.complete,
            callers: evidence.callers,
            terminals: evidence.terminals,
            reasons: evidence.reasons,
            verdict,
        });
    }
    Ok(ProbeOutput {
        rows,
        call_world_calls: world.calls,
        call_world_unresolved: world.unresolved_calls,
        endpoint_slots,
        endpoint_sites,
        endpoint_diagnostic,
    })
}

fn endpoint_diagnostics_tsv(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    targets: &[LicP1Target],
    endpoints: &FxHashMap<SlotRef, Vec<SinkEndpoint>>,
) -> Result<String, String> {
    let mut rows = Vec::new();
    for target in targets {
        let rhs = slot_from_key(program, slots, &target.key.function, target.key.rhs)?;
        let SlotRef::Local(function, _) = rhs else {
            continue;
        };
        let mut matches = endpoints
            .iter()
            .flat_map(|(&terminal_slot, endpoints)| {
                endpoints
                    .iter()
                    .filter(move |endpoint| endpoint.function == function)
                    .map(move |endpoint| (terminal_slot, endpoint))
            })
            .collect::<Vec<_>>();
        matches.sort_by_key(|(slot, endpoint)| {
            (
                endpoint.location,
                endpoint.callee.clone(),
                SlotKey::of(*slot),
            )
        });
        if matches.is_empty() {
            rows.push(format!(
                "{}\t{}\t{}\t{}\t0\t-\t-\t-\t-\t-\t0\t-\t0",
                target.key.program,
                target.key.function,
                LicP1Key::slot_text(target.key.lhs),
                LicP1Key::slot_text(target.key.rhs),
            ));
            continue;
        }
        let count = matches.len();
        for (terminal_slot, endpoint) in matches {
            let load_slot = endpoint
                .load_slot
                .map(slot_text)
                .unwrap_or_else(|| "-".to_owned());
            rows.push(format!(
                "{}\t{}\t{}\t{}\t{}\t{}\tbb{}:{}\t_{}\t{}\t{}\t{}\t{}\t{}",
                target.key.program,
                target.key.function,
                LicP1Key::slot_text(target.key.lhs),
                LicP1Key::slot_text(target.key.rhs),
                count,
                endpoint.callee,
                endpoint.location.block,
                endpoint.location.statement_index,
                endpoint.operand_local.as_u32(),
                endpoint
                    .chain
                    .iter()
                    .map(|local| format!("{local:?}"))
                    .collect::<Vec<_>>()
                    .join("->"),
                slot_text(terminal_slot),
                usize::from(terminal_slot == rhs),
                load_slot,
                usize::from(endpoint.load_slot == Some(rhs)),
            ));
        }
    }
    rows.sort();
    let mut output = String::from(
        "program\tfunction\tlhs\trhs\tfunction_endpoint_count\tcallee\tlocation\t\
         operand_local\tlocal_chain\tterminal_slot\treaches_rhs\tload_slot\tload_hits_rhs\n",
    );
    for row in rows {
        output.push_str(&row);
        output.push('\n');
    }
    Ok(output)
}

fn endpoint_diagnostics_tsv_empty() -> String {
    "program\tfunction\tlhs\trhs\tfunction_endpoint_count\tcallee\tlocation\t\
     operand_local\tlocal_chain\tterminal_slot\treaches_rhs\tload_slot\tload_hits_rhs\n"
        .to_owned()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CallFamily {
    Allocator,
    LocalFunction,
    Extern,
    LibcOther,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TerminalShape {
    NoEndpointPlaceholder,
    CallAllocator,
    CallLocalFunction,
    CallExtern,
    CallLibcOther,
    Parameter,
    MultiDef,
    SingleLoad,
    Other,
}

impl TerminalShape {
    fn label(self) -> &'static str {
        match self {
            Self::NoEndpointPlaceholder => "no-endpoint-placeholder",
            Self::CallAllocator => "call-destination-allocator",
            Self::CallLocalFunction => "call-destination-local-function",
            Self::CallExtern => "call-destination-extern",
            Self::CallLibcOther => "call-destination-libc-other",
            Self::Parameter => "function-parameter",
            Self::MultiDef => "multi-def-local",
            Self::SingleLoad => "single-load",
            Self::Other => "other",
        }
    }
}

#[derive(Clone, Copy)]
struct TerminalFacts {
    call: Option<CallFamily>,
    parameter: bool,
    definitions: usize,
    single_load: bool,
}

fn classify_terminal_facts(facts: TerminalFacts) -> TerminalShape {
    if facts.definitions > 1 {
        return TerminalShape::MultiDef;
    }
    if let Some(call) = facts.call {
        return match call {
            CallFamily::Allocator => TerminalShape::CallAllocator,
            CallFamily::LocalFunction => TerminalShape::CallLocalFunction,
            CallFamily::Extern => TerminalShape::CallExtern,
            CallFamily::LibcOther => TerminalShape::CallLibcOther,
        };
    }
    if facts.parameter && facts.definitions == 0 {
        TerminalShape::Parameter
    } else if facts.definitions == 1 && facts.single_load {
        TerminalShape::SingleLoad
    } else {
        TerminalShape::Other
    }
}

#[derive(Clone, Debug)]
struct EndpointTrace {
    key: LicP1Key,
    placeholder: bool,
    callee: String,
    location: String,
    terminal_local: Option<Local>,
    terminal_slot: Option<SlotKey>,
    load_slot: Option<SlotKey>,
}

fn parse_endpoint_traces(text: &str, program: &str) -> Result<Vec<EndpointTrace>, String> {
    let mut lines = text.lines();
    let header = lines.next().ok_or("missing endpoint trace header")?;
    let columns = header
        .split('\t')
        .enumerate()
        .map(|(index, name)| (name, index))
        .collect::<BTreeMap<_, _>>();
    let get = |fields: &[&str], name: &str| -> Result<String, String> {
        let index = columns
            .get(name)
            .ok_or_else(|| format!("missing endpoint column {name}"))?;
        fields
            .get(*index)
            .map(|value| (*value).to_owned())
            .ok_or_else(|| format!("short endpoint row at {name}"))
    };
    let mut answer = Vec::new();
    for line in lines.filter(|line| !line.is_empty()) {
        let fields = line.split('\t').collect::<Vec<_>>();
        if get(&fields, "program")? != program {
            continue;
        }
        let endpoint_count = get(&fields, "function_endpoint_count")?
            .parse::<usize>()
            .map_err(|_| "invalid endpoint count".to_owned())?;
        let chain = get(&fields, "local_chain")?;
        let terminal_local = chain
            .rsplit("->")
            .next()
            .filter(|local| local.starts_with('_'))
            .and_then(|local| local[1..].parse::<u32>().ok())
            .map(Local::from_u32);
        let parse_optional_slot = |name: &str| -> Result<Option<SlotKey>, String> {
            let value = get(&fields, name)?;
            (value != "-").then(|| parse_slot_key(&value)).transpose()
        };
        answer.push(EndpointTrace {
            key: LicP1Key {
                program: program.to_owned(),
                function: get(&fields, "function")?,
                lhs: parse_slot_key(&get(&fields, "lhs")?)?,
                rhs: parse_slot_key(&get(&fields, "rhs")?)?,
            },
            placeholder: endpoint_count == 0,
            callee: get(&fields, "callee")?,
            location: get(&fields, "location")?,
            terminal_local,
            terminal_slot: parse_optional_slot("terminal_slot")?,
            load_slot: parse_optional_slot("load_slot")?,
        });
    }
    Ok(answer)
}

#[derive(Clone, Debug)]
struct CharacterizedTerminal {
    trace: EndpointTrace,
    shape: TerminalShape,
    detail: String,
}

fn call_family(tcx: TyCtxt<'_>, body: &Body<'_>, local: Local) -> Vec<(CallFamily, String)> {
    let mut answer = Vec::new();
    for data in body.basic_blocks.iter() {
        let TerminatorKind::Call {
            func, destination, ..
        } = &data.terminator().kind
        else {
            continue;
        };
        if destination.as_local() != Some(local) {
            continue;
        }
        let Some((callee, _)) = func.const_fn_def() else {
            answer.push((CallFamily::Extern, "indirect-call".to_owned()));
            continue;
        };
        let name = tcx.item_name(callee).to_string();
        let Some(local_callee) = callee.as_local() else {
            answer.push((CallFamily::Extern, name));
            continue;
        };
        match tcx.hir_node_by_def_id(local_callee) {
            rustc_hir::Node::ForeignItem(item) => {
                let name = item.ident.as_str();
                let family = if boundary_table::sources_foreign().any(|source| source == name) {
                    CallFamily::Allocator
                } else if boundary_table::lookup(
                    name,
                    crate::analyses::borrow_ownership::boundary_table::Matcher::ForeignC,
                )
                .is_some()
                {
                    CallFamily::LibcOther
                } else {
                    CallFamily::Extern
                };
                answer.push((family, name.to_owned()));
            }
            rustc_hir::Node::Item(_) | rustc_hir::Node::ImplItem(_) => {
                answer.push((CallFamily::LocalFunction, name));
            }
            _ => answer.push((CallFamily::Extern, name)),
        }
    }
    answer
}

fn characterize_terminal(
    tcx: TyCtxt<'_>,
    slots: &CrateSlots,
    function: rustc_span::def_id::LocalDefId,
    body: &Body<'_>,
    trace: EndpointTrace,
) -> CharacterizedTerminal {
    if trace.placeholder {
        return CharacterizedTerminal {
            trace,
            shape: TerminalShape::NoEndpointPlaceholder,
            detail: "no E-R3 endpoint in containing function".to_owned(),
        };
    }
    let Some(local) = trace.terminal_local else {
        return CharacterizedTerminal {
            trace,
            shape: TerminalShape::Other,
            detail: "terminal local absent from stored chain".to_owned(),
        };
    };
    let statement_definitions = body
        .basic_blocks
        .iter()
        .flat_map(|data| data.statements.iter())
        .filter(|statement| {
            matches!(&statement.kind, StatementKind::Assign(assign) if assign.0.as_local() == Some(local))
        })
        .count();
    let calls = call_family(tcx, body, local);
    let definitions = statement_definitions + calls.len();
    let load = single_load_slot(slots, function, body, local);
    let shape = classify_terminal_facts(TerminalFacts {
        call: if definitions == 1 {
            calls.first().map(|call| call.0)
        } else {
            None
        },
        parameter: local.index() >= 1 && local.index() <= body.arg_count,
        definitions,
        single_load: load.is_some(),
    });
    let detail = match shape {
        TerminalShape::CallAllocator
        | TerminalShape::CallLocalFunction
        | TerminalShape::CallExtern
        | TerminalShape::CallLibcOther => calls[0].1.clone(),
        TerminalShape::Parameter => format!("argument{}", local.index()),
        TerminalShape::MultiDef => format!("definitions={definitions}"),
        TerminalShape::SingleLoad => load.map(slot_text).unwrap_or_else(|| "-".to_owned()),
        TerminalShape::Other => format!("definitions={definitions}"),
        TerminalShape::NoEndpointPlaceholder => unreachable!(),
    };
    CharacterizedTerminal {
        trace,
        shape,
        detail,
    }
}

fn terminal_rows_tsv(rows: &[CharacterizedTerminal]) -> String {
    let mut output = String::from(
        "program\tfunction\tlhs\trhs\tcallee\tlocation\tterminal_local\tterminal_slot\t\
         load_slot\tterminal_class\tdetail\n",
    );
    for row in rows {
        output.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            row.trace.key.program,
            row.trace.key.function,
            LicP1Key::slot_text(row.trace.key.lhs),
            LicP1Key::slot_text(row.trace.key.rhs),
            row.trace.callee,
            row.trace.location,
            row.trace
                .terminal_local
                .map(|local| format!("{local:?}"))
                .unwrap_or_else(|| "-".to_owned()),
            row.trace
                .terminal_slot
                .map(LicP1Key::slot_text)
                .unwrap_or_else(|| "-".to_owned()),
            row.trace
                .load_slot
                .map(LicP1Key::slot_text)
                .unwrap_or_else(|| "-".to_owned()),
            row.shape.label(),
            clean(&row.detail),
        ));
    }
    output
}

fn slot_owner_from_key(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    function_path: &str,
    key: SlotKey,
) -> Result<(SlotOwner, u8), String> {
    if key.variant == 0 {
        if key.slot >= slots.field_slots.len() {
            return Err(format!("field slot index drift: {}", key.slot));
        }
        let slot = slots
            .field_slots
            .slot(crate::analyses::borrow_ownership::slots::SlotId::from_usize(key.slot));
        return Ok((slot.owner, slot.depth));
    }
    match slot_from_key(program, slots, function_path, key)? {
        SlotRef::Local(function, slot) => {
            let slot = slots.fn_local_slots[&function].slot(slot);
            Ok((slot.owner, slot.depth))
        }
        SlotRef::Field(slot) => {
            let slot = slots.field_slots.slot(slot);
            Ok((slot.owner, slot.depth))
        }
    }
}

fn owner_text(tcx: TyCtxt<'_>, owner: SlotOwner) -> String {
    match owner {
        SlotOwner::Local(local) => format!("local:{local:?}"),
        SlotOwner::Field(field) => format!(
            "field:{}:{}",
            tcx.def_path_str(field.struct_did.to_def_id()),
            field.field_index
        ),
    }
}

fn owner_sort_key(tcx: TyCtxt<'_>, owner: SlotOwner) -> String {
    owner_text(tcx, owner)
}

fn shortest_owner_path(
    tcx: TyCtxt<'_>,
    edges: &[(SlotOwner, SlotOwner)],
    start: SlotOwner,
    end: SlotOwner,
) -> Option<Vec<SlotOwner>> {
    let mut outgoing: FxHashMap<SlotOwner, Vec<SlotOwner>> = FxHashMap::default();
    for &(source, target) in edges {
        outgoing.entry(source).or_default().push(target);
    }
    for targets in outgoing.values_mut() {
        targets.sort_by_key(|owner| owner_sort_key(tcx, *owner));
        targets.dedup();
    }
    let mut queue = VecDeque::from([start]);
    let mut previous = FxHashMap::default();
    let mut seen = FxHashSet::from_iter([start]);
    while let Some(node) = queue.pop_front() {
        if node == end {
            let mut path = vec![node];
            let mut cursor = node;
            while let Some(&parent) = previous.get(&cursor) {
                path.push(parent);
                cursor = parent;
            }
            path.reverse();
            return Some(path);
        }
        for &next in outgoing.get(&node).into_iter().flatten() {
            if seen.insert(next) {
                previous.insert(next, node);
                queue.push_back(next);
            }
        }
    }
    None
}

fn render_owner_path(tcx: TyCtxt<'_>, path: Option<Vec<SlotOwner>>) -> String {
    let Some(path) = path else {
        return "-".to_owned();
    };
    let mut output = owner_text(tcx, path[0]);
    for edge in path.windows(2) {
        let hop = match (edge[0], edge[1]) {
            (SlotOwner::Local(_), SlotOwner::Field(_)) => "store-into-field",
            (SlotOwner::Field(_), SlotOwner::Local(_)) => "load-from-field",
            _ => "value-flow",
        };
        output.push_str(&format!(" -[{hop}]-> {}", owner_text(tcx, edge[1])));
    }
    output
}

fn field_path_rows_tsv(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    rows: &[CharacterizedTerminal],
) -> Result<String, String> {
    let mut output = String::from(
        "program\tfunction\tlhs\trhs\tfield_slot\trhs_depth\tfield_depth\tfact_scope\t\
         rhs_to_field\tfield_to_rhs\tany_path\n",
    );
    for row in rows
        .iter()
        .filter(|row| row.shape == TerminalShape::SingleLoad)
    {
        let load = row
            .trace
            .load_slot
            .ok_or("single-load row lacks load slot")?;
        let (rhs, rhs_depth) =
            slot_owner_from_key(program, slots, &row.trace.key.function, row.trace.key.rhs)?;
        let (field, field_depth) =
            slot_owner_from_key(program, slots, &row.trace.key.function, load)?;
        let SlotRef::Local(function, _) =
            slot_from_key(program, slots, &row.trace.key.function, row.trace.key.rhs)?
        else {
            return Err("field-path RHS is not local".to_owned());
        };
        let edges = origins.native_flows()[&function].body.depth0_value_flows();
        let in_scope = rhs_depth == 0 && field_depth == 0;
        let forward = in_scope
            .then(|| shortest_owner_path(program.tcx, &edges, rhs, field))
            .flatten();
        let reverse = in_scope
            .then(|| shortest_owner_path(program.tcx, &edges, field, rhs))
            .flatten();
        let any = usize::from(forward.is_some() || reverse.is_some());
        output.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            row.trace.key.program,
            row.trace.key.function,
            LicP1Key::slot_text(row.trace.key.lhs),
            LicP1Key::slot_text(row.trace.key.rhs),
            LicP1Key::slot_text(load),
            rhs_depth,
            field_depth,
            if in_scope {
                "closed-depth0-value-flow"
            } else {
                "outside-depth0-facts"
            },
            clean(&render_owner_path(program.tcx, forward)),
            clean(&render_owner_path(program.tcx, reverse)),
            any,
        ));
    }
    Ok(output)
}

pub(crate) fn run_characterization_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> super::report::Row {
    let started = Instant::now();
    let program_name = std::env::var("CRAT_BOC1_NAME").expect("T1 program name");
    let input_path = std::env::var("CRAT_T1_ENDPOINT_INPUT").expect("T1 endpoint trace input path");
    let terminal_path = std::env::var("CRAT_T1_TERMINAL_OUTPUT").expect("T1 terminal output path");
    let field_path = std::env::var("CRAT_T1_FIELD_PATH_OUTPUT").expect("T1 field-path output path");
    let input = fs::read_to_string(Path::new(&input_path)).expect("read T1 endpoint traces");
    let traces = parse_endpoint_traces(&input, &program_name).expect("parse T1 endpoint traces");

    let rows = if traces.is_empty() {
        Vec::new()
    } else {
        let program = super::collect_program(tcx);
        let slots = CrateSlots::build(&program);
        traces
            .into_iter()
            .map(|trace| {
                if trace.placeholder {
                    return CharacterizedTerminal {
                        trace,
                        shape: TerminalShape::NoEndpointPlaceholder,
                        detail: "no E-R3 endpoint in containing function".to_owned(),
                    };
                }
                let SlotRef::Local(function, _) =
                    slot_from_key(&program, &slots, &trace.key.function, trace.key.rhs)
                        .expect("resolve characterization function")
                else {
                    panic!("T1 characterization RHS must be local")
                };
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                characterize_terminal(tcx, &slots, function, &body, trace)
            })
            .collect::<Vec<_>>()
    };
    fs::write(Path::new(&terminal_path), terminal_rows_tsv(&rows))
        .expect("write T1 terminal characterization");

    let field_rows = if rows
        .iter()
        .any(|row| row.shape == TerminalShape::SingleLoad)
    {
        let program = super::collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
        field_path_rows_tsv(&program, &slots, &origins, &rows)
            .expect("project T1 field value-flow paths")
    } else {
        "program\tfunction\tlhs\trhs\tfield_slot\trhs_depth\tfield_depth\tfact_scope\t\
         rhs_to_field\tfield_to_rhs\tany_path\n"
            .to_owned()
    };
    fs::write(Path::new(&field_path), &field_rows).expect("write T1 field-path characterization");

    let mut counts = BTreeMap::new();
    for row in &rows {
        *counts.entry(row.shape.label()).or_insert(0usize) += 1;
    }
    let field_load_rows = rows
        .iter()
        .filter(|row| row.shape == TerminalShape::SingleLoad)
        .count();
    let field_path_yes = field_rows
        .lines()
        .skip(1)
        .filter(|line| line.rsplit('\t').next() == Some("1"))
        .count();
    let mut receipt = super::report::Row::default();
    receipt.set("status", "ok");
    receipt.set("data", "provisional");
    receipt.set("corpus", "rs-crown");
    receipt.set("frame", "c080e9e7");
    receipt.set("program", program_name);
    receipt.set("trace_rows", rows.len());
    receipt.set(
        "real_endpoints",
        rows.iter()
            .filter(|row| row.shape != TerminalShape::NoEndpointPlaceholder)
            .count(),
    );
    receipt.set(
        "no_endpoint_placeholders",
        counts
            .get(TerminalShape::NoEndpointPlaceholder.label())
            .copied()
            .unwrap_or(0),
    );
    for shape in [
        TerminalShape::CallAllocator,
        TerminalShape::CallLocalFunction,
        TerminalShape::CallExtern,
        TerminalShape::CallLibcOther,
        TerminalShape::Parameter,
        TerminalShape::MultiDef,
        TerminalShape::SingleLoad,
        TerminalShape::Other,
    ] {
        receipt.set(
            &format!("terminal_{}", shape.label().replace('-', "_")),
            counts.get(shape.label()).copied().unwrap_or(0),
        );
    }
    receipt.set("field_load_rows", field_load_rows);
    receipt.set("field_path_yes", field_path_yes);
    receipt.set("field_path_no", field_load_rows - field_path_yes);
    receipt.set("solver_checks", 0);
    receipt.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    receipt.set(
        "t_total_s",
        format!("{:.3}", started.elapsed().as_secs_f64()),
    );
    receipt
}

fn clean(value: &str) -> String {
    value.replace(['\t', '\n', '\r'], " ")
}

fn rows_tsv(rows: &[ProbeRow]) -> String {
    let mut output = String::from(
        "program\tfunction\tlhs\trhs\tendpoint_matches\tfree_function\tfree_location\t\
         free_callee\tfreed_slot\torigin_may_set\torigin_complete\tobserved_callers\t\
         terminal_roots\treasons\tverdict\ta5_world\tcorpus\tframe\n",
    );
    for row in rows {
        let (free_location, free_callee) = row.endpoint.as_ref().map_or_else(
            || ("-".to_owned(), "-".to_owned()),
            |endpoint| {
                (
                    format!(
                        "bb{}:{}",
                        endpoint.location.block, endpoint.location.statement_index
                    ),
                    endpoint.callee.clone(),
                )
            },
        );
        let may_set = row
            .may_set
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(",");
        let verdict = match row.verdict {
            Verdict::Yes => "YES",
            Verdict::No => "NO",
            Verdict::Indeterminate => "INDETERMINATE",
        };
        output.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t\
             closed_world_frozen_graph\trs-crown\tc080e9e7\n",
            clean(&row.key.program),
            clean(&row.key.function),
            LicP1Key::slot_text(row.key.lhs),
            LicP1Key::slot_text(row.key.rhs),
            row.endpoint_matches,
            clean(&row.key.function),
            free_location,
            clean(&free_callee),
            LicP1Key::slot_text(row.key.rhs),
            may_set,
            row.origin_complete as u8,
            clean(&row.callers.iter().cloned().collect::<Vec<_>>().join(" | ")),
            clean(
                &row.terminals
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(" | ")
            ),
            clean(&row.reasons.iter().cloned().collect::<Vec<_>>().join(" | ")),
            verdict,
        ));
    }
    output
}

pub(crate) fn run_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> super::report::Row {
    let started = Instant::now();
    let program_name = std::env::var("CRAT_BOC1_NAME").expect("T1 program name");
    let ledger_path = std::env::var("CRAT_T1_LIC_P1_LEDGER").expect("T1 LIC-P1 ledger");
    let output_path = std::env::var("CRAT_T1_OUTPUT").expect("T1 output path");
    let ledger = fs::read_to_string(Path::new(&ledger_path)).expect("read T1 LIC-P1 ledger");
    let targets = parse_lic_p1_targets(&ledger, &program_name).expect("parse T1 targets");

    let output = if targets.is_empty() {
        ProbeOutput {
            rows: Vec::new(),
            call_world_calls: 0,
            call_world_unresolved: 0,
            endpoint_slots: 0,
            endpoint_sites: 0,
            endpoint_diagnostic: endpoint_diagnostics_tsv_empty(),
        }
    } else {
        let program = super::collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
        let facts = MutFacts::from_program(&program);
        probe_targets(&program_name, &program, &slots, &origins, &facts, &targets)
            .expect("T1 probe")
    };
    fs::write(Path::new(&output_path), rows_tsv(&output.rows)).expect("write T1 rows");
    if let Some(path) = std::env::var_os("CRAT_T1_DIAG_OUTPUT") {
        fs::write(Path::new(&path), &output.endpoint_diagnostic).expect("write T1 diagnostics");
    }

    let mut yes = 0usize;
    let mut no = 0usize;
    let mut indeterminate = 0usize;
    let mut unique_endpoints = 0usize;
    let mut missing_endpoints = 0usize;
    let mut ambiguous_endpoints = 0usize;
    for row in &output.rows {
        match row.verdict {
            Verdict::Yes => yes += 1,
            Verdict::No => no += 1,
            Verdict::Indeterminate => indeterminate += 1,
        }
        match row.endpoint_matches {
            0 => missing_endpoints += 1,
            1 => unique_endpoints += 1,
            _ => ambiguous_endpoints += 1,
        }
    }
    let mut receipt = super::report::Row::default();
    receipt.set("status", "ok");
    receipt.set("data", "provisional");
    receipt.set("corpus", "rs-crown");
    receipt.set("frame", "c080e9e7");
    receipt.set("a5_world", "closed_world_frozen_graph");
    receipt.set("program", program_name);
    receipt.set("targets", output.rows.len());
    receipt.set("yes", yes);
    receipt.set("no", no);
    receipt.set("indeterminate", indeterminate);
    receipt.set("unique_endpoints", unique_endpoints);
    receipt.set("missing_endpoints", missing_endpoints);
    receipt.set("ambiguous_endpoints", ambiguous_endpoints);
    receipt.set("call_world_calls", output.call_world_calls);
    receipt.set("call_world_unresolved", output.call_world_unresolved);
    receipt.set("endpoint_slots", output.endpoint_slots);
    receipt.set("endpoint_sites", output.endpoint_sites);
    receipt.set("solver_checks", 0);
    receipt.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    receipt.set(
        "t_total_s",
        format!("{:.3}", started.elapsed().as_secs_f64()),
    );
    receipt
}

#[derive(Clone, Debug)]
struct SlotEvidence {
    inflow: Inflow,
    may_set: BTreeSet<usize>,
    complete: bool,
    callers: BTreeSet<String>,
    terminals: BTreeSet<String>,
    reasons: BTreeSet<String>,
}

impl SlotEvidence {
    fn terminal(inflow: Inflow, terminal: String, reason: &str) -> Self {
        Self {
            inflow,
            may_set: BTreeSet::new(),
            complete: inflow != Inflow::Unknown,
            callers: BTreeSet::new(),
            terminals: BTreeSet::from([terminal]),
            reasons: BTreeSet::from([reason.to_owned()]),
        }
    }
}

struct SlotClassifier<'a, 'tcx> {
    program: &'a RustProgram<'tcx>,
    slots: &'a CrateSlots,
    flows: &'a OriginFlowResults,
    world: &'a ClosedWorldCallWorld,
    fresh: &'a FxHashSet<SlotRef>,
    cache: FxHashMap<SlotRef, SlotEvidence>,
}

impl<'a, 'tcx> SlotClassifier<'a, 'tcx> {
    fn classify(&mut self, slot: SlotRef) -> SlotEvidence {
        self.classify_inner(slot, &mut FxHashSet::default())
    }

    fn classify_inner(&mut self, slot: SlotRef, active: &mut FxHashSet<SlotRef>) -> SlotEvidence {
        if let Some(evidence) = self.cache.get(&slot) {
            return evidence.clone();
        }
        if !active.insert(slot) {
            return SlotEvidence::terminal(Inflow::Unknown, slot_text(slot), "caller-origin-cycle");
        }
        let mut evidence = self.classify_uncached(slot, active);
        active.remove(&slot);
        if evidence.inflow == Inflow::Unknown {
            evidence.complete = false;
        }
        self.cache.insert(slot, evidence.clone());
        evidence
    }

    fn classify_uncached(
        &mut self,
        slot: SlotRef,
        active: &mut FxHashSet<SlotRef>,
    ) -> SlotEvidence {
        if self.fresh.contains(&slot) {
            return SlotEvidence::terminal(Inflow::Alloc, slot_text(slot), "allocator-source-slot");
        }
        let SlotRef::Local(function, slot_id) = slot else {
            return SlotEvidence::terminal(
                Inflow::Unknown,
                slot_text(slot),
                "field-origin-not-call-instantiable",
            );
        };
        let Some(universe) = self.slots.fn_local_slots.get(&function) else {
            return SlotEvidence::terminal(
                Inflow::Unknown,
                slot_text(slot),
                "missing-slot-universe",
            );
        };
        let slot_data = universe.slot(slot_id);
        let SlotOwner::Local(local) = slot_data.owner else {
            return SlotEvidence::terminal(Inflow::Unknown, slot_text(slot), "nonlocal-slot-owner");
        };
        if slot_data.depth != 0 {
            return SlotEvidence::terminal(Inflow::Unknown, slot_text(slot), "non-depth-zero-slot");
        }
        let body = self
            .program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let Some(flow) = self.flows.get(&function) else {
            return SlotEvidence::terminal(Inflow::Unknown, slot_text(slot), "missing-origin-flow");
        };
        let Some((may_set, complete)) = flow.body.depth0_origin_indices(
            &body,
            local,
            self.world.unknown_reachable.contains(&function),
        ) else {
            return SlotEvidence::terminal(Inflow::Unknown, slot_text(slot), "missing-origin-slot");
        };
        let Some((arguments, argument_complete)) = flow.body.depth0_argument_origins(&body, local)
        else {
            return SlotEvidence::terminal(
                Inflow::Unknown,
                slot_text(slot),
                "missing-argument-origin",
            );
        };
        if !complete || !argument_complete {
            let mut evidence = SlotEvidence::terminal(
                Inflow::Unknown,
                slot_text(slot),
                if self.world.unknown_reachable.contains(&function) {
                    "open-boundary-origin"
                } else {
                    "incomplete-origin-may-set"
                },
            );
            evidence.may_set = may_set;
            return evidence;
        }
        if arguments.is_empty() {
            let mut evidence = SlotEvidence::terminal(
                Inflow::NonAlloc,
                slot_text(slot),
                "complete-nonallocator-local-root",
            );
            evidence.may_set = may_set;
            return evidence;
        }

        let mut inflows = Vec::new();
        let mut combined = SlotEvidence {
            inflow: Inflow::Unknown,
            may_set,
            complete: true,
            callers: BTreeSet::new(),
            terminals: BTreeSet::new(),
            reasons: BTreeSet::new(),
        };
        for argument in arguments {
            if argument == 0 {
                inflows.push(Inflow::Unknown);
                combined
                    .reasons
                    .insert("return-place-as-argument".to_owned());
                continue;
            }
            let actuals = self.observed_actuals(function, argument - 1);
            if actuals.is_empty() {
                inflows.push(Inflow::Unknown);
                combined
                    .reasons
                    .insert(format!("no-observed-caller-for-arg{argument}"));
                continue;
            }
            for (caller, call, actual) in actuals {
                let caller_path = self.program.tcx.def_path_str(caller.to_def_id());
                let call_text = format!(
                    "{}:bb{}:arg{}=>{}",
                    caller_path,
                    call.block,
                    argument,
                    slot_text_opt(actual)
                );
                combined.callers.insert(call_text);
                let Some(actual) = actual else {
                    inflows.push(Inflow::Unknown);
                    combined
                        .reasons
                        .insert("unresolved-caller-actual".to_owned());
                    continue;
                };
                let evidence = self.classify_inner(actual, active);
                inflows.push(evidence.inflow);
                combined.terminals.extend(evidence.terminals);
                combined.reasons.extend(evidence.reasons);
                combined.callers.extend(evidence.callers);
                combined.complete &= evidence.complete;
            }
        }
        combined.inflow = match join_inflows(&inflows) {
            Verdict::Yes => Inflow::Alloc,
            Verdict::No => Inflow::NonAlloc,
            Verdict::Indeterminate => Inflow::Unknown,
        };
        combined
    }

    fn observed_actuals(
        &self,
        target: rustc_span::def_id::LocalDefId,
        argument: usize,
    ) -> Vec<(
        rustc_span::def_id::LocalDefId,
        crate::analyses::borrow_ownership::l2::MirLocationKey,
        Option<SlotRef>,
    )> {
        let mut rows = Vec::new();
        for (&(caller, block), targets) in &self.world.resolved {
            if !targets.contains(&target) {
                continue;
            }
            let body = self
                .program
                .tcx
                .mir_drops_elaborated_and_const_checked(caller)
                .borrow();
            let args = match &body.basic_blocks[block].terminator().kind {
                TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => args,
                _ => continue,
            };
            let actual = args.get(argument).and_then(|arg| {
                resolved_actual_slot(self.program.tcx, self.slots, caller, &body, &arg.node)
            });
            rows.push((
                caller,
                crate::analyses::borrow_ownership::l2::MirLocationKey::new(
                    block.as_u32(),
                    body.basic_blocks[block].statements.len(),
                ),
                actual,
            ));
        }
        rows.sort_by_key(|(caller, location, actual)| {
            (
                caller.local_def_index.as_u32(),
                *location,
                actual.map(SlotKey::of),
            )
        });
        rows
    }
}

fn slot_text(slot: SlotRef) -> String {
    match slot {
        SlotRef::Field(slot) => format!("field:{}", slot.index()),
        SlotRef::Local(function, slot) => {
            format!(
                "local:{}:{}",
                function.local_def_index.as_u32(),
                slot.index()
            )
        }
    }
}

fn slot_text_opt(slot: Option<SlotRef>) -> String {
    slot.map(slot_text)
        .unwrap_or_else(|| "unresolved".to_owned())
}

#[cfg(test)]
fn fixture_inflow(code: &'static str, function_name: &str, local_name: &str) -> Inflow {
    let mut answer = None;
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = super::collect_program(tcx);
        let function = program
            .functions
            .iter()
            .copied()
            .find(|function| tcx.item_name(function.to_def_id()).as_str() == function_name)
            .expect("fixture function");
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let local = body
            .var_debug_info
            .iter()
            .find_map(|info| {
                (info.name.as_str() == local_name).then(|| match info.value {
                    rustc_middle::mir::VarDebugInfoContents::Place(place) => Some(place.local),
                    _ => None,
                })?
            })
            .expect("fixture local");
        let slots = CrateSlots::build(&program);
        let slot = slots
            .fn_local_slots
            .get(&function)
            .and_then(|universe| universe.slot_for_local_depth(local, 0))
            .map(|slot| SlotRef::Local(function, slot))
            .expect("fixture slot");
        let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
        let world = resolve_closed_world_call_world(
            &program,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        let fresh = collect_malloc_source_slots(tcx, &program.functions, &slots);
        let evidence = SlotClassifier {
            program: &program,
            slots: &slots,
            flows: origins.native_flows(),
            world: &world,
            fresh: &fresh,
            cache: FxHashMap::default(),
        }
        .classify(slot);
        answer = Some(evidence.inflow);
    })
    .unwrap_or_else(|error| error.raise());
    answer.expect("compiler callback")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parser_keeps_only_unknown_origin_rows_and_exact_join_keys() {
        let input = "program\tfunction\tlhs\trhs\tstored_scope\tstored_families\tquery_status\t\
                     exact_labels\tbucket\tsubbucket\tclassification_source\tchecks\tprior_checks\t\
                     copy_lend_mode\tsmt_seed\tsat_seed\n\
                     p\tcrate::f\tlocal:1:2\tlocal:1:3\texhaustive\town-assume\tunsat\tlabel\t\
                     token-cannot-exist\tunknown-origin\ttargeted-resolve\t1\t0\tlend_arm\t0\t0\n\
                     p\tcrate::g\tlocal:2:2\tlocal:2:3\texhaustive\town-assume\tunsat\tlabel\t\
                     token-cannot-exist\tinvisible-allocation\ttargeted-resolve\t1\t0\tlend_arm\t0\t0\n";
        let rows = parse_lic_p1_targets(input, "p").expect("valid fixture");
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].key.diagnostic(), "p|crate::f|local:1:2|local:1:3");
    }

    #[test]
    fn duplicate_lic_p1_key_is_rejected() {
        let header = "program\tfunction\tlhs\trhs\tstored_scope\tstored_families\tquery_status\t\
                      exact_labels\tbucket\tsubbucket\tclassification_source\tchecks\tprior_checks\t\
                      copy_lend_mode\tsmt_seed\tsat_seed\n";
        let row = "p\tcrate::f\tlocal:1:2\tlocal:1:3\texhaustive\town-assume\tunsat\tlabel\t\
                   token-cannot-exist\tunknown-origin\ttargeted-resolve\t1\t0\tlend_arm\t0\t0\n";
        let error = parse_lic_p1_targets(&format!("{header}{row}{row}"), "p")
            .expect_err("duplicate must fail closed");
        assert!(error.contains("duplicate LIC-P1 key"), "{error}");
    }

    #[test]
    fn endpoint_resolution_is_unique_or_indeterminate() {
        assert_eq!(endpoint_disposition(0), EndpointDisposition::Indeterminate);
        assert_eq!(endpoint_disposition(1), EndpointDisposition::Unique);
        assert_eq!(endpoint_disposition(2), EndpointDisposition::Indeterminate);
    }

    #[test]
    fn all_observed_inflows_use_three_valued_fail_closed_join() {
        assert_eq!(join_inflows(&[Inflow::Alloc, Inflow::Alloc]), Verdict::Yes);
        assert_eq!(
            join_inflows(&[Inflow::Alloc, Inflow::NonAlloc]),
            Verdict::No
        );
        assert_eq!(
            join_inflows(&[Inflow::Alloc, Inflow::Unknown]),
            Verdict::Indeterminate
        );
        assert_eq!(join_inflows(&[]), Verdict::Indeterminate);
    }

    #[test]
    fn observed_private_caller_with_malloc_actual_is_alloc_rooted() {
        let code = r#"
            extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }
            unsafe fn release(p: *mut i32) { free(p.cast()); }
            unsafe fn entry() { let p = malloc(4) as *mut i32; release(p); }
        "#;
        assert_eq!(fixture_inflow(code, "release", "p"), Inflow::Alloc);
    }

    #[test]
    fn observed_private_caller_with_stack_actual_is_not_alloc_rooted() {
        let code = r#"
            extern "C" { fn free(p: *mut core::ffi::c_void); }
            unsafe fn release(p: *mut i32) { free(p.cast()); }
            unsafe fn entry() { let mut cell = 0; release(&raw mut cell); }
        "#;
        assert_eq!(fixture_inflow(code, "release", "p"), Inflow::NonAlloc);
    }

    #[test]
    fn open_boundary_is_indeterminate_even_with_an_observed_alloc_caller() {
        let code = r#"
            extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }
            pub unsafe fn release(p: *mut i32) { free(p.cast()); }
            unsafe fn entry() { let p = malloc(4) as *mut i32; release(p); }
        "#;
        assert_eq!(fixture_inflow(code, "release", "p"), Inflow::Unknown);
    }

    #[test]
    fn e_r3_sink_endpoint_maps_exactly_to_the_freed_rhs_slot() {
        let code = r#"
            extern "C" { fn free(p: *mut core::ffi::c_void); }
            unsafe fn release(p: *mut i32) { free(p as *mut core::ffi::c_void); }
        "#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = super::super::collect_program(tcx);
            let release = program.functions[0];
            let body = tcx.mir_drops_elaborated_and_const_checked(release).borrow();
            let local = body
                .var_debug_info
                .iter()
                .find_map(|info| {
                    (info.name.as_str() == "p").then(|| match info.value {
                        rustc_middle::mir::VarDebugInfoContents::Place(place) => Some(place.local),
                        _ => None,
                    })?
                })
                .expect("p local");
            let slots = CrateSlots::build(&program);
            let rhs = slots
                .fn_local_slots
                .get(&release)
                .and_then(|universe| universe.slot_for_local_depth(local, 0))
                .map(|slot| SlotRef::Local(release, slot))
                .expect("p slot");
            let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
            let facts = crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(
                &program,
            );
            let endpoints = capture_sink_endpoints(&program, &slots, &origins, &facts)
                .expect("endpoint capture");
            let matched = endpoints.get(&rhs).unwrap_or_else(|| {
                panic!(
                    "rhs endpoint {rhs:?}; captured keys {:?}",
                    endpoints.keys().collect::<Vec<_>>()
                )
            });
            assert_eq!(matched.len(), 1, "{matched:#?}");
            assert_eq!(matched[0].callee, "free");
            assert_ne!(matched[0].operand_local, matched[0].local);
            assert_eq!(matched[0].chain.first(), Some(&matched[0].operand_local));
            assert_eq!(matched[0].chain.last(), Some(&matched[0].local));
            let target = LicP1Target {
                key: LicP1Key {
                    program: "fixture".to_owned(),
                    function: tcx.def_path_str(release.to_def_id()),
                    lhs: SlotKey::of(rhs),
                    rhs: SlotKey::of(rhs),
                },
            };
            let diagnostic = endpoint_diagnostics_tsv(&program, &slots, &[target], &endpoints)
                .expect("diagnostic");
            assert!(diagnostic.contains("\tfree\tbb"), "{diagnostic}");
            let fields = diagnostic
                .lines()
                .nth(1)
                .expect("diagnostic data row")
                .split('\t')
                .collect::<Vec<_>>();
            assert_eq!(fields[10], "1", "direct terminal reaches RHS: {diagnostic}");
            assert_eq!(fields[11], "-", "direct terminal has no load: {diagnostic}");
            assert_eq!(fields[12], "0", "no load cannot hit RHS: {diagnostic}");
        })
        .unwrap();
    }

    #[test]
    fn endpoint_single_load_diagnostic_resolves_owned_slot_key() {
        let code = r#"
            extern "C" { fn free(p: *mut core::ffi::c_void); }
            unsafe fn release(pp: *mut *mut i32) { free((*pp) as *mut core::ffi::c_void); }
        "#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = super::super::collect_program(tcx);
            let release = program.functions[0];
            let body = tcx.mir_drops_elaborated_and_const_checked(release).borrow();
            let pp = body
                .var_debug_info
                .iter()
                .find_map(|info| {
                    (info.name.as_str() == "pp").then(|| match info.value {
                        rustc_middle::mir::VarDebugInfoContents::Place(place) => Some(place.local),
                        _ => None,
                    })?
                })
                .expect("pp local");
            let slots = CrateSlots::build(&program);
            let loaded = slots
                .fn_local_slots
                .get(&release)
                .and_then(|universe| universe.slot_for_local_depth(pp, 1))
                .map(|slot| SlotRef::Local(release, slot))
                .expect("loaded pointee slot");
            let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
            let facts = MutFacts::from_program(&program);
            let endpoints = capture_sink_endpoints(&program, &slots, &origins, &facts)
                .expect("endpoint capture");
            let endpoint = endpoints
                .values()
                .flatten()
                .find(|endpoint| endpoint.callee == "free")
                .expect("free endpoint");
            assert_eq!(endpoint.load_slot, Some(loaded), "{endpoint:#?}");
        })
        .unwrap();
    }

    #[test]
    fn per_lic_row_probe_joins_endpoint_origin_and_callers() {
        let code = r#"
            extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }
            unsafe fn release(p: *mut i32) { free(p as *mut core::ffi::c_void); }
            unsafe fn entry() { let p = malloc(4) as *mut i32; release(p); }
        "#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = super::super::collect_program(tcx);
            let release = program
                .functions
                .iter()
                .copied()
                .find(|function| tcx.item_name(function.to_def_id()).as_str() == "release")
                .expect("release");
            let body = tcx.mir_drops_elaborated_and_const_checked(release).borrow();
            let local = body
                .var_debug_info
                .iter()
                .find_map(|info| {
                    (info.name.as_str() == "p").then(|| match info.value {
                        rustc_middle::mir::VarDebugInfoContents::Place(place) => Some(place.local),
                        _ => None,
                    })?
                })
                .expect("p local");
            let slots = CrateSlots::build(&program);
            let rhs = slots
                .fn_local_slots
                .get(&release)
                .and_then(|universe| universe.slot_for_local_depth(local, 0))
                .map(|slot| SlotRef::Local(release, slot))
                .expect("rhs slot");
            let key = LicP1Key {
                program: "fixture".to_owned(),
                function: tcx.def_path_str(release.to_def_id()),
                lhs: SlotKey::of(rhs),
                rhs: SlotKey::of(rhs),
            };
            let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
            let facts = MutFacts::from_program(&program);
            let rows = probe_targets(
                "fixture",
                &program,
                &slots,
                &origins,
                &facts,
                &[LicP1Target { key }],
            )
            .expect("probe");
            assert_eq!(rows.rows.len(), 1);
            assert_eq!(rows.rows[0].endpoint_matches, 1);
            assert_eq!(rows.rows[0].verdict, Verdict::Yes);
            assert!(
                rows.rows[0]
                    .callers
                    .iter()
                    .any(|caller| caller.contains("entry"))
            );
            let tsv = rows_tsv(&rows.rows);
            assert!(tsv.starts_with("program\tfunction\tlhs\trhs\t"));
            assert!(tsv.contains("\tYES\tclosed_world_frozen_graph\trs-crown\tc080e9e7\n"));
        })
        .unwrap();
    }

    #[test]
    fn terminal_shape_precedence_is_closed_and_typed() {
        assert_eq!(
            classify_terminal_facts(TerminalFacts {
                call: Some(CallFamily::Allocator),
                parameter: false,
                definitions: 0,
                single_load: false,
            }),
            TerminalShape::CallAllocator
        );
        assert_eq!(
            classify_terminal_facts(TerminalFacts {
                call: None,
                parameter: true,
                definitions: 0,
                single_load: false,
            }),
            TerminalShape::Parameter
        );
        assert_eq!(
            classify_terminal_facts(TerminalFacts {
                call: None,
                parameter: false,
                definitions: 2,
                single_load: true,
            }),
            TerminalShape::MultiDef
        );
        assert_eq!(
            classify_terminal_facts(TerminalFacts {
                call: None,
                parameter: false,
                definitions: 1,
                single_load: true,
            }),
            TerminalShape::SingleLoad
        );
    }

    #[test]
    fn endpoint_trace_parser_keeps_placeholder_and_real_units_distinct() {
        let input = "program\tfunction\tlhs\trhs\tfunction_endpoint_count\tcallee\tlocation\t\
                     operand_local\tlocal_chain\tterminal_slot\treaches_rhs\tload_slot\tload_hits_rhs\n\
                     p\tcrate::f\tlocal:1:2\tlocal:1:3\t0\t-\t-\t-\t-\t-\t0\t-\t0\n\
                     p\tcrate::g\tlocal:2:2\tlocal:2:3\t1\tfree\tbb1:4\t_5\t_5->_1\tlocal:2:0\t0\tfield:7\t0\n";
        let rows = parse_endpoint_traces(input, "p").expect("trace fixture");
        assert_eq!(rows.len(), 2);
        assert!(rows[0].placeholder);
        assert!(!rows[1].placeholder);
        assert_eq!(rows[1].terminal_local, Some(Local::from_u32(1)));
    }
}
