//! T1 closed-world origin/caller market probe (measurement-only).

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    time::{Duration, Instant},
};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::Idx;
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
        let mut seen = FxHashSet::default();
        for _ in 0..LOCAL_CHAIN_LIMIT {
            if !seen.insert(local) {
                return None;
            }
            if self.allocator_destinations.contains(&local) {
                return Some((local, true));
            }
            let Some(definitions) = self.definitions.get(&local) else {
                return Some((local, false));
            };
            if definitions.len() != 1 {
                return None;
            }
            let Some(next) = definitions[0] else {
                return Some((local, false));
            };
            local = next;
        }
        None
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
    local: Local,
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
            let Some((local, _allocator_rooted)) =
                LocalDefChain::new(program.tcx, &body).terminal(local)
            else {
                continue;
            };
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
                    local,
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
    })
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
}
