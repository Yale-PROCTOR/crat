//! Test-only P2/S2-3 field-ownership diagnosis on the substrate of record.
//!
//! The corpus path is deliberately two-phase: discovery writes the derived
//! field/store population before any BO solve, then the probe phase spends a
//! capped number of incremental tracked queries only on owning-capable fields.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Write,
    ops::Range,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};

use rustc_middle::{
    mir::{AggregateKind, Operand, Rvalue, StatementKind},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;
use z3::SatResult;

use super::report::Row;
use crate::analyses::borrow_ownership::{
    CrateCtxt, SlotKind,
    borrow_verify::{verify_to_fixpoint_counting_with_flows, with_mode_a_commit_trace},
    coherence::{add_coherence, constrain_field_ownership},
    crate_slots::CrateSlots,
    emit_crate_ownership_constraints,
    mutability_facts::{MutFacts, MutFactsMode},
    origins::compute_origins,
    resolve::{ResolvedSlot, resolve_place},
    slots::{SlotId, SlotOwner},
    solver::{KindSolver, SlotRef, core_label_family},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DiscoveryClass {
    NoOwnedCapableStore,
    StoreBlocked,
    Eligible,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ForceResult {
    NotQueried,
    Sat,
    Unsat,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TerminalBucket {
    NoOwnedCapableStore,
    StoreBlocked,
    HardUnsat,
    SolverUnknown,
    BudgetNotQueried,
    ForceOwnSatNotSelected,
    OwningAccepted,
}

impl TerminalBucket {
    fn label(self) -> &'static str {
        match self {
            TerminalBucket::NoOwnedCapableStore => "no-owned-capable-store",
            TerminalBucket::StoreBlocked => "store-blocked",
            TerminalBucket::HardUnsat => "hard-UNSAT",
            TerminalBucket::SolverUnknown => "solver-unknown",
            TerminalBucket::BudgetNotQueried => "budget-not-queried",
            TerminalBucket::ForceOwnSatNotSelected => "force-own-SAT-not-selected",
            TerminalBucket::OwningAccepted => "Owning-accepted",
        }
    }
}

const DEFAULT_QUERY_BUDGET: usize = 200;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StoreDisposition {
    Resolved,
    AddressOf,
    Unresolved,
}

impl StoreDisposition {
    fn label(self) -> &'static str {
        match self {
            StoreDisposition::Resolved => "resolved",
            StoreDisposition::AddressOf => "address-of",
            StoreDisposition::Unresolved => "unresolved",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct StoreRecord {
    location: String,
    disposition: StoreDisposition,
    rhs_key: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FieldDiscovery {
    field_slot: usize,
    field_key: String,
    stores: Vec<StoreRecord>,
}

impl FieldDiscovery {
    fn resolved_count(&self) -> usize {
        self.stores
            .iter()
            .filter(|store| store.disposition == StoreDisposition::Resolved)
            .count()
    }

    fn blocked_address_of(&self) -> usize {
        self.stores
            .iter()
            .filter(|store| store.disposition == StoreDisposition::AddressOf)
            .count()
    }

    fn blocked_unresolved(&self) -> usize {
        self.stores
            .iter()
            .filter(|store| store.disposition == StoreDisposition::Unresolved)
            .count()
    }

    fn class(&self) -> DiscoveryClass {
        classify_field(
            self.resolved_count(),
            self.blocked_address_of(),
            self.blocked_unresolved(),
        )
    }
}

fn classify_field(resolved: usize, address_of: usize, unresolved: usize) -> DiscoveryClass {
    if address_of + unresolved > 0 {
        DiscoveryClass::StoreBlocked
    } else if resolved == 0 {
        DiscoveryClass::NoOwnedCapableStore
    } else {
        DiscoveryClass::Eligible
    }
}

fn terminal_bucket(
    discovery: DiscoveryClass,
    force: ForceResult,
    accepted_kind: Option<SlotKind>,
) -> TerminalBucket {
    match discovery {
        DiscoveryClass::NoOwnedCapableStore => TerminalBucket::NoOwnedCapableStore,
        DiscoveryClass::StoreBlocked => TerminalBucket::StoreBlocked,
        DiscoveryClass::Eligible => match force {
            ForceResult::NotQueried => TerminalBucket::BudgetNotQueried,
            ForceResult::Unsat => TerminalBucket::HardUnsat,
            ForceResult::Unknown => TerminalBucket::SolverUnknown,
            ForceResult::Sat => match accepted_kind {
                Some(SlotKind::Owning) => TerminalBucket::OwningAccepted,
                Some(SlotKind::Raw | SlotKind::Ref) => TerminalBucket::ForceOwnSatNotSelected,
                None => panic!("a force-own SAT candidate requires an accepted ordinary model"),
            },
        },
    }
}

fn field_key(tcx: TyCtxt<'_>, slots: &CrateSlots, field: SlotId) -> String {
    let slot = slots.field_slots.slot(field);
    let SlotOwner::Field(owner) = slot.owner else {
        panic!("field SlotRef has non-field owner: {field:?}");
    };
    format!(
        "{}::field{}@d{}",
        tcx.def_path_str(owner.struct_did.to_def_id()),
        owner.field_index,
        slot.depth
    )
}

fn slot_key(tcx: TyCtxt<'_>, slots: &CrateSlots, fn_did: LocalDefId, slot: ResolvedSlot) -> String {
    match slot {
        ResolvedSlot::Field(field) => field_key(tcx, slots, field),
        ResolvedSlot::Local(local_slot) => {
            let slot = slots.fn_local_slots[&fn_did].slot(local_slot);
            let SlotOwner::Local(local) = slot.owner else {
                panic!("local slot has non-local owner: {local_slot:?}");
            };
            format!(
                "{}::_{}@d{}",
                tcx.def_path_str(fn_did.to_def_id()),
                local.index(),
                slot.depth
            )
        }
    }
}

fn store_location(tcx: TyCtxt<'_>, fn_did: LocalDefId, bb: usize, stmt: usize) -> String {
    format!("{}:bb{bb}:stmt{stmt}", tcx.def_path_str(fn_did.to_def_id()))
}

fn scan_fields(tcx: TyCtxt<'_>) -> BTreeMap<String, FieldDiscovery> {
    let program = super::collect_program(tcx);
    let slots = CrateSlots::build(&program);
    let mut fields = BTreeMap::new();
    for index in 0..slots.field_slots.len() {
        let field = SlotId::from_usize(index);
        if slots.field_slots.slot(field).depth != 0 {
            continue;
        }
        let key = field_key(tcx, &slots, field);
        assert!(
            fields
                .insert(
                    key.clone(),
                    FieldDiscovery {
                        field_slot: index,
                        field_key: key,
                        stores: Vec::new(),
                    },
                )
                .is_none(),
            "duplicate field key"
        );
    }

    for &fn_did in &program.functions {
        let body_ref = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        let body = &*body_ref;
        for (bb, bbdata) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in bbdata.statements.iter().enumerate() {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                    continue;
                };
                let location = store_location(tcx, fn_did, bb.index(), statement_index);

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
                        let key = field_key(tcx, &slots, field);
                        let Some(record) = fields.get_mut(&key) else {
                            continue;
                        };
                        match operand {
                            Operand::Copy(place) | Operand::Move(place) => {
                                let resolved = resolve_place(&slots, fn_did, body, *place, 0, None);
                                record.stores.push(StoreRecord {
                                    location: location.clone(),
                                    disposition: if resolved.is_some() {
                                        StoreDisposition::Resolved
                                    } else {
                                        StoreDisposition::Unresolved
                                    },
                                    rhs_key: resolved
                                        .map(|slot| slot_key(tcx, &slots, fn_did, slot)),
                                });
                            }
                            Operand::Constant(_) => {}
                        }
                    }
                    continue;
                }

                let Some(ResolvedSlot::Field(field)) =
                    resolve_place(&slots, fn_did, body, *lhs, 0, None)
                else {
                    continue;
                };
                let key = field_key(tcx, &slots, field);
                let Some(record) = fields.get_mut(&key) else {
                    continue;
                };
                let (rhs_place, direct_disposition) = match rvalue {
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                    | Rvalue::CopyForDeref(place)
                    | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
                        (Some(*place), StoreDisposition::Resolved)
                    }
                    Rvalue::Use(Operand::Constant(_))
                    | Rvalue::Cast(_, Operand::Constant(_), _) => continue,
                    Rvalue::Ref(..) | Rvalue::RawPtr(..) => (None, StoreDisposition::AddressOf),
                    _ => (None, StoreDisposition::Unresolved),
                };
                let resolved =
                    rhs_place.and_then(|place| resolve_place(&slots, fn_did, body, place, 0, None));
                record.stores.push(StoreRecord {
                    location,
                    disposition: if rhs_place.is_some() && resolved.is_none() {
                        StoreDisposition::Unresolved
                    } else {
                        direct_disposition
                    },
                    rhs_key: resolved.map(|slot| slot_key(tcx, &slots, fn_did, slot)),
                });
            }
        }
    }
    fields
}

fn tsv_cell(value: &str) -> String {
    value.replace(['\t', '\n', '\r'], "_")
}

fn write_discovery(
    program: &str,
    field_path: &Path,
    store_path: &Path,
    fields: &BTreeMap<String, FieldDiscovery>,
) -> Result<(), String> {
    let mut field_tsv = String::from(
        "program\tfield_key\tfield_slot\tdiscovery_class\tresolved_stores\tblocked_address_of\tblocked_unresolved\n",
    );
    let mut store_tsv =
        String::from("program\tfield_key\tfield_slot\tstore_location\tdisposition\trhs_slot_key\n");
    for field in fields.values() {
        let class = match field.class() {
            DiscoveryClass::NoOwnedCapableStore => "no-owned-capable-store",
            DiscoveryClass::StoreBlocked => "store-blocked",
            DiscoveryClass::Eligible => "eligible",
        };
        field_tsv.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            tsv_cell(program),
            tsv_cell(&field.field_key),
            field.field_slot,
            class,
            field.resolved_count(),
            field.blocked_address_of(),
            field.blocked_unresolved(),
        ));
        for store in &field.stores {
            store_tsv.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\n",
                tsv_cell(program),
                tsv_cell(&field.field_key),
                field.field_slot,
                tsv_cell(&store.location),
                store.disposition.label(),
                tsv_cell(store.rhs_key.as_deref().unwrap_or("-")),
            ));
        }
    }
    fs::write(field_path, field_tsv)
        .map_err(|error| format!("write {}: {error}", field_path.display()))?;
    fs::write(store_path, store_tsv)
        .map_err(|error| format!("write {}: {error}", store_path.display()))
}

pub(super) fn run_discovery_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
    let program = std::env::var("CRAT_BOC1_NAME").expect("discovery requires program name");
    let field_path = std::env::var("CRAT_S23_FIELD_ARTIFACT")
        .expect("discovery requires CRAT_S23_FIELD_ARTIFACT");
    let store_path = std::env::var("CRAT_S23_STORE_ARTIFACT")
        .expect("discovery requires CRAT_S23_STORE_ARTIFACT");
    let fields = scan_fields(tcx);
    write_discovery(
        &program,
        Path::new(&field_path),
        Path::new(&store_path),
        &fields,
    )
    .unwrap_or_else(|error| panic!("{error}"));
    let mut row = Row::default();
    row.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    row.set("fields", fields.len());
    row.set(
        "no_owned_capable_store",
        fields
            .values()
            .filter(|field| field.class() == DiscoveryClass::NoOwnedCapableStore)
            .count(),
    );
    row.set(
        "store_blocked",
        fields
            .values()
            .filter(|field| field.class() == DiscoveryClass::StoreBlocked)
            .count(),
    );
    row.set(
        "eligible",
        fields
            .values()
            .filter(|field| field.class() == DiscoveryClass::Eligible)
            .count(),
    );
    row.set("status", "ok");
    row
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProbeRecord {
    field_key: String,
    field_slot: usize,
    accepted_kind: SlotKind,
    force_result: ForceResult,
    core_families: Vec<String>,
    core_labels: Vec<String>,
}

fn read_target_keys(path: &Path) -> Result<Vec<String>, String> {
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read target keys {}: {error}", path.display()))?;
    let keys = input
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let unique = keys.iter().collect::<BTreeSet<_>>();
    if unique.len() != keys.len() {
        return Err("target key file contains duplicates".to_owned());
    }
    Ok(keys)
}

fn kind_label(kind: SlotKind) -> &'static str {
    match kind {
        SlotKind::Raw => "raw",
        SlotKind::Ref => "ref",
        SlotKind::Owning => "owning",
    }
}

fn write_probe(path: &Path, program: &str, records: &[ProbeRecord]) -> Result<(), String> {
    let mut out = String::from(
        "program\tfield_key\tfield_slot\taccepted_kind\tforce_result\tcore_families\tcore_labels\n",
    );
    for record in records {
        let force = match record.force_result {
            ForceResult::Sat => "sat",
            ForceResult::Unsat => "unsat",
            ForceResult::Unknown => "unknown",
            ForceResult::NotQueried => "not-queried",
        };
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            tsv_cell(program),
            tsv_cell(&record.field_key),
            record.field_slot,
            kind_label(record.accepted_kind),
            force,
            tsv_cell(&record.core_families.join("|")),
            tsv_cell(&record.core_labels.join("|")),
        ));
    }
    fs::write(path, out).map_err(|error| format!("write {}: {error}", path.display()))
}

fn probe_checkpoint_temp_path(path: &Path) -> PathBuf {
    path.with_extension("tsv.tmp")
}

fn write_probe_checkpoint(
    path: &Path,
    program: &str,
    records: &[ProbeRecord],
) -> Result<(), String> {
    let temp = probe_checkpoint_temp_path(path);
    write_probe(&temp, program, records)?;
    fs::rename(&temp, path).map_err(|error| {
        format!(
            "publish checkpoint {} from {}: {error}",
            path.display(),
            temp.display()
        )
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CheckpointProgress {
    phase: String,
    candidate: Option<String>,
    completed: usize,
    elapsed_s: String,
}

fn checkpoint_phase_line(
    phase: &str,
    candidate: Option<&str>,
    completed: usize,
    elapsed: Duration,
) -> String {
    assert!(
        !phase.is_empty() && !phase.bytes().any(|byte| byte.is_ascii_whitespace()),
        "checkpoint phase must be one nonempty token"
    );
    let candidate = candidate.unwrap_or("none");
    assert!(
        !candidate.bytes().any(|byte| byte.is_ascii_whitespace()),
        "checkpoint candidate must be one token"
    );
    format!(
        "BOC1PHASE s23-probe phase={phase} candidate={candidate} completed={completed} t_s={:.3}",
        elapsed.as_secs_f64()
    )
}

fn emit_checkpoint_phase(started: Instant, phase: &str, candidate: Option<&str>, completed: usize) {
    eprintln!(
        "{}",
        checkpoint_phase_line(phase, candidate, completed, started.elapsed())
    );
}

fn parse_checkpoint_phase(line: &str) -> Option<CheckpointProgress> {
    let mut tokens = line.split_whitespace();
    if tokens.next()? != "BOC1PHASE" || tokens.next()? != "s23-probe" {
        return None;
    }
    let fields = tokens
        .filter_map(|token| token.split_once('='))
        .collect::<BTreeMap<_, _>>();
    let phase = fields.get("phase")?.to_string();
    let candidate = match *fields.get("candidate")? {
        "none" => None,
        candidate => Some(candidate.to_owned()),
    };
    let completed = fields.get("completed")?.parse().ok()?;
    let elapsed_s = fields.get("t_s")?.to_string();
    elapsed_s.parse::<f64>().ok()?;
    Some(CheckpointProgress {
        phase,
        candidate,
        completed,
        elapsed_s,
    })
}

pub(super) fn run_probe_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
    let started = Instant::now();
    let program_name = std::env::var("CRAT_BOC1_NAME").expect("probe requires program name");
    let targets_path =
        std::env::var("CRAT_S23_TARGET_KEYS").expect("probe requires CRAT_S23_TARGET_KEYS");
    let probe_path =
        std::env::var("CRAT_S23_PROBE_ARTIFACT").expect("probe requires artifact path");
    let checkpoint_path = std::env::var_os("CRAT_S23_CHECKPOINT_ARTIFACT").map(PathBuf::from);
    emit_checkpoint_phase(started, "worker-start", None, 0);
    let targets =
        read_target_keys(Path::new(&targets_path)).unwrap_or_else(|error| panic!("{error}"));
    assert!(
        !targets.is_empty(),
        "probe worker requires nonempty targets"
    );

    emit_checkpoint_phase(started, "collect-program-start", None, 0);
    let program = super::collect_program(tcx);
    let fields = scan_fields(tcx);
    for key in &targets {
        let field = fields
            .get(key)
            .unwrap_or_else(|| panic!("target field not re-derived: {key}"));
        assert_eq!(
            field.class(),
            DiscoveryClass::Eligible,
            "target field is not eligible: {key}"
        );
    }
    emit_checkpoint_phase(started, "collect-program-complete", None, 0);

    emit_checkpoint_phase(started, "ordinary-start", None, 0);
    let origins = compute_origins(&program);
    let slots = CrateSlots::build(&program);
    let crate_ctxt = CrateCtxt::new(&program);

    let ordinary = KindSolver::new(&slots);
    let (_stats, selectors) =
        emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &ordinary)
            .unwrap_or_else(|error| panic!("ordinary emission: {error:#}"));
    for &fn_did in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        add_coherence(&ordinary, &slots, fn_did, &body);
    }
    let mutability = match MutFactsMode::current() {
        MutFactsMode::Off => MutFacts::all_mut(),
        MutFactsMode::On => MutFacts::from_program(&program),
    };
    let ((model, repair_stats), commit_trace) = with_mode_a_commit_trace(|| {
        verify_to_fixpoint_counting_with_flows(
            &program,
            &slots,
            origins.native_flows(),
            &ordinary,
            &selectors,
            &mutability,
        )
    });
    let model = model.unwrap_or_else(|| {
        panic!(
            "ordinary Mode-A model declined for {program_name}: cap_exhausted={} field_conflict={:?}",
            repair_stats.cap_exhausted, repair_stats.field_conflict_decline
        )
    });
    emit_checkpoint_phase(started, "ordinary-complete", None, 0);

    emit_checkpoint_phase(started, "tracked-start", None, 0);
    let tracked = KindSolver::new_tracked(&slots);
    let (_stats, _selectors) =
        emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &tracked)
            .unwrap_or_else(|error| panic!("tracked emission: {error:#}"));
    let tracker = tracked.tracker().expect("new_tracked has tracker");
    tracker.set_context("coherence");
    for &fn_did in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        add_coherence(&tracked, &slots, fn_did, &body);
    }
    tracker.set_context("field-law");
    constrain_field_ownership(&tracked, &slots, &program);
    for commit in &commit_trace {
        tracker.set_context(&format!("mode-a-round{}", commit.round));
        tracked.add_borrow_exclusion(Some(commit.target), &[]);
    }
    assert_eq!(
        tracked.optimize().check(&tracker.tracks()),
        SatResult::Sat,
        "tracked hard baseline is not SAT before force-own queries"
    );
    emit_checkpoint_phase(started, "tracked-baseline-complete", None, 0);

    let mut records = Vec::with_capacity(targets.len());
    for key in targets {
        emit_checkpoint_phase(started, "force-own-start", Some(&key), records.len());
        let field = &fields[&key];
        let slot = SlotRef::Field(SlotId::from_usize(field.field_slot));
        let accepted_kind = *model
            .get(&slot)
            .unwrap_or_else(|| panic!("accepted model lacks target field: {key}"));
        tracked.push_scope();
        tracker.set_context("s23-force-own");
        tracked.assert_owning(slot);
        let result = tracked.optimize().check(&tracker.tracks());
        let mut labels = if result == SatResult::Unsat {
            tracked
                .optimize()
                .get_unsat_core()
                .iter()
                .filter_map(|literal| tracker.label_of(literal))
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        labels.sort();
        labels.dedup();
        let families = labels
            .iter()
            .filter_map(|label| core_label_family(label))
            .map(str::to_owned)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        tracked.pop_scope();
        records.push(ProbeRecord {
            field_key: key.clone(),
            field_slot: field.field_slot,
            accepted_kind,
            force_result: match result {
                SatResult::Sat => ForceResult::Sat,
                SatResult::Unsat => ForceResult::Unsat,
                SatResult::Unknown => ForceResult::Unknown,
            },
            core_families: families,
            core_labels: labels,
        });
        if let Some(checkpoint_path) = &checkpoint_path {
            write_probe_checkpoint(checkpoint_path, &program_name, &records)
                .unwrap_or_else(|error| panic!("{error}"));
            emit_checkpoint_phase(started, "checkpoint-written", Some(&key), records.len());
        } else {
            emit_checkpoint_phase(started, "force-own-complete", Some(&key), records.len());
        }
    }
    emit_checkpoint_phase(started, "finalize-start", None, records.len());
    write_probe(Path::new(&probe_path), &program_name, &records)
        .unwrap_or_else(|error| panic!("{error}"));
    emit_checkpoint_phase(started, "complete", None, records.len());

    let mut row = Row::default();
    row.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    row.set("queried", records.len());
    row.set(
        "hard_unsat",
        records
            .iter()
            .filter(|record| record.force_result == ForceResult::Unsat)
            .count(),
    );
    row.set(
        "force_sat",
        records
            .iter()
            .filter(|record| record.force_result == ForceResult::Sat)
            .count(),
    );
    row.set(
        "solver_unknown",
        records
            .iter()
            .filter(|record| record.force_result == ForceResult::Unknown)
            .count(),
    );
    row.set(
        "owning_accepted",
        records
            .iter()
            .filter(|record| record.accepted_kind == SlotKind::Owning)
            .count(),
    );
    row.set("mode_a_commits", commit_trace.len());
    row.set("ordinary_check_sat", ordinary.check_sat_count());
    row.set("tracked_check_sat", records.len() + 1);
    row.set(
        "t_total_s",
        format!("{:.3}", started.elapsed().as_secs_f64()),
    );
    row.set("status", "ok");
    row
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CandidateSummary {
    program: String,
    field_key: String,
    field_slot: usize,
    discovery: DiscoveryClass,
    resolved_stores: usize,
    blocked_address_of: usize,
    blocked_unresolved: usize,
}

fn parse_discovery(path: &Path) -> Result<Vec<CandidateSummary>, String> {
    const HEADER: &str = "program\tfield_key\tfield_slot\tdiscovery_class\tresolved_stores\tblocked_address_of\tblocked_unresolved";
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read discovery {}: {error}", path.display()))?;
    let mut lines = input.lines();
    if lines.next() != Some(HEADER) {
        return Err(format!("discovery header drift: {}", path.display()));
    }
    let mut rows = Vec::new();
    for (offset, line) in lines.enumerate() {
        let columns = line.split('\t').collect::<Vec<_>>();
        if columns.len() != 7 {
            return Err(format!(
                "discovery {} line {} has {} columns",
                path.display(),
                offset + 2,
                columns.len()
            ));
        }
        let parse_count = |column: usize, name: &str| {
            columns[column].parse::<usize>().map_err(|error| {
                format!(
                    "discovery {} line {} {name}: {error}",
                    path.display(),
                    offset + 2
                )
            })
        };
        let discovery = match columns[3] {
            "no-owned-capable-store" => DiscoveryClass::NoOwnedCapableStore,
            "store-blocked" => DiscoveryClass::StoreBlocked,
            "eligible" => DiscoveryClass::Eligible,
            other => return Err(format!("unknown discovery class {other:?}")),
        };
        let row = CandidateSummary {
            program: columns[0].to_owned(),
            field_key: columns[1].to_owned(),
            field_slot: parse_count(2, "field_slot")?,
            discovery,
            resolved_stores: parse_count(4, "resolved_stores")?,
            blocked_address_of: parse_count(5, "blocked_address_of")?,
            blocked_unresolved: parse_count(6, "blocked_unresolved")?,
        };
        if classify_field(
            row.resolved_stores,
            row.blocked_address_of,
            row.blocked_unresolved,
        ) != row.discovery
        {
            return Err(format!(
                "discovery class/count mismatch for {} {}",
                row.program, row.field_key
            ));
        }
        rows.push(row);
    }
    Ok(rows)
}

fn validate_stores(path: &Path, candidates: &[CandidateSummary]) -> Result<(), String> {
    const HEADER: &str =
        "program\tfield_key\tfield_slot\tstore_location\tdisposition\trhs_slot_key";
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read stores {}: {error}", path.display()))?;
    let mut lines = input.lines();
    if lines.next() != Some(HEADER) {
        return Err(format!("store header drift: {}", path.display()));
    }
    let known = candidates
        .iter()
        .map(|candidate| {
            (
                (candidate.program.as_str(), candidate.field_key.as_str()),
                candidate,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut counts: BTreeMap<(&str, &str), (usize, usize, usize)> = BTreeMap::new();
    let mut identities = BTreeSet::new();
    for (offset, line) in lines.enumerate() {
        let columns = line.split('\t').collect::<Vec<_>>();
        if columns.len() != 6 {
            return Err(format!(
                "stores {} line {} has {} columns",
                path.display(),
                offset + 2,
                columns.len()
            ));
        }
        let key = (columns[0], columns[1]);
        let candidate = known.get(&key).ok_or_else(|| {
            format!(
                "store row references unknown candidate {} {}",
                columns[0], columns[1]
            )
        })?;
        if columns[2].parse::<usize>().ok() != Some(candidate.field_slot) {
            return Err(format!("store field-slot mismatch for {} {}", key.0, key.1));
        }
        if !identities.insert((columns[0], columns[1], columns[3], columns[5])) {
            return Err(format!("duplicate store identity for {} {}", key.0, key.1));
        }
        let entry = counts.entry(key).or_default();
        match columns[4] {
            "resolved" if columns[5] != "-" => entry.0 += 1,
            "address-of" if columns[5] == "-" => entry.1 += 1,
            "unresolved" if columns[5] == "-" => entry.2 += 1,
            other => {
                return Err(format!(
                    "invalid store disposition/RHS pair {other:?}/{}",
                    columns[5]
                ));
            }
        }
    }
    for candidate in candidates {
        let actual = counts
            .get(&(candidate.program.as_str(), candidate.field_key.as_str()))
            .copied()
            .unwrap_or_default();
        let expected = (
            candidate.resolved_stores,
            candidate.blocked_address_of,
            candidate.blocked_unresolved,
        );
        if actual != expected {
            return Err(format!(
                "store counts mismatch for {} {}: artifact={actual:?} fields={expected:?}",
                candidate.program, candidate.field_key
            ));
        }
    }
    Ok(())
}

fn parse_probe(path: &Path) -> Result<Vec<ProbeRecord>, String> {
    parse_probe_for_program(path, None)
}

fn parse_probe_for_program(
    path: &Path,
    expected_program: Option<&str>,
) -> Result<Vec<ProbeRecord>, String> {
    const HEADER: &str =
        "program\tfield_key\tfield_slot\taccepted_kind\tforce_result\tcore_families\tcore_labels";
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read probe {}: {error}", path.display()))?;
    let mut lines = input.lines();
    if lines.next() != Some(HEADER) {
        return Err(format!("probe header drift: {}", path.display()));
    }
    let mut rows = Vec::new();
    for (offset, line) in lines.enumerate() {
        let columns = line.split('\t').collect::<Vec<_>>();
        if columns.len() != 7 {
            return Err(format!(
                "probe {} line {} has {} columns",
                path.display(),
                offset + 2,
                columns.len()
            ));
        }
        if let Some(expected_program) = expected_program
            && columns[0] != expected_program
        {
            return Err(format!(
                "probe {} line {} program identity mismatch: expected {expected_program:?}, got {:?}",
                path.display(),
                offset + 2,
                columns[0]
            ));
        }
        let accepted_kind = match columns[3] {
            "raw" => SlotKind::Raw,
            "ref" => SlotKind::Ref,
            "owning" => SlotKind::Owning,
            other => return Err(format!("unknown accepted kind {other:?}")),
        };
        let force_result = match columns[4] {
            "sat" => ForceResult::Sat,
            "unsat" => ForceResult::Unsat,
            "unknown" => ForceResult::Unknown,
            "not-queried" => ForceResult::NotQueried,
            other => return Err(format!("unknown force result {other:?}")),
        };
        rows.push(ProbeRecord {
            field_key: columns[1].to_owned(),
            field_slot: columns[2].parse().map_err(|error| {
                format!(
                    "probe {} line {} field_slot: {error}",
                    path.display(),
                    offset + 2
                )
            })?,
            accepted_kind,
            force_result,
            core_families: if columns[5].is_empty() {
                Vec::new()
            } else {
                columns[5].split('|').map(str::to_owned).collect()
            },
            core_labels: if columns[6].is_empty() {
                Vec::new()
            } else {
                columns[6].split('|').map(str::to_owned).collect()
            },
        });
    }
    Ok(rows)
}

fn parse_combined_probe(
    path: &Path,
    identity: &MeasurementIdentity,
) -> Result<Vec<(String, ProbeRecord)>, String> {
    const HEADER: &str = "platform\tmachine_id\tprogram\tfield_key\tfield_slot\taccepted_kind\tforce_result\tcore_families\tcore_labels";
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read combined probe {}: {error}", path.display()))?;
    let mut lines = input.lines();
    if lines.next() != Some(HEADER) {
        return Err(format!("combined probe header drift: {}", path.display()));
    }
    let mut rows = Vec::new();
    for (offset, line) in lines.enumerate() {
        let columns = line.split('\t').collect::<Vec<_>>();
        if columns.len() != 9 {
            return Err(format!(
                "combined probe {} line {} has {} columns",
                path.display(),
                offset + 2,
                columns.len()
            ));
        }
        if columns[0] != identity.platform || columns[1] != identity.machine_id {
            return Err(format!(
                "combined probe {} line {} measurement identity mismatch",
                path.display(),
                offset + 2
            ));
        }
        let accepted_kind = match columns[5] {
            "raw" => SlotKind::Raw,
            "ref" => SlotKind::Ref,
            "owning" => SlotKind::Owning,
            other => return Err(format!("unknown accepted kind {other:?}")),
        };
        let force_result = match columns[6] {
            "sat" => ForceResult::Sat,
            "unsat" => ForceResult::Unsat,
            "unknown" => ForceResult::Unknown,
            "not-queried" => ForceResult::NotQueried,
            other => return Err(format!("unknown force result {other:?}")),
        };
        rows.push((
            columns[2].to_owned(),
            ProbeRecord {
                field_key: columns[3].to_owned(),
                field_slot: columns[4].parse().map_err(|error| {
                    format!(
                        "combined probe {} line {} field_slot: {error}",
                        path.display(),
                        offset + 2
                    )
                })?,
                accepted_kind,
                force_result,
                core_families: if columns[7].is_empty() {
                    Vec::new()
                } else {
                    columns[7].split('|').map(str::to_owned).collect()
                },
                core_labels: if columns[8].is_empty() {
                    Vec::new()
                } else {
                    columns[8].split('|').map(str::to_owned).collect()
                },
            },
        ));
    }
    Ok(rows)
}

fn append_artifact(combined: &mut String, path: &Path) -> Result<(), String> {
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read artifact {}: {error}", path.display()))?;
    let mut lines = input.lines();
    let header = lines
        .next()
        .ok_or_else(|| format!("empty artifact {}", path.display()))?;
    if combined.is_empty() {
        combined.push_str(header);
        combined.push('\n');
    } else if combined.lines().next() != Some(header) {
        return Err(format!("combined header mismatch at {}", path.display()));
    }
    for line in lines {
        combined.push_str(line);
        combined.push('\n');
    }
    Ok(())
}

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

fn write_targets(path: &Path, keys: &[String]) -> Result<(), String> {
    let mut out = keys.join("\n");
    out.push('\n');
    fs::write(path, out).map_err(|error| format!("write targets {}: {error}", path.display()))
}

fn checkpoint_batch_ranges(total: usize) -> Result<Vec<Range<usize>>, String> {
    if total != P2_BROTLI_ELIGIBLE {
        return Err(format!(
            "checkpoint plan requires exactly {P2_BROTLI_ELIGIBLE} candidates, got {total}"
        ));
    }
    let mut start = 0usize;
    Ok(P2_CHECKPOINT_BATCH_SIZES
        .iter()
        .map(|size| {
            let range = start..start + size;
            start = range.end;
            range
        })
        .collect())
}

fn checkpoint_batch_timeout_s(value: Option<&str>) -> Result<usize, String> {
    let timeout_s = match value {
        Some(value) => value
            .parse::<usize>()
            .map_err(|_| format!("invalid checkpoint wall cap: {value}"))?,
        None => 14400,
    };
    if timeout_s != 14400 {
        return Err(format!(
            "Linux checkpoint wall-liveness bound must be exactly 14,400s, got {timeout_s}s"
        ));
    }
    Ok(timeout_s)
}

fn checkpoint_data_value(status: &str) -> &'static str {
    if status == "ok" { "true" } else { "false" }
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let output = Command::new("shasum")
        .args(["-a", "256"])
        .arg(path)
        .output()
        .map_err(|error| format!("run shasum for {}: {error}", path.display()))?;
    if !output.status.success() {
        return Err(format!(
            "shasum failed for {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .next()
        .filter(|digest| digest.len() == 64)
        .map(str::to_owned)
        .ok_or_else(|| format!("invalid shasum output for {}", path.display()))
}

fn sha256_text(input: &str) -> Result<String, String> {
    let mut child = Command::new("shasum")
        .args(["-a", "256"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("spawn shasum: {error}"))?;
    child
        .stdin
        .take()
        .ok_or_else(|| "open shasum stdin".to_owned())?
        .write_all(input.as_bytes())
        .map_err(|error| format!("write shasum stdin: {error}"))?;
    let output = child
        .wait_with_output()
        .map_err(|error| format!("wait for shasum: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "shasum failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .next()
        .filter(|digest| digest.len() == 64)
        .map(str::to_owned)
        .ok_or_else(|| "invalid shasum output for text".to_owned())
}

fn write_sha256_manifest(root: &Path, files: &[PathBuf], manifest: &Path) -> Result<(), String> {
    let mut entries = files
        .iter()
        .map(|path| {
            let relative = path.strip_prefix(root).map_err(|_| {
                format!(
                    "manifest path {} is outside {}",
                    path.display(),
                    root.display()
                )
            })?;
            if relative.as_os_str().is_empty() {
                return Err("manifest cannot hash its root directory".to_owned());
            }
            Ok((relative.to_path_buf(), sha256_file(path)?))
        })
        .collect::<Result<Vec<_>, String>>()?;
    entries.sort_by(|left, right| left.0.cmp(&right.0));
    let rendered = entries
        .iter()
        .map(|(relative, digest)| format!("{digest}  ./{}\n", relative.display()))
        .collect::<String>();
    fs::write(manifest, rendered)
        .map_err(|error| format!("write manifest {}: {error}", manifest.display()))
}

fn verify_sha256_manifest(root: &Path, manifest: &Path) -> Result<(), String> {
    let manifest_name = manifest.strip_prefix(root).map_err(|_| {
        format!(
            "manifest {} is outside verification root {}",
            manifest.display(),
            root.display()
        )
    })?;
    let output = Command::new("shasum")
        .args(["-a", "256", "-c"])
        .arg(manifest_name)
        .current_dir(root)
        .output()
        .map_err(|error| format!("verify manifest {}: {error}", manifest.display()))?;
    if output.status.success() {
        Ok(())
    } else {
        Err(format!(
            "manifest verification failed at {}: {} {}",
            manifest.display(),
            String::from_utf8_lossy(&output.stdout).trim(),
            String::from_utf8_lossy(&output.stderr).trim()
        ))
    }
}

fn parse_receipt(path: &Path) -> Result<BTreeMap<String, String>, String> {
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read receipt {}: {error}", path.display()))?;
    let mut values = BTreeMap::new();
    for (offset, line) in input.lines().enumerate() {
        let Some((key, value)) = line.split_once('=') else {
            return Err(format!(
                "receipt {} line {} lacks '='",
                path.display(),
                offset + 1
            ));
        };
        if values.insert(key.to_owned(), value.to_owned()).is_some() {
            return Err(format!(
                "duplicate receipt key {key:?} in {}",
                path.display()
            ));
        }
    }
    Ok(values)
}

#[derive(Clone, Debug)]
struct FinalRecord {
    candidate: CandidateSummary,
    bucket: TerminalBucket,
    accepted_kind: Option<SlotKind>,
    force_result: ForceResult,
    core_families: Vec<String>,
}

fn render_final_tsv(records: &[FinalRecord], identity: &MeasurementIdentity) -> String {
    let mut out = String::from(
        "platform\tmachine_id\tprogram\tfield_key\tfield_slot\tdiscovery_class\tresolved_stores\tblocked_address_of\tblocked_unresolved\taccepted_kind\tforce_result\tterminal_bucket\tcore_families\n",
    );
    for record in records {
        let discovery = match record.candidate.discovery {
            DiscoveryClass::NoOwnedCapableStore => "no-owned-capable-store",
            DiscoveryClass::StoreBlocked => "store-blocked",
            DiscoveryClass::Eligible => "eligible",
        };
        let force = match record.force_result {
            ForceResult::NotQueried => "not-queried",
            ForceResult::Sat => "sat",
            ForceResult::Unsat => "unsat",
            ForceResult::Unknown => "unknown",
        };
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            identity.platform,
            identity.machine_id,
            record.candidate.program,
            record.candidate.field_key,
            record.candidate.field_slot,
            discovery,
            record.candidate.resolved_stores,
            record.candidate.blocked_address_of,
            record.candidate.blocked_unresolved,
            record.accepted_kind.map(kind_label).unwrap_or("-"),
            force,
            record.bucket.label(),
            record.core_families.join("|"),
        ));
    }
    out
}

fn artifact_path(root: &Path, phase: &str, program: &str, suffix: &str) -> PathBuf {
    root.join(phase).join(format!("{program}.{suffix}"))
}

/// P2 corpus driver. Discovery is a strict artifact boundary: every one of the
/// 20 derived programs must finish and its field/store rows must be merged
/// before the first ordinary BO solve or tracked query is launched.
#[test]
#[ignore = "P2/S2-3 derived-corpus diagnosis; run explicitly"]
fn s23_p2_corpus() {
    let measurement_identity = MeasurementIdentity::from_env();
    let root = super::orchestrate::workspace_root()
        .canonicalize()
        .expect("canonical workspace root");
    assert!(
        !super::orchestrate::git_dirty(),
        "commit the green P2 harness before measurement"
    );
    assert!(
        matches!(
            std::env::var("CRAT_BOC1_SUBSTRATE").as_deref(),
            Err(_) | Ok("derived")
        ),
        "P2 defaults to the derived substrate and refuses raw"
    );
    assert_eq!(
        std::env::var("CRAT_BO_REPAIR").as_deref(),
        Ok("mode_a"),
        "P2 profile requires Mode-A"
    );
    assert_eq!(
        std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
        Ok("0"),
        "P2 profile requires L2 off"
    );
    assert_eq!(
        std::env::var("CRAT_BO_SAFE_MONO").as_deref(),
        Ok("per_site"),
        "P2 profile requires per-site SAFE-MONO"
    );
    assert_eq!(
        std::env::var("CRAT_BO_FORK_ENGINE").as_deref(),
        Ok("fork"),
        "P2 profile requires the fork engine"
    );
    assert_eq!(
        std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
        Ok("uncapped"),
        "the dedicated Linux P2 lane runs without a harness RSS cap"
    );

    let corpus_link = root.join("benchmarks/rs-crown-derived");
    assert!(
        fs::symlink_metadata(&corpus_link)
            .expect("derived corpus metadata")
            .file_type()
            .is_symlink(),
        "derived corpus must retain its read-only symlink shape"
    );
    let snapshot = PathBuf::from(
        std::env::var_os("CRAT_S23_SNAPSHOT").expect("P2 requires CRAT_S23_SNAPSHOT"),
    );
    assert_eq!(
        fs::read_dir(&snapshot)
            .expect("read snapshot")
            .filter_map(Result::ok)
            .filter(|entry| entry.file_type().is_ok_and(|kind| kind.is_file()))
            .count(),
        100,
        "P2 snapshot inventory drifted"
    );
    let deps_link = root.join("deps_crate/target");
    assert!(
        fs::symlink_metadata(&deps_link)
            .expect("deps metadata")
            .file_type()
            .is_symlink(),
        "deps_crate provisioning must remain a read-only symlink"
    );

    let out = PathBuf::from(
        std::env::var_os("CRAT_BOC1_OUT").expect("P2 requires a private CRAT_BOC1_OUT"),
    )
    .join("s23-p2");
    assert!(
        !out.starts_with(root.join("target/boc1")),
        "P2 must not write the ladder lane artifact tree"
    );
    for phase in ["discovery", "stores", "targets", "probes"] {
        fs::create_dir_all(out.join(phase)).expect("create P2 artifact directory");
    }
    let discovery_timeout =
        Duration::from_secs(env_usize("CRAT_S23_DISCOVERY_TIMEOUT_SECS", 900) as u64);
    let probe_timeout = Duration::from_secs(env_usize("CRAT_S23_PROBE_TIMEOUT_SECS", 1800) as u64);

    let mut all_candidates = Vec::new();
    let mut combined_fields = String::new();
    let mut combined_stores = String::new();
    for corpus_program in super::CORPUS {
        let input = corpus_link
            .join(corpus_program.name)
            .join(corpus_program.lib_root);
        let field_path = artifact_path(&out, "discovery", corpus_program.name, "fields.tsv");
        let store_path = artifact_path(&out, "stores", corpus_program.name, "stores.tsv");
        let outcome = super::orchestrate::run_child_env(
            corpus_program.name,
            &input,
            "s23-discover",
            discovery_timeout,
            &[
                ("CRAT_S23_FIELD_ARTIFACT", field_path.display().to_string()),
                ("CRAT_S23_STORE_ARTIFACT", store_path.display().to_string()),
            ],
        );
        assert_eq!(
            outcome.status, "ok",
            "P2 discovery STOP at {}: status={} peak_rss_kb={} wall_s={:.3} note={}",
            corpus_program.name, outcome.status, outcome.peak_rss_kb, outcome.wall_s, outcome.note
        );
        let mut candidates = parse_discovery(&field_path).unwrap_or_else(|error| panic!("{error}"));
        assert!(
            candidates
                .iter()
                .all(|candidate| candidate.program == corpus_program.name),
            "discovery artifact program identity drift"
        );
        validate_stores(&store_path, &candidates).unwrap_or_else(|error| panic!("{error}"));
        append_artifact(&mut combined_fields, &field_path)
            .unwrap_or_else(|error| panic!("{error}"));
        append_artifact(&mut combined_stores, &store_path)
            .unwrap_or_else(|error| panic!("{error}"));
        all_candidates.append(&mut candidates);
    }
    all_candidates.sort_by(|left, right| {
        (&left.program, &left.field_key).cmp(&(&right.program, &right.field_key))
    });
    assert!(
        !all_candidates.is_empty(),
        "P2 field universe must be nonempty"
    );
    let identities = all_candidates
        .iter()
        .map(|candidate| (&candidate.program, &candidate.field_key))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        identities.len(),
        all_candidates.len(),
        "duplicate P2 candidate identity"
    );
    fs::write(out.join("candidate-universe.tsv"), &combined_fields)
        .expect("write combined candidate universe");
    fs::write(out.join("store-sites.tsv"), &combined_stores).expect("write combined store sites");

    let eligible = all_candidates
        .iter()
        .filter(|candidate| candidate.discovery == DiscoveryClass::Eligible)
        .map(|candidate| (candidate.program.clone(), candidate.field_key.clone()))
        .collect::<Vec<_>>();
    assert!(
        !eligible.is_empty(),
        "P2 force-own entering population must be nonempty"
    );
    let eligible_len = eligible.len();
    match std::env::var("CRAT_S23_DISCOVERY_ONLY").as_deref() {
        Ok("1") => {
            let candidate_universe = out.join("candidate-universe.tsv");
            assert_eq!(
                sha256_file(&candidate_universe).expect("hash candidate universe"),
                P2_CANDIDATE_UNIVERSE_SHA256,
                "Linux discovery does not reproduce the macOS checkpoint universe"
            );
            let bootstrap_provenance = out.join("bootstrap-provenance.txt");
            fs::write(
                &bootstrap_provenance,
                format!(
                    "machine_id={}\nplatform={}\nstatus=discovery-only\nanalysis_head={}\nmac_base_manifest_sha256={}\ncandidate_universe_sha256={}\nscreened={}\neligible={}\n",
                    measurement_identity.machine_id,
                    measurement_identity.platform,
                    super::orchestrate::git_sha(),
                    P2_BASE_MANIFEST_SHA256,
                    P2_CANDIDATE_UNIVERSE_SHA256,
                    all_candidates.len(),
                    eligible_len,
                ),
            )
            .expect("write discovery-only provenance");
            let mut artifacts = vec![
                candidate_universe,
                out.join("store-sites.tsv"),
                bootstrap_provenance,
            ];
            for phase in ["discovery", "stores"] {
                artifacts.extend(
                    fs::read_dir(out.join(phase))
                        .expect("read discovery-only phase")
                        .filter_map(Result::ok)
                        .map(|entry| entry.path()),
                );
            }
            artifacts.sort();
            let manifest = out.join("artifact-manifest.sha256");
            write_sha256_manifest(&out, &artifacts, &manifest)
                .unwrap_or_else(|error| panic!("write discovery-only manifest: {error}"));
            verify_sha256_manifest(&out, &manifest)
                .unwrap_or_else(|error| panic!("verify discovery-only manifest: {error}"));
            println!(
                "S23P2BOOTSTRAP machine_id={} platform={} screened={} eligible={} candidate_universe_sha256={}",
                measurement_identity.machine_id,
                measurement_identity.platform,
                all_candidates.len(),
                eligible_len,
                P2_CANDIDATE_UNIVERSE_SHA256,
            );
            return;
        }
        Err(_) | Ok("0") => {}
        Ok(other) => panic!("CRAT_S23_DISCOVERY_ONLY must be 0 or 1, got {other:?}"),
    }
    let query_budget = env_usize("CRAT_S23_QUERY_BUDGET", DEFAULT_QUERY_BUDGET);
    assert!(query_budget > 0, "P2 query budget must be positive");
    let selected = eligible
        .into_iter()
        .take(query_budget)
        .collect::<BTreeSet<_>>();
    let mut selected_by_program: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (program, key) in &selected {
        selected_by_program
            .entry(program.clone())
            .or_default()
            .push(key.clone());
    }

    let mut probes = BTreeMap::new();
    let mut probe_wall_s = 0.0f64;
    let mut probe_peak_rss_kb = BTreeMap::new();
    for corpus_program in super::CORPUS {
        let Some(keys) = selected_by_program.get(corpus_program.name) else {
            continue;
        };
        let target_path = artifact_path(&out, "targets", corpus_program.name, "targets.txt");
        let probe_path = artifact_path(&out, "probes", corpus_program.name, "probes.tsv");
        write_targets(&target_path, keys).unwrap_or_else(|error| panic!("{error}"));
        let input = corpus_link
            .join(corpus_program.name)
            .join(corpus_program.lib_root);
        let outcome = super::orchestrate::run_child_env(
            corpus_program.name,
            &input,
            "s23-probe",
            probe_timeout,
            &[
                ("CRAT_S23_TARGET_KEYS", target_path.display().to_string()),
                ("CRAT_S23_PROBE_ARTIFACT", probe_path.display().to_string()),
            ],
        );
        assert_eq!(
            outcome.status, "ok",
            "P2 probe STOP at {}: status={} peak_rss_kb={} wall_s={:.3} note={}",
            corpus_program.name, outcome.status, outcome.peak_rss_kb, outcome.wall_s, outcome.note
        );
        probe_wall_s += outcome.wall_s;
        probe_peak_rss_kb.insert(corpus_program.name.to_owned(), outcome.peak_rss_kb);
        let rows = parse_probe(&probe_path).unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(rows.len(), keys.len(), "probe row count drift");
        for row in rows {
            let identity = (corpus_program.name.to_owned(), row.field_key.clone());
            assert!(
                selected.contains(&identity),
                "probe emitted an unselected key"
            );
            assert!(
                probes.insert(identity, row).is_none(),
                "duplicate probe key"
            );
        }
    }
    assert_eq!(probes.len(), selected.len(), "selected/probed mismatch");

    let mut final_records = Vec::with_capacity(all_candidates.len());
    for candidate in all_candidates {
        let identity = (candidate.program.clone(), candidate.field_key.clone());
        let probe = probes.get(&identity);
        let (force_result, accepted_kind, core_families) = match probe {
            Some(probe) => (
                probe.force_result,
                Some(probe.accepted_kind),
                probe.core_families.clone(),
            ),
            None => (ForceResult::NotQueried, None, Vec::new()),
        };
        let bucket = terminal_bucket(candidate.discovery, force_result, accepted_kind);
        final_records.push(FinalRecord {
            candidate,
            bucket,
            accepted_kind,
            force_result,
            core_families,
        });
    }
    fs::write(
        out.join("classification.tsv"),
        render_final_tsv(&final_records, &measurement_identity),
    )
    .expect("write final classification");

    let mut bucket_counts = BTreeMap::new();
    let mut first_witness = BTreeMap::new();
    for record in &final_records {
        *bucket_counts.entry(record.bucket.label()).or_insert(0usize) += 1;
        first_witness
            .entry(record.bucket.label())
            .or_insert_with(|| {
                format!(
                    "{}|{}",
                    record.candidate.program, record.candidate.field_key
                )
            });
    }
    let hard_unsat = final_records
        .iter()
        .filter(|record| record.bucket == TerminalBucket::HardUnsat)
        .collect::<Vec<_>>();
    let own_assume_cores = hard_unsat
        .iter()
        .filter(|record| {
            record
                .core_families
                .iter()
                .any(|family| family == "own-assume")
        })
        .count();
    let mut family_histogram = BTreeMap::new();
    for record in &hard_unsat {
        for family in &record.core_families {
            *family_histogram.entry(family.clone()).or_insert(0usize) += 1;
        }
    }
    let force_sat = final_records
        .iter()
        .filter(|record| record.force_result == ForceResult::Sat)
        .count();
    let solver_unknown = bucket_counts
        .get(TerminalBucket::SolverUnknown.label())
        .copied()
        .unwrap_or(0);
    assert_eq!(
        solver_unknown, 0,
        "P2 STOP: tracked solver returned Unknown"
    );

    let counts_line = |map: &BTreeMap<&str, usize>| {
        map.iter()
            .map(|(key, value)| format!("{key}={value}"))
            .collect::<Vec<_>>()
            .join(" ")
    };
    let report = format!(
        "# P2 / S2-3 derived-substrate diagnosis\n\n\
         - Measurement identity: machine `{}`, platform `{}`; every count and timing below belongs to this identity, and timings are not compared across machines.\n\
         - Screened depth-0 pointer-field universe: **{}**.\n\
         - Re-derived eligible owning-store candidates: **{}** (historical raw-form 155 is context only, not inherited).\n\
         - Targeted tracked-query budget: **{}**; queried **{}**; budget-not-queried **{}**.\n\
         - Hard-UNSAT: **{}**; cores containing `own-assume`: **{}**.\n\
         - Force-own SAT: **{}**; Owning in the accepted ordinary model: **{}**.\n\
         - Probe wall sum: **{:.3}s** (programs serialized); harness memory limit: **uncapped**.\n\
         - Terminal counts: `{}`.\n\
         - Core-family incidence (raw tracked cores; families are incidence, not necessity): `{}`.\n\n\
         ## Deterministic first witnesses\n\n{}\n\
         ## Controls and scope\n\n\
         Discovery completed and the combined candidate/store artifacts were written before any BO solve. The classifier unit test exercises every terminal bucket, including a positive synthetic `Owning accepted` control. A zero bucket is interpreted only against the nonempty screened/eligible populations above. Production analysis code was read-only.\n",
        measurement_identity.machine_id,
        measurement_identity.platform,
        final_records.len(),
        eligible_len,
        query_budget,
        selected.len(),
        bucket_counts
            .get(TerminalBucket::BudgetNotQueried.label())
            .copied()
            .unwrap_or(0),
        hard_unsat.len(),
        own_assume_cores,
        force_sat,
        bucket_counts
            .get(TerminalBucket::OwningAccepted.label())
            .copied()
            .unwrap_or(0),
        probe_wall_s,
        counts_line(&bucket_counts),
        family_histogram
            .iter()
            .map(|(family, count)| format!("{family}={count}"))
            .collect::<Vec<_>>()
            .join(" "),
        first_witness
            .iter()
            .map(|(bucket, witness)| format!("- `{bucket}`: `{witness}`"))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    fs::write(out.join("report.md"), report).expect("write P2 report");
    let provenance = format!(
        "machine_id={}\nplatform={}\nanalysis_worktree_head={}\nsubstrate=derived\nsubstrate_selector={}\nsnapshot={}\nsnapshot_files=100\ndeps_shape=read-only-symlink\nrepair=mode_a\nl2=0\nsafe_mono=per_site\nfork_engine=fork\nmemory_limit=uncapped\nquery_budget={}\nqueried={}\nprobe_wall_sum_s={:.3}\nprobe_peak_rss_kb={:?}\n",
        measurement_identity.machine_id,
        measurement_identity.platform,
        super::orchestrate::git_sha(),
        std::env::var("CRAT_BOC1_SUBSTRATE").unwrap_or_else(|_| "default-derived".to_owned()),
        snapshot.display(),
        query_budget,
        selected.len(),
        probe_wall_s,
        probe_peak_rss_kb,
    );
    fs::write(out.join("provenance.txt"), provenance).expect("write P2 provenance");

    println!(
        "S23P2 machine_id={} platform={} fields={} eligible={} queried={} hard_unsat={} own_assume_cores={} force_sat={} owning_accepted={} budget_not_queried={}",
        measurement_identity.machine_id,
        measurement_identity.platform,
        final_records.len(),
        eligible_len,
        selected.len(),
        hard_unsat.len(),
        own_assume_cores,
        force_sat,
        bucket_counts
            .get(TerminalBucket::OwningAccepted.label())
            .copied()
            .unwrap_or(0),
        bucket_counts
            .get(TerminalBucket::BudgetNotQueried.label())
            .copied()
            .unwrap_or(0),
    );
}

const P2_BASE_HARNESS_HEAD: &str = "c4e3a812c059164ec5759e54b001cfc2ac6caa32";
const P2_BASE_MANIFEST_SHA256: &str =
    "2bd754f81995bfc0d14b3887663678dfc2e8fdf0a3f38a09a1aee972d34fcbcc";
const P2_CANDIDATE_UNIVERSE_SHA256: &str =
    "56ca571ac8a6b99e42884b6495a6bab4a0ad46a4e2c1ac6a9bac30df5ff95527";
const P2_QUERY_BUDGET: usize = 200;
const P2_BROTLI_ELIGIBLE: usize = 112;
const P2_CHECKPOINT_BATCH_SIZES: [usize; 8] = [24, 24, 12, 12, 12, 12, 12, 4];
const P2_CHECKPOINT_BATCH_PLAN: &str = "24,24,12,12,12,12,12,4";
const P2_MAC_BROTLI_COMPLETED: usize = 24;
const P2_NON_BROTLI_IDENTITY_SHA256: &str =
    "45d335cbed633056ac80cb89da546e6572b7145ec4d134e3df3f5c07e564abe9";
const P2_ACCEPTED_AGGREGATE_MANIFEST_SHA256: &str =
    "3ef9b9406b5fc88f06a7c3ac31f00c15eea0b7730bfedb6fb4ce8b5cbef0c9ee";
const P2_COMPLETION_IDENTITY_SHA256: &str =
    "6fe2fd3e95580e6cd2eb2d841aa9560ae8d3b010c25f69d75336e10fe7848d74";
const P2_COMPLETION_CANDIDATES: usize = 61;
const P2_COMPLETION_ORDER: &str = "quadtree,urlparser,rgba,lil,lodepng";
const P2_COMPLETION_PROGRAMS: [(&str, usize); 5] = [
    ("quadtree", 10),
    ("urlparser", 11),
    ("rgba", 1),
    ("lil", 8),
    ("lodepng", 31),
];
const P2_FIRST_TIME_BROTLI_FORCE_SAT: [&str; 3] = [
    "src::enc::backward_references::H35::field4@d0",
    "src::enc::backward_references::H55::field4@d0",
    "src::enc::backward_references::H65::field4@d0",
];
const P2_NON_BROTLI_SELECTED: [(&str, usize); 13] = [
    ("avl", 2),
    ("binn", 4),
    ("bst", 2),
    ("buffer", 2),
    ("bzip2", 23),
    ("genann", 3),
    ("heman", 3),
    ("ht", 6),
    ("json.h", 15),
    ("libcsv", 1),
    ("libtree", 9),
    ("libzahl", 1),
    ("lil", 17),
];

#[derive(Clone, Debug, PartialEq, Eq)]
struct MeasurementIdentity {
    machine_id: String,
    platform: String,
}

impl MeasurementIdentity {
    fn parse(machine_id: &str, platform: &str) -> Result<Self, String> {
        let valid = |value: &str| {
            !value.is_empty()
                && value
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || b"._-".contains(&byte))
        };
        if !valid(machine_id) {
            return Err("machine identifier must use only [A-Za-z0-9._-]".to_owned());
        }
        if !valid(platform) {
            return Err("platform must use only [A-Za-z0-9._-]".to_owned());
        }
        Ok(Self {
            machine_id: machine_id.to_owned(),
            platform: platform.to_owned(),
        })
    }

    fn from_env() -> Self {
        let machine_id = std::env::var("CRAT_MEASUREMENT_MACHINE_ID")
            .expect("measurement requires CRAT_MEASUREMENT_MACHINE_ID");
        let platform = std::env::var("CRAT_MEASUREMENT_PLATFORM")
            .expect("measurement requires CRAT_MEASUREMENT_PLATFORM");
        Self::parse(&machine_id, &platform)
            .unwrap_or_else(|error| panic!("invalid measurement identity: {error}"))
    }
}

struct CheckpointContract {
    corpus_link: PathBuf,
    snapshot: PathBuf,
    base: PathBuf,
    batches: PathBuf,
    identity: MeasurementIdentity,
    base_manifest_sha256: String,
}

fn checkpoint_contract() -> CheckpointContract {
    let identity = MeasurementIdentity::from_env();
    let root = super::orchestrate::workspace_root()
        .canonicalize()
        .expect("canonical workspace root");
    assert!(
        !super::orchestrate::git_dirty(),
        "commit the green checkpoint harness before measurement"
    );
    assert!(
        matches!(
            std::env::var("CRAT_BOC1_SUBSTRATE").as_deref(),
            Err(_) | Ok("derived")
        ),
        "P2 checkpoints default to the derived substrate and refuse raw"
    );
    assert_eq!(std::env::var("CRAT_BO_REPAIR").as_deref(), Ok("mode_a"));
    assert_eq!(
        std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
        Ok("0")
    );
    assert_eq!(
        std::env::var("CRAT_BO_SAFE_MONO").as_deref(),
        Ok("per_site")
    );
    assert_eq!(std::env::var("CRAT_BO_FORK_ENGINE").as_deref(), Ok("fork"));
    assert!(
        matches!(
            std::env::var("CRAT_BO_MUT_FACTS").as_deref(),
            Err(_) | Ok("on")
        ),
        "P2 profile requires mutability facts on"
    );
    assert_eq!(
        std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
        Ok("uncapped"),
        "the dedicated Linux checkpoint lane runs without a harness RSS cap"
    );

    let corpus_link = root.join("benchmarks/rs-crown-derived");
    assert!(
        fs::symlink_metadata(&corpus_link)
            .expect("derived corpus metadata")
            .file_type()
            .is_symlink(),
        "derived corpus must retain its read-only symlink shape"
    );
    assert!(
        fs::symlink_metadata(root.join("deps_crate/target"))
            .expect("deps metadata")
            .file_type()
            .is_symlink(),
        "deps_crate provisioning must remain a read-only symlink"
    );
    let snapshot = PathBuf::from(
        std::env::var_os("CRAT_S23_SNAPSHOT").expect("P2 requires CRAT_S23_SNAPSHOT"),
    );
    assert_eq!(
        fs::read_dir(&snapshot)
            .expect("read snapshot")
            .filter_map(Result::ok)
            .filter(|entry| entry.file_type().is_ok_and(|kind| kind.is_file()))
            .count(),
        100,
        "P2 snapshot inventory drifted"
    );
    let base = PathBuf::from(
        std::env::var_os("CRAT_S23_BASE_ROOT").expect("P2 requires CRAT_S23_BASE_ROOT"),
    );
    let base_manifest = base.join("artifact-manifest.sha256");
    let base_manifest_sha256 = sha256_file(&base_manifest).expect("hash base manifest");
    verify_sha256_manifest(&base, &base_manifest)
        .unwrap_or_else(|error| panic!("preserved P2 artifacts failed re-verification: {error}"));
    assert_eq!(
        sha256_file(&base.join("candidate-universe.tsv")).expect("hash candidate universe"),
        P2_CANDIDATE_UNIVERSE_SHA256,
        "candidate universe identity drifted"
    );
    if base_manifest_sha256 != P2_BASE_MANIFEST_SHA256 {
        let provenance = parse_receipt(&base.join("bootstrap-provenance.txt"))
            .unwrap_or_else(|error| panic!("Linux bootstrap provenance: {error}"));
        assert_eq!(
            provenance.get("status").map(String::as_str),
            Some("discovery-only")
        );
        assert_eq!(
            provenance.get("machine_id").map(String::as_str),
            Some(identity.machine_id.as_str())
        );
        assert_eq!(
            provenance.get("platform").map(String::as_str),
            Some(identity.platform.as_str())
        );
        assert_eq!(
            provenance
                .get("candidate_universe_sha256")
                .map(String::as_str),
            Some(P2_CANDIDATE_UNIVERSE_SHA256)
        );
    }
    let batches = PathBuf::from(
        std::env::var_os("CRAT_S23_BATCH_ROOT").expect("P2 requires CRAT_S23_BATCH_ROOT"),
    );
    assert!(
        !batches.starts_with(root.join("target")),
        "checkpoint artifacts must remain in the private run root"
    );
    CheckpointContract {
        corpus_link,
        snapshot,
        base,
        batches,
        identity,
        base_manifest_sha256,
    }
}

fn checkpoint_candidates(base: &Path) -> Vec<CandidateSummary> {
    let mut candidates = parse_discovery(&base.join("candidate-universe.tsv"))
        .unwrap_or_else(|error| panic!("candidate universe: {error}"));
    candidates.sort_by(|left, right| {
        (&left.program, &left.field_key).cmp(&(&right.program, &right.field_key))
    });
    let identities = candidates
        .iter()
        .map(|candidate| (&candidate.program, &candidate.field_key))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        identities.len(),
        candidates.len(),
        "duplicate candidate identity"
    );
    candidates
}

fn selected_checkpoint_candidates(candidates: &[CandidateSummary]) -> BTreeSet<(String, String)> {
    let eligible = candidates
        .iter()
        .filter(|candidate| candidate.discovery == DiscoveryClass::Eligible)
        .map(|candidate| (candidate.program.clone(), candidate.field_key.clone()))
        .collect::<Vec<_>>();
    assert_eq!(eligible.len(), 261, "derived eligible population drifted");
    eligible.into_iter().take(P2_QUERY_BUDGET).collect()
}

fn validate_exact_candidate_partition(
    universe: &[(String, String)],
    completed: &[(String, String)],
    completion: &[(String, String)],
) -> Result<(), String> {
    let unique = |label: &str, rows: &[(String, String)]| {
        let set = rows.iter().cloned().collect::<BTreeSet<_>>();
        if set.len() != rows.len() {
            Err(format!("{label} candidate partition contains a duplicate"))
        } else {
            Ok(set)
        }
    };
    let universe = unique("universe", universe)?;
    let completed = unique("completed", completed)?;
    let completion = unique("completion", completion)?;
    let overlap = completed
        .intersection(&completion)
        .cloned()
        .collect::<Vec<_>>();
    if !overlap.is_empty() {
        return Err(format!("candidate partition overlap: {overlap:?}"));
    }
    let combined = completed
        .union(&completion)
        .cloned()
        .collect::<BTreeSet<_>>();
    let extra = combined.difference(&universe).cloned().collect::<Vec<_>>();
    if !extra.is_empty() {
        return Err(format!(
            "candidate partition contains extra identities: {extra:?}"
        ));
    }
    let missing = universe.difference(&combined).cloned().collect::<Vec<_>>();
    if !missing.is_empty() {
        return Err(format!(
            "candidate partition is missing identities: {missing:?}"
        ));
    }
    Ok(())
}

fn completion_checkpoint_programs(
    candidates: &[CandidateSummary],
) -> Result<Vec<(String, Vec<String>)>, String> {
    let eligible = candidates
        .iter()
        .filter(|candidate| candidate.discovery == DiscoveryClass::Eligible)
        .map(|candidate| (candidate.program.clone(), candidate.field_key.clone()))
        .collect::<Vec<_>>();
    if eligible.len() != P2_QUERY_BUDGET + P2_COMPLETION_CANDIDATES {
        return Err(format!(
            "completion universe drifted: expected {}, got {}",
            P2_QUERY_BUDGET + P2_COMPLETION_CANDIDATES,
            eligible.len()
        ));
    }
    let completed = selected_checkpoint_candidates(candidates)
        .into_iter()
        .collect::<Vec<_>>();
    let completed_set = completed.iter().cloned().collect::<BTreeSet<_>>();
    let completion = eligible
        .iter()
        .filter(|identity| !completed_set.contains(*identity))
        .cloned()
        .collect::<Vec<_>>();
    validate_exact_candidate_partition(&eligible, &completed, &completion)?;
    if completion.len() != P2_COMPLETION_CANDIDATES {
        return Err(format!(
            "completion population drifted: expected {P2_COMPLETION_CANDIDATES}, got {}",
            completion.len()
        ));
    }

    let candidate_slots = candidates
        .iter()
        .map(|candidate| {
            (
                (candidate.program.clone(), candidate.field_key.clone()),
                candidate.field_slot,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut identity_list = String::new();
    for (program, key) in &completion {
        let slot = candidate_slots
            .get(&(program.clone(), key.clone()))
            .ok_or_else(|| format!("completion identity lacks slot: {program} {key}"))?;
        identity_list.push_str(&format!("{program}\t{key}\t{slot}\n"));
    }
    let digest = sha256_text(&identity_list)?;
    if digest != P2_COMPLETION_IDENTITY_SHA256 {
        return Err(format!(
            "completion identity digest drifted: expected {P2_COMPLETION_IDENTITY_SHA256}, got {digest}"
        ));
    }

    let grouped = completion.into_iter().fold(
        BTreeMap::<String, Vec<String>>::new(),
        |mut programs, (program, key)| {
            programs.entry(program).or_default().push(key);
            programs
        },
    );
    let actual = grouped
        .iter()
        .map(|(program, keys)| (program.as_str(), keys.len()))
        .collect::<BTreeMap<_, _>>();
    let expected = P2_COMPLETION_PROGRAMS
        .iter()
        .copied()
        .collect::<BTreeMap<_, _>>();
    if actual != expected {
        return Err(format!(
            "completion program partition drifted: expected {expected:?}, got {actual:?}"
        ));
    }
    P2_COMPLETION_PROGRAMS
        .iter()
        .map(|(program, _)| {
            grouped
                .get(*program)
                .cloned()
                .map(|keys| ((*program).to_owned(), keys))
                .ok_or_else(|| format!("completion program {program} is missing"))
        })
        .collect()
}

fn non_brotli_checkpoint_programs(
    candidates: &[CandidateSummary],
) -> Result<BTreeMap<String, Vec<String>>, String> {
    let mut programs = BTreeMap::<String, Vec<String>>::new();
    for (program, key) in selected_checkpoint_candidates(candidates) {
        if program != "brotli" {
            programs.entry(program).or_default().push(key);
        }
    }
    let expected = P2_NON_BROTLI_SELECTED
        .iter()
        .map(|(program, count)| ((*program).to_owned(), *count))
        .collect::<BTreeMap<_, _>>();
    let actual = programs
        .iter()
        .map(|(program, keys)| (program.clone(), keys.len()))
        .collect::<BTreeMap<_, _>>();
    if actual != expected {
        return Err(format!(
            "non-brotli selected partition drifted: expected {expected:?}, got {actual:?}"
        ));
    }
    let rows = programs.values().map(Vec::len).sum::<usize>();
    if rows != 88 {
        return Err(format!("non-brotli selected population drifted: {rows}"));
    }
    let candidate_slots = candidates
        .iter()
        .map(|candidate| {
            (
                (candidate.program.clone(), candidate.field_key.clone()),
                candidate.field_slot,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut identity_list = String::new();
    for (program, keys) in &programs {
        for key in keys {
            let slot = candidate_slots
                .get(&(program.clone(), key.clone()))
                .ok_or_else(|| format!("selected identity lacks slot: {program} {key}"))?;
            identity_list.push_str(&format!("{program}\t{key}\t{slot}\n"));
        }
    }
    let identity_sha256 = sha256_text(&identity_list)?;
    if identity_sha256 != P2_NON_BROTLI_IDENTITY_SHA256 {
        return Err(format!(
            "non-brotli selected identity digest drifted: expected {P2_NON_BROTLI_IDENTITY_SHA256}, got {identity_sha256}"
        ));
    }
    Ok(programs)
}

fn validate_recovery_rows(
    program: &str,
    expected_keys: &[String],
    rows: &[ProbeRecord],
    candidate_slots: &BTreeMap<(String, String), usize>,
) -> Result<(), String> {
    if rows.len() != expected_keys.len() {
        return Err(format!(
            "identity mismatch for {program}: expected {} rows, got {}",
            expected_keys.len(),
            rows.len()
        ));
    }
    for (row, expected_key) in rows.iter().zip(expected_keys) {
        if &row.field_key != expected_key {
            return Err(format!(
                "identity mismatch for {program}: expected {expected_key}, got {}",
                row.field_key
            ));
        }
        let expected_slot = candidate_slots
            .get(&(program.to_owned(), expected_key.clone()))
            .ok_or_else(|| {
                format!("identity mismatch for {program}: {expected_key} lacks a candidate slot")
            })?;
        if row.field_slot != *expected_slot {
            return Err(format!(
                "identity mismatch for {program}::{expected_key}: expected field_slot={expected_slot}, got {}",
                row.field_slot
            ));
        }
        if row.force_result != ForceResult::Unsat {
            return Err(format!(
                "platform deviation at {program}::{expected_key}: mac verdict=unsat, Linux verdict={:?}; named suspect=c_char-signedness",
                row.force_result
            ));
        }
        for required in ["own-assume", "link-own"] {
            if !row.core_families.iter().any(|family| family == required) {
                return Err(format!(
                    "platform deviation at {program}::{expected_key}: mac core contains {required}, Linux core families={:?}; named suspect=c_char-signedness",
                    row.core_families
                ));
            }
        }
    }
    Ok(())
}

fn validate_completed_recovery_shard(
    program: &str,
    expected_keys: &[String],
    receipt: &BTreeMap<String, String>,
    rows: &[ProbeRecord],
    identity: &MeasurementIdentity,
    candidate_slots: &BTreeMap<(String, String), usize>,
) -> Result<(), String> {
    let require = |field: &str, expected: &str| match receipt.get(field) {
        Some(actual) if actual == expected => Ok(()),
        actual => Err(format!(
            "completed recovery shard {program} requires {field}={expected:?}, got {actual:?}"
        )),
    };
    require("machine_id", &identity.machine_id)?;
    require("platform", &identity.platform)?;
    require("program", program)?;
    require("status", "ok")?;
    require("worker_status", "ok")?;
    require("data", "true")?;
    require("checkpoint_data", "false")?;
    require("memory_limit", "uncapped")?;
    require("wall_bound_kind", "liveness")?;
    require("wall_cap_s", "14400")?;
    require("last_phase", "complete")?;
    require("candidate_universe_sha256", P2_CANDIDATE_UNIVERSE_SHA256)?;
    require(
        "non_brotli_identity_list_sha256",
        P2_NON_BROTLI_IDENTITY_SHA256,
    )?;
    require("mac_comparison_kind", "universal-record-per-exact-key")?;
    require("mac_expected_verdict", "unsat")?;
    require("mac_expected_core_families", "own-assume|link-own")?;
    require("mac_comparison", "match")?;
    require("validation_error", "none")?;
    for field in ["planned_targets", "queried", "checkpoint_rows"] {
        let actual = receipt
            .get(field)
            .ok_or_else(|| format!("completed recovery shard {program} lacks {field}"))?
            .parse::<usize>()
            .map_err(|error| {
                format!("completed recovery shard {program} has invalid {field}: {error}")
            })?;
        if actual != expected_keys.len() {
            return Err(format!(
                "completed recovery shard {program} requires {field}={}, got {actual}",
                expected_keys.len()
            ));
        }
    }
    for (field, expected) in [
        ("hard_unsat", expected_keys.len()),
        ("force_sat", 0),
        ("solver_unknown", 0),
    ] {
        let actual = receipt
            .get(field)
            .ok_or_else(|| format!("completed recovery shard {program} lacks {field}"))?
            .parse::<usize>()
            .map_err(|error| {
                format!("completed recovery shard {program} has invalid {field}: {error}")
            })?;
        if actual != expected {
            return Err(format!(
                "completed recovery shard {program} requires {field}={expected}, got {actual}"
            ));
        }
    }
    validate_recovery_rows(program, expected_keys, rows, candidate_slots)
}

fn validate_completion_rows(
    program: &str,
    expected_keys: &[String],
    rows: &[ProbeRecord],
    candidate_slots: &BTreeMap<(String, String), usize>,
) -> Result<(), String> {
    if rows.len() != expected_keys.len() {
        return Err(format!(
            "identity mismatch for {program}: expected {} rows, got {}",
            expected_keys.len(),
            rows.len()
        ));
    }
    for (row, expected_key) in rows.iter().zip(expected_keys) {
        if &row.field_key != expected_key {
            return Err(format!(
                "identity mismatch for {program}: expected {expected_key}, got {}",
                row.field_key
            ));
        }
        let expected_slot = candidate_slots
            .get(&(program.to_owned(), expected_key.clone()))
            .ok_or_else(|| {
                format!("identity mismatch for {program}: {expected_key} lacks a candidate slot")
            })?;
        if row.field_slot != *expected_slot {
            return Err(format!(
                "identity mismatch for {program}::{expected_key}: expected field_slot={expected_slot}, got {}",
                row.field_slot
            ));
        }
        match row.force_result {
            ForceResult::Sat | ForceResult::Unsat => {}
            ForceResult::Unknown => {
                return Err(format!("solver Unknown at {program}::{expected_key}"));
            }
            ForceResult::NotQueried => {
                return Err(format!(
                    "identity mismatch for {program}::{expected_key}: completed row is not-queried"
                ));
            }
        }
    }
    Ok(())
}

fn completion_row_failure_candidate(
    program: &str,
    expected_keys: &[String],
    rows: &[ProbeRecord],
    candidate_slots: &BTreeMap<(String, String), usize>,
) -> String {
    if rows.len() < expected_keys.len() {
        return expected_keys[rows.len()].clone();
    }
    if rows.len() > expected_keys.len() {
        return rows[expected_keys.len()].field_key.clone();
    }
    for (row, expected_key) in rows.iter().zip(expected_keys) {
        let identity = (program.to_owned(), expected_key.clone());
        if &row.field_key != expected_key
            || candidate_slots.get(&identity).copied() != Some(row.field_slot)
            || matches!(
                row.force_result,
                ForceResult::Unknown | ForceResult::NotQueried
            )
        {
            return if row.field_key.is_empty() {
                expected_key.clone()
            } else {
                row.field_key.clone()
            };
        }
    }
    "<completion-row>".to_owned()
}

fn validate_completed_completion_shard(
    program: &str,
    expected_keys: &[String],
    receipt: &BTreeMap<String, String>,
    rows: &[ProbeRecord],
    identity: &MeasurementIdentity,
    candidate_slots: &BTreeMap<(String, String), usize>,
) -> Result<(), String> {
    let require = |field: &str, expected: &str| match receipt.get(field) {
        Some(actual) if actual == expected => Ok(()),
        actual => Err(format!(
            "completed completion shard {program} requires {field}={expected:?}, got {actual:?}"
        )),
    };
    require("machine_id", &identity.machine_id)?;
    require("platform", &identity.platform)?;
    require("program", program)?;
    require("status", "ok")?;
    require("worker_status", "ok")?;
    require("data", "true")?;
    require("checkpoint_data", "false")?;
    require("memory_limit", "uncapped")?;
    require("wall_bound_kind", "liveness")?;
    require("wall_cap_s", "14400")?;
    require("last_phase", "complete")?;
    require("candidate_universe_sha256", P2_CANDIDATE_UNIVERSE_SHA256)?;
    require(
        "completion_identity_list_sha256",
        P2_COMPLETION_IDENTITY_SHA256,
    )?;
    require(
        "accepted_aggregate_manifest_sha256",
        P2_ACCEPTED_AGGREGATE_MANIFEST_SHA256,
    )?;
    if let Some(index) = P2_COMPLETION_PROGRAMS
        .iter()
        .position(|(candidate_program, _)| *candidate_program == program)
    {
        require("completion_order", P2_COMPLETION_ORDER)?;
        require(
            "completed_predecessors",
            &P2_COMPLETION_PROGRAMS[..index]
                .iter()
                .map(|(candidate_program, _)| *candidate_program)
                .collect::<Vec<_>>()
                .join(","),
        )?;
    }
    require("validation_error", "none")?;
    for field in ["planned_targets", "queried", "checkpoint_rows"] {
        let actual = receipt
            .get(field)
            .ok_or_else(|| format!("completed completion shard {program} lacks {field}"))?
            .parse::<usize>()
            .map_err(|error| {
                format!("completed completion shard {program} has invalid {field}: {error}")
            })?;
        if actual != expected_keys.len() {
            return Err(format!(
                "completed completion shard {program} requires {field}={}, got {actual}",
                expected_keys.len()
            ));
        }
    }
    validate_completion_rows(program, expected_keys, rows, candidate_slots)?;
    let hard_unsat = rows
        .iter()
        .filter(|row| row.force_result == ForceResult::Unsat)
        .count();
    let force_sat = rows
        .iter()
        .filter(|row| row.force_result == ForceResult::Sat)
        .count();
    for (field, expected) in [
        ("hard_unsat", hard_unsat),
        ("force_sat", force_sat),
        ("solver_unknown", 0),
    ] {
        let actual = receipt
            .get(field)
            .ok_or_else(|| format!("completed completion shard {program} lacks {field}"))?
            .parse::<usize>()
            .map_err(|error| {
                format!("completed completion shard {program} has invalid {field}: {error}")
            })?;
        if actual != expected {
            return Err(format!(
                "completed completion shard {program} requires {field}={expected}, got {actual}"
            ));
        }
    }
    Ok(())
}

fn validate_brotli_mac_overlap(
    brotli_keys: &[String],
    force_sat_keys: &[String],
) -> Result<(), String> {
    if brotli_keys.len() < P2_MAC_BROTLI_COMPLETED {
        return Err(format!(
            "brotli identity mismatch: expected at least {P2_MAC_BROTLI_COMPLETED} keys, got {}",
            brotli_keys.len()
        ));
    }
    for key in force_sat_keys {
        if brotli_keys[..P2_MAC_BROTLI_COMPLETED].contains(key) {
            return Err(format!(
                "platform deviation at brotli::{key}: Linux force-SAT overlaps the mac-measured hard-UNSAT prefix"
            ));
        }
    }
    Ok(())
}

fn insert_probe_artifact(
    program: &str,
    path: &Path,
    candidates: &BTreeMap<(String, String), usize>,
    selected: &BTreeSet<(String, String)>,
    probes: &mut BTreeMap<(String, String), ProbeRecord>,
) -> Result<usize, String> {
    let rows = parse_probe_for_program(path, Some(program))?;
    for row in &rows {
        let identity = (program.to_owned(), row.field_key.clone());
        if !selected.contains(&identity) {
            return Err(format!(
                "probe {} emitted unselected candidate {} {}",
                path.display(),
                program,
                row.field_key
            ));
        }
        if candidates.get(&identity).copied() != Some(row.field_slot) {
            return Err(format!(
                "probe {} field-slot drift for {} {}",
                path.display(),
                program,
                row.field_key
            ));
        }
        if row.force_result == ForceResult::NotQueried {
            return Err(format!(
                "queried probe row is not-queried: {program} {}",
                row.field_key
            ));
        }
        if probes.insert(identity, row.clone()).is_some() {
            return Err(format!(
                "duplicate probe candidate: {program} {}",
                row.field_key
            ));
        }
    }
    Ok(rows.len())
}

/// Run exactly one brotli checkpoint. An already-manifested batch is verified
/// and skipped; any unmanifested batch directory is a STOP rather than an
/// implicit overwrite.
#[test]
#[ignore = "P2 brotli checkpoint; run one dedicated-host batch explicitly"]
fn s23_p2_brotli_checkpoint() {
    let contract = checkpoint_contract();
    let candidates = checkpoint_candidates(&contract.base);
    let brotli = candidates
        .iter()
        .filter(|candidate| {
            candidate.program == "brotli" && candidate.discovery == DiscoveryClass::Eligible
        })
        .map(|candidate| candidate.field_key.clone())
        .collect::<Vec<_>>();
    assert_eq!(
        brotli.len(),
        P2_BROTLI_ELIGIBLE,
        "brotli eligible population drifted"
    );
    let selected = selected_checkpoint_candidates(&candidates);
    assert!(
        brotli
            .iter()
            .all(|key| selected.contains(&("brotli".to_owned(), key.clone()))),
        "checkpoint candidates must remain inside the registered 200-query budget"
    );
    assert!(
        std::env::var_os("CRAT_S23_BATCH_SIZE").is_none(),
        "CRAT_S23_BATCH_SIZE is retired; the checkpoint uses its registered heterogeneous plan"
    );
    let ranges = checkpoint_batch_ranges(brotli.len())
        .unwrap_or_else(|error| panic!("checkpoint plan: {error}"));
    let batch_index = std::env::var("CRAT_S23_BATCH_INDEX")
        .expect("checkpoint requires CRAT_S23_BATCH_INDEX")
        .parse::<usize>()
        .expect("CRAT_S23_BATCH_INDEX must be an integer");
    let range = ranges
        .get(batch_index)
        .unwrap_or_else(|| panic!("batch index {batch_index} outside 0..{}", ranges.len()));
    let keys = &brotli[range.clone()];
    let batch_dir = contract.batches.join(format!("batch-{batch_index:03}"));
    let manifest = batch_dir.join("artifact-manifest.sha256");
    if manifest.is_file() {
        verify_sha256_manifest(&batch_dir, &manifest)
            .unwrap_or_else(|error| panic!("completed batch failed re-verification: {error}"));
        let receipt = parse_receipt(&batch_dir.join("receipt.txt"))
            .unwrap_or_else(|error| panic!("completed batch receipt: {error}"));
        assert_eq!(
            receipt.get("status").map(String::as_str),
            Some("ok"),
            "P2 STOP: preserved batch is a failed attempt, not a resumable completion"
        );
        assert_eq!(
            receipt.get("machine_id").map(String::as_str),
            Some(contract.identity.machine_id.as_str()),
            "completed batch belongs to another machine"
        );
        assert_eq!(
            receipt.get("platform").map(String::as_str),
            Some(contract.identity.platform.as_str()),
            "completed batch belongs to another platform"
        );
        assert_eq!(
            read_target_keys(&batch_dir.join("targets.txt"))
                .unwrap_or_else(|error| panic!("completed batch targets: {error}")),
            keys,
            "completed batch target slice drifted"
        );
        let rows = parse_probe(&batch_dir.join("probes.tsv"))
            .unwrap_or_else(|error| panic!("completed batch probes: {error}"));
        assert!(
            rows.iter()
                .zip(keys)
                .all(|(row, key)| &row.field_key == key)
                && rows.len() == keys.len(),
            "completed batch probe order/identity drifted"
        );
        assert!(
            rows.iter()
                .all(|row| row.force_result != ForceResult::Unknown),
            "P2 STOP: completed checkpoint contains solver Unknown"
        );
        println!(
            "S23P2BATCH machine_id={} platform={} batch={} status=verified-skip candidates={}",
            contract.identity.machine_id,
            contract.identity.platform,
            batch_index,
            range.end - range.start
        );
        return;
    }
    let timeout_override = std::env::var("CRAT_S23_BATCH_TIMEOUT_SECS").ok();
    let timeout_s = checkpoint_batch_timeout_s(timeout_override.as_deref())
        .unwrap_or_else(|error| panic!("{error}"));
    assert!(
        !batch_dir.exists(),
        "P2 STOP: unmanifested partial batch exists at {}; preserve it for inspection",
        batch_dir.display()
    );
    fs::create_dir_all(&batch_dir).expect("create batch directory");

    let targets = batch_dir.join("targets.txt");
    let probe = batch_dir.join("probes.tsv");
    let checkpoint = batch_dir.join("partial-probes.tsv");
    let checkpoint_temp = probe_checkpoint_temp_path(&checkpoint);
    let stdout = batch_dir.join("stdout.txt");
    let stderr = batch_dir.join("stderr.txt");
    let receipt = batch_dir.join("receipt.txt");
    write_targets(&targets, keys).unwrap_or_else(|error| panic!("{error}"));
    let corpus_program = super::CORPUS
        .iter()
        .find(|program| program.name == "brotli")
        .expect("brotli corpus entry");
    let input = contract
        .corpus_link
        .join(corpus_program.name)
        .join(corpus_program.lib_root);
    let outcome = super::orchestrate::run_child_labeled(
        "brotli",
        &input,
        "s23-probe",
        &format!("s23-brotli-batch-{batch_index:03}"),
        Duration::from_secs(timeout_s as u64),
        &[
            ("CRAT_S23_TARGET_KEYS", targets.display().to_string()),
            ("CRAT_S23_PROBE_ARTIFACT", probe.display().to_string()),
            (
                "CRAT_S23_CHECKPOINT_ARTIFACT",
                checkpoint.display().to_string(),
            ),
        ],
    );
    fs::write(&stdout, &outcome.stdout).expect("write batch stdout");
    fs::write(&stderr, &outcome.stderr).expect("write batch stderr");
    let row_value = |key: &str| {
        outcome
            .row
            .as_ref()
            .and_then(|row| row.get(key))
            .unwrap_or("-")
    };
    let progress = outcome
        .stderr
        .lines()
        .filter_map(parse_checkpoint_phase)
        .next_back()
        .unwrap_or_else(|| CheckpointProgress {
            phase: "worker-not-entered".to_owned(),
            candidate: None,
            completed: 0,
            elapsed_s: format!("{:.3}", outcome.wall_s),
        });
    let checkpoint_rows = if checkpoint.is_file() {
        parse_probe(&checkpoint).unwrap_or_else(|error| panic!("partial checkpoint: {error}"))
    } else {
        Vec::new()
    };
    assert!(
        checkpoint_rows.len() == progress.completed
            || (progress.phase == "force-own-start"
                && checkpoint_rows.len() == progress.completed + 1),
        "partial checkpoint row count {} disagrees with last progress marker {:?}",
        checkpoint_rows.len(),
        progress
    );
    let data = checkpoint_data_value(&outcome.status);
    let amortized = outcome.wall_s / keys.len() as f64;
    fs::write(
        &receipt,
        format!(
            "machine_id={}\nplatform={}\nmachine_protocol=dedicated-host\nmemory_limit=uncapped\nwall_bound_kind=liveness\nbatch={batch_index}\nprogram=brotli\nstatus={}\ndata={}\ncheckpoint_data=false\nanalysis_head={}\nbase_harness_head={}\nbase_manifest_sha256={}\nmac_base_manifest_sha256={}\nsnapshot={}\nbatch_size={}\nbatch_plan={}\nwall_cap_s={}\nrange_start={}\nrange_end={}\nplanned_targets={}\nqueried={}\nfirst_key={}\nlast_key={}\nlast_phase={}\nlast_candidate={}\nlast_phase_t_s={}\ncheckpoint_rows={}\ncheckpoint_last_key={}\nwall_s={:.3}\nwall_s_per_candidate={:.6}\npeak_rss_kb={}\nworker_t_total_s={}\nhard_unsat={}\nforce_sat={}\nsolver_unknown={}\naccepted_owning={}\n",
            contract.identity.machine_id,
            contract.identity.platform,
            outcome.status,
            data,
            super::orchestrate::git_sha(),
            P2_BASE_HARNESS_HEAD,
            contract.base_manifest_sha256,
            P2_BASE_MANIFEST_SHA256,
            contract.snapshot.display(),
            keys.len(),
            P2_CHECKPOINT_BATCH_PLAN,
            timeout_s,
            range.start,
            range.end,
            keys.len(),
            checkpoint_rows.len(),
            keys.first().expect("nonempty batch"),
            keys.last().expect("nonempty batch"),
            progress.phase,
            progress.candidate.as_deref().unwrap_or("none"),
            progress.elapsed_s,
            checkpoint_rows.len(),
            checkpoint_rows
                .last()
                .map(|row| row.field_key.as_str())
                .unwrap_or("none"),
            outcome.wall_s,
            amortized,
            outcome.peak_rss_kb,
            row_value("t_total_s"),
            row_value("hard_unsat"),
            row_value("force_sat"),
            row_value("solver_unknown"),
            row_value("owning_accepted"),
        ),
    )
    .expect("write batch receipt");
    let seal_batch = || {
        let mut artifacts = vec![
            targets.clone(),
            stdout.clone(),
            stderr.clone(),
            receipt.clone(),
        ];
        if probe.is_file() {
            artifacts.push(probe.clone());
        }
        if checkpoint.is_file() {
            artifacts.push(checkpoint.clone());
        }
        if checkpoint_temp.is_file() {
            artifacts.push(checkpoint_temp.clone());
        }
        write_sha256_manifest(&batch_dir, &artifacts, &manifest)
            .unwrap_or_else(|error| panic!("write batch manifest: {error}"));
        verify_sha256_manifest(&batch_dir, &manifest)
            .unwrap_or_else(|error| panic!("verify batch manifest: {error}"));
    };
    if outcome.status != "ok" {
        seal_batch();
        panic!(
            "P2 checkpoint STOP: batch={} status={} peak_rss_kb={} wall_s={:.3} note={}",
            batch_index, outcome.status, outcome.peak_rss_kb, outcome.wall_s, outcome.note
        );
    }
    let rows = parse_probe(&probe).unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(rows.len(), keys.len(), "batch row count drift");
    assert!(
        rows.iter()
            .zip(keys)
            .all(|(row, key)| &row.field_key == key),
        "batch probe order/identity drifted"
    );
    assert!(
        rows.iter()
            .all(|row| row.force_result != ForceResult::Unknown),
        "P2 STOP: checkpoint returned solver Unknown"
    );
    seal_batch();
    println!(
        "S23P2BATCH machine_id={} platform={} memory_limit=uncapped batch={} status=ok candidates={} wall_s={:.3} wall_s_per_candidate={:.6} peak_rss_kb={}",
        contract.identity.machine_id,
        contract.identity.platform,
        batch_index,
        keys.len(),
        outcome.wall_s,
        amortized,
        outcome.peak_rss_kb
    );
}

/// Recover one selected non-brotli program as an immutable, manifested shard.
/// The macOS row artifacts were not transfer-durable, so each Linux row is
/// compared with the durable universal record: hard-UNSAT with both required
/// core families present.
#[test]
#[ignore = "P2 non-brotli recovery; run one dedicated-host shard explicitly"]
fn s23_p2_non_brotli_recovery_shard() {
    let contract = checkpoint_contract();
    let candidates = checkpoint_candidates(&contract.base);
    let candidate_slots = candidates
        .iter()
        .map(|candidate| {
            (
                (candidate.program.clone(), candidate.field_key.clone()),
                candidate.field_slot,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let programs = non_brotli_checkpoint_programs(&candidates)
        .unwrap_or_else(|error| panic!("P2 recovery partition: {error}"));
    let program = std::env::var("CRAT_S23_RECOVERY_PROGRAM")
        .expect("recovery requires CRAT_S23_RECOVERY_PROGRAM");
    let keys = programs.get(&program).unwrap_or_else(|| {
        panic!(
            "recovery program {program:?} is outside the registered set {:?}",
            programs.keys().collect::<Vec<_>>()
        )
    });
    let timeout_override = std::env::var("CRAT_S23_BATCH_TIMEOUT_SECS").ok();
    let timeout_s = checkpoint_batch_timeout_s(timeout_override.as_deref())
        .unwrap_or_else(|error| panic!("recovery liveness bound: {error}"));
    let shard_dir = contract.batches.join("non-brotli-shards").join(&program);
    let manifest = shard_dir.join("artifact-manifest.sha256");
    let targets = shard_dir.join("targets.txt");
    let probe = shard_dir.join("probes.tsv");
    let checkpoint = shard_dir.join("partial-probes.tsv");
    let checkpoint_temp = probe_checkpoint_temp_path(&checkpoint);
    let stdout = shard_dir.join("stdout.txt");
    let stderr = shard_dir.join("stderr.txt");
    let receipt_path = shard_dir.join("receipt.txt");

    if manifest.is_file() {
        verify_sha256_manifest(&shard_dir, &manifest)
            .unwrap_or_else(|error| panic!("completed recovery shard manifest: {error}"));
        let receipt = parse_receipt(&receipt_path)
            .unwrap_or_else(|error| panic!("completed recovery shard receipt: {error}"));
        let rows = parse_probe_for_program(&probe, Some(&program))
            .unwrap_or_else(|error| panic!("completed recovery shard probes: {error}"));
        validate_completed_recovery_shard(
            &program,
            keys,
            &receipt,
            &rows,
            &contract.identity,
            &candidate_slots,
        )
        .unwrap_or_else(|error| panic!("P2 recovery STOP: {error}"));
        assert_eq!(
            read_target_keys(&targets)
                .unwrap_or_else(|error| panic!("completed recovery targets: {error}")),
            *keys,
            "completed recovery target identity drifted"
        );
        assert_eq!(
            parse_probe_for_program(&checkpoint, Some(&program))
                .unwrap_or_else(|error| panic!("completed recovery checkpoint: {error}")),
            rows,
            "completed recovery checkpoint/final drifted"
        );
        assert!(
            !checkpoint_temp.exists(),
            "completed recovery shard retained a temporary checkpoint"
        );
        println!(
            "S23P2RECOVERY machine_id={} platform={} program={} status=verified-skip candidates={}",
            contract.identity.machine_id,
            contract.identity.platform,
            program,
            keys.len()
        );
        return;
    }
    assert!(
        !shard_dir.exists(),
        "P2 STOP: unmanifested recovery shard exists at {}; preserve it for inspection",
        shard_dir.display()
    );
    fs::create_dir_all(&shard_dir).expect("create recovery shard directory");
    write_targets(&targets, keys).unwrap_or_else(|error| panic!("recovery targets: {error}"));

    let corpus_program = super::CORPUS
        .iter()
        .find(|entry| entry.name == program)
        .unwrap_or_else(|| panic!("recovery program {program} lacks a corpus entry"));
    let input = contract
        .corpus_link
        .join(corpus_program.name)
        .join(corpus_program.lib_root);
    let outcome = super::orchestrate::run_child_labeled(
        &program,
        &input,
        "s23-probe",
        &format!("s23-p2-recovery-{program}"),
        Duration::from_secs(timeout_s as u64),
        &[
            ("CRAT_S23_TARGET_KEYS", targets.display().to_string()),
            ("CRAT_S23_PROBE_ARTIFACT", probe.display().to_string()),
            (
                "CRAT_S23_CHECKPOINT_ARTIFACT",
                checkpoint.display().to_string(),
            ),
        ],
    );
    fs::write(&stdout, &outcome.stdout).expect("write recovery stdout");
    fs::write(&stderr, &outcome.stderr).expect("write recovery stderr");
    let progress = outcome
        .stderr
        .lines()
        .filter_map(parse_checkpoint_phase)
        .next_back()
        .unwrap_or_else(|| CheckpointProgress {
            phase: "worker-not-entered".to_owned(),
            candidate: None,
            completed: 0,
            elapsed_s: format!("{:.3}", outcome.wall_s),
        });
    let (checkpoint_rows, mut validation_error) = if checkpoint.is_file() {
        match parse_probe_for_program(&checkpoint, Some(&program)) {
            Ok(rows) => (rows, None),
            Err(error) => (
                Vec::new(),
                Some(format!(
                    "identity mismatch for {program}: invalid partial checkpoint: {error}"
                )),
            ),
        }
    } else {
        (Vec::new(), None)
    };
    if validation_error.is_none()
        && !(checkpoint_rows.len() == progress.completed
            || (progress.phase == "force-own-start"
                && checkpoint_rows.len() == progress.completed + 1))
    {
        validation_error = Some(format!(
            "identity mismatch for {program}: partial checkpoint rows={} disagree with phase={} completed={}",
            checkpoint_rows.len(),
            progress.phase,
            progress.completed
        ));
    }
    if validation_error.is_none() {
        if checkpoint_rows.len() > keys.len() {
            validation_error = Some(format!(
                "identity mismatch for {program}: partial checkpoint has {} rows for {} targets",
                checkpoint_rows.len(),
                keys.len()
            ));
        } else if let Err(error) = validate_recovery_rows(
            &program,
            &keys[..checkpoint_rows.len()],
            &checkpoint_rows,
            &candidate_slots,
        ) {
            validation_error = Some(error);
        }
    }
    let mut final_rows = Vec::new();
    if outcome.status == "ok" {
        match parse_probe_for_program(&probe, Some(&program)) {
            Ok(rows) => {
                if validation_error.is_none() {
                    if let Err(error) =
                        validate_recovery_rows(&program, keys, &rows, &candidate_slots)
                    {
                        validation_error = Some(error);
                    } else if rows != checkpoint_rows {
                        validation_error = Some(format!(
                            "identity mismatch for {program}: completed checkpoint/final tables differ"
                        ));
                    } else if checkpoint_temp.exists() {
                        validation_error = Some(format!(
                            "identity mismatch for {program}: temporary checkpoint survived publish"
                        ));
                    }
                }
                final_rows = rows;
            }
            Err(error) => {
                validation_error = Some(format!(
                    "identity mismatch for {program}: invalid final probe artifact: {error}"
                ));
            }
        }
    }
    let effective_status = if validation_error
        .as_deref()
        .is_some_and(|error| error.starts_with("platform deviation"))
    {
        "platform-deviation".to_owned()
    } else if validation_error.is_some() {
        "identity-mismatch".to_owned()
    } else if outcome.status != "ok" {
        outcome.status.clone()
    } else {
        "ok".to_owned()
    };
    let observed_rows = if final_rows.is_empty() {
        &checkpoint_rows
    } else {
        &final_rows
    };
    let queried = observed_rows.len();
    let hard_unsat = observed_rows
        .iter()
        .filter(|row| row.force_result == ForceResult::Unsat)
        .count();
    let force_sat = observed_rows
        .iter()
        .filter(|row| row.force_result == ForceResult::Sat)
        .count();
    let solver_unknown = observed_rows
        .iter()
        .filter(|row| row.force_result == ForceResult::Unknown)
        .count();
    let accepted_owning = observed_rows
        .iter()
        .filter(|row| row.accepted_kind == SlotKind::Owning)
        .count();
    let mac_comparison = match effective_status.as_str() {
        "ok" => "match",
        "platform-deviation" => "deviation",
        _ => "not-completed",
    };
    fs::write(
        &receipt_path,
        format!(
            "machine_id={}\nplatform={}\nmachine_protocol=dedicated-host\nmemory_limit=uncapped\nwall_bound_kind=liveness\nprogram={}\nstatus={}\nworker_status={}\ndata={}\ncheckpoint_data=false\nanalysis_head={}\nbase_harness_head={}\nbase_manifest_sha256={}\nmac_base_manifest_sha256={}\nmac_record_commit=bbaaaf0ac4914398e7024dd137accbdc3932ecf5\ncandidate_universe_sha256={}\nnon_brotli_identity_list_sha256={}\nmac_comparison_kind=universal-record-per-exact-key\nmac_expected_verdict=unsat\nmac_expected_core_families=own-assume|link-own\nmac_comparison={}\nsnapshot={}\nwall_cap_s={}\nplanned_targets={}\nqueried={}\nfirst_key={}\nlast_key={}\nlast_phase={}\nlast_candidate={}\nlast_phase_t_s={}\ncheckpoint_rows={}\ncheckpoint_last_key={}\nwall_s={:.3}\nwall_s_per_candidate={:.6}\npeak_rss_kb={}\nhard_unsat={}\nforce_sat={}\nsolver_unknown={}\naccepted_owning={}\nvalidation_error={}\n",
            contract.identity.machine_id,
            contract.identity.platform,
            program,
            effective_status,
            outcome.status,
            checkpoint_data_value(&effective_status),
            super::orchestrate::git_sha(),
            P2_BASE_HARNESS_HEAD,
            contract.base_manifest_sha256,
            P2_BASE_MANIFEST_SHA256,
            P2_CANDIDATE_UNIVERSE_SHA256,
            P2_NON_BROTLI_IDENTITY_SHA256,
            mac_comparison,
            contract.snapshot.display(),
            timeout_s,
            keys.len(),
            queried,
            keys.first().expect("nonempty recovery shard"),
            keys.last().expect("nonempty recovery shard"),
            progress.phase,
            progress.candidate.as_deref().unwrap_or("none"),
            progress.elapsed_s,
            checkpoint_rows.len(),
            checkpoint_rows
                .last()
                .map(|row| row.field_key.as_str())
                .unwrap_or("none"),
            outcome.wall_s,
            outcome.wall_s / keys.len() as f64,
            outcome.peak_rss_kb,
            hard_unsat,
            force_sat,
            solver_unknown,
            accepted_owning,
            validation_error.as_deref().unwrap_or("none"),
        ),
    )
    .expect("write recovery receipt");
    let mut artifacts = vec![
        targets.clone(),
        stdout.clone(),
        stderr.clone(),
        receipt_path.clone(),
    ];
    if probe.is_file() {
        artifacts.push(probe.clone());
    }
    if checkpoint.is_file() {
        artifacts.push(checkpoint.clone());
    }
    if checkpoint_temp.is_file() {
        artifacts.push(checkpoint_temp.clone());
    }
    write_sha256_manifest(&shard_dir, &artifacts, &manifest)
        .unwrap_or_else(|error| panic!("write recovery shard manifest: {error}"));
    verify_sha256_manifest(&shard_dir, &manifest)
        .unwrap_or_else(|error| panic!("verify recovery shard manifest: {error}"));

    if effective_status != "ok" {
        panic!(
            "P2 recovery STOP: program={} status={} phase={} candidate={} peak_rss_kb={} wall_s={:.3} detail={}",
            program,
            effective_status,
            progress.phase,
            progress.candidate.as_deref().unwrap_or("none"),
            outcome.peak_rss_kb,
            outcome.wall_s,
            validation_error.as_deref().unwrap_or(&outcome.note),
        );
    }
    let receipt = parse_receipt(&receipt_path)
        .unwrap_or_else(|error| panic!("completed recovery receipt: {error}"));
    validate_completed_recovery_shard(
        &program,
        keys,
        &receipt,
        &final_rows,
        &contract.identity,
        &candidate_slots,
    )
    .unwrap_or_else(|error| panic!("P2 recovery STOP: {error}"));
    println!(
        "S23P2RECOVERY machine_id={} platform={} memory_limit=uncapped program={} status=ok candidates={} hard_unsat={} force_sat={} wall_s={:.3} wall_s_per_candidate={:.6} peak_rss_kb={}",
        contract.identity.machine_id,
        contract.identity.platform,
        program,
        keys.len(),
        hard_unsat,
        force_sat,
        outcome.wall_s,
        outcome.wall_s / keys.len() as f64,
        outcome.peak_rss_kb,
    );
}

/// Measure one program from the exact 61-candidate complement of the accepted
/// 200-row aggregate. SAT and UNSAT are both first-time result classes here;
/// Unknown, identity drift, or an incomplete worker is a manifested data=false
/// STOP and is never eligible for aggregation.
#[test]
#[ignore = "P2 61-candidate completion; run one dedicated-host shard explicitly"]
fn s23_p2_completion_shard() {
    let contract = checkpoint_contract();
    let candidates = checkpoint_candidates(&contract.base);
    let candidate_slots = candidates
        .iter()
        .map(|candidate| {
            (
                (candidate.program.clone(), candidate.field_key.clone()),
                candidate.field_slot,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let programs = completion_checkpoint_programs(&candidates)
        .unwrap_or_else(|error| panic!("P2 completion partition: {error}"));
    let program = std::env::var("CRAT_S23_COMPLETION_PROGRAM")
        .expect("completion requires CRAT_S23_COMPLETION_PROGRAM");
    let program_index = programs
        .iter()
        .position(|(candidate_program, _)| candidate_program == &program)
        .unwrap_or_else(|| {
            panic!(
                "completion program {program:?} is outside the registered order {:?}",
                programs
                    .iter()
                    .map(|(candidate_program, _)| candidate_program)
                    .collect::<Vec<_>>()
            )
        });
    let keys = &programs[program_index].1;
    let completed_predecessors = programs[..program_index]
        .iter()
        .map(|(candidate_program, _)| candidate_program.as_str())
        .collect::<Vec<_>>()
        .join(",");
    for (predecessor, predecessor_keys) in &programs[..program_index] {
        let predecessor_dir = contract
            .batches
            .join("completion-shards")
            .join(predecessor);
        let predecessor_manifest = predecessor_dir.join("artifact-manifest.sha256");
        let stop_candidate = keys
            .first()
            .map(String::as_str)
            .unwrap_or("<empty-shard>");
        verify_sha256_manifest(&predecessor_dir, &predecessor_manifest).unwrap_or_else(|error| {
            panic!(
                "P2 completion STOP: program={program} status=sequence-violation phase=predecessor-manifest candidate={stop_candidate} detail={predecessor}:{error}"
            )
        });
        let predecessor_receipt = parse_receipt(&predecessor_dir.join("receipt.txt"))
            .unwrap_or_else(|error| {
                panic!(
                    "P2 completion STOP: program={program} status=sequence-violation phase=predecessor-receipt candidate={stop_candidate} detail={predecessor}:{error}"
                )
            });
        if predecessor_receipt.get("data").map(String::as_str) != Some("true") {
            panic!(
                "P2 completion STOP: program={program} status=sequence-violation phase=predecessor-data candidate={stop_candidate} detail={predecessor}:data-false"
            );
        }
        let predecessor_rows = parse_probe_for_program(
            &predecessor_dir.join("probes.tsv"),
            Some(predecessor),
        )
        .unwrap_or_else(|error| {
            panic!(
                "P2 completion STOP: program={program} status=sequence-violation phase=predecessor-probes candidate={stop_candidate} detail={predecessor}:{error}"
            )
        });
        validate_completed_completion_shard(
            predecessor,
            predecessor_keys,
            &predecessor_receipt,
            &predecessor_rows,
            &contract.identity,
            &candidate_slots,
        )
        .unwrap_or_else(|error| {
            panic!(
                "P2 completion STOP: program={program} status=sequence-violation phase=predecessor-validation candidate={stop_candidate} detail={predecessor}:{error}"
            )
        });
        assert_eq!(
            read_target_keys(&predecessor_dir.join("targets.txt"))
                .unwrap_or_else(|error| panic!("predecessor targets {predecessor}: {error}")),
            *predecessor_keys,
            "P2 completion STOP: program={program} status=sequence-violation phase=predecessor-targets candidate={stop_candidate} detail={predecessor}"
        );
        assert_eq!(
            parse_probe_for_program(
                &predecessor_dir.join("partial-probes.tsv"),
                Some(predecessor),
            )
            .unwrap_or_else(|error| panic!("predecessor checkpoint {predecessor}: {error}")),
            predecessor_rows,
            "P2 completion STOP: program={program} status=sequence-violation phase=predecessor-checkpoint candidate={stop_candidate} detail={predecessor}"
        );
        assert!(
            !probe_checkpoint_temp_path(&predecessor_dir.join("partial-probes.tsv")).exists(),
            "P2 completion STOP: program={program} status=sequence-violation phase=predecessor-checkpoint candidate={stop_candidate} detail={predecessor}:temporary-file"
        );
    }
    let timeout_override = std::env::var("CRAT_S23_BATCH_TIMEOUT_SECS").ok();
    let timeout_s = checkpoint_batch_timeout_s(timeout_override.as_deref())
        .unwrap_or_else(|error| panic!("completion liveness bound: {error}"));
    let shard_dir = contract.batches.join("completion-shards").join(&program);
    let manifest = shard_dir.join("artifact-manifest.sha256");
    let targets = shard_dir.join("targets.txt");
    let probe = shard_dir.join("probes.tsv");
    let checkpoint = shard_dir.join("partial-probes.tsv");
    let checkpoint_temp = probe_checkpoint_temp_path(&checkpoint);
    let stdout = shard_dir.join("stdout.txt");
    let stderr = shard_dir.join("stderr.txt");
    let receipt_path = shard_dir.join("receipt.txt");

    if manifest.is_file() {
        verify_sha256_manifest(&shard_dir, &manifest)
            .unwrap_or_else(|error| panic!("completed completion shard manifest: {error}"));
        let receipt = parse_receipt(&receipt_path)
            .unwrap_or_else(|error| panic!("completed completion shard receipt: {error}"));
        if receipt.get("data").map(String::as_str) != Some("true") {
            panic!(
                "P2 completion STOP: program={} status={} phase={} candidate={}; manifested data=false shard is provenance-only",
            program,
                receipt
                    .get("status")
                    .map(String::as_str)
                    .unwrap_or("missing"),
                receipt
                    .get("stop_phase")
                    .map(String::as_str)
                    .unwrap_or("missing"),
                receipt
                    .get("stop_candidate")
                    .map(String::as_str)
                    .unwrap_or("missing"),
            );
        }
        let rows = parse_probe_for_program(&probe, Some(&program))
            .unwrap_or_else(|error| panic!("completed completion shard probes: {error}"));
        validate_completed_completion_shard(
            &program,
            keys,
            &receipt,
            &rows,
            &contract.identity,
            &candidate_slots,
        )
        .unwrap_or_else(|error| panic!("P2 completion STOP: {error}"));
        assert_eq!(
            read_target_keys(&targets)
                .unwrap_or_else(|error| panic!("completed completion targets: {error}")),
            *keys,
            "completed completion target identity drifted"
        );
        assert_eq!(
            parse_probe_for_program(&checkpoint, Some(&program))
                .unwrap_or_else(|error| panic!("completed completion checkpoint: {error}")),
            rows,
            "completed completion checkpoint/final drifted"
        );
        assert!(
            !checkpoint_temp.exists(),
            "completed completion shard retained a temporary checkpoint"
        );
        println!(
            "S23P2COMPLETION machine_id={} platform={} program={} status=verified-skip candidates={}",
            contract.identity.machine_id,
            contract.identity.platform,
            program,
            keys.len()
        );
        return;
    }
    assert!(
        !shard_dir.exists(),
        "P2 STOP: unmanifested completion shard exists at {}; preserve it for inspection",
        shard_dir.display()
    );
    fs::create_dir_all(&shard_dir).expect("create completion shard directory");
    write_targets(&targets, keys).unwrap_or_else(|error| panic!("completion targets: {error}"));

    let corpus_program = super::CORPUS
        .iter()
        .find(|entry| entry.name == program)
        .unwrap_or_else(|| panic!("completion program {program} lacks a corpus entry"));
    let input = contract
        .corpus_link
        .join(corpus_program.name)
        .join(corpus_program.lib_root);
    let outcome = super::orchestrate::run_child_labeled(
        &program,
        &input,
        "s23-probe",
        &format!("s23-p2-completion-{program}"),
        Duration::from_secs(timeout_s as u64),
        &[
            ("CRAT_S23_TARGET_KEYS", targets.display().to_string()),
            ("CRAT_S23_PROBE_ARTIFACT", probe.display().to_string()),
            (
                "CRAT_S23_CHECKPOINT_ARTIFACT",
                checkpoint.display().to_string(),
            ),
        ],
    );
    fs::write(&stdout, &outcome.stdout).expect("write completion stdout");
    fs::write(&stderr, &outcome.stderr).expect("write completion stderr");
    let progress = outcome
        .stderr
        .lines()
        .filter_map(parse_checkpoint_phase)
        .next_back()
        .unwrap_or_else(|| CheckpointProgress {
            phase: "worker-not-entered".to_owned(),
            candidate: None,
            completed: 0,
            elapsed_s: format!("{:.3}", outcome.wall_s),
        });
    let mut failure_phase = None::<String>;
    let mut failure_candidate = None::<String>;
    let (checkpoint_rows, mut validation_error) = if checkpoint.is_file() {
        match parse_probe_for_program(&checkpoint, Some(&program)) {
            Ok(rows) => (rows, None),
            Err(error) => {
                failure_phase = Some("checkpoint-parse".to_owned());
                failure_candidate = Some("<partial-probes.tsv>".to_owned());
                (
                    Vec::new(),
                    Some(format!(
                        "identity mismatch for {program}: invalid partial checkpoint: {error}"
                    )),
                )
            }
        }
    } else {
        (Vec::new(), None)
    };
    if validation_error.is_none()
        && !(checkpoint_rows.len() == progress.completed
            || (progress.phase == "force-own-start"
                && checkpoint_rows.len() == progress.completed + 1))
    {
        failure_phase = Some("checkpoint-progress".to_owned());
        failure_candidate = progress.candidate.clone().or_else(|| {
            keys.get(checkpoint_rows.len().min(keys.len() - 1))
                .cloned()
        });
        validation_error = Some(format!(
            "identity mismatch for {program}: partial checkpoint rows={} disagree with phase={} completed={}",
            checkpoint_rows.len(),
            progress.phase,
            progress.completed
        ));
    }
    if validation_error.is_none() {
        if checkpoint_rows.len() > keys.len() {
            failure_phase = Some("checkpoint-identity".to_owned());
            failure_candidate = checkpoint_rows
                .get(keys.len())
                .map(|row| row.field_key.clone());
            validation_error = Some(format!(
                "identity mismatch for {program}: partial checkpoint has {} rows for {} targets",
                checkpoint_rows.len(),
                keys.len()
            ));
        } else if let Err(error) = validate_completion_rows(
            &program,
            &keys[..checkpoint_rows.len()],
            &checkpoint_rows,
            &candidate_slots,
        ) {
            failure_phase = Some("checkpoint-row-validation".to_owned());
            failure_candidate = Some(completion_row_failure_candidate(
                &program,
                &keys[..checkpoint_rows.len()],
                &checkpoint_rows,
                &candidate_slots,
            ));
            validation_error = Some(error);
        }
    }
    let mut final_rows = Vec::new();
    if outcome.status == "ok" {
        match parse_probe_for_program(&probe, Some(&program)) {
            Ok(rows) => {
                if validation_error.is_none() {
                    if let Err(error) =
                        validate_completion_rows(&program, keys, &rows, &candidate_slots)
                    {
                        failure_phase = Some("final-row-validation".to_owned());
                        failure_candidate = Some(completion_row_failure_candidate(
                            &program,
                            keys,
                            &rows,
                            &candidate_slots,
                        ));
                        validation_error = Some(error);
                    } else if rows != checkpoint_rows {
                        let mismatch = rows
                            .iter()
                            .zip(&checkpoint_rows)
                            .position(|(final_row, checkpoint_row)| final_row != checkpoint_row)
                            .unwrap_or(rows.len().min(checkpoint_rows.len()));
                        failure_phase = Some("checkpoint-final-identity".to_owned());
                        failure_candidate = rows
                            .get(mismatch)
                            .or_else(|| checkpoint_rows.get(mismatch))
                            .map(|row| row.field_key.clone())
                            .or_else(|| keys.get(mismatch).cloned());
                        validation_error = Some(format!(
                            "identity mismatch for {program}: completed checkpoint/final tables differ"
                        ));
                    } else if checkpoint_temp.exists() {
                        failure_phase = Some("checkpoint-publish".to_owned());
                        failure_candidate = keys.last().cloned();
                        validation_error = Some(format!(
                            "identity mismatch for {program}: temporary checkpoint survived publish"
                        ));
                    }
                }
                final_rows = rows;
            }
            Err(error) => {
                failure_phase = Some("final-probe-parse".to_owned());
                failure_candidate = Some("<probes.tsv>".to_owned());
                validation_error = Some(format!(
                    "identity mismatch for {program}: invalid final probe artifact: {error}"
                ));
            }
        }
    }
    let observed_rows = if final_rows.is_empty() {
        &checkpoint_rows
    } else {
        &final_rows
    };
    let unknown_candidate = observed_rows
        .iter()
        .find(|row| row.force_result == ForceResult::Unknown)
        .map(|row| row.field_key.as_str());
    let effective_status = if unknown_candidate.is_some() {
        "solver-unknown".to_owned()
    } else if validation_error.is_some() {
        "identity-mismatch".to_owned()
    } else if outcome.status != "ok" {
        outcome.status.clone()
    } else {
        "ok".to_owned()
    };
    let stop_phase = if unknown_candidate.is_some() {
        "force-own-result"
    } else if let Some(failure_phase) = failure_phase.as_deref() {
        failure_phase
    } else {
        progress.phase.as_str()
    };
    let stop_candidate = unknown_candidate
        .or(failure_candidate.as_deref())
        .or(progress.candidate.as_deref())
        .or_else(|| {
            keys.get(progress.completed.min(keys.len() - 1))
                .map(String::as_str)
        })
        .unwrap_or("none");
    let queried = observed_rows.len();
    let hard_unsat = observed_rows
        .iter()
        .filter(|row| row.force_result == ForceResult::Unsat)
        .count();
    let force_sat = observed_rows
        .iter()
        .filter(|row| row.force_result == ForceResult::Sat)
        .count();
    let solver_unknown = observed_rows
        .iter()
        .filter(|row| row.force_result == ForceResult::Unknown)
        .count();
    let accepted_owning = observed_rows
        .iter()
        .filter(|row| row.accepted_kind == SlotKind::Owning)
        .count();
    fs::write(
        &receipt_path,
        format!(
            "machine_id={}\nplatform={}\nmachine_protocol=dedicated-host\nmemory_limit=uncapped\nwall_bound_kind=liveness\nprogram={}\nstatus={}\nworker_status={}\ndata={}\ncheckpoint_data=false\nanalysis_head={}\nbase_harness_head={}\nbase_manifest_sha256={}\naccepted_aggregate_manifest_sha256={}\ncandidate_universe_sha256={}\ncompletion_identity_list_sha256={}\ncompletion_order={}\ncompleted_predecessors={}\nsnapshot={}\nwall_cap_s={}\nplanned_targets={}\nqueried={}\nfirst_key={}\nlast_key={}\nlast_phase={}\nlast_candidate={}\nlast_phase_t_s={}\nstop_phase={}\nstop_candidate={}\ncheckpoint_rows={}\ncheckpoint_last_key={}\nwall_s={:.3}\nwall_s_per_candidate={:.6}\npeak_rss_kb={}\nhard_unsat={}\nforce_sat={}\nsolver_unknown={}\naccepted_owning={}\nvalidation_error={}\n",
            contract.identity.machine_id,
            contract.identity.platform,
            program,
            effective_status,
            outcome.status,
            checkpoint_data_value(&effective_status),
            super::orchestrate::git_sha(),
            P2_BASE_HARNESS_HEAD,
            contract.base_manifest_sha256,
            P2_ACCEPTED_AGGREGATE_MANIFEST_SHA256,
            P2_CANDIDATE_UNIVERSE_SHA256,
            P2_COMPLETION_IDENTITY_SHA256,
            P2_COMPLETION_ORDER,
            completed_predecessors,
            contract.snapshot.display(),
            timeout_s,
            keys.len(),
            queried,
            keys.first().expect("nonempty completion shard"),
            keys.last().expect("nonempty completion shard"),
            progress.phase,
            progress.candidate.as_deref().unwrap_or("none"),
            progress.elapsed_s,
            stop_phase,
            stop_candidate,
            checkpoint_rows.len(),
            checkpoint_rows
                .last()
                .map(|row| row.field_key.as_str())
                .unwrap_or("none"),
            outcome.wall_s,
            outcome.wall_s / keys.len() as f64,
            outcome.peak_rss_kb,
            hard_unsat,
            force_sat,
            solver_unknown,
            accepted_owning,
            validation_error.as_deref().unwrap_or("none"),
        ),
    )
    .expect("write completion receipt");
    let mut artifacts = vec![
        targets.clone(),
        stdout.clone(),
        stderr.clone(),
        receipt_path.clone(),
    ];
    if probe.is_file() {
        artifacts.push(probe.clone());
    }
    if checkpoint.is_file() {
        artifacts.push(checkpoint.clone());
    }
    if checkpoint_temp.is_file() {
        artifacts.push(checkpoint_temp.clone());
    }
    write_sha256_manifest(&shard_dir, &artifacts, &manifest)
        .unwrap_or_else(|error| panic!("write completion shard manifest: {error}"));
    verify_sha256_manifest(&shard_dir, &manifest)
        .unwrap_or_else(|error| panic!("verify completion shard manifest: {error}"));

    if effective_status != "ok" {
        panic!(
            "P2 completion STOP: program={} status={} phase={} candidate={} peak_rss_kb={} wall_s={:.3} detail={}",
            program,
            effective_status,
            stop_phase,
            stop_candidate,
            outcome.peak_rss_kb,
            outcome.wall_s,
            validation_error.as_deref().unwrap_or(&outcome.note),
        );
    }
    let receipt = parse_receipt(&receipt_path)
        .unwrap_or_else(|error| panic!("completed completion receipt: {error}"));
    validate_completed_completion_shard(
        &program,
        keys,
        &receipt,
        &final_rows,
        &contract.identity,
        &candidate_slots,
    )
    .unwrap_or_else(|error| panic!("P2 completion STOP: {error}"));
    println!(
        "S23P2COMPLETION machine_id={} platform={} memory_limit=uncapped program={} status=ok candidates={} hard_unsat={} force_sat={} wall_s={:.3} wall_s_per_candidate={:.6} peak_rss_kb={}",
        contract.identity.machine_id,
        contract.identity.platform,
        program,
        keys.len(),
        hard_unsat,
        force_sat,
        outcome.wall_s,
        outcome.wall_s / keys.len() as f64,
        outcome.peak_rss_kb,
    );
}

/// Combine 13 manifested Linux recovery shards with eight manifested brotli
/// checkpoints. No private-directory-only input is accepted.
/// This phase launches no corpus worker and forms the aggregate only after the
/// selected 200/261 eligible candidates are complete exactly once.
#[test]
#[ignore = "P2 checkpoint aggregate; run after all brotli batches"]
fn s23_p2_checkpoint_aggregate() {
    let contract = checkpoint_contract();
    let platform_equivalence = std::env::var("CRAT_S23_PLATFORM_EQUIVALENCE")
        .expect("aggregate requires the recorded batch-0 platform-equivalence verdict");
    assert_eq!(
        platform_equivalence, "brotli-batch-000-verdict-and-core-families-identical",
        "aggregate refuses an unrecognized platform-equivalence verdict"
    );
    let candidates = checkpoint_candidates(&contract.base);
    assert_eq!(candidates.len(), 410, "screened field population drifted");
    let selected = selected_checkpoint_candidates(&candidates);
    assert_eq!(selected.len(), P2_QUERY_BUDGET);
    assert_eq!(
        selected
            .iter()
            .filter(|(program, _)| program == "brotli")
            .count(),
        P2_BROTLI_ELIGIBLE
    );
    let candidate_slots = candidates
        .iter()
        .map(|candidate| {
            (
                (candidate.program.clone(), candidate.field_key.clone()),
                candidate.field_slot,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let aggregate = contract.batches.join("aggregate");
    let aggregate_manifest = aggregate.join("artifact-manifest.sha256");
    if aggregate_manifest.is_file() {
        verify_sha256_manifest(&aggregate, &aggregate_manifest)
            .unwrap_or_else(|error| panic!("aggregate failed re-verification: {error}"));
        println!("S23P2AGG status=verified-skip");
        return;
    }
    assert!(
        !aggregate.exists(),
        "P2 STOP: unmanifested partial aggregate exists at {}",
        aggregate.display()
    );

    let mut probes = BTreeMap::new();
    let recovery_programs = non_brotli_checkpoint_programs(&candidates)
        .unwrap_or_else(|error| panic!("P2 recovery partition: {error}"));
    let recovery_root = contract.batches.join("non-brotli-shards");
    let published_programs = fs::read_dir(&recovery_root)
        .expect("read published recovery shards")
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_ok_and(|kind| kind.is_dir()))
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        published_programs,
        recovery_programs.keys().cloned().collect(),
        "P2 STOP: published recovery shard set drifted"
    );
    let mut recovery_rows = 0usize;
    let mut recovery_stats = Vec::new();
    for (program, expected) in &recovery_programs {
        let shard_dir = recovery_root.join(program);
        let manifest = shard_dir.join("artifact-manifest.sha256");
        verify_sha256_manifest(&shard_dir, &manifest)
            .unwrap_or_else(|error| panic!("recovery shard {program} manifest: {error}"));
        assert_eq!(
            read_target_keys(&shard_dir.join("targets.txt"))
                .unwrap_or_else(|error| panic!("recovery shard {program} targets: {error}")),
            *expected,
            "recovery shard {program} target identity drifted"
        );
        let receipt = parse_receipt(&shard_dir.join("receipt.txt"))
            .unwrap_or_else(|error| panic!("recovery shard {program} receipt: {error}"));
        let rows = parse_probe_for_program(&shard_dir.join("probes.tsv"), Some(program))
            .unwrap_or_else(|error| panic!("recovery shard {program} probes: {error}"));
        validate_completed_recovery_shard(
            program,
            expected,
            &receipt,
            &rows,
            &contract.identity,
            &candidate_slots,
        )
        .unwrap_or_else(|error| panic!("P2 recovery STOP: {error}"));
        assert_eq!(
            parse_probe_for_program(&shard_dir.join("partial-probes.tsv"), Some(program))
                .unwrap_or_else(|error| {
                    panic!("recovery shard {program} partial checkpoint: {error}")
                }),
            rows,
            "recovery shard {program} checkpoint/final drifted"
        );
        assert!(
            !probe_checkpoint_temp_path(&shard_dir.join("partial-probes.tsv")).exists(),
            "recovery shard {program} retained a temporary checkpoint"
        );
        recovery_rows += insert_probe_artifact(
            program,
            &shard_dir.join("probes.tsv"),
            &candidate_slots,
            &selected,
            &mut probes,
        )
        .unwrap_or_else(|error| panic!("recovery shard {program}: {error}"));
        recovery_stats.push((
            program.clone(),
            expected.len(),
            receipt["wall_s"]
                .parse::<f64>()
                .expect("recovery shard wall"),
            receipt["wall_s_per_candidate"]
                .parse::<f64>()
                .expect("recovery shard per-candidate wall"),
            receipt["peak_rss_kb"]
                .parse::<u64>()
                .expect("recovery shard peak RSS"),
            sha256_file(&manifest).expect("hash recovery shard manifest"),
        ));
    }
    assert_eq!(recovery_rows, 88, "recovered row population drifted");

    let brotli_keys = selected
        .iter()
        .filter(|(program, _)| program == "brotli")
        .map(|(_, key)| key.clone())
        .collect::<Vec<_>>();
    assert!(
        std::env::var_os("CRAT_S23_BATCH_SIZE").is_none(),
        "CRAT_S23_BATCH_SIZE is retired; the aggregate uses the registered heterogeneous plan"
    );
    let ranges = checkpoint_batch_ranges(brotli_keys.len())
        .unwrap_or_else(|error| panic!("checkpoint plan: {error}"));
    let mut batch_stats = Vec::new();
    let mut brotli_rows = 0usize;
    for (batch_index, range) in ranges.iter().enumerate() {
        let batch_dir = contract.batches.join(format!("batch-{batch_index:03}"));
        let manifest = batch_dir.join("artifact-manifest.sha256");
        verify_sha256_manifest(&batch_dir, &manifest)
            .unwrap_or_else(|error| panic!("batch {batch_index} manifest: {error}"));
        let expected = &brotli_keys[range.clone()];
        assert_eq!(
            read_target_keys(&batch_dir.join("targets.txt"))
                .unwrap_or_else(|error| panic!("batch {batch_index} targets: {error}")),
            expected,
            "batch {batch_index} target slice drifted"
        );
        let receipt = parse_receipt(&batch_dir.join("receipt.txt"))
            .unwrap_or_else(|error| panic!("batch {batch_index} receipt: {error}"));
        assert_eq!(receipt.get("status").map(String::as_str), Some("ok"));
        if batch_index >= 2 {
            assert_eq!(
                receipt.get("data").map(String::as_str),
                Some("true"),
                "batch {batch_index} is not a completed data-bearing run"
            );
            assert_eq!(
                receipt.get("checkpoint_data").map(String::as_str),
                Some("false"),
                "batch {batch_index} checkpoint artifact must remain provenance-only"
            );
            assert_eq!(
                receipt.get("wall_bound_kind").map(String::as_str),
                Some("liveness"),
                "batch {batch_index} wall bound kind drift"
            );
            assert_eq!(
                receipt
                    .get("wall_cap_s")
                    .and_then(|value| value.parse().ok()),
                Some(14400usize),
                "batch {batch_index} wall-liveness bound drift"
            );
        }
        assert_eq!(
            receipt.get("machine_id").map(String::as_str),
            Some(contract.identity.machine_id.as_str())
        );
        assert_eq!(
            receipt.get("platform").map(String::as_str),
            Some(contract.identity.platform.as_str())
        );
        assert_eq!(
            receipt.get("queried").and_then(|value| value.parse().ok()),
            Some(expected.len())
        );
        assert_eq!(
            receipt.get("batch").and_then(|value| value.parse().ok()),
            Some(batch_index),
            "batch {batch_index} receipt index drift"
        );
        assert_eq!(
            receipt
                .get("range_start")
                .and_then(|value| value.parse().ok()),
            Some(range.start),
            "batch {batch_index} range start drift"
        );
        assert_eq!(
            receipt
                .get("range_end")
                .and_then(|value| value.parse().ok()),
            Some(range.end),
            "batch {batch_index} range end drift"
        );
        assert_eq!(
            receipt
                .get("batch_size")
                .and_then(|value| value.parse().ok()),
            Some(expected.len()),
            "batch {batch_index} candidate-count drift"
        );
        if batch_index >= 2 {
            assert_eq!(
                receipt.get("batch_plan").map(String::as_str),
                Some(P2_CHECKPOINT_BATCH_PLAN),
                "batch {batch_index} plan provenance drift"
            );
        }
        let memory_limit = match receipt.get("memory_limit") {
            Some(value) => {
                assert_eq!(value, "uncapped", "batch {batch_index} memory limit drift");
                value.clone()
            }
            None => {
                assert_eq!(
                    batch_index, 0,
                    "only the completed cross-platform control may use the retired cap"
                );
                "8192-mib-control".to_owned()
            }
        };
        brotli_rows += insert_probe_artifact(
            "brotli",
            &batch_dir.join("probes.tsv"),
            &candidate_slots,
            &selected,
            &mut probes,
        )
        .unwrap_or_else(|error| panic!("batch {batch_index} probes: {error}"));
        batch_stats.push((
            batch_index,
            expected.len(),
            receipt["wall_s"].parse::<f64>().expect("batch wall"),
            receipt["wall_s_per_candidate"]
                .parse::<f64>()
                .expect("batch per-candidate wall"),
            receipt["peak_rss_kb"]
                .parse::<u64>()
                .expect("batch peak RSS"),
            memory_limit,
        ));
    }
    assert_eq!(brotli_rows, P2_BROTLI_ELIGIBLE);
    let mac_brotli_rows = brotli_keys[..P2_MAC_BROTLI_COMPLETED]
        .iter()
        .map(|key| {
            probes
                .get(&("brotli".to_owned(), key.clone()))
                .expect("mac-measured brotli row must be present")
                .clone()
        })
        .collect::<Vec<_>>();
    validate_recovery_rows(
        "brotli",
        &brotli_keys[..P2_MAC_BROTLI_COMPLETED],
        &mac_brotli_rows,
        &candidate_slots,
    )
    .unwrap_or_else(|error| panic!("P2 platform STOP: {error}"));
    let brotli_force_sat_keys = brotli_keys
        .iter()
        .filter(|key| {
            probes
                .get(&("brotli".to_owned(), (*key).clone()))
                .is_some_and(|row| row.force_result == ForceResult::Sat)
        })
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(
        brotli_force_sat_keys,
        P2_FIRST_TIME_BROTLI_FORCE_SAT.map(str::to_owned),
        "brotli force-SAT identity drifted"
    );
    validate_brotli_mac_overlap(&brotli_keys, &brotli_force_sat_keys)
        .unwrap_or_else(|error| panic!("P2 platform STOP: {error}"));
    assert_eq!(probes.len(), P2_QUERY_BUDGET);
    assert_eq!(
        probes.keys().cloned().collect::<BTreeSet<_>>(),
        selected,
        "selected candidates were not probed exactly once"
    );

    let mut final_records = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        let identity = (candidate.program.clone(), candidate.field_key.clone());
        let probe = probes.get(&identity);
        let (force_result, accepted_kind, core_families) = match probe {
            Some(probe) => (
                probe.force_result,
                Some(probe.accepted_kind),
                probe.core_families.clone(),
            ),
            None => (ForceResult::NotQueried, None, Vec::new()),
        };
        final_records.push(FinalRecord {
            bucket: terminal_bucket(candidate.discovery, force_result, accepted_kind),
            candidate,
            accepted_kind,
            force_result,
            core_families,
        });
    }
    let mut bucket_counts = BTreeMap::new();
    for record in &final_records {
        *bucket_counts.entry(record.bucket.label()).or_insert(0usize) += 1;
    }
    assert_eq!(bucket_counts.values().sum::<usize>(), final_records.len());
    assert_eq!(
        final_records
            .iter()
            .filter(|record| record.candidate.discovery == DiscoveryClass::Eligible)
            .count(),
        261
    );
    assert_eq!(
        bucket_counts
            .get(TerminalBucket::SolverUnknown.label())
            .copied()
            .unwrap_or(0),
        0,
        "P2 STOP: aggregate contains solver Unknown"
    );
    let hard_unsat = final_records
        .iter()
        .filter(|record| record.bucket == TerminalBucket::HardUnsat)
        .collect::<Vec<_>>();
    let own_assume = hard_unsat
        .iter()
        .filter(|record| {
            record
                .core_families
                .iter()
                .any(|family| family == "own-assume")
        })
        .count();
    let link_own = hard_unsat
        .iter()
        .filter(|record| {
            record
                .core_families
                .iter()
                .any(|family| family == "link-own")
        })
        .count();
    let mut family_histogram = BTreeMap::new();
    for record in &hard_unsat {
        for family in &record.core_families {
            *family_histogram.entry(family.clone()).or_insert(0usize) += 1;
        }
    }
    let accepted = |kind| {
        final_records
            .iter()
            .filter(|record| record.accepted_kind == Some(kind))
            .count()
    };
    let force_sat = final_records
        .iter()
        .filter(|record| record.force_result == ForceResult::Sat)
        .count();
    let non_brotli_hard_unsat = hard_unsat
        .iter()
        .filter(|record| record.candidate.program != "brotli")
        .count();
    let brotli_hard_unsat = hard_unsat
        .iter()
        .filter(|record| record.candidate.program == "brotli")
        .count();
    let non_brotli_force_sat = final_records
        .iter()
        .filter(|record| {
            record.candidate.program != "brotli" && record.force_result == ForceResult::Sat
        })
        .count();
    let brotli_force_sat = final_records
        .iter()
        .filter(|record| {
            record.candidate.program == "brotli" && record.force_result == ForceResult::Sat
        })
        .count();
    let core_family_count = |program_is_brotli: bool, family: &str| {
        hard_unsat
            .iter()
            .filter(|record| {
                (record.candidate.program == "brotli") == program_is_brotli
                    && record
                        .core_families
                        .iter()
                        .any(|candidate_family| candidate_family == family)
            })
            .count()
    };
    let non_brotli_own_assume = core_family_count(false, "own-assume");
    let non_brotli_link_own = core_family_count(false, "link-own");
    let brotli_own_assume = core_family_count(true, "own-assume");
    let brotli_link_own = core_family_count(true, "link-own");
    assert_eq!(
        (
            non_brotli_hard_unsat,
            non_brotli_force_sat,
            non_brotli_own_assume,
            non_brotli_link_own,
        ),
        (88, 0, 88, 88),
        "P2 platform STOP: recovered non-brotli class diverged from the mac universal record"
    );
    assert_eq!(
        (
            brotli_hard_unsat,
            brotli_force_sat,
            brotli_own_assume,
            brotli_link_own,
        ),
        (109, 3, 109, 109),
        "brotli result-class partition drifted"
    );
    assert_eq!(
        (hard_unsat.len(), force_sat, own_assume, link_own),
        (197, 3, 197, 197)
    );
    let wall_sum = batch_stats
        .iter()
        .map(|(_, _, wall, _, _, _)| wall)
        .sum::<f64>();
    let recovery_wall_sum = recovery_stats
        .iter()
        .map(|(_, _, wall, _, _, _)| wall)
        .sum::<f64>();
    let recovery_table = recovery_stats
        .iter()
        .map(|(program, queried, wall, per_candidate, peak, _)| {
            format!(
                "| {} | {} | {program} | {queried} | {wall:.3} | {per_candidate:.6} | {peak} |",
                contract.identity.platform, contract.identity.machine_id,
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let recovery_manifests = recovery_stats
        .iter()
        .map(|(program, _, _, _, _, digest)| format!("{program}:{digest}"))
        .collect::<Vec<_>>()
        .join(",");
    let batch_table = batch_stats
        .iter()
        .map(|(index, queried, wall, per_candidate, peak, memory_limit)| {
            format!(
                "| {} | {} | {memory_limit} | {index} | {queried} | {wall:.3} | {per_candidate:.6} | {peak} |",
                contract.identity.platform, contract.identity.machine_id,
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let terminal_counts = bucket_counts
        .iter()
        .map(|(bucket, count)| format!("{bucket}={count}"))
        .collect::<Vec<_>>()
        .join(" ");
    let core_counts = family_histogram
        .iter()
        .map(|(family, count)| format!("{family}={count}"))
        .collect::<Vec<_>>()
        .join(" ");
    let first_time_sat = brotli_force_sat_keys.join(", ");
    let first_time_sat_provenance = brotli_force_sat_keys.join("|");

    fs::create_dir_all(&aggregate).expect("create aggregate directory");
    let classification = aggregate.join("classification.tsv");
    let combined_probes = aggregate.join("combined-probes.tsv");
    let per_program = aggregate.join("per-program.tsv");
    let report = aggregate.join("report.md");
    let provenance = aggregate.join("provenance.txt");
    fs::write(
        &classification,
        render_final_tsv(&final_records, &contract.identity),
    )
    .expect("write checkpoint classification");
    let mut combined = String::from(
        "platform\tmachine_id\tprogram\tfield_key\tfield_slot\taccepted_kind\tforce_result\tcore_families\tcore_labels\n",
    );
    for ((program, _), probe) in &probes {
        let force = match probe.force_result {
            ForceResult::Sat => "sat",
            ForceResult::Unsat => "unsat",
            ForceResult::Unknown => "unknown",
            ForceResult::NotQueried => "not-queried",
        };
        combined.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            contract.identity.platform,
            contract.identity.machine_id,
            program,
            probe.field_key,
            probe.field_slot,
            kind_label(probe.accepted_kind),
            force,
            probe.core_families.join("|"),
            probe.core_labels.join("|")
        ));
    }
    fs::write(&combined_probes, combined).expect("write combined probes");
    let mut per_program_rows = String::from(
        "platform\tmachine_id\tprogram\tscreened\teligible\tno_owned_capable_store\tstore_blocked\tqueried\thard_unsat\tforce_sat\tsolver_unknown\tbudget_not_queried\taccepted_raw\taccepted_ref\taccepted_owning\n",
    );
    for corpus_program in super::CORPUS {
        let rows = final_records
        .iter()
            .filter(|record| record.candidate.program == corpus_program.name)
        .collect::<Vec<_>>();
        let count_discovery = |class| {
            rows.iter()
                .filter(|record| record.candidate.discovery == class)
                .count()
        };
        let count_bucket = |bucket| rows.iter().filter(|record| record.bucket == bucket).count();
        let count_kind = |kind| {
            rows.iter()
                .filter(|record| record.accepted_kind == Some(kind))
                .count()
        };
        per_program_rows.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            contract.identity.platform,
            contract.identity.machine_id,
            corpus_program.name,
            rows.len(),
            count_discovery(DiscoveryClass::Eligible),
            count_discovery(DiscoveryClass::NoOwnedCapableStore),
            count_discovery(DiscoveryClass::StoreBlocked),
            rows.iter()
                .filter(|record| record.force_result != ForceResult::NotQueried)
                .count(),
            count_bucket(TerminalBucket::HardUnsat),
            rows.iter()
                .filter(|record| record.force_result == ForceResult::Sat)
                .count(),
            count_bucket(TerminalBucket::SolverUnknown),
            count_bucket(TerminalBucket::BudgetNotQueried),
            count_kind(SlotKind::Raw),
            count_kind(SlotKind::Ref),
            count_kind(SlotKind::Owning),
        ));
    }
    fs::write(&per_program, per_program_rows).expect("write per-program aggregate");
    fs::write(
        &report,
        format!(
            "# P2 / S2-3 checkpointed derived-substrate diagnosis\n\n- Measurement identity: machine `{}`, platform `{}`; every count and timing below belongs to this identity. Timings are not compared across machines.\n- Brotli batch-0 cross-platform control: `{}`.\n- Screened depth-0 pointer-field universe: **{}**.\n- Eligible owning-store candidates: **261**; no owned-capable store: **{}**; store-blocked: **{}**.\n- Query partition: **200 completed queries + {} budget-not-queried = 261**.\n- Completed result classes: non-brotli **88 hard-UNSAT + 0 force-own SAT**; brotli **109 hard-UNSAT + 3 force-own SAT**; corpus total **197 hard-UNSAT + 3 force-own SAT + 0 Unknown**.\n- Required core-family incidence among hard-UNSAT only: non-brotli `own-assume` **88/88**, `link-own` **88/88**; brotli `own-assume` **109/109**, `link-own` **109/109**; corpus hard-UNSAT `own-assume` **197/197**, `link-own` **197/197**. The three SAT rows have no UNSAT core and are excluded from those denominators.\n- Ordinary accepted kinds among the 200 queried candidates: Raw **{}**, Ref **{}**, Owning **{}**.\n- Recovered non-brotli control: **88 exact keys across 13 completed manifested Linux shards**. Every recovered row matches the durable mac record's universal expectation (hard-UNSAT with `own-assume` and `link-own` present). The original mac row artifacts were not transferred, so this is an aggregate-record comparison, not byte identity or richer per-row family equality. Mac record commit: `bbaaaf0ac4914398e7024dd137accbdc3932ecf5`.\n- Brotli overlap: macOS completed only positions 1–24, which remain 24/24 hard-UNSAT with both required families. The mac all-112 attempt emitted zero rows. Linux SAT positions 36, 51, and 57 are therefore first-time measurements: `{first_time_sat}`.\n- Recovery-shard Linux-local wall sum: **{recovery_wall_sum:.3}s**. Brotli-batch Linux-local wall sum: **{wall_sum:.3}s**. These sums are retained separately and never compared across machines. Recovery shards and brotli batches 1–7 ran uncapped; brotli batch 0 retains its historical control setup.\n- Registered brotli batch plan: **{P2_CHECKPOINT_BATCH_PLAN}** candidates.\n- Terminal counts: `{terminal_counts}`.\n- Core-family incidence among hard-UNSAT rows (incidence, not necessity): `{core_counts}`.\n\n## Non-brotli recovery shards\n\n| platform | machine id | program | candidates | wall s | wall s / candidate | peak RSS KiB |\n|---|---|---|---:|---:|---:|---:|\n{recovery_table}\n\n## Brotli checkpoints\n\n| platform | machine id | memory limit | batch | candidates | wall s | wall s / candidate | peak RSS KiB |\n|---|---|---|---:|---:|---:|---:|---:|\n{batch_table}\n\nEvery aggregation input was a completed, published SHA-256-manifested artifact. The missing private mac directory is recorded as an unattributed environment event. Migration lesson: private-directory data is not transfer-durable and cannot be an aggregation input. The aggregate launched no corpus worker and formed only after all 200 selected candidates were present exactly once. Production analysis code remained read-only.\n",
            contract.identity.machine_id,
            contract.identity.platform,
            platform_equivalence,
            final_records.len(),
            bucket_counts
                .get(TerminalBucket::NoOwnedCapableStore.label())
                .copied()
                .unwrap_or(0),
            bucket_counts
                .get(TerminalBucket::StoreBlocked.label())
                .copied()
                .unwrap_or(0),
            bucket_counts
                .get(TerminalBucket::BudgetNotQueried.label())
                .copied()
                .unwrap_or(0),
            accepted(SlotKind::Raw),
            accepted(SlotKind::Ref),
            accepted(SlotKind::Owning),
        ),
    )
    .expect("write checkpoint report");
    fs::write(
        &provenance,
        format!(
            "machine_id={}\nplatform={}\nplatform_equivalence={}\nanalysis_worktree_head={}\nbase_harness_head={}\nbase_manifest_sha256={}\nmac_base_manifest_sha256={}\nmac_record_commit=bbaaaf0ac4914398e7024dd137accbdc3932ecf5\ncandidate_universe_sha256={}\nnon_brotli_identity_list_sha256={}\nsubstrate=derived\nsubstrate_selector={}\nsnapshot={}\nsnapshot_files=100\ndeps_shape=read-only-symlink\nrepair=mode_a\nl2=0\nsafe_mono=per_site\nfork_engine=fork\nmemory_limit=batch0:8192-mib-control,batches1-7-and-recovery:uncapped\nquery_budget={}\nqueried={}\nrecovery_rows={}\nrecovery_shards={}\nrecovery_manifest_sha256s={}\nrecovery_wall_sum_s={:.3}\nmac_non_brotli_control=88-hard-unsat,own-assume-88,link-own-88\nmac_non_brotli_comparison=universal-record-per-exact-key-not-row-artifact-identity\nmac_brotli_completed={}\nmac_brotli_all112_attempt=timeout-zero-probe-rows\nbrotli_first_time_force_sat_keys={}\nbrotli_rows={}\nbatch_plan={}\nbatches={}\nbatch_wall_sum_s={:.3}\naggregation_input_policy=manifested-published-completed-only\nenvironment_event=mac-private-row-artifacts-not-transferred-no-attribution\nmigration_lesson=private-directory-data-is-not-transfer-durable\ntiming_comparison=forbidden-across-machines\n",
            contract.identity.machine_id,
            contract.identity.platform,
            platform_equivalence,
            super::orchestrate::git_sha(),
            P2_BASE_HARNESS_HEAD,
            contract.base_manifest_sha256,
            P2_BASE_MANIFEST_SHA256,
            P2_CANDIDATE_UNIVERSE_SHA256,
            P2_NON_BROTLI_IDENTITY_SHA256,
            std::env::var("CRAT_BOC1_SUBSTRATE")
                .unwrap_or_else(|_| "default-derived".to_owned()),
            contract.snapshot.display(),
            P2_QUERY_BUDGET,
            probes.len(),
            recovery_rows,
            recovery_stats.len(),
            recovery_manifests,
            recovery_wall_sum,
            P2_MAC_BROTLI_COMPLETED,
            first_time_sat_provenance,
            brotli_rows,
            P2_CHECKPOINT_BATCH_PLAN,
            ranges.len(),
            wall_sum,
        ),
    )
    .expect("write checkpoint provenance");
    write_sha256_manifest(
        &aggregate,
        &[
            classification,
            combined_probes,
            per_program,
            report,
            provenance,
        ],
        &aggregate_manifest,
    )
    .unwrap_or_else(|error| panic!("write aggregate manifest: {error}"));
    verify_sha256_manifest(&aggregate, &aggregate_manifest)
        .unwrap_or_else(|error| panic!("verify aggregate manifest: {error}"));
    println!(
        "S23P2AGG machine_id={} platform={} fields={} eligible=261 queried={} hard_unsat={} force_sat={} accepted_raw={} accepted_ref={} accepted_owning={} budget_not_queried={} own_assume_cores={} link_own_cores={}",
        contract.identity.machine_id,
        contract.identity.platform,
        final_records.len(),
        probes.len(),
        hard_unsat.len(),
        force_sat,
        accepted(SlotKind::Raw),
        accepted(SlotKind::Ref),
        accepted(SlotKind::Owning),
        bucket_counts
            .get(TerminalBucket::BudgetNotQueried.label())
            .copied()
            .unwrap_or(0),
        own_assume,
        link_own,
        );
}

/// Form a new full-population aggregate from the immutable accepted 200-row
/// aggregate plus the five completed 61-candidate shards. The predecessor is
/// verified and never rewritten.
#[test]
#[ignore = "P2 261-row completion aggregate; run after all five completion shards"]
fn s23_p2_completion_aggregate() {
    let contract = checkpoint_contract();
    let analysis_head = super::orchestrate::git_sha();
    let candidates = checkpoint_candidates(&contract.base);
    let selected = selected_checkpoint_candidates(&candidates);
    let completion_programs = completion_checkpoint_programs(&candidates)
        .unwrap_or_else(|error| panic!("P2 completion partition: {error}"));
    let candidate_slots = candidates
        .iter()
        .map(|candidate| {
            (
                (candidate.program.clone(), candidate.field_key.clone()),
                candidate.field_slot,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let eligible = candidates
        .iter()
        .filter(|candidate| candidate.discovery == DiscoveryClass::Eligible)
        .map(|candidate| (candidate.program.clone(), candidate.field_key.clone()))
        .collect::<BTreeSet<_>>();
    assert_eq!(eligible.len(), P2_QUERY_BUDGET + P2_COMPLETION_CANDIDATES);

    let predecessor = contract.batches.join("aggregate");
    let predecessor_manifest = predecessor.join("artifact-manifest.sha256");
    verify_sha256_manifest(&predecessor, &predecessor_manifest)
        .unwrap_or_else(|error| panic!("P2 completion STOP: predecessor manifest: {error}"));
            assert_eq!(
        sha256_file(&predecessor_manifest).expect("hash predecessor manifest"),
        P2_ACCEPTED_AGGREGATE_MANIFEST_SHA256,
        "P2 completion STOP: immutable accepted-200 aggregate identity mismatch"
            );
    let predecessor_provenance = parse_receipt(&predecessor.join("provenance.txt"))
        .unwrap_or_else(|error| panic!("P2 completion STOP: predecessor provenance: {error}"));
    for (field, expected) in [
        ("machine_id", contract.identity.machine_id.as_str()),
        ("platform", contract.identity.platform.as_str()),
        ("candidate_universe_sha256", P2_CANDIDATE_UNIVERSE_SHA256),
        ("query_budget", "200"),
        ("queried", "200"),
    ] {
            assert_eq!(
            predecessor_provenance.get(field).map(String::as_str),
            Some(expected),
            "P2 completion STOP: predecessor {field} identity mismatch"
            );
    }

    let aggregate = contract.batches.join("aggregate-261");
    let aggregate_manifest = aggregate.join("artifact-manifest.sha256");
    if aggregate_manifest.is_file() {
        verify_sha256_manifest(&aggregate, &aggregate_manifest)
            .unwrap_or_else(|error| panic!("completed 261 aggregate manifest: {error}"));
        let provenance = parse_receipt(&aggregate.join("provenance.txt"))
            .unwrap_or_else(|error| panic!("completed 261 aggregate provenance: {error}"));
        for (field, expected) in [
            ("machine_id", contract.identity.machine_id.as_str()),
            ("platform", contract.identity.platform.as_str()),
            ("analysis_head", analysis_head.as_str()),
            (
                "accepted_aggregate_manifest_sha256",
                P2_ACCEPTED_AGGREGATE_MANIFEST_SHA256,
            ),
            (
                "completion_identity_list_sha256",
                P2_COMPLETION_IDENTITY_SHA256,
            ),
            ("queried", "261"),
            ("solver_unknown", "0"),
        ] {
            assert_eq!(
                provenance.get(field).map(String::as_str),
                Some(expected),
                "completed 261 aggregate {field} drifted"
            );
        }
        println!(
            "S23P2FULLAGG machine_id={} platform={} status=verified-skip queried=261",
            contract.identity.machine_id, contract.identity.platform
            );
        return;
        }
    assert!(
        !aggregate.exists(),
        "P2 completion STOP: unmanifested partial aggregate exists at {}",
        aggregate.display()
        );

    let mut probes = BTreeMap::<(String, String), ProbeRecord>::new();
    for (program, row) in
        parse_combined_probe(&predecessor.join("combined-probes.tsv"), &contract.identity)
            .unwrap_or_else(|error| panic!("P2 completion STOP: predecessor probes: {error}"))
    {
        let identity = (program.clone(), row.field_key.clone());
        assert!(
            selected.contains(&identity),
            "P2 completion STOP: predecessor emitted unselected identity {identity:?}"
        );
        assert_eq!(
            candidate_slots.get(&identity).copied(),
            Some(row.field_slot),
            "P2 completion STOP: predecessor field-slot identity mismatch at {identity:?}"
        );
        assert!(
            matches!(row.force_result, ForceResult::Sat | ForceResult::Unsat),
            "P2 completion STOP: predecessor has non-result at {identity:?}"
        );
        assert!(
            probes.insert(identity.clone(), row).is_none(),
            "P2 completion STOP: predecessor duplicate at {identity:?}"
        );
    }
    assert_eq!(probes.len(), P2_QUERY_BUDGET);
    assert_eq!(
        probes.keys().cloned().collect::<BTreeSet<_>>(),
        selected,
        "P2 completion STOP: predecessor is not the exact accepted 200"
        );
    let predecessor_hard_unsat = probes
        .values()
        .filter(|row| row.force_result == ForceResult::Unsat)
        .collect::<Vec<_>>();
    assert_eq!(predecessor_hard_unsat.len(), 197);
        assert_eq!(
        probes
            .values()
            .filter(|row| row.force_result == ForceResult::Sat)
            .count(),
        3
        );
    for family in ["own-assume", "link-own"] {
            assert_eq!(
            predecessor_hard_unsat
                .iter()
                .filter(|row| row
                    .core_families
                    .iter()
                    .any(|candidate| candidate == family))
                .count(),
            197,
            "P2 completion STOP: predecessor {family} incidence drifted"
            );
        }

    let mut completion_identities = Vec::new();
    let mut shard_stats = Vec::new();
    for (program, keys) in &completion_programs {
        let shard_dir = contract.batches.join("completion-shards").join(program);
        let manifest = shard_dir.join("artifact-manifest.sha256");
        verify_sha256_manifest(&shard_dir, &manifest).unwrap_or_else(|error| {
            panic!(
                "P2 completion STOP: phase=aggregate-shard-manifest candidate={program}::<shard> detail={error}"
            )
        });
        let receipt = parse_receipt(&shard_dir.join("receipt.txt")).unwrap_or_else(|error| {
            panic!(
                "P2 completion STOP: phase=aggregate-shard-receipt candidate={program}::<shard> detail={error}"
            )
        });
        for (field, expected) in [
            ("analysis_head", analysis_head.as_str()),
            (
                "base_manifest_sha256",
                contract.base_manifest_sha256.as_str(),
            ),
            (
                "accepted_aggregate_manifest_sha256",
                P2_ACCEPTED_AGGREGATE_MANIFEST_SHA256,
            ),
        ] {
                assert_eq!(
                receipt.get(field).map(String::as_str),
                Some(expected),
                "P2 completion STOP: phase=aggregate-shard-identity candidate={program}::<shard> field={field}"
                );
            }
        let rows = parse_probe_for_program(&shard_dir.join("probes.tsv"), Some(program))
            .unwrap_or_else(|error| {
                panic!(
                    "P2 completion STOP: phase=aggregate-shard-probes candidate={program}::<shard> detail={error}"
                )
            });
        validate_completed_completion_shard(
            program,
            keys,
            &receipt,
            &rows,
            &contract.identity,
            &candidate_slots,
        )
        .unwrap_or_else(|error| {
            panic!(
                "P2 completion STOP: phase=aggregate-shard-validation candidate={program}::<shard> detail={error}"
            )
        });
        assert_eq!(
            read_target_keys(&shard_dir.join("targets.txt"))
                .unwrap_or_else(|error| panic!("completion targets {program}: {error}")),
            *keys,
            "P2 completion STOP: phase=aggregate-shard-targets candidate={program}::<shard>"
        );
        assert_eq!(
            parse_probe_for_program(&shard_dir.join("partial-probes.tsv"), Some(program))
                .unwrap_or_else(|error| panic!("completion checkpoint {program}: {error}")),
            rows,
            "P2 completion STOP: phase=aggregate-shard-checkpoint candidate={program}::<shard>"
        );
        assert!(
            !probe_checkpoint_temp_path(&shard_dir.join("partial-probes.tsv")).exists(),
            "P2 completion STOP: phase=aggregate-shard-checkpoint candidate={program}::<temporary>"
        );
        for row in rows {
            let identity = (program.clone(), row.field_key.clone());
            completion_identities.push(identity.clone());
            assert!(
                probes.insert(identity.clone(), row).is_none(),
                "P2 completion STOP: phase=aggregate-union candidate={identity:?} overlap"
            );
        }
        shard_stats.push((
            program.clone(),
            keys.len(),
            receipt["hard_unsat"]
                .parse::<usize>()
                .expect("completion hard-UNSAT count"),
            receipt["force_sat"]
                .parse::<usize>()
                .expect("completion force-SAT count"),
            receipt["wall_s"].parse::<f64>().expect("completion wall"),
            receipt["wall_s_per_candidate"]
                .parse::<f64>()
                .expect("completion wall per candidate"),
            receipt["peak_rss_kb"]
                .parse::<u64>()
                .expect("completion peak RSS"),
            sha256_file(&manifest).expect("hash completion manifest"),
        ));
    }
    validate_exact_candidate_partition(
        &eligible.iter().cloned().collect::<Vec<_>>(),
        &selected.iter().cloned().collect::<Vec<_>>(),
        &completion_identities,
    )
    .unwrap_or_else(|error| {
        panic!("P2 completion STOP: phase=aggregate-union candidate=<partition> detail={error}")
    });
    assert_eq!(probes.len(), 261);
    assert_eq!(probes.keys().cloned().collect::<BTreeSet<_>>(), eligible);

    let mut final_records = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        let identity = (candidate.program.clone(), candidate.field_key.clone());
        let probe = probes.get(&identity);
        let (force_result, accepted_kind, core_families) = match probe {
            Some(probe) => (
                probe.force_result,
                Some(probe.accepted_kind),
                probe.core_families.clone(),
            ),
            None => (ForceResult::NotQueried, None, Vec::new()),
        };
        final_records.push(FinalRecord {
            bucket: terminal_bucket(candidate.discovery, force_result, accepted_kind),
            candidate,
            accepted_kind,
            force_result,
            core_families,
        });
    }
    let mut bucket_counts = BTreeMap::new();
    for record in &final_records {
        *bucket_counts.entry(record.bucket.label()).or_insert(0usize) += 1;
    }
    assert_eq!(bucket_counts.values().sum::<usize>(), final_records.len());
    assert_eq!(
        bucket_counts
            .get(TerminalBucket::BudgetNotQueried.label())
            .copied()
            .unwrap_or(0),
        0
    );
    assert_eq!(
        bucket_counts
            .get(TerminalBucket::SolverUnknown.label())
            .copied()
            .unwrap_or(0),
        0,
        "P2 completion STOP: phase=aggregate-classification candidate=<unknown>"
    );
    let hard_unsat = final_records
        .iter()
        .filter(|record| record.force_result == ForceResult::Unsat)
        .collect::<Vec<_>>();
    let force_sat = final_records
        .iter()
        .filter(|record| record.force_result == ForceResult::Sat)
        .count();
    let own_assume = hard_unsat
        .iter()
        .filter(|record| {
            record
                .core_families
                .iter()
                .any(|family| family == "own-assume")
        })
        .count();
    let link_own = hard_unsat
        .iter()
        .filter(|record| {
            record
                .core_families
        .iter()
                .any(|family| family == "link-own")
        })
        .count();
    let own_assume_missing = hard_unsat.len() - own_assume;
    let link_own_missing = hard_unsat.len() - link_own;
    let accepted = |kind| {
        final_records
        .iter()
            .filter(|record| record.accepted_kind == Some(kind))
            .count()
    };
    let completion_hard_unsat = shard_stats
        .iter()
        .map(|(_, _, count, _, _, _, _, _)| count)
        .sum::<usize>();
    let completion_force_sat = shard_stats
        .iter()
        .map(|(_, _, _, count, _, _, _, _)| count)
        .sum::<usize>();
    assert_eq!(
        hard_unsat.len() + force_sat,
        P2_QUERY_BUDGET + P2_COMPLETION_CANDIDATES
    );
    assert_eq!(hard_unsat.len(), 197 + completion_hard_unsat);
    assert_eq!(force_sat, 3 + completion_force_sat);

    fs::create_dir_all(&aggregate).expect("create 261 aggregate directory");
    let classification = aggregate.join("classification.tsv");
    let combined_probes = aggregate.join("combined-probes.tsv");
    let per_program = aggregate.join("per-program.tsv");
    let report = aggregate.join("report.md");
    let provenance = aggregate.join("provenance.txt");
    fs::write(
        &classification,
        render_final_tsv(&final_records, &contract.identity),
    )
    .expect("write 261 classification");
    let mut combined = String::from(
        "platform\tmachine_id\tprogram\tfield_key\tfield_slot\taccepted_kind\tforce_result\tcore_families\tcore_labels\n",
    );
    for ((program, _), probe) in &probes {
        let force = match probe.force_result {
            ForceResult::Sat => "sat",
            ForceResult::Unsat => "unsat",
            ForceResult::Unknown => "unknown",
            ForceResult::NotQueried => "not-queried",
        };
        combined.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            contract.identity.platform,
            contract.identity.machine_id,
            program,
            probe.field_key,
            probe.field_slot,
            kind_label(probe.accepted_kind),
            force,
            probe.core_families.join("|"),
            probe.core_labels.join("|")
        ));
    }
    fs::write(&combined_probes, combined).expect("write 261 combined probes");
    let mut per_program_rows = String::from(
        "platform\tmachine_id\tprogram\tscreened\teligible\tno_owned_capable_store\tstore_blocked\tqueried\thard_unsat\tforce_sat\tsolver_unknown\tbudget_not_queried\taccepted_raw\taccepted_ref\taccepted_owning\n",
    );
    for corpus_program in super::CORPUS {
        let rows = final_records
            .iter()
            .filter(|record| record.candidate.program == corpus_program.name)
            .collect::<Vec<_>>();
        let count_discovery = |class| {
            rows.iter()
                .filter(|record| record.candidate.discovery == class)
                .count()
        };
        let count_bucket = |bucket| rows.iter().filter(|record| record.bucket == bucket).count();
        let count_kind = |kind| {
            rows.iter()
                .filter(|record| record.accepted_kind == Some(kind))
                .count()
        };
        per_program_rows.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            contract.identity.platform,
            contract.identity.machine_id,
            corpus_program.name,
            rows.len(),
            count_discovery(DiscoveryClass::Eligible),
            count_discovery(DiscoveryClass::NoOwnedCapableStore),
            count_discovery(DiscoveryClass::StoreBlocked),
            rows.iter()
                .filter(|record| record.force_result != ForceResult::NotQueried)
                .count(),
            count_bucket(TerminalBucket::HardUnsat),
            rows.iter()
                .filter(|record| record.force_result == ForceResult::Sat)
                .count(),
            count_bucket(TerminalBucket::SolverUnknown),
            count_bucket(TerminalBucket::BudgetNotQueried),
            count_kind(SlotKind::Raw),
            count_kind(SlotKind::Ref),
            count_kind(SlotKind::Owning),
        ));
    }
    fs::write(&per_program, per_program_rows).expect("write 261 per-program aggregate");

    let completion_table = shard_stats
        .iter()
        .map(|(program, candidates, unsat, sat, wall, per_candidate, peak, _)| {
            format!(
                "| {} | {} | {program} | {candidates} | {unsat} | {sat} | {wall:.3} | {per_candidate:.6} | {peak} |",
                contract.identity.platform, contract.identity.machine_id,
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let completion_wall_sum = shard_stats
        .iter()
        .map(|(_, _, _, _, wall, _, _, _)| wall)
        .sum::<f64>();
    let completion_manifests = shard_stats
        .iter()
        .map(|(program, _, _, _, _, _, _, digest)| format!("{program}:{digest}"))
        .collect::<Vec<_>>()
        .join(",");
    fs::write(
        &report,
        format!(
            "# P2 / S2-3 complete 261-candidate diagnosis\n\n- Measurement identity: machine `{}`, platform `{}`. Every count, wall time, and peak RSS below belongs to this machine; timings are not compared across machines.\n- Immutable predecessor: **200 completed** rows, manifest `{}`. Its **61 budget-not-queried** state is superseded by the five completion shards and is retained as predecessor provenance.\n- Full eligible partition: **261 completed = {} hard-UNSAT + {} force-own SAT + 0 Unknown + 0 budget-not-queried**.\n- Completion-only classes: **61 completed = {} hard-UNSAT + {} force-own SAT + 0 Unknown**.\n- Hard-UNSAT core-family incidence: `own-assume` **{}/{}** (missing **{}**), `link-own` **{}/{}** (missing **{}**). SAT rows have no UNSAT core and are excluded from these denominators.\n- Ordinary accepted kinds among 261 queried candidates: Raw **{}**, Ref **{}**, Owning **{}**.\n- Completion-shard Linux-local wall sum: **{:.3}s**. Each shard ran sequentially with uncapped RAM/CPU and an exact 14,400-second wall liveness bound.\n\n## Completion shards\n\n| platform | machine id | program | candidates | hard-UNSAT | force-SAT | wall s | wall s / candidate | peak RSS KiB |\n|---|---|---|---:|---:|---:|---:|---:|---:|\n{}\n\nOnly the verified immutable 200-row aggregate and five completed, SHA-256-manifested `data=true` shards feed this aggregate. Atomic partial checkpoints remain `data=false` provenance and are excluded. Production analysis code remained read-only.\n",
            contract.identity.machine_id,
            contract.identity.platform,
            P2_ACCEPTED_AGGREGATE_MANIFEST_SHA256,
            hard_unsat.len(),
            force_sat,
            completion_hard_unsat,
            completion_force_sat,
            own_assume,
            hard_unsat.len(),
            own_assume_missing,
            link_own,
            hard_unsat.len(),
            link_own_missing,
            accepted(SlotKind::Raw),
            accepted(SlotKind::Ref),
            accepted(SlotKind::Owning),
            completion_wall_sum,
            completion_table,
        ),
    )
    .expect("write 261 report");
    fs::write(
        &provenance,
        format!(
            "machine_id={}\nplatform={}\nanalysis_head={}\nbase_harness_head={}\nbase_manifest_sha256={}\ncandidate_universe_sha256={}\naccepted_aggregate_manifest_sha256={}\ncompletion_identity_list_sha256={}\nsubstrate=derived\nsnapshot={}\nsnapshot_files=100\ndeps_shape=read-only-symlink\nrepair=mode_a\nl2=0\nsafe_mono=per_site\nfork_engine=fork\nmemory_limit=uncapped\nwall_bound_kind=liveness\nwall_cap_s=14400\npredecessor_queried=200\npredecessor_budget_not_queried=61\npredecessor_state=superseded-not-erased\ncompletion_candidates=61\ncompletion_shards=5\ncompletion_shard_order=quadtree,urlparser,rgba,lil,lodepng\ncompletion_manifest_sha256s={}\ncompletion_wall_sum_s={:.3}\nqueried=261\nhard_unsat={}\nforce_sat={}\nsolver_unknown=0\nbudget_not_queried=0\nown_assume_core_incidence={}\nlink_own_core_incidence={}\nown_assume_core_missing={}\nlink_own_core_missing={}\naccepted_raw={}\naccepted_ref={}\naccepted_owning={}\naggregation_input_policy=manifested-published-completed-data-true-only\ntiming_comparison=forbidden-across-machines\n",
            contract.identity.machine_id,
            contract.identity.platform,
            analysis_head,
            P2_BASE_HARNESS_HEAD,
            contract.base_manifest_sha256,
            P2_CANDIDATE_UNIVERSE_SHA256,
            P2_ACCEPTED_AGGREGATE_MANIFEST_SHA256,
            P2_COMPLETION_IDENTITY_SHA256,
            contract.snapshot.display(),
            completion_manifests,
            completion_wall_sum,
            hard_unsat.len(),
            force_sat,
            own_assume,
            link_own,
            own_assume_missing,
            link_own_missing,
            accepted(SlotKind::Raw),
            accepted(SlotKind::Ref),
            accepted(SlotKind::Owning),
        ),
    )
    .expect("write 261 provenance");
    write_sha256_manifest(
        &aggregate,
        &[
            classification,
            combined_probes,
            per_program,
            report,
            provenance,
        ],
        &aggregate_manifest,
    )
    .unwrap_or_else(|error| panic!("write 261 aggregate manifest: {error}"));
    verify_sha256_manifest(&aggregate, &aggregate_manifest)
        .unwrap_or_else(|error| panic!("verify 261 aggregate manifest: {error}"));
    println!(
        "S23P2FULLAGG machine_id={} platform={} queried=261 hard_unsat={} force_sat={} solver_unknown=0 budget_not_queried=0 own_assume_cores={} link_own_cores={} own_assume_missing={} link_own_missing={}",
        contract.identity.machine_id,
        contract.identity.platform,
        hard_unsat.len(),
        force_sat,
        own_assume,
        link_own,
        own_assume_missing,
        link_own_missing,
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checkpoint_batches_preserve_completed_prefix_and_cover_112_once() {
        assert_eq!(
            std::any::TypeId::of::<std::os::raw::c_char>(),
            std::any::TypeId::of::<i8>(),
            "named platform risk: c_char must be signed on the Linux control host"
        );
        assert_eq!(
            super::super::orchestrate::memory_limit_kb(Some("uncapped")),
            Ok(None)
        );
        assert_eq!(
            super::super::orchestrate::memory_limit_kb(Some("8192")),
            Ok(Some(8192 * 1024))
        );
        assert!(super::super::orchestrate::memory_limit_kb(Some("0")).is_err());

        let identity = MeasurementIdentity::parse("lambda7", "linux-x86_64")
            .expect("valid measurement identity");
        assert_eq!(identity.machine_id, "lambda7");
        assert_eq!(identity.platform, "linux-x86_64");
        assert!(MeasurementIdentity::parse("", "linux-x86_64").is_err());
        assert!(MeasurementIdentity::parse("lambda7", "linux\tx86_64").is_err());

        assert_eq!(checkpoint_batch_timeout_s(None), Ok(14400));
        assert_eq!(checkpoint_batch_timeout_s(Some("14400")), Ok(14400));
        assert!(checkpoint_batch_timeout_s(Some("7200")).is_err());
        assert!(checkpoint_batch_timeout_s(Some("3600")).is_err());
        assert_eq!(checkpoint_data_value("ok"), "true");
        for status in ["timeout", "oom-kill", "panic", "crash", "no-output"] {
            assert_eq!(checkpoint_data_value(status), "false");
        }

        let witness_root = std::env::temp_dir().join(format!(
            "crat-s23-checkpoint-control-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("control clock")
                .as_nanos()
        ));
        fs::create_dir(&witness_root).expect("create checkpoint control directory");
        let witness_path = witness_root.join("partial-probes.tsv");
        let witness_key = "fixture::H0::field0@d0";
        let witness_records = vec![ProbeRecord {
            field_key: witness_key.to_owned(),
            field_slot: 0,
            accepted_kind: SlotKind::Raw,
            force_result: ForceResult::Unsat,
            core_families: vec!["own-assume".to_owned(), "link-own".to_owned()],
            core_labels: Vec::new(),
        }];
        write_probe_checkpoint(&witness_path, "fixture", &witness_records)
            .expect("write positive-control checkpoint");
        assert!(
            !probe_checkpoint_temp_path(&witness_path).exists(),
            "atomic checkpoint publish must not leave its temporary file"
        );
        let marker = checkpoint_phase_line(
            "checkpoint-written",
            Some(witness_key),
            1,
            Duration::from_millis(1250),
        );
        eprintln!("{marker}");
        eprintln!(
            "S23CHECKPOINT data=false path={} rows=1",
            witness_path.display()
        );
        let progress = parse_checkpoint_phase(&marker).expect("parse checkpoint marker");
        assert_eq!(progress.phase, "checkpoint-written");
        assert_eq!(progress.candidate.as_deref(), Some(witness_key));
        assert_eq!(progress.completed, 1);
        assert_eq!(progress.elapsed_s, "1.250");
        assert_eq!(
            parse_probe(&witness_path).expect("parse positive-control checkpoint"),
            witness_records
        );
        assert!(
            parse_probe_for_program(&witness_path, Some("wrong-program")).is_err(),
            "program-column identity mismatch must be rejected"
        );
        fs::remove_file(&witness_path).expect("remove checkpoint control artifact");
        fs::remove_dir(&witness_root).expect("remove checkpoint control directory");

        let ranges = checkpoint_batch_ranges(112).expect("valid checkpoint plan");
        assert_eq!(
            ranges
                .iter()
                .map(|range| range.end - range.start)
                .collect::<Vec<_>>(),
            vec![24, 24, 12, 12, 12, 12, 12, 4]
        );
        assert_eq!(ranges.first().map(|range| range.start), Some(0));
        assert_eq!(ranges.last().map(|range| range.end), Some(112));
        assert_eq!(ranges.len(), 8);
        assert_eq!(ranges[0], 0..24);
        assert_eq!(ranges[1], 24..48);
        for pair in ranges.windows(2) {
            assert_eq!(pair[0].end, pair[1].start);
        }
    }

    #[test]
    fn checkpoint_batch_plan_rejects_empty_inputs() {
        assert!(checkpoint_batch_ranges(0).is_err());
        assert!(checkpoint_batch_ranges(111).is_err());
    }

    #[test]
    fn non_brotli_recovery_partition_and_completed_data_gate() {
        assert_eq!(
            P2_NON_BROTLI_SELECTED,
            [
                ("avl", 2),
                ("binn", 4),
                ("bst", 2),
                ("buffer", 2),
                ("bzip2", 23),
                ("genann", 3),
                ("heman", 3),
                ("ht", 6),
                ("json.h", 15),
                ("libcsv", 1),
                ("libtree", 9),
                ("libzahl", 1),
                ("lil", 17),
            ]
        );
        assert_eq!(
            P2_NON_BROTLI_SELECTED
                .iter()
                .map(|(_, count)| count)
                .sum::<usize>(),
            88
        );

        let identity =
            MeasurementIdentity::parse("lambda7", "linux-x86_64").expect("valid recovery identity");
        let key = "fixture::H0::field0@d0".to_owned();
        let expected = vec![key.clone()];
        let rows = vec![ProbeRecord {
            field_key: key,
            field_slot: 0,
            accepted_kind: SlotKind::Raw,
            force_result: ForceResult::Unsat,
            core_families: vec!["link-own".to_owned(), "own-assume".to_owned()],
            core_labels: Vec::new(),
        }];
        let candidate_slots =
            BTreeMap::from([(("fixture".to_owned(), expected[0].clone()), 0usize)]);
        let mut receipt = BTreeMap::from([
            ("machine_id".to_owned(), "lambda7".to_owned()),
            ("platform".to_owned(), "linux-x86_64".to_owned()),
            ("program".to_owned(), "fixture".to_owned()),
            ("status".to_owned(), "ok".to_owned()),
            ("worker_status".to_owned(), "ok".to_owned()),
            ("data".to_owned(), "true".to_owned()),
            ("checkpoint_data".to_owned(), "false".to_owned()),
            ("memory_limit".to_owned(), "uncapped".to_owned()),
            ("wall_bound_kind".to_owned(), "liveness".to_owned()),
            ("wall_cap_s".to_owned(), "14400".to_owned()),
            ("planned_targets".to_owned(), "1".to_owned()),
            ("queried".to_owned(), "1".to_owned()),
            ("checkpoint_rows".to_owned(), "1".to_owned()),
            ("last_phase".to_owned(), "complete".to_owned()),
            (
                "candidate_universe_sha256".to_owned(),
                P2_CANDIDATE_UNIVERSE_SHA256.to_owned(),
            ),
            (
                "non_brotli_identity_list_sha256".to_owned(),
                P2_NON_BROTLI_IDENTITY_SHA256.to_owned(),
            ),
            (
                "mac_comparison_kind".to_owned(),
                "universal-record-per-exact-key".to_owned(),
            ),
            ("mac_expected_verdict".to_owned(), "unsat".to_owned()),
            (
                "mac_expected_core_families".to_owned(),
                "own-assume|link-own".to_owned(),
            ),
            ("mac_comparison".to_owned(), "match".to_owned()),
            ("validation_error".to_owned(), "none".to_owned()),
            ("hard_unsat".to_owned(), "1".to_owned()),
            ("force_sat".to_owned(), "0".to_owned()),
            ("solver_unknown".to_owned(), "0".to_owned()),
        ]);
        let mut incomplete = receipt.clone();
        incomplete.insert("status".to_owned(), "timeout".to_owned());
        incomplete.insert("data".to_owned(), "false".to_owned());
        incomplete.insert("queried".to_owned(), "0".to_owned());
        incomplete.insert("checkpoint_rows".to_owned(), "0".to_owned());
        incomplete.insert("last_phase".to_owned(), "force-own-start".to_owned());
        let rejected = validate_completed_recovery_shard(
            "fixture",
            &expected,
            &incomplete,
            &[],
            &identity,
            &candidate_slots,
        );
        eprintln!(
            "S23RECOVERYGATE fixture=incomplete data=false result={}",
            if rejected.is_err() {
                "rejected"
            } else {
                "accepted"
            }
        );
        assert!(rejected.is_err(), "incomplete fixture must be rejected");

        let accepted = validate_completed_recovery_shard(
            "fixture",
            &expected,
            &receipt,
            &rows,
            &identity,
            &candidate_slots,
        );
        eprintln!(
            "S23RECOVERYGATE fixture=complete data=true result={}",
            if accepted.is_ok() {
                "accepted"
            } else {
                "rejected"
            }
        );
        assert_eq!(accepted, Ok(()));

        let mut sat_rows = rows.clone();
        sat_rows[0].force_result = ForceResult::Sat;
        assert!(
            validate_completed_recovery_shard(
                "fixture",
                &expected,
                &receipt,
                &sat_rows,
                &identity,
                &candidate_slots,
            )
            .is_err_and(|error| error.starts_with("platform deviation"))
        );

        let mut missing_family_rows = rows.clone();
        missing_family_rows[0]
            .core_families
            .retain(|family| family != "link-own");
        assert!(
            validate_completed_recovery_shard(
                "fixture",
                &expected,
                &receipt,
                &missing_family_rows,
                &identity,
                &candidate_slots,
            )
            .is_err_and(|error| error.starts_with("platform deviation"))
        );

        let mut wrong_slot_rows = rows.clone();
        wrong_slot_rows[0].field_slot = 1;
        assert!(
            validate_completed_recovery_shard(
                "fixture",
                &expected,
                &receipt,
                &wrong_slot_rows,
                &identity,
                &candidate_slots,
            )
            .is_err_and(|error| error.starts_with("identity mismatch"))
        );

        receipt.insert("data".to_owned(), "false".to_owned());
        assert!(
            validate_completed_recovery_shard(
                "fixture",
                &expected,
                &receipt,
                &rows,
                &identity,
                &candidate_slots,
            )
            .is_err()
        );
    }

    #[test]
    fn brotli_mac_overlap_gate_rejects_only_measured_prefix() {
        let keys = (0..25)
            .map(|index| format!("key-{index:02}"))
            .collect::<Vec<_>>();
        assert_eq!(
            validate_brotli_mac_overlap(&keys, &[keys[24].clone()]),
            Ok(())
        );
        let deviation = validate_brotli_mac_overlap(&keys, &[keys[3].clone()])
            .expect_err("SAT inside the mac-measured prefix must stop");
        assert!(deviation.contains("platform deviation"));
        assert!(deviation.contains("key-03"));
    }

    #[test]
    fn p2_first_failure_partition_and_positive_owning_control() {
        let cases = [
            (
                DiscoveryClass::NoOwnedCapableStore,
                ForceResult::NotQueried,
                None,
                TerminalBucket::NoOwnedCapableStore,
            ),
            (
                DiscoveryClass::StoreBlocked,
                ForceResult::NotQueried,
                None,
                TerminalBucket::StoreBlocked,
            ),
            (
                DiscoveryClass::Eligible,
                ForceResult::Unsat,
                Some(SlotKind::Raw),
                TerminalBucket::HardUnsat,
            ),
            (
                DiscoveryClass::Eligible,
                ForceResult::Unknown,
                Some(SlotKind::Raw),
                TerminalBucket::SolverUnknown,
            ),
            (
                DiscoveryClass::Eligible,
                ForceResult::NotQueried,
                None,
                TerminalBucket::BudgetNotQueried,
            ),
            (
                DiscoveryClass::Eligible,
                ForceResult::Sat,
                Some(SlotKind::Ref),
                TerminalBucket::ForceOwnSatNotSelected,
            ),
            (
                DiscoveryClass::Eligible,
                ForceResult::Sat,
                Some(SlotKind::Owning),
                TerminalBucket::OwningAccepted,
            ),
        ];
        for (discovery, force, accepted, expected) in cases {
            assert_eq!(terminal_bucket(discovery, force, accepted), expected);
        }
    }

    #[test]
    fn p2_discovery_classifies_mixed_stores_at_the_first_blocker() {
        assert_eq!(classify_field(0, 0, 0), DiscoveryClass::NoOwnedCapableStore);
        assert_eq!(classify_field(2, 1, 0), DiscoveryClass::StoreBlocked);
        assert_eq!(classify_field(2, 0, 1), DiscoveryClass::StoreBlocked);
        assert_eq!(classify_field(2, 0, 0), DiscoveryClass::Eligible);
    }

    #[test]
    fn p2_completion_partition_identity_gate_is_two_sided() {
        assert_eq!(
            P2_COMPLETION_PROGRAMS
                .iter()
                .map(|(program, _)| *program)
                .collect::<Vec<_>>()
                .join(","),
            P2_COMPLETION_ORDER
        );
        assert_eq!(
            P2_COMPLETION_PROGRAMS
                .iter()
                .map(|(_, count)| count)
                .sum::<usize>(),
            P2_COMPLETION_CANDIDATES
        );
        let id = |key: &str| ("fixture".to_owned(), key.to_owned());
        let universe = vec![id("a"), id("b"), id("c")];
        let completed = vec![id("a"), id("b")];
        let completion = vec![id("c")];

        assert_eq!(
            validate_exact_candidate_partition(&universe, &completed, &completion),
            Ok(())
        );
        assert!(
            validate_exact_candidate_partition(&universe, &completed, &[])
                .is_err_and(|error| error.contains("missing"))
        );
        assert!(
            validate_exact_candidate_partition(&universe, &completed, &[id("b"), id("c")])
                .is_err_and(|error| error.contains("overlap"))
        );
        assert!(
            validate_exact_candidate_partition(&universe, &completed, &[id("c"), id("c")])
                .is_err_and(|error| error.contains("duplicate"))
        );
    }

    #[test]
    fn p2_completion_completed_data_gate_is_two_sided() {
        let identity = MeasurementIdentity::parse("lambda7", "linux-x86_64")
            .expect("valid completion identity");
        let key = "fixture::H0::field0@d0".to_owned();
        let expected = vec![key.clone()];
        let rows = vec![ProbeRecord {
            field_key: key.clone(),
            field_slot: 0,
            accepted_kind: SlotKind::Raw,
            force_result: ForceResult::Sat,
            core_families: Vec::new(),
            core_labels: Vec::new(),
        }];
        let candidate_slots = BTreeMap::from([(("fixture".to_owned(), key), 0usize)]);
        let receipt = BTreeMap::from([
            ("machine_id".to_owned(), "lambda7".to_owned()),
            ("platform".to_owned(), "linux-x86_64".to_owned()),
            ("program".to_owned(), "fixture".to_owned()),
            ("status".to_owned(), "ok".to_owned()),
            ("worker_status".to_owned(), "ok".to_owned()),
            ("data".to_owned(), "true".to_owned()),
            ("checkpoint_data".to_owned(), "false".to_owned()),
            ("memory_limit".to_owned(), "uncapped".to_owned()),
            ("wall_bound_kind".to_owned(), "liveness".to_owned()),
            ("wall_cap_s".to_owned(), "14400".to_owned()),
            ("planned_targets".to_owned(), "1".to_owned()),
            ("queried".to_owned(), "1".to_owned()),
            ("checkpoint_rows".to_owned(), "1".to_owned()),
            ("last_phase".to_owned(), "complete".to_owned()),
            ("hard_unsat".to_owned(), "0".to_owned()),
            ("force_sat".to_owned(), "1".to_owned()),
            ("solver_unknown".to_owned(), "0".to_owned()),
            ("validation_error".to_owned(), "none".to_owned()),
            (
                "candidate_universe_sha256".to_owned(),
                P2_CANDIDATE_UNIVERSE_SHA256.to_owned(),
            ),
            (
                "completion_identity_list_sha256".to_owned(),
                P2_COMPLETION_IDENTITY_SHA256.to_owned(),
            ),
            (
                "accepted_aggregate_manifest_sha256".to_owned(),
                P2_ACCEPTED_AGGREGATE_MANIFEST_SHA256.to_owned(),
            ),
        ]);

        let mut incomplete = receipt.clone();
        incomplete.insert("status".to_owned(), "timeout".to_owned());
        incomplete.insert("data".to_owned(), "false".to_owned());
        incomplete.insert("queried".to_owned(), "0".to_owned());
        incomplete.insert("checkpoint_rows".to_owned(), "0".to_owned());
        incomplete.insert("last_phase".to_owned(), "force-own-start".to_owned());
        assert!(
            validate_completed_completion_shard(
                "fixture",
                &expected,
                &incomplete,
                &[],
                &identity,
                &candidate_slots,
            )
            .is_err(),
            "incomplete data=false fixture must be rejected"
        );

        assert_eq!(
            validate_completed_completion_shard(
                "fixture",
                &expected,
                &receipt,
                &rows,
                &identity,
                &candidate_slots,
            ),
            Ok(())
        );

        let mut unknown_rows = rows;
        unknown_rows[0].force_result = ForceResult::Unknown;
        assert_eq!(
            completion_row_failure_candidate(
                "fixture",
                &expected,
                &unknown_rows,
                &candidate_slots,
            ),
            expected[0]
        );
        assert!(
            validate_completed_completion_shard(
                "fixture",
                &expected,
                &receipt,
                &unknown_rows,
                &identity,
                &candidate_slots,
            )
            .is_err_and(|error| error.contains("Unknown"))
        );
    }
}
