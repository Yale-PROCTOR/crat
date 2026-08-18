//! Test-only P2/S2-3 field-ownership diagnosis on the substrate of record.
//!
//! The corpus path is deliberately two-phase: discovery writes the derived
//! field/store population before any BO solve, then the probe phase spends a
//! capped number of incremental tracked queries only on owning-capable fields.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    ops::Range,
    path::{Path, PathBuf},
    process::Command,
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

pub(super) fn run_probe_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
    let started = Instant::now();
    let program_name = std::env::var("CRAT_BOC1_NAME").expect("probe requires program name");
    let targets_path =
        std::env::var("CRAT_S23_TARGET_KEYS").expect("probe requires CRAT_S23_TARGET_KEYS");
    let probe_path =
        std::env::var("CRAT_S23_PROBE_ARTIFACT").expect("probe requires artifact path");
    let targets =
        read_target_keys(Path::new(&targets_path)).unwrap_or_else(|error| panic!("{error}"));
    assert!(
        !targets.is_empty(),
        "probe worker requires nonempty targets"
    );

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

    let mut records = Vec::with_capacity(targets.len());
    for key in targets {
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
            field_key: key,
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
    }
    write_probe(Path::new(&probe_path), &program_name, &records)
        .unwrap_or_else(|error| panic!("{error}"));

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

fn checkpoint_batch_ranges(total: usize, batch_size: usize) -> Result<Vec<Range<usize>>, String> {
    if total == 0 {
        return Err("checkpoint plan requires a nonempty candidate set".to_owned());
    }
    if batch_size == 0 {
        return Err("checkpoint batch size must be positive".to_owned());
    }
    Ok((0..total)
        .step_by(batch_size)
        .map(|start| start..(start + batch_size).min(total))
        .collect())
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

fn render_final_tsv(records: &[FinalRecord]) -> String {
    let mut out = String::from(
        "program\tfield_key\tfield_slot\tdiscovery_class\tresolved_stores\tblocked_address_of\tblocked_unresolved\taccepted_kind\tforce_result\tterminal_bucket\tcore_families\n",
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
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
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
        env_usize("CRAT_BOC1_MEM_MB", 8192),
        8192,
        "P2 uses the standing default cap; no high-cap run is authorized"
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
        render_final_tsv(&final_records),
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
         - Screened depth-0 pointer-field universe: **{}**.\n\
         - Re-derived eligible owning-store candidates: **{}** (historical raw-form 155 is context only, not inherited).\n\
         - Targeted tracked-query budget: **{}**; queried **{}**; budget-not-queried **{}**.\n\
         - Hard-UNSAT: **{}**; cores containing `own-assume`: **{}**.\n\
         - Force-own SAT: **{}**; Owning in the accepted ordinary model: **{}**.\n\
         - Probe wall sum: **{:.3}s** (programs serialized); default memory cap: **8192 MiB**.\n\
         - Terminal counts: `{}`.\n\
         - Core-family incidence (raw tracked cores; families are incidence, not necessity): `{}`.\n\n\
         ## Deterministic first witnesses\n\n{}\n\
         ## Controls and scope\n\n\
         Discovery completed and the combined candidate/store artifacts were written before any BO solve. The classifier unit test exercises every terminal bucket, including a positive synthetic `Owning accepted` control. A zero bucket is interpreted only against the nonempty screened/eligible populations above. Production analysis code was read-only.\n",
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
        "analysis_worktree_head={}\nsubstrate=derived\nsubstrate_selector={}\nsnapshot={}\nsnapshot_files=100\ndeps_shape=read-only-symlink\nrepair=mode_a\nl2=0\nsafe_mono=per_site\nfork_engine=fork\nmem_cap_mib=8192\nquery_budget={}\nqueried={}\nprobe_wall_sum_s={:.3}\nprobe_peak_rss_kb={:?}\n",
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
        "S23P2 fields={} eligible={} queried={} hard_unsat={} own_assume_cores={} force_sat={} owning_accepted={} budget_not_queried={}",
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

struct CheckpointContract {
    corpus_link: PathBuf,
    snapshot: PathBuf,
    base: PathBuf,
    batches: PathBuf,
}

fn checkpoint_contract() -> CheckpointContract {
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
        env_usize("CRAT_BOC1_MEM_MB", 8192),
        8192,
        "checkpoint probes retain the standing default memory cap"
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
    assert_eq!(
        sha256_file(&base_manifest).expect("hash base manifest"),
        P2_BASE_MANIFEST_SHA256,
        "preserved P2 manifest identity drifted"
    );
    verify_sha256_manifest(&base, &base_manifest)
        .unwrap_or_else(|error| panic!("preserved P2 artifacts failed re-verification: {error}"));
    assert_eq!(
        sha256_file(&base.join("candidate-universe.tsv")).expect("hash candidate universe"),
        P2_CANDIDATE_UNIVERSE_SHA256,
        "candidate universe identity drifted"
    );
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

fn insert_probe_artifact(
    program: &str,
    path: &Path,
    candidates: &BTreeMap<(String, String), usize>,
    selected: &BTreeSet<(String, String)>,
    probes: &mut BTreeMap<(String, String), ProbeRecord>,
) -> Result<usize, String> {
    let rows = parse_probe(path)?;
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
#[ignore = "P2 brotli checkpoint; run one machine-quiet batch explicitly"]
fn s23_p2_brotli_checkpoint() {
    let contract = checkpoint_contract();
    assert_eq!(
        std::env::var("CRAT_S23_MACHINE_QUIET").as_deref(),
        Ok("verified"),
        "each batch requires a fresh external machine-quiet check"
    );
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
    let batch_size = env_usize("CRAT_S23_BATCH_SIZE", 24);
    assert!(
        (20..=30).contains(&batch_size),
        "initial checkpoint size must stay within the authorized 20–30 range"
    );
    let ranges = checkpoint_batch_ranges(brotli.len(), batch_size)
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
            "S23P2BATCH batch={} status=verified-skip candidates={}",
            batch_index,
            range.end - range.start
        );
        return;
    }
    assert!(
        !batch_dir.exists(),
        "P2 STOP: unmanifested partial batch exists at {}; preserve it for inspection",
        batch_dir.display()
    );
    fs::create_dir_all(&batch_dir).expect("create batch directory");

    let targets = batch_dir.join("targets.txt");
    let probe = batch_dir.join("probes.tsv");
    let stdout = batch_dir.join("stdout.txt");
    let stderr = batch_dir.join("stderr.txt");
    let receipt = batch_dir.join("receipt.txt");
    write_targets(&targets, keys).unwrap_or_else(|error| panic!("{error}"));
    let timeout_s = env_usize("CRAT_S23_BATCH_TIMEOUT_SECS", 3600);
    assert_eq!(
        timeout_s, 3600,
        "checkpoint wall cap must be exactly 3,600s"
    );
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
    let amortized = outcome.wall_s / keys.len() as f64;
    fs::write(
        &receipt,
        format!(
            "batch={batch_index}\nprogram=brotli\nstatus={}\nanalysis_head={}\nbase_harness_head={}\nbase_manifest_sha256={}\nsnapshot={}\nmachine_quiet=verified\nbatch_size={}\nwall_cap_s={}\nrange_start={}\nrange_end={}\nqueried={}\nfirst_key={}\nlast_key={}\nwall_s={:.3}\nwall_s_per_candidate={:.6}\npeak_rss_kb={}\nworker_t_total_s={}\nhard_unsat={}\nforce_sat={}\nsolver_unknown={}\naccepted_owning={}\n",
            outcome.status,
            super::orchestrate::git_sha(),
            P2_BASE_HARNESS_HEAD,
            P2_BASE_MANIFEST_SHA256,
            contract.snapshot.display(),
            batch_size,
            timeout_s,
            range.start,
            range.end,
            keys.len(),
            keys.first().expect("nonempty batch"),
            keys.last().expect("nonempty batch"),
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
        "S23P2BATCH batch={} status=ok candidates={} wall_s={:.3} wall_s_per_candidate={:.6} peak_rss_kb={}",
        batch_index,
        keys.len(),
        outcome.wall_s,
        amortized,
        outcome.peak_rss_kb
    );
}

/// Combine the 88 preserved rows with five manifested brotli checkpoints.
/// This phase launches no corpus worker and forms the aggregate only after the
/// selected 200/261 eligible candidates are complete exactly once.
#[test]
#[ignore = "P2 checkpoint aggregate; run after all brotli batches"]
fn s23_p2_checkpoint_aggregate() {
    let contract = checkpoint_contract();
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
    let mut preserved_paths = fs::read_dir(contract.base.join("probes"))
        .expect("read preserved probes")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "tsv"))
        .collect::<Vec<_>>();
    preserved_paths.sort();
    let mut preserved_rows = 0usize;
    for path in &preserved_paths {
        let file_name = path
            .file_name()
            .and_then(|name| name.to_str())
            .expect("UTF-8 probe filename");
        let program = file_name
            .strip_suffix(".probes.tsv")
            .expect("preserved probe suffix");
        preserved_rows +=
            insert_probe_artifact(program, path, &candidate_slots, &selected, &mut probes)
                .unwrap_or_else(|error| panic!("preserved probe: {error}"));
    }
    assert_eq!(preserved_rows, 88, "preserved row population drifted");

    let brotli_keys = selected
        .iter()
        .filter(|(program, _)| program == "brotli")
        .map(|(_, key)| key.clone())
        .collect::<Vec<_>>();
    let batch_size = env_usize("CRAT_S23_BATCH_SIZE", 24);
    let ranges = checkpoint_batch_ranges(brotli_keys.len(), batch_size)
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
        brotli_rows += insert_probe_artifact(
            "brotli",
            &batch_dir.join("probes.tsv"),
            &candidate_slots,
            &selected,
            &mut probes,
        )
        .unwrap_or_else(|error| panic!("batch {batch_index} probes: {error}"));
        let receipt = parse_receipt(&batch_dir.join("receipt.txt"))
            .unwrap_or_else(|error| panic!("batch {batch_index} receipt: {error}"));
        assert_eq!(receipt.get("status").map(String::as_str), Some("ok"));
        assert_eq!(
            receipt.get("machine_quiet").map(String::as_str),
            Some("verified")
        );
        assert_eq!(
            receipt.get("queried").and_then(|value| value.parse().ok()),
            Some(expected.len())
        );
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
        ));
    }
    assert_eq!(brotli_rows, P2_BROTLI_ELIGIBLE);
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
    let wall_sum = batch_stats
        .iter()
        .map(|(_, _, wall, _, _)| wall)
        .sum::<f64>();
    let batch_table = batch_stats
        .iter()
        .map(|(index, queried, wall, per_candidate, peak)| {
            format!("| {index} | {queried} | {wall:.3} | {per_candidate:.6} | {peak} |")
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

    fs::create_dir_all(&aggregate).expect("create aggregate directory");
    let classification = aggregate.join("classification.tsv");
    let combined_probes = aggregate.join("combined-probes.tsv");
    let per_program = aggregate.join("per-program.tsv");
    let report = aggregate.join("report.md");
    let provenance = aggregate.join("provenance.txt");
    fs::write(&classification, render_final_tsv(&final_records))
        .expect("write checkpoint classification");
    let mut combined = String::from(
        "program\tfield_key\tfield_slot\taccepted_kind\tforce_result\tcore_families\tcore_labels\n",
    );
    for ((program, _), probe) in &probes {
        let force = match probe.force_result {
            ForceResult::Sat => "sat",
            ForceResult::Unsat => "unsat",
            ForceResult::Unknown => "unknown",
            ForceResult::NotQueried => "not-queried",
        };
        combined.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
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
        "program\tscreened\teligible\tno_owned_capable_store\tstore_blocked\tqueried\thard_unsat\tforce_sat\tsolver_unknown\tbudget_not_queried\taccepted_raw\taccepted_ref\taccepted_owning\n",
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
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
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
            "# P2 / S2-3 checkpointed derived-substrate diagnosis\n\n- Screened depth-0 pointer-field universe: **{}**.\n- Eligible owning-store candidates: **261**; no owned-capable store: **{}**; store-blocked: **{}**.\n- Capped tracked-query partition: **200 queried + {} budget-not-queried = 261**.\n- Query result: hard-UNSAT **{}**; force-own SAT **{}**; solver Unknown **0**.\n- Ordinary accepted kinds among queried candidates: Raw **{}**, Ref **{}**, Owning **{}**.\n- Preserved non-brotli rows: **88**, reverified through base manifest `{}`.\n- Brotli checkpoint rows: **112**; batch wall sum **{wall_sum:.3}s**; default cap **8,192 MiB**.\n- Raw tracked cores containing `own-assume`: **{own_assume}/{}**; containing `link-own`: **{link_own}/{}**.\n- Terminal counts: `{terminal_counts}`.\n- Core-family incidence (raw tracked cores; incidence, not necessity): `{core_counts}`.\n\n## Brotli checkpoints\n\n| batch | candidates | wall s | wall s / candidate | peak RSS KiB |\n|---:|---:|---:|---:|---:|\n{batch_table}\n\nThe first batch supplies the observed per-candidate sizing number. Every batch was launched separately under the machine-quiet precondition and wrote its own SHA-256 manifest before the next launch. The aggregate launched no corpus worker and formed only after all 200 selected candidates were present exactly once. Production analysis code remained read-only.\n",
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
            hard_unsat.len(),
            force_sat,
            accepted(SlotKind::Raw),
            accepted(SlotKind::Ref),
            accepted(SlotKind::Owning),
            P2_BASE_MANIFEST_SHA256,
            hard_unsat.len(),
            hard_unsat.len(),
        ),
    )
    .expect("write checkpoint report");
    fs::write(
        &provenance,
        format!(
            "analysis_worktree_head={}\nbase_harness_head={}\nbase_manifest_sha256={}\ncandidate_universe_sha256={}\nsubstrate=derived\nsubstrate_selector={}\nsnapshot={}\nsnapshot_files=100\ndeps_shape=read-only-symlink\nrepair=mode_a\nl2=0\nsafe_mono=per_site\nfork_engine=fork\nmem_cap_mib=8192\nquery_budget={}\nqueried={}\npreserved_rows={}\nbrotli_rows={}\nbatch_size={}\nbatches={}\nbatch_wall_sum_s={:.3}\n",
            super::orchestrate::git_sha(),
            P2_BASE_HARNESS_HEAD,
            P2_BASE_MANIFEST_SHA256,
            P2_CANDIDATE_UNIVERSE_SHA256,
            std::env::var("CRAT_BOC1_SUBSTRATE")
                .unwrap_or_else(|_| "default-derived".to_owned()),
            contract.snapshot.display(),
            P2_QUERY_BUDGET,
            probes.len(),
            preserved_rows,
            brotli_rows,
            batch_size,
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
        "S23P2AGG fields={} eligible=261 queried={} hard_unsat={} force_sat={} accepted_raw={} accepted_ref={} accepted_owning={} budget_not_queried={} own_assume_cores={} link_own_cores={}",
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checkpoint_batches_cover_112_once_with_bounded_sizes() {
        let ranges = checkpoint_batch_ranges(112, 24).expect("valid checkpoint plan");
        assert_eq!(
            ranges
                .iter()
                .map(|range| range.end - range.start)
                .collect::<Vec<_>>(),
            vec![24, 24, 24, 24, 16]
        );
        assert_eq!(ranges.first().map(|range| range.start), Some(0));
        assert_eq!(ranges.last().map(|range| range.end), Some(112));
        for pair in ranges.windows(2) {
            assert_eq!(pair[0].end, pair[1].start);
        }
    }

    #[test]
    fn checkpoint_batch_plan_rejects_empty_inputs() {
        assert!(checkpoint_batch_ranges(0, 24).is_err());
        assert!(checkpoint_batch_ranges(112, 0).is_err());
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
}
