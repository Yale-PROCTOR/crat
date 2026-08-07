//! Test-only P2/S2-3 field-ownership diagnosis on the substrate of record.
//!
//! The corpus path is deliberately two-phase: discovery writes the derived
//! field/store population before any BO solve, then the probe phase spends a
//! capped number of incremental tracked queries only on owning-capable fields.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
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

#[cfg(test)]
mod tests {
    use super::*;

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
