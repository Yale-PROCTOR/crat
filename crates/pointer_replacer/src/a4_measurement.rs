//! Test-only A4 predicted-layer simulation.
//!
//! This module owns measurement selection, re-solving, checkpoints, and
//! reporting. It is reachable only through the `bo_c1` test harness; the
//! production analysis and rewriter do not depend on it.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{Duration, Instant},
};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        AggregateKind, Local, Location, Operand, Rvalue, StatementKind,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::LocalDefId;
use z3::{SatResult, ast::Bool};

use super::{
    collect_program,
    ownership_diagnostic_package::{self, RemovalFilter},
    report::Row,
};
use crate::analyses::borrow_ownership::{
    SlotKind,
    borrow_verify::with_mode_a_commit_trace,
    coherence::constrain_field_ownership,
    construction::{CopyLendMode, construct_bo_into, verify_bo_construction_counting},
    crate_slots::CrateSlots,
    export::{BoExport, VersionSite, location_key, with_bo_export},
    l2::MirLocationKey,
    mutability_facts::{MutFacts, MutFactsMode},
    origin_summary::OriginSummaries,
    origins::compute_origins,
    resolve::{ResolvedSlot, resolve_place},
    slots::{SlotId, SlotOwner},
    solver::{CoreTracker, KindSolver, Selectors, SlotRef, core_label_family},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PathStep {
    Move,
    Copy { sole_use: bool },
    Cast { pointer_depth_preserved: bool },
    Join,
    OpaqueCall,
    Realloc,
    UnresolvedStore,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct StoreProof {
    surviving_local_sources: usize,
    steps: Vec<PathStep>,
    competing_live_use: bool,
}

fn exact_relaxation_is_eligible(stores: &[StoreProof]) -> bool {
    !stores.is_empty()
        && stores.iter().all(|store| {
            store.surviving_local_sources == 1
                && !store.competing_live_use
                && !store.steps.is_empty()
                && store.steps.iter().all(|step| {
                    matches!(
                        step,
                        PathStep::Move
                            | PathStep::Copy { sole_use: true }
                            | PathStep::Cast {
                                pointer_depth_preserved: true
                            }
                    )
                })
        })
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct BaselineRow {
    program: String,
    field_key: String,
}

fn validate_complete_baseline(
    expected: &[BaselineRow],
    actual: &[BaselineRow],
) -> Result<(), String> {
    let expected_set = expected.iter().collect::<std::collections::BTreeSet<_>>();
    let actual_set = actual.iter().collect::<std::collections::BTreeSet<_>>();
    if expected_set.len() != expected.len() {
        return Err("expected baseline contains duplicate identities".to_owned());
    }
    if actual_set.len() != actual.len() {
        return Err("actual baseline contains duplicate identities".to_owned());
    }
    if expected_set != actual_set {
        return Err(format!(
            "baseline identity mismatch: expected={} actual={} missing={:?} extra={:?}",
            expected.len(),
            actual.len(),
            expected_set.difference(&actual_set).collect::<Vec<_>>(),
            actual_set.difference(&expected_set).collect::<Vec<_>>(),
        ));
    }
    Ok(())
}

fn checkpoint_temp_path(path: &Path) -> PathBuf {
    path.with_extension("tsv.tmp")
}

fn write_atomic_checkpoint(path: &Path, contents: &str) -> Result<(), String> {
    let temp = checkpoint_temp_path(path);
    fs::write(&temp, contents).map_err(|error| format!("write {}: {error}", temp.display()))?;
    fs::rename(&temp, path).map_err(|error| {
        format!(
            "publish checkpoint {} from {}: {error}",
            path.display(),
            temp.display()
        )
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ForceResult {
    Sat,
    Unsat,
    Unknown,
}

impl ForceResult {
    fn label(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
        }
    }
}

impl From<SatResult> for ForceResult {
    fn from(value: SatResult) -> Self {
        match value {
            SatResult::Sat => Self::Sat,
            SatResult::Unsat => Self::Unsat,
            SatResult::Unknown => Self::Unknown,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AcceptedBaseline {
    program: String,
    field_key: String,
    field_slot: usize,
    accepted_kind: SlotKind,
    force_result: ForceResult,
    core_families: Vec<String>,
    core_labels: Vec<String>,
}

fn kind_label(kind: SlotKind) -> &'static str {
    match kind {
        SlotKind::Raw => "raw",
        SlotKind::Ref => "ref",
        SlotKind::Owning => "owning",
    }
}

fn parse_kind(value: &str) -> Result<SlotKind, String> {
    match value {
        "raw" => Ok(SlotKind::Raw),
        "ref" => Ok(SlotKind::Ref),
        "owning" => Ok(SlotKind::Owning),
        other => Err(format!("unknown slot kind {other:?}")),
    }
}

fn parse_force(value: &str) -> Result<ForceResult, String> {
    match value {
        "sat" => Ok(ForceResult::Sat),
        "unsat" => Ok(ForceResult::Unsat),
        "unknown" => Ok(ForceResult::Unknown),
        other => Err(format!("unknown force result {other:?}")),
    }
}

fn parse_accepted_baseline(path: &Path) -> Result<Vec<AcceptedBaseline>, String> {
    const HEADER: &str = "platform\tmachine_id\tprogram\tfield_key\tfield_slot\taccepted_kind\tforce_result\tcore_families\tcore_labels";
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read accepted baseline {}: {error}", path.display()))?;
    let mut lines = input.lines();
    if lines.next() != Some(HEADER) {
        return Err(format!(
            "accepted baseline header drift: {}",
            path.display()
        ));
    }
    let mut rows = Vec::new();
    let mut identities = BTreeSet::new();
    for (offset, line) in lines.enumerate() {
        let columns = line.split('\t').collect::<Vec<_>>();
        if columns.len() != 9 {
            return Err(format!(
                "accepted baseline line {} has {} columns",
                offset + 2,
                columns.len()
            ));
        }
        if columns[0] != "linux-x86_64" || columns[1] != "lambda7" {
            return Err(format!(
                "accepted baseline line {} measurement identity drift",
                offset + 2
            ));
        }
        let identity = (columns[2].to_owned(), columns[3].to_owned());
        if !identities.insert(identity.clone()) {
            return Err(format!(
                "duplicate accepted baseline identity {} {}",
                identity.0, identity.1
            ));
        }
        rows.push(AcceptedBaseline {
            program: identity.0,
            field_key: identity.1,
            field_slot: columns[4]
                .parse()
                .map_err(|error| format!("baseline line {} field slot: {error}", offset + 2))?,
            accepted_kind: parse_kind(columns[5])?,
            force_result: parse_force(columns[6])?,
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
        });
    }
    if rows.len() != 261 {
        return Err(format!(
            "accepted baseline must contain 261 rows, got {}",
            rows.len()
        ));
    }
    Ok(rows)
}

fn field_key(tcx: TyCtxt<'_>, slots: &CrateSlots, field: SlotId) -> String {
    let slot = slots.field_slots.slot(field);
    let SlotOwner::Field(owner) = slot.owner else {
        panic!("field slot has non-field owner: {field:?}");
    };
    format!(
        "{}::field{}@d{}",
        tcx.def_path_str(owner.struct_did.to_def_id()),
        owner.field_index,
        slot.depth
    )
}

fn candidate_fields(tcx: TyCtxt<'_>, slots: &CrateSlots) -> BTreeMap<String, SlotId> {
    (0..slots.field_slots.len())
        .filter_map(|index| {
            let slot = SlotId::from_usize(index);
            (slots.field_slots.slot(slot).depth == 0).then(|| (field_key(tcx, slots, slot), slot))
        })
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TransferEdge {
    from: Local,
    to: Local,
    location: MirLocationKey,
    step: PathStep,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct StoreEdge {
    fn_did: LocalDefId,
    rhs: Option<Local>,
    location: MirLocationKey,
    step: PathStep,
}

fn pointer_depth(mut ty: Ty<'_>) -> Option<u8> {
    let mut depth = 0u8;
    while let TyKind::RawPtr(inner, _) = ty.kind() {
        depth = depth.checked_add(1)?;
        ty = *inner;
    }
    (depth > 0).then_some(depth)
}

fn innermost_is_c_void(tcx: TyCtxt<'_>, mut ty: Ty<'_>) -> bool {
    while let TyKind::RawPtr(inner, _) = ty.kind() {
        ty = *inner;
    }
    ty.ty_adt_def()
        .is_some_and(|def| tcx.item_name(def.did()).as_str() == "c_void")
}

fn cast_preserves_pointer_identity(tcx: TyCtxt<'_>, from: Ty<'_>, to: Ty<'_>) -> bool {
    pointer_depth(from).is_some()
        && pointer_depth(from) == pointer_depth(to)
        && !innermost_is_c_void(tcx, from)
        && !innermost_is_c_void(tcx, to)
}

fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}

fn operand_step(operand: &Operand<'_>) -> PathStep {
    match operand {
        Operand::Move(_) => PathStep::Move,
        Operand::Copy(_) => PathStep::Copy { sole_use: false },
        Operand::Constant(_) => PathStep::UnresolvedStore,
    }
}

#[derive(Default)]
struct ProgramFlow {
    transfers: FxHashMap<LocalDefId, Vec<TransferEdge>>,
    stores: BTreeMap<String, Vec<StoreEdge>>,
}

fn scan_program_flow(
    tcx: TyCtxt<'_>,
    slots: &CrateSlots,
    target_keys: &BTreeSet<String>,
) -> ProgramFlow {
    let program = collect_program(tcx);
    let mut flow = ProgramFlow::default();
    for &fn_did in &program.functions {
        let body_ref = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        let body = &*body_ref;
        for (block, bbdata) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in bbdata.statements.iter().enumerate() {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                    continue;
                };
                let location = location_key(Location {
                    block,
                    statement_index,
                });

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
                        let key = field_key(tcx, slots, field);
                        if target_keys.contains(&key) {
                            if matches!(operand, Operand::Constant(_)) {
                                continue;
                            }
                            flow.stores.entry(key).or_default().push(StoreEdge {
                                fn_did,
                                rhs: operand_local(operand),
                                location,
                                step: operand_step(operand),
                            });
                        }
                    }
                    continue;
                }

                if let Some(ResolvedSlot::Field(field)) =
                    resolve_place(slots, fn_did, body, *lhs, 0, None)
                {
                    let key = field_key(tcx, slots, field);
                    if target_keys.contains(&key) {
                        let (rhs, step) = match rvalue {
                            Rvalue::Use(operand @ (Operand::Copy(_) | Operand::Move(_))) => {
                                (operand_local(operand), operand_step(operand))
                            }
                            Rvalue::Cast(
                                _,
                                operand @ (Operand::Copy(_) | Operand::Move(_)),
                                to,
                            ) => {
                                let rhs = operand_local(operand);
                                let preserves = rhs.is_some_and(|local| {
                                    cast_preserves_pointer_identity(
                                        tcx,
                                        body.local_decls[local].ty,
                                        *to,
                                    )
                                });
                                (
                                    rhs,
                                    PathStep::Cast {
                                        pointer_depth_preserved: preserves,
                                    },
                                )
                            }
                            Rvalue::Use(Operand::Constant(_))
                            | Rvalue::Cast(_, Operand::Constant(_), _) => continue,
                            _ => (None, PathStep::UnresolvedStore),
                        };
                        flow.stores.entry(key).or_default().push(StoreEdge {
                            fn_did,
                            rhs,
                            location,
                            step,
                        });
                    }
                    continue;
                }

                if !lhs.projection.is_empty() {
                    continue;
                }
                let (rhs, step) = match rvalue {
                    Rvalue::Use(operand @ (Operand::Copy(_) | Operand::Move(_))) => {
                        (operand_local(operand), operand_step(operand))
                    }
                    Rvalue::Cast(_, operand @ (Operand::Copy(_) | Operand::Move(_)), to) => {
                        let rhs = operand_local(operand);
                        let preserves = rhs.is_some_and(|local| {
                            cast_preserves_pointer_identity(tcx, body.local_decls[local].ty, *to)
                        });
                        (
                            rhs,
                            PathStep::Cast {
                                pointer_depth_preserved: preserves,
                            },
                        )
                    }
                    _ => (None, PathStep::OpaqueCall),
                };
                if let Some(from) = rhs {
                    flow.transfers
                        .entry(fn_did)
                        .or_default()
                        .push(TransferEdge {
                            from,
                            to: lhs.local,
                            location,
                            step,
                        });
                }
            }
        }
    }
    flow
}

#[derive(Clone, Debug)]
struct SourceRoot {
    index: usize,
    fn_did: LocalDefId,
    local: Local,
    location: MirLocationKey,
    realloc: bool,
}

fn source_roots(export: &BoExport) -> Vec<SourceRoot> {
    export
        .source_sites
        .iter()
        .enumerate()
        .filter_map(|(index, source)| {
            let call = source.call.as_ref()?;
            let locals = export
                .version_sites
                .iter()
                .filter(|site| {
                    site.fn_did == call.fn_did
                        && site.location == call.location
                        && site.def_var == Some(source.var)
                })
                .map(|site| site.local)
                .collect::<FxHashSet<_>>();
            (locals.len() == 1).then(|| SourceRoot {
                index,
                fn_did: call.fn_did,
                local: *locals.iter().next().expect("one source local"),
                location: call.location,
                realloc: call.callee == "realloc",
            })
        })
        .collect()
}

fn paths_between<'a>(
    edges: &'a [TransferEdge],
    source: Local,
    target: Local,
) -> Vec<Vec<&'a TransferEdge>> {
    fn visit<'a>(
        edges: &'a [TransferEdge],
        current: Local,
        target: Local,
        seen: &mut FxHashSet<Local>,
        path: &mut Vec<&'a TransferEdge>,
        found: &mut Vec<Vec<&'a TransferEdge>>,
    ) {
        if found.len() >= 2 {
            return;
        }
        if current == target {
            found.push(path.clone());
            return;
        }
        if !seen.insert(current) {
            return;
        }
        for edge in edges.iter().filter(|edge| edge.from == current) {
            path.push(edge);
            visit(edges, edge.to, target, seen, path, found);
            path.pop();
            if found.len() >= 2 {
                break;
            }
        }
        seen.remove(&current);
    }

    let mut found = Vec::new();
    visit(
        edges,
        source,
        target,
        &mut FxHashSet::default(),
        &mut Vec::new(),
        &mut found,
    );
    found
}

struct TokenUseAudit<'a> {
    path_locals: &'a FxHashSet<Local>,
    allowed_transfer_locations: &'a BTreeSet<MirLocationKey>,
    token_uses: FxHashMap<Local, usize>,
    competing: bool,
}

impl<'tcx> Visitor<'tcx> for TokenUseAudit<'_> {
    fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
        if !self.path_locals.contains(&local) {
            return;
        }
        let location = location_key(location);
        match context {
            PlaceContext::NonUse(_)
            | PlaceContext::MutatingUse(
                MutatingUseContext::Call
                | MutatingUseContext::Store
                | MutatingUseContext::Projection,
            )
            | PlaceContext::NonMutatingUse(
                NonMutatingUseContext::Inspect | NonMutatingUseContext::Projection,
            ) => {}
            PlaceContext::NonMutatingUse(
                NonMutatingUseContext::Copy | NonMutatingUseContext::Move,
            ) => {
                *self.token_uses.entry(local).or_default() += 1;
                if !self.allowed_transfer_locations.contains(&location) {
                    self.competing = true;
                }
            }
            _ => self.competing = true,
        }
    }
}

#[derive(Clone, Debug)]
struct DetailedStoreProof {
    contract: StoreProof,
    vars: BTreeSet<usize>,
    source_index: Option<usize>,
}

fn vars_on_path(
    sites: &[VersionSite],
    fn_did: LocalDefId,
    locals: &FxHashSet<Local>,
    locations: &BTreeSet<MirLocationKey>,
) -> BTreeSet<usize> {
    sites
        .iter()
        .filter(|site| {
            site.fn_did == fn_did
                && locals.contains(&site.local)
                && locations.contains(&site.location)
        })
        .flat_map(|site| [site.use_var, site.def_var])
        .flatten()
        .map(|var| var.index())
        .collect()
}

fn prove_store(
    tcx: TyCtxt<'_>,
    flow: &ProgramFlow,
    export: &BoExport,
    roots: &[SourceRoot],
    store: StoreEdge,
) -> DetailedStoreProof {
    let Some(rhs) = store.rhs else {
        return DetailedStoreProof {
            contract: StoreProof {
                surviving_local_sources: 0,
                steps: vec![PathStep::UnresolvedStore],
                competing_live_use: false,
            },
            vars: BTreeSet::new(),
            source_index: None,
        };
    };
    let edges = flow
        .transfers
        .get(&store.fn_did)
        .map(Vec::as_slice)
        .unwrap_or_default();
    let mut candidates = Vec::new();
    for root in roots.iter().filter(|root| root.fn_did == store.fn_did) {
        for path in paths_between(edges, root.local, rhs) {
            candidates.push((root, path));
            if candidates.len() >= 2 {
                break;
            }
        }
        if candidates.len() >= 2 {
            break;
        }
    }
    if candidates.len() != 1 {
        return DetailedStoreProof {
            contract: StoreProof {
                surviving_local_sources: candidates.len(),
                steps: vec![if candidates.len() > 1 {
                    PathStep::Join
                } else {
                    PathStep::OpaqueCall
                }],
                competing_live_use: false,
            },
            vars: BTreeSet::new(),
            source_index: None,
        };
    }
    let (root, path) = candidates.pop().expect("one source path");
    let mut locals = FxHashSet::default();
    locals.insert(root.local);
    for edge in &path {
        locals.insert(edge.from);
        locals.insert(edge.to);
    }
    locals.insert(rhs);
    let mut locations = BTreeSet::from([root.location, store.location]);
    locations.extend(path.iter().map(|edge| edge.location));

    let incoming = |local| edges.iter().filter(|edge| edge.to == local).count();
    let joined = incoming(root.local) != 0 || path.iter().any(|edge| incoming(edge.to) != 1);
    let body_ref = tcx
        .mir_drops_elaborated_and_const_checked(store.fn_did)
        .borrow();
    let mut audit = TokenUseAudit {
        path_locals: &locals,
        allowed_transfer_locations: &locations,
        token_uses: FxHashMap::default(),
        competing: joined,
    };
    audit.visit_body(&body_ref);

    let mut steps = path.iter().map(|edge| edge.step).collect::<Vec<_>>();
    steps.push(store.step);
    for (step, from) in steps.iter_mut().zip(
        path.iter()
            .map(|edge| edge.from)
            .chain(std::iter::once(rhs)),
    ) {
        if matches!(step, PathStep::Copy { .. }) {
            *step = PathStep::Copy {
                sole_use: audit.token_uses.get(&from).copied().unwrap_or(0) == 1,
            };
        }
    }
    if root.realloc {
        steps.insert(0, PathStep::Realloc);
    }
    DetailedStoreProof {
        contract: StoreProof {
            surviving_local_sources: 1,
            steps,
            competing_live_use: audit.competing,
        },
        vars: vars_on_path(&export.version_sites, store.fn_did, &locals, &locations),
        source_index: Some(root.index),
    }
}

fn bare_negative_own_assume(label: &str) -> Option<(&str, usize)> {
    let marker = "::own-assume[";
    let offset = label.rfind(marker)? + 2;
    let bare = &label[offset..];
    if !bare.ends_with("=false)") {
        return None;
    }
    let var = bare
        .rsplit_once('(')?
        .1
        .strip_suffix("=false)")?
        .parse()
        .ok()?;
    Some((bare, var))
}

#[derive(Clone, Debug)]
struct CandidateProof {
    eligible: bool,
    reason: String,
    exact_labels: BTreeSet<String>,
    source_indices: BTreeSet<usize>,
}

fn proof_reason(stores: &[StoreProof]) -> String {
    if stores.is_empty() {
        return "no-resolved-store".to_owned();
    }
    for store in stores {
        if store.surviving_local_sources != 1 {
            return format!("allocation-source-count-{}", store.surviving_local_sources);
        }
        if store.competing_live_use {
            return "competing-live-use".to_owned();
        }
        for step in &store.steps {
            let reason = match step {
                PathStep::Move | PathStep::Copy { sole_use: true } => continue,
                PathStep::Copy { sole_use: false } => "copy-duplicates-token",
                PathStep::Cast {
                    pointer_depth_preserved: false,
                } => "ownership-erasing-cast",
                PathStep::Cast {
                    pointer_depth_preserved: true,
                } => continue,
                PathStep::Join => "join-or-mixed-origin",
                PathStep::OpaqueCall => "opaque-origin",
                PathStep::Realloc => "realloc-origin",
                PathStep::UnresolvedStore => "unresolved-store",
            };
            return reason.to_owned();
        }
    }
    "eligible".to_owned()
}

fn candidate_proof(
    tcx: TyCtxt<'_>,
    flow: &ProgramFlow,
    export: &BoExport,
    baseline: &AcceptedBaseline,
) -> CandidateProof {
    let roots = source_roots(export);
    let detailed = flow
        .stores
        .get(&baseline.field_key)
        .into_iter()
        .flatten()
        .copied()
        .map(|store| prove_store(tcx, flow, export, &roots, store))
        .collect::<Vec<_>>();
    let contracts = detailed
        .iter()
        .map(|proof| proof.contract.clone())
        .collect::<Vec<_>>();
    if !exact_relaxation_is_eligible(&contracts) {
        return CandidateProof {
            eligible: false,
            reason: proof_reason(&contracts),
            exact_labels: BTreeSet::new(),
            source_indices: BTreeSet::new(),
        };
    }
    let path_vars = detailed
        .iter()
        .flat_map(|proof| proof.vars.iter().copied())
        .collect::<BTreeSet<_>>();
    let exact_labels = baseline
        .core_labels
        .iter()
        .filter_map(|label| bare_negative_own_assume(label))
        .filter(|(_, var)| path_vars.contains(var))
        .map(|(bare, _)| bare.to_owned())
        .collect::<BTreeSet<_>>();
    let source_indices = detailed
        .iter()
        .filter_map(|proof| proof.source_index)
        .collect::<BTreeSet<_>>();
    let eligible = !exact_labels.is_empty() && source_indices.len() == detailed.len();
    CandidateProof {
        eligible,
        reason: if exact_labels.is_empty() {
            "no-core-negative-on-proven-path".to_owned()
        } else if source_indices.len() != detailed.len() {
            "source-selector-identity-mismatch".to_owned()
        } else {
            "eligible".to_owned()
        },
        exact_labels,
        source_indices,
    }
}

fn core_evidence(
    core: &[Bool],
    tracker: &CoreTracker,
    selectors: &Selectors,
) -> (Vec<String>, Vec<String>) {
    let mut labels = core
        .iter()
        .map(|literal| {
            if let Some(label) = tracker.label_of(literal) {
                return label;
            }
            if let Some(index) = selectors
                .sources()
                .iter()
                .position(|selector| selector == literal)
            {
                return format!("allocation-token(source-index={index})");
            }
            panic!("A4 core contains an unattributed assumption literal: {literal}");
        })
        .collect::<Vec<_>>();
    labels.sort();
    labels.dedup();
    let families = labels
        .iter()
        .filter_map(|label| {
            if label.starts_with("allocation-token(") {
                Some("allocation-token")
            } else {
                core_label_family(label)
            }
        })
        .map(str::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    (families, labels)
}

fn relaxed_assumptions(
    tracker: &CoreTracker,
    tracks: &[Bool],
    selectors: &Selectors,
    omitted: &BTreeSet<String>,
    sources: &BTreeSet<usize>,
) -> Vec<Bool> {
    let mut assumptions = tracks
        .iter()
        .filter(|track| {
            tracker
                .label_of(track)
                .and_then(|label| bare_negative_own_assume(&label).map(|(bare, _)| bare.to_owned()))
                .is_none_or(|bare| !omitted.contains(&bare))
        })
        .cloned()
        .collect::<Vec<_>>();
    assumptions.extend(sources.iter().map(|&index| {
        selectors
            .sources()
            .get(index)
            .unwrap_or_else(|| panic!("source selector index {index} drifted"))
            .clone()
    }));
    assumptions
}

fn replay_relaxed_candidate(
    program: &crate::utils::rustc::RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mutability: &MutFacts,
    field: SlotRef,
    omitted: &BTreeSet<String>,
    sources: &BTreeSet<usize>,
) -> Option<FxHashMap<SlotRef, SlotKind>> {
    ownership_diagnostic_package::with_removal_filter(
        RemovalFilter::ExactOwnAssumeLabels(omitted.clone()),
        || {
            let solver = KindSolver::new(slots);
            let construction = construct_bo_into(
                program,
                slots,
                origins,
                mutability,
                &solver,
                CopyLendMode::current(),
            )
            .expect("A4 relaxed emission");
            for &index in sources {
                solver.optimize().assert(
                    construction
                        .selectors
                        .sources()
                        .get(index)
                        .unwrap_or_else(|| panic!("relaxed source index {index} drifted")),
                );
            }
            solver.assert_owning(field);
            verify_bo_construction_counting(
                program,
                slots,
                origins,
                &solver,
                &construction,
                mutability,
            )
            .0
        },
    )
}

#[derive(Clone, Debug)]
struct SimulationRecord {
    baseline: AcceptedBaseline,
    proof_eligible: bool,
    proof_reason: String,
    selected_labels: Vec<String>,
    source_indices: Vec<usize>,
    necessary_labels: usize,
    relaxed_force: String,
    relaxed_kind: Option<SlotKind>,
    relaxed_core_families: Vec<String>,
    relaxed_core_labels: Vec<String>,
}

fn tsv_cell(value: &str) -> String {
    value.replace(['\t', '\n', '\r'], "_")
}

fn render_records(program: &str, mode: CopyLendMode, records: &[SimulationRecord]) -> String {
    let mut out = String::from(
        "copy_lend_mode\tprogram\tfield_key\tfield_slot\tbaseline_kind\tbaseline_force\tbaseline_core_families\tproof_eligible\tproof_reason\tselected_own_assumes\tsource_selector_indices\tnecessary_labels\trelaxed_force\trelaxed_kind\trelaxed_core_families\trelaxed_core_labels\n",
    );
    for record in records {
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            mode.label(),
            tsv_cell(program),
            tsv_cell(&record.baseline.field_key),
            record.baseline.field_slot,
            kind_label(record.baseline.accepted_kind),
            record.baseline.force_result.label(),
            tsv_cell(&record.baseline.core_families.join("|")),
            record.proof_eligible,
            tsv_cell(&record.proof_reason),
            tsv_cell(&record.selected_labels.join("|")),
            record
                .source_indices
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join("|"),
            record.necessary_labels,
            record.relaxed_force,
            record.relaxed_kind.map(kind_label).unwrap_or("-"),
            tsv_cell(&record.relaxed_core_families.join("|")),
            tsv_cell(&record.relaxed_core_labels.join("|")),
        ));
    }
    out
}

fn phase_line(started: Instant, phase: &str, candidate: Option<&str>, completed: usize) -> String {
    format!(
        "BOC1PHASE a4-probe phase={phase} candidate={} completed={completed} t_s={:.3}",
        candidate.unwrap_or("none"),
        started.elapsed().as_secs_f64()
    )
}

fn emit_phase(started: Instant, phase: &str, candidate: Option<&str>, completed: usize) {
    eprintln!("{}", phase_line(started, phase, candidate, completed));
}

pub(super) fn run_probe_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
    let started = Instant::now();
    let program_name = std::env::var("CRAT_BOC1_NAME").expect("A4 worker program name");
    let baseline_path = PathBuf::from(
        std::env::var_os("CRAT_A4_ACCEPTED_BASELINE").expect("A4 accepted baseline path"),
    );
    let artifact_path =
        PathBuf::from(std::env::var_os("CRAT_A4_ARTIFACT").expect("A4 artifact path"));
    let checkpoint_path =
        PathBuf::from(std::env::var_os("CRAT_A4_CHECKPOINT").expect("A4 checkpoint path"));
    emit_phase(started, "worker-start", None, 0);
    let all_baseline = parse_accepted_baseline(&baseline_path)
        .unwrap_or_else(|error| panic!("A4 STOP phase=baseline-parse candidate=none: {error}"));
    let baseline = all_baseline
        .into_iter()
        .filter(|row| row.program == program_name)
        .collect::<Vec<_>>();
    assert!(
        !baseline.is_empty(),
        "A4 STOP phase=baseline-program candidate={program_name}: no rows"
    );
    let expected = baseline
        .iter()
        .map(|row| BaselineRow {
            program: row.program.clone(),
            field_key: row.field_key.clone(),
        })
        .collect::<Vec<_>>();
    validate_complete_baseline(&expected, &expected)
        .unwrap_or_else(|error| panic!("A4 STOP phase=baseline-identity candidate=none: {error}"));

    emit_phase(started, "ordinary-start", None, 0);
    let program = collect_program(tcx);
    let origins = compute_origins(&program);
    let slots = CrateSlots::build(&program);
    let ordinary = KindSolver::new(&slots);
    let mutability = match MutFactsMode::current() {
        MutFactsMode::Off => MutFacts::all_mut(),
        MutFactsMode::On => MutFacts::from_program(&program),
    };
    let (((ordinary_model, _ordinary_stats), commit_trace), ordinary_export) =
        with_bo_export(|| {
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &mutability,
                &ordinary,
                CopyLendMode::current(),
            )
            .expect("A4 ordinary emission");
            let ((model, stats), trace) = with_mode_a_commit_trace(|| {
                verify_bo_construction_counting(
                    &program,
                    &slots,
                    &origins,
                    &ordinary,
                    &construction,
                    &mutability,
                )
            });
            ((model, stats), trace)
        });
    let ordinary_model = ordinary_model.unwrap_or_else(|| {
        panic!("A4 STOP phase=ordinary candidate=none: selector-off baseline declined")
    });
    emit_phase(started, "ordinary-complete", None, 0);

    emit_phase(started, "tracked-start", None, 0);
    let tracked = KindSolver::new_tracked(&slots);
    let (tracked_construction, tracked_export) = with_bo_export(|| {
        construct_bo_into(
            &program,
            &slots,
            &origins,
            &mutability,
            &tracked,
            CopyLendMode::current(),
        )
        .expect("A4 tracked emission")
    });
    assert_eq!(
        ordinary_export.source_sites, tracked_export.source_sites,
        "A4 STOP phase=selector-alignment candidate=none: source provenance drift"
    );
    assert_eq!(
        ordinary_export.version_sites, tracked_export.version_sites,
        "A4 STOP phase=selector-alignment candidate=none: SSA provenance drift"
    );
    let tracker = tracked.tracker().expect("tracked solver has tracker");
    let tracked_selectors = tracked_construction.selectors;
    tracker.set_context("field-law");
    constrain_field_ownership(&tracked, &slots, &program);
    for commit in &commit_trace {
        tracker.set_context(&format!("mode-a-round{}", commit.round));
        tracked.add_borrow_exclusion(Some(commit.target), &[]);
    }
    assert_eq!(
        tracked.optimize().check(&tracker.tracks()),
        SatResult::Sat,
        "A4 STOP phase=tracked-baseline candidate=none: hard baseline UNSAT"
    );
    emit_phase(started, "tracked-complete", None, 0);

    let fields = candidate_fields(tcx, &slots);
    let target_keys = baseline
        .iter()
        .map(|row| row.field_key.clone())
        .collect::<BTreeSet<_>>();
    let flow = scan_program_flow(tcx, &slots, &target_keys);
    let mut records = Vec::with_capacity(baseline.len());
    for expected_row in baseline {
        let key = expected_row.field_key.clone();
        emit_phase(started, "candidate-start", Some(&key), records.len());
        let field = *fields.get(&key).unwrap_or_else(|| {
            panic!("A4 STOP phase=field-identity candidate={key}: target not re-derived")
        });
        assert_eq!(
            field.index(),
            expected_row.field_slot,
            "A4 STOP phase=field-identity candidate={key}: field slot drift"
        );
        let field_ref = SlotRef::Field(field);
        let ordinary_kind = ordinary_model.get(&field_ref).copied().unwrap_or_else(|| {
            panic!("A4 STOP phase=ordinary-identity candidate={key}: missing field")
        });
        assert_eq!(
            ordinary_kind, expected_row.accepted_kind,
            "A4 STOP phase=ordinary-identity candidate={key}: accepted kind drift"
        );

        tracked.push_scope();
        tracker.set_context("s23-force-own");
        tracked.assert_owning(field_ref);
        let tracks = tracker.tracks();
        let baseline_result = tracked.optimize().check(&tracks);
        assert_ne!(
            baseline_result,
            SatResult::Unknown,
            "A4 STOP phase=selector-off-force candidate={key}: solver Unknown"
        );
        let (baseline_families, baseline_labels) = if baseline_result == SatResult::Unsat {
            core_evidence(
                &tracked.optimize().get_unsat_core(),
                tracker,
                &tracked_selectors,
            )
        } else {
            (Vec::new(), Vec::new())
        };
        assert_eq!(
            ForceResult::from(baseline_result),
            expected_row.force_result,
            "A4 STOP phase=selector-off-force candidate={key}: verdict drift"
        );
        assert_eq!(
            baseline_families, expected_row.core_families,
            "A4 STOP phase=selector-off-core candidate={key}: family drift"
        );
        assert_eq!(
            baseline_labels, expected_row.core_labels,
            "A4 STOP phase=selector-off-core candidate={key}: label drift"
        );

        let proof = if baseline_result == SatResult::Unsat {
            candidate_proof(tcx, &flow, &ordinary_export, &expected_row)
        } else {
            CandidateProof {
                eligible: false,
                reason: "baseline-force-sat-exception".to_owned(),
                exact_labels: BTreeSet::new(),
                source_indices: BTreeSet::new(),
            }
        };
        if baseline_result == SatResult::Sat {
            assert!(
                proof.exact_labels.is_empty() && proof.source_indices.is_empty(),
                "A4 STOP phase=exception-selector candidate={key}: SAT exception selected"
            );
        }

        let mut selected = proof.exact_labels.clone();
        let (relaxed_result, relaxed_families, relaxed_labels, necessary_labels) =
            if !proof.eligible {
                (baseline_result, baseline_families, baseline_labels, 0usize)
            } else {
                let assumptions = relaxed_assumptions(
                    tracker,
                    &tracks,
                    &tracked_selectors,
                    &selected,
                    &proof.source_indices,
                );
                let mut result = tracked.optimize().check(&assumptions);
                assert_ne!(
                    result,
                    SatResult::Unknown,
                    "A4 STOP phase=relaxed-force candidate={key}: solver Unknown"
                );
                if result == SatResult::Sat {
                    for label in selected.clone() {
                        let mut trial = selected.clone();
                        trial.remove(&label);
                        let trial_assumptions = relaxed_assumptions(
                            tracker,
                            &tracks,
                            &tracked_selectors,
                            &trial,
                            &proof.source_indices,
                        );
                        match tracked.optimize().check(&trial_assumptions) {
                            SatResult::Sat => {
                                selected = trial;
                            }
                            SatResult::Unsat => {}
                            SatResult::Unknown => panic!(
                                "A4 STOP phase=necessity candidate={key}: solver Unknown at {label}"
                            ),
                        }
                    }
                    let final_assumptions = relaxed_assumptions(
                        tracker,
                        &tracks,
                        &tracked_selectors,
                        &selected,
                        &proof.source_indices,
                    );
                    result = tracked.optimize().check(&final_assumptions);
                    assert_eq!(
                        result,
                        SatResult::Sat,
                        "A4 STOP phase=necessity candidate={key}: minimized set lost sufficiency"
                    );
                }
                let (families, labels) = if result == SatResult::Unsat {
                    core_evidence(
                        &tracked.optimize().get_unsat_core(),
                        tracker,
                        &tracked_selectors,
                    )
                } else {
                    (Vec::new(), Vec::new())
                };
                let necessary = if result == SatResult::Sat {
                    selected.len()
                } else {
                    0
                };
                (result, families, labels, necessary)
            };

        let (relaxed_force, relaxed_kind) = if relaxed_result == SatResult::Sat
            && expected_row.force_result == ForceResult::Unsat
        {
            emit_phase(started, "borrow-replay-start", Some(&key), records.len());
            match replay_relaxed_candidate(
                &program,
                &slots,
                &origins,
                &mutability,
                field_ref,
                &selected,
                &proof.source_indices,
            ) {
                Some(model) => {
                    let kind = model.get(&field_ref).copied().unwrap_or_else(|| {
                        panic!("A4 STOP phase=borrow-replay candidate={key}: field absent")
                    });
                    assert_eq!(
                        kind,
                        SlotKind::Owning,
                        "A4 STOP phase=borrow-replay candidate={key}: token lost"
                    );
                    ("sat".to_owned(), Some(kind))
                }
                None => ("borrow-replay-decline".to_owned(), None),
            }
        } else {
            (
                ForceResult::from(relaxed_result).label().to_owned(),
                (relaxed_result == SatResult::Sat).then_some(ordinary_kind),
            )
        };
        tracked.pop_scope();

        records.push(SimulationRecord {
            baseline: expected_row,
            proof_eligible: proof.eligible,
            proof_reason: proof.reason,
            selected_labels: selected.into_iter().collect(),
            source_indices: proof.source_indices.into_iter().collect(),
            necessary_labels,
            relaxed_force,
            relaxed_kind,
            relaxed_core_families: relaxed_families,
            relaxed_core_labels: relaxed_labels,
        });
        write_atomic_checkpoint(
            &checkpoint_path,
            &render_records(&program_name, CopyLendMode::current(), &records),
        )
        .unwrap_or_else(|error| panic!("A4 STOP phase=checkpoint candidate={key}: {error}"));
        emit_phase(started, "checkpoint-written", Some(&key), records.len());
    }

    write_atomic_checkpoint(
        &artifact_path,
        &render_records(&program_name, CopyLendMode::current(), &records),
    )
    .unwrap_or_else(|error| panic!("A4 STOP phase=finalize candidate=none: {error}"));
    emit_phase(started, "complete", None, records.len());
    let mut row = Row::default();
    row.set("copy_lend_mode", CopyLendMode::current().label());
    row.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    row.set("queried", records.len());
    row.set(
        "proof_eligible",
        records
            .iter()
            .filter(|record| record.proof_eligible)
            .count(),
    );
    row.set(
        "flipped_sat",
        records
            .iter()
            .filter(|record| {
                record.baseline.force_result == ForceResult::Unsat && record.relaxed_force == "sat"
            })
            .count(),
    );
    row.set(
        "borrow_decline",
        records
            .iter()
            .filter(|record| record.relaxed_force == "borrow-replay-decline")
            .count(),
    );
    row.set(
        "t_total_s",
        format!("{:.3}", started.elapsed().as_secs_f64()),
    );
    row.set("status", "ok");
    row
}

const ACCEPTED_AGGREGATE_MANIFEST_SHA256: &str =
    "65a0eb62613431cfdadf9d1b46199a5789a818a1e77bc6e0f71374b34fa547e1";
const CANDIDATE_UNIVERSE_SHA256: &str =
    "56ca571ac8a6b99e42884b6495a6bab4a0ad46a4e2c1ac6a9bac30df5ff95527";
const RAW_CORPUS_DIGEST: &str = "9fc912af10fd3b235fe4d444d2fbac0bc521509b1c9447fc551acd0130e0e621";
const DERIVED_SUBSTRATE_DIGEST: &str =
    "db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6";
const SNAPSHOT_PATH: &str = "/home/p51lee/dev/agent-worktrees/m1-artifact-snapshots/3b26a0ff";
const MACHINE_ID: &str = "lambda7";
const PLATFORM: &str = "linux-x86_64";
const LIVENESS_BOUND_S: u64 = 14_400;

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParsedSimulation {
    copy_lend_mode: String,
    program: String,
    field_key: String,
    field_slot: usize,
    baseline_kind: SlotKind,
    baseline_force: String,
    baseline_core_families: Vec<String>,
    proof_eligible: bool,
    proof_reason: String,
    selected_labels: Vec<String>,
    source_indices: Vec<usize>,
    necessary_labels: usize,
    relaxed_force: String,
    relaxed_kind: Option<SlotKind>,
    relaxed_core_families: Vec<String>,
    relaxed_core_labels: Vec<String>,
}

fn parse_list(value: &str) -> Vec<String> {
    if value.is_empty() {
        Vec::new()
    } else {
        value.split('|').map(str::to_owned).collect()
    }
}

fn parse_simulation(
    path: &Path,
    expected_program: Option<&str>,
) -> Result<Vec<ParsedSimulation>, String> {
    const HEADER: &str = "copy_lend_mode\tprogram\tfield_key\tfield_slot\tbaseline_kind\tbaseline_force\tbaseline_core_families\tproof_eligible\tproof_reason\tselected_own_assumes\tsource_selector_indices\tnecessary_labels\trelaxed_force\trelaxed_kind\trelaxed_core_families\trelaxed_core_labels";
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read simulation {}: {error}", path.display()))?;
    let mut lines = input.lines();
    if lines.next() != Some(HEADER) {
        return Err(format!("simulation header drift: {}", path.display()));
    }
    let mut rows = Vec::new();
    let mut identities = BTreeSet::new();
    for (offset, line) in lines.enumerate() {
        let columns = line.split('\t').collect::<Vec<_>>();
        if columns.len() != 16 {
            return Err(format!(
                "simulation {} line {} has {} columns",
                path.display(),
                offset + 2,
                columns.len()
            ));
        }
        if !matches!(columns[0], "baseline" | "removal_only" | "lend_arm") {
            return Err(format!(
                "simulation {} line {} copy-lend mode drift",
                path.display(),
                offset + 2
            ));
        }
        if expected_program.is_some_and(|program| columns[1] != program) {
            return Err(format!(
                "simulation {} line {} program mismatch",
                path.display(),
                offset + 2
            ));
        }
        if !identities.insert((columns[1].to_owned(), columns[2].to_owned())) {
            return Err(format!(
                "simulation {} line {} duplicates an identity",
                path.display(),
                offset + 2
            ));
        }
        let relaxed_kind = match columns[13] {
            "-" => None,
            kind => Some(parse_kind(kind)?),
        };
        let source_indices = if columns[10].is_empty() {
            Vec::new()
        } else {
            columns[10]
                .split('|')
                .map(|value| {
                    value.parse::<usize>().map_err(|error| {
                        format!("simulation {} source index: {error}", path.display())
                    })
                })
                .collect::<Result<Vec<_>, _>>()?
        };
        let proof_eligible = columns[7]
            .parse::<bool>()
            .map_err(|error| format!("simulation {} proof flag: {error}", path.display()))?;
        let row = ParsedSimulation {
            copy_lend_mode: columns[0].to_owned(),
            program: columns[1].to_owned(),
            field_key: columns[2].to_owned(),
            field_slot: columns[3]
                .parse()
                .map_err(|error| format!("simulation {} field slot: {error}", path.display()))?,
            baseline_kind: parse_kind(columns[4])?,
            baseline_force: columns[5].to_owned(),
            baseline_core_families: parse_list(columns[6]),
            proof_eligible,
            proof_reason: columns[8].to_owned(),
            selected_labels: parse_list(columns[9]),
            source_indices,
            necessary_labels: columns[11].parse().map_err(|error| {
                format!("simulation {} necessary labels: {error}", path.display())
            })?,
            relaxed_force: columns[12].to_owned(),
            relaxed_kind,
            relaxed_core_families: parse_list(columns[14]),
            relaxed_core_labels: parse_list(columns[15]),
        };
        if !matches!(row.baseline_force.as_str(), "sat" | "unsat") {
            return Err(format!(
                "simulation {} contains invalid baseline verdict {:?}",
                path.display(),
                row.baseline_force
            ));
        }
        if !matches!(
            row.relaxed_force.as_str(),
            "sat" | "unsat" | "borrow-replay-decline"
        ) {
            return Err(format!(
                "simulation {} contains invalid relaxed verdict {:?}",
                path.display(),
                row.relaxed_force
            ));
        }
        if row.proof_eligible != !row.selected_labels.is_empty() {
            return Err(format!(
                "simulation {} proof/selector mismatch for {}",
                path.display(),
                row.field_key
            ));
        }
        rows.push(row);
    }
    Ok(rows)
}

fn sha256(path: &Path) -> Result<String, String> {
    let output = Command::new("sha256sum")
        .arg(path)
        .output()
        .map_err(|error| format!("run sha256sum for {}: {error}", path.display()))?;
    if !output.status.success() {
        return Err(format!(
            "sha256sum failed for {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .next()
        .map(str::to_owned)
        .ok_or_else(|| format!("sha256sum emitted no digest for {}", path.display()))
}

fn write_manifest(dir: &Path, files: &[&str]) -> Result<String, String> {
    let mut lines = String::new();
    for file in files {
        let path = dir.join(file);
        if !path.is_file() {
            return Err(format!("manifest input missing: {}", path.display()));
        }
        lines.push_str(&format!("{}  ./{file}\n", sha256(&path)?));
    }
    let manifest = dir.join("artifact-manifest.sha256");
    fs::write(&manifest, lines)
        .map_err(|error| format!("write {}: {error}", manifest.display()))?;
    sha256(&manifest)
}

fn verify_manifest(dir: &Path) -> Result<String, String> {
    let manifest = dir.join("artifact-manifest.sha256");
    if !manifest.is_file() {
        return Err(format!("manifest missing: {}", manifest.display()));
    }
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
    sha256(&manifest)
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

fn completed_receipt(receipt: &BTreeMap<String, String>) -> Result<(), String> {
    let require = |key: &str, expected: &str| {
        let actual = receipt.get(key).map(String::as_str);
        if actual == Some(expected) {
            Ok(())
        } else {
            Err(format!(
                "receipt {key}: expected {expected:?}, got {actual:?}"
            ))
        }
    };
    require("status", "ok")?;
    require("data", "true")?;
    require("checkpoint_data", "false")?;
    require("machine_id", MACHINE_ID)?;
    require("platform", PLATFORM)?;
    require("memory_limit", "uncapped")?;
    require("wall_cap_s", "14400")
}

fn last_phase(stderr: &str) -> (String, String) {
    let Some(line) = stderr
        .lines()
        .filter(|line| line.starts_with("BOC1PHASE a4-probe "))
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

struct CensusContract {
    run_root: PathBuf,
    accepted_root: PathBuf,
    baseline_path: PathBuf,
    baseline: Vec<AcceptedBaseline>,
    programs: Vec<super::CorpusProgram>,
    head: String,
}

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

fn census_contract() -> CensusContract {
    use super::orchestrate::{git_dirty, git_sha, out_dir, workspace_root};

    assert_eq!(
        std::env::var("CRAT_BO_REPAIR").as_deref(),
        Ok("mode_a"),
        "A4 simulation requires Mode-A"
    );
    assert_eq!(
        std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
        Ok("0"),
        "A4 simulation requires L2 explicitly off"
    );
    assert_eq!(
        std::env::var("CRAT_BOC1_SUBSTRATE").as_deref(),
        Ok("derived"),
        "A4 simulation requires the derived substrate"
    );
    assert_eq!(
        std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
        Ok("uncapped"),
        "A4 Linux measurement is uncapped"
    );
    let timeout = std::env::var("CRAT_A4_TIMEOUT_S")
        .unwrap_or_else(|_| LIVENESS_BOUND_S.to_string())
        .parse::<u64>()
        .expect("CRAT_A4_TIMEOUT_S is an integer");
    assert_eq!(
        timeout, LIVENESS_BOUND_S,
        "A4 wall cap is a 14,400-second liveness bound"
    );
    assert_eq!(
        command_stdout(Command::new("hostname"), "read hostname"),
        MACHINE_ID,
        "A4 machine identity drift"
    );
    assert_eq!(
        format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH),
        PLATFORM,
        "A4 platform identity drift"
    );
    assert!(
        !git_dirty(),
        "A4 harness tree must be clean before measurement"
    );
    let head = git_sha();
    let mut contains = Command::new("git");
    contains
        .args(["branch", "-r", "--contains", &head])
        .current_dir(workspace_root());
    let remote_branches = command_stdout(contains, "locate published A4 head");
    assert!(
        remote_branches
            .lines()
            .any(|line| line.trim() == "origin/codex/a4-predicted-layer-simulation"),
        "A4 harness head {head} is not published on its task branch"
    );

    let run_root =
        PathBuf::from(std::env::var_os("CRAT_A4_RUN_ROOT").expect("A4 requires CRAT_A4_RUN_ROOT"));
    assert!(run_root.is_absolute(), "A4 run root must be absolute");
    assert!(
        !run_root.starts_with(workspace_root()),
        "A4 run root must live outside the code worktree"
    );
    assert_eq!(
        out_dir(),
        run_root,
        "CRAT_BOC1_OUT must equal CRAT_A4_RUN_ROOT"
    );
    let accepted_root = PathBuf::from(
        std::env::var_os("CRAT_A4_ACCEPTED_ROOT").expect("A4 accepted P2 aggregate root"),
    );
    let accepted_manifest = verify_manifest(&accepted_root)
        .unwrap_or_else(|error| panic!("A4 STOP phase=input-manifest candidate=none: {error}"));
    assert_eq!(
        accepted_manifest, ACCEPTED_AGGREGATE_MANIFEST_SHA256,
        "A4 STOP phase=input-manifest candidate=none: accepted aggregate identity drift"
    );
    let baseline_path = accepted_root.join("combined-probes.tsv");
    let baseline = parse_accepted_baseline(&baseline_path)
        .unwrap_or_else(|error| panic!("A4 STOP phase=input-schema candidate=none: {error}"));
    assert_eq!(
        baseline
            .iter()
            .filter(|row| row.force_result == ForceResult::Unsat)
            .count(),
        257
    );
    assert_eq!(
        baseline
            .iter()
            .filter(|row| row.force_result == ForceResult::Sat)
            .count(),
        4
    );
    let program_names = baseline
        .iter()
        .map(|row| row.program.as_str())
        .collect::<BTreeSet<_>>();
    let programs = super::CORPUS
        .iter()
        .copied()
        .filter(|program| program_names.contains(program.name))
        .collect::<Vec<_>>();
    assert_eq!(
        programs.len(),
        18,
        "A4 query population must span 18 programs"
    );
    assert_eq!(
        programs
            .iter()
            .map(|program| program.name)
            .collect::<BTreeSet<_>>(),
        program_names,
        "A4 program population drift"
    );
    assert!(
        workspace_root()
            .join("deps_crate/target/debug/deps")
            .is_dir(),
        "A4 deps_crate build is missing"
    );
    assert!(Path::new(SNAPSHOT_PATH).is_dir(), "A4 snapshot is missing");
    CensusContract {
        run_root,
        accepted_root,
        baseline_path,
        baseline,
        programs,
        head,
    }
}

fn expected_program_rows<'a>(
    baseline: &'a [AcceptedBaseline],
    program: &str,
) -> Vec<&'a AcceptedBaseline> {
    baseline
        .iter()
        .filter(|row| row.program == program)
        .collect()
}

fn validate_shard_rows(
    rows: &[ParsedSimulation],
    expected: &[&AcceptedBaseline],
) -> Result<(), String> {
    let actual_identity = rows
        .iter()
        .map(|row| (row.program.as_str(), row.field_key.as_str(), row.field_slot))
        .collect::<BTreeSet<_>>();
    let expected_identity = expected
        .iter()
        .map(|row| (row.program.as_str(), row.field_key.as_str(), row.field_slot))
        .collect::<BTreeSet<_>>();
    if actual_identity != expected_identity {
        return Err(format!(
            "shard identity mismatch: expected={} actual={}",
            expected_identity.len(),
            actual_identity.len()
        ));
    }
    for row in rows {
        let accepted = expected
            .iter()
            .find(|expected| expected.field_key == row.field_key)
            .expect("identity already checked");
        if row.baseline_kind != accepted.accepted_kind
            || row.baseline_force != accepted.force_result.label()
            || row.baseline_core_families != accepted.core_families
        {
            return Err(format!("selector-off baseline drift for {}", row.field_key));
        }
        if row.baseline_force == "sat"
            && (row.proof_eligible
                || !row.selected_labels.is_empty()
                || !row.source_indices.is_empty()
                || row.relaxed_force != "sat"
                || row.relaxed_kind != Some(row.baseline_kind))
        {
            return Err(format!("force-SAT exception changed at {}", row.field_key));
        }
    }
    Ok(())
}

fn preserve_failed_shard(
    dir: &Path,
    program: &str,
    status: &str,
    phase: &str,
    candidate: &str,
    wall_s: f64,
    peak_rss_kb: u64,
    head: &str,
) -> String {
    let receipt = format!(
        "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nmemory_limit=uncapped\nwall_bound_kind=liveness\nwall_cap_s={LIVENESS_BOUND_S}\nprogram={program}\nstatus={status}\ndata=false\ncheckpoint_data=false\nanalysis_head={head}\nlast_phase={phase}\nlast_candidate={candidate}\nwall_s={wall_s:.3}\npeak_rss_kb={peak_rss_kb}\n"
    );
    fs::write(dir.join("receipt.txt"), receipt).expect("write failed A4 receipt");
    let mut files = vec!["receipt.txt"];
    if dir.join("result.tsv").is_file() {
        files.push("result.tsv");
    }
    if dir.join("partial.tsv").is_file() {
        files.push("partial.tsv");
    }
    if dir.join("partial.tsv.tmp").is_file() {
        files.push("partial.tsv.tmp");
    }
    write_manifest(dir, &files).expect("manifest failed A4 shard")
}

fn run_program_shard(contract: &CensusContract, program: super::CorpusProgram) {
    use super::orchestrate::{run_child_env, workspace_root};

    let dir = contract.run_root.join("shards").join(program.name);
    if dir.is_dir() {
        let manifest = verify_manifest(&dir).unwrap_or_else(|error| {
            panic!(
                "A4 STOP phase=verified-skip candidate={}::<shard>: {error}",
                program.name
            )
        });
        let receipt = parse_receipt(&dir.join("receipt.txt")).unwrap_or_else(|error| {
            panic!(
                "A4 STOP phase=verified-skip candidate={}::<receipt>: {error}",
                program.name
            )
        });
        completed_receipt(&receipt).unwrap_or_else(|error| {
            panic!(
                "A4 STOP phase=verified-skip candidate={}::<data>: {error}",
                program.name
            )
        });
        let rows =
            parse_simulation(&dir.join("result.tsv"), Some(program.name)).unwrap_or_else(|error| {
                panic!(
                    "A4 STOP phase=verified-skip candidate={}: {error}",
                    program.name
                )
            });
        validate_shard_rows(
            &rows,
            &expected_program_rows(&contract.baseline, program.name),
        )
        .unwrap_or_else(|error| {
            panic!(
                "A4 STOP phase=verified-skip candidate={}: {error}",
                program.name
            )
        });
        eprintln!(
            "A4 verified-skip program={} manifest={manifest}",
            program.name
        );
        return;
    }
    fs::create_dir_all(dir.parent().expect("A4 shard parent")).expect("create A4 shard parent");
    fs::create_dir(&dir).expect("create fresh A4 shard");
    let artifact = dir.join("result.tsv");
    let checkpoint = dir.join("partial.tsv");
    let input = workspace_root()
        .join("benchmarks/rs-crown-derived")
        .join(program.name)
        .join(program.lib_root);
    let outcome = run_child_env(
        program.name,
        &input,
        "a4-probe",
        Duration::from_secs(LIVENESS_BOUND_S),
        &[
            (
                "CRAT_A4_ACCEPTED_BASELINE",
                contract.baseline_path.display().to_string(),
            ),
            ("CRAT_A4_ARTIFACT", artifact.display().to_string()),
            ("CRAT_A4_CHECKPOINT", checkpoint.display().to_string()),
        ],
    );
    let (phase, candidate) = last_phase(&outcome.stderr);
    if outcome.status != "ok" {
        let manifest = preserve_failed_shard(
            &dir,
            program.name,
            &outcome.status,
            &phase,
            &candidate,
            outcome.wall_s,
            outcome.peak_rss_kb,
            &contract.head,
        );
        panic!(
            "A4 STOP phase={phase} candidate={candidate} program={} status={} wall_s={:.3} peak_rss_kb={} manifest={manifest}",
            program.name, outcome.status, outcome.wall_s, outcome.peak_rss_kb
        );
    }
    let rows = parse_simulation(&artifact, Some(program.name)).unwrap_or_else(|error| {
        preserve_failed_shard(
            &dir,
            program.name,
            "schema-violation",
            "result-schema",
            program.name,
            outcome.wall_s,
            outcome.peak_rss_kb,
            &contract.head,
        );
        panic!(
            "A4 STOP phase=result-schema candidate={}: {error}",
            program.name
        )
    });
    let expected = expected_program_rows(&contract.baseline, program.name);
    validate_shard_rows(&rows, &expected).unwrap_or_else(|error| {
        preserve_failed_shard(
            &dir,
            program.name,
            "identity-mismatch",
            "result-identity",
            program.name,
            outcome.wall_s,
            outcome.peak_rss_kb,
            &contract.head,
        );
        panic!(
            "A4 STOP phase=result-identity candidate={}: {error}",
            program.name
        )
    });
    assert_eq!(
        fs::read(&artifact).expect("read A4 result"),
        fs::read(&checkpoint).expect("read A4 checkpoint"),
        "A4 STOP phase=checkpoint-identity candidate={}: final/checkpoint drift",
        program.name
    );
    assert!(
        !checkpoint_temp_path(&checkpoint).exists(),
        "A4 STOP phase=checkpoint-publish candidate={}: temporary survived",
        program.name
    );
    let receipt = format!(
        "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nmemory_limit=uncapped\nwall_bound_kind=liveness\nwall_cap_s={LIVENESS_BOUND_S}\nprogram={}\nstatus=ok\ndata=true\ncheckpoint_data=false\nanalysis_head={}\naccepted_aggregate_manifest_sha256={ACCEPTED_AGGREGATE_MANIFEST_SHA256}\ncandidate_universe_sha256={CANDIDATE_UNIVERSE_SHA256}\nraw_corpus_digest={RAW_CORPUS_DIGEST}\nderived_substrate_digest={DERIVED_SUBSTRATE_DIGEST}\nsnapshot={SNAPSHOT_PATH}\nqueried={}\nproof_eligible={}\nflipped_sat={}\nborrow_replay_decline={}\nlast_phase={phase}\nlast_candidate={candidate}\nwall_s={:.3}\npeak_rss_kb={}\n",
        program.name,
        contract.head,
        rows.len(),
        rows.iter().filter(|row| row.proof_eligible).count(),
        rows.iter()
            .filter(|row| row.baseline_force == "unsat" && row.relaxed_force == "sat")
            .count(),
        rows.iter()
            .filter(|row| row.relaxed_force == "borrow-replay-decline")
            .count(),
        outcome.wall_s,
        outcome.peak_rss_kb,
    );
    fs::write(dir.join("receipt.txt"), receipt).expect("write completed A4 receipt");
    let manifest = write_manifest(&dir, &["result.tsv", "partial.tsv", "receipt.txt"])
        .expect("manifest completed A4 shard");
    eprintln!(
        "A4 completed program={} rows={} wall_s={:.3} peak_rss_kb={} manifest={manifest}",
        program.name,
        rows.len(),
        outcome.wall_s,
        outcome.peak_rss_kb
    );
}

fn aggregate(contract: &CensusContract) {
    let aggregate_dir = contract.run_root.join("aggregate");
    assert!(
        !aggregate_dir.exists(),
        "A4 aggregate already exists; completed artifacts are immutable"
    );
    fs::create_dir(&aggregate_dir).expect("create A4 aggregate directory");
    let mut all_rows = Vec::new();
    let mut combined = String::new();
    let mut shard_manifests = Vec::new();
    let mut receipts = Vec::new();
    for program in &contract.programs {
        let dir = contract.run_root.join("shards").join(program.name);
        shard_manifests.push((
            program.name,
            verify_manifest(&dir).expect("verify A4 shard"),
        ));
        let receipt = parse_receipt(&dir.join("receipt.txt")).expect("parse A4 receipt");
        completed_receipt(&receipt).expect("A4 aggregate accepts completed data only");
        receipts.push(receipt);
        let input = fs::read_to_string(dir.join("result.tsv")).expect("read A4 shard result");
        let mut lines = input.lines();
        let header = lines.next().expect("A4 shard header");
        if combined.is_empty() {
            combined.push_str(header);
            combined.push('\n');
        } else {
            assert_eq!(
                combined.lines().next(),
                Some(header),
                "A4 shard header drift"
            );
        }
        for line in lines {
            combined.push_str(line);
            combined.push('\n');
        }
        all_rows.extend(
            parse_simulation(&dir.join("result.tsv"), Some(program.name))
                .expect("parse manifested A4 shard"),
        );
    }
    assert_eq!(all_rows.len(), 261, "A4 aggregate must contain 261 rows");
    let actual = all_rows
        .iter()
        .map(|row| BaselineRow {
            program: row.program.clone(),
            field_key: row.field_key.clone(),
        })
        .collect::<Vec<_>>();
    let expected = contract
        .baseline
        .iter()
        .map(|row| BaselineRow {
            program: row.program.clone(),
            field_key: row.field_key.clone(),
        })
        .collect::<Vec<_>>();
    validate_complete_baseline(&expected, &actual).expect("A4 aggregate exact identity");
    let exceptions = all_rows
        .iter()
        .filter(|row| row.baseline_force == "sat")
        .collect::<Vec<_>>();
    assert_eq!(exceptions.len(), 4, "A4 exception population drift");
    assert!(exceptions.iter().all(|row| {
        !row.proof_eligible
            && row.selected_labels.is_empty()
            && row.source_indices.is_empty()
            && row.relaxed_force == "sat"
            && row.relaxed_kind == Some(row.baseline_kind)
    }));
    let eligible = all_rows.iter().filter(|row| row.proof_eligible).count();
    let flips = all_rows
        .iter()
        .filter(|row| row.baseline_force == "unsat" && row.relaxed_force == "sat")
        .count();
    let borrow_declines = all_rows
        .iter()
        .filter(|row| row.relaxed_force == "borrow-replay-decline")
        .count();
    let hard_after = all_rows
        .iter()
        .filter(|row| row.baseline_force == "unsat" && row.relaxed_force == "unsat")
        .count();
    assert_eq!(hard_after + flips + borrow_declines, 257);
    let own_assume_after = all_rows
        .iter()
        .filter(|row| row.relaxed_force == "unsat")
        .filter(|row| {
            row.relaxed_core_families
                .iter()
                .any(|family| family == "own-assume")
        })
        .count();
    let link_own_after = all_rows
        .iter()
        .filter(|row| row.relaxed_force == "unsat")
        .filter(|row| {
            row.relaxed_core_families
                .iter()
                .any(|family| family == "link-own")
        })
        .count();

    let mut per_program = String::from(
        "program\tcandidates\tproof_eligible\tflipped_sat\tborrow_replay_decline\thard_after\tforce_sat_exception\twall_s\tpeak_rss_kb\n",
    );
    for (program, receipt) in contract.programs.iter().zip(&receipts) {
        let rows = all_rows
            .iter()
            .filter(|row| row.program == program.name)
            .collect::<Vec<_>>();
        let count = |predicate: fn(&ParsedSimulation) -> bool| {
            rows.iter().filter(|row| predicate(row)).count()
        };
        per_program.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            program.name,
            rows.len(),
            count(|row| row.proof_eligible),
            count(|row| row.baseline_force == "unsat" && row.relaxed_force == "sat"),
            count(|row| row.relaxed_force == "borrow-replay-decline"),
            count(|row| row.baseline_force == "unsat" && row.relaxed_force == "unsat"),
            count(|row| row.baseline_force == "sat"),
            receipt.get("wall_s").expect("receipt wall"),
            receipt.get("peak_rss_kb").expect("receipt RSS"),
        ));
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
    let report = format!(
        "# A4 predicted-layer simulation\n\n- Machine `{MACHINE_ID}`, platform `{PLATFORM}`; uncapped RAM/CPU with a {LIVENESS_BOUND_S}-second per-program liveness bound. Timings are machine-local and not compared across machines.\n- Selector-off identity: **261/261 exact** against accepted P2 manifest `{ACCEPTED_AGGREGATE_MANIFEST_SHA256}`.\n- Baseline partition: **257 hard-UNSAT + 4 force-SAT + 0 Unknown**.\n- Exact proof selector: **{eligible}/257** hard rows eligible.\n- Predicted repair yield: **{flips}/257** hard rows flip to force-SAT and pass normal borrow replay; **{borrow_declines}** reach ownership SAT but decline in replay; **{hard_after}** remain ownership hard-UNSAT.\n- Four known force-SAT exceptions remain selector-empty and stable.\n- Remaining hard-UNSAT core incidence: `own-assume` **{own_assume_after}/{hard_after}**, `link-own` **{link_own_after}/{hard_after}**.\n- Sequential shard wall sum: **{total_wall:.3}s**; maximum observed worker RSS: **{peak_rss} KiB**.\n\nOnly completed, SHA-256-manifested `data=true` shards feed this aggregate. Atomic partial checkpoints are `data=false` provenance and are excluded. Production analysis and rewriter code remained untouched.\n"
    );
    let provenance = format!(
        "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nanalysis_head={}\nanalysis_branch=codex/a4-predicted-layer-simulation\nbaseline_branch=analysis-lane\nbaseline_head=bc31ac186fce5fb7e95d9e3db083174f514fd8ab\naccepted_root={}\naccepted_aggregate_manifest_sha256={ACCEPTED_AGGREGATE_MANIFEST_SHA256}\ncandidate_universe_sha256={CANDIDATE_UNIVERSE_SHA256}\nraw_corpus_digest={RAW_CORPUS_DIGEST}\nderived_substrate_digest={DERIVED_SUBSTRATE_DIGEST}\nsnapshot={SNAPSHOT_PATH}\nmemory_limit=uncapped\nwall_bound_kind=liveness\nwall_cap_s={LIVENESS_BOUND_S}\nprograms={}\nqueried=261\nbaseline_hard_unsat=257\nbaseline_force_sat=4\nproof_eligible={eligible}\nflipped_sat={flips}\nborrow_replay_decline={borrow_declines}\nhard_after={hard_after}\nown_assume_core_incidence_after={own_assume_after}\nlink_own_core_incidence_after={link_own_after}\nwall_sum_s={total_wall:.3}\npeak_rss_kb={peak_rss}\nshard_manifests={}\naggregation_input_policy=manifested-published-completed-data-true-only\ntiming_comparison=forbidden-across-machines\n",
        contract.head,
        contract.accepted_root.display(),
        contract.programs.len(),
        shard_manifests
            .iter()
            .map(|(program, digest)| format!("{program}:{digest}"))
            .collect::<Vec<_>>()
            .join(","),
    );
    fs::write(aggregate_dir.join("combined.tsv"), combined).expect("write A4 combined");
    fs::write(aggregate_dir.join("per-program.tsv"), per_program).expect("write A4 per-program");
    fs::write(aggregate_dir.join("report.md"), report).expect("write A4 report");
    fs::write(aggregate_dir.join("provenance.txt"), provenance).expect("write A4 provenance");
    let manifest = write_manifest(
        &aggregate_dir,
        &[
            "combined.tsv",
            "per-program.tsv",
            "report.md",
            "provenance.txt",
        ],
    )
    .expect("write A4 aggregate manifest");
    eprintln!(
        "A4 aggregate complete manifest={manifest} eligible={eligible} flips={flips} borrow_declines={borrow_declines} hard_after={hard_after}"
    );
}

#[test]
#[ignore = "A4 predicted-layer census; run sequentially on the dedicated Linux lane"]
fn a4_predicted_layer_census() {
    let contract = census_contract();
    if !contract.run_root.exists() {
        fs::create_dir(&contract.run_root).expect("create fresh A4 run root");
    }
    for &program in &contract.programs {
        run_program_shard(&contract, program);
    }
    aggregate(&contract);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(program: &str, field_key: &str) -> BaselineRow {
        BaselineRow {
            program: program.to_owned(),
            field_key: field_key.to_owned(),
        }
    }

    fn unique_path(steps: Vec<PathStep>) -> StoreProof {
        StoreProof {
            surviving_local_sources: 1,
            steps,
            competing_live_use: false,
        }
    }

    #[test]
    fn a4_unique_allocation_move_store_is_selector_eligible() {
        assert!(exact_relaxation_is_eligible(&[unique_path(vec![
            PathStep::Move
        ])]));
        assert!(exact_relaxation_is_eligible(&[unique_path(vec![
            PathStep::Copy { sole_use: true }
        ])]));
        assert!(exact_relaxation_is_eligible(&[unique_path(vec![
            PathStep::Cast {
                pointer_depth_preserved: true,
            }
        ])]));
    }

    #[test]
    fn a4_copy_merge_opaque_realloc_and_unresolved_paths_fail_closed() {
        for step in [
            PathStep::Copy { sole_use: false },
            PathStep::Cast {
                pointer_depth_preserved: false,
            },
            PathStep::Join,
            PathStep::OpaqueCall,
            PathStep::Realloc,
            PathStep::UnresolvedStore,
        ] {
            assert!(!exact_relaxation_is_eligible(&[unique_path(vec![step])]));
        }
        assert!(!exact_relaxation_is_eligible(&[StoreProof {
            surviving_local_sources: 2,
            steps: vec![PathStep::Move],
            competing_live_use: false,
        }]));
        assert!(!exact_relaxation_is_eligible(&[StoreProof {
            surviving_local_sources: 1,
            steps: vec![PathStep::Move],
            competing_live_use: true,
        }]));
        assert!(!exact_relaxation_is_eligible(&[]));
    }

    #[test]
    fn a4_completed_data_gate_has_two_sided_witness() {
        let expected = vec![row("a", "f0"), row("b", "f1")];
        assert!(validate_complete_baseline(&expected, &expected).is_ok());
        assert!(validate_complete_baseline(&expected, &expected[..1]).is_err());

        let complete = BTreeMap::from([
            ("status".to_owned(), "ok".to_owned()),
            ("data".to_owned(), "true".to_owned()),
            ("checkpoint_data".to_owned(), "false".to_owned()),
            ("machine_id".to_owned(), MACHINE_ID.to_owned()),
            ("platform".to_owned(), PLATFORM.to_owned()),
            ("memory_limit".to_owned(), "uncapped".to_owned()),
            ("wall_cap_s".to_owned(), "14400".to_owned()),
        ]);
        assert!(completed_receipt(&complete).is_ok());
        let mut incomplete = complete;
        incomplete.insert("data".to_owned(), "false".to_owned());
        assert!(completed_receipt(&incomplete).is_err());
    }

    #[test]
    fn a4_checkpoint_write_is_atomic_and_observable() {
        let root =
            std::env::temp_dir().join(format!("crat-a4-checkpoint-control-{}", std::process::id()));
        fs::create_dir_all(&root).expect("create checkpoint control directory");
        let path = root.join("partial.tsv");
        write_atomic_checkpoint(&path, "phase\tcandidate\nsolve\tfixture\n")
            .expect("publish checkpoint");
        assert_eq!(
            fs::read_to_string(&path).expect("read checkpoint"),
            "phase\tcandidate\nsolve\tfixture\n"
        );
        assert!(!checkpoint_temp_path(&path).exists());
        let marker = phase_line(Instant::now(), "checkpoint-written", Some("fixture"), 1);
        assert!(marker.contains("phase=checkpoint-written"));
        assert!(marker.contains("candidate=fixture"));
        assert!(marker.contains("completed=1"));
        fs::remove_file(path).expect("remove checkpoint artifact");
        fs::remove_dir(root).expect("remove checkpoint control directory");
    }
}
