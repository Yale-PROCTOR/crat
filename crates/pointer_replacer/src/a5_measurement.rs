use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    time::{Duration, Instant},
};

use points_to::andersen::{self, Var};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, TerminatorKind},
    ty::TyCtxt,
};
use rustc_type_ir::TyKind;
use sha2::{Digest, Sha256};

use crate::{
    analyses::{
        borrow::lifetime_flow::{self, BodyLifetimeFlow},
        borrow_ownership::{
            SlotKind,
            a5_overlap::{
                A5Mode, A5World, C9MarkKey, PairClass, PairFacts, PairSide, SetPairEvidence,
                SnapshotVerdict, WholeProgramAttestation, classify_pair,
            },
            a5_producer::{audit_a5_site_branches, produce_a5_plan},
            a5_snapshot_effects::snapshot_verdict_for_target,
            borrow_engine::ParameterOverlap,
            borrow_verify::revalidate_replaying_with_parameter_overlap,
            construction::{
                CopyLendMode, a5_site_artifact, construct_bo_into, verify_bo_construction,
                verify_bo_construction_with_parameter_overlaps,
            },
            crate_slots::CrateSlots,
            export::with_bo_export,
            l2::{MirLocationKey, SlotKey},
            mutability_facts::MutFacts,
            origins::compute_origins,
            resolve::{ResolvedSlot, resolve_place},
            slots::SlotId,
            solver::{KindSolver, SlotRef},
        },
    },
    coverage_recon::schema::Outcome,
    utils::rustc::RustProgram,
};

#[path = "analyses/borrow/places_conflict.rs"]
#[allow(dead_code)]
mod projection_conflict;

use projection_conflict::{AccessDepth, PlaceConflictBias, places_conflict};

const COUNT_SENTINEL: &str = "A5P1 ";
const BASE_SENTINEL: &str = "A5P1BASE ";
const PAIR_SENTINEL: &str = "A5P1PAIR\t";
const W14_PAIR_SENTINEL: &str = "A5W14PAIR\t";
const W14_EXPOSURE_SENTINEL: &str = "A5W14EXPOSURE\t";
const REPLAY_SAFE_DEFINITION: &str = "no incompatible access derived by precise replay with the effective parameter-overlap map injected; O2 closed-world frozen graph.";
const CLOSED_WORLD_FRAME_UNKNOWN_REACHABLE: usize = 2_318;
const CLOSED_WORLD_FRAME_LOCAL_FUNCTIONS: usize = 2_456;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FormalKey {
    function: String,
    parameter: u32,
    depth: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FormalDecision {
    settles_ref: bool,
    currently_predicted_refs: BTreeSet<FormalKey>,
    mutable: bool,
    mutability_default_fires: usize,
}

fn join_formal_mutability(values: impl IntoIterator<Item = Option<bool>>) -> (bool, usize) {
    let mut mutable = false;
    let mut default_fires = 0;
    for value in values {
        match value {
            Some(value) => mutable |= value,
            None => {
                mutable = true;
                default_fires += 1;
            }
        }
    }
    (mutable, default_fires)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ArtifactFormal {
    settles_ref: bool,
    currently_predicted_ref: bool,
    ptr_depth: u8,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct CoverageCounts {
    calls_total: usize,
    direct_local: usize,
    indirect_local: usize,
    direct_external: usize,
    indirect_unresolved: usize,
    non_fn_def_constant: usize,
}

impl CoverageCounts {
    fn validate(&self) -> Result<(), String> {
        let classified = self.direct_local
            + self.indirect_local
            + self.direct_external
            + self.indirect_unresolved
            + self.non_fn_def_constant;
        if classified != self.calls_total {
            return Err(format!(
                "call coverage mismatch: total={} classified={classified}",
                self.calls_total
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct Timings {
    origins: Duration,
    andersen: Duration,
    accepted_model: Duration,
}

#[derive(Clone, Debug)]
struct Measurement {
    counts: ProgramCounts,
    pairs: Vec<PairLedgerRow>,
    classifier: ClassifierDifferential,
    snapshot: SnapshotCoverage,
    final_marks: Vec<C9MarkKey>,
    w14: Option<W14Measurement>,
    coverage: CoverageCounts,
    timings: Timings,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExposureClass {
    Demoted,
    Marked,
    SharedSafe,
    ReplaySafe,
    Unresolved,
}

impl ExposureClass {
    fn label(self) -> &'static str {
        match self {
            Self::Demoted => "demoted",
            Self::Marked => "marked",
            Self::SharedSafe => "shared-safe",
            Self::ReplaySafe => "replay-safe",
            Self::Unresolved => "unresolved",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExposureLedgerRow {
    program: String,
    formal: FormalKey,
    baseline: SlotKind,
    precise: SlotKind,
    class: ExposureClass,
    effective_mut_mut: bool,
    effective_mut_read_only: bool,
    effective_shared_shared: bool,
}

#[derive(Clone, Debug)]
struct W14Measurement {
    pairs: Vec<ExtendedPairLedgerRow>,
    exposures: Vec<ExposureLedgerRow>,
    precise_rounds: usize,
}

struct BatchPrecise<'a> {
    model: &'a rustc_hash::FxHashMap<SlotRef, SlotKind>,
    planned_marks: &'a BTreeSet<C9MarkKey>,
    model_retained_marks: usize,
    rounds: usize,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct BatchW14Summary {
    pub pair_den: usize,
    pub mut_mut: usize,
    pub mut_read_only: usize,
    pub shared_shared: usize,
    pub effective_pairs: usize,
    pub planned_marks: usize,
    pub model_retained_marks: usize,
    pub exposures: usize,
    pub demoted: usize,
    pub marked: usize,
    pub shared_safe: usize,
    pub replay_safe: usize,
    pub unresolved: usize,
    pub precise_rounds: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct ClassifierDifferential {
    candidates: usize,
    not_proven_disjoint: usize,
    byte_mismatches: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct SnapshotCoverage {
    mut_read_only: usize,
    markable: usize,
    read_after_write: usize,
    opaque_escape: usize,
    recursive: usize,
    volatile_or_atomic: usize,
    unresolved: usize,
    target_type_mismatch: usize,
    noncopy_scalar: usize,
    final_markable: usize,
    all_witness_demoted: usize,
    filter_unresolved: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum PairMutability {
    MutMut,
    MutReadOnly,
    SharedShared,
}

impl PairMutability {
    fn from_sides(left: bool, right: bool) -> PairMutability {
        match (left, right) {
            (true, true) => PairMutability::MutMut,
            (false, false) => PairMutability::SharedShared,
            _ => PairMutability::MutReadOnly,
        }
    }

    fn label(self) -> &'static str {
        match self {
            PairMutability::MutMut => "mut_mut",
            PairMutability::MutReadOnly => "mut_read_only",
            PairMutability::SharedShared => "shared_shared",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PairLedgerRow {
    program: String,
    site: String,
    left_argument: usize,
    right_argument: usize,
    class: PairMutability,
    left_mutable: bool,
    right_mutable: bool,
    left_default_fires: usize,
    right_default_fires: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct TargetFunction {
    key: u32,
    path: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct TargetFormalPair {
    function: TargetFunction,
    left_parameter: u32,
    right_parameter: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExtendedPairLedgerRow {
    pair: PairLedgerRow,
    target_formals: Vec<TargetFormalPair>,
    left_formals: BTreeSet<FormalKey>,
    right_formals: BTreeSet<FormalKey>,
    raw_overlap: bool,
    effective_overlap: bool,
    markability: String,
    planned_mark: bool,
    selected_mark: bool,
    model_attribution: String,
}

impl PairLedgerRow {
    fn validate(&self) -> Result<(), String> {
        if self.program.is_empty()
            || self.site.is_empty()
            || self.program.contains(['\t', '\n', '\r'])
            || self.site.contains(['\t', '\n', '\r'])
        {
            return Err("pair ledger identity contains an empty or control field".to_owned());
        }
        if self.left_argument == 0 || self.left_argument >= self.right_argument {
            return Err("pair ledger arguments are not ordered one-based indices".to_owned());
        }
        if self.class != PairMutability::from_sides(self.left_mutable, self.right_mutable) {
            return Err("pair ledger class disagrees with side mutability".to_owned());
        }
        Ok(())
    }

    fn default_fires(&self) -> usize {
        self.left_default_fires + self.right_default_fires
    }
}

fn classify_pair_legacy(facts: &PairFacts<String>) -> PairClass {
    if facts.storage_alias {
        return PairClass::NotProvenDisjoint;
    }
    let complete_disjoint = |evidence: &SetPairEvidence<String>| {
        let SetPairEvidence::Complete { left, right } = evidence else {
            return false;
        };
        !left.is_empty() && !right.is_empty() && left.is_disjoint(right)
    };
    if facts.projection_disjoint
        || complete_disjoint(&facts.origins)
        || complete_disjoint(&facts.points_to)
    {
        PairClass::ProvenDisjoint
    } else {
        PairClass::NotProvenDisjoint
    }
}

fn classify_pair_differential(facts: &PairFacts<String>) -> Result<PairClass, String> {
    let legacy = classify_pair_legacy(facts);
    let shared = classify_pair(facts);
    if legacy.label().as_bytes() != shared.label().as_bytes() {
        return Err(format!(
            "A5 classifier verdict mismatch: legacy={} shared={}",
            legacy.label(),
            shared.label()
        ));
    }
    Ok(shared)
}

fn combine_snapshot_verdicts(
    verdicts: impl IntoIterator<Item = SnapshotVerdict>,
) -> Option<SnapshotVerdict> {
    let mut seen = false;
    let mut combined = SnapshotVerdict::Markable;
    for verdict in verdicts {
        seen = true;
        combined = match (combined, verdict) {
            (_, SnapshotVerdict::VolatileOrAtomic) => SnapshotVerdict::VolatileOrAtomic,
            (SnapshotVerdict::VolatileOrAtomic, _) => SnapshotVerdict::VolatileOrAtomic,
            (_, SnapshotVerdict::Recursive) => SnapshotVerdict::Recursive,
            (SnapshotVerdict::Recursive, _) => SnapshotVerdict::Recursive,
            (_, SnapshotVerdict::OpaqueEscape) => SnapshotVerdict::OpaqueEscape,
            (SnapshotVerdict::OpaqueEscape, _) => SnapshotVerdict::OpaqueEscape,
            (_, SnapshotVerdict::ReadAfterWrite) => SnapshotVerdict::ReadAfterWrite,
            (SnapshotVerdict::ReadAfterWrite, _) => SnapshotVerdict::ReadAfterWrite,
            _ => SnapshotVerdict::Markable,
        };
    }
    seen.then_some(combined)
}

fn target_type_filters(
    tcx: TyCtxt<'_>,
    targets: &[LocalDefId],
    left: usize,
    right: usize,
) -> (bool, bool) {
    let mut expected = None;
    let mut agree = !targets.is_empty();
    let mut copy_scalar = !targets.is_empty();
    for &target in targets {
        let body = tcx.mir_drops_elaborated_and_const_checked(target).borrow();
        let Some(left_ty) = body
            .local_decls
            .get(Local::from_usize(left + 1))
            .and_then(|d| d.ty.builtin_deref(true))
        else {
            return (false, false);
        };
        let Some(right_ty) = body
            .local_decls
            .get(Local::from_usize(right + 1))
            .and_then(|d| d.ty.builtin_deref(true))
        else {
            return (false, false);
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
    (agree, copy_scalar)
}

fn argument_slot_key<'tcx>(
    slots: &CrateSlots,
    function: LocalDefId,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<SlotKey> {
    let place = operand.place()?;
    let slot = match resolve_place(slots, function, body, place, 0, None)? {
        ResolvedSlot::Local(slot) => SlotRef::Local(function, slot),
        ResolvedSlot::Field(slot) => SlotRef::Field(slot),
    };
    Some(SlotKey::of(slot))
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CallSite {
    id: String,
    targets: Vec<TargetFunction>,
    arguments: Vec<FormalDecision>,
    pair_facts: BTreeMap<(usize, usize), PairFacts<String>>,
    snapshot_verdicts: BTreeMap<(usize, usize), SnapshotVerdict>,
    post_filter: BTreeMap<(usize, usize), (bool, bool)>,
    mark_keys: BTreeMap<(usize, usize), C9MarkKey>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct FunctionNode {
    unknown_caller_root: bool,
    callees: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProgramInput {
    name: String,
    call_sites: Vec<CallSite>,
    functions: BTreeMap<String, FunctionNode>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ProgramCounts {
    program: String,
    sites_with_two_ref_args: usize,
    sites_not_proven_disjoint: usize,
    attributed_predicted_refs: usize,
    attributed_predicted_refs_depth0: usize,
    unknown_caller_reachable: usize,
    local_functions: usize,
    pair_denominator: usize,
    mut_mut: usize,
    mut_read_only: usize,
    shared_shared: usize,
    sites_with_mut_mut: usize,
    sites_with_mut_read_only: usize,
    sites_with_shared_shared: usize,
    mutability_default_fires: usize,
}

impl ProgramCounts {
    fn validate(&self) -> Result<(), String> {
        if self.program.is_empty() || self.program.chars().any(char::is_whitespace) {
            return Err("program must be a non-empty whitespace-free key".to_owned());
        }
        if self.sites_not_proven_disjoint > self.sites_with_two_ref_args {
            return Err("count 2 exceeds count 1".to_owned());
        }
        if self.attributed_predicted_refs_depth0 > self.attributed_predicted_refs {
            return Err("depth-0 count exceeds the all-depth count".to_owned());
        }
        if self.unknown_caller_reachable > self.local_functions {
            return Err("call-graph numerator exceeds its denominator".to_owned());
        }
        if self.pair_denominator != self.mut_mut + self.mut_read_only + self.shared_shared {
            return Err("count-(5) pair partition does not reconcile".to_owned());
        }
        if self.pair_denominator < self.sites_not_proven_disjoint {
            return Err(
                "count-(5) pair denominator is smaller than its C2 site population".to_owned(),
            );
        }
        if [
            self.sites_with_mut_mut,
            self.sites_with_mut_read_only,
            self.sites_with_shared_shared,
        ]
        .into_iter()
        .any(|count| count > self.sites_not_proven_disjoint)
        {
            return Err("count-(5) site incidence exceeds the C2 site denominator".to_owned());
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MeasuredProgram {
    counts: ProgramCounts,
    pairs: Vec<PairLedgerRow>,
    extended_pairs: Vec<ExtendedPairLedgerRow>,
    classifier: ClassifierDifferential,
    snapshot: SnapshotCoverage,
    final_marks: Vec<C9MarkKey>,
}

fn target_formal_pairs(site: &CallSite, left: usize, right: usize) -> Vec<TargetFormalPair> {
    site.targets
        .iter()
        .cloned()
        .map(|function| TargetFormalPair {
            function,
            left_parameter: left as u32 + 1,
            right_parameter: right as u32 + 1,
        })
        .collect()
}

fn markability_reason(
    site: &CallSite,
    pair: (usize, usize),
    class: PairMutability,
) -> (&'static str, bool) {
    if class == PairMutability::MutMut {
        return ("mut-mut", false);
    }
    if class == PairMutability::SharedShared {
        return ("shared-shared", false);
    }
    match site.snapshot_verdicts.get(&pair) {
        Some(SnapshotVerdict::ReadAfterWrite) => ("read-after-write", false),
        Some(SnapshotVerdict::OpaqueEscape) => ("opaque-escape", false),
        Some(SnapshotVerdict::Recursive) => ("recursive", false),
        Some(SnapshotVerdict::VolatileOrAtomic) => ("volatile-or-atomic", false),
        None => ("snapshot-unresolved", false),
        Some(SnapshotVerdict::Markable) => match site.post_filter.get(&pair) {
            Some((false, _)) => ("target-type-mismatch", false),
            Some((true, false)) => ("noncopy-scalar", false),
            Some((true, true)) if site.mark_keys.contains_key(&pair) => {
                ("markable-candidate", true)
            }
            Some((true, true)) | None => ("filter-unresolved", false),
        },
    }
}

fn measure_program(input: &ProgramInput) -> Result<MeasuredProgram, String> {
    let mut site_ids = BTreeSet::new();
    let mut sites_with_two_ref_args = 0usize;
    let mut sites_not_proven_disjoint = 0usize;
    let mut attributed = BTreeSet::new();
    let mut pairs = Vec::new();
    let mut extended_pairs = Vec::new();
    let mut mut_mut = 0;
    let mut mut_read_only = 0;
    let mut shared_shared = 0;
    let mut sites_with_mut_mut = 0;
    let mut sites_with_mut_read_only = 0;
    let mut sites_with_shared_shared = 0;
    let mut mutability_default_fires = 0;
    let mut classifier = ClassifierDifferential::default();
    let mut snapshot = SnapshotCoverage::default();
    let mut final_marks = Vec::new();
    let mut all_witnesses_markable = BTreeMap::<TargetFormalPair, bool>::new();

    for site in &input.call_sites {
        let ref_args = site
            .arguments
            .iter()
            .enumerate()
            .filter_map(|(index, formal)| formal.settles_ref.then_some(index))
            .collect::<Vec<_>>();
        for (offset, &left) in ref_args.iter().enumerate() {
            for &right in &ref_args[offset + 1..] {
                let facts = site
                    .pair_facts
                    .get(&(left, right))
                    .cloned()
                    .unwrap_or_default();
                if classify_pair(&facts) != PairClass::NotProvenDisjoint {
                    continue;
                }
                let class = PairMutability::from_sides(
                    site.arguments[left].mutable,
                    site.arguments[right].mutable,
                );
                let (_, candidate) = markability_reason(site, (left, right), class);
                for target in target_formal_pairs(site, left, right) {
                    all_witnesses_markable
                        .entry(target)
                        .and_modify(|all| *all &= candidate)
                        .or_insert(candidate);
                }
            }
        }
    }

    for site in &input.call_sites {
        if !site_ids.insert(site.id.as_str()) {
            return Err(format!("duplicate call-site id `{}`", site.id));
        }
        let ref_args = site
            .arguments
            .iter()
            .enumerate()
            .filter_map(|(index, formal)| formal.settles_ref.then_some(index))
            .collect::<Vec<_>>();
        if ref_args.len() < 2 {
            continue;
        }
        sites_with_two_ref_args += 1;

        let mut risky = false;
        let mut site_classes = BTreeSet::new();
        for (offset, &left) in ref_args.iter().enumerate() {
            for &right in &ref_args[offset + 1..] {
                let facts = site
                    .pair_facts
                    .get(&(left, right))
                    .cloned()
                    .unwrap_or_default();
                classifier.candidates += 1;
                let verdict = classify_pair_differential(&facts).map_err(|why| {
                    classifier.byte_mismatches += 1;
                    format!(
                        "{why}; site={} arguments={}/{}",
                        site.id,
                        left + 1,
                        right + 1
                    )
                })?;
                if verdict == PairClass::NotProvenDisjoint {
                    classifier.not_proven_disjoint += 1;
                    risky = true;
                    let left_formal = &site.arguments[left];
                    let right_formal = &site.arguments[right];
                    let class =
                        PairMutability::from_sides(left_formal.mutable, right_formal.mutable);
                    let target_formals = target_formal_pairs(site, left, right);
                    let (local_reason, candidate) = markability_reason(site, (left, right), class);
                    let selected_mark = candidate
                        && !target_formals.is_empty()
                        && target_formals
                            .iter()
                            .all(|pair| all_witnesses_markable.get(pair).copied() == Some(true));
                    match class {
                        PairMutability::MutMut => mut_mut += 1,
                        PairMutability::MutReadOnly => {
                            mut_read_only += 1;
                            snapshot.mut_read_only += 1;
                            match site.snapshot_verdicts.get(&(left, right)) {
                                Some(SnapshotVerdict::Markable) => {
                                    snapshot.markable += 1;
                                    match site.post_filter.get(&(left, right)) {
                                        Some((true, true)) => {
                                            if selected_mark
                                                && let Some(mark) =
                                                    site.mark_keys.get(&(left, right))
                                            {
                                                snapshot.final_markable += 1;
                                                final_marks.push(mark.clone());
                                            } else if candidate {
                                                // A locally markable witness can still be demoted by
                                                // another witness of the same formal pair.
                                                snapshot.all_witness_demoted += 1;
                                            } else {
                                                snapshot.filter_unresolved += 1;
                                            }
                                        }
                                        Some((false, _)) => snapshot.target_type_mismatch += 1,
                                        Some((true, false)) => snapshot.noncopy_scalar += 1,
                                        None => snapshot.filter_unresolved += 1,
                                    }
                                }
                                Some(SnapshotVerdict::ReadAfterWrite) => {
                                    snapshot.read_after_write += 1
                                }
                                Some(SnapshotVerdict::OpaqueEscape) => snapshot.opaque_escape += 1,
                                Some(SnapshotVerdict::Recursive) => snapshot.recursive += 1,
                                Some(SnapshotVerdict::VolatileOrAtomic) => {
                                    snapshot.volatile_or_atomic += 1
                                }
                                None => snapshot.unresolved += 1,
                            }
                        }
                        PairMutability::SharedShared => shared_shared += 1,
                    }
                    site_classes.insert(class);
                    let pair = PairLedgerRow {
                        program: input.name.clone(),
                        site: site.id.clone(),
                        left_argument: left + 1,
                        right_argument: right + 1,
                        class,
                        left_mutable: left_formal.mutable,
                        right_mutable: right_formal.mutable,
                        left_default_fires: left_formal.mutability_default_fires,
                        right_default_fires: right_formal.mutability_default_fires,
                    };
                    pair.validate()?;
                    mutability_default_fires += pair.default_fires();
                    let markability = if selected_mark {
                        "selected-mark"
                    } else if candidate {
                        "all-witness-demotion"
                    } else {
                        local_reason
                    };
                    extended_pairs.push(ExtendedPairLedgerRow {
                        pair: pair.clone(),
                        target_formals,
                        left_formals: left_formal.currently_predicted_refs.clone(),
                        right_formals: right_formal.currently_predicted_refs.clone(),
                        raw_overlap: true,
                        effective_overlap: !selected_mark,
                        markability: markability.to_owned(),
                        planned_mark: selected_mark,
                        selected_mark,
                        model_attribution: "not-evaluated".to_owned(),
                    });
                    pairs.push(pair);
                    for index in [left, right] {
                        let formal = &site.arguments[index];
                        attributed.extend(formal.currently_predicted_refs.iter().cloned());
                    }
                }
            }
        }
        sites_not_proven_disjoint += usize::from(risky);
        sites_with_mut_mut += usize::from(site_classes.contains(&PairMutability::MutMut));
        sites_with_mut_read_only +=
            usize::from(site_classes.contains(&PairMutability::MutReadOnly));
        sites_with_shared_shared +=
            usize::from(site_classes.contains(&PairMutability::SharedShared));
    }

    let reachable = unknown_reachable(&input.functions)?;

    let counts = ProgramCounts {
        program: input.name.clone(),
        sites_with_two_ref_args,
        sites_not_proven_disjoint,
        attributed_predicted_refs: attributed.len(),
        attributed_predicted_refs_depth0: attributed.iter().filter(|key| key.depth == 0).count(),
        unknown_caller_reachable: reachable.len(),
        local_functions: input.functions.len(),
        pair_denominator: pairs.len(),
        mut_mut,
        mut_read_only,
        shared_shared,
        sites_with_mut_mut,
        sites_with_mut_read_only,
        sites_with_shared_shared,
        mutability_default_fires,
    };
    counts.validate()?;
    if classifier.not_proven_disjoint != pairs.len() {
        return Err("shared classifier denominator disagrees with the pair ledger".to_owned());
    }
    extended_pairs.sort_by(|left, right| {
        (
            left.pair.program.as_str(),
            left.pair.site.as_str(),
            left.pair.left_argument,
            left.pair.right_argument,
        )
            .cmp(&(
                right.pair.program.as_str(),
                right.pair.site.as_str(),
                right.pair.left_argument,
                right.pair.right_argument,
            ))
    });
    final_marks.sort();
    Ok(MeasuredProgram {
        counts,
        pairs,
        extended_pairs,
        classifier,
        snapshot,
        final_marks,
    })
}

fn build_parameter_overlaps(
    program: &RustProgram<'_>,
    rows: &[ExtendedPairLedgerRow],
) -> Result<rustc_hash::FxHashMap<LocalDefId, ParameterOverlap>, String> {
    let by_key = program
        .functions
        .iter()
        .copied()
        .map(|did| (did.local_def_index.as_u32(), did))
        .collect::<BTreeMap<_, _>>();
    let mut pairs = rustc_hash::FxHashMap::<LocalDefId, Vec<(Local, Local)>>::default();
    for row in rows.iter().filter(|row| row.effective_overlap) {
        for target in &row.target_formals {
            let did = by_key.get(&target.function.key).copied().ok_or_else(|| {
                format!(
                    "W14 target {} ({}) is outside the local program",
                    target.function.key, target.function.path
                )
            })?;
            pairs.entry(did).or_default().push((
                Local::from_usize(target.left_parameter as usize),
                Local::from_usize(target.right_parameter as usize),
            ));
        }
    }
    Ok(pairs
        .into_iter()
        .map(|(did, pairs)| (did, ParameterOverlap::from_pairs(pairs)))
        .collect())
}

fn build_exposure_ledger(
    program: &str,
    rows: &[ExtendedPairLedgerRow],
    expected_depth_zero: usize,
    baseline: &AcceptedFormalModel,
    precise: &AcceptedFormalModel,
) -> Result<Vec<ExposureLedgerRow>, String> {
    let mut participation = BTreeMap::<FormalKey, Vec<&ExtendedPairLedgerRow>>::new();
    for row in rows {
        for formal in row
            .left_formals
            .iter()
            .chain(&row.right_formals)
            .filter(|formal| formal.depth == 0)
        {
            participation.entry(formal.clone()).or_default().push(row);
        }
    }
    if participation.len() != expected_depth_zero {
        return Err(format!(
            "W14 exposure identity count {} disagrees with C3-d0 {}",
            participation.len(),
            expected_depth_zero
        ));
    }

    let mut answer = Vec::with_capacity(participation.len());
    for (formal, rows) in participation {
        let baseline_kind = baseline
            .kinds
            .get(&formal)
            .copied()
            .ok_or_else(|| format!("W14 baseline lacks {formal:?}"))?;
        if baseline_kind != SlotKind::Ref {
            return Err(format!("W14 exposure {formal:?} is not baseline Ref"));
        }
        let precise_kind = precise
            .kinds
            .get(&formal)
            .copied()
            .ok_or_else(|| format!("W14 precise model lacks {formal:?}"))?;
        let effective_mut_mut = rows
            .iter()
            .any(|row| row.effective_overlap && row.pair.class == PairMutability::MutMut);
        let effective_mut_read_only = rows
            .iter()
            .any(|row| row.effective_overlap && row.pair.class == PairMutability::MutReadOnly);
        let effective_shared_shared = rows
            .iter()
            .any(|row| row.effective_overlap && row.pair.class == PairMutability::SharedShared);
        let class = if precise_kind != SlotKind::Ref {
            ExposureClass::Demoted
        } else if rows.iter().any(|row| row.selected_mark) {
            ExposureClass::Marked
        } else {
            let non_shared = rows
                .iter()
                .copied()
                .filter(|row| row.pair.class != PairMutability::SharedShared)
                .collect::<Vec<_>>();
            if non_shared.is_empty() {
                ExposureClass::SharedSafe
            } else if effective_mut_mut || effective_mut_read_only {
                ExposureClass::ReplaySafe
            } else {
                ExposureClass::Unresolved
            }
        };
        answer.push(ExposureLedgerRow {
            program: program.to_owned(),
            formal,
            baseline: baseline_kind,
            precise: precise_kind,
            class,
            effective_mut_mut,
            effective_mut_read_only,
            effective_shared_shared,
        });
    }
    Ok(answer)
}

fn filter_planned_marks_postsolve(
    rows: &[ExtendedPairLedgerRow],
    precise: &AcceptedFormalModel,
) -> Vec<ExtendedPairLedgerRow> {
    let mut filtered = rows.to_vec();
    for row in filtered.iter_mut().filter(|row| row.planned_mark) {
        let left_fallen = row
            .left_formals
            .iter()
            .filter(|formal| precise.kinds.get(*formal) != Some(&SlotKind::Ref))
            .cloned()
            .collect::<Vec<_>>();
        let right_fallen = row
            .right_formals
            .iter()
            .filter(|formal| precise.kinds.get(*formal) != Some(&SlotKind::Ref))
            .cloned()
            .collect::<Vec<_>>();
        row.selected_mark = left_fallen.is_empty() && right_fallen.is_empty();
        if row.selected_mark {
            row.model_attribution = "retained:both-ref".to_owned();
            continue;
        }
        row.markability = "demoted-by-model".to_owned();
        let fallen = left_fallen
            .iter()
            .chain(&right_fallen)
            .cloned()
            .collect::<BTreeSet<_>>();
        let cooccurring = rows
            .iter()
            .filter(|other| {
                other.effective_overlap
                    && other
                        .left_formals
                        .iter()
                        .chain(&other.right_formals)
                        .any(|formal| fallen.contains(formal))
            })
            .map(|other| other.pair.class.label())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
            .join(",");
        row.model_attribution = format!(
            "left_fell={};right_fell={};cooccurring={}",
            left_fallen
                .iter()
                .map(formal_label)
                .collect::<Vec<_>>()
                .join("|"),
            right_fallen
                .iter()
                .map(formal_label)
                .collect::<Vec<_>>()
                .join("|"),
            if cooccurring.is_empty() {
                "none"
            } else {
                &cooccurring
            },
        );
    }
    filtered
}

fn run_focused_w14(
    program_name: &str,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    mutability: &MutFacts,
    formals: &BTreeMap<(String, u32), ArtifactFormal>,
    baseline: &AcceptedFormalModel,
    measured: &MeasuredProgram,
    batch: Option<&BatchPrecise<'_>>,
) -> Result<W14Measurement, String> {
    if measured.extended_pairs.len() != measured.pairs.len()
        || measured.extended_pairs.iter().any(|row| !row.raw_overlap)
    {
        return Err("W14 raw/extended pair ledger does not cover the exact denominator".to_owned());
    }
    let (precise, precise_rounds) = if let Some(batch) = batch {
        let measured_marks = measured
            .final_marks
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        if measured_marks != *batch.planned_marks {
            return Err(format!(
                "production planned-mark identities disagree with W14: production={} W14={}",
                batch.planned_marks.len(),
                measured_marks.len()
            ));
        }
        (
            project_formal_kinds(program.tcx, program, slots, formals, batch.model)?,
            batch.rounds,
        )
    } else {
        let parameter_overlaps = build_parameter_overlaps(program, &measured.extended_pairs)?;
        let solver = KindSolver::new(slots);
        let origins = compute_origins(program);
        let construction = construct_bo_into(
            program,
            slots,
            &origins,
            mutability,
            &solver,
            CopyLendMode::Baseline,
        )
        .map_err(|error| format!("W14 construction failed: {error}"))?;
        let (model, stats) = verify_bo_construction_with_parameter_overlaps(
            program,
            slots,
            &origins,
            &solver,
            &construction,
            mutability,
            &parameter_overlaps,
        );
        let model = model.ok_or_else(|| "W14 precise replay declined".to_owned())?;
        (
            project_formal_kinds(program.tcx, program, slots, formals, &model)?,
            stats.rounds,
        )
    };

    let filtered_pairs = filter_planned_marks_postsolve(&measured.extended_pairs, &precise);
    let exposures = build_exposure_ledger(
        program_name,
        &filtered_pairs,
        measured.counts.attributed_predicted_refs_depth0,
        baseline,
        &precise,
    )?;
    Ok(W14Measurement {
        pairs: filtered_pairs,
        exposures,
        precise_rounds,
    })
}

fn unknown_reachable(
    functions: &BTreeMap<String, FunctionNode>,
) -> Result<BTreeSet<String>, String> {
    let mut reachable = BTreeSet::new();
    let mut pending = functions
        .iter()
        .filter_map(|(name, node)| node.unknown_caller_root.then_some(name.clone()))
        .collect::<Vec<_>>();
    while let Some(function) = pending.pop() {
        if !reachable.insert(function.clone()) {
            continue;
        }
        let Some(node) = functions.get(&function) else {
            return Err(format!(
                "call graph references unknown local function `{function}`"
            ));
        };
        for callee in &node.callees {
            if !functions.contains_key(callee) {
                return Err(format!(
                    "call graph references unknown local callee `{callee}`"
                ));
            }
            pending.push(callee.clone());
        }
    }
    Ok(reachable)
}

fn parse_formals(
    a_text: &str,
    b_text: &str,
    facts_text: &str,
) -> Result<BTreeMap<(String, u32), ArtifactFormal>, String> {
    let a = crate::coverage_recon::schema::decode(a_text)
        .map_err(|why| format!("producer A: {why}"))?;
    let b = crate::coverage_recon::schema::decode(b_text)
        .map_err(|why| format!("producer B: {why}"))?;
    let verdict = crate::coverage_recon::compare::compare(&a, &b);
    if !verdict.passed() {
        return Err(format!(
            "reconciliation failed: {} violation(s), {} finding(s)",
            verdict.violations.len(),
            verdict.findings.len()
        ));
    }

    const FACTS_HEADER: &str = "fn_path\tmir_local\tis_param\tannotated\tslot\tkind\traw_op\tptr_cmp\tctor\tlen_class\tsize_expr";
    let mut lines = facts_text.lines();
    if lines.next() != Some(FACTS_HEADER) {
        return Err("facts join header does not match the registered schema".to_owned());
    }
    let mut facts = BTreeMap::new();
    for (offset, line) in lines.enumerate() {
        let columns = line.split('\t').collect::<Vec<_>>();
        if columns.len() != 11 {
            return Err(format!(
                "facts line {} has {} columns, expected 11",
                offset + 2,
                columns.len()
            ));
        }
        if !matches!(columns[2], "0" | "1")
            || !matches!(columns[3], "0" | "1")
            || !matches!(columns[4], "0" | "1")
            || !matches!(columns[5], "ref" | "raw" | "owning" | "-")
        {
            return Err(format!(
                "facts line {} contains an invalid enum",
                offset + 2
            ));
        }
        let mir_local = columns[1]
            .parse::<u32>()
            .map_err(|why| format!("facts line {} mir_local: {why}", offset + 2))?;
        let key = (columns[0].to_owned(), mir_local);
        if facts
            .insert(key.clone(), (columns[2] == "1", columns[5]))
            .is_some()
        {
            return Err(format!("duplicate facts identity {}#{}", key.0, key.1));
        }
    }

    let a_keys = a
        .iter()
        .map(|row| (row.fn_path.clone(), row.mir_local))
        .collect::<BTreeSet<_>>();
    let fact_keys = facts.keys().cloned().collect::<BTreeSet<_>>();
    if a_keys.len() != a.len() {
        return Err("producer A contains a duplicate subject identity".to_owned());
    }
    if a_keys != fact_keys {
        return Err(format!(
            "facts/A population mismatch: A={} facts={}",
            a_keys.len(),
            fact_keys.len()
        ));
    }

    let mut formals = BTreeMap::new();
    for row in &a {
        let Some(parameter) = row.arg_index else {
            continue;
        };
        let key = (row.fn_path.clone(), row.mir_local);
        let &(is_param, kind) = facts
            .get(&key)
            .ok_or_else(|| format!("missing facts row {}#{}", key.0, key.1))?;
        if !is_param {
            return Err(format!(
                "artifact parameter {}#{} is not a facts parameter",
                key.0, key.1
            ));
        }
        let formal_key = (row.fn_path.clone(), parameter);
        let formal = ArtifactFormal {
            settles_ref: kind == "ref",
            currently_predicted_ref: matches!(
                row.outcome,
                Some(Outcome::RefMut | Outcome::RefShared)
            ),
            ptr_depth: row.ptr_depth,
        };
        if formals.insert(formal_key.clone(), formal).is_some() {
            return Err(format!(
                "duplicate formal identity {}#arg{}",
                formal_key.0, formal_key.1
            ));
        }
    }
    Ok(formals)
}

fn snapshot_formals(
    snapshot: &Path,
    program: &str,
) -> Result<BTreeMap<(String, u32), ArtifactFormal>, String> {
    let read = |suffix: &str| {
        let path = snapshot.join(format!("{program}.{suffix}"));
        fs::read_to_string(&path).map_err(|why| format!("read {}: {why}", path.display()))
    };
    parse_formals(&read("a.jsonl")?, &read("b.jsonl")?, &read("facts.tsv")?)
}

fn unknown_caller_roots(tcx: TyCtxt<'_>, functions: &[LocalDefId]) -> FxHashSet<LocalDefId> {
    let program = super::collect_program(tcx);
    let fn_ptrs = crate::rewriter::collector::collect_fn_ptrs(&program);
    functions
        .iter()
        .copied()
        .filter(|did| tcx.visibility(did.to_def_id()).is_public() || fn_ptrs.contains(did))
        .collect()
}

fn indirect_targets(
    pre: &andersen::PreAnalysisData<'_>,
    solutions: &andersen::Solutions,
    caller: LocalDefId,
    block: BasicBlock,
) -> Result<Vec<LocalDefId>, String> {
    let location = pre
        .indirect_calls
        .get(&caller)
        .and_then(|calls| calls.get(&block))
        .ok_or_else(|| format!("missing Andersen indirect-call site {caller:?}/{block:?}"))?;
    let mut targets = solutions[*location]
        .iter()
        .filter_map(|location| pre.inv_fns.get(&location).copied())
        .collect::<Vec<_>>();
    targets.sort_unstable_by_key(|did| did.local_def_index.as_u32());
    targets.dedup();
    Ok(targets)
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

fn origin_points(
    body: &Body<'_>,
    flow: &BodyLifetimeFlow,
    caller_reachable_from_unknown: bool,
    operand: &Operand<'_>,
) -> Option<(
    rustc_index::bit_set::DenseBitSet<lifetime_flow::LifetimeSlot>,
    bool,
)> {
    let place = operand.place()?;
    if !place.projection.is_empty() {
        return None;
    }
    let target = flow.slot_for_local(place.local, 0)?;
    let mut origins = rustc_index::bit_set::DenseBitSet::new_empty(flow.slots.len());
    for (source, _) in flow.slots.iter_enumerated() {
        if source == target || flow.value_flows.contains(source, target) {
            origins.insert(source);
        }
    }
    let mut complete = !flow.unknown_targets.contains(target);
    if caller_reachable_from_unknown {
        for argument in body.args_iter() {
            let Some(source) = flow.slot_for_local(argument, 0) else {
                continue;
            };
            if source == target || flow.value_flows.contains(source, target) {
                complete = false;
                break;
            }
        }
    }
    Some((origins, complete))
}

fn origin_pair_facts<'tcx>(
    body: &Body<'tcx>,
    flow: &BodyLifetimeFlow,
    caller_reachable_from_unknown: bool,
    left: &Operand<'tcx>,
    right: &Operand<'tcx>,
) -> (bool, SetPairEvidence<String>) {
    let left_place = left.place();
    let right_place = right.place();
    let storage_alias = match (left_place, right_place) {
        (Some(left), Some(right)) if left == right => true,
        (Some(left), Some(right)) if left.projection.is_empty() && right.projection.is_empty() => {
            match (
                flow.slot_for_local(left.local, 0),
                flow.slot_for_local(right.local, 0),
            ) {
                (Some(left), Some(right)) => flow.storage_aliases.contains(left, right),
                _ => false,
            }
        }
        _ => false,
    };
    let evidence = match (
        origin_points(body, flow, caller_reachable_from_unknown, left),
        origin_points(body, flow, caller_reachable_from_unknown, right),
    ) {
        (Some((left, left_complete)), Some((right, right_complete))) => {
            let left = left
                .iter()
                .map(|slot| slot.index().to_string())
                .collect::<BTreeSet<_>>();
            let right = right
                .iter()
                .map(|slot| slot.index().to_string())
                .collect::<BTreeSet<_>>();
            if left_complete && right_complete {
                SetPairEvidence::Complete { left, right }
            } else {
                SetPairEvidence::Incomplete { left, right }
            }
        }
        _ => SetPairEvidence::Unknown,
    };
    (storage_alias, evidence)
}

fn call_pair_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    pre: &andersen::PreAnalysisData<'tcx>,
    solutions: &andersen::Solutions,
    unknown_locations: &BTreeSet<usize>,
    flow: &BodyLifetimeFlow,
    caller_reachable_from_unknown: bool,
    caller: LocalDefId,
    left: &Operand<'tcx>,
    right: &Operand<'tcx>,
) -> PairFacts<String> {
    let left_place = left.place();
    let right_place = right.place();
    let (storage_alias, origins) =
        origin_pair_facts(body, flow, caller_reachable_from_unknown, left, right);
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
        (Some((left, left_complete)), Some((right, right_complete)))
            if left_complete && right_complete =>
        {
            SetPairEvidence::Complete { left, right }
        }
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

fn formal_for_argument(
    tcx: TyCtxt<'_>,
    targets: &[LocalDefId],
    parameter: usize,
    formals: &BTreeMap<(String, u32), ArtifactFormal>,
    current_refs: &BTreeMap<(String, u32), BTreeSet<FormalKey>>,
    mutability: &MutFacts,
) -> Result<FormalDecision, String> {
    let mut settles_ref = true;
    let mut currently_predicted_refs = BTreeSet::new();
    let mut target_mutability = Vec::with_capacity(targets.len());
    for &target in targets {
        let body = tcx.mir_drops_elaborated_and_const_checked(target).borrow();
        if parameter >= body.arg_count {
            return Err(format!(
                "call argument {} exceeds target {} arity {}",
                parameter + 1,
                tcx.def_path_str(target.to_def_id()),
                body.arg_count
            ));
        }
        let local = rustc_middle::mir::Local::from_usize(parameter + 1);
        target_mutability.push(
            (!mutability.is_defaulted(target, local)).then(|| mutability.is_mutable(target, local)),
        );
        let path = tcx.def_path_str(target.to_def_id());
        let key = (path.clone(), parameter as u32 + 1);
        let Some(formal) = formals.get(&key) else {
            if body.local_decls[local].ty.is_raw_ptr() {
                return Err(format!(
                    "pointer formal {}#arg{} has no artifact row",
                    path,
                    parameter + 1
                ));
            }
            settles_ref = false;
            continue;
        };
        let refs = current_refs.get(&key).ok_or_else(|| {
            format!(
                "current-head baseline model has no formal identity for {}#arg{} (snapshot depth {})",
                path,
                parameter + 1,
                formal.ptr_depth,
            )
        })?;
        let depth_zero = FormalKey {
            function: path,
            parameter: parameter as u32 + 1,
            depth: 0,
        };
        settles_ref &= refs.contains(&depth_zero);
        currently_predicted_refs.extend(refs.iter().cloned());
    }
    if !settles_ref {
        currently_predicted_refs.clear();
    }
    let (mutable, mutability_default_fires) = join_formal_mutability(target_mutability);
    Ok(FormalDecision {
        settles_ref,
        currently_predicted_refs,
        mutable,
        mutability_default_fires,
    })
}

struct AcceptedFormalModel {
    refs: BTreeMap<(String, u32), BTreeSet<FormalKey>>,
    kinds: BTreeMap<FormalKey, SlotKind>,
}

fn project_formal_kinds(
    tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    formals: &BTreeMap<(String, u32), ArtifactFormal>,
    model: &rustc_hash::FxHashMap<SlotRef, SlotKind>,
) -> Result<AcceptedFormalModel, String> {
    let mut refs = BTreeMap::new();
    let mut kinds = BTreeMap::new();
    for &function in &program.functions {
        let path = tcx.def_path_str(function.to_def_id());
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let universe = slots
            .fn_local_slots
            .get(&function)
            .ok_or_else(|| format!("accepted model lacks slot universe for {path}"))?;
        for parameter in 0..body.arg_count {
            let key = (path.clone(), parameter as u32 + 1);
            let Some(formal) = formals.get(&key) else {
                continue;
            };
            let local = Local::from_usize(parameter + 1);
            let mut accepted_refs = BTreeSet::new();
            for depth in 0..formal.ptr_depth {
                let slot = universe.slot_for_local_depth(local, depth).ok_or_else(|| {
                    format!("accepted model lacks {path}#arg{}@{depth}", parameter + 1)
                })?;
                let formal_key = FormalKey {
                    function: path.clone(),
                    parameter: parameter as u32 + 1,
                    depth,
                };
                let kind = model
                    .get(&SlotRef::Local(function, slot))
                    .copied()
                    .ok_or_else(|| format!("accepted model has no kind for {formal_key:?}"))?;
                if kind == SlotKind::Ref {
                    accepted_refs.insert(formal_key.clone());
                }
                kinds.insert(formal_key, kind);
            }
            refs.insert(key, accepted_refs);
        }
    }
    Ok(AcceptedFormalModel { refs, kinds })
}

fn accepted_current_model(
    tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    formals: &BTreeMap<(String, u32), ArtifactFormal>,
) -> Result<AcceptedFormalModel, String> {
    let slots = CrateSlots::build(program);
    let mutable = MutFacts::from_program(program);
    let (model, _export) = with_bo_export(|| {
        let solver = KindSolver::new(&slots);
        let origins = compute_origins(program);
        let Ok(construction) = construct_bo_into(
            program,
            &slots,
            &origins,
            &mutable,
            &solver,
            CopyLendMode::Baseline,
        ) else {
            return None;
        };
        verify_bo_construction(program, &slots, &origins, &solver, &construction, &mutable)
    });
    let model = model.ok_or_else(|| "targeted accepted-model export declined".to_owned())?;

    project_formal_kinds(tcx, program, &slots, formals, &model)
}

fn measure_tcx(
    program_name: &str,
    tcx: TyCtxt<'_>,
    formals: &BTreeMap<(String, u32), ArtifactFormal>,
    accepted: &AcceptedFormalModel,
    accepted_model_time: Duration,
    focused_w14: bool,
    batch: Option<&BatchPrecise<'_>>,
) -> Result<Measurement, String> {
    let program = super::collect_program(tcx);
    let slots = CrateSlots::build(&program);
    let mutability = MutFacts::from_program(&program);
    let functions = program.functions.iter().copied().collect::<FxHashSet<_>>();
    let roots = unknown_caller_roots(tcx, &program.functions);

    let t_origins = Instant::now();
    let lifetime_flows = lifetime_flow::analyze_program_lifetime_flow(&program);
    let origins_time = t_origins.elapsed();

    let t_andersen = Instant::now();
    let arena = typed_arena::Arena::new();
    let type_shapes = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: roots
            .iter()
            .map(|did| tcx.item_name(did.to_def_id()).to_string())
            .collect(),
    };
    let pre = andersen::pre_analyze(&config, &type_shapes, tcx);
    let solutions = andersen::analyze(&config, &pre, &type_shapes, tcx);
    let andersen_time = t_andersen.elapsed();

    let mut unknown_locations = BTreeSet::new();
    for variable in &pre.exposed_fn_arg_vars {
        let start = pre.vars[variable];
        let end = pre.index_info.get_end(start);
        unknown_locations.extend(start.index()..=end.index());
    }

    let mut coverage = CoverageCounts::default();
    let mut function_nodes = BTreeMap::new();
    for &function in &program.functions {
        function_nodes.insert(
            tcx.def_path_str(function.to_def_id()),
            FunctionNode {
                unknown_caller_root: roots.contains(&function),
                callees: BTreeSet::new(),
            },
        );
    }

    let mut resolved_targets = rustc_hash::FxHashMap::default();
    for &caller in &program.functions {
        let caller_path = tcx.def_path_str(caller.to_def_id());
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            let function = match &block_data.terminator().kind {
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => func,
                _ => continue,
            };
            coverage.calls_total += 1;
            let targets = if let Some(function) = function.constant() {
                let TyKind::FnDef(target, _) = *function.ty().kind() else {
                    coverage.non_fn_def_constant += 1;
                    continue;
                };
                let Some(target) = target.as_local() else {
                    coverage.direct_external += 1;
                    continue;
                };
                if !functions.contains(&target) {
                    coverage.direct_external += 1;
                    continue;
                }
                coverage.direct_local += 1;
                vec![target]
            } else {
                let targets = indirect_targets(&pre, &solutions, caller, block)?;
                let targets = targets
                    .into_iter()
                    .filter(|target| functions.contains(target))
                    .collect::<Vec<_>>();
                if targets.is_empty() {
                    coverage.indirect_unresolved += 1;
                    continue;
                }
                coverage.indirect_local += 1;
                targets
            };

            let target_paths = targets
                .iter()
                .map(|target| tcx.def_path_str(target.to_def_id()))
                .collect::<BTreeSet<_>>();
            function_nodes
                .get_mut(&caller_path)
                .expect("caller node")
                .callees
                .extend(target_paths.iter().cloned());
            resolved_targets.insert((caller, block), targets);
        }
    }

    let unknown_reachable = unknown_reachable(&function_nodes)?;
    let mut call_sites = Vec::new();
    for &caller in &program.functions {
        let caller_path = tcx.def_path_str(caller.to_def_id());
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let flow = &lifetime_flows
            .get(&caller)
            .ok_or_else(|| format!("missing lifetime flow for {caller_path}"))?
            .body;
        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            let call_args = match &block_data.terminator().kind {
                TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
                    &args[..]
                }
                _ => continue,
            };
            let Some(targets) = resolved_targets.get(&(caller, block)) else {
                continue;
            };
            let target_paths = targets
                .iter()
                .map(|target| tcx.def_path_str(target.to_def_id()))
                .collect::<BTreeSet<_>>();
            let mut target_functions = targets
                .iter()
                .map(|target| TargetFunction {
                    key: target.local_def_index.as_u32(),
                    path: tcx.def_path_str(target.to_def_id()),
                })
                .collect::<Vec<_>>();
            target_functions.sort();
            target_functions.dedup();

            let arguments = (0..call_args.len())
                .map(|parameter| {
                    formal_for_argument(
                        tcx,
                        targets,
                        parameter,
                        formals,
                        &accepted.refs,
                        &mutability,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let mut pair_facts = BTreeMap::new();
            let mut snapshot_verdicts = BTreeMap::new();
            let mut post_filter = BTreeMap::new();
            let mut mark_keys = BTreeMap::new();
            for left in 0..call_args.len() {
                for right in left + 1..call_args.len() {
                    pair_facts.insert(
                        (left, right),
                        call_pair_facts(
                            tcx,
                            &body,
                            &pre,
                            &solutions,
                            &unknown_locations,
                            flow,
                            unknown_reachable.contains(&caller_path),
                            caller,
                            &call_args[left].node,
                            &call_args[right].node,
                        ),
                    );
                    let read_only = match (arguments[left].mutable, arguments[right].mutable) {
                        (false, true) => Some(PairSide::Left),
                        (true, false) => Some(PairSide::Right),
                        _ => None,
                    };
                    if let Some(read_only) = read_only
                        && let Some(verdict) =
                            combine_snapshot_verdicts(targets.iter().map(|target| {
                                snapshot_verdict_for_target(tcx, *target, left, right, read_only)
                            }))
                    {
                        snapshot_verdicts.insert((left, right), verdict);
                        post_filter.insert(
                            (left, right),
                            target_type_filters(tcx, targets, left, right),
                        );
                        let filters = target_type_filters(tcx, targets, left, right);
                        if filters == (true, true)
                            && let (Some(left_actual), Some(right_actual)) = (
                                argument_slot_key(&slots, caller, &body, &call_args[left].node),
                                argument_slot_key(&slots, caller, &body, &call_args[right].node),
                            )
                        {
                            let target = targets[0];
                            let target_body =
                                tcx.mir_drops_elaborated_and_const_checked(target).borrow();
                            let pointee = target_body.local_decls[Local::from_usize(left + 1)]
                                .ty
                                .builtin_deref(true)
                                .expect("type filter proved a pointee")
                                .to_string();
                            if let Some(mark) = C9MarkKey::new(
                                caller.local_def_index.as_u32(),
                                MirLocationKey::new(
                                    block.as_u32(),
                                    body.basic_blocks[block].statements.len(),
                                ),
                                targets.iter().map(|target| target.local_def_index.as_u32()),
                                target.local_def_index.as_u32(),
                                left as u32 + 1,
                                left_actual,
                                right as u32 + 1,
                                right_actual,
                                read_only,
                                pointee,
                            ) {
                                mark_keys.insert((left, right), mark);
                            }
                        }
                    }
                }
            }
            call_sites.push(CallSite {
                id: format!(
                    "{}:bb{}:{}:{}",
                    caller_path,
                    block.index(),
                    tcx.sess
                        .source_map()
                        .span_to_diagnostic_string(block_data.terminator().source_info.span),
                    target_paths.into_iter().collect::<Vec<_>>().join("|")
                ),
                targets: target_functions,
                arguments,
                pair_facts,
                snapshot_verdicts,
                post_filter,
                mark_keys,
            });
        }
    }

    let measured = measure_program(&ProgramInput {
        name: program_name.to_owned(),
        call_sites,
        functions: function_nodes,
    })?;
    let w14 = focused_w14
        .then(|| {
            run_focused_w14(
                program_name,
                &program,
                &slots,
                &mutability,
                formals,
                accepted,
                &measured,
                batch,
            )
        })
        .transpose()?;
    coverage.validate()?;
    Ok(Measurement {
        counts: measured.counts,
        pairs: measured.pairs,
        classifier: measured.classifier,
        snapshot: measured.snapshot,
        final_marks: measured.final_marks,
        w14,
        coverage,
        timings: Timings {
            origins: origins_time,
            andersen: andersen_time,
            accepted_model: accepted_model_time,
        },
    })
}

pub(super) fn run_batch_w14(
    program_name: &str,
    tcx: TyCtxt<'_>,
    baseline_model: &rustc_hash::FxHashMap<SlotRef, SlotKind>,
    precise_model: &rustc_hash::FxHashMap<SlotRef, SlotKind>,
    planned_marks: &BTreeSet<C9MarkKey>,
    model_retained_marks: usize,
    precise_rounds: usize,
    artifact_dir: &Path,
) -> Result<BatchW14Summary, String> {
    let snapshot = std::env::var_os("CRAT_A5_SNAPSHOT")
        .map(std::path::PathBuf::from)
        .ok_or_else(|| "A5 batch requires CRAT_A5_SNAPSHOT".to_owned())?;
    let formals = snapshot_formals(&snapshot, program_name)?;
    let program = super::collect_program(tcx);
    let slots = CrateSlots::build(&program);
    let baseline = project_formal_kinds(tcx, &program, &slots, &formals, baseline_model)?;
    let batch = BatchPrecise {
        model: precise_model,
        planned_marks,
        model_retained_marks,
        rounds: precise_rounds,
    };
    let measured = measure_tcx(
        program_name,
        tcx,
        &formals,
        &baseline,
        Duration::ZERO,
        true,
        Some(&batch),
    )?;
    let w14 = measured
        .w14
        .as_ref()
        .ok_or_else(|| "A5 batch W14 result is absent".to_owned())?;
    let count = |class| {
        w14.exposures
            .iter()
            .filter(|row| row.class == class)
            .count()
    };
    let selected_marks = w14.pairs.iter().filter(|row| row.selected_mark).count();
    if selected_marks != batch.model_retained_marks {
        return Err(format!(
            "production model-retained marks {} disagree with W14 {}",
            batch.model_retained_marks, selected_marks
        ));
    }

    fs::create_dir_all(artifact_dir)
        .map_err(|error| format!("create A5 batch artifact dir: {error}"))?;
    let mut pairs = String::from(
        "program\tsite\tleft_argument\tright_argument\tclass\ttarget_formals\tleft_formals\tright_formals\traw_overlap\teffective_overlap\tmarkability\tretained_mark\tcopy_lend_mode\ta5_mode\ta5_world\ta5_abi_guard\tplanned_mark\tmodel_attribution\n",
    );
    for row in &w14.pairs {
        let line = render_extended_pair_line(row);
        pairs.push_str(line.strip_prefix(W14_PAIR_SENTINEL).unwrap_or(&line));
        pairs.push('\n');
    }
    fs::write(artifact_dir.join("w14-pair-ledger.tsv"), pairs)
        .map_err(|error| format!("write W14 pair ledger: {error}"))?;
    let mut exposures = String::from(
        "program\tfunction\tparameter\tdepth\tbaseline_kind\tprecise_kind\tmovement\tclass\tcopy_lend_mode\ta5_mode\ta5_world\ta5_abi_guard\teffective_mut_mut\teffective_mut_read_only\teffective_shared_shared\tincidence\n",
    );
    for row in &w14.exposures {
        let line = render_exposure_line(row);
        exposures.push_str(line.strip_prefix(W14_EXPOSURE_SENTINEL).unwrap_or(&line));
        exposures.push('\n');
    }
    fs::write(artifact_dir.join("w14-exposure-ledger.tsv"), exposures)
        .map_err(|error| format!("write W14 exposure ledger: {error}"))?;

    Ok(BatchW14Summary {
        pair_den: measured.counts.pair_denominator,
        mut_mut: measured.counts.mut_mut,
        mut_read_only: measured.counts.mut_read_only,
        shared_shared: measured.counts.shared_shared,
        effective_pairs: w14.pairs.iter().filter(|row| row.effective_overlap).count(),
        planned_marks: w14.pairs.iter().filter(|row| row.planned_mark).count(),
        model_retained_marks: selected_marks,
        exposures: w14.exposures.len(),
        demoted: count(ExposureClass::Demoted),
        marked: count(ExposureClass::Marked),
        shared_safe: count(ExposureClass::SharedSafe),
        replay_safe: count(ExposureClass::ReplaySafe),
        unresolved: count(ExposureClass::Unresolved),
        precise_rounds: w14.precise_rounds,
    })
}

fn read_drift_exposures(
    path: &Path,
    program: &str,
    expected_class: &str,
) -> Result<BTreeSet<FormalKey>, String> {
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read drift exposure {}: {error}", path.display()))?;
    let mut rows = BTreeSet::new();
    for (index, line) in input.lines().enumerate() {
        if index == 0 {
            continue;
        }
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 16 {
            return Err(format!(
                "drift exposure {}:{} has {} fields",
                path.display(),
                index + 1,
                fields.len()
            ));
        }
        if fields[0] == program && fields[7] == expected_class {
            rows.insert(FormalKey {
                function: fields[1].to_owned(),
                parameter: fields[2]
                    .parse()
                    .map_err(|error| format!("drift parameter: {error}"))?,
                depth: fields[3]
                    .parse()
                    .map_err(|error| format!("drift depth: {error}"))?,
            });
        }
    }
    Ok(rows)
}

fn read_preserved_model(
    path: &Path,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
) -> Result<FxHashMap<SlotRef, SlotKind>, String> {
    let mut by_key = BTreeMap::<SlotKey, SlotRef>::new();
    for &did in &program.functions {
        let universe = &slots.fn_local_slots[&did];
        for index in 0..universe.len() {
            let slot = SlotRef::Local(did, SlotId::from_usize(index));
            by_key.insert(SlotKey::of(slot), slot);
        }
    }
    for index in 0..slots.field_slots.len() {
        let slot = SlotRef::Field(SlotId::from_usize(index));
        by_key.insert(SlotKey::of(slot), slot);
    }

    let input = fs::read_to_string(path)
        .map_err(|error| format!("read preserved model {}: {error}", path.display()))?;
    let mut model = FxHashMap::default();
    for (index, line) in input.lines().enumerate() {
        if index == 0 {
            continue;
        }
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 4 {
            return Err(format!(
                "preserved model {}:{} has {} fields",
                path.display(),
                index + 1,
                fields.len()
            ));
        }
        let key = SlotKey {
            variant: fields[0]
                .parse()
                .map_err(|error| format!("model variant: {error}"))?,
            owner: fields[1]
                .parse()
                .map_err(|error| format!("model owner: {error}"))?,
            slot: fields[2]
                .parse()
                .map_err(|error| format!("model slot: {error}"))?,
        };
        let slot = by_key
            .get(&key)
            .copied()
            .ok_or_else(|| format!("preserved model key {key:?} is outside current slots"))?;
        let kind = match fields[3] {
            "Raw" => SlotKind::Raw,
            "Ref" => SlotKind::Ref,
            "Owning" => SlotKind::Owning,
            other => return Err(format!("unknown preserved model kind {other}")),
        };
        model.insert(slot, kind);
    }
    if model.len() != by_key.len() {
        return Err(format!(
            "preserved model covers {} of {} slots",
            model.len(),
            by_key.len()
        ));
    }
    Ok(model)
}

fn read_production_overlap_map(
    path: &Path,
    program: &RustProgram<'_>,
) -> Result<FxHashMap<LocalDefId, ParameterOverlap>, String> {
    let by_key = program
        .functions
        .iter()
        .copied()
        .map(|did| (did.local_def_index.as_u32(), did))
        .collect::<BTreeMap<_, _>>();
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read production summary {}: {error}", path.display()))?;
    let mut pairs = FxHashMap::<LocalDefId, Vec<(Local, Local)>>::default();
    for (index, line) in input.lines().enumerate() {
        if index == 0 {
            continue;
        }
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 14 {
            return Err(format!(
                "production summary {}:{} has {} fields",
                path.display(),
                index + 1,
                fields.len()
            ));
        }
        if fields[12] != "closed_world_frozen_graph" || fields[13] != "precise_replay" {
            return Err("production summary has the wrong launch identity".to_owned());
        }
        let did_key = fields[0]
            .parse::<u32>()
            .map_err(|error| format!("summary callee: {error}"))?;
        let did = by_key
            .get(&did_key)
            .copied()
            .ok_or_else(|| format!("summary callee {did_key} is outside current program"))?;
        pairs.entry(did).or_default().push((
            Local::from_usize(
                fields[1]
                    .parse()
                    .map_err(|error| format!("summary left parameter: {error}"))?,
            ),
            Local::from_usize(
                fields[2]
                    .parse()
                    .map_err(|error| format!("summary right parameter: {error}"))?,
            ),
        ));
    }
    Ok(pairs
        .into_iter()
        .map(|(did, pairs)| (did, ParameterOverlap::from_pairs(pairs)))
        .collect())
}

pub(super) fn run_w14_drift_trace_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> super::report::Row {
    let t0 = Instant::now();
    let mut row = super::report::Row::default();
    row.set("t_tcx_s", t_tcx.as_secs_f64());
    row.set("data", "false");
    row.set("a5_world", "closed_world_frozen_graph");
    row.set("a5_mode", "precise_replay");
    row.set("trace_kind", "direct-replay-production-overlap-map");
    let name = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_owned());
    let old_exposure = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_DRIFT_OLD_EXPOSURE").expect("old drift exposure ledger"),
    );
    let new_exposure = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_DRIFT_NEW_EXPOSURE").expect("new drift exposure ledger"),
    );
    let model_path = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_DRIFT_MODEL").expect("preserved production model"),
    );
    let summary_path = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_DRIFT_SUMMARY").expect("preserved production summary"),
    );
    let heavy = std::env::var("CRAT_A5_DRIFT_HEAVY").as_deref() == Ok("1");
    let program = super::collect_program(tcx);
    let slots = CrateSlots::build(&program);
    let old = read_drift_exposures(&old_exposure, &name, "demoted").expect("old drift rows");
    let new = read_drift_exposures(&new_exposure, &name, "replay-safe").expect("new drift rows");
    let drift = old.intersection(&new).cloned().collect::<Vec<_>>();
    let sampled = if heavy && drift.len() > 10 {
        drift.iter().take(10).cloned().collect::<Vec<_>>()
    } else {
        drift.clone()
    };
    let model = read_preserved_model(&model_path, &program, &slots).expect("preserved model");
    let overlaps =
        read_production_overlap_map(&summary_path, &program).expect("production overlap map");
    let mutability = MutFacts::from_program(&program);
    let conflicts = revalidate_replaying_with_parameter_overlap(
        &program,
        &slots,
        |slot| model.get(&slot) == Some(&SlotKind::Ref),
        |slot| model.get(&slot) == Some(&SlotKind::Raw),
        &mutability,
        &overlaps,
    );
    let by_path = program
        .functions
        .iter()
        .copied()
        .map(|did| (tcx.def_path_str(did.to_def_id()), did))
        .collect::<BTreeMap<_, _>>();
    let mut conflicting_rows = 0usize;
    let mut conflict_edges = 0usize;
    for formal in &sampled {
        let did = by_path
            .get(&formal.function)
            .copied()
            .expect("drift function in current program");
        let local = Local::from_usize(formal.parameter as usize);
        let slot = slots.fn_local_slots[&did]
            .slot_for_local_depth(local, formal.depth)
            .map(|slot| SlotRef::Local(did, slot))
            .expect("drift formal slot");
        let edges = conflicts
            .get(&did)
            .into_iter()
            .flatten()
            .filter(|conflict| conflict.issuer == Some(slot) || conflict.requirers.contains(&slot))
            .collect::<Vec<_>>();
        conflicting_rows += usize::from(!edges.is_empty());
        conflict_edges += edges.len();
        let trace = if edges.is_empty() {
            "none".to_owned()
        } else {
            edges
                .iter()
                .map(|conflict| {
                    let issuer = conflict
                        .issuer
                        .map(SlotKey::of)
                        .map(|key| format!("{}:{}:{}", key.variant, key.owner, key.slot))
                        .unwrap_or_else(|| "none".to_owned());
                    let requirers = conflict
                        .requirers
                        .iter()
                        .copied()
                        .map(SlotKey::of)
                        .map(|key| format!("{}:{}:{}", key.variant, key.owner, key.slot))
                        .collect::<Vec<_>>()
                        .join("|");
                    format!("{issuer}->{requirers}")
                })
                .collect::<Vec<_>>()
                .join(";")
        };
        println!(
            "A5DRIFTTRACE\t{name}\t{}\t{}\t{}\t{trace}",
            formal.function, formal.parameter, formal.depth
        );
    }
    row.set("drift_total", drift.len());
    row.set("drift_sampled", sampled.len());
    row.set(
        "drift_exhaustive",
        usize::from(sampled.len() == drift.len()),
    );
    row.set("conflicting_rows", conflicting_rows);
    row.set("conflict_edges", conflict_edges);
    row.set("status", "ok");
    row.set("t_total_s", t0.elapsed().as_secs_f64());
    row
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ProductionSiteKey {
    callee: u32,
    left_parameter: u32,
    right_parameter: u32,
    caller: u32,
    block: u32,
}

fn parse_w14_site(site: &str) -> Result<(&str, u32), String> {
    let marker = site
        .find(":bb")
        .ok_or_else(|| format!("W14 site lacks MIR block: {site}"))?;
    let caller = &site[..marker];
    let suffix = &site[marker + 3..];
    let end = suffix
        .find(':')
        .ok_or_else(|| format!("W14 site lacks block terminator: {site}"))?;
    let block = suffix[..end]
        .parse()
        .map_err(|error| format!("W14 site block: {error}"))?;
    Ok((caller, block))
}

fn receipt_usize(receipt: &str, key: &str) -> Result<usize, String> {
    receipt
        .lines()
        .find_map(|line| line.strip_prefix(&format!("{key}=")))
        .ok_or_else(|| format!("receipt lacks {key}"))?
        .parse()
        .map_err(|error| format!("receipt {key}: {error}"))
}

pub(super) fn join_production_site_artifacts(
    tcx: TyCtxt<'_>,
    t_tcx: Duration,
    name: &str,
    pair_path: &Path,
    site_path: &Path,
    receipt_path: &Path,
) -> super::report::Row {
    let t0 = Instant::now();
    let mut row = super::report::Row::default();
    row.set("t_tcx_s", t_tcx.as_secs_f64());
    row.set("data", "false");
    row.set("join_kind", "registered-site-to-production-site-key");
    let program = super::collect_program(tcx);
    let path_to_did = program
        .functions
        .iter()
        .copied()
        .map(|did| {
            (
                tcx.def_path_str(did.to_def_id()),
                did.local_def_index.as_u32(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let sites = fs::read_to_string(&site_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", site_path.display()));
    let mut production_keys = BTreeSet::new();
    let mut ambiguous_production_keys = BTreeSet::new();
    let mut statement_by_key = BTreeMap::new();
    let mut production_class_by_key = BTreeMap::<ProductionSiteKey, String>::new();
    for (index, line) in sites.lines().enumerate() {
        if index == 0 {
            continue;
        }
        let fields = line.split('\t').collect::<Vec<_>>();
        assert_eq!(fields.len(), 16, "production-site row width");
        let key = ProductionSiteKey {
            callee: fields[3].parse().expect("site target"),
            left_parameter: fields[4].parse().expect("site left"),
            right_parameter: fields[5].parse().expect("site right"),
            caller: fields[0].parse().expect("site caller"),
            block: fields[1].parse().expect("site block"),
        };
        let statement = fields[2].parse::<usize>().expect("site statement");
        if statement_by_key
            .insert(key.clone(), statement)
            .is_some_and(|old| old != statement)
        {
            ambiguous_production_keys.insert(key.clone());
        }
        if production_class_by_key
            .insert(key.clone(), fields[12].to_owned())
            .is_some_and(|old| old != fields[12])
        {
            ambiguous_production_keys.insert(key.clone());
        }
        production_keys.insert(key);
    }

    let pairs = fs::read_to_string(&pair_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", pair_path.display()));
    let mut registered_rows = 0usize;
    let mut matched_rows = 0usize;
    let mut unmatched_rows = 0usize;
    let mut matched_keys = BTreeSet::new();
    let mut expansions = BTreeMap::<ProductionSiteKey, usize>::new();
    let mut class_by_key = BTreeMap::<ProductionSiteKey, String>::new();
    let mut mixed_keys = BTreeSet::new();
    let mut matched_class = BTreeMap::<String, usize>::new();
    let mut unmatched_class = BTreeMap::<String, usize>::new();
    for (index, line) in pairs.lines().enumerate() {
        if index == 0 {
            continue;
        }
        let fields = line.split('\t').collect::<Vec<_>>();
        assert_eq!(fields.len(), 18, "W14 pair row width");
        assert_eq!(fields[0], name, "W14 program identity");
        assert!(!fields[5].contains('|'), "ambiguous W14 target set");
        let (caller_path, block) = parse_w14_site(fields[1]).expect("W14 site identity");
        let caller = path_to_did
            .get(caller_path)
            .copied()
            .unwrap_or_else(|| panic!("W14 caller {caller_path} outside current program"));
        let target = fields[5];
        let target_path = target
            .split_once('[')
            .map(|(path, _)| path)
            .expect("W14 target path");
        let callee = path_to_did
            .get(target_path)
            .copied()
            .unwrap_or_else(|| panic!("W14 callee {target_path} outside current program"));
        let key = ProductionSiteKey {
            callee,
            left_parameter: fields[2].parse().expect("W14 left parameter"),
            right_parameter: fields[3].parse().expect("W14 right parameter"),
            caller,
            block,
        };
        let class = fields[4].to_owned();
        registered_rows += 1;
        let matched = production_keys.contains(&key);
        if matched {
            matched_rows += 1;
            matched_keys.insert(key.clone());
            *expansions.entry(key.clone()).or_default() += 1;
            *matched_class.entry(class.clone()).or_default() += 1;
            if class_by_key
                .insert(key.clone(), class.clone())
                .is_some_and(|old| old != class)
            {
                mixed_keys.insert(key.clone());
            }
            if production_class_by_key.get(&key) != Some(&class) {
                mixed_keys.insert(key.clone());
            }
        } else {
            unmatched_rows += 1;
            *unmatched_class.entry(class.clone()).or_default() += 1;
        }
        println!(
            "A5SITEJOIN\t{name}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            caller_path,
            block,
            target_path,
            fields[2],
            fields[3],
            class,
            if matched { "matched" } else { "unmatched" }
        );
    }
    let receipt = fs::read_to_string(&receipt_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", receipt_path.display()));
    let production_pairs = receipt_usize(&receipt, "a5_raw_site_pairs").expect("site-pair count");
    let production_mut_mut =
        receipt_usize(&receipt, "a5_raw_site_mut_mut").expect("site mut-mut count");
    let production_mut_read_only =
        receipt_usize(&receipt, "a5_raw_site_mut_read_only").expect("site mut-read-only count");
    let production_shared_shared =
        receipt_usize(&receipt, "a5_raw_site_shared_shared").expect("site shared-shared count");
    let multi_expansion = expansions.values().filter(|&&count| count != 1).count();
    row.set("registered_site_rows", registered_rows);
    row.set("production_site_pairs", production_pairs);
    row.set("matched_registered_rows", matched_rows);
    row.set("unique_matched_production_pairs", matched_keys.len());
    row.set("registered_unmatched", unmatched_rows);
    row.set(
        "production_unmatched",
        production_keys.difference(&matched_keys).count(),
    );
    row.set(
        "production_count_residual",
        production_pairs.abs_diff(production_keys.len()),
    );
    row.set("ambiguous_summary_keys", ambiguous_production_keys.len());
    row.set("ambiguous_production_keys", ambiguous_production_keys.len());
    row.set("mixed_class_pairs", mixed_keys.len());
    row.set("multi_expansion_pairs", multi_expansion);
    row.set(
        "matched_mut_mut",
        matched_class.get("mut_mut").copied().unwrap_or(0),
    );
    row.set(
        "matched_mut_read_only",
        matched_class.get("mut_read_only").copied().unwrap_or(0),
    );
    row.set(
        "matched_shared_shared",
        matched_class.get("shared_shared").copied().unwrap_or(0),
    );
    row.set(
        "unmatched_mut_mut",
        unmatched_class.get("mut_mut").copied().unwrap_or(0),
    );
    row.set(
        "unmatched_mut_read_only",
        unmatched_class.get("mut_read_only").copied().unwrap_or(0),
    );
    row.set(
        "unmatched_shared_shared",
        unmatched_class.get("shared_shared").copied().unwrap_or(0),
    );
    row.set("production_mut_mut", production_mut_mut);
    row.set("production_mut_read_only", production_mut_read_only);
    row.set("production_shared_shared", production_shared_shared);
    row.set("status", "ok");
    row.set("t_total_s", t0.elapsed().as_secs_f64());
    row
}

pub(super) fn run_production_site_join_worker(
    tcx: TyCtxt<'_>,
    t_tcx: Duration,
) -> super::report::Row {
    let name = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_owned());
    let pair_path = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_SITE_JOIN_W14_PAIR").expect("W14 pair ledger"),
    );
    let site_path = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_SITE_JOIN_LEDGER").expect("production site ledger"),
    );
    let receipt_path = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_SITE_JOIN_RECEIPT").expect("construction receipt"),
    );
    join_production_site_artifacts(tcx, t_tcx, &name, &pair_path, &site_path, &receipt_path)
}

pub(super) fn run_site_scope_repartition_worker(
    tcx: TyCtxt<'_>,
    t_tcx: Duration,
) -> super::report::Row {
    let t0 = Instant::now();
    let mut row = super::report::Row::default();
    row.set("t_tcx_s", t_tcx.as_secs_f64());
    row.set("data", "false");
    row.set("a5_mode", "precise_replay");
    row.set("frame", "in-process-census-derived-baseline");
    let name = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_owned());
    let w14_path = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_SCOPE_W14_PAIR").expect("preserved W14 pair ledger"),
    );
    let shard = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_SCOPE_SHARD").expect("scope-repartition shard"),
    );
    let program = super::collect_program(tcx);
    let slots = CrateSlots::build(&program);
    let origins = compute_origins(&program);
    let mutability = MutFacts::from_program(&program);
    let audits = audit_a5_site_branches(&program, &slots, origins.native_flows());
    let audit_by_key = audits
        .iter()
        .map(|audit| {
            (
                (
                    audit.caller_path.as_str(),
                    audit.block,
                    audit.target_path.as_str(),
                    audit.left_parameter,
                    audit.right_parameter,
                ),
                audit,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let did_by_path = program
        .functions
        .iter()
        .copied()
        .map(|did| (tcx.def_path_str(did.to_def_id()), did))
        .collect::<BTreeMap<_, _>>();
    let mut model = FxHashMap::default();
    for &did in &program.functions {
        for index in 0..slots.fn_local_slots[&did].len() {
            model.insert(
                SlotRef::Local(did, SlotId::from_usize(index)),
                SlotKind::Raw,
            );
        }
    }
    for index in 0..slots.field_slots.len() {
        model.insert(SlotRef::Field(SlotId::from_usize(index)), SlotKind::Raw);
    }
    let pairs = fs::read_to_string(&w14_path).expect("read preserved W14 pairs");
    let mut registered = Vec::new();
    let mut family_counts = BTreeMap::<&'static str, usize>::new();
    for (index, line) in pairs.lines().enumerate() {
        if index == 0 {
            continue;
        }
        let fields = line.split('\t').collect::<Vec<_>>();
        assert_eq!(fields.len(), 18, "W14 scope row width");
        assert_eq!(fields[0], name);
        let (caller, block) = parse_w14_site(fields[1]).expect("W14 scope site");
        let target = fields[5]
            .split_once('[')
            .map(|(path, _)| path)
            .expect("W14 scope target");
        let left = fields[2].parse::<u32>().expect("W14 scope left");
        let right = fields[3].parse::<u32>().expect("W14 scope right");
        let audit = audit_by_key
            .get(&(caller, block, target, left, right))
            .copied()
            .unwrap_or_else(|| {
                panic!("W14 row lacks producer audit: {caller}:bb{block}:{target}#{left}/{right}")
            });
        *family_counts.entry(audit.family).or_default() += 1;
        let target_did = did_by_path[target];
        for parameter in [left, right] {
            let slot = slots.fn_local_slots[&target_did]
                .slot_for_local_depth(Local::from_usize(parameter as usize), 0)
                .map(|slot| SlotRef::Local(target_did, slot))
                .expect("W14 target formal slot");
            model.insert(slot, SlotKind::Ref);
        }
        println!(
            "A5SCOPE\t{name}\t{caller}\t{block}\t{target}\t{left}\t{right}\t{}\t{}",
            fields[4], audit.family
        );
        registered.push(audit);
    }
    let plan = produce_a5_plan(
        &program,
        &slots,
        origins.native_flows(),
        &mutability,
        &model,
        A5Mode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
    )
    .expect("attempt-3 in-process A5 plan");
    let production_keys = plan
        .site_ledger
        .iter()
        .map(|site| {
            (
                site.caller,
                site.location.block,
                site.target,
                site.left_parameter,
                site.right_parameter,
            )
        })
        .collect::<BTreeSet<_>>();
    let mut residual_family_counts = BTreeMap::<&'static str, usize>::new();
    for audit in &registered {
        let key = (
            audit.caller,
            audit.block,
            audit.target,
            audit.left_parameter,
            audit.right_parameter,
        );
        if !production_keys.contains(&key) {
            *residual_family_counts.entry(audit.family).or_default() += 1;
        }
    }
    fs::create_dir_all(&shard).expect("create scope-repartition shard");
    let summary_path = shard.join("summary.tsv");
    let site_path = shard.join("production-site-ledger.tsv");
    let receipt_path = shard.join("construction-receipt.txt");
    let pair_path = shard.join("w14-pair-ledger.tsv");
    fs::write(&summary_path, &plan.summary_artifact.summary_tsv).expect("write scope summary");
    fs::write(&site_path, a5_site_artifact(A5Mode::PreciseReplay, &plan))
        .expect("write scope production-site ledger");
    fs::write(
        &receipt_path,
        format!(
            "status=ok\ndata=false\na5_raw_site_pairs={}\na5_raw_site_mut_mut={}\na5_raw_site_mut_read_only={}\na5_raw_site_shared_shared={}\n",
            plan.stats.raw_site_pairs,
            plan.stats.raw_site_mut_mut,
            plan.stats.raw_site_mut_read_only,
            plan.stats.raw_site_shared_shared,
        ),
    )
    .expect("write scope receipt");
    fs::write(&pair_path, &pairs).expect("write scope W14 pairs");
    let joined = join_production_site_artifacts(
        tcx,
        Duration::ZERO,
        &name,
        &pair_path,
        &site_path,
        &receipt_path,
    );
    for key in [
        "registered_site_rows",
        "production_site_pairs",
        "matched_registered_rows",
        "unique_matched_production_pairs",
        "registered_unmatched",
        "production_unmatched",
        "production_count_residual",
        "ambiguous_summary_keys",
        "ambiguous_production_keys",
        "mixed_class_pairs",
        "multi_expansion_pairs",
        "matched_mut_mut",
        "matched_mut_read_only",
        "matched_shared_shared",
        "unmatched_mut_mut",
        "unmatched_mut_read_only",
        "unmatched_shared_shared",
        "production_mut_mut",
        "production_mut_read_only",
        "production_shared_shared",
    ] {
        row.set(key, joined.get(key).expect("scope join field"));
    }
    let residual_family_total = residual_family_counts.values().sum::<usize>();
    assert_eq!(
        residual_family_total,
        joined
            .get("registered_unmatched")
            .expect("scope unmatched")
            .parse::<usize>()
            .expect("numeric scope unmatched"),
        "branch families must partition the exact registered residual"
    );
    for (family, count) in family_counts {
        row.set(&format!("family_{family}"), count);
    }
    for (family, count) in residual_family_counts {
        row.set(&format!("residual_family_{family}"), count);
    }
    if name == "ht" {
        for audit in registered.into_iter().filter(|audit| {
            audit.block == 14
                && matches!(
                    audit.caller_path.as_str(),
                    "src::ht::ht_expand" | "src::ht::ht_set"
                )
                && audit.target_path == "src::ht::ht_set_entry"
        }) {
            println!(
                "A5HTCONTRAST\tcaller={}\tblock={}\ttarget={}\tpair={}/{}\tfamily={}\tclassifier={:?}\tdependencies={}\tleft_operand={}\tright_operand={}\tleft_actual={:?}\tright_actual={:?}\tterminator={}",
                audit.caller_path,
                audit.block,
                audit.target_path,
                audit.left_parameter,
                audit.right_parameter,
                audit.family,
                audit.classifier,
                audit.dependencies,
                audit.left_operand,
                audit.right_operand,
                audit.left_actual,
                audit.right_actual,
                audit.terminator,
            );
        }
    }
    row.set("status", "ok");
    row.set("t_total_s", t0.elapsed().as_secs_f64());
    row
}

fn batch_sha256(path: &Path) -> Result<String, String> {
    let bytes = fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    Ok(format!("{:x}", Sha256::digest(bytes)))
}

fn batch_artifact_files(root: &Path, directory: &Path, out: &mut Vec<std::path::PathBuf>) {
    let mut entries = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("read {}: {error}", directory.display()))
        .map(|entry| entry.expect("batch artifact entry").path())
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            batch_artifact_files(root, &path, out);
        } else if path.file_name().and_then(|name| name.to_str())
            != Some("artifact-manifest.sha256")
        {
            out.push(
                path.strip_prefix(root)
                    .expect("artifact below root")
                    .to_path_buf(),
            );
        }
    }
}

fn write_batch_manifest(root: &Path) -> Result<String, String> {
    let mut files = Vec::new();
    batch_artifact_files(root, root, &mut files);
    files.sort();
    let mut manifest = String::new();
    for relative in files {
        manifest.push_str(&format!(
            "{}  ./{}\n",
            batch_sha256(&root.join(&relative))?,
            relative.display()
        ));
    }
    let path = root.join("artifact-manifest.sha256");
    fs::write(&path, manifest)
        .map_err(|error| format!("write batch artifact manifest: {error}"))?;
    batch_sha256(&path)
}

fn batch_number(row: &super::report::Row, key: &str) -> usize {
    row.get(key)
        .unwrap_or_else(|| panic!("batch row lacks {key}"))
        .parse::<usize>()
        .unwrap_or_else(|error| panic!("batch row {key} is not numeric: {error}"))
}

const A5_POPULATION_REASON_KEYS: [&str; 27] = [
    "rw_reason_arg-stays-raw",
    "rw_reason_arg-unadaptable-shape",
    "rw_reason_borrowed-into-raw-param",
    "rw_reason_call-site-not-adapted",
    "rw_reason_class-blocked",
    "rw_reason_copy-source-coupled",
    "rw_reason_duplicate-place-root",
    "rw_reason_escapes-via-field-store",
    "rw_reason_escapes-via-foreign-arg",
    "rw_reason_escapes-via-return",
    "rw_reason_flows-into-other-form",
    "rw_reason_flows-into-raw-param",
    "rw_reason_freed-slot",
    "rw_reason_kind-owning",
    "rw_reason_kind-raw",
    "rw_reason_nested-use-edits",
    "rw_reason_null-init",
    "rw_reason_opt-local-construction",
    "rw_reason_opt-use-unsupported",
    "rw_reason_place-read-pointee",
    "rw_reason_ptr-comparison",
    "rw_reason_raw-pointer-operation",
    "rw_reason_return-not-adapted",
    "rw_reason_slice-local-construction",
    "rw_reason_slice-neg-or-unknown-offset",
    "rw_reason_slice-use-unsupported",
    "rw_reason_unsupported-decl-shape",
];

const A5_OPERATIONAL_ROLLBACK_KEY: &str = "rw_reason_reverted-after-verify-failure";

fn batch_population_reason_keys(
    rows: &[super::report::Row],
) -> Result<BTreeSet<&'static str>, String> {
    let registered = A5_POPULATION_REASON_KEYS
        .into_iter()
        .collect::<BTreeSet<_>>();
    let observed = rows
        .iter()
        .flat_map(|row| row.0.iter().map(|(key, _)| key.as_str()))
        .filter(|key| key.starts_with("rw_reason_") && *key != "rw_reason_key_count")
        .collect::<BTreeSet<_>>();
    for key in &observed {
        if *key != A5_OPERATIONAL_ROLLBACK_KEY && !registered.contains(key) {
            return Err(format!("unregistered batch reason field {key}"));
        }
    }
    let population = A5_POPULATION_REASON_KEYS
        .into_iter()
        .filter(|key| observed.contains(key))
        .collect::<BTreeSet<_>>();
    if population != registered {
        let missing = registered
            .difference(&population)
            .copied()
            .collect::<Vec<_>>();
        return Err(format!(
            "batch lacks registered population keys {missing:?}"
        ));
    }
    Ok(population)
}

#[test]
fn batch_population_oracle_is_exact_and_excludes_operational_reasons() {
    let mut row = super::report::Row::default();
    for key in A5_POPULATION_REASON_KEYS {
        row.set(key, 1);
    }
    row.set(A5_OPERATIONAL_ROLLBACK_KEY, 1);
    let mut rows = [row];

    assert_eq!(
        batch_population_reason_keys(&rows).expect("registered population universe"),
        A5_POPULATION_REASON_KEYS.into_iter().collect(),
        "operational rw_reason_* fields are not population keys"
    );

    rows[0].set("rw_reason_not-registered", 1);
    assert!(
        batch_population_reason_keys(&rows).is_err(),
        "an unknown reason is a schema STOP, not a silently ignored field"
    );
}

fn batch_optional_number(row: &super::report::Row, key: &str) -> Result<usize, String> {
    row.get(key)
        .map(|value| {
            value
                .parse::<usize>()
                .map_err(|error| format!("batch row {key} is not numeric: {error}"))
        })
        .unwrap_or(Ok(0))
}

fn reconcile_batch_rollback_rows(rows: &mut [super::report::Row]) -> Result<(), String> {
    for row in rows {
        let program = row.get("program").unwrap_or("missing-program").to_owned();
        let configuration = row
            .get("configuration")
            .unwrap_or("missing-configuration")
            .to_owned();
        let emitted = batch_optional_number(row, "rw_emitted")?;
        let degraded = batch_optional_number(row, "rw_degraded")?;
        let reverted = batch_optional_number(row, "rw_reverted")?;
        let operational = batch_optional_number(row, A5_OPERATIONAL_ROLLBACK_KEY)?;
        if operational != reverted {
            return Err(format!(
                "{program}/{configuration}: operational rollback {operational} != rw_reverted {reverted}"
            ));
        }
        let decided_ref = emitted
            .checked_add(reverted)
            .ok_or_else(|| format!("{program}/{configuration}: decided-ref overflow"))?;
        let degraded_pre_revert = degraded.checked_sub(reverted).ok_or_else(|| {
            format!("{program}/{configuration}: degraded {degraded} is below reverted {reverted}")
        })?;
        let pre_revert_subjects = decided_ref
            .checked_add(degraded_pre_revert)
            .ok_or_else(|| format!("{program}/{configuration}: pre-frame overflow"))?;
        let post_revert_subjects = emitted
            .checked_add(degraded)
            .ok_or_else(|| format!("{program}/{configuration}: post-frame overflow"))?;
        if pre_revert_subjects != post_revert_subjects {
            return Err(format!(
                "{program}/{configuration}: S2b frame mismatch {pre_revert_subjects} != {post_revert_subjects}"
            ));
        }
        row.set("rw_reverted_after_verify_failure", operational);
        row.set("rw_decided_ref", decided_ref);
        row.set("rw_degraded_pre_revert", degraded_pre_revert);
        row.set("rw_subjects_pre_revert", pre_revert_subjects);
        row.set("rw_subjects_post_revert", post_revert_subjects);
    }
    Ok(())
}

#[test]
fn batch_rollback_reconciles_operational_and_both_s2b_frames() {
    let mut row = super::report::Row::default();
    row.set("program", "fixture");
    row.set("configuration", "precise");
    row.set("rw_emitted", 7);
    row.set("rw_degraded", 5);
    row.set("rw_reverted", 2);
    row.set(A5_OPERATIONAL_ROLLBACK_KEY, 2);
    let mut rows = [row];

    reconcile_batch_rollback_rows(&mut rows).expect("two-frame reconciliation");
    assert_eq!(rows[0].get("rw_reverted_after_verify_failure"), Some("2"));
    assert_eq!(rows[0].get("rw_decided_ref"), Some("9"));
    assert_eq!(rows[0].get("rw_degraded_pre_revert"), Some("3"));
    assert_eq!(rows[0].get("rw_subjects_pre_revert"), Some("12"));
    assert_eq!(rows[0].get("rw_subjects_post_revert"), Some("12"));

    rows[0].set(A5_OPERATIONAL_ROLLBACK_KEY, 1);
    assert!(reconcile_batch_rollback_rows(&mut rows).is_err());
}

fn parse_batch_csv(input: &str) -> Result<Vec<super::report::Row>, String> {
    let mut lines = input.lines();
    let header = lines
        .next()
        .ok_or_else(|| "batch CSV lacks header".to_owned())?
        .split(',')
        .collect::<Vec<_>>();
    let unique = header.iter().copied().collect::<BTreeSet<_>>();
    if unique.len() != header.len() {
        return Err("batch CSV has duplicate header fields".to_owned());
    }
    lines
        .enumerate()
        .map(|(index, line)| {
            let fields = line.split(',').collect::<Vec<_>>();
            if fields.len() != header.len() {
                return Err(format!(
                    "batch CSV row {} has {} fields, expected {}",
                    index + 2,
                    fields.len(),
                    header.len()
                ));
            }
            let mut row = super::report::Row::default();
            for (key, value) in header.iter().zip(fields) {
                if !value.is_empty() {
                    row.set(key, value);
                }
            }
            Ok(row)
        })
        .collect()
}

fn batch_model_digest_stamp(row: &super::report::Row, expected: &str) -> Result<(), String> {
    match row.get("official_evaluation_sha256") {
        Some(actual) if actual == expected => Ok(()),
        Some(actual) => Err(format!(
            "official evaluation digest stamp mismatch: expected {expected}, got {actual}"
        )),
        None => Err("batch-model row lacks verified official-evaluation digest stamp".to_owned()),
    }
}

const A5_BATCH_ATTESTED_GUARD: &str = "permitted:measurement-frozen-graph-attested";

fn batch_attestation_stamp(row: &super::report::Row) -> Result<(), String> {
    match row.get("a5_abi_guard") {
        Some(A5_BATCH_ATTESTED_GUARD) => Ok(()),
        Some(actual) => Err(format!(
            "batch row lacks the permitted frozen-graph attestation: got {actual}"
        )),
        None => Err("batch row lacks the A5 ABI-guard stamp".to_owned()),
    }
}

#[test]
fn batch_model_digest_stamp_is_mandatory_and_exact() {
    let expected = "7aa16d5b63ff39e6aaabd3590ec2be9c88c9d8a753bd9f74cd4e6056d9974fd7";
    let missing = super::report::Row::default();
    assert!(
        batch_model_digest_stamp(&missing, expected).is_err(),
        "an unstamped batch-model row must be refused"
    );
    let mut present = super::report::Row::default();
    present.set("official_evaluation_sha256", expected);
    assert_eq!(batch_model_digest_stamp(&present, expected), Ok(()));
    present.set("official_evaluation_sha256", "wrong");
    assert!(
        batch_model_digest_stamp(&present, expected).is_err(),
        "a merely present but wrong digest must be refused"
    );
}

#[test]
fn batch_attestation_stamp_is_mandatory_and_product_default_is_not_accepted() {
    let missing = super::report::Row::default();
    assert!(batch_attestation_stamp(&missing).is_err());

    let mut product_default = super::report::Row::default();
    product_default.set("a5_abi_guard", "refused:unresolved-target");
    assert!(batch_attestation_stamp(&product_default).is_err());

    let mut attested = super::report::Row::default();
    attested.set("a5_abi_guard", A5_BATCH_ATTESTED_GUARD);
    assert_eq!(batch_attestation_stamp(&attested), Ok(()));
}

fn validate_launch4_preflight(
    output: &Path,
    rows: &[super::report::Row],
    official_digest: &str,
) -> Result<(), String> {
    if rows.len() != 6 {
        return Err(format!(
            "preflight expected six bst/ht rows, got {}",
            rows.len()
        ));
    }
    for (configuration, mode) in [
        ("baseline", "baseline"),
        ("precise", "precise_replay"),
        ("coarse", "coarse_constraint"),
    ] {
        let selected = rows
            .iter()
            .filter(|row| row.get("configuration") == Some(configuration))
            .collect::<Vec<_>>();
        if selected.len() != 2 {
            return Err(format!("preflight {configuration} row count moved"));
        }
        for row in selected {
            batch_model_digest_stamp(row, official_digest)?;
            batch_attestation_stamp(row)?;
            for (key, expected) in [
                ("a5_mode", mode),
                ("a5_world", "closed_world_frozen_graph"),
                ("copy_lend_mode", "baseline"),
                ("a2_mode", "off"),
                ("rw_a5_abi_guard", A5_BATCH_ATTESTED_GUARD),
            ] {
                if row.get(key) != Some(expected) {
                    return Err(format!(
                        "preflight {configuration} stamp {key} expected {expected:?}, got {:?}",
                        row.get(key)
                    ));
                }
            }
            for key in [
                "a5_production_pair_den",
                "a5_production_mut_mut",
                "a5_production_mut_read_only",
                "a5_production_shared_shared",
                "a5_planned_marks",
                "a5_model_retained_marks",
                "a5_demoted_by_model_marks",
                "rw_a5_model_retained_marks",
                "rw_a5_emission_retained_marks",
            ] {
                batch_number(row, key);
            }
        }
    }

    let precise = rows
        .iter()
        .filter(|row| row.get("configuration") == Some("precise"))
        .collect::<Vec<_>>();
    for row in precise {
        for key in [
            "a5_w14_pairs",
            "a5_w14_mut_mut",
            "a5_w14_mut_read_only",
            "a5_w14_shared_shared",
            "a5_w14_effective_pairs",
            "a5_w14_planned_marks",
            "a5_w14_model_retained_marks",
            "a5_w14_demoted_by_model_marks",
            "a5_w14_exposures",
            "a5_w14_demoted",
            "a5_w14_marked",
            "a5_w14_shared_safe",
            "a5_w14_replay_safe",
            "a5_w14_unresolved",
            "a5_w14_precise_rounds",
            "a5_site_join_registered_site_rows",
            "a5_site_join_production_site_pairs",
            "a5_site_join_matched_registered_rows",
            "a5_site_join_unique_matched_production_pairs",
            "a5_site_join_registered_unmatched",
            "a5_site_join_production_unmatched",
            "a5_site_join_production_count_residual",
            "a5_site_join_ambiguous_summary_keys",
            "a5_site_join_ambiguous_production_keys",
            "a5_site_join_mixed_class_pairs",
            "a5_site_join_multi_expansion_pairs",
            "a5_site_join_matched_mut_mut",
            "a5_site_join_matched_mut_read_only",
            "a5_site_join_matched_shared_shared",
            "a5_site_join_production_mut_mut",
            "a5_site_join_production_mut_read_only",
            "a5_site_join_production_shared_shared",
        ] {
            batch_number(row, key);
        }
    }
    for program in ["bst", "ht"] {
        for artifact in ["w14-pair-ledger.tsv", "w14-exposure-ledger.tsv"] {
            let path = output.join("precise").join(program).join(artifact);
            if !path.is_file() {
                return Err(format!("preflight lacks {}", path.display()));
            }
        }
    }
    Ok(())
}

#[test]
#[ignore = "A5 item-22 serialized baseline/precise/coarse corpus sweep"]
fn a5_item22_batch_corpus() {
    const DIGEST: &str = "db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6";
    assert_eq!(
        std::env::var("CRAT_BOC1_SUBSTRATE").as_deref(),
        Ok("derived")
    );
    assert_eq!(std::env::var("CRAT_BOC1_MEM_MB").as_deref(), Ok("49152"));
    assert_eq!(
        std::env::var("CRAT_BOC1_TIMEOUT_SECS").as_deref(),
        Ok("14400")
    );
    assert_eq!(super::CORPUS.len(), 20);
    let snapshot = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_SNAPSHOT").expect("batch requires CRAT_A5_SNAPSHOT"),
    );
    assert!(
        snapshot.is_dir(),
        "missing A5 snapshot {}",
        snapshot.display()
    );
    let output = super::orchestrate::out_dir().join("a5-item22-batch");
    fs::create_dir_all(&output).expect("create A5 item-22 output");
    let root = super::orchestrate::workspace_root();
    let official_link = root.join("benchmarks/rs-crown-transformed/evaluation.tsv");
    let official_target = fs::read_link(&official_link).expect("read official evaluation symlink");
    assert!(
        official_target.is_absolute(),
        "official evaluation link must be absolute"
    );
    let official_digest = batch_sha256(&official_link).expect("hash official evaluation link");
    assert_eq!(
        official_digest,
        "7aa16d5b63ff39e6aaabd3590ec2be9c88c9d8a753bd9f74cd4e6056d9974fd7"
    );
    let official_root = official_target
        .parent()
        .expect("official evaluation target parent")
        .to_path_buf();
    fs::write(
        output.join("preflight-receipt.txt"),
        format!(
            "status=ready\ndata=false\nanalysis_head={}\na5_world=closed_world_frozen_graph\na5_abi_guard=required:{A5_BATCH_ATTESTED_GUARD}\ncopy_lend_mode=baseline\na2_mode=off\nderived_substrate_sha256={DIGEST}\nofficial_evaluation_link={}\nofficial_evaluation_target={}\nofficial_evaluation_sha256_start={official_digest}\nofficial_evaluation_link_installed=true\n",
            super::orchestrate::git_sha(),
            official_link.display(),
            official_target.display(),
        ),
    )
    .expect("write A5 batch preflight receipt");
    let preflight = std::env::var("CRAT_A5_BATCH_PREFLIGHT").as_deref() == Ok("1");
    let programs = if preflight {
        vec![super::CORPUS[0], super::CORPUS[2]]
    } else {
        super::CORPUS.to_vec()
    };
    let required_rows = programs.len() * 3;
    let timeout = Duration::from_secs(14_400);
    let modes = [
        ("baseline", "baseline"),
        ("precise", "precise_replay"),
        ("coarse", "coarse_constraint"),
    ];
    let mut rows = Vec::<super::report::Row>::new();

    for (label, mode) in modes {
        for program in &programs {
            let input = program.input_path(&root);
            let shard = output.join(label).join(program.name);
            fs::create_dir_all(&shard).expect("create A5 batch shard");
            let common = vec![
                ("CRAT_BO_A5_MODE", mode.to_owned()),
                (
                    "CRAT_BO_A5_ATTESTATION",
                    "frozen_benchmark_graph".to_owned(),
                ),
                ("CRAT_BO_COPY_LEND_MODE", "baseline".to_owned()),
                ("CRAT_BO_A2_MODE", "off".to_owned()),
                ("CRAT_BO_REPAIR", "mode_a".to_owned()),
                ("CRAT_A5_SNAPSHOT", snapshot.display().to_string()),
                ("CRAT_A5_BATCH_SHARD_DIR", shard.display().to_string()),
                (
                    "CRAT_BOC1_PROJECTION_SNAPSHOT",
                    shard.join("model-projection.tsv").display().to_string(),
                ),
                (
                    "CRAT_BOC1_CROWN_ARTIFACT",
                    official_root.display().to_string(),
                ),
                (
                    "CRAT_A5_OFFICIAL_EVALUATION",
                    official_link.display().to_string(),
                ),
                (
                    "CRAT_A5_OFFICIAL_EVALUATION_SHA256",
                    official_digest.clone(),
                ),
            ];
            eprintln!("[a5-item22] {label}/{} model", program.name);
            let model = super::orchestrate::run_child_labeled(
                program.name,
                &input,
                "a5-batch-model",
                &format!("a5-batch-model-{label}"),
                timeout,
                &common,
            );
            let model_row = model.row.clone().unwrap_or_default();
            if model.status != "ok" || model_row.get("status") != Some("ok") {
                fs::write(
                    output.join("receipt.txt"),
                    format!(
                        "status=failed\ndata=false\nprogram={}\na5_mode={mode}\nphase=model\nchild_status={}\nnote={}\nderived_substrate_sha256={DIGEST}\n",
                        program.name, model.status, model.note
                    ),
                )
                .expect("write failed A5 batch receipt");
                panic!(
                    "A5 item-22 STOP: {label}/{} model status={} note={}",
                    program.name, model.status, model.note
                );
            }

            eprintln!("[a5-item22] {label}/{} rewriter", program.name);
            let rewrite = super::orchestrate::run_child_labeled(
                program.name,
                &input,
                "m1-emit",
                &format!("a5-m1-emit-{label}"),
                timeout,
                &common,
            );
            let rewrite_row = rewrite.row.clone().unwrap_or_default();
            if rewrite.status != "ok" || rewrite_row.get("status") != Some("ok") {
                fs::write(
                    output.join("receipt.txt"),
                    format!(
                        "status=failed\ndata=false\nprogram={}\na5_mode={mode}\nphase=rewriter\nchild_status={}\nnote={}\nderived_substrate_sha256={DIGEST}\n",
                        program.name, rewrite.status, rewrite.note
                    ),
                )
                .expect("write failed A5 batch receipt");
                panic!(
                    "A5 item-22 STOP: {label}/{} rewriter status={} note={}",
                    program.name, rewrite.status, rewrite.note
                );
            }

            let mut combined = super::report::Row::default();
            combined.set("program", program.name);
            combined.set("configuration", label);
            for (key, value) in &model_row.0 {
                if !matches!(key.as_str(), "program" | "mode") {
                    combined.set(key, value);
                }
            }
            for key in [
                "status",
                "emitted",
                "degraded",
                "files_touched",
                "reverted",
                "a5_model_retained_marks",
                "a5_emission_retained_marks",
                "a5_abi_guard",
                "t_total_s",
            ] {
                if let Some(value) = rewrite_row.get(key) {
                    combined.set(&format!("rw_{key}"), value);
                }
            }
            for (key, value) in &rewrite_row.0 {
                if key.starts_with("reason_") {
                    combined.set(&format!("rw_{key}"), value);
                }
            }
            for (key, expected) in [
                ("a5_mode", mode),
                ("a5_world", "closed_world_frozen_graph"),
                ("a5_abi_guard", A5_BATCH_ATTESTED_GUARD),
                ("copy_lend_mode", "baseline"),
                ("a2_mode", "off"),
            ] {
                assert_eq!(combined.get(key), Some(expected), "model stamp {key}");
                assert_eq!(rewrite_row.get(key), Some(expected), "rewriter stamp {key}");
            }
            batch_model_digest_stamp(&combined, &official_digest)
                .expect("per-worker official artifact digest");
            batch_attestation_stamp(&combined).expect("per-worker frozen-graph attestation");
            fs::write(
                shard.join("shard-receipt.txt"),
                format!(
                    "status=ok\ndata=true\nprogram={}\na5_mode={mode}\na5_world=closed_world_frozen_graph\na5_abi_guard={A5_BATCH_ATTESTED_GUARD}\ncopy_lend_mode=baseline\na2_mode=off\nmodel_wall_s={:.3}\nrewriter_wall_s={:.3}\nderived_substrate_sha256={DIGEST}\nofficial_evaluation_link={}\nofficial_evaluation_target={}\nofficial_evaluation_sha256={}\n",
                    program.name,
                    model.wall_s,
                    rewrite.wall_s,
                    official_link.display(),
                    official_target.display(),
                    official_digest,
                ),
            )
            .expect("write A5 shard receipt");
            rows.push(combined);
            fs::write(
                output.join("per-program.csv"),
                super::report::render_csv(&rows),
            )
            .expect("write A5 partial rows");
            fs::write(
                output.join("partial-receipt.txt"),
                format!(
                    "status=running\ndata=false\ncompleted_rows={}\nrequired_rows={required_rows}\nderived_substrate_sha256={DIGEST}\n",
                    rows.len(),
                ),
            )
            .expect("write A5 partial receipt");
        }
    }
    assert_eq!(rows.len(), required_rows);

    let final_digest = batch_sha256(&official_link).expect("rehash official evaluation link");
    assert_eq!(
        final_digest, official_digest,
        "official evaluation digest moved during the sweep"
    );
    if preflight {
        validate_launch4_preflight(&output, &rows, &official_digest)
            .unwrap_or_else(|error| panic!("A5 item-22 launch-4 preflight STOP: {error}"));
        fs::write(
            output.join("preflight-complete.txt"),
            format!(
            "status=ok\ndata=false\nprograms=bst,ht\nconfigurations=baseline,precise_replay,coarse_constraint\nrows=6\na5_abi_guard={A5_BATCH_ATTESTED_GUARD}\nofficial_evaluation_sha256={official_digest}\n"
            ),
        )
        .expect("write A5 launch-4 preflight completion");
        return;
    }
    reconcile_batch_rollback_rows(&mut rows)
        .unwrap_or_else(|error| panic!("A5 item-22 rollback reconciliation STOP: {error}"));
    fs::write(
        output.join("per-program-reconciled.csv"),
        super::report::render_csv(&rows),
    )
    .expect("write A5 reconciled per-program rows");
    let measurement_head = super::orchestrate::git_sha();
    finish_a5_item22_batch(
        &output,
        &rows,
        modes,
        DIGEST,
        &official_link,
        &official_target,
        &official_digest,
        &measurement_head,
    );
}

#[test]
#[ignore = "A5 item-22 aggregation-only replay over preserved launch-4 rows"]
fn a5_item22_batch_aggregate_only() {
    const DIGEST: &str = "db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6";
    const OFFICIAL_DIGEST: &str =
        "7aa16d5b63ff39e6aaabd3590ec2be9c88c9d8a753bd9f74cd4e6056d9974fd7";
    let output = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_BATCH_PRESERVED")
            .expect("aggregation-only replay requires CRAT_A5_BATCH_PRESERVED"),
    );
    assert!(!output.join("aggregate.csv").exists());
    assert!(!output.join("complete.txt").exists());
    let raw = fs::read_to_string(output.join("per-program.csv"))
        .expect("read preserved launch-4 worker rows");
    let mut rows = parse_batch_csv(&raw).expect("parse preserved launch-4 worker rows");
    assert_eq!(rows.len(), 60, "aggregation input row count");
    batch_population_reason_keys(&rows).expect("registered 27-key population universe");

    let mut configurations = BTreeMap::<&str, usize>::new();
    for row in &rows {
        assert_eq!(row.get("status"), Some("ok"), "model worker status");
        assert_eq!(row.get("rw_status"), Some("ok"), "rewriter worker status");
        batch_model_digest_stamp(row, OFFICIAL_DIGEST).expect("preserved digest stamp");
        batch_attestation_stamp(row).expect("preserved attestation stamp");
        *configurations
            .entry(row.get("configuration").expect("configuration stamp"))
            .or_default() += 1;
    }
    assert_eq!(
        configurations,
        BTreeMap::from([("baseline", 20), ("coarse", 20), ("precise", 20)])
    );

    let partial = fs::read_to_string(output.join("partial-receipt.txt"))
        .expect("read preserved partial receipt");
    for stamp in ["data=false", "completed_rows=60", "required_rows=60"] {
        assert!(partial.lines().any(|line| line == stamp), "partial {stamp}");
    }
    let preflight = fs::read_to_string(output.join("preflight-receipt.txt"))
        .expect("read preserved launch preflight receipt");
    let measurement_head = preflight
        .lines()
        .find_map(|line| line.strip_prefix("analysis_head="))
        .expect("measurement analysis head");

    reconcile_batch_rollback_rows(&mut rows)
        .unwrap_or_else(|error| panic!("A5 aggregation-only rollback STOP: {error}"));
    fs::write(
        output.join("per-program-reconciled.csv"),
        super::report::render_csv(&rows),
    )
    .expect("write reconciled launch-4 per-program rows");

    let root = super::orchestrate::workspace_root();
    let official_link = root.join("benchmarks/rs-crown-transformed/evaluation.tsv");
    let official_target = fs::read_link(&official_link).expect("official artifact symlink");
    assert!(official_target.is_absolute());
    assert_eq!(batch_sha256(&official_link).as_deref(), Ok(OFFICIAL_DIGEST));
    finish_a5_item22_batch(
        &output,
        &rows,
        [
            ("baseline", "baseline"),
            ("precise", "precise_replay"),
            ("coarse", "coarse_constraint"),
        ],
        DIGEST,
        &official_link,
        &official_target,
        OFFICIAL_DIGEST,
        measurement_head,
    );
}

#[test]
#[ignore = "A5 W14 drift direct-replay diagnostic over preserved launch-4 models"]
fn a5_w14_drift_soundness_diagnostic() {
    const OLD_EXPOSURE_SHA256: &str =
        "2cbf2f8ec8df784c9a672da1ff32164feb972275fdb968e71be8a66536630e9b";
    const OLD_PAIR_SHA256: &str =
        "a2da08e8fe3871b29eff9f12409c84c1400def2972396d2fc49915fb563ed65a";
    let old_root = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_DRIFT_OLD_ROOT").expect("old W14 artifact root"),
    );
    let launch_root = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_DRIFT_LAUNCH_ROOT").expect("launch-4 artifact root"),
    );
    let old_exposure = old_root.join("w14-exposure-ledger.tsv");
    assert_eq!(
        batch_sha256(&old_exposure).as_deref(),
        Ok(OLD_EXPOSURE_SHA256)
    );
    assert_eq!(
        batch_sha256(&old_root.join("w14-pair-ledger.tsv")).as_deref(),
        Ok(OLD_PAIR_SHA256)
    );
    let output = super::orchestrate::out_dir().join("a5-w14-drift-diagnostic");
    fs::create_dir_all(&output).expect("create W14 drift diagnostic output");
    let root = super::orchestrate::workspace_root();
    let selected = [
        "binn", "brotli", "bzip2", "heman", "json.h", "lodepng", "quadtree",
    ];
    let heavy = ["brotli", "heman", "lodepng"]
        .into_iter()
        .collect::<BTreeSet<_>>();
    let expected = BTreeMap::from([
        ("binn", 5usize),
        ("brotli", 80),
        ("bzip2", 4),
        ("heman", 38),
        ("json.h", 19),
        ("lodepng", 30),
        ("quadtree", 2),
    ]);
    let mut rows = Vec::new();
    let timeout = Duration::from_secs(14_400);
    for name in selected {
        let corpus = super::CORPUS
            .iter()
            .find(|program| program.name == name)
            .expect("drift program in corpus");
        let precise = launch_root.join("precise").join(name);
        let common = vec![
            ("CRAT_BO_FORK_ENGINE", "fork".to_owned()),
            ("CRAT_BO_COPY_LEND_MODE", "baseline".to_owned()),
            ("CRAT_BO_A2_MODE", "off".to_owned()),
            (
                "CRAT_A5_DRIFT_OLD_EXPOSURE",
                old_exposure.display().to_string(),
            ),
            (
                "CRAT_A5_DRIFT_NEW_EXPOSURE",
                precise
                    .join("w14-exposure-ledger.tsv")
                    .display()
                    .to_string(),
            ),
            (
                "CRAT_A5_DRIFT_MODEL",
                precise.join("model.tsv").display().to_string(),
            ),
            (
                "CRAT_A5_DRIFT_SUMMARY",
                precise.join("summary.tsv").display().to_string(),
            ),
            (
                "CRAT_A5_DRIFT_HEAVY",
                usize::from(heavy.contains(name)).to_string(),
            ),
        ];
        let child = super::orchestrate::run_child_labeled(
            name,
            &corpus.input_path(&root),
            "a5-w14-drift-trace",
            "a5-w14-drift-trace",
            timeout,
            &common,
        );
        let row = child.row.unwrap_or_default();
        if child.status != "ok" || row.get("status") != Some("ok") {
            fs::write(
                output.join("receipt.txt"),
                format!(
                    "status=failed\ndata=false\nprogram={name}\nchild_status={}\nnote={}\n",
                    child.status, child.note
                ),
            )
            .expect("write W14 drift failure receipt");
            panic!("W14 drift trace STOP: {name} status={}", child.status);
        }
        assert_eq!(batch_number(&row, "drift_total"), expected[name]);
        rows.push(row);
        fs::write(
            output.join("per-program.csv"),
            super::report::render_csv(&rows),
        )
        .expect("write W14 drift partial rows");
        fs::write(
            output.join("partial-receipt.txt"),
            format!(
                "status=running\ndata=false\ncompleted_programs={}\nrequired_programs=7\n",
                rows.len()
            ),
        )
        .expect("write W14 drift partial receipt");
    }
    let sum = |key| rows.iter().map(|row| batch_number(row, key)).sum::<usize>();
    assert_eq!(sum("drift_total"), 178);
    assert_eq!(sum("drift_sampled"), 60);
    if sum("conflicting_rows") != 0 || sum("conflict_edges") != 0 {
        fs::write(
            output.join("receipt.txt"),
            format!(
                "status=production-defect\ndata=false\nconflicting_rows={}\nconflict_edges={}\n",
                sum("conflicting_rows"),
                sum("conflict_edges")
            ),
        )
        .expect("write W14 drift production-defect receipt");
        panic!("W14 drift direct replay found a production conflict");
    }
    fs::write(
        output.join("receipt.txt"),
        format!(
            "schema=a5-w14-drift-v1\nstatus=ok\ndata=false\nanalysis_head={}\nold_exposure_sha256={OLD_EXPOSURE_SHA256}\nold_pair_sha256={OLD_PAIR_SHA256}\nidentity_rows=178\nfamily_stale_registered_expectation=178\nfamily_producer_change=0\nfamily_replay_classification_change=0\nsample_rule=exhaustive-sloc-le-4413-or-losses-le-10;first-10-pinned-identity-otherwise\nsampled_rows=60\nconflicting_rows=0\nconflict_edges=0\ntrace_kind=direct-replay-production-overlap-map\n",
            super::orchestrate::git_sha()
        ),
    )
    .expect("write W14 drift diagnostic receipt");
}

#[test]
#[ignore = "A5 production-site versus registered-site exact join diagnostic"]
fn a5_production_site_join_diagnostic() {
    let launch_root = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_SITE_JOIN_LAUNCH_ROOT").expect("launch-4 artifact root"),
    );
    let output = super::orchestrate::out_dir().join("a5-production-site-join");
    fs::create_dir_all(&output).expect("create production-site join output");
    let root = super::orchestrate::workspace_root();
    let timeout = Duration::from_secs(14_400);
    let mut rows = Vec::new();
    for program in super::CORPUS {
        let precise = launch_root.join("precise").join(program.name);
        let common = vec![
            (
                "CRAT_A5_SITE_JOIN_W14_PAIR",
                precise.join("w14-pair-ledger.tsv").display().to_string(),
            ),
            (
                "CRAT_A5_SITE_JOIN_LEDGER",
                precise
                    .join("production-site-ledger.tsv")
                    .display()
                    .to_string(),
            ),
            (
                "CRAT_A5_SITE_JOIN_RECEIPT",
                precise
                    .join("construction-receipt.txt")
                    .display()
                    .to_string(),
            ),
        ];
        let child = super::orchestrate::run_child_labeled(
            program.name,
            &program.input_path(&root),
            "a5-production-site-join",
            "a5-production-site-join",
            timeout,
            &common,
        );
        let row = child.row.unwrap_or_default();
        if child.status != "ok" || row.get("status") != Some("ok") {
            fs::write(
                output.join("receipt.txt"),
                format!(
                    "status=failed\ndata=false\nprogram={}\nchild_status={}\nnote={}\n",
                    program.name, child.status, child.note
                ),
            )
            .expect("write site-join failure receipt");
            panic!(
                "A5 production-site join STOP: {} status={}",
                program.name, child.status
            );
        }
        rows.push(row);
        fs::write(
            output.join("per-program.csv"),
            super::report::render_csv(&rows),
        )
        .expect("write site-join partial rows");
        fs::write(
            output.join("partial-receipt.txt"),
            format!(
                "status=running\ndata=false\ncompleted_programs={}\nrequired_programs=20\n",
                rows.len()
            ),
        )
        .expect("write site-join partial receipt");
    }
    let sum = |key| rows.iter().map(|row| batch_number(row, key)).sum::<usize>();
    assert_eq!(sum("registered_site_rows"), 5_555);
    assert_eq!(sum("production_site_pairs"), 3_422);
    assert_eq!(
        sum("production_site_pairs"),
        sum("production_mut_mut")
            + sum("production_mut_read_only")
            + sum("production_shared_shared")
    );
    let registered_unmatched = sum("registered_unmatched");
    let production_unmatched = sum("production_unmatched");
    let mixed = sum("mixed_class_pairs");
    let ambiguous = sum("ambiguous_summary_keys");
    let multi = sum("multi_expansion_pairs");
    let status = if mixed != 0 || ambiguous != 0 {
        "ambiguous"
    } else if registered_unmatched != 0 || production_unmatched != 0 {
        "scope-loss"
    } else {
        "exact-granularity"
    };
    fs::write(
        output.join("receipt.txt"),
        format!(
            "schema=a5-production-site-join-v1\nstatus={status}\ndata=false\nanalysis_head={}\nregistered_site_rows={}\nproduction_site_pairs={}\nmatched_registered_rows={}\nunique_matched_production_pairs={}\nregistered_unmatched={registered_unmatched}\nproduction_unmatched={production_unmatched}\nmixed_class_pairs={mixed}\nambiguous_summary_keys={ambiguous}\nmulti_expansion_pairs={multi}\nmatched_mut_mut={}\nmatched_mut_read_only={}\nmatched_shared_shared={}\nunmatched_mut_mut={}\nunmatched_mut_read_only={}\nunmatched_shared_shared={}\nproduction_mut_mut={}\nproduction_mut_read_only={}\nproduction_shared_shared={}\nmodel_impact=changed-injected-facts-if-scope-restored\n",
            super::orchestrate::git_sha(),
            sum("registered_site_rows"),
            sum("production_site_pairs"),
            sum("matched_registered_rows"),
            sum("unique_matched_production_pairs"),
            sum("matched_mut_mut"),
            sum("matched_mut_read_only"),
            sum("matched_shared_shared"),
            sum("unmatched_mut_mut"),
            sum("unmatched_mut_read_only"),
            sum("unmatched_shared_shared"),
            sum("production_mut_mut"),
            sum("production_mut_read_only"),
            sum("production_shared_shared"),
        ),
    )
    .expect("write production-site join receipt");
}

#[test]
#[ignore = "A5 attempt-3 in-process precise-frame site-scope repartition"]
fn a5_site_scope_repartition_diagnostic() {
    let launch_root = std::path::PathBuf::from(
        std::env::var_os("CRAT_A5_SCOPE_LAUNCH_ROOT").expect("launch-4 artifact root"),
    );
    let output = super::orchestrate::out_dir().join("a5-site-scope-repartition");
    fs::create_dir_all(&output).expect("create site-scope repartition output");
    let root = super::orchestrate::workspace_root();
    let timeout = Duration::from_secs(14_400);
    let mut rows = Vec::new();
    for program in super::CORPUS {
        let shard = output.join("precise").join(program.name);
        let common = vec![
            (
                "CRAT_A5_SCOPE_W14_PAIR",
                launch_root
                    .join("precise")
                    .join(program.name)
                    .join("w14-pair-ledger.tsv")
                    .display()
                    .to_string(),
            ),
            ("CRAT_A5_SCOPE_SHARD", shard.display().to_string()),
        ];
        let child = super::orchestrate::run_child_labeled(
            program.name,
            &program.input_path(&root),
            "a5-site-scope-repartition",
            "a5-site-scope-repartition",
            timeout,
            &common,
        );
        let row = child.row.unwrap_or_default();
        if child.status != "ok" || row.get("status") != Some("ok") {
            fs::write(
                output.join("receipt.txt"),
                format!(
                    "status=failed\ndata=false\nprogram={}\nchild_status={}\nnote={}\n",
                    program.name, child.status, child.note
                ),
            )
            .expect("write scope-repartition failure receipt");
            panic!(
                "A5 scope-repartition STOP: {} status={}",
                program.name, child.status
            );
        }
        rows.push(row);
        fs::write(
            output.join("per-program.csv"),
            super::report::render_csv(&rows),
        )
        .expect("write scope-repartition partial rows");
    }
    let sum = |key| rows.iter().map(|row| batch_number(row, key)).sum::<usize>();
    assert_eq!(sum("registered_site_rows"), 5_555);
    let family_keys = rows
        .iter()
        .flat_map(|row| row.0.iter().map(|(key, _)| key.as_str()))
        .filter(|key| key.starts_with("family_"))
        .collect::<BTreeSet<_>>();
    let optional_sum = |key| {
        rows.iter()
            .map(|row| batch_optional_number(row, key).expect("optional numeric family"))
            .sum::<usize>()
    };
    let family_total = family_keys
        .iter()
        .map(|key| optional_sum(key))
        .sum::<usize>();
    assert_eq!(family_total, 5_555);
    let residual = sum("registered_unmatched");
    let residual_family_keys = rows
        .iter()
        .flat_map(|row| row.0.iter().map(|(key, _)| key.as_str()))
        .filter(|key| key.starts_with("residual_family_"))
        .collect::<BTreeSet<_>>();
    let residual_family_total = residual_family_keys
        .iter()
        .map(|key| optional_sum(key))
        .sum::<usize>();
    assert_eq!(residual_family_total, residual);
    let mut families = String::new();
    for key in &family_keys {
        families.push_str(&format!("{}={}\n", key, optional_sum(key)));
    }
    for key in &residual_family_keys {
        families.push_str(&format!("{}={}\n", key, optional_sum(key)));
    }
    fs::write(
        output.join("receipt.txt"),
        format!(
            "schema=a5-site-scope-repartition-v1\nstatus=ok\ndata=false\nanalysis_head={}\nprograms=20\nregistered_site_rows={}\nproduction_site_pairs={}\nregistered_unmatched={}\nproduction_unmatched={}\nmixed_class_pairs={}\nambiguous_summary_keys={}\n{families}",
            super::orchestrate::git_sha(),
            sum("registered_site_rows"),
            sum("production_site_pairs"),
            residual,
            sum("production_unmatched"),
            sum("mixed_class_pairs"),
            sum("ambiguous_summary_keys"),
        ),
    )
    .expect("write scope-repartition receipt");
}

fn finish_a5_item22_batch(
    output: &Path,
    rows: &[super::report::Row],
    modes: [(&str, &str); 3],
    digest: &str,
    official_link: &Path,
    official_target: &Path,
    official_digest: &str,
    measurement_head: &str,
) {
    let reason_keys = batch_population_reason_keys(rows)
        .unwrap_or_else(|error| panic!("A5 batch reason-schema STOP: {error}"));
    assert_eq!(reason_keys.len(), 27, "A5 batch 27-key oracle cardinality");
    let mut aggregates = Vec::new();
    for (label, mode) in modes {
        let selected = rows
            .iter()
            .filter(|row| row.get("configuration") == Some(label))
            .collect::<Vec<_>>();
        assert_eq!(selected.len(), 20);
        let sum = |key| {
            selected
                .iter()
                .map(|row| batch_number(row, key))
                .sum::<usize>()
        };
        let mut row = super::report::Row::default();
        row.set("configuration", label);
        row.set("a5_mode", mode);
        row.set("a5_world", "closed_world_frozen_graph");
        row.set("a5_abi_guard", A5_BATCH_ATTESTED_GUARD);
        row.set("copy_lend_mode", "baseline");
        row.set("a2_mode", "off");
        row.set("accepted", selected.len());
        for key in [
            "n_ref",
            "n_raw",
            "n_own",
            "n_ref_d0",
            "n_own_d0",
            "sources_total",
            "sources_kept",
            "sinks_total",
            "sinks_kept",
            "s23_stores_owned",
            "s23_owning_model",
            "a5_production_pair_den",
            "a5_production_mut_mut",
            "a5_production_mut_read_only",
            "a5_production_shared_shared",
            "a5_planned_marks",
            "a5_model_retained_marks",
            "rw_emitted",
            "rw_degraded",
            "rw_reverted",
            "rw_reverted_after_verify_failure",
            "rw_decided_ref",
            "rw_degraded_pre_revert",
            "rw_subjects_pre_revert",
            "rw_subjects_post_revert",
            "rw_a5_model_retained_marks",
            "rw_a5_emission_retained_marks",
        ] {
            row.set(key, sum(key));
        }
        row.set("rw_reason_key_count", reason_keys.len());
        for key in &reason_keys {
            let count = selected
                .iter()
                .filter_map(|program| program.get(key))
                .map(|value| value.parse::<usize>().expect("numeric reason count"))
                .sum::<usize>();
            row.set(key, count);
        }
        let expected_reverted = match label {
            "baseline" => 1_056,
            "precise" => 984,
            "coarse" => 860,
            other => panic!("unknown A5 batch configuration {other}"),
        };
        assert_eq!(sum("rw_reverted"), expected_reverted, "{label} reverted");
        assert_eq!(
            sum("rw_reverted_after_verify_failure"),
            expected_reverted,
            "{label} operational rollback"
        );
        assert_eq!(
            sum("rw_decided_ref"),
            sum("rw_emitted") + sum("rw_reverted"),
            "{label} S2b decided-ref identity"
        );
        assert_eq!(
            sum("rw_subjects_pre_revert"),
            sum("rw_subjects_post_revert"),
            "{label} S2b two-frame population identity"
        );
        let mut projection = BTreeMap::<String, usize>::new();
        for program in super::CORPUS {
            let source = fs::read_to_string(
                output
                    .join(label)
                    .join(program.name)
                    .join("model-projection.tsv"),
            )
            .expect("read A5 projection snapshot");
            for line in source.lines().skip(1) {
                let fields = line.split('\t').collect::<Vec<_>>();
                assert_eq!(fields.len(), 9, "projection row width");
                *projection.entry(fields[2].to_owned()).or_default() += 1;
            }
        }
        let projection_total = projection.values().sum::<usize>();
        assert_eq!(projection_total, 2_414, "official projection universe");
        row.set("projection_total", projection_total);
        row.set(
            "projection_ref_backed",
            projection
                .get("predicted-eliminated-ref-backed")
                .copied()
                .unwrap_or(0),
        );
        row.set(
            "projection_owning_backed",
            projection
                .get("predicted-eliminated-owning-backed")
                .copied()
                .unwrap_or(0),
        );
        row.set(
            "projection_remaining",
            projection.get("predicted-remaining").copied().unwrap_or(0),
        );
        row.set(
            "projection_unmapped",
            projection
                .get("unmapped-counted-remaining")
                .copied()
                .unwrap_or(0),
        );
        if label == "precise" {
            for key in [
                "a5_w14_pairs",
                "a5_w14_mut_mut",
                "a5_w14_mut_read_only",
                "a5_w14_shared_shared",
                "a5_w14_effective_pairs",
                "a5_w14_planned_marks",
                "a5_w14_model_retained_marks",
                "a5_w14_demoted_by_model_marks",
                "a5_w14_exposures",
                "a5_w14_demoted",
                "a5_w14_marked",
                "a5_w14_shared_safe",
                "a5_w14_replay_safe",
                "a5_w14_unresolved",
                "a5_w14_precise_rounds",
                "a5_site_join_registered_site_rows",
                "a5_site_join_production_site_pairs",
                "a5_site_join_matched_registered_rows",
                "a5_site_join_unique_matched_production_pairs",
                "a5_site_join_registered_unmatched",
                "a5_site_join_production_unmatched",
                "a5_site_join_production_count_residual",
                "a5_site_join_ambiguous_summary_keys",
                "a5_site_join_ambiguous_production_keys",
                "a5_site_join_mixed_class_pairs",
                "a5_site_join_multi_expansion_pairs",
                "a5_site_join_matched_mut_mut",
                "a5_site_join_matched_mut_read_only",
                "a5_site_join_matched_shared_shared",
                "a5_site_join_production_mut_mut",
                "a5_site_join_production_mut_read_only",
                "a5_site_join_production_shared_shared",
            ] {
                row.set(key, sum(key));
            }
        }
        aggregates.push(row);
    }

    let precise = &aggregates[1];
    for aggregate in &aggregates {
        assert_eq!(
            batch_number(aggregate, "projection_unmapped"),
            254,
            "official projection unmapped validity limit"
        );
    }
    for (key, expected) in [
        ("a5_w14_pairs", 5_555),
        ("a5_w14_mut_mut", 2_391),
        ("a5_w14_mut_read_only", 2_480),
        ("a5_w14_shared_shared", 684),
        ("a5_w14_planned_marks", 4),
        ("a5_w14_exposures", 2_014),
        ("a5_w14_shared_safe", 114),
        ("a5_w14_unresolved", 0),
    ] {
        assert_eq!(
            batch_number(precise, key),
            expected,
            "A5 item-22 gate {key}"
        );
    }
    for (key, expected) in [
        ("a5_site_join_registered_site_rows", 5_555),
        ("a5_site_join_production_site_pairs", 5_555),
        ("a5_site_join_matched_registered_rows", 5_555),
        ("a5_site_join_unique_matched_production_pairs", 5_555),
        ("a5_site_join_registered_unmatched", 0),
        ("a5_site_join_production_unmatched", 0),
        ("a5_site_join_production_count_residual", 0),
        ("a5_site_join_ambiguous_summary_keys", 0),
        ("a5_site_join_ambiguous_production_keys", 0),
        ("a5_site_join_mixed_class_pairs", 0),
        ("a5_site_join_multi_expansion_pairs", 0),
        ("a5_site_join_matched_mut_mut", 2_391),
        ("a5_site_join_matched_mut_read_only", 2_480),
        ("a5_site_join_matched_shared_shared", 684),
        ("a5_site_join_production_mut_mut", 2_391),
        ("a5_site_join_production_mut_read_only", 2_480),
        ("a5_site_join_production_shared_shared", 684),
    ] {
        assert_eq!(
            batch_number(precise, key),
            expected,
            "A5 item-22 permanent site-join gate {key}"
        );
    }
    for aggregate in [&aggregates[1], &aggregates[2]] {
        assert_eq!(batch_number(aggregate, "a5_production_pair_den"), 5_555);
        assert_eq!(batch_number(aggregate, "a5_production_mut_mut"), 2_391);
        assert_eq!(
            batch_number(aggregate, "a5_production_mut_read_only"),
            2_480
        );
        assert_eq!(batch_number(aggregate, "a5_production_shared_shared"), 684);
    }
    assert!(
        batch_number(precise, "rw_a5_emission_retained_marks")
            <= batch_number(precise, "rw_a5_model_retained_marks")
    );

    fs::write(
        output.join("aggregate.csv"),
        super::report::render_csv(&aggregates),
    )
    .expect("write A5 aggregate");
    fs::write(
        output.join("receipt.txt"),
        format!(
            "schema=a5-item22-batch-v1\nstatus=ok\ndata=true\nanalysis_head={measurement_head}\naggregation_head={}\nprograms=20\nconfigurations=baseline,precise_replay,coarse_constraint\na5_world=closed_world_frozen_graph\na5_abi_guard={A5_BATCH_ATTESTED_GUARD}\ncopy_lend_mode=baseline\na2_mode=off\nz3_smt_seed=0\nz3_sat_seed=0\nmem_cap_mib=49152\nworker_bound_s=14400\nderived_substrate_sha256={digest}\nofficial_evaluation_link={}\nofficial_evaluation_target={}\nofficial_evaluation_sha256_start={official_digest}\nofficial_evaluation_sha256_end={official_digest}\nofficial_evaluation_link_installed=true\n",
            super::orchestrate::git_sha(),
            official_link.display(),
            official_target.display(),
        ),
    )
    .expect("write A5 batch receipt");
    let manifest = write_batch_manifest(output).expect("write A5 batch manifest");
    fs::write(
        output.join("complete.txt"),
        format!("status=ok\ndata=true\nmanifest_sha256={manifest}\n"),
    )
    .expect("write A5 batch completion");
}

pub(super) fn run_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> super::report::Row {
    let t0 = Instant::now();
    let mut row = super::report::Row::default();
    let focused_w14 = std::env::var("CRAT_A5_W14_FOCUSED").as_deref() == Ok("1");
    row.set("copy_lend_mode", CopyLendMode::Baseline.label());
    row.set("a5_world", A5World::ClosedWorldFrozenGraph.label());
    row.set(
        "a5_mode",
        if focused_w14 {
            "precise_replay"
        } else {
            "classifier_differential"
        },
    );
    row.set(
        "a5_abi_guard",
        if focused_w14 {
            "permitted:measurement-frozen-graph-attested"
        } else {
            "not-yet-consumed-item4"
        },
    );
    let program = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_owned());
    let Some(snapshot) = std::env::var_os("CRAT_A5_SNAPSHOT").map(std::path::PathBuf::from) else {
        row.set("status", "missing-snapshot");
        return row;
    };
    let measured = snapshot_formals(&snapshot, &program).and_then(|formals| {
        let t_model = Instant::now();
        let rust_program = super::collect_program(tcx);
        let accepted = accepted_current_model(tcx, &rust_program, &formals)?;
        let model_time = t_model.elapsed();
        measure_tcx(
            &program,
            tcx,
            &formals,
            &accepted,
            model_time,
            focused_w14,
            None,
        )
    });
    match measured {
        Ok(measured) => {
            let counts = &measured.counts;
            for pair in &measured.pairs {
                println!("{}", render_pair_line(pair));
            }
            for mark in &measured.final_marks {
                let params = mark.pair.params();
                println!(
                    "A5C9MARK\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                    mark.caller,
                    mark.location.block,
                    mark.location.statement_index,
                    params.first(),
                    params.second(),
                    match mark.shared_side {
                        PairSide::Left => "left",
                        PairSide::Right => "right",
                    },
                    mark.pointee_type,
                    mark.targets
                        .iter()
                        .map(u32::to_string)
                        .collect::<Vec<_>>()
                        .join(",")
                );
            }
            if let Some(w14) = &measured.w14 {
                for pair in &w14.pairs {
                    println!("{}", render_extended_pair_line(pair));
                }
                for exposure in &w14.exposures {
                    println!("{}", render_exposure_line(exposure));
                }
                let exposure_count = |class| {
                    w14.exposures
                        .iter()
                        .filter(|row| row.class == class)
                        .count()
                };
                let incidence_count = |mut_mut, mut_read_only, shared_shared| {
                    w14.exposures
                        .iter()
                        .filter(|row| {
                            matches!(row.class, ExposureClass::Marked | ExposureClass::ReplaySafe)
                                && row.effective_mut_mut == mut_mut
                                && row.effective_mut_read_only == mut_read_only
                                && row.effective_shared_shared == shared_shared
                        })
                        .count()
                };
                row.set("a5_w14_pairs", w14.pairs.len());
                row.set(
                    "a5_w14_effective_pairs",
                    w14.pairs
                        .iter()
                        .filter(|pair| pair.effective_overlap)
                        .count(),
                );
                row.set(
                    "a5_w14_selected_marks",
                    w14.pairs.iter().filter(|pair| pair.selected_mark).count(),
                );
                row.set(
                    "a5_w14_planned_marks",
                    w14.pairs.iter().filter(|pair| pair.planned_mark).count(),
                );
                row.set(
                    "a5_w14_demoted_by_model",
                    w14.pairs
                        .iter()
                        .filter(|pair| pair.planned_mark && !pair.selected_mark)
                        .count(),
                );
                row.set("a5_w14_exposures", w14.exposures.len());
                row.set("a5_w14_demoted", exposure_count(ExposureClass::Demoted));
                row.set("a5_w14_marked", exposure_count(ExposureClass::Marked));
                row.set(
                    "a5_w14_shared_safe",
                    exposure_count(ExposureClass::SharedSafe),
                );
                row.set(
                    "a5_w14_replay_safe",
                    exposure_count(ExposureClass::ReplaySafe),
                );
                row.set(
                    "a5_w14_unresolved",
                    exposure_count(ExposureClass::Unresolved),
                );
                row.set("a5_w14_incidence_m", incidence_count(true, false, false));
                row.set("a5_w14_incidence_mr", incidence_count(true, true, false));
                row.set("a5_w14_incidence_r", incidence_count(false, true, false));
                row.set("a5_w14_incidence_rs", incidence_count(false, true, true));
                row.set("a5_w14_replay_safe_definition", REPLAY_SAFE_DEFINITION);
                row.set("a5_w14_precise_rounds", w14.precise_rounds);
            }
            println!("{}", render_count_line(counts));
            row.set("status", "ok");
            row.set("c1", counts.sites_with_two_ref_args);
            row.set("c2", counts.sites_not_proven_disjoint);
            row.set("c3", counts.attributed_predicted_refs);
            row.set("c3_depth0", counts.attributed_predicted_refs_depth0);
            row.set("cg_num", counts.unknown_caller_reachable);
            row.set("cg_den", counts.local_functions);
            row.set("pair_den", counts.pair_denominator);
            row.set("mut_mut", counts.mut_mut);
            row.set("mut_read_only", counts.mut_read_only);
            row.set("shared_shared", counts.shared_shared);
            row.set("sites_with_mut_mut", counts.sites_with_mut_mut);
            row.set("sites_with_mut_read_only", counts.sites_with_mut_read_only);
            row.set("sites_with_shared_shared", counts.sites_with_shared_shared);
            row.set("mut_default_fires", counts.mutability_default_fires);
            row.set("a5_classifier_api", "shared-v1");
            row.set("a5_classifier_candidates", measured.classifier.candidates);
            row.set(
                "a5_classifier_not_proven",
                measured.classifier.not_proven_disjoint,
            );
            row.set(
                "a5_classifier_byte_mismatches",
                measured.classifier.byte_mismatches,
            );
            row.set("a5_snapshot_total", measured.snapshot.mut_read_only);
            row.set("a5_snapshot_markable", measured.snapshot.markable);
            row.set(
                "a5_snapshot_read_after_write",
                measured.snapshot.read_after_write,
            );
            row.set("a5_snapshot_opaque_escape", measured.snapshot.opaque_escape);
            row.set("a5_snapshot_recursive", measured.snapshot.recursive);
            row.set(
                "a5_snapshot_volatile_or_atomic",
                measured.snapshot.volatile_or_atomic,
            );
            row.set("a5_snapshot_unresolved", measured.snapshot.unresolved);
            row.set(
                "a5_snapshot_target_type_mismatch",
                measured.snapshot.target_type_mismatch,
            );
            row.set(
                "a5_snapshot_noncopy_scalar",
                measured.snapshot.noncopy_scalar,
            );
            row.set(
                "a5_snapshot_final_markable",
                measured.snapshot.final_markable,
            );
            row.set(
                "a5_snapshot_all_witness_demoted",
                measured.snapshot.all_witness_demoted,
            );
            row.set(
                "a5_snapshot_filter_unresolved",
                measured.snapshot.filter_unresolved,
            );
            row.set("a5_c9_final_marks", measured.final_marks.len());
            row.set("calls_total", measured.coverage.calls_total);
            row.set("direct_local", measured.coverage.direct_local);
            row.set("indirect_local", measured.coverage.indirect_local);
            row.set("direct_external", measured.coverage.direct_external);
            row.set("indirect_unresolved", measured.coverage.indirect_unresolved);
            row.set("non_fn_def_constant", measured.coverage.non_fn_def_constant);
            row.set(
                "t_origins_s",
                format!("{:.3}", measured.timings.origins.as_secs_f64()),
            );
            row.set(
                "t_andersen_s",
                format!("{:.3}", measured.timings.andersen.as_secs_f64()),
            );
            row.set(
                "t_model_s",
                format!("{:.3}", measured.timings.accepted_model.as_secs_f64()),
            );
        }
        Err(why) => {
            row.set("status", "a5-error");
            row.set("detail", super::report::sanitize(&why));
        }
    }
    row.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    row.set(
        "t_total_s",
        format!("{:.3}", (t0.elapsed() + t_tcx).as_secs_f64()),
    );
    row
}

fn render_base_line(counts: &ProgramCounts) -> String {
    render_count_line_with_sentinel(BASE_SENTINEL, counts)
}

fn render_count_line(counts: &ProgramCounts) -> String {
    render_count_line_with_sentinel(COUNT_SENTINEL, counts)
}

fn render_count_line_with_sentinel(sentinel: &str, counts: &ProgramCounts) -> String {
    counts
        .validate()
        .expect("only valid P1 counts may be rendered");
    format!(
        "{sentinel}program={} c1={} c2={} c3={} c3_depth0={} cg_num={} cg_den={} pair_den={} mut_mut={} mut_read_only={} shared_shared={} site_mut_mut={} site_mut_read_only={} site_shared_shared={} mut_default_fires={}",
        counts.program,
        counts.sites_with_two_ref_args,
        counts.sites_not_proven_disjoint,
        counts.attributed_predicted_refs,
        counts.attributed_predicted_refs_depth0,
        counts.unknown_caller_reachable,
        counts.local_functions,
        counts.pair_denominator,
        counts.mut_mut,
        counts.mut_read_only,
        counts.shared_shared,
        counts.sites_with_mut_mut,
        counts.sites_with_mut_read_only,
        counts.sites_with_shared_shared,
        counts.mutability_default_fires,
    )
}

fn render_pair_line(pair: &PairLedgerRow) -> String {
    pair.validate()
        .expect("only valid count-(5) pair rows may be rendered");
    format!(
        "{PAIR_SENTINEL}{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
        pair.program,
        pair.site,
        pair.left_argument,
        pair.right_argument,
        pair.class.label(),
        usize::from(pair.left_mutable),
        usize::from(pair.right_mutable),
        pair.left_default_fires,
        pair.right_default_fires,
    )
}

fn kind_label(kind: SlotKind) -> &'static str {
    match kind {
        SlotKind::Raw => "raw",
        SlotKind::Ref => "ref",
        SlotKind::Owning => "owning",
    }
}

fn formal_label(formal: &FormalKey) -> String {
    format!("{}#{}@{}", formal.function, formal.parameter, formal.depth)
}

fn render_extended_pair_line(row: &ExtendedPairLedgerRow) -> String {
    let targets = row
        .target_formals
        .iter()
        .map(|target| {
            format!(
                "{}[{}]#{}/{}",
                target.function.path,
                target.function.key,
                target.left_parameter,
                target.right_parameter
            )
        })
        .collect::<Vec<_>>()
        .join("|");
    let left = row
        .left_formals
        .iter()
        .map(formal_label)
        .collect::<Vec<_>>()
        .join("|");
    let right = row
        .right_formals
        .iter()
        .map(formal_label)
        .collect::<Vec<_>>()
        .join("|");
    format!(
        "{W14_PAIR_SENTINEL}{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\tbaseline\tprecise_replay\tclosed_world_frozen_graph\tpermitted:measurement-frozen-graph-attested\t{}\t{}",
        row.pair.program,
        row.pair.site,
        row.pair.left_argument,
        row.pair.right_argument,
        row.pair.class.label(),
        targets,
        left,
        right,
        usize::from(row.raw_overlap),
        usize::from(row.effective_overlap),
        row.markability,
        usize::from(row.selected_mark),
        usize::from(row.planned_mark),
        row.model_attribution,
    )
}

fn render_exposure_line(row: &ExposureLedgerRow) -> String {
    let incidence = format!(
        "{}{}{}",
        if row.effective_mut_mut { "M" } else { "" },
        if row.effective_mut_read_only { "R" } else { "" },
        if row.effective_shared_shared { "S" } else { "" },
    );
    format!(
        "{W14_EXPOSURE_SENTINEL}{}\t{}\t{}\t{}\t{}\t{}\t{}->{}\t{}\tbaseline\tprecise_replay\tclosed_world_frozen_graph\tpermitted:measurement-frozen-graph-attested\t{}\t{}\t{}\t{}",
        row.program,
        row.formal.function,
        row.formal.parameter,
        row.formal.depth,
        kind_label(row.baseline),
        kind_label(row.precise),
        kind_label(row.baseline),
        kind_label(row.precise),
        row.class.label(),
        usize::from(row.effective_mut_mut),
        usize::from(row.effective_mut_read_only),
        usize::from(row.effective_shared_shared),
        if incidence.is_empty() {
            "none"
        } else {
            &incidence
        },
    )
}

fn parse_pair_line(line: &str) -> Result<PairLedgerRow, String> {
    let columns = line
        .trim_end()
        .strip_prefix(PAIR_SENTINEL)
        .ok_or_else(|| "missing A5P1PAIR sentinel".to_owned())?
        .split('\t')
        .collect::<Vec<_>>();
    if columns.len() != 9 {
        return Err(format!(
            "pair ledger row has {} columns, expected 9",
            columns.len()
        ));
    }
    let number = |index: usize, name: &str| {
        columns[index]
            .parse::<usize>()
            .map_err(|why| format!("invalid pair `{name}`: {why}"))
    };
    let boolean = |index: usize, name: &str| match columns[index] {
        "0" => Ok(false),
        "1" => Ok(true),
        other => Err(format!("invalid pair `{name}` boolean `{other}`")),
    };
    let class = match columns[4] {
        "mut_mut" => PairMutability::MutMut,
        "mut_read_only" => PairMutability::MutReadOnly,
        "shared_shared" => PairMutability::SharedShared,
        other => return Err(format!("invalid pair class `{other}`")),
    };
    let row = PairLedgerRow {
        program: columns[0].to_owned(),
        site: columns[1].to_owned(),
        left_argument: number(2, "left_argument")?,
        right_argument: number(3, "right_argument")?,
        class,
        left_mutable: boolean(5, "left_mutable")?,
        right_mutable: boolean(6, "right_mutable")?,
        left_default_fires: number(7, "left_default_fires")?,
        right_default_fires: number(8, "right_default_fires")?,
    };
    row.validate()?;
    Ok(row)
}

fn parse_count_line(line: &str) -> Result<ProgramCounts, String> {
    parse_count_line_with_sentinel(COUNT_SENTINEL, line)
}

fn parse_base_line(line: &str) -> Result<ProgramCounts, String> {
    parse_count_line_with_sentinel(BASE_SENTINEL, line)
}

fn parse_count_line_with_sentinel(sentinel: &str, line: &str) -> Result<ProgramCounts, String> {
    let body = line
        .trim()
        .strip_prefix(sentinel)
        .ok_or_else(|| format!("missing {} sentinel", sentinel.trim()))?;
    let mut fields = BTreeMap::new();
    for token in body.split_whitespace() {
        let (key, value) = token
            .split_once('=')
            .ok_or_else(|| format!("malformed token `{token}`"))?;
        if fields.insert(key, value).is_some() {
            return Err(format!("duplicate field `{key}`"));
        }
    }
    const EXPECTED: [&str; 15] = [
        "program",
        "c1",
        "c2",
        "c3",
        "c3_depth0",
        "cg_num",
        "cg_den",
        "pair_den",
        "mut_mut",
        "mut_read_only",
        "shared_shared",
        "site_mut_mut",
        "site_mut_read_only",
        "site_shared_shared",
        "mut_default_fires",
    ];
    if fields.len() != EXPECTED.len() || EXPECTED.iter().any(|key| !fields.contains_key(key)) {
        return Err("count row does not contain the exact P1 schema".to_owned());
    }
    let number = |key: &str| -> Result<usize, String> {
        fields[key]
            .parse::<usize>()
            .map_err(|error| format!("invalid `{key}`: {error}"))
    };
    let counts = ProgramCounts {
        program: fields["program"].to_owned(),
        sites_with_two_ref_args: number("c1")?,
        sites_not_proven_disjoint: number("c2")?,
        attributed_predicted_refs: number("c3")?,
        attributed_predicted_refs_depth0: number("c3_depth0")?,
        unknown_caller_reachable: number("cg_num")?,
        local_functions: number("cg_den")?,
        pair_denominator: number("pair_den")?,
        mut_mut: number("mut_mut")?,
        mut_read_only: number("mut_read_only")?,
        shared_shared: number("shared_shared")?,
        sites_with_mut_mut: number("site_mut_mut")?,
        sites_with_mut_read_only: number("site_mut_read_only")?,
        sites_with_shared_shared: number("site_shared_shared")?,
        mutability_default_fires: number("mut_default_fires")?,
    };
    counts.validate()?;
    Ok(counts)
}

fn parse_single_raw_line(stdout: &str, sentinel: &str) -> Result<(String, ProgramCounts), String> {
    let lines = stdout
        .lines()
        .filter(|line| line.starts_with(sentinel))
        .collect::<Vec<_>>();
    if lines.len() != 1 {
        return Err(format!(
            "expected exactly one {} raw row, found {}",
            sentinel.trim(),
            lines.len()
        ));
    }
    let counts = parse_count_line_with_sentinel(sentinel, lines[0])?;
    Ok((lines[0].to_owned(), counts))
}

fn parse_pair_ledger(stdout: &str, counts: &ProgramCounts) -> Result<Vec<PairLedgerRow>, String> {
    let pairs = stdout
        .lines()
        .filter(|line| line.starts_with(PAIR_SENTINEL))
        .map(parse_pair_line)
        .collect::<Result<Vec<_>, _>>()?;
    if pairs.iter().any(|pair| pair.program != counts.program) {
        return Err("pair ledger contains a different program identity".to_owned());
    }
    let mut identities = BTreeSet::new();
    if pairs.iter().any(|pair| {
        !identities.insert((pair.site.as_str(), pair.left_argument, pair.right_argument))
    }) {
        return Err("pair ledger contains a duplicate exact pair identity".to_owned());
    }
    let mut by_class = BTreeMap::new();
    for pair in &pairs {
        *by_class.entry(pair.class).or_insert(0usize) += 1;
    }
    if pairs.len() != counts.pair_denominator
        || by_class.get(&PairMutability::MutMut).copied().unwrap_or(0) != counts.mut_mut
        || by_class
            .get(&PairMutability::MutReadOnly)
            .copied()
            .unwrap_or(0)
            != counts.mut_read_only
        || by_class
            .get(&PairMutability::SharedShared)
            .copied()
            .unwrap_or(0)
            != counts.shared_shared
        || pairs
            .iter()
            .map(PairLedgerRow::default_fires)
            .sum::<usize>()
            != counts.mutability_default_fires
    {
        return Err("pair ledger does not reconcile with the count-(5) row".to_owned());
    }
    Ok(pairs)
}

fn aggregate(rows: &[ProgramCounts]) -> Result<ProgramCounts, String> {
    let mut programs = BTreeSet::new();
    let mut total = ProgramCounts {
        program: "TOTAL".to_owned(),
        sites_with_two_ref_args: 0,
        sites_not_proven_disjoint: 0,
        attributed_predicted_refs: 0,
        attributed_predicted_refs_depth0: 0,
        unknown_caller_reachable: 0,
        local_functions: 0,
        pair_denominator: 0,
        mut_mut: 0,
        mut_read_only: 0,
        shared_shared: 0,
        sites_with_mut_mut: 0,
        sites_with_mut_read_only: 0,
        sites_with_shared_shared: 0,
        mutability_default_fires: 0,
    };
    for row in rows {
        if !programs.insert(row.program.as_str()) {
            return Err(format!("duplicate aggregate program `{}`", row.program));
        }
        total.sites_with_two_ref_args += row.sites_with_two_ref_args;
        total.sites_not_proven_disjoint += row.sites_not_proven_disjoint;
        total.attributed_predicted_refs += row.attributed_predicted_refs;
        total.attributed_predicted_refs_depth0 += row.attributed_predicted_refs_depth0;
        total.unknown_caller_reachable += row.unknown_caller_reachable;
        total.local_functions += row.local_functions;
        total.pair_denominator += row.pair_denominator;
        total.mut_mut += row.mut_mut;
        total.mut_read_only += row.mut_read_only;
        total.shared_shared += row.shared_shared;
        total.sites_with_mut_mut += row.sites_with_mut_mut;
        total.sites_with_mut_read_only += row.sites_with_mut_read_only;
        total.sites_with_shared_shared += row.sites_with_shared_shared;
        total.mutability_default_fires += row.mutability_default_fires;
    }
    total.validate()?;
    Ok(total)
}

fn a5_substrate_dir(selector: Option<&str>) -> Result<&'static str, String> {
    match selector {
        None | Some("derived") => Ok("benchmarks/rs-crown-derived"),
        Some(other) => Err(format!(
            "A5/P1 is anchored to the derived substrate; got CRAT_BOC1_SUBSTRATE={other:?}"
        )),
    }
}

#[derive(Clone, Debug)]
struct FinalRun {
    counts: ProgramCounts,
    pairs: Vec<PairLedgerRow>,
    w14_pairs: Vec<String>,
    w14_exposures: Vec<String>,
    metadata: super::report::Row,
    raw_line: String,
    wall_seconds: f64,
}

fn parse_w14_ledgers(
    stdout: &str,
    metadata: &super::report::Row,
    counts: &ProgramCounts,
) -> Result<(Vec<String>, Vec<String>), String> {
    let pairs = stdout
        .lines()
        .filter(|line| line.starts_with(W14_PAIR_SENTINEL))
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let exposures = stdout
        .lines()
        .filter(|line| line.starts_with(W14_EXPOSURE_SENTINEL))
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let Some(expected_pairs) = metadata.get("a5_w14_pairs") else {
        if pairs.is_empty() && exposures.is_empty() {
            return Ok((pairs, exposures));
        }
        return Err("W14 ledger rows exist without W14 metadata".to_owned());
    };
    let expected_pairs = expected_pairs
        .parse::<usize>()
        .map_err(|why| format!("invalid a5_w14_pairs: {why}"))?;
    let expected_exposures = metadata
        .get("a5_w14_exposures")
        .ok_or_else(|| "W14 metadata lacks exposure count".to_owned())?
        .parse::<usize>()
        .map_err(|why| format!("invalid a5_w14_exposures: {why}"))?;
    if pairs.len() != expected_pairs
        || pairs.len() != counts.pair_denominator
        || exposures.len() != expected_exposures
        || exposures.len() != counts.attributed_predicted_refs_depth0
    {
        return Err("W14 ledger rows do not reconcile with worker metadata".to_owned());
    }
    let mut identities = BTreeSet::new();
    for line in &pairs {
        let columns = line
            .strip_prefix(W14_PAIR_SENTINEL)
            .expect("filtered W14 pair")
            .split('\t')
            .collect::<Vec<_>>();
        if !matches!(columns.len(), 16 | 18)
            || columns[0] != counts.program
            || columns[8] != "1"
            || columns[12..16]
                != [
                    "baseline",
                    "precise_replay",
                    "closed_world_frozen_graph",
                    "permitted:measurement-frozen-graph-attested",
                ]
        {
            return Err("W14 pair row violates the exact schema/raw-overlap gate".to_owned());
        }
        if !identities.insert((columns[1], columns[2], columns[3])) {
            return Err("W14 pair ledger contains a duplicate exact identity".to_owned());
        }
    }
    identities.clear();
    for line in &exposures {
        let columns = line
            .strip_prefix(W14_EXPOSURE_SENTINEL)
            .expect("filtered W14 exposure")
            .split('\t')
            .collect::<Vec<_>>();
        if !matches!(columns.len(), 12 | 16)
            || columns[0] != counts.program
            || columns[4] != "ref"
            || columns[8..12]
                != [
                    "baseline",
                    "precise_replay",
                    "closed_world_frozen_graph",
                    "permitted:measurement-frozen-graph-attested",
                ]
        {
            return Err("W14 exposure row violates the exact schema/baseline-Ref gate".to_owned());
        }
        if !identities.insert((columns[1], columns[2], columns[3])) {
            return Err("W14 exposure ledger contains a duplicate formal identity".to_owned());
        }
    }
    Ok((pairs, exposures))
}

#[derive(Clone, Debug)]
enum CompletedBase {
    Final(FinalRun),
    NeedsDepth {
        counts: ProgramCounts,
        wall_seconds: f64,
    },
}

fn parse_completed_base(
    expected_program: &str,
    stdout: &str,
    stderr: &str,
) -> Result<CompletedBase, String> {
    if !stderr.is_empty() {
        return Err(format!(
            "{expected_program}: preserved base stderr is nonempty"
        ));
    }
    let mut metadata_rows = stdout
        .lines()
        .filter_map(super::report::parse_kv_line)
        .collect::<Vec<_>>();
    if metadata_rows.len() != 1 {
        return Err(format!(
            "{expected_program}: expected exactly one BOC1 row, found {}",
            metadata_rows.len()
        ));
    }
    let metadata = metadata_rows.pop().expect("one metadata row");
    if metadata.get("program") != Some(expected_program) {
        return Err(format!(
            "{expected_program}: BOC1 program mismatch {:?}",
            metadata.get("program")
        ));
    }
    if metadata.get("mode") != Some("a5-p1") {
        return Err(format!(
            "{expected_program}: BOC1 mode mismatch {:?}",
            metadata.get("mode")
        ));
    }
    let wall_seconds = metadata
        .get("t_total_s")
        .ok_or_else(|| format!("{expected_program}: missing t_total_s"))?
        .parse::<f64>()
        .map_err(|why| format!("{expected_program}: invalid t_total_s: {why}"))?;
    match metadata.get("status") {
        Some("ok") => {
            let (raw_line, counts) = parse_single_raw_line(stdout, COUNT_SENTINEL)?;
            if counts.program != expected_program {
                return Err(format!(
                    "{expected_program}: invalid final counts {counts:?}"
                ));
            }
            let pairs = parse_pair_ledger(stdout, &counts)?;
            let (w14_pairs, w14_exposures) = parse_w14_ledgers(stdout, &metadata, &counts)?;
            Ok(CompletedBase::Final(FinalRun {
                counts,
                pairs,
                w14_pairs,
                w14_exposures,
                metadata,
                raw_line,
                wall_seconds,
            }))
        }
        Some("needs-depth") => {
            let (_, counts) = parse_single_raw_line(stdout, BASE_SENTINEL)?;
            if counts.program != expected_program || counts.sites_not_proven_disjoint == 0 {
                return Err(format!(
                    "{expected_program}: invalid needs-depth base counts {counts:?}"
                ));
            }
            Ok(CompletedBase::NeedsDepth {
                counts,
                wall_seconds,
            })
        }
        other => Err(format!(
            "{expected_program}: preserved base status is not complete: {other:?}"
        )),
    }
}

fn load_preserved_bases(directory: &Path) -> Result<BTreeMap<String, CompletedBase>, String> {
    let expected_names = super::CORPUS
        .iter()
        .filter(|program| program.name != "brotli")
        .flat_map(|program| {
            [
                format!("{}.a5-p1.out", program.name),
                format!("{}.a5-p1.err", program.name),
            ]
        })
        .collect::<BTreeSet<_>>();
    let actual_names = fs::read_dir(directory)
        .map_err(|why| format!("read preserved base directory: {why}"))?
        .map(|entry| {
            let entry = entry.map_err(|why| format!("read preserved base entry: {why}"))?;
            if !entry
                .file_type()
                .map_err(|why| format!("read preserved base file type: {why}"))?
                .is_file()
            {
                return Err(format!(
                    "preserved base entry is not a file: {}",
                    entry.path().display()
                ));
            }
            entry
                .file_name()
                .into_string()
                .map_err(|_| "preserved base filename is not UTF-8".to_owned())
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    if actual_names != expected_names {
        return Err(format!(
            "preserved base inventory mismatch: expected {} files, found {}",
            expected_names.len(),
            actual_names.len()
        ));
    }

    super::CORPUS
        .iter()
        .filter(|program| program.name != "brotli")
        .map(|program| {
            let stdout = fs::read_to_string(directory.join(format!("{}.a5-p1.out", program.name)))
                .map_err(|why| format!("{}: read preserved stdout: {why}", program.name))?;
            let stderr = fs::read_to_string(directory.join(format!("{}.a5-p1.err", program.name)))
                .map_err(|why| format!("{}: read preserved stderr: {why}", program.name))?;
            parse_completed_base(program.name, &stdout, &stderr)
                .map(|row| (program.name.to_owned(), row))
        })
        .collect()
}

#[test]
#[ignore = "A5/P1 artifact-first corpus measurement; requires CRAT_A5_SNAPSHOT and a private CRAT_BOC1_OUT"]
fn a5_p1_corpus() {
    use std::{fs, path::PathBuf};

    const DATE: &str = "2026-08-20";
    const ANALYSIS_SEMANTICS_HEAD: &str = "809dd9de";
    const SNAPSHOT_PRODUCER_HEAD: &str = "3b26a0ff85517a33acf916e8dbe2624ffc924a85";
    const SNAPSHOT_PRODUCER_BRANCH_HEAD: &str = "52da86648db9d76d8945063792f37da61bf8c8b9";
    const MANIFEST_COMMIT: &str = "a654d5ecde8a0ea9fccc8a3e7b9caaa8fac5812d";
    const RAW_FROZEN_DIGEST: &str =
        "9fc912af10fd3b235fe4d444d2fbac0bc521509b1c9447fc551acd0130e0e621";
    const DERIVED_SUBSTRATE_DIGEST: &str =
        "db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6";
    let classifier_differential = match std::env::var("CRAT_A5_CLASSIFIER_DIFFERENTIAL").as_deref()
    {
        Ok("1") => true,
        Err(std::env::VarError::NotPresent) | Ok("0") => false,
        Ok(other) => panic!("CRAT_A5_CLASSIFIER_DIFFERENTIAL must be 0 or 1, got {other:?}"),
        Err(error) => panic!("CRAT_A5_CLASSIFIER_DIFFERENTIAL is not valid Unicode: {error}"),
    };
    let snapshot_coverage = std::env::var("CRAT_A5_SNAPSHOT_COVERAGE").as_deref() == Ok("1");
    let focused_w14 = std::env::var("CRAT_A5_W14_FOCUSED").as_deref() == Ok("1");

    if focused_w14 {
        assert!(
            classifier_differential && snapshot_coverage,
            "W14 focused mode requires classifier and snapshot ledgers in the same run"
        );
        assert_eq!(
            std::env::var("CRAT_BO_COPY_LEND_MODE").as_deref(),
            Ok("baseline"),
            "W14 focused mode keeps A12 dormant"
        );
        for key in [
            "CRAT_A5_RECOVER_BROTLI",
            "CRAT_A5_RECOVER_BROTLI_DEPTH",
            "CRAT_A5_PRESERVED_BASE_DIR",
            "CRAT_A5_PRESERVED_FINAL_DIR",
        ] {
            assert!(
                std::env::var_os(key).is_none(),
                "W14 focused mode refuses preserved or recovery rows: {key}"
            );
        }
    }

    assert_eq!(
        super::CORPUS.len(),
        20,
        "P1 requires the frozen 20-program catalog"
    );
    assert!(
        std::env::var_os("CRAT_BOC1_PROGRAMS").is_none(),
        "P1 cannot run a post-selected corpus subset"
    );
    assert_eq!(
        std::env::var("CRAT_BO_REPAIR").as_deref(),
        Ok("mode_a"),
        "P1 requires the accepted-model repair profile explicitly"
    );
    assert_eq!(
        std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
        Ok("0"),
        "P1 measures the snapshot's L2-off accepted model"
    );
    assert_eq!(
        std::env::var("CRAT_BO_SAFE_MONO").as_deref(),
        Ok("per_site"),
        "P1 requires the shipped safety-mono profile explicitly"
    );
    assert_eq!(
        std::env::var("CRAT_BO_FORK_ENGINE").as_deref(),
        Ok("fork"),
        "P1 requires the shipped fork engine explicitly"
    );
    let root = super::orchestrate::workspace_root()
        .canonicalize()
        .expect("canonical workspace root");
    let analysis_head = super::orchestrate::git_sha();
    assert_ne!(analysis_head, "unknown", "P1 requires a code HEAD stamp");
    assert!(
        !super::orchestrate::git_dirty(),
        "commit the green harness before running P1"
    );
    let resolver_cwd = root.join("crates/pointer_replacer");
    assert_eq!(
        std::env::current_dir()
            .expect("current directory")
            .canonicalize()
            .expect("canonical current directory"),
        resolver_cwd
            .canonicalize()
            .expect("canonical pointer_replacer directory"),
        "Cargo must run the driver with CWD=crates/pointer_replacer; workers resolve deps through DIR=<root>"
    );
    let substrate_selector = std::env::var("CRAT_BOC1_SUBSTRATE").ok();
    let substrate_dir = a5_substrate_dir(substrate_selector.as_deref())
        .expect("P1 requires the derived substrate/default selector");
    let corpus_link = root.join(substrate_dir);
    assert!(
        fs::symlink_metadata(&corpus_link)
            .expect("derived corpus metadata")
            .file_type()
            .is_symlink(),
        "P1 records the guarded read-only derived-corpus symlink shape"
    );
    let corpus_target = corpus_link
        .canonicalize()
        .expect("canonical derived corpus");
    let out = PathBuf::from(
        std::env::var_os("CRAT_BOC1_OUT").expect("P1 requires an explicit private CRAT_BOC1_OUT"),
    );
    assert!(
        !out.starts_with(root.join("target/boc1")),
        "P1 must not write the ladder lane's target/boc1 tree"
    );
    let snapshot =
        PathBuf::from(std::env::var_os("CRAT_A5_SNAPSHOT").expect("P1 requires CRAT_A5_SNAPSHOT"));
    assert!(snapshot.is_dir(), "immutable snapshot is not a directory");
    assert_eq!(
        fs::read_dir(&snapshot)
            .expect("read immutable snapshot")
            .filter_map(Result::ok)
            .filter(|entry| entry.file_type().is_ok_and(|kind| kind.is_file()))
            .count(),
        100,
        "snapshot inventory moved after Boundary 0"
    );

    let deps_link = root.join("deps_crate/target");
    let deps_shape = if fs::symlink_metadata(&deps_link)
        .expect("deps target metadata")
        .file_type()
        .is_symlink()
    {
        "read-only-symlink-to-main-checkout-build"
    } else {
        "worktree-local-locked-build"
    };
    let deps_target = deps_link.canonicalize().expect("canonical deps target");
    let deps_dir = deps_target.join("debug/deps");
    let deps_entries = fs::read_dir(&deps_dir).expect("read linked deps directory");
    let mut rlibs = 0usize;
    let mut bytemuck_derive = false;
    for entry in deps_entries.filter_map(Result::ok) {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        rlibs += usize::from(name.ends_with(".rlib"));
        bytemuck_derive |= name.starts_with("libbytemuck_derive")
            && (name.ends_with(".dylib") || name.ends_with(".so"));
    }
    assert!(rlibs > 0, "linked deps target contains no rlibs");
    assert!(
        bytemuck_derive,
        "linked deps target lacks bytemuck_derive dylib"
    );

    let base_timeout = Duration::from_secs(
        std::env::var("CRAT_A5_BASE_TIMEOUT_SECS")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(900),
    );
    let deep_timeout = Duration::from_secs(
        std::env::var("CRAT_A5_DEEP_TIMEOUT_SECS")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(3000),
    );
    let snapshot_env = snapshot.display().to_string();

    if std::env::var("CRAT_A5_W14_RECOVER_BROTLI").as_deref() == Ok("1") {
        assert!(focused_w14, "W14 brotli recovery requires focused mode");
        assert_eq!(
            std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
            Ok("49152"),
            "W14 brotli recovery retains the 49,152-MiB cap"
        );
        assert!(
            std::env::var_os("CRAT_A5_W14_HELD_DIR").is_none(),
            "W14 recovery and aggregation are separate serialized phases"
        );
        let program = super::CORPUS
            .iter()
            .find(|program| program.name == "brotli")
            .expect("brotli catalog row");
        let input = corpus_link.join(program.name).join(program.lib_root);
        let outcome = super::orchestrate::run_child_labeled(
            program.name,
            &input,
            "a5-p1",
            "a5-w14-recovery",
            base_timeout,
            &[("CRAT_A5_SNAPSHOT", snapshot_env.clone())],
        );
        assert_eq!(
            outcome.status, "ok",
            "brotli W14 recovery status={} note={}",
            outcome.status, outcome.note
        );
        let metadata = outcome.row.as_ref().expect("brotli W14 metadata");
        let (_, counts) =
            parse_single_raw_line(&outcome.stdout, COUNT_SENTINEL).expect("brotli W14 count row");
        parse_pair_ledger(&outcome.stdout, &counts).expect("brotli exact pair ledger");
        parse_w14_ledgers(&outcome.stdout, metadata, &counts)
            .expect("brotli W14 ledgers reconcile");
        let recovery = out.join("a5-w14-recovery");
        fs::create_dir_all(&recovery).expect("create W14 recovery receipt directory");
        fs::write(
            recovery.join("receipt.txt"),
            format!(
                "status=ok\ndata=true\nprogram=brotli\nanalysis_head={analysis_head}\n\
                 copy_lend_mode=baseline\na5_mode=precise_replay\na5_world=closed_world_frozen_graph\n\
                 replay_safe_definition={}\n\
                 mem_cap_mib=49152\npeak_rss_kb={}\nwall_s={:.3}\n",
                REPLAY_SAFE_DEFINITION, outcome.peak_rss_kb, outcome.wall_s,
            ),
        )
        .expect("write W14 recovery receipt");
        return;
    }

    if std::env::var("CRAT_A5_RECOVER_BROTLI").as_deref() == Ok("1") {
        assert_eq!(
            std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
            Ok("49152"),
            "the amended one-shot brotli recovery is authorized only at the 49,152-MiB cap"
        );
        assert!(
            std::env::var_os("CRAT_A5_PRESERVED_BASE_DIR").is_none(),
            "the one-shot recovery must classify brotli only"
        );
        let program = super::CORPUS
            .iter()
            .find(|program| program.name == "brotli")
            .expect("brotli catalog row");
        let input = corpus_link.join(program.name).join(program.lib_root);
        let outcome = super::orchestrate::run_child_labeled(
            program.name,
            &input,
            "a5-p1",
            "a5-p1-recovery",
            base_timeout,
            &[("CRAT_A5_SNAPSHOT", snapshot_env.clone())],
        );
        let recovery_output = out.join("a5-p1-recovery");
        fs::create_dir_all(&recovery_output).expect("create P1 recovery output directory");
        let receipt = format!(
            "program=brotli\nstatus={}\nmem_cap_mib=49152\npeak_rss_kb={}\npeak_rss_mib={:.3}\nwall_s={:.3}\nanalysis_worktree_head={analysis_head}\nanalysis_semantics_head={ANALYSIS_SEMANTICS_HEAD}\ncopy_lend_mode=baseline\nsnapshot_producer_head={SNAPSHOT_PRODUCER_HEAD}\nmanifest_commit={MANIFEST_COMMIT}\nderived_substrate_sha256={DERIVED_SUBSTRATE_DIGEST}\nmachine_quiet_precondition=lambda7-high-memory\n",
            outcome.status,
            outcome.peak_rss_kb,
            outcome.peak_rss_kb as f64 / 1024.0,
            outcome.wall_s,
        );
        fs::write(recovery_output.join("receipt.txt"), &receipt)
            .expect("write P1 recovery receipt");
        println!(
            "A5P1RECOVERY program=brotli status={} mem_cap_mib=49152 peak_rss_kb={} peak_rss_mib={:.3} wall_s={:.3}",
            outcome.status,
            outcome.peak_rss_kb,
            outcome.peak_rss_kb as f64 / 1024.0,
            outcome.wall_s,
        );
        assert!(
            matches!(outcome.status.as_str(), "ok" | "needs-depth"),
            "brotli recovery status={} note={}",
            outcome.status,
            outcome.note
        );
        parse_completed_base(program.name, &outcome.stdout, &outcome.stderr)
            .expect("complete brotli base recovery row");
        return;
    }

    if std::env::var("CRAT_A5_RECOVER_BROTLI_DEPTH").as_deref() == Ok("1") {
        assert_eq!(
            std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
            Ok("24576"),
            "the one-shot brotli depth recovery is authorized only at the 24,576-MiB cap"
        );
        assert!(
            std::env::var_os("CRAT_A5_PRESERVED_BASE_DIR").is_none()
                && std::env::var_os("CRAT_A5_PRESERVED_FINAL_DIR").is_none(),
            "the one-shot depth recovery must export brotli only"
        );
        let program = super::CORPUS
            .iter()
            .find(|program| program.name == "brotli")
            .expect("brotli catalog row");
        let input = corpus_link.join(program.name).join(program.lib_root);
        let outcome = super::orchestrate::run_child_labeled(
            program.name,
            &input,
            "a5-p1",
            "a5-p1-depth-recovery",
            deep_timeout,
            &[
                ("CRAT_A5_SNAPSHOT", snapshot_env.clone()),
                ("CRAT_A5_DEEP", "1".to_owned()),
            ],
        );
        let recovery_output = out.join("a5-p1-depth-recovery");
        fs::create_dir_all(&recovery_output).expect("create P1 depth recovery output directory");
        let receipt = format!(
            "program=brotli\nphase=targeted-depth\nstatus={}\nmem_cap_mib=24576\npeak_rss_kb={}\npeak_rss_mib={:.3}\nwall_s={:.3}\nanalysis_worktree_head={analysis_head}\nsnapshot_producer_head={SNAPSHOT_PRODUCER_HEAD}\nmanifest_commit={MANIFEST_COMMIT}\nderived_substrate_sha256={DERIVED_SUBSTRATE_DIGEST}\nmachine_quiet_precondition=externally-verified\n",
            outcome.status,
            outcome.peak_rss_kb,
            outcome.peak_rss_kb as f64 / 1024.0,
            outcome.wall_s,
        );
        fs::write(recovery_output.join("receipt.txt"), &receipt)
            .expect("write P1 depth recovery receipt");
        println!(
            "A5P1DEPTHRECOVERY program=brotli status={} mem_cap_mib=24576 peak_rss_kb={} peak_rss_mib={:.3} wall_s={:.3}",
            outcome.status,
            outcome.peak_rss_kb,
            outcome.peak_rss_kb as f64 / 1024.0,
            outcome.wall_s,
        );
        assert_eq!(
            outcome.status, "ok",
            "brotli depth recovery status={} note={}",
            outcome.status, outcome.note
        );
        match parse_completed_base(program.name, &outcome.stdout, &outcome.stderr)
            .expect("complete brotli targeted-depth recovery row")
        {
            CompletedBase::Final(_) => {}
            CompletedBase::NeedsDepth { .. } => {
                panic!("brotli targeted-depth recovery did not emit a final row")
            }
        }
        return;
    }

    let mut final_runs = BTreeMap::new();
    let mut needs_depth = Vec::new();
    let mut brotli_peak_rss_kb = None;
    let mut brotli_depth_peak_rss_kb = None;
    let mut brotli_depth_wall_s = None;
    let held_w14_directory = std::env::var_os("CRAT_A5_W14_HELD_DIR");
    let preserved_final_directory = std::env::var_os("CRAT_A5_PRESERVED_FINAL_DIR");
    if let Some(directory) = held_w14_directory {
        assert!(focused_w14, "held W14 rows require focused mode");
        assert!(
            preserved_final_directory.is_none()
                && std::env::var_os("CRAT_A5_PRESERVED_BASE_DIR").is_none(),
            "W14 held-row aggregation does not mix older resume protocols"
        );
        let directory = PathBuf::from(directory);
        for program in super::CORPUS
            .iter()
            .filter(|program| program.name != "brotli")
        {
            let stdout = fs::read_to_string(directory.join(format!("{}.a5-p1.out", program.name)))
                .unwrap_or_else(|why| panic!("{}: read held stdout: {why}", program.name));
            let stderr = fs::read_to_string(directory.join(format!("{}.a5-p1.err", program.name)))
                .unwrap_or_else(|why| panic!("{}: read held stderr: {why}", program.name));
            match parse_completed_base(program.name, &stdout, &stderr)
                .unwrap_or_else(|why| panic!("{}: held W14 row: {why}", program.name))
            {
                CompletedBase::Final(run) => {
                    final_runs.insert(program.name, run);
                }
                CompletedBase::NeedsDepth { .. } => {
                    panic!("{}: held W14 row still needs depth", program.name)
                }
            }
        }
        let recovery_logs = out.join("logs");
        let stdout = fs::read_to_string(recovery_logs.join("brotli.a5-w14-recovery.out"))
            .expect("read brotli W14 recovery stdout");
        let stderr = fs::read_to_string(recovery_logs.join("brotli.a5-w14-recovery.err"))
            .expect("read brotli W14 recovery stderr");
        match parse_completed_base("brotli", &stdout, &stderr)
            .expect("complete brotli W14 recovery row")
        {
            CompletedBase::Final(run) => {
                final_runs.insert("brotli", run);
            }
            CompletedBase::NeedsDepth { .. } => panic!("brotli W14 recovery needs depth"),
        }
        assert_eq!(final_runs.len(), 20);
    } else if let Some(directory) = preserved_final_directory {
        assert_eq!(
            std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
            Ok("8192"),
            "artifact-only final aggregation records the default 8,192-MiB policy"
        );
        assert!(
            std::env::var_os("CRAT_A5_PRESERVED_BASE_DIR").is_none(),
            "final-row aggregation must not enter the base-row resume path"
        );
        let mut rows = load_preserved_bases(Path::new(&directory))
            .unwrap_or_else(|why| panic!("preserved final-row gate failed: {why}"));
        for program in super::CORPUS
            .iter()
            .filter(|program| program.name != "brotli")
        {
            match rows
                .remove(program.name)
                .expect("preserved final row for every non-brotli program")
            {
                CompletedBase::Final(run) => {
                    final_runs.insert(program.name, run);
                }
                CompletedBase::NeedsDepth { .. } => {
                    panic!("{}: preserved final row still needs depth", program.name)
                }
            }
        }
        assert!(rows.is_empty());
        let recovery_logs = out.join("logs");
        let recovery_stdout =
            fs::read_to_string(recovery_logs.join("brotli.a5-p1-depth-recovery.out"))
                .expect("read brotli depth recovery stdout");
        let recovery_stderr =
            fs::read_to_string(recovery_logs.join("brotli.a5-p1-depth-recovery.err"))
                .expect("read brotli depth recovery stderr");
        match parse_completed_base("brotli", &recovery_stdout, &recovery_stderr)
            .expect("complete brotli depth recovery row")
        {
            CompletedBase::Final(run) => {
                final_runs.insert("brotli", run);
            }
            CompletedBase::NeedsDepth { .. } => {
                panic!("brotli depth recovery did not emit a final row")
            }
        }
        assert_eq!(final_runs.len(), super::CORPUS.len());
        let base_receipt = fs::read_to_string(out.join("a5-p1-recovery/receipt.txt"))
            .expect("read brotli base recovery receipt");
        brotli_peak_rss_kb = Some(
            base_receipt
                .lines()
                .find_map(|line| line.strip_prefix("peak_rss_kb="))
                .expect("base recovery receipt peak_rss_kb")
                .parse::<u64>()
                .expect("numeric base recovery peak_rss_kb"),
        );
        let depth_receipt = fs::read_to_string(out.join("a5-p1-depth-recovery/receipt.txt"))
            .expect("read brotli depth recovery receipt");
        brotli_depth_peak_rss_kb = Some(
            depth_receipt
                .lines()
                .find_map(|line| line.strip_prefix("peak_rss_kb="))
                .expect("depth recovery receipt peak_rss_kb")
                .parse::<u64>()
                .expect("numeric depth recovery peak_rss_kb"),
        );
        brotli_depth_wall_s = Some(
            depth_receipt
                .lines()
                .find_map(|line| line.strip_prefix("wall_s="))
                .expect("depth recovery receipt wall_s")
                .parse::<f64>()
                .expect("numeric depth recovery wall_s"),
        );
    } else if let Some(directory) = std::env::var_os("CRAT_A5_PRESERVED_BASE_DIR") {
        assert_eq!(
            std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
            Ok("8192"),
            "targeted depth exports after recovery return to the default 8,192-MiB cap"
        );
        let mut bases = load_preserved_bases(Path::new(&directory))
            .unwrap_or_else(|why| panic!("preserved base gate failed: {why}"));
        let recovery_logs = out.join("logs");
        let recovery_stdout = fs::read_to_string(recovery_logs.join("brotli.a5-p1-recovery.out"))
            .expect("read brotli recovery stdout");
        let recovery_stderr = fs::read_to_string(recovery_logs.join("brotli.a5-p1-recovery.err"))
            .expect("read brotli recovery stderr");
        bases.insert(
            "brotli".to_owned(),
            parse_completed_base("brotli", &recovery_stdout, &recovery_stderr)
                .expect("complete brotli recovery row"),
        );
        assert_eq!(bases.len(), super::CORPUS.len());
        let receipt = fs::read_to_string(out.join("a5-p1-recovery/receipt.txt"))
            .expect("read brotli recovery receipt");
        brotli_peak_rss_kb = Some(
            receipt
                .lines()
                .find_map(|line| line.strip_prefix("peak_rss_kb="))
                .expect("recovery receipt peak_rss_kb")
                .parse::<u64>()
                .expect("numeric recovery peak_rss_kb"),
        );
        for program in super::CORPUS {
            match bases
                .remove(program.name)
                .expect("completed base row for every catalog program")
            {
                CompletedBase::Final(run) => {
                    final_runs.insert(program.name, run);
                }
                CompletedBase::NeedsDepth {
                    counts,
                    wall_seconds,
                } => needs_depth.push((*program, counts, wall_seconds)),
            }
        }
        assert!(bases.is_empty());
    } else {
        for program in super::CORPUS {
            let input = corpus_link.join(program.name).join(program.lib_root);
            let outcome = super::orchestrate::run_child_env(
                program.name,
                &input,
                "a5-p1",
                base_timeout,
                &[("CRAT_A5_SNAPSHOT", snapshot_env.clone())],
            );
            match outcome.status.as_str() {
                "ok" => {
                    let (raw_line, counts) = parse_single_raw_line(&outcome.stdout, COUNT_SENTINEL)
                        .unwrap_or_else(|why| panic!("{}: {why}", program.name));
                    let pairs = parse_pair_ledger(&outcome.stdout, &counts)
                        .unwrap_or_else(|why| panic!("{}: {why}", program.name));
                    let metadata = outcome.row.expect("final worker BOC1 row");
                    let (w14_pairs, w14_exposures) =
                        parse_w14_ledgers(&outcome.stdout, &metadata, &counts)
                            .unwrap_or_else(|why| panic!("{}: {why}", program.name));
                    assert_eq!(counts.program, program.name);
                    final_runs.insert(
                        program.name,
                        FinalRun {
                            counts,
                            pairs,
                            w14_pairs,
                            w14_exposures,
                            metadata,
                            raw_line,
                            wall_seconds: outcome.wall_s,
                        },
                    );
                }
                "needs-depth" => {
                    let (_, counts) = parse_single_raw_line(&outcome.stdout, BASE_SENTINEL)
                        .unwrap_or_else(|why| panic!("{}: {why}", program.name));
                    assert_eq!(counts.program, program.name);
                    assert!(counts.sites_not_proven_disjoint > 0);
                    needs_depth.push((*program, counts, outcome.wall_s));
                }
                other => panic!(
                    "{}: base worker status={other} note={}",
                    program.name, outcome.note
                ),
            }
        }
    }

    assert!(
        needs_depth.len() < super::CORPUS.len(),
        "all 20 programs require a targeted accepted-model export; P1 refuses a suite-wide re-solve"
    );
    let current_head_baseline_model_count = super::CORPUS.len();
    for (program, base, base_wall) in needs_depth {
        let input = corpus_link.join(program.name).join(program.lib_root);
        let outcome = super::orchestrate::run_child_env(
            program.name,
            &input,
            "a5-p1",
            deep_timeout,
            &[
                ("CRAT_A5_SNAPSHOT", snapshot_env.clone()),
                ("CRAT_A5_DEEP", "1".to_owned()),
            ],
        );
        assert_eq!(
            outcome.status, "ok",
            "{}: targeted depth worker failed: {}",
            program.name, outcome.note
        );
        let (raw_line, counts) = parse_single_raw_line(&outcome.stdout, COUNT_SENTINEL)
            .unwrap_or_else(|why| panic!("{}: {why}", program.name));
        let pairs = parse_pair_ledger(&outcome.stdout, &counts)
            .unwrap_or_else(|why| panic!("{}: {why}", program.name));
        let metadata = outcome.row.expect("targeted worker BOC1 row");
        let (w14_pairs, w14_exposures) = parse_w14_ledgers(&outcome.stdout, &metadata, &counts)
            .unwrap_or_else(|why| panic!("{}: {why}", program.name));
        assert_eq!(counts.program, program.name);
        assert_eq!(counts.sites_with_two_ref_args, base.sites_with_two_ref_args);
        assert_eq!(
            counts.sites_not_proven_disjoint,
            base.sites_not_proven_disjoint
        );
        assert_eq!(
            counts.attributed_predicted_refs_depth0,
            base.attributed_predicted_refs_depth0
        );
        assert_eq!(
            counts.unknown_caller_reachable,
            base.unknown_caller_reachable
        );
        assert_eq!(counts.local_functions, base.local_functions);
        assert_eq!(counts.pair_denominator, base.pair_denominator);
        assert_eq!(counts.mut_mut, base.mut_mut);
        assert_eq!(counts.mut_read_only, base.mut_read_only);
        assert_eq!(counts.shared_shared, base.shared_shared);
        assert_eq!(counts.sites_with_mut_mut, base.sites_with_mut_mut);
        assert_eq!(
            counts.sites_with_mut_read_only,
            base.sites_with_mut_read_only
        );
        assert_eq!(
            counts.sites_with_shared_shared,
            base.sites_with_shared_shared
        );
        assert_eq!(
            counts.mutability_default_fires,
            base.mutability_default_fires
        );
        final_runs.insert(
            program.name,
            FinalRun {
                counts,
                pairs,
                w14_pairs,
                w14_exposures,
                metadata,
                raw_line,
                wall_seconds: base_wall + outcome.wall_s,
            },
        );
    }

    assert_eq!(final_runs.len(), super::CORPUS.len());
    let rows = super::CORPUS
        .iter()
        .map(|program| {
            final_runs
                .get(program.name)
                .expect("final row for every catalog program")
                .counts
                .clone()
        })
        .collect::<Vec<_>>();
    let total = aggregate(&rows).expect("valid P1 aggregate");
    assert_eq!(
        total.unknown_caller_reachable, CLOSED_WORLD_FRAME_UNKNOWN_REACHABLE,
        "count-(5) closedness numerator moved"
    );
    assert_eq!(
        total.local_functions, CLOSED_WORLD_FRAME_LOCAL_FUNCTIONS,
        "count-(5) closedness denominator moved"
    );
    let classifier_sum = |key: &str| {
        final_runs
            .values()
            .map(|run| {
                run.metadata
                    .get(key)
                    .unwrap_or_else(|| panic!("{} missing {key}", run.counts.program))
                    .parse::<usize>()
                    .unwrap_or_else(|why| panic!("{} invalid {key}: {why}", run.counts.program))
            })
            .sum::<usize>()
    };
    let classifier_candidates =
        classifier_differential.then(|| classifier_sum("a5_classifier_candidates"));
    let classifier_not_proven =
        classifier_differential.then(|| classifier_sum("a5_classifier_not_proven"));
    let classifier_byte_mismatches =
        classifier_differential.then(|| classifier_sum("a5_classifier_byte_mismatches"));
    if classifier_differential {
        assert!(final_runs.values().all(|run| {
            run.metadata.get("a5_classifier_api") == Some("shared-v1")
                && run.metadata.get("a5_world") == Some("closed_world_frozen_graph")
        }));
        assert_eq!(classifier_byte_mismatches, Some(0));
        assert_eq!(classifier_not_proven, Some(5_555));
        assert!(classifier_candidates.is_some_and(|count| count >= 5_555));
        assert_eq!(total.pair_denominator, 5_555);
        assert_eq!(total.mut_mut, 2_391);
        assert_eq!(total.mut_read_only, 2_480);
        assert_eq!(total.shared_shared, 684);
    }
    let snapshot_sum = |key: &str| classifier_sum(key);
    let snapshot_totals = snapshot_coverage.then(|| {
        [
            snapshot_sum("a5_snapshot_total"),
            snapshot_sum("a5_snapshot_markable"),
            snapshot_sum("a5_snapshot_read_after_write"),
            snapshot_sum("a5_snapshot_opaque_escape"),
            snapshot_sum("a5_snapshot_recursive"),
            snapshot_sum("a5_snapshot_volatile_or_atomic"),
            snapshot_sum("a5_snapshot_unresolved"),
            snapshot_sum("a5_snapshot_target_type_mismatch"),
            snapshot_sum("a5_snapshot_noncopy_scalar"),
            snapshot_sum("a5_snapshot_final_markable"),
            snapshot_sum("a5_snapshot_all_witness_demoted"),
            snapshot_sum("a5_snapshot_filter_unresolved"),
        ]
    });
    if let Some(
        [
            den,
            markable,
            read_after,
            opaque,
            recursive,
            volatile,
            unresolved,
            type_mismatch,
            noncopy,
            final_markable,
            all_witness_demoted,
            filter_unresolved,
        ],
    ) = snapshot_totals
    {
        assert_eq!(den, 2_480);
        assert_eq!(unresolved, 0);
        assert_eq!(markable + read_after + opaque + recursive + volatile, den);
        assert_eq!(filter_unresolved, 0);
        assert_eq!(
            final_markable + all_witness_demoted + type_mismatch + noncopy,
            markable
        );
    }

    let w14_totals = focused_w14.then(|| {
        let optional_sum = |key: &str, fallback: Option<&str>| {
            final_runs
                .values()
                .map(|run| {
                    run.metadata
                        .get(key)
                        .or_else(|| fallback.and_then(|fallback| run.metadata.get(fallback)))
                        .unwrap_or("0")
                        .parse::<usize>()
                        .unwrap_or_else(|why| panic!("{} invalid {key}: {why}", run.counts.program))
                })
                .sum::<usize>()
        };
        let values = [
            classifier_sum("a5_w14_pairs"),
            classifier_sum("a5_w14_effective_pairs"),
            optional_sum("a5_w14_planned_marks", Some("a5_w14_selected_marks")),
            classifier_sum("a5_w14_selected_marks"),
            optional_sum("a5_w14_demoted_by_model", None),
            classifier_sum("a5_w14_exposures"),
            classifier_sum("a5_w14_demoted"),
            classifier_sum("a5_w14_marked"),
            classifier_sum("a5_w14_shared_safe"),
            classifier_sum("a5_w14_replay_safe"),
            classifier_sum("a5_w14_unresolved"),
            classifier_sum("a5_w14_precise_rounds"),
            classifier_sum("a5_w14_incidence_m"),
            classifier_sum("a5_w14_incidence_mr"),
            classifier_sum("a5_w14_incidence_r"),
            classifier_sum("a5_w14_incidence_rs"),
        ];
        assert_eq!(values[0], 5_555, "W14 pair denominator moved");
        assert_eq!(values[2], 4, "W14 planned-mark count moved");
        assert_eq!(values[2], values[3] + values[4]);
        assert_eq!(values[5], 2_014, "W14 exposure denominator moved");
        assert_eq!(values[6], 389, "W14 demoted exposure count moved");
        assert_eq!(values[7], 2, "W14 marked exposure count moved");
        assert_eq!(values[8], 114, "W14 shared-safe exposure count moved");
        assert_eq!(values[9], 1_509, "W14 replay-safe exposure count moved");
        assert_eq!(values[10], 0, "W14 unresolved exposure residual");
        assert_eq!(
            values[6] + values[7] + values[8] + values[9] + values[10],
            values[5]
        );
        assert_eq!(values[12..16], [319, 336, 558, 298]);
        values
    });

    let output = out.join("a5-p1");
    fs::create_dir_all(&output).expect("create P1 output directory");
    let mut raw = String::new();
    let mut pair_ledger = String::from(
        "program\tsite\tleft_argument\tright_argument\tclass\tleft_mutable\tright_mutable\tleft_default_fires\tright_default_fires\n",
    );
    let mut w14_pair_ledger = String::from(
        "program\tsite\tleft_argument\tright_argument\tclass\ttarget_formals\tleft_formals\tright_formals\traw_overlap\teffective_overlap\tmarkability\tretained_mark\tcopy_lend_mode\ta5_mode\ta5_world\ta5_abi_guard\tplanned_mark\tmodel_attribution\n",
    );
    let mut w14_exposure_ledger = String::from(
        "program\tfunction\tparameter\tdepth\tbaseline_kind\tprecise_kind\tmovement\tclass\tcopy_lend_mode\ta5_mode\ta5_world\ta5_abi_guard\teffective_mut_mut\teffective_mut_read_only\teffective_shared_shared\tincidence\n",
    );
    let mut w14_programs = String::from(
        "program\tpairs\teffective_pairs\tplanned_marks\tretained_marks\tdemoted_by_model\texposures\tdemoted\tmarked\tshared_safe\treplay_safe\tunresolved\tprecise_rounds\tincidence_m\tincidence_mr\tincidence_r\tincidence_rs\n",
    );
    let mut tsv = String::from(
        "program\tc1\tc2\tc3\tc3_depth0\tcg_num\tcg_den\tpair_den\tmut_mut\tmut_read_only\tshared_shared\tsite_mut_mut\tsite_mut_read_only\tsite_shared_shared\tmut_default_fires\tcalls_total\tdirect_local\tindirect_local\tdirect_external\tindirect_unresolved\tnon_fn_def_constant\tt_origins_s\tt_andersen_s\tt_model_s\twall_s\n",
    );
    let mut markdown = format!(
        "# A5 current-head refresh with count-(5)\n\nHEAD `{analysis_head}`, date {DATE}; manifest docs `{MANIFEST_COMMIT}` supplies identity/depth cross-checks only; all C1-C3 decisions come from the current-head `baseline` BO model.\n\n| program | C1 | C2/site denominator | C3-all | C3-d0 | pair denominator | mut+mut | mut+read-only | shared+shared | site mut+mut | site mut+read-only | site shared+shared | unknown-reachable / local functions |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n"
    );
    let percent = |numerator: usize, denominator: usize| {
        if denominator == 0 {
            "0 (N/A)".to_owned()
        } else {
            format!(
                "{} ({:.2}%)",
                numerator,
                100.0 * numerator as f64 / denominator as f64
            )
        }
    };
    for program in super::CORPUS {
        let run = &final_runs[program.name];
        raw.push_str(&run.raw_line);
        raw.push('\n');
        for pair in &run.pairs {
            pair_ledger.push_str(
                render_pair_line(pair)
                    .strip_prefix(PAIR_SENTINEL)
                    .expect("rendered pair sentinel"),
            );
            pair_ledger.push('\n');
        }
        for pair in &run.w14_pairs {
            w14_pair_ledger.push_str(
                pair.strip_prefix(W14_PAIR_SENTINEL)
                    .expect("parsed W14 pair sentinel"),
            );
            w14_pair_ledger.push('\n');
        }
        for exposure in &run.w14_exposures {
            w14_exposure_ledger.push_str(
                exposure
                    .strip_prefix(W14_EXPOSURE_SENTINEL)
                    .expect("parsed W14 exposure sentinel"),
            );
            w14_exposure_ledger.push('\n');
        }
        if focused_w14 {
            let get_w14 = |key: &str| {
                run.metadata
                    .get(key)
                    .unwrap_or_else(|| panic!("{} missing {key}", program.name))
            };
            w14_programs.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                program.name,
                get_w14("a5_w14_pairs"),
                get_w14("a5_w14_effective_pairs"),
                run.metadata
                    .get("a5_w14_planned_marks")
                    .unwrap_or_else(|| get_w14("a5_w14_selected_marks")),
                get_w14("a5_w14_selected_marks"),
                run.metadata.get("a5_w14_demoted_by_model").unwrap_or("0"),
                get_w14("a5_w14_exposures"),
                get_w14("a5_w14_demoted"),
                get_w14("a5_w14_marked"),
                get_w14("a5_w14_shared_safe"),
                get_w14("a5_w14_replay_safe"),
                get_w14("a5_w14_unresolved"),
                get_w14("a5_w14_precise_rounds"),
                get_w14("a5_w14_incidence_m"),
                get_w14("a5_w14_incidence_mr"),
                get_w14("a5_w14_incidence_r"),
                get_w14("a5_w14_incidence_rs"),
            ));
        }
        let get = |key: &str| run.metadata.get(key).unwrap_or("missing");
        tsv.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.3}\n",
            program.name,
            run.counts.sites_with_two_ref_args,
            run.counts.sites_not_proven_disjoint,
            run.counts.attributed_predicted_refs,
            run.counts.attributed_predicted_refs_depth0,
            run.counts.unknown_caller_reachable,
            run.counts.local_functions,
            run.counts.pair_denominator,
            run.counts.mut_mut,
            run.counts.mut_read_only,
            run.counts.shared_shared,
            run.counts.sites_with_mut_mut,
            run.counts.sites_with_mut_read_only,
            run.counts.sites_with_shared_shared,
            run.counts.mutability_default_fires,
            get("calls_total"),
            get("direct_local"),
            get("indirect_local"),
            get("direct_external"),
            get("indirect_unresolved"),
            get("non_fn_def_constant"),
            get("t_origins_s"),
            get("t_andersen_s"),
            get("t_model_s"),
            run.wall_seconds,
        ));
        markdown.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} / {} |\n",
            program.name,
            run.counts.sites_with_two_ref_args,
            run.counts.sites_not_proven_disjoint,
            run.counts.attributed_predicted_refs,
            run.counts.attributed_predicted_refs_depth0,
            run.counts.pair_denominator,
            percent(run.counts.mut_mut, run.counts.pair_denominator),
            percent(run.counts.mut_read_only, run.counts.pair_denominator),
            percent(run.counts.shared_shared, run.counts.pair_denominator),
            percent(
                run.counts.sites_with_mut_mut,
                run.counts.sites_not_proven_disjoint,
            ),
            percent(
                run.counts.sites_with_mut_read_only,
                run.counts.sites_not_proven_disjoint,
            ),
            percent(
                run.counts.sites_with_shared_shared,
                run.counts.sites_not_proven_disjoint,
            ),
            run.counts.unknown_caller_reachable,
            run.counts.local_functions,
        ));
    }
    markdown.push_str(&format!(
        "| **TOTAL / micro-average** | **{}** | **{}** | **{}** | **{}** | **{}** | **{}** | **{}** | **{}** | **{}** | **{}** | **{}** | **{} / {} ({:.2}%)** |\n",
        total.sites_with_two_ref_args,
        total.sites_not_proven_disjoint,
        total.attributed_predicted_refs,
        total.attributed_predicted_refs_depth0,
        total.pair_denominator,
        percent(total.mut_mut, total.pair_denominator),
        percent(total.mut_read_only, total.pair_denominator),
        percent(total.shared_shared, total.pair_denominator),
        percent(total.sites_with_mut_mut, total.sites_not_proven_disjoint),
        percent(
            total.sites_with_mut_read_only,
            total.sites_not_proven_disjoint,
        ),
        percent(
            total.sites_with_shared_shared,
            total.sites_not_proven_disjoint,
        ),
        total.unknown_caller_reachable,
        total.local_functions,
        100.0 * total.unknown_caller_reachable as f64 / total.local_functions as f64,
    ));
    let nonzero_programs =
        |field: fn(&ProgramCounts) -> usize| rows.iter().filter(|row| field(row) != 0).count();
    markdown.push_str(&format!(
        "\nCount-(5) program spread (nonzero / 20): pair denominator {}; mut+mut {}; mut+read-only {}; shared+shared {}; site mut+mut {}; site mut+read-only {}; site shared+shared {}. Missing-Foster default fires: {}.\n",
        nonzero_programs(|row| row.pair_denominator),
        nonzero_programs(|row| row.mut_mut),
        nonzero_programs(|row| row.mut_read_only),
        nonzero_programs(|row| row.shared_shared),
        nonzero_programs(|row| row.sites_with_mut_mut),
        nonzero_programs(|row| row.sites_with_mut_read_only),
        nonzero_programs(|row| row.sites_with_shared_shared),
        total.mutability_default_fires,
    ));
    if let Some(peak_rss_kb) = brotli_peak_rss_kb {
        markdown.push_str(&format!(
            "\nResource note: derived expansion collapsed brotli into one ~500k-SLOC file; its amended one-shot 49,152-MiB base-classification recovery peaked at {:.3} MiB RSS (200 ms sampling).\n",
            peak_rss_kb as f64 / 1024.0,
        ));
    }
    if let (Some(peak_rss_kb), Some(wall_s)) = (brotli_depth_peak_rss_kb, brotli_depth_wall_s) {
        markdown.push_str(&format!(
            "Targeted-depth note: the separate one-shot 24,576-MiB brotli export peaked at {:.3} MiB RSS (200 ms sampling) and took {:.3} s wall.\n",
            peak_rss_kb as f64 / 1024.0,
            wall_s,
        ));
    }
    let preserved_base_dir =
        std::env::var("CRAT_A5_PRESERVED_BASE_DIR").unwrap_or_else(|_| "none".to_owned());
    let preserved_base_hash_manifest_sha256 =
        std::env::var("CRAT_A5_PRESERVED_HASH_MANIFEST_SHA256")
            .unwrap_or_else(|_| "none".to_owned());
    if preserved_base_dir != "none" {
        assert_ne!(
            preserved_base_hash_manifest_sha256, "none",
            "resumed P1 requires the externally re-verified hash-manifest digest"
        );
    }
    let preserved_final_dir =
        std::env::var("CRAT_A5_PRESERVED_FINAL_DIR").unwrap_or_else(|_| "none".to_owned());
    let preserved_final_hash_manifest_sha256 =
        std::env::var("CRAT_A5_PRESERVED_FINAL_HASH_MANIFEST_SHA256")
            .unwrap_or_else(|_| "none".to_owned());
    if preserved_final_dir != "none" {
        assert_ne!(
            preserved_final_hash_manifest_sha256, "none",
            "final-row aggregation requires the externally re-verified hash-manifest digest"
        );
    }
    let brotli_peak_rss_kb = brotli_peak_rss_kb
        .map(|value| value.to_string())
        .unwrap_or_else(|| "not-applicable".to_owned());
    let brotli_depth_peak_rss_kb = brotli_depth_peak_rss_kb
        .map(|value| value.to_string())
        .unwrap_or_else(|| "not-applicable".to_owned());
    let brotli_depth_wall_s = brotli_depth_wall_s
        .map(|value| format!("{value:.3}"))
        .unwrap_or_else(|| "not-applicable".to_owned());
    let provenance = format!(
        "date={DATE}\nanalysis_worktree_head={analysis_head}\nanalysis_semantics_head={ANALYSIS_SEMANTICS_HEAD}\ncopy_lend_mode=baseline\nfoster_fact_producer=MutFacts::from_program(mutability_analysis+SourceVarGroups::postprocess_mut_res)\nsnapshot_role=identity-and-pointer-depth-cross-check-only\nsnapshot_producer_head={SNAPSHOT_PRODUCER_HEAD}\nsnapshot_producer_branch_head={SNAPSHOT_PRODUCER_BRANCH_HEAD}\nsnapshot_producer_branch_delta=one-test-only-commit-after-capture\nmanifest_commit={MANIFEST_COMMIT}\nraw_frozen_corpus_sha256={RAW_FROZEN_DIGEST}\nderived_substrate_sha256={DERIVED_SUBSTRATE_DIGEST}\nreplay_safe_definition={REPLAY_SAFE_DEFINITION}\nsubstrate=derived\nsubstrate_selector={}\nrepair=mode_a\nl2=0\nsafe_mono=per_site\nfork_engine=fork\nmutability_facts=on-direct-from-program\nz3_smt_seed=0\nz3_sat_seed=0\ncorpus_shape=read-only-symlink-to-main-checkout-derived-corpus\ncorpus_link={}\ncorpus_target={}\nsnapshot={}\ndeps_shape={}\ndeps_link={}\ndeps_target={}\ndeps_rlibs={}\ndeps_bytemuck_derive=present\nresolver_DIR={}\nresolver_CWD={}\nbase_timeout_s={}\ndeep_timeout_s={}\ncurrent_head_baseline_model_programs={}\npreserved_base_dir={}\npreserved_base_rows={}\npreserved_base_hash_manifest_sha256={}\npreserved_base_wall_source=child-t_total_s\npreserved_final_dir={}\npreserved_final_rows={}\npreserved_final_hash_manifest_sha256={}\npreserved_final_wall_source=child-t_total_s\nbrotli_recovery_mem_cap_mib={}\nbrotli_recovery_peak_rss_kb={}\nbrotli_depth_recovery_mem_cap_mib={}\nbrotli_depth_recovery_peak_rss_kb={}\nbrotli_depth_recovery_wall_s={}\nbrotli_single_file_side_effect=derived-expand-collapsed-to-about-500k-sloc\n",
        substrate_selector.as_deref().unwrap_or("default-derived"),
        corpus_link.display(),
        corpus_target.display(),
        snapshot.display(),
        deps_shape,
        deps_link.display(),
        deps_target.display(),
        rlibs,
        root.display(),
        resolver_cwd.display(),
        base_timeout.as_secs(),
        deep_timeout.as_secs(),
        current_head_baseline_model_count,
        preserved_base_dir,
        if preserved_base_dir == "none" { 0 } else { 19 },
        preserved_base_hash_manifest_sha256,
        preserved_final_dir,
        if preserved_final_dir == "none" { 0 } else { 19 },
        preserved_final_hash_manifest_sha256,
        if brotli_peak_rss_kb == "not-applicable" {
            "not-applicable"
        } else {
            "49152"
        },
        brotli_peak_rss_kb,
        if brotli_depth_peak_rss_kb == "not-applicable" {
            "not-applicable"
        } else {
            "24576"
        },
        brotli_depth_peak_rss_kb,
        brotli_depth_wall_s,
    );
    fs::write(output.join("raw-counts.txt"), raw).expect("write raw P1 rows");
    fs::write(output.join("pair-ledger.tsv"), pair_ledger)
        .expect("write exact count-(5) pair ledger");
    if focused_w14 {
        fs::write(output.join("w14-pair-ledger.tsv"), w14_pair_ledger)
            .expect("write W14 extended pair ledger");
        fs::write(output.join("w14-exposure-ledger.tsv"), w14_exposure_ledger)
            .expect("write W14 exposure ledger");
        fs::write(output.join("w14-per-program.tsv"), w14_programs)
            .expect("write W14 per-program table");
        let values = w14_totals.expect("focused W14 totals");
        fs::write(
            output.join("w14-receipt.txt"),
            format!(
                "status={}\ndata={}\nanalysis_head={analysis_head}\ncopy_lend_mode=baseline\n\
                 a5_mode=precise_replay\na5_world=closed_world_frozen_graph\n\
                 unknown_caller_seeding=false\na5_abi_guard=permitted:measurement-frozen-graph-attested\n\
                 pairs={}\neffective_pairs={}\nplanned_marks={}\nretained_marks={}\n\
                 demoted_by_model={}\nexposures={}\n\
                 demoted={}\nmarked={}\nshared_safe={}\nreplay_safe={}\nunresolved={}\n\
                 precise_rounds={}\nincidence_m={}\nincidence_mr={}\nincidence_r={}\nincidence_rs={}\n\
                 replay_safe_definition={}\n\
                 pair_partition=5555=2391+2480+684\n",
                if values[10] == 0 { "ok" } else { "unresolved" },
                values[10] == 0,
                values[0],
                values[1],
                values[2],
                values[3],
                values[4],
                values[5],
                values[6],
                values[7],
                values[8],
                values[9],
                values[10],
                values[11],
                values[12],
                values[13],
                values[14],
                values[15],
                REPLAY_SAFE_DEFINITION,
            ),
        )
        .expect("write W14 receipt");
    }
    fs::write(output.join("per-program.tsv"), tsv).expect("write P1 TSV");
    fs::write(output.join("report.md"), markdown).expect("write P1 markdown");
    fs::write(output.join("provenance.txt"), provenance).expect("write P1 provenance");
    if classifier_differential {
        fs::write(
            output.join("classifier-differential.txt"),
            format!(
                "status=ok\ndata=true\nanalysis_head={analysis_head}\na5_world=closed_world_frozen_graph\n\
                 a5_mode=classifier_differential\na5_abi_guard=not-yet-consumed-item4\n\
                 replay_safe_definition={}\n\
                 classifier_api=shared-v1\nlegacy_oracle=count5-private-v1\n\
                 candidates={}\nnot_proven_disjoint={}\nbyte_mismatches={}\n\
                 pair_partition=5555=2391+2480+684\nunresolved=0\n",
                REPLAY_SAFE_DEFINITION,
                classifier_candidates.expect("differential candidate total"),
                classifier_not_proven.expect("differential NotProven total"),
                classifier_byte_mismatches.expect("differential mismatch total"),
            ),
        )
        .expect("write classifier differential receipt");
    }
    if let Some(
        [
            den,
            markable,
            read_after,
            opaque,
            recursive,
            volatile,
            unresolved,
            type_mismatch,
            noncopy,
            final_markable,
            all_witness_demoted,
            filter_unresolved,
        ],
    ) = snapshot_totals
    {
        fs::write(
            output.join("snapshot-coverage.txt"),
            format!(
                "status=ok\ndata=true\nanalysis_head={analysis_head}\na5_world=closed_world_frozen_graph\n\
                 a5_mode=precise_replay\nunknown_caller_seeding=false\ndenominator={den}\n\
                 replay_safe_definition={}\n\
                 markable={markable}\nread_after_write={read_after}\nopaque_escape={opaque}\n\
                 recursive={recursive}\nvolatile_or_atomic={volatile}\nunresolved={unresolved}\n\
                 target_type_mismatch={type_mismatch}\nnoncopy_scalar={noncopy}\n\
                 final_markable={final_markable}\nall_witness_demoted={all_witness_demoted}\n\
                 filter_unresolved={filter_unresolved}\n",
                REPLAY_SAFE_DEFINITION,
            ),
        )
        .expect("write snapshot coverage receipt");
    }
    println!("{}", render_count_line(&total));
    if let Some(values) = w14_totals {
        assert_eq!(
            values[10], 0,
            "W14 unresolved exposure residual; artifacts preserved for STOP"
        );
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;

    fn set(values: &[&str]) -> BTreeSet<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    fn formal(function: &str, parameter: u32, depth: u8) -> FormalDecision {
        FormalDecision {
            settles_ref: true,
            currently_predicted_refs: BTreeSet::from([FormalKey {
                function: function.to_owned(),
                parameter,
                depth,
            }]),
            mutable: true,
            mutability_default_fires: 0,
        }
    }

    fn formal_with_mutability(
        function: &str,
        parameter: u32,
        mutable: bool,
        default_fires: usize,
    ) -> FormalDecision {
        FormalDecision {
            mutable,
            mutability_default_fires: default_fires,
            ..formal(function, parameter, 0)
        }
    }

    fn target() -> TargetFunction {
        TargetFunction {
            key: 7,
            path: "callee".to_owned(),
        }
    }

    fn mark(block: u32) -> C9MarkKey {
        C9MarkKey::new(
            9,
            MirLocationKey::new(block, 0),
            [7],
            7,
            1,
            SlotKey {
                variant: 1,
                owner: 9,
                slot: 1,
            },
            2,
            SlotKey {
                variant: 1,
                owner: 9,
                slot: 2,
            },
            PairSide::Right,
            "i32".to_owned(),
        )
        .expect("mark")
    }

    fn mut_read_only_site(id: &str, block: u32, verdict: SnapshotVerdict) -> CallSite {
        CallSite {
            id: id.to_owned(),
            targets: vec![target()],
            arguments: vec![
                formal_with_mutability("callee", 1, true, 0),
                formal_with_mutability("callee", 2, false, 0),
            ],
            pair_facts: BTreeMap::from([((0, 1), PairFacts::default())]),
            snapshot_verdicts: BTreeMap::from([((0, 1), verdict)]),
            post_filter: BTreeMap::from([((0, 1), (true, true))]),
            mark_keys: BTreeMap::from([((0, 1), mark(block))]),
        }
    }

    #[test]
    fn count5_mutability_join_ors_targets_and_defaults_missing_to_mutable() {
        assert_eq!(join_formal_mutability([Some(false), Some(true)]), (true, 0));
        assert_eq!(join_formal_mutability([Some(false), None]), (true, 1));
        assert_eq!(
            join_formal_mutability([Some(false), Some(false)]),
            (false, 0)
        );
    }

    #[test]
    fn count5_partitions_exact_pairs_and_tracks_nonexclusive_site_incidence() {
        let all_risky = |argument_count: usize| {
            (0..argument_count)
                .flat_map(|left| (left + 1..argument_count).map(move |right| (left, right)))
                .map(|pair| (pair, PairFacts::default()))
                .collect()
        };
        let input = ProgramInput {
            name: "fixture".to_owned(),
            call_sites: vec![
                CallSite {
                    id: "caller:bb0:callee".to_owned(),
                    targets: Vec::new(),
                    arguments: vec![
                        formal_with_mutability("callee", 1, true, 0),
                        formal_with_mutability("callee", 2, true, 0),
                        formal_with_mutability("callee", 3, false, 1),
                    ],
                    pair_facts: all_risky(3),
                    snapshot_verdicts: BTreeMap::new(),
                    post_filter: BTreeMap::new(),
                    mark_keys: BTreeMap::new(),
                },
                CallSite {
                    id: "caller:bb1:callee".to_owned(),
                    targets: Vec::new(),
                    arguments: vec![
                        formal_with_mutability("callee", 1, false, 0),
                        formal_with_mutability("callee", 2, false, 0),
                    ],
                    pair_facts: all_risky(2),
                    snapshot_verdicts: BTreeMap::new(),
                    post_filter: BTreeMap::new(),
                    mark_keys: BTreeMap::new(),
                },
            ],
            functions: BTreeMap::new(),
        };

        let measured = measure_program(&input).expect("valid count-(5) fixture");

        assert_eq!(measured.counts.sites_not_proven_disjoint, 2);
        assert_eq!(measured.counts.pair_denominator, 4);
        assert_eq!(measured.counts.mut_mut, 1);
        assert_eq!(measured.counts.mut_read_only, 2);
        assert_eq!(measured.counts.shared_shared, 1);
        assert_eq!(measured.counts.sites_with_mut_mut, 1);
        assert_eq!(measured.counts.sites_with_mut_read_only, 1);
        assert_eq!(measured.counts.sites_with_shared_shared, 1);
        assert_eq!(measured.counts.mutability_default_fires, 2);
        assert_eq!(measured.pairs.len(), 4);
        assert_eq!(measured.pairs[0].left_argument, 1);
        assert_eq!(measured.pairs[0].right_argument, 2);
        assert_eq!(measured.pairs[0].class, PairMutability::MutMut);
        let encoded = render_pair_line(&measured.pairs[2]);
        assert_eq!(parse_pair_line(&encoded), Ok(measured.pairs[2].clone()));
    }

    #[test]
    fn one_unmarkable_witness_keeps_the_formal_pair_effective() {
        let call_sites = vec![
            mut_read_only_site("caller:bb0", 0, SnapshotVerdict::Markable),
            mut_read_only_site("caller:bb1", 1, SnapshotVerdict::ReadAfterWrite),
        ];
        let input = ProgramInput {
            name: "fixture".to_owned(),
            call_sites: call_sites.clone(),
            functions: BTreeMap::new(),
        };

        let measured = measure_program(&input).expect("W14 pair measurement");
        assert_eq!(measured.extended_pairs.len(), 2);
        assert!(
            measured
                .extended_pairs
                .iter()
                .all(|row| row.raw_overlap && row.effective_overlap && !row.selected_mark)
        );
        assert_eq!(
            measured.extended_pairs[0].markability,
            "all-witness-demotion"
        );
        assert_eq!(measured.extended_pairs[1].markability, "read-after-write");
        assert!(measured.final_marks.is_empty());

        let reversed = measure_program(&ProgramInput {
            name: "fixture".to_owned(),
            call_sites: call_sites.into_iter().rev().collect(),
            functions: BTreeMap::new(),
        })
        .expect("reverse W14 pair measurement");
        assert_eq!(measured.extended_pairs, reversed.extended_pairs);
        assert_eq!(measured.final_marks, reversed.final_marks);

        let kinds = measured
            .extended_pairs
            .iter()
            .flat_map(|row| row.left_formals.iter().chain(&row.right_formals))
            .cloned()
            .map(|formal| (formal, SlotKind::Ref))
            .collect::<BTreeMap<_, _>>();
        let model = AcceptedFormalModel {
            refs: BTreeMap::new(),
            kinds,
        };
        let exposure = build_exposure_ledger(
            "fixture",
            &measured.extended_pairs,
            measured.counts.attributed_predicted_refs_depth0,
            &model,
            &model,
        )
        .expect("replay-safe exposure");
        assert!(exposure.iter().all(|row| {
            row.class == ExposureClass::ReplaySafe
                && !row.effective_mut_mut
                && row.effective_mut_read_only
                && !row.effective_shared_shared
        }));
    }

    #[test]
    fn w14_selected_mark_requires_all_witnesses_and_two_final_refs() {
        let input = ProgramInput {
            name: "fixture".to_owned(),
            call_sites: vec![mut_read_only_site(
                "caller:bb0",
                0,
                SnapshotVerdict::Markable,
            )],
            functions: BTreeMap::new(),
        };
        let measured = measure_program(&input).expect("W14 pair measurement");
        assert_eq!(measured.final_marks.len(), 1);
        assert!(measured.extended_pairs[0].selected_mark);
        assert!(!measured.extended_pairs[0].effective_overlap);

        let keys = measured.extended_pairs[0]
            .left_formals
            .iter()
            .chain(&measured.extended_pairs[0].right_formals)
            .cloned()
            .collect::<Vec<_>>();
        let baseline = AcceptedFormalModel {
            refs: BTreeMap::new(),
            kinds: keys
                .iter()
                .cloned()
                .map(|key| (key, SlotKind::Ref))
                .collect(),
        };
        let exposure = build_exposure_ledger(
            "fixture",
            &measured.extended_pairs,
            measured.counts.attributed_predicted_refs_depth0,
            &baseline,
            &baseline,
        )
        .expect("reconciled exposure");
        assert_eq!(exposure.len(), 2);
        assert!(
            exposure
                .iter()
                .all(|row| row.class == ExposureClass::Marked)
        );
        let mut metadata = super::super::report::Row::default();
        metadata.set("a5_w14_pairs", 1);
        metadata.set("a5_w14_exposures", 2);
        let stdout = std::iter::once(render_extended_pair_line(&measured.extended_pairs[0]))
            .chain(exposure.iter().map(render_exposure_line))
            .collect::<Vec<_>>()
            .join("\n");
        parse_w14_ledgers(&stdout, &metadata, &measured.counts)
            .expect("new W14 schemas round-trip");

        let mut precise = AcceptedFormalModel {
            refs: BTreeMap::new(),
            kinds: baseline.kinds.clone(),
        };
        precise.kinds.insert(keys[0].clone(), SlotKind::Raw);
        let filtered = filter_planned_marks_postsolve(&measured.extended_pairs, &precise);
        assert!(filtered[0].planned_mark);
        assert!(!filtered[0].selected_mark);
        assert_eq!(filtered[0].markability, "demoted-by-model");
        assert!(filtered[0].model_attribution.contains("fell="));
    }

    #[test]
    fn absence_of_storage_alias_is_unknown_not_disjoint() {
        let facts = PairFacts::<String> {
            storage_alias: false,
            ..PairFacts::<String>::default()
        };

        assert_eq!(classify_pair(&facts), PairClass::NotProvenDisjoint);
    }

    #[test]
    fn only_complete_positive_evidence_proves_disjointness() {
        let projection_disjoint = PairFacts::<String> {
            projection_disjoint: true,
            ..PairFacts::<String>::default()
        };
        let complete_disjoint_origins = PairFacts {
            origins: SetPairEvidence::Complete {
                left: set(&["origin-a"]),
                right: set(&["origin-b"]),
            },
            ..PairFacts::default()
        };
        let complete_disjoint_points_to = PairFacts {
            points_to: SetPairEvidence::Complete {
                left: set(&["alloc-a"]),
                right: set(&["alloc-b"]),
            },
            ..PairFacts::default()
        };
        let incomplete_disjoint = PairFacts {
            points_to: SetPairEvidence::Incomplete {
                left: set(&["alloc-a"]),
                right: set(&["alloc-b"]),
            },
            ..PairFacts::default()
        };
        let known_storage_alias = PairFacts::<String> {
            storage_alias: true,
            projection_disjoint: true,
            ..PairFacts::<String>::default()
        };

        assert_eq!(
            classify_pair(&projection_disjoint),
            PairClass::ProvenDisjoint
        );
        assert_eq!(
            classify_pair(&complete_disjoint_origins),
            PairClass::ProvenDisjoint
        );
        assert_eq!(
            classify_pair(&complete_disjoint_points_to),
            PairClass::ProvenDisjoint
        );
        assert_eq!(
            classify_pair(&incomplete_disjoint),
            PairClass::NotProvenDisjoint
        );
        assert_eq!(
            classify_pair(&known_storage_alias),
            PairClass::NotProvenDisjoint
        );
    }

    #[test]
    fn shared_classifier_matches_the_legacy_verdict_bytes() {
        let cases = [
            PairFacts::default(),
            PairFacts {
                projection_disjoint: true,
                ..PairFacts::default()
            },
            PairFacts {
                storage_alias: true,
                projection_disjoint: true,
                ..PairFacts::default()
            },
        ];

        for facts in cases {
            assert_eq!(
                classify_pair_differential(&facts),
                Ok(classify_pair(&facts))
            );
        }
    }

    #[test]
    fn risky_sites_deduplicate_formals_and_report_the_depth_zero_subset() {
        let outer = formal("callee", 1, 0);
        let deeper = formal("callee", 2, 1);
        let mut pair_facts = BTreeMap::new();
        pair_facts.insert((0, 1), PairFacts::default());
        let site = CallSite {
            id: "caller:bb0".to_owned(),
            targets: Vec::new(),
            arguments: vec![outer.clone(), deeper.clone()],
            pair_facts,
            snapshot_verdicts: BTreeMap::new(),
            post_filter: BTreeMap::new(),
            mark_keys: BTreeMap::new(),
        };
        let one_ref_site = CallSite {
            id: "caller:bb2".to_owned(),
            targets: Vec::new(),
            arguments: vec![formal("callee", 3, 0)],
            pair_facts: BTreeMap::new(),
            snapshot_verdicts: BTreeMap::new(),
            post_filter: BTreeMap::new(),
            mark_keys: BTreeMap::new(),
        };
        let program = ProgramInput {
            name: "fixture".to_owned(),
            call_sites: vec![
                site.clone(),
                CallSite {
                    id: "caller:bb1".to_owned(),
                    ..site
                },
                one_ref_site,
            ],
            functions: BTreeMap::new(),
        };

        let measured = measure_program(&program).expect("valid fixture").counts;

        assert_eq!(measured.sites_with_two_ref_args, 2);
        assert_eq!(measured.sites_not_proven_disjoint, 2);
        assert_eq!(measured.attributed_predicted_refs, 2);
        assert_eq!(measured.attributed_predicted_refs_depth0, 1);
    }

    #[test]
    fn closedness_is_the_forward_closure_of_unknown_caller_roots() {
        let functions = BTreeMap::from([
            (
                "root".to_owned(),
                FunctionNode {
                    unknown_caller_root: true,
                    callees: set(&["mid"]),
                },
            ),
            (
                "mid".to_owned(),
                FunctionNode {
                    unknown_caller_root: false,
                    callees: set(&["leaf"]),
                },
            ),
            ("leaf".to_owned(), FunctionNode::default()),
            ("closed".to_owned(), FunctionNode::default()),
        ]);
        let program = ProgramInput {
            name: "fixture".to_owned(),
            call_sites: Vec::new(),
            functions,
        };

        let measured = measure_program(&program).expect("valid fixture").counts;

        assert_eq!(measured.unknown_caller_reachable, 3);
        assert_eq!(measured.local_functions, 4);
    }

    #[test]
    fn raw_count_rows_round_trip_and_missing_fields_fail_closed() {
        let counts = ProgramCounts {
            program: "fixture".to_owned(),
            sites_with_two_ref_args: 7,
            sites_not_proven_disjoint: 5,
            attributed_predicted_refs: 4,
            attributed_predicted_refs_depth0: 3,
            unknown_caller_reachable: 2,
            local_functions: 6,
            pair_denominator: 5,
            mut_mut: 2,
            mut_read_only: 2,
            shared_shared: 1,
            sites_with_mut_mut: 2,
            sites_with_mut_read_only: 2,
            sites_with_shared_shared: 1,
            mutability_default_fires: 0,
        };
        let encoded = render_count_line(&counts);

        assert_eq!(parse_count_line(&encoded), Ok(counts.clone()));
        assert!(parse_count_line("A5P1 program=fixture c1=7").is_err());
        assert!(
            parse_count_line(
                "A5P1 program=fixture program=fixture c1=7 c2=5 c3=4 c3_depth0=3 cg_num=2 cg_den=6"
            )
            .is_err()
        );
        assert!(
            parse_count_line("A5P1 program=fixture c1=1 c2=2 c3=4 c3_depth0=3 cg_num=2 cg_den=6")
                .is_err()
        );
        let raw = format!("noise\n{}\nother", render_count_line(&counts));
        assert_eq!(
            parse_single_raw_line(&raw, COUNT_SENTINEL),
            Ok((render_count_line(&counts), counts.clone()))
        );
        assert!(
            parse_single_raw_line(
                &format!(
                    "{}\n{}",
                    render_count_line(&counts),
                    render_count_line(&counts)
                ),
                COUNT_SENTINEL,
            )
            .is_err()
        );
        assert!(parse_count_line(&render_base_line(&counts)).is_err());
        assert_eq!(parse_base_line(&render_base_line(&counts)), Ok(counts));
    }

    #[test]
    fn aggregation_sums_closedness_for_the_micro_average() {
        let rows = [
            ProgramCounts {
                program: "small".to_owned(),
                sites_with_two_ref_args: 1,
                sites_not_proven_disjoint: 1,
                attributed_predicted_refs: 2,
                attributed_predicted_refs_depth0: 1,
                unknown_caller_reachable: 1,
                local_functions: 2,
                pair_denominator: 1,
                mut_mut: 1,
                sites_with_mut_mut: 1,
                ..ProgramCounts::default()
            },
            ProgramCounts {
                program: "large".to_owned(),
                sites_with_two_ref_args: 3,
                sites_not_proven_disjoint: 2,
                attributed_predicted_refs: 4,
                attributed_predicted_refs_depth0: 3,
                unknown_caller_reachable: 9,
                local_functions: 10,
                pair_denominator: 2,
                mut_read_only: 1,
                shared_shared: 1,
                sites_with_mut_read_only: 1,
                sites_with_shared_shared: 1,
                ..ProgramCounts::default()
            },
        ];

        let total = aggregate(&rows).expect("valid aggregate");

        assert_eq!(total.sites_with_two_ref_args, 4);
        assert_eq!(total.sites_not_proven_disjoint, 3);
        assert_eq!(total.attributed_predicted_refs, 6);
        assert_eq!(total.attributed_predicted_refs_depth0, 4);
        assert_eq!(total.unknown_caller_reachable, 10);
        assert_eq!(total.local_functions, 12);
    }

    #[test]
    fn p1_substrate_defaults_to_derived_and_refuses_raw() {
        assert_eq!(a5_substrate_dir(None), Ok("benchmarks/rs-crown-derived"));
        assert_eq!(
            a5_substrate_dir(Some("derived")),
            Ok("benchmarks/rs-crown-derived")
        );
        assert!(a5_substrate_dir(Some("raw")).is_err());
    }

    #[test]
    fn p1_resume_accepts_only_complete_independent_base_rows() {
        let counts = ProgramCounts {
            program: "fixture".to_owned(),
            sites_with_two_ref_args: 7,
            sites_not_proven_disjoint: 1,
            unknown_caller_reachable: 2,
            local_functions: 6,
            pair_denominator: 1,
            mut_mut: 1,
            sites_with_mut_mut: 1,
            ..ProgramCounts::default()
        };
        let stdout = format!(
            "noise\n{}\nBOC1 program=fixture mode=a5-p1 status=needs-depth t_total_s=1.250\n",
            render_base_line(&counts),
        );

        let row = parse_completed_base("fixture", &stdout, "").expect("complete base row");
        match row {
            CompletedBase::NeedsDepth {
                counts,
                wall_seconds,
            } => {
                assert_eq!(counts.program, "fixture");
                assert_eq!(counts.sites_not_proven_disjoint, 1);
                assert_eq!(wall_seconds, 1.25);
            }
            CompletedBase::Final(_) => panic!("fixture needs the depth export"),
        }

        assert!(parse_completed_base("fixture", &stdout, "warning").is_err());
        assert!(parse_completed_base("other", &stdout, "").is_err());
        assert!(parse_completed_base("fixture", "running 1 test\n", "").is_err());
    }

    #[test]
    fn p1_final_resume_accepts_targeted_rows_with_nonzero_c2() {
        let counts = ProgramCounts {
            program: "fixture".to_owned(),
            sites_with_two_ref_args: 7,
            sites_not_proven_disjoint: 1,
            attributed_predicted_refs: 2,
            attributed_predicted_refs_depth0: 1,
            unknown_caller_reachable: 2,
            local_functions: 6,
            pair_denominator: 1,
            mut_mut: 1,
            sites_with_mut_mut: 1,
            ..ProgramCounts::default()
        };
        let pair = PairLedgerRow {
            program: "fixture".to_owned(),
            site: "caller:bb0:callee".to_owned(),
            left_argument: 1,
            right_argument: 2,
            class: PairMutability::MutMut,
            left_mutable: true,
            right_mutable: true,
            left_default_fires: 0,
            right_default_fires: 0,
        };
        let stdout = format!(
            "{}\n{}\nBOC1 program=fixture mode=a5-p1 status=ok t_total_s=2.500\n",
            render_pair_line(&pair),
            render_count_line(&counts),
        );

        let row = parse_completed_base("fixture", &stdout, "").expect("targeted final row");
        match row {
            CompletedBase::Final(run) => {
                assert_eq!(run.counts.sites_not_proven_disjoint, 1);
                assert_eq!(run.counts.attributed_predicted_refs_depth0, 1);
                assert_eq!(run.pairs, vec![pair]);
                assert_eq!(run.wall_seconds, 2.5);
            }
            CompletedBase::NeedsDepth { .. } => panic!("targeted row must be final"),
        }
    }

    #[test]
    fn artifact_join_distinguishes_settled_from_currently_predicted_ref() {
        // Minimized from the manifest-verified libcsv/csv_fwrite rows.  Reconciliation
        // requires binding_i.hi <= decl_i.lo and decl_(i-1).hi <= binding_i.lo;
        // the synthetic change is limited to fp's outcome/degrade_reason under test.
        let a = concat!(
            "{\"fn_path\":\"src::libcsv::csv_fwrite\",\"mir_local\":1,\"param_name\":\"fp\",\"arg_index\":1,\"ptr_depth\":1,\"pairing_confidence\":\"high\",\"decl_span\":\"/Users/p51lee/dev/agent-worktrees/crat-m1/crates/pointer_replacer/../../benchmarks/rs-crown/libcsv/src/libcsv.rs:856:13: 856:22\",\"decl_span_lo\":34779,\"decl_span_hi\":34788,\"binding_span_lo\":null,\"binding_span_hi\":null,\"decl_shape\":\"raw-ptr\",\"outcome\":\"degraded\",\"degrade_reason\":\"raw-pointer-operation\"}\n",
            "{\"fn_path\":\"src::libcsv::csv_fwrite\",\"mir_local\":2,\"param_name\":\"src\",\"arg_index\":2,\"ptr_depth\":1,\"pairing_confidence\":\"high\",\"decl_span\":\"/Users/p51lee/dev/agent-worktrees/crat-m1/crates/pointer_replacer/../../benchmarks/rs-crown/libcsv/src/libcsv.rs:857:14: 857:33\",\"decl_span_lo\":34803,\"decl_span_hi\":34822,\"binding_span_lo\":null,\"binding_span_hi\":null,\"decl_shape\":\"raw-ptr\",\"outcome\":\"ref-shared\",\"degrade_reason\":null}\n",
        );
        let b = concat!(
            "{\"fn_path\":\"src::libcsv::csv_fwrite\",\"mir_local\":1,\"param_name\":\"fp\",\"arg_index\":1,\"ptr_depth\":1,\"pairing_confidence\":\"high\",\"decl_span\":null,\"decl_span_lo\":null,\"decl_span_hi\":null,\"binding_span_lo\":34771,\"binding_span_hi\":34777,\"decl_shape\":null,\"outcome\":null,\"degrade_reason\":null}\n",
            "{\"fn_path\":\"src::libcsv::csv_fwrite\",\"mir_local\":2,\"param_name\":\"src\",\"arg_index\":2,\"ptr_depth\":1,\"pairing_confidence\":\"high\",\"decl_span\":null,\"decl_span_lo\":null,\"decl_span_hi\":null,\"binding_span_lo\":34794,\"binding_span_hi\":34801,\"decl_shape\":null,\"outcome\":null,\"degrade_reason\":null}\n",
        );
        let facts = concat!(
            "fn_path\tmir_local\tis_param\tannotated\tslot\tkind\traw_op\tptr_cmp\tctor\tlen_class\tsize_expr\n",
            "src::libcsv::csv_fwrite\t1\t1\t1\t1\tref\t-\t0\tparam\tparam-no-site\t\n",
            "src::libcsv::csv_fwrite\t2\t1\t1\t1\tref\t-\t0\tparam\tparam-no-site\t\n",
        );

        let formals = parse_formals(a, b, facts).expect("valid joined fixture");
        let fp = &formals[&("src::libcsv::csv_fwrite".to_owned(), 1)];
        let src = &formals[&("src::libcsv::csv_fwrite".to_owned(), 2)];

        assert!(fp.settles_ref);
        assert!(!fp.currently_predicted_ref);
        assert!(src.settles_ref);
        assert!(src.currently_predicted_ref);
    }

    #[test]
    fn unknown_root_parameters_keep_a_direct_call_pair_risky() {
        ::utils::compilation::run_compiler_on_str(
            r#"
unsafe fn two(x: *mut i32, y: *mut i32) { *x = *y + 1; }
pub unsafe fn entry(p: *mut i32, q: *mut i32) { two(p, q); }
"#,
            |tcx| {
                let program = super::super::collect_program(tcx);
                let two = program
                    .functions
                    .iter()
                    .copied()
                    .find(|did| tcx.item_name(did.to_def_id()).as_str() == "two")
                    .expect("two");
                let path = tcx.def_path_str(two.to_def_id());
                let formals = BTreeMap::from([
                    (
                        (path.clone(), 1),
                        ArtifactFormal {
                            settles_ref: false,
                            currently_predicted_ref: false,
                            ptr_depth: 1,
                        },
                    ),
                    (
                        (path, 2),
                        ArtifactFormal {
                            settles_ref: false,
                            currently_predicted_ref: false,
                            ptr_depth: 1,
                        },
                    ),
                ]);

                let accepted = accepted_current_model(tcx, &program, &formals)
                    .expect("current-head baseline model");
                let measured = measure_tcx(
                    "fixture",
                    tcx,
                    &formals,
                    &accepted,
                    Duration::ZERO,
                    false,
                    None,
                )
                .expect("measured fixture");

                assert_eq!(measured.counts.sites_with_two_ref_args, 1);
                assert_eq!(measured.counts.sites_not_proven_disjoint, 1);
                assert_eq!(measured.counts.attributed_predicted_refs, 2);
                assert_eq!(measured.counts.attributed_predicted_refs_depth0, 2);
                assert_eq!(measured.counts.unknown_caller_reachable, 2);
                assert_eq!(measured.counts.local_functions, 2);

                let focused = measure_tcx(
                    "fixture",
                    tcx,
                    &formals,
                    &accepted,
                    Duration::ZERO,
                    true,
                    None,
                )
                .expect("focused W14 fixture");
                let w14 = focused.w14.expect("focused W14 rows");
                assert_eq!(w14.pairs.len(), 1);
                assert_eq!(w14.exposures.len(), 2);
                assert!(
                    w14.exposures
                        .iter()
                        .all(|row| row.class != ExposureClass::Unresolved)
                );
            },
        )
        .expect("fixture compiles");
    }
}
