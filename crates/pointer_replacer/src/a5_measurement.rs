use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    time::{Duration, Instant},
};

use points_to::andersen::{self, Var};
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, TerminatorKind},
    ty::TyCtxt,
};
use rustc_type_ir::TyKind;

use crate::{
    analyses::{
        borrow::lifetime_flow::{self, BodyLifetimeFlow},
        borrow_ownership::{
            SlotKind,
            a5_overlap::{
                A5World, C9MarkKey, PairClass, PairFacts, PairSide, SetPairEvidence,
                SnapshotVerdict, classify_pair,
            },
            a5_snapshot_effects::snapshot_verdict_for_target,
            borrow_engine::ParameterOverlap,
            construction::{
                CopyLendMode, construct_bo_into, verify_bo_construction,
                verify_bo_construction_with_parameter_overlaps,
            },
            crate_slots::CrateSlots,
            export::with_bo_export,
            l2::{MirLocationKey, SlotKey},
            mutability_facts::MutFacts,
            origins::compute_origins,
            resolve::{ResolvedSlot, resolve_place},
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
) -> Result<W14Measurement, String> {
    if measured.extended_pairs.len() != measured.pairs.len()
        || measured.extended_pairs.iter().any(|row| !row.raw_overlap)
    {
        return Err("W14 raw/extended pair ledger does not cover the exact denominator".to_owned());
    }
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
    let precise = project_formal_kinds(program.tcx, program, slots, formals, &model)?;

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
        precise_rounds: stats.rounds,
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
        measure_tcx(&program, tcx, &formals, &accepted, model_time, focused_w14)
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
            || columns[8..]
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
                let measured =
                    measure_tcx("fixture", tcx, &formals, &accepted, Duration::ZERO, false)
                        .expect("measured fixture");

                assert_eq!(measured.counts.sites_with_two_ref_args, 1);
                assert_eq!(measured.counts.sites_not_proven_disjoint, 1);
                assert_eq!(measured.counts.attributed_predicted_refs, 2);
                assert_eq!(measured.counts.attributed_predicted_refs_depth0, 2);
                assert_eq!(measured.counts.unknown_caller_reachable, 2);
                assert_eq!(measured.counts.local_functions, 2);

                let focused =
                    measure_tcx("fixture", tcx, &formals, &accepted, Duration::ZERO, true)
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
