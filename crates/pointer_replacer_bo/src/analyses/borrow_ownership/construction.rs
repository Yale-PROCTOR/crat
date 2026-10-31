#[cfg(test)]
use std::cell::Cell;
use std::collections::BTreeSet;
#[cfg(test)]
use std::time::{Duration, Instant};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::{
    BasicBlock, Body, Local, Location, Operand, Place, ProjectionElem, RETURN_PLACE, Rvalue,
    StatementKind,
    visit::{PlaceContext, Visitor},
};
use rustc_mir_dataflow::Analysis;
use rustc_span::def_id::LocalDefId;
use sha2::{Digest, Sha256};

#[cfg(test)]
use super::borrow_verify::verify_guarded_to_fixpoint_counting_impl;
#[cfg(test)]
use super::borrow_verify::verify_to_fixpoint_counting_with_flows;
#[cfg(test)]
use super::coherence::add_coherence_tagging_uses;
#[cfg(test)]
use super::{BoOwnEmissionStats, param_overlap::CopyMarkKey};
use super::{
    CrateCtxt, SlotKind,
    borrow_verify::{LoopBackend, verify_to_fixpoint_counting_with_flows_impl},
    boundary_table::{self, Matcher, Role},
    coherence::{
        CopyLendPair, FieldRefPlan, add_coherence, add_coherence_removal_only,
        add_coherence_with_copy_lends, constrain_field_ref_worthiness,
        positive_opaque_return_slots,
    },
    crate_slots::{CrateSlots, ptr_chain_depth},
    emit_crate_ownership_constraints, emit_crate_ownership_constraints_with_copy_lends,
    guarded_repair::{MirLocationKey, SlotKey},
    mutability_facts::MutFacts,
    origin_flow::OriginFlowResults,
    origin_summary::{OriginSummaries, SignatureRoot},
    overlap_producer::{OverlapPlan, PlannedCopyMark, produce_overlap_plan},
    param_overlap::{
        AbiGuardDisposition, OverlapMode, OverlapWorld, WholeProgramAttestation,
        apply_coarse_constraints,
    },
    resolve::{ResolvedSlot, resolve_place},
    slots::SlotOwner,
    solver::{KindSolver, Selectors, SlotRef},
    sources::collect_malloc_source_slots,
};
use crate::{
    analyses::{
        liveness::MaybeLiveLocals,
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum CopyLendMode {
    #[default]
    Baseline,
    RemovalOnly,
    LendArm,
}

impl CopyLendMode {
    pub(crate) fn current() -> Self {
        #[cfg(test)]
        if let Some(mode) = COPY_LEND_MODE_OVERRIDE.with(Cell::get) {
            return mode;
        }
        Self::LendArm
    }

    #[cfg(test)]
    pub(crate) fn with_override<T>(self, f: impl FnOnce() -> T) -> T {
        struct Restore(Option<CopyLendMode>);
        impl Drop for Restore {
            fn drop(&mut self) {
                COPY_LEND_MODE_OVERRIDE.with(|slot| slot.set(self.0));
            }
        }
        let _restore = Restore(COPY_LEND_MODE_OVERRIDE.with(|slot| slot.replace(Some(self))));
        f()
    }

    #[cfg(test)]
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Baseline => "baseline",
            Self::RemovalOnly => "removal_only",
            Self::LendArm => "lend_arm",
        }
    }
}

#[cfg(test)]
thread_local! {
    static COPY_LEND_MODE_OVERRIDE: Cell<Option<CopyLendMode>> = const { Cell::new(None) };
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct CopyLendEligibility {
    pub(crate) pairs: FxHashSet<CopyLendPair>,
    pub(crate) sites: Vec<CopyLendSite>,
}

/// Exact primary exclusion used by the retained copy-lend funnel diagnostic. The
/// production predicate and the diagnostic share this enum-returning
/// classifier, so measurement cannot silently reinterpret eligibility.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CopyLendEligibilityDrop {
    C2MutableOrMissingDestination,
    C3FieldInClosure,
    /// The copy's destination flows to a release.
    FreeDestination,
    C3AggregateStore,
    C3FieldStore,
    C3Return,
    C3UnresolvedStore,
    C3OrdinaryCall,
    C3ReallocSource,
    C3OutwardUnknownCall,
    /// The source holds its caller's value and nothing in the function releases it,
    /// so the lend reading would make an owner of a value the function was only
    /// handed.
    GuardCallerDerivedSource,
    /// Mutable copy-lend: the destination is written through and
    /// `p`, or another copy of `p`, is used while `q` is live, so `q = &mut *p` would not be
    /// unique.
    C2MutableWindowAccess,
}

impl CopyLendEligibilityDrop {
    #[cfg(test)]
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::C2MutableOrMissingDestination => "c2-mutable-or-missing-destination",
            Self::C3FieldInClosure => "c3-field-in-closure",
            Self::FreeDestination => "s2-2-free-destination",
            Self::C3AggregateStore => "c3-aggregate-store",
            Self::C3FieldStore => "c3-field-store",
            Self::C3Return => "c3-return",
            Self::C3UnresolvedStore => "c3-unresolved-store",
            Self::C3OrdinaryCall => "c3-ordinary-call",
            Self::C3ReallocSource => "c3-realloc-source",
            Self::C3OutwardUnknownCall => "c3-outward-unknown-call",
            Self::GuardCallerDerivedSource => "guard-caller-derived-source",
            Self::C2MutableWindowAccess => "c2-mutable-window-access",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CopyLendPairCandidate {
    pub(crate) pair: CopyLendPair,
    pub(crate) sites: Vec<CopyLendSite>,
    pub(crate) drop: Option<CopyLendEligibilityDrop>,
}

pub(crate) struct BoConstruction {
    pub(crate) source_events: std::sync::Arc<super::source_events::SourceEvents>,
    #[cfg(test)]
    pub(crate) qualifier_facts: super::qualifier_facts::QualifierFacts,
    #[cfg(test)]
    pub(crate) array_fields: super::array_fields::ArrayFieldFacts,
    pub(crate) mode: CopyLendMode,
    pub(crate) nullability: super::nullability::NullabilityFacts,
    pub(crate) field_ref_plan: FieldRefPlan,
    #[cfg(test)]
    pub(crate) a2_killed_memberships: usize,
    #[cfg(test)]
    pub(crate) a2_opaque_result_guards: usize,
    pub(crate) selectors: Selectors,
    pub(crate) eligibility: CopyLendEligibility,
    pub(crate) esc_minimal: super::esc_minimal::EscMinimalSelection,
    #[cfg(test)]
    pub(crate) stats: BoOwnEmissionStats,
    #[cfg(test)]
    pub(crate) eligibility_elapsed: Duration,
    #[cfg(test)]
    pub(crate) emit_elapsed: Duration,
    #[cfg(test)]
    pub(crate) coherence_elapsed: Duration,
}

#[derive(Clone, Debug)]
pub(crate) struct VerifiedBo {
    pub(crate) model: FxHashMap<SlotRef, SlotKind>,
    pub(crate) baseline_model: FxHashMap<SlotRef, SlotKind>,
    /// The copy marks the accepted model kept.
    #[cfg(test)]
    pub(crate) retained_copy_marks: BTreeSet<CopyMarkKey>,
    /// The kept copy marks with what the rewriter needs to place them.
    pub(crate) retained_copy_plans: Vec<PlannedCopyMark>,
    #[cfg(test)]
    pub(crate) summary_artifact: super::param_overlap::OverlapSummaryArtifact,
    #[cfg(test)]
    pub(crate) mark_artifact: String,
    #[cfg(test)]
    pub(crate) site_artifact: String,
    #[cfg(test)]
    pub(crate) nullable_artifact: String,
    #[cfg(test)]
    pub(crate) field_ref_artifact: String,
    pub(crate) receipt: String,
    #[cfg(test)]
    pub(crate) round_stats: super::borrow_verify::RoundStats,
    #[cfg(test)]
    pub(crate) esc_minimal: super::esc_minimal::EscMinimalSelection,
    #[cfg(test)]
    pub(crate) selector_sources: usize,
    #[cfg(test)]
    pub(crate) selector_sinks: usize,
    #[cfg(test)]
    pub(crate) emission_stats: BoOwnEmissionStats,
    #[cfg(test)]
    pub(crate) construction_emit_elapsed: Duration,
    #[cfg(test)]
    pub(crate) construction_coherence_elapsed: Duration,
    #[cfg(test)]
    pub(crate) check_sat_count: usize,
    #[cfg(test)]
    pub(crate) hard_check_count: usize,
    #[cfg(test)]
    pub(crate) optimize_materialization_count: usize,
    #[cfg(test)]
    pub(crate) lazy_plain_hard_check_count: usize,
    #[cfg(test)]
    pub(crate) lazy_tracked_recheck_count: usize,
    #[cfg(test)]
    pub(crate) lazy_plain_materialization_count: usize,
    #[cfg(test)]
    pub(crate) hard_check_elapsed: Duration,
    #[cfg(test)]
    pub(crate) optimize_materialization_elapsed: Duration,
    /// How many return-refinement links the construction added.
    pub(crate) return_refined_links: usize,
    /// The copy marks the overlap plan proposed.
    #[cfg(test)]
    pub(crate) planned_copy_marks: BTreeSet<CopyMarkKey>,
    #[cfg(test)]
    pub(crate) producer_stats: super::overlap_producer::OverlapProducerStats,
}

/// Typed diagnostic for every `None` boundary before the production overlap
/// worker can write its model and its endpoint-retraction and escape-minimal
/// ledgers. Production callers retain the
/// historical `Option` API; measurement callers use the reporting twin below.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OverlapPreledgerDeclineReason {
    BaselineConstruction,
    BaselineVerification,
    /// The overlap plan could not be produced.
    OverlapPlanProduction,
    RefinedFallbackConstruction,
    RefinedFallbackVerification,
    PreciseConstruction,
    PreciseVerification,
    CoarseConstruction,
    CoarseVerification,
}

impl OverlapPreledgerDeclineReason {
    #[cfg(test)]
    pub(crate) const ALL: [Self; 9] = [
        Self::BaselineConstruction,
        Self::BaselineVerification,
        Self::OverlapPlanProduction,
        Self::RefinedFallbackConstruction,
        Self::RefinedFallbackVerification,
        Self::PreciseConstruction,
        Self::PreciseVerification,
        Self::CoarseConstruction,
        Self::CoarseVerification,
    ];

    #[cfg(test)]
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::BaselineConstruction => "baseline-construction",
            Self::BaselineVerification => "baseline-verification",
            Self::OverlapPlanProduction => "a5-plan-production",
            Self::RefinedFallbackConstruction => "refined-fallback-construction",
            Self::RefinedFallbackVerification => "refined-fallback-verification",
            Self::PreciseConstruction => "precise-construction",
            Self::PreciseVerification => "precise-verification",
            Self::CoarseConstruction => "coarse-construction",
            Self::CoarseVerification => "coarse-verification",
        }
    }
}

/// Relay main/388 O2 (R1383-1 R4): the receipt's incumbent lines -- rounds whose model is an optimize
/// incumbent at the budget, incumbents the hard evaluation refused, and the budget in force -- written
/// only when the solve met one, so a receipt without one is byte for byte what it was.
pub(crate) fn incumbent_keys(stats: &[&super::borrow_verify::RoundStats]) -> String {
    let accepted: usize = stats.iter().map(|stats| stats.incumbent_rounds).sum();
    let refused: usize = stats.iter().map(|stats| stats.hard_eval_failed).sum();
    if accepted + refused == 0 {
        return String::new();
    }
    format!(
        "incumbent_rounds={accepted}\nhard_eval_failed={refused}\nquery_budget_ms={}\n",
        super::execution_guard::query_timeout_ms()
    )
}

/// Name which of `verify_to_fixpoint`'s `None` exits fired, from the stats it
/// fills on the way out.
fn precise_verification_cause(stats: &super::borrow_verify::RoundStats) -> String {
    let cause = if stats.cap_exhausted {
        "cap-exhausted".to_owned()
    } else if let Some(field) = stats.field_conflict_decline {
        format!(
            "field-conflict field={field:?} kind={:?}",
            stats.field_conflict_kind
        )
    } else if !stats.source_retirement_decline.is_empty() {
        format!(
            "source-retirement unresolved={} first={:?}",
            stats.source_retirement_decline.len(),
            stats.source_retirement_decline.first()
        )
    } else {
        "round-solve-unsat-or-reader-failure".to_owned()
    };
    format!(
        "{cause}; rounds={} commits_conflict={} commits_per_round={:?} dropped_sinks={} dropped_sources={} repair={:?}",
        stats.rounds,
        stats.commits_conflict,
        stats.commits_per_round,
        stats.dropped_sinks,
        stats.dropped_sources,
        stats.repair
    )
}

/// Why an overlap solve declined before its ledger: the stage, and the detail
/// where one exists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OverlapPreledgerDecline {
    reason: OverlapPreledgerDeclineReason,
    detail: Option<String>,
}

impl OverlapPreledgerDecline {
    fn at(reason: OverlapPreledgerDeclineReason) -> Self {
        Self {
            reason,
            detail: None,
        }
    }

    fn from_error(reason: OverlapPreledgerDeclineReason, error: impl std::fmt::Display) -> Self {
        Self {
            reason,
            detail: Some(error.to_string()),
        }
    }

    fn with_detail(reason: OverlapPreledgerDeclineReason, detail: String) -> Self {
        Self {
            reason,
            detail: Some(detail),
        }
    }

    #[cfg(test)]
    pub(crate) fn reason(&self) -> OverlapPreledgerDeclineReason {
        self.reason
    }

    #[cfg(test)]
    pub(crate) fn detail(&self) -> Option<&str> {
        self.detail.as_deref()
    }
}

/// The digest of the frozen overlap pair ledger; the overlap receipt prints it.
const OVERLAP_PAIR_LEDGER_SHA256: &str =
    "16dac90cf269c5480e6f612e54733dd210e41393a879202c7138e93cd7d360e1";
const REPLAY_SAFE_DEFINITION: &str = "no incompatible access derived by precise replay with the effective parameter-overlap map injected; O2 closed-world frozen graph.";

struct NullabilityArtifacts {
    artifact: String,
    slots: usize,
    fields: usize,
}

fn nullability_artifacts(construction: &BoConstruction) -> NullabilityArtifacts {
    let mut rows = construction
        .nullability
        .slots()
        .into_iter()
        .map(|slot| {
            let key = SlotKey::of(slot);
            (
                key,
                construction.nullability.is_null_use.contains(&slot),
                construction.nullability.null_literal.contains(&slot),
                matches!(slot, SlotRef::Field(_)),
            )
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| row.0);
    let mut artifact = String::from("variant\towner\tslot\tis_null_use\tnull_literal\tnullable\n");
    for (key, is_null, literal, _) in &rows {
        artifact.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\ttrue\n",
            key.variant, key.owner, key.slot, is_null, literal,
        ));
    }
    NullabilityArtifacts {
        slots: rows.len(),
        fields: rows.iter().filter(|row| row.3).count(),
        artifact,
    }
}

/// The field-reference plan's opacity facts: a per-field table and the counts the
/// receipt prints.
struct OpacityArtifacts {
    artifact: String,
    opaque_stores: usize,
    unresolved_unresolvable: usize,
    nullable_store_fields: usize,
}

/// The opacity facts of `construction`'s field-reference plan.
fn opacity_artifacts(construction: &BoConstruction) -> OpacityArtifacts {
    let mut artifact =
        String::from("variant\towner\tslot\topaque\tunresolved_unresolvable\tnullable\tsafe\n");
    for row in &construction.field_ref_plan.rows {
        let key = SlotKey::of(row.field);
        artifact.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            key.variant,
            key.owner,
            key.slot,
            row.opaque,
            row.unresolved_unresolvable,
            row.nullable,
            row.safe,
        ));
    }
    OpacityArtifacts {
        opaque_stores: construction
            .field_ref_plan
            .rows
            .iter()
            .map(|row| row.opaque)
            .sum(),
        unresolved_unresolvable: construction
            .field_ref_plan
            .rows
            .iter()
            .map(|row| row.unresolved_unresolvable)
            .sum(),
        nullable_store_fields: construction
            .field_ref_plan
            .rows
            .iter()
            .filter(|row| row.nullable > 0)
            .count(),
        artifact,
    }
}

pub(crate) fn model_digest(model: &FxHashMap<SlotRef, SlotKind>) -> String {
    let mut rows = model
        .iter()
        .map(|(&slot, kind)| {
            let key = SlotKey::of(slot);
            let kind = match kind {
                SlotKind::Raw => "raw",
                SlotKind::Ref => "ref",
                SlotKind::Owning => "owning",
            };
            format!("{}\t{}\t{}\t{kind}", key.variant, key.owner, key.slot)
        })
        .collect::<Vec<_>>();
    rows.sort();
    format!("{:x}", Sha256::digest(rows.join("\n").as_bytes()))
}

fn receipt_field<'a>(receipt: &'a str, key: &str) -> Option<&'a str> {
    receipt
        .lines()
        .find_map(|line| line.strip_prefix(&format!("{key}=")))
}

/// Rebuild only the session-local copy-mark carriers needed by the rewriter from
/// a cached precise model. No solver is constructed or queried here: the
/// overlap plan is a deterministic MIR/fact projection from the cached baseline model,
/// and the persisted construction receipt is checked against both the plan and
/// the consumed final model before its spans are admitted.
pub(crate) fn cached_precise_rewriter_payload(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    baseline_model: &FxHashMap<SlotRef, SlotKind>,
    model: &FxHashMap<SlotRef, SlotKind>,
    attestation: Option<WholeProgramAttestation>,
    receipt: &str,
) -> Result<Vec<PlannedCopyMark>, String> {
    let plan = produce_overlap_plan(
        program,
        slots,
        origins.native_flows(),
        mut_facts,
        baseline_model,
        OverlapMode::PreciseReplay,
        attestation,
    )
    .map_err(|error| format!("cached precise overlap plan: {error:#}"))?;
    let (retained_marks, retained_plans) =
        if matches!(plan.abi_guard, AbiGuardDisposition::Refused { .. }) {
            (BTreeSet::new(), Vec::new())
        } else {
            (plan.retained_marks(model), plan.retained_mark_plans(model))
        };
    let expected = [
        ("a5_mode", OverlapMode::PreciseReplay.label().to_owned()),
        (
            "a5_world",
            OverlapWorld::ClosedWorldFrozenGraph.label().to_owned(),
        ),
        ("selected_model_sha256", model_digest(model)),
        ("a5_summary_sha256", summary_digest(&plan)),
        ("a5_retained_marks", retained_marks.len().to_string()),
        ("a5_retained_mark_sites", retained_plans.len().to_string()),
    ];
    for (key, value) in expected {
        if receipt_field(receipt, key) != Some(value.as_str()) {
            return Err(format!(
                "cached precise receipt mismatch for {key}: expected {value:?}, got {:?}",
                receipt_field(receipt, key)
            ));
        }
    }
    Ok(retained_plans)
}

fn summary_digest(plan: &OverlapPlan) -> String {
    format!(
        "{:x}",
        Sha256::digest(
            format!(
                "{}{}",
                plan.summary_artifact.receipt, plan.summary_artifact.summary_tsv
            )
            .as_bytes()
        )
    )
}

/// The proposed and kept copy marks as a table.
#[cfg(test)]
fn overlap_mark_artifact(
    mode: OverlapMode,
    plan: &OverlapPlan,
    retained: &BTreeSet<CopyMarkKey>,
    selected_model_sha256: &str,
) -> String {
    let mut out = format!(
        "# a5_mode={}\n# a5_world={}\n# a5_abi_guard={}\n# a5_producer=rustc-mir-current-v1\n\
         # a5_pair_ledger_sha256={OVERLAP_PAIR_LEDGER_SHA256}\n# selected_model_sha256={selected_model_sha256}\n\
         caller\tblock\tstatement\tcallee\tleft_param\tright_param\tshared_side\tpointee_type\tretained\n",
        mode.label(),
        OverlapWorld::ClosedWorldFrozenGraph.label(),
        plan.abi_guard.stamp(),
    );
    for mark in &plan.planned_marks {
        let pair = mark.key.pair;
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{:?}\t{}\t{}\n",
            mark.key.caller,
            mark.key.location.block,
            mark.key.location.statement_index,
            pair.function(),
            pair.params().first(),
            pair.params().second(),
            mark.key.shared_side,
            mark.key.pointee_type,
            retained.contains(&mark.key),
        ));
    }
    out
}

/// The overlap site ledger as a table.
#[cfg(test)]
pub(crate) fn overlap_site_artifact(mode: OverlapMode, plan: &OverlapPlan) -> String {
    let mut out = String::from(
        "caller\tblock\tstatement\ttarget\tleft_parameter\tright_parameter\tleft_variant\tleft_owner\tleft_slot\tright_variant\tright_owner\tright_slot\tclass\ta5_world\ta5_mode\ta5_abi_guard\n",
    );
    for site in &plan.site_ledger {
        let class = match site.class {
            super::param_overlap::WitnessMutability::MutMut => "mut_mut",
            super::param_overlap::WitnessMutability::MutReadOnly { .. } => "mut_read_only",
            super::param_overlap::WitnessMutability::SharedShared => "shared_shared",
        };
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            site.caller,
            site.location.block,
            site.location.statement_index,
            site.target,
            site.left_parameter,
            site.right_parameter,
            site.left_actual.variant,
            site.left_actual.owner,
            site.left_actual.slot,
            site.right_actual.variant,
            site.right_actual.owner,
            site.right_actual.slot,
            class,
            OverlapWorld::ClosedWorldFrozenGraph.label(),
            mode.label(),
            plan.abi_guard.stamp(),
        ));
    }
    out
}

fn canonical_receipt(input: String) -> String {
    fn key(line: &str) -> &str {
        line.split_once('=').map_or(line, |(key, _)| key)
    }
    let mut lines = input.lines().collect::<Vec<_>>();
    lines.sort_by(|left, right| {
        let rank = |key: &str| match key {
            "schema" => 0,
            "status" => 1,
            "data" => 2,
            _ => 3,
        };
        let left_key = key(left);
        let right_key = key(right);
        (rank(left_key), left_key).cmp(&(rank(right_key), right_key))
    });
    for pair in lines.windows(2) {
        let left = pair[0].split_once('=').map_or(pair[0], |(key, _)| key);
        let right = pair[1].split_once('=').map_or(pair[1], |(key, _)| key);
        assert_ne!(left, right, "duplicate receipt key {left}");
    }
    format!("{}\n", lines.join("\n"))
}

/// The guarded repair's stamp, only when a verification ran guarded, so every plain-repair
/// receipt is byte-identical. `repair=guarded->mode-a` when any guarded run declined and its
/// program fell back to the plain repair; the fallbacks are counted and their reasons named.
fn repair_keys(stats: &[&super::borrow_verify::RoundStats], receipt: String) -> String {
    let receipt = format!("{receipt}{}", incumbent_keys(stats));
    let guarded = stats
        .iter()
        .filter(|stats| stats.repair == super::borrow_verify::RepairMode::Guarded)
        .collect::<Vec<_>>();
    if guarded.is_empty() {
        return receipt;
    }
    let fallbacks = guarded
        .iter()
        .filter_map(|stats| stats.guarded_fallback.as_ref())
        .collect::<Vec<_>>();
    let mut receipt = receipt;
    receipt.push_str(&format!(
        "repair={}\nguarded_verifications={}\nguarded_fallbacks={}\n",
        if fallbacks.is_empty() {
            "guarded"
        } else {
            "guarded->mode-a"
        },
        guarded.len(),
        fallbacks.len()
    ));
    if !fallbacks.is_empty() {
        receipt.push_str(&format!(
            "guarded_fallback_reasons={}\n",
            fallbacks
                .iter()
                .map(|fallback| format!(
                    "{}@rounds:{}@commits:{}",
                    fallback.reason, fallback.rounds, fallback.commits
                ))
                .collect::<Vec<_>>()
                .join(",")
        ));
    }
    canonical_receipt(receipt)
}

/// The type route's count and digest, only when it removed a pair,
/// so every receipt without one is byte-identical.
fn type_disjoint_keys(plan: &OverlapPlan, mut receipt: String) -> String {
    if !plan.type_disjoint.is_empty() {
        receipt.push_str(&format!(
            "a5_type_disjoint_pairs={}\na5_type_disjoint_sha256={:x}\n",
            plan.type_disjoint.len(),
            Sha256::digest(plan.type_disjoint.join("\n").as_bytes())
        ));
    }
    receipt
}

fn overlap_receipt(
    mode: OverlapMode,
    plan: &OverlapPlan,
    retained: usize,
    retained_sites: usize,
    selected_model_sha256: &str,
    nullability: &NullabilityArtifacts,
    opacity: &OpacityArtifacts,
) -> String {
    canonical_receipt(type_disjoint_keys(
        plan,
        format!(
            "schema=bo-construction-v1\nstatus=ok\ndata=true\ncopy_lend_mode=baseline\n\
         a2_mode=off\nsoundness_mode=a14\na5_mode={}\na5_world={}\nunknown_caller_seeding=false\n\
         a5_abi_guard={}\na5_raw_pairs={}\na5_effective_pairs={}\n\
         a5_raw_site_pairs={}\na5_raw_site_mut_mut={}\na5_raw_site_mut_read_only={}\n\
         a5_raw_site_shared_shared={}\n\
         a5_planned_marks={}\na5_retained_marks={}\na5_retained_mark_sites={}\n\
         a5_producer=rustc-mir-current-v1\n\
         a5_foster_producer=MutFacts::from_program(mutability_analysis+SourceVarGroups::postprocess_mut_res)\n\
         a5_pair_ledger_sha256={OVERLAP_PAIR_LEDGER_SHA256}\nselected_model_sha256={}\n\
         a5_summary_sha256={}\nnullable_slots={}\nnullable_fields={}\n\
         nullable_ledger_sha256={:x}\na14_opaque_stores={}\n\
         a14_unresolved_unresolvable={}\na14_nullable_store_fields={}\n\
         field_ref_ledger_sha256={:x}\nreplay_safe_definition={REPLAY_SAFE_DEFINITION}\n",
            mode.label(),
            OverlapWorld::ClosedWorldFrozenGraph.label(),
            plan.abi_guard.stamp(),
            plan.stats.raw_pairs,
            plan.stats.effective_pairs,
            plan.stats.raw_site_pairs,
            plan.stats.raw_site_mut_mut,
            plan.stats.raw_site_mut_read_only,
            plan.stats.raw_site_shared_shared,
            plan.stats.planned_marks,
            retained,
            retained_sites,
            selected_model_sha256,
            summary_digest(plan),
            nullability.slots,
            nullability.fields,
            Sha256::digest(nullability.artifact.as_bytes()),
            opacity.opaque_stores,
            opacity.unresolved_unresolvable,
            opacity.nullable_store_fields,
            Sha256::digest(opacity.artifact.as_bytes()),
        ),
    ))
}

pub(crate) fn construct_bo_into(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    solver: &KindSolver,
    mode: CopyLendMode,
) -> anyhow::Result<BoConstruction> {
    construct_bo_into_with_esc(program, slots, origins, mut_facts, solver, mode, true)
}

/// The overlap solve's reference construction: the ordinary construction under
/// the active copy-lend mode, without the escape-minimal selection.
fn construct_bo_overlap_reference(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    solver: &KindSolver,
) -> anyhow::Result<BoConstruction> {
    construct_bo_into_with_esc(
        program,
        slots,
        origins,
        mut_facts,
        solver,
        CopyLendMode::current(),
        false,
    )
}

/// One eligible-or-not copy pair of the copy-lend funnel on the overlap solve.
#[cfg(test)]
pub(crate) struct FrameFunnelRow {
    pub(crate) fn_did: LocalDefId,
    pub(crate) lhs_local: Local,
    pub(crate) rhs_local: Local,
    pub(crate) sites: usize,
    /// `None` = S1 (eligible under C1–C4).
    pub(crate) drop: Option<CopyLendEligibilityDrop>,
    /// S2: the lend reading (destination Ref, source Owning) is satisfiable in the
    /// solve's hard universe; `None` for an ineligible pair.
    pub(crate) lend: Option<z3::SatResult>,
    /// The source alone Owning, for attribution; `None` for an ineligible pair.
    pub(crate) source_own: Option<z3::SatResult>,
    pub(crate) shape: &'static str,
}

/// The copy-lend funnel S0 → S2 on the overlap solve's reference construction:
/// S0 = every depth-0 local copy pair, S1 = C1–C4 eligible, S2 = the lend
/// reading satisfiable in the hard universe (endpoint selectors free).
/// Measurement only.
#[cfg(test)]
pub(crate) fn copy_lend_frame_funnel(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    query_timeout: Duration,
) -> Vec<FrameFunnelRow> {
    assert_eq!(CopyLendMode::current(), CopyLendMode::LendArm);
    let _world = super::licensing::stack_entry::enter_world(Some(
        WholeProgramAttestation::FrozenBenchmarkGraph,
    ));
    super::execution_guard::enter_model();
    let inventory = std::sync::Arc::new(super::source_events::collect(program));
    super::source_events::with_inventory(&inventory, || {
        let candidates =
            analyze_copy_lend_candidates(program, slots, mut_facts, origins.native_flows());
        let solver = KindSolver::new_hard_only(slots);
        solver.set_random_seed(0);
        solver.set_query_timeout(query_timeout);
        let construction =
            construct_bo_overlap_reference(program, slots, origins, mut_facts, &solver)
                .expect("funnel frame construction");
        let eligible = candidates
            .iter()
            .filter(|candidate| candidate.drop.is_none())
            .map(|candidate| candidate.pair)
            .collect::<FxHashSet<_>>();
        assert_eq!(
            eligible, construction.eligibility.pairs,
            "funnel classifier and frame eligibility diverged"
        );
        super::coherence::constrain_field_ownership(&solver, slots, program);
        candidates
            .into_iter()
            .map(|CopyLendPairCandidate { pair, sites, drop }| {
                let (lend, source_own) = if drop.is_none() {
                    (
                        Some(
                            solver.check_with_assumptions(&[solver.lend_guard(pair.lhs, pair.rhs)]),
                        ),
                        Some(solver.check_with_assumptions(&[solver.owning_literal(pair.rhs)])),
                    )
                } else {
                    (None, None)
                };
                let site = sites[0];
                let body = program
                    .tcx
                    .mir_drops_elaborated_and_const_checked(site.fn_did)
                    .borrow();
                FrameFunnelRow {
                    fn_did: site.fn_did,
                    lhs_local: site.lhs_local,
                    rhs_local: site.rhs_local,
                    sites: sites.len(),
                    drop,
                    lend,
                    source_own,
                    shape: copy_lend_source_consumer(
                        program,
                        &body,
                        site.rhs_local,
                        site.lhs_local,
                    ),
                }
            })
            .collect()
    })
}

/// Wall probe: why a slot is not Owning / not Ref in the overlap solve. On its reference
/// construction's hard universe (assertion-tracked), each target is asked
/// `own` and `ref ∧ ¬own`, first alone ("hard") and then with every `holds` slot
/// kept at its accepted kind ("held": Ref slots keep `ref`, Owning slots keep
/// `own`). An UNSAT hard query names the constraints (the core's labels); an
/// UNSAT held query that is SAT hard names the accepted kinds it would cost (the
/// objective's trade); SAT held means only the verify loop can explain the kind.
/// Measurement only; one row per target and query.
#[cfg(test)]
pub(crate) fn a4_wall_probe(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    targets: &[(String, SlotRef)],
    holds: &[(String, SlotRef, bool)],
    query_timeout: Duration,
) -> Vec<String> {
    use z3::{SatResult, ast::Bool};
    let _world = super::licensing::stack_entry::enter_world(Some(
        WholeProgramAttestation::FrozenBenchmarkGraph,
    ));
    super::execution_guard::enter_model();
    let inventory = std::sync::Arc::new(super::source_events::collect(program));
    super::source_events::with_inventory(&inventory, || {
        let solver = KindSolver::new_hard_only(slots);
        solver.set_random_seed(0);
        solver.set_query_timeout(query_timeout);
        construct_bo_overlap_reference(program, slots, origins, mut_facts, &solver)
            .expect("a4 frame construction");
        super::coherence::constrain_field_ownership(&solver, slots, program);
        let tracker = solver.tracker().expect("mandatory tracker");
        // Counterfactual: `CRAT_E5C_A4_DROP` = `|`-separated label substrings;
        // every tracked constraint whose label contains one is switched off.
        let drop: Vec<String> = std::env::var("CRAT_E5C_A4_DROP")
            .unwrap_or_default()
            .split('|')
            .filter(|d| !d.is_empty())
            .map(str::to_owned)
            .collect();
        let base: Vec<Bool> = tracker
            .labeled_tracks()
            .into_iter()
            .filter(|(_, label)| !drop.iter().any(|d| label.contains(d.as_str())))
            .map(|(track, _)| track)
            .collect();
        let check = |extra: &[Bool]| -> SatResult {
            let mut assumptions = base.clone();
            assumptions.extend_from_slice(extra);
            solver.optimize().check(&assumptions)
        };
        let verdict = |r: SatResult| match r {
            SatResult::Sat => "sat",
            SatResult::Unsat => "unsat",
            SatResult::Unknown => "unknown",
        };
        let mut rows = Vec::new();
        for (key, slot) in targets {
            let own = solver.owning_literal(*slot);
            let ref_only = Bool::and(&[&solver.ref_literal(*slot), &own.not()]);
            let fast = std::env::var_os("CRAT_E5C_A4_FAST").is_some();
            for (goal, force) in [("own", own.clone()), ("ref", ref_only)] {
                if fast && goal == "ref" {
                    continue;
                }
                let core = |r: SatResult, extra: &[(Bool, String)]| -> String {
                    if r != SatResult::Unsat {
                        return "-".to_owned();
                    }
                    // Deletion-minimal: a tracked constraint is kept only if the
                    // query turns SAT without it (untracked asserts stay on).
                    let mut kept: Vec<Bool> = solver
                        .optimize()
                        .get_unsat_core()
                        .into_iter()
                        .filter(|literal| *literal != force)
                        .collect();
                    if kept.len() <= 400 {
                        let mut index = 0;
                        while index < kept.len() {
                            let mut trial = kept.clone();
                            trial.remove(index);
                            let mut assumptions = trial.clone();
                            assumptions.push(force.clone());
                            // untracked asserts stay on; dropped tracks stay off
                            let keep_off: Vec<Bool> = tracker
                                .labeled_tracks()
                                .into_iter()
                                .filter(|(_, l)| drop.iter().any(|d| l.contains(d.as_str())))
                                .map(|(t, _)| t.not())
                                .collect();
                            assumptions.extend(keep_off);
                            if solver.optimize().check(&assumptions) == SatResult::Unsat {
                                kept = trial;
                            } else {
                                index += 1;
                            }
                        }
                    }
                    let mut held = Vec::new();
                    let mut labels = Vec::new();
                    for literal in kept {
                        if let Some((_, k)) = extra.iter().find(|(l, _)| *l == literal) {
                            held.push(k.clone());
                        } else if let Some(label) = tracker.label_of(&literal) {
                            labels.push(label);
                        } else {
                            labels.push(format!("?{literal}"));
                        }
                    }
                    held.sort();
                    labels.sort();
                    format!(
                        "held[{}]={} | hard[{}]={}",
                        held.len(),
                        held.join(","),
                        labels.len(),
                        labels.join(" ; ")
                    )
                };
                let hard = check(std::slice::from_ref(&force));
                if fast {
                    rows.push(format!("{key}\t{goal}\t{}\t-\t-\t-", verdict(hard)));
                    continue;
                }
                let hard_core = core(hard, &[]);
                let extra = holds
                    .iter()
                    .filter(|(_, other, _)| other != slot)
                    .map(|(k, other, owning)| {
                        let literal = if *owning {
                            solver.owning_literal(*other)
                        } else {
                            solver.ref_literal(*other)
                        };
                        (literal, k.clone())
                    })
                    .collect::<Vec<_>>();
                let mut assumptions = vec![force.clone()];
                assumptions.extend(extra.iter().map(|(l, _)| l.clone()));
                let held = check(&assumptions);
                let held_core = core(held, &extra);
                rows.push(format!(
                    "{key}\t{goal}\t{}\t{}\t{hard_core}\t{held_core}",
                    verdict(hard),
                    verdict(held)
                ));
            }
        }
        rows
    })
}

/// How the source of a copy pair is consumed: a call taking the source's value
/// (the source, or a copy or cast of it other than the pair's destination) as an
/// argument. `free` = libc `free` (the `q = p; … free(p)` shape); `local-callee` =
/// a function of the program (W52_RETIRE's local-consumer shape); `other-call`;
/// `no-call`. The first three are ranked in that order.
#[cfg(test)]
fn copy_lend_source_consumer(
    program: &RustProgram<'_>,
    body: &Body<'_>,
    source: Local,
    destination: Local,
) -> &'static str {
    use rustc_middle::mir::TerminatorKind;
    let mut carriers = FxHashSet::from_iter([source]);
    loop {
        let before = carriers.len();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                    continue;
                };
                let rhs = match rvalue {
                    Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs))
                    | Rvalue::Cast(_, Operand::Copy(rhs) | Operand::Move(rhs), _) => rhs,
                    _ => continue,
                };
                if lhs.projection.is_empty()
                    && rhs.projection.is_empty()
                    && lhs.local != destination
                    && carriers.contains(&rhs.local)
                {
                    carriers.insert(lhs.local);
                }
            }
        }
        if carriers.len() == before {
            break;
        }
    }
    let mut rank = 0u8;
    for data in body.basic_blocks.iter() {
        let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
            continue;
        };
        let carries = args.iter().any(|arg| match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => {
                place.projection.is_empty() && carriers.contains(&place.local)
            }
            Operand::Constant(_) => false,
        });
        if !carries {
            continue;
        }
        let here = match func.const_fn_def() {
            Some((def_id, _))
                if def_id
                    .as_local()
                    .is_some_and(|local| program.functions.contains(&local)) =>
            {
                2
            }
            Some((def_id, _)) if program.tcx.item_name(def_id).as_str() == "free" => 3,
            _ => 1,
        };
        rank = rank.max(here);
    }
    match rank {
        3 => "free",
        2 => "local-callee",
        1 => "other-call",
        _ => "no-call",
    }
}

fn construct_bo_into_with_esc(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    solver: &KindSolver,
    mode: CopyLendMode,
    enable_esc_minimal: bool,
) -> anyhow::Result<BoConstruction> {
    crate::phase_log::mark("bc:source_events", "start", "");
    crate::analysis_budget::check("bc:source_events")?;
    let source_events = super::source_events::for_construction(program);
    crate::phase_log::mark("bc:source_events", "end", "");
    #[cfg(test)]
    let source_events = super::wrapper_fault_tests::inventory(source_events);
    super::export::record(|export| export.source_events = Some(source_events.clone()));
    crate::phase_log::mark("bc:record_sites", "start", "");
    crate::analysis_budget::check("bc:record_sites")?;
    super::comparison::record_sites(program, slots);
    crate::phase_log::mark("bc:record_sites", "end", "");
    crate::phase_log::mark("bc:crate_ctxt", "start", "");
    crate::analysis_budget::check("bc:crate_ctxt")?;
    let crate_ctxt = CrateCtxt::new(program);
    crate::phase_log::mark(
        "bc:crate_ctxt",
        "end",
        &format!("functions={}", program.functions.len()),
    );
    crate::phase_log::mark(
        "bc:esc_minimal",
        "start",
        &format!("enabled={enable_esc_minimal}"),
    );
    crate::analysis_budget::check("bc:esc_minimal")?;
    let esc_minimal = if enable_esc_minimal {
        super::esc_minimal::select(program, slots)
    } else {
        super::esc_minimal::EscMinimalSelection::default()
    };
    crate::phase_log::mark("bc:esc_minimal", "end", "");
    crate::phase_log::mark(
        "bc:copy_lend_eligibility",
        "start",
        &format!("mode={mode:?}"),
    );
    crate::analysis_budget::check("bc:copy_lend_eligibility")?;
    #[cfg(test)]
    let t = Instant::now();
    let eligibility = if mode == CopyLendMode::LendArm {
        analyze_copy_lend_eligibility(program, slots, mut_facts, origins.native_flows())
    } else {
        CopyLendEligibility::default()
    };
    crate::phase_log::mark(
        "bc:copy_lend_eligibility",
        "end",
        &format!("pairs={}", eligibility.pairs.len()),
    );
    #[cfg(test)]
    let eligibility_elapsed = t.elapsed();
    crate::phase_log::mark("bc:ownership_constraints", "start", "");
    crate::analysis_budget::check("bc:ownership_constraints")?;
    #[cfg(test)]
    let t = Instant::now();
    let (stats, selectors) = super::source_events::with_inventory(&source_events, || match mode {
        CopyLendMode::LendArm => emit_crate_ownership_constraints_with_copy_lends(
            &crate_ctxt,
            slots,
            origins,
            solver,
            &eligibility.pairs,
        ),
        CopyLendMode::Baseline | CopyLendMode::RemovalOnly => {
            emit_crate_ownership_constraints(&crate_ctxt, slots, origins, solver)
        }
    })?;
    crate::phase_log::mark(
        "bc:ownership_constraints",
        "end",
        &format!(
            "z3_ast_len={} hard_assertions={}",
            stats.z3_ast_len,
            if crate::phase_log::on() {
                solver.hard_assertion_count()
            } else {
                0
            }
        ),
    );
    #[cfg(not(test))]
    let _ = stats;
    #[cfg(test)]
    let emit_elapsed = t.elapsed();
    #[cfg(test)]
    let t = Instant::now();
    if let Some(tracker) = solver.tracker() {
        tracker.set_context("coherence");
    }
    crate::phase_log::mark("bc:coherence", "start", "");
    crate::analysis_budget::check("bc:coherence")?;
    let total = program.functions.len();
    for (index, &fn_did) in program.functions.iter().enumerate() {
        crate::analysis_budget::check("bc:coherence")?;
        let probe = crate::phase_log::Probe::begin();
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        match mode {
            CopyLendMode::Baseline => add_coherence(solver, slots, fn_did, &body),
            CopyLendMode::RemovalOnly => add_coherence_removal_only(solver, slots, fn_did, &body),
            CopyLendMode::LendArm => {
                add_coherence_with_copy_lends(solver, slots, fn_did, &body, &eligibility.pairs)
            }
        }
        crate::phase_log::Probe::end(probe, "bc:coherence", index, total, || {
            format!(
                "{} {}",
                program.tcx.def_path_str(fn_did),
                crate::phase_log::body_size(&body)
            )
        });
    }
    crate::phase_log::mark("bc:coherence", "end", "");
    crate::phase_log::mark("bc:nullability", "start", "");
    crate::analysis_budget::check("bc:nullability")?;
    let mut nullability = super::nullability::analyze(program.tcx, &program.functions, slots);
    crate::phase_log::mark("bc:nullability", "end", "");
    crate::phase_log::mark("bc:field_ref_worthiness", "start", "");
    crate::analysis_budget::check("bc:field_ref_worthiness")?;
    let field_ref_plan = constrain_field_ref_worthiness(
        solver,
        slots,
        program,
        origins.try_native_flows(),
        &nullability,
    );
    crate::phase_log::mark("bc:field_ref_worthiness", "end", "");
    crate::phase_log::mark("bc:array_fields", "start", "");
    crate::analysis_budget::check("bc:array_fields")?;
    let array_fields = super::array_fields::constrain(program, slots, solver, &mut nullability);
    crate::phase_log::mark("bc:array_fields", "end", "");
    super::export::record(|export| export.array_fields = Some(array_fields.clone()));
    #[cfg(test)]
    let coherence_elapsed = t.elapsed();
    crate::phase_log::mark("bc:qualifier_facts", "start", "");
    crate::analysis_budget::check("bc:qualifier_facts")?;
    let qualifier_facts = super::qualifier_facts::collect(program, slots, mut_facts, &nullability);
    crate::phase_log::mark("bc:qualifier_facts", "end", "");
    crate::phase_log::mark("bc:selectors_demand_capture", "start", "");
    crate::analysis_budget::check("bc:selectors_demand_capture")?;
    super::export::record(|export| export.qualifier_facts = Some(qualifier_facts.clone()));
    solver.set_demand_capture(super::demand_evidence::begin_construction(
        program,
        slots,
        selectors.keys(),
    ));
    crate::phase_log::mark(
        "bc:selectors_demand_capture",
        "end",
        &format!(
            "hard_assertions={}",
            if crate::phase_log::on() {
                solver.hard_assertion_count()
            } else {
                0
            }
        ),
    );
    Ok(BoConstruction {
        source_events,
        #[cfg(test)]
        qualifier_facts,
        #[cfg(test)]
        array_fields,
        mode,
        nullability,
        field_ref_plan,
        #[cfg(test)]
        a2_killed_memberships: 0,
        #[cfg(test)]
        a2_opaque_result_guards: 0,
        selectors,
        eligibility,
        esc_minimal,
        #[cfg(test)]
        stats,
        #[cfg(test)]
        eligibility_elapsed,
        #[cfg(test)]
        emit_elapsed,
        #[cfg(test)]
        coherence_elapsed,
    })
}

pub(crate) fn pure_modeled_return_origin(
    origins: &OriginSummaries,
    callee: LocalDefId,
    depth: u8,
) -> bool {
    let summary = &origins[&callee];
    let Some((returned, _)) = summary.slots.iter_enumerated().find(|(_, slot)| {
        slot.place.root == SignatureRoot::Return
            && slot.place.deref_depth == 0
            && slot.place.field.is_none()
            && slot.depth == depth
    }) else {
        return false;
    };
    if summary.unknown.contains(returned) {
        return false;
    }
    summary.subset.rows().any(|source| {
        source != returned
            && !summary.unknown.contains(source)
            && summary.subset.contains(source, returned)
            && !summary.subset.contains(returned, source)
            && matches!(summary.slots[source].place.root, SignatureRoot::Arg(_))
    })
}

fn a16_resolved_slot_ref(fn_did: LocalDefId, slot: ResolvedSlot) -> SlotRef {
    match slot {
        ResolvedSlot::Local(slot) => SlotRef::Local(fn_did, slot),
        ResolvedSlot::Field(slot) => SlotRef::Field(slot),
    }
}

fn add_refined_return_kind_links(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
) -> usize {
    let fresh_slots = collect_malloc_source_slots(program.tcx, &program.functions, slots);
    let opaque_slots = positive_opaque_return_slots(slots, program, origins.native_flows());
    let mut links = 0usize;
    for &caller in &program.functions {
        let body_ref = program
            .tcx
            .mir_drops_elaborated_and_const_checked(caller)
            .borrow();
        let body = &*body_ref;
        for data in body.basic_blocks.iter() {
            let Some(terminator) = data.terminator.as_ref() else {
                continue;
            };
            let Some(call) = terminator.as_call(program.tcx) else {
                continue;
            };
            let CallKind::FreeStanding(callee) = call.func else {
                continue;
            };
            if !matches!(
                program.tcx.hir_node_by_def_id(callee),
                rustc_hir::Node::Item(_)
            ) {
                continue;
            }
            let rustc_middle::mir::TerminatorKind::Call { func, .. } = &terminator.kind else {
                continue;
            };
            let rustc_middle::ty::TyKind::FnDef(direct, _) = func.ty(body, program.tcx).kind()
            else {
                continue;
            };
            if direct.as_local() != Some(callee) {
                continue;
            }
            let depths = ptr_chain_depth(call.destination.ty(body, program.tcx).ty);
            for depth in 0..depths {
                let depth = u8::try_from(depth).expect("return pointer depth exceeds u8");
                if !pure_modeled_return_origin(origins, callee, depth) {
                    continue;
                }
                let Some(destination) =
                    resolve_place(slots, caller, body, call.destination, depth, None)
                else {
                    continue;
                };
                let Some(return_slot) = slots
                    .fn_local_slots
                    .get(&callee)
                    .and_then(|universe| universe.slot_for_local_depth(RETURN_PLACE, depth))
                else {
                    continue;
                };
                let return_slot = SlotRef::Local(callee, return_slot);
                if fresh_slots.contains(&return_slot) || opaque_slots.contains(&return_slot) {
                    continue;
                }
                solver.constrain_origin_return_ref(
                    a16_resolved_slot_ref(caller, destination),
                    return_slot,
                );
                links += 1;
            }
        }
    }
    links
}

/// Accepted return-refinement construction: add one-way links only for
/// modeled-origin returns and report their exact site count.
#[cfg(test)]
pub(crate) fn construct_bo_into_return_refined(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    solver: &KindSolver,
) -> anyhow::Result<(BoConstruction, usize)> {
    construct_bo_into_a16_refined_with_esc(program, slots, origins, mut_facts, solver, true)
}

fn construct_bo_into_a16_refined_with_esc(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    solver: &KindSolver,
    enable_esc_minimal: bool,
) -> anyhow::Result<(BoConstruction, usize)> {
    let construction = if enable_esc_minimal {
        construct_bo_into(
            program,
            slots,
            origins,
            mut_facts,
            solver,
            CopyLendMode::current(),
        )?
    } else {
        construct_bo_overlap_reference(program, slots, origins, mut_facts, solver)?
    };
    let links = add_refined_return_kind_links(program, slots, origins, solver);
    Ok((construction, links))
}

/// Shared construction for the parked tracking harness: baseline mode, with the harness's
/// existing Use-family tracking preserved exactly. No eligibility or lend behavior is reachable.
#[cfg(test)]
pub(crate) fn construct_tracked_census_baseline(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
) -> anyhow::Result<BoConstruction> {
    let source_events = super::source_events::for_construction(program);
    super::export::record(|export| export.source_events = Some(source_events.clone()));
    super::comparison::record_sites(program, slots);
    let crate_ctxt = CrateCtxt::new(program);
    let t = Instant::now();
    let (stats, selectors) = super::source_events::with_inventory(&source_events, || {
        emit_crate_ownership_constraints(&crate_ctxt, slots, origins, solver)
    })?;
    let emit_elapsed = t.elapsed();
    let t = Instant::now();
    solver
        .tracker()
        .expect("tracked census construction")
        .set_context("coherence");
    for &fn_did in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        add_coherence_tagging_uses(solver, slots, fn_did, &body);
    }
    let mut nullability = super::nullability::NullabilityFacts::default();
    let array_fields = super::array_fields::constrain(program, slots, solver, &mut nullability);
    super::export::record(|export| export.array_fields = Some(array_fields.clone()));
    let qualifier_facts =
        super::qualifier_facts::collect_without_mutability(program, slots, &nullability);
    super::export::record(|export| export.qualifier_facts = Some(qualifier_facts.clone()));
    solver.set_demand_capture(super::demand_evidence::begin_construction(
        program,
        slots,
        selectors.keys(),
    ));
    Ok(BoConstruction {
        source_events,
        qualifier_facts,
        array_fields,
        mode: CopyLendMode::Baseline,
        nullability,
        field_ref_plan: FieldRefPlan::default(),
        a2_killed_memberships: 0,
        a2_opaque_result_guards: 0,
        selectors,
        eligibility: CopyLendEligibility::default(),
        esc_minimal: super::esc_minimal::select(program, slots),
        stats,
        eligibility_elapsed: Duration::ZERO,
        emit_elapsed,
        coherence_elapsed: t.elapsed(),
    })
}

#[cfg(test)]
pub(crate) fn construct_bo_into_a2(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    a2: &super::origin_flow::A2Plan,
    mut_facts: &MutFacts,
    solver: &KindSolver,
    copy_lend_mode: CopyLendMode,
) -> anyhow::Result<BoConstruction> {
    let mut construction =
        construct_bo_into(program, slots, origins, mut_facts, solver, copy_lend_mode)?;
    let mut guards = 0usize;
    for guard in &a2.opaque_result_guards {
        let Some(universe) = slots.fn_local_slots.get(&guard.function) else {
            continue;
        };
        let Some(slot) = universe.slot_for_local_depth(guard.local, guard.depth) else {
            continue;
        };
        solver.add_borrow_exclusion(Some(SlotRef::Local(guard.function, slot)), &[]);
        super::raw_cause::note_eager(solver, "opaque-result-guard");
        guards += 1;
    }
    construction.a2_killed_memberships = a2.killed_memberships;
    construction.a2_opaque_result_guards = guards;
    Ok(construction)
}

#[cfg(test)]
pub(crate) fn verify_bo_construction(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
    construction: &BoConstruction,
    mut_facts: &MutFacts,
) -> Option<FxHashMap<SlotRef, SlotKind>> {
    verify_bo_construction_counting(program, slots, origins, solver, construction, mut_facts).0
}

/// Verify a shared construction against an explicitly supplied flow graph. This is reserved for
/// diagnostic constructions that deliberately substitute the origin summaries while replaying the
/// production flow facts; the construction mode still owns emission/coherence selection.
#[cfg(test)]
pub(crate) fn verify_bo_construction_with_flows(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    construction: &BoConstruction,
    mut_facts: &MutFacts,
) -> Option<FxHashMap<SlotRef, SlotKind>> {
    assert_ne!(
        construction.mode,
        CopyLendMode::LendArm,
        "a lend-arm construction must replay the same native flows that produced eligibility"
    );
    super::source_events::with_inventory(&construction.source_events, || {
        verify_to_fixpoint_counting_with_flows(
            program,
            slots,
            origin_flows,
            solver,
            &construction.selectors,
            mut_facts,
        )
        .0
    })
}

fn with_construction_replay<T>(construction: &BoConstruction, f: impl FnOnce() -> T) -> T {
    super::source_events::with_inventory(&construction.source_events, || {
        super::esc_minimal::with_presentations(&construction.esc_minimal, f)
    })
}

pub(crate) fn verify_bo_construction_with_parameter_overlaps(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
    construction: &BoConstruction,
    mut_facts: &MutFacts,
    parameter_overlaps: &FxHashMap<LocalDefId, super::borrow_engine::ParameterOverlap>,
) -> (
    Option<FxHashMap<SlotRef, SlotKind>>,
    super::borrow_verify::RoundStats,
) {
    assert_ne!(
        construction.mode,
        CopyLendMode::RemovalOnly,
        "the parameter-overlap focused replay runs Baseline or the LendArm selector, never RemovalOnly"
    );
    with_construction_replay(construction, || {
        verify_constructed_to_fixpoint(
            program,
            slots,
            origins,
            solver,
            construction,
            mut_facts,
            Some(parameter_overlaps),
        )
    })
}

fn verify_constructed_to_fixpoint(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
    construction: &BoConstruction,
    mut_facts: &MutFacts,
    parameter_overlaps: Option<&FxHashMap<LocalDefId, super::borrow_engine::ParameterOverlap>>,
) -> (
    Option<FxHashMap<SlotRef, SlotKind>>,
    super::borrow_verify::RoundStats,
) {
    #[cfg(test)]
    super::wrapper_fault_tests::verification(slots, solver);
    let copy_lends =
        (construction.mode == CopyLendMode::LendArm).then_some(&construction.eligibility.pairs);
    let result = verify_to_fixpoint_counting_with_flows_impl(
        program,
        slots,
        origins.native_flows(),
        solver,
        &construction.selectors,
        mut_facts,
        copy_lends,
        Some(&construction.esc_minimal.loans),
        parameter_overlaps,
        LoopBackend::HardCheckRoundOptimize,
    );
    #[cfg(test)]
    super::wrapper_fault_tests::verification_result(solver);
    result
}

pub(crate) fn verify_bo_construction_counting(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
    construction: &BoConstruction,
    mut_facts: &MutFacts,
) -> (
    Option<FxHashMap<SlotRef, SlotKind>>,
    super::borrow_verify::RoundStats,
) {
    with_construction_replay(construction, || {
        verify_constructed_to_fixpoint(
            program,
            slots,
            origins,
            solver,
            construction,
            mut_facts,
            None,
        )
    })
}

#[cfg(test)]
#[derive(Clone, Copy)]
pub(crate) enum TestValidationBackend {
    LegacyOptimize,
    HardCheckRoundOptimize,
}

#[cfg(test)]
impl TestValidationBackend {
    fn loop_backend(self) -> LoopBackend {
        match self {
            Self::LegacyOptimize => LoopBackend::LegacyOptimize,
            Self::HardCheckRoundOptimize => LoopBackend::HardCheckRoundOptimize,
        }
    }
}

/// Test-only differential door. Construction remains identical to production;
/// only the selector-check backend is varied after the shared construction has
/// been built.
#[cfg(test)]
pub(crate) fn verify_bo_construction_counting_for_test(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
    construction: &BoConstruction,
    mut_facts: &MutFacts,
    backend: TestValidationBackend,
) -> (
    Option<FxHashMap<SlotRef, SlotKind>>,
    super::borrow_verify::RoundStats,
) {
    let copy_lends =
        (construction.mode == CopyLendMode::LendArm).then_some(&construction.eligibility.pairs);
    with_construction_replay(construction, || {
        verify_to_fixpoint_counting_with_flows_impl(
            program,
            slots,
            origins.native_flows(),
            solver,
            &construction.selectors,
            mut_facts,
            copy_lends,
            Some(&construction.esc_minimal.loans),
            None,
            backend.loop_backend(),
        )
    })
}

/// Guarded-repair twin of `verify_bo_construction_counting_for_test`, owned by the same
/// production construction boundary.
#[cfg(test)]
pub(crate) fn verify_bo_construction_l2_for_test(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
    construction: &BoConstruction,
    mut_facts: &MutFacts,
    backend: TestValidationBackend,
) -> (
    Option<FxHashMap<SlotRef, SlotKind>>,
    super::borrow_verify::RoundStats,
) {
    let copy_lends =
        (construction.mode == CopyLendMode::LendArm).then_some(&construction.eligibility.pairs);
    with_construction_replay(construction, || {
        verify_guarded_to_fixpoint_counting_impl(
            program,
            slots,
            origins.native_flows(),
            solver,
            &construction.selectors,
            mut_facts,
            copy_lends,
            Some(&construction.esc_minimal.loans),
            backend.loop_backend(),
        )
    })
}

/// Solve under `mode` and `attestation`; `None` when the solve declines (its
/// reasons are `solve_bo_overlap_config_reporting`'s).
pub(crate) fn solve_bo_overlap_config(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    mode: OverlapMode,
    attestation: Option<WholeProgramAttestation>,
) -> Option<VerifiedBo> {
    solve_bo_overlap_config_reporting(program, slots, origins, mut_facts, mode, attestation).ok()
}

/// Diagnostic twin of `solve_bo_overlap_config`: identical construction and solve,
/// with a typed reason at every historical pre-ledger `None` exit.
pub(crate) fn solve_bo_overlap_config_reporting(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    mode: OverlapMode,
    attestation: Option<WholeProgramAttestation>,
) -> Result<VerifiedBo, OverlapPreledgerDecline> {
    // Return refinement is part of the precise production semantics. The
    // retained Baseline mode is a diagnostic overlap control, not another
    // production configuration.
    let refined = mode == OverlapMode::PreciseReplay;
    // Complete cache capture is owned here only when no caller already owns
    // it; an existing caller must receive its original recording unchanged.
    let owned_capture = (!super::export::capturing()).then(super::export::arm_scope);
    let (verified, _links) = solve_bo_overlap_config_inner(
        program,
        slots,
        origins,
        mut_facts,
        mode,
        attestation,
        refined,
        true,
    )?;
    let verified = stamp_a16_refined_receipt(verified, refined);
    let captured = if let Some(capture) = owned_capture {
        capture.finish()
    } else {
        super::export::snapshot().expect("active accepted-model capture")
    };
    super::model_cache::prepare(program, slots, origins, &verified, &captured);
    Ok(verified)
}

/// Measurement reference: the overlap and return-refinement production semantics
/// with escaped-loan selection disabled in both the planning baseline and candidate
/// construction. This is the byte-equivalence reference path.
#[cfg(test)]
pub(crate) fn solve_bo_overlap_reference_reporting(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    attestation: Option<WholeProgramAttestation>,
) -> Result<VerifiedBo, OverlapPreledgerDecline> {
    let (verified, _links) = solve_bo_overlap_config_inner(
        program,
        slots,
        origins,
        mut_facts,
        OverlapMode::PreciseReplay,
        attestation,
        true,
        false,
    )?;
    Ok(stamp_a16_refined_receipt(verified, true))
}

fn stamp_a16_refined_receipt(mut verified: VerifiedBo, refined: bool) -> VerifiedBo {
    if refined {
        verified.receipt = verified.receipt.replacen(
            "soundness_mode=a14\n",
            "soundness_mode=a14_a16_refined\n",
            1,
        );
        verified.receipt.push_str(&format!(
            "a16_refined_links={}\n",
            verified.return_refined_links
        ));
    }
    verified
}

/// The overlap solve inside its attested world and model-entry count, with the
/// source events collected once.
fn solve_bo_overlap_config_inner(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    mode: OverlapMode,
    attestation: Option<WholeProgramAttestation>,
    refined: bool,
    enable_esc_minimal: bool,
) -> Result<(VerifiedBo, usize), OverlapPreledgerDecline> {
    let _call_world = super::licensing::stack_entry::enter_world(attestation);
    super::execution_guard::enter_model();
    crate::phase_log::mark("solve:source_events", "start", "");
    let inventory = std::sync::Arc::new(super::source_events::collect(program));
    crate::phase_log::mark("solve:source_events", "end", "");
    super::source_events::with_inventory(&inventory, || {
        solve_bo_overlap_config_with_source_events(
            program,
            slots,
            origins,
            mut_facts,
            mode,
            attestation,
            refined,
            enable_esc_minimal,
        )
    })
}

/// The overlap solve itself: the baseline solve, the overlap plan, then the
/// precise solve or its refined fallback.
fn solve_bo_overlap_config_with_source_events(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    mode: OverlapMode,
    attestation: Option<WholeProgramAttestation>,
    refined: bool,
    enable_esc_minimal: bool,
) -> Result<(VerifiedBo, usize), OverlapPreledgerDecline> {
    // The overlap solve runs LendArm, or Baseline under a test's override;
    // RemovalOnly is a measurement mode and never reaches this solve.
    assert_ne!(
        CopyLendMode::current(),
        CopyLendMode::RemovalOnly,
        "the overlap solve runs the baseline or the lend-arm copy-lend mode, never removal-only"
    );
    // The index-range table (relay era-5c/267): model-independent, built once
    // for the whole solve; every replay below reads it, and the copy
    // relaxation's call arm asks it which formals a callee keeps (relay
    // era-5c/269), so it is built first.
    crate::phase_log::mark("solve:index_ranges", "start", "");
    let _index_ranges = super::index_ranges::ensure(program);
    crate::phase_log::mark("solve:index_ranges", "end", "");
    // The copies the depth-0 relaxation may take, for this solve.
    crate::phase_log::mark("solve:copy_relax", "start", "");
    let (eligible, multi_views) = analyze_copy_relax_sites(program, slots, origins.native_flows());
    crate::phase_log::mark("solve:copy_relax", "end", "");
    super::export::record_multi_views(multi_views);
    super::copy_relax::install(eligible);

    let baseline_solver = KindSolver::new(slots);
    crate::phase_log::mark("solve:baseline_construction", "start", "");
    let baseline_construction =
        construct_bo_overlap_reference(program, slots, origins, mut_facts, &baseline_solver)
            .map_err(|error| {
                OverlapPreledgerDecline::from_error(
                    OverlapPreledgerDeclineReason::BaselineConstruction,
                    error,
                )
            })?;
    crate::phase_log::mark("solve:baseline_construction", "end", "");
    crate::phase_log::mark("solve:baseline_verify", "start", "");
    // Relay main/388 walls 3+4 (R1363-1): the verify's `verify:<sub>` / `z3:<sub>` marks, here only.
    let (baseline_model, baseline_round_stats) = crate::phase_log::with_sub_marks(|| {
        verify_bo_construction_counting(
            program,
            slots,
            origins,
            &baseline_solver,
            &baseline_construction,
            mut_facts,
        )
    });
    crate::phase_log::mark(
        "solve:baseline_verify",
        "end",
        &format!("rounds={}", baseline_round_stats.rounds),
    );
    let baseline_model = baseline_model.ok_or_else(|| {
        let first = baseline_solver
            .round_model_failure()
            .map(|failure| failure.summary())
            .unwrap_or_else(|| if baseline_round_stats.source_retirement_decline.is_empty() {
                "untyped-round-decline".to_owned()
            } else {
                "source-retirement-coverage".to_owned()
            });
        OverlapPreledgerDecline::with_detail(
            OverlapPreledgerDeclineReason::BaselineVerification,
            format!(
                "expected=accepted-model got={first} rounds={} commits={} selected_copy_lends={} dropped_sources={} dropped_sinks={} field_conflict={:?} field_kind={:?} cap_exhausted={} l2_decline={:?} source_retirement={:?}{}",
                baseline_round_stats.rounds,
                baseline_round_stats.commits_conflict,
                baseline_round_stats.copy_lend_replay_selections,
                baseline_round_stats.dropped_sources,
                baseline_round_stats.dropped_sinks,
                baseline_round_stats.field_conflict_decline,
                baseline_round_stats.field_conflict_kind,
                baseline_round_stats.cap_exhausted,
                baseline_round_stats.guarded_decline,
                baseline_round_stats.source_retirement_decline,
                incumbent_keys(&[&baseline_round_stats])
                    .lines()
                    .map(|line| format!(" {line}"))
                    .collect::<String>(),
            ),
        )
    })?;
    let baseline_nullability = nullability_artifacts(&baseline_construction);
    let baseline_a14 = opacity_artifacts(&baseline_construction);
    if mode == OverlapMode::Baseline {
        let plan = if attestation == Some(WholeProgramAttestation::FrozenBenchmarkGraph) {
            OverlapPlan::baseline_attested()
        } else {
            OverlapPlan::baseline()
        };
        let selected_model_sha256 = model_digest(&baseline_model);
        return Ok((
            VerifiedBo {
                receipt: repair_keys(
                    &[&baseline_round_stats],
                    overlap_receipt(
                        mode,
                        &plan,
                        0,
                        0,
                        &selected_model_sha256,
                        &baseline_nullability,
                        &baseline_a14,
                    ),
                ),
                #[cfg(test)]
                mark_artifact: overlap_mark_artifact(
                    mode,
                    &plan,
                    &BTreeSet::new(),
                    &selected_model_sha256,
                ),
                #[cfg(test)]
                site_artifact: overlap_site_artifact(mode, &plan),
                #[cfg(test)]
                nullable_artifact: baseline_nullability.artifact.clone(),
                #[cfg(test)]
                field_ref_artifact: baseline_a14.artifact.clone(),
                #[cfg(test)]
                summary_artifact: plan.summary_artifact.clone(),
                baseline_model: baseline_model.clone(),
                model: baseline_model,
                #[cfg(test)]
                retained_copy_marks: BTreeSet::new(),
                retained_copy_plans: Vec::new(),
                #[cfg(test)]
                round_stats: baseline_round_stats,
                #[cfg(test)]
                esc_minimal: baseline_construction.esc_minimal.clone(),
                #[cfg(test)]
                selector_sources: baseline_construction.selectors.sources().len(),
                #[cfg(test)]
                selector_sinks: baseline_construction.selectors.sinks().len(),
                #[cfg(test)]
                emission_stats: baseline_construction.stats,
                #[cfg(test)]
                construction_emit_elapsed: baseline_construction.emit_elapsed,
                #[cfg(test)]
                construction_coherence_elapsed: baseline_construction.coherence_elapsed,
                #[cfg(test)]
                check_sat_count: baseline_solver.check_sat_count(),
                #[cfg(test)]
                hard_check_count: baseline_solver.hard_check_count(),
                #[cfg(test)]
                optimize_materialization_count: baseline_solver.optimize_materialization_count(),
                #[cfg(test)]
                lazy_plain_hard_check_count: baseline_solver.lazy_plain_hard_check_count(),
                #[cfg(test)]
                lazy_tracked_recheck_count: baseline_solver.lazy_tracked_recheck_count(),
                #[cfg(test)]
                lazy_plain_materialization_count: baseline_solver
                    .lazy_plain_materialization_count(),
                #[cfg(test)]
                hard_check_elapsed: baseline_solver.hard_check_elapsed(),
                #[cfg(test)]
                optimize_materialization_elapsed: baseline_solver
                    .optimize_materialization_elapsed(),
                return_refined_links: 0,
                #[cfg(test)]
                planned_copy_marks: BTreeSet::new(),
                #[cfg(test)]
                producer_stats: plan.stats,
            },
            0,
        ));
    }

    crate::phase_log::mark("solve:overlap_plan", "start", "");
    crate::analysis_budget::check("solve:overlap_plan").map_err(|error| {
        OverlapPreledgerDecline::from_error(
            OverlapPreledgerDeclineReason::OverlapPlanProduction,
            error,
        )
    })?;
    let plan = produce_overlap_plan(
        program,
        slots,
        origins.native_flows(),
        mut_facts,
        &baseline_model,
        mode,
        attestation,
    )
    .map_err(|error| {
        OverlapPreledgerDecline::from_error(
            OverlapPreledgerDeclineReason::OverlapPlanProduction,
            error,
        )
    })?;
    crate::phase_log::mark("solve:overlap_plan", "end", "");
    if matches!(plan.abi_guard, AbiGuardDisposition::Refused { .. }) {
        if refined {
            // Refusing overlap promotion must not also disable the independently
            // applied return-refinement constraint. Product/unattested mode keeps
            // the overlap guard's fallback while applying the same one-way return
            // rule as the attested production path.
            let solver = KindSolver::new(slots);
            let (construction, refined_links) = construct_bo_into_a16_refined_with_esc(
                program,
                slots,
                origins,
                mut_facts,
                &solver,
                enable_esc_minimal,
            )
            .map_err(|error| {
                OverlapPreledgerDecline::from_error(
                    OverlapPreledgerDeclineReason::RefinedFallbackConstruction,
                    error,
                )
            })?;
            let (model, round_stats) = verify_bo_construction_counting(
                program,
                slots,
                origins,
                &solver,
                &construction,
                mut_facts,
            );
            let model = model.ok_or_else(|| {
                OverlapPreledgerDecline::at(
                    OverlapPreledgerDeclineReason::RefinedFallbackVerification,
                )
            })?;
            let selected_model_sha256 = model_digest(&model);
            let nullability = nullability_artifacts(&construction);
            let opacity = opacity_artifacts(&construction);
            return Ok((
                VerifiedBo {
                    receipt: repair_keys(
                        &[&baseline_round_stats, &round_stats],
                        overlap_receipt(
                            mode,
                            &plan,
                            0,
                            0,
                            &selected_model_sha256,
                            &nullability,
                            &opacity,
                        ),
                    ),
                    #[cfg(test)]
                    mark_artifact: overlap_mark_artifact(
                        mode,
                        &plan,
                        &BTreeSet::new(),
                        &selected_model_sha256,
                    ),
                    #[cfg(test)]
                    site_artifact: overlap_site_artifact(mode, &plan),
                    #[cfg(test)]
                    nullable_artifact: nullability.artifact,
                    #[cfg(test)]
                    field_ref_artifact: opacity.artifact,
                    #[cfg(test)]
                    summary_artifact: plan.summary_artifact.clone(),
                    baseline_model,
                    model,
                    #[cfg(test)]
                    retained_copy_marks: BTreeSet::new(),
                    retained_copy_plans: Vec::new(),
                    #[cfg(test)]
                    round_stats,
                    #[cfg(test)]
                    esc_minimal: construction.esc_minimal.clone(),
                    #[cfg(test)]
                    selector_sources: construction.selectors.sources().len(),
                    #[cfg(test)]
                    selector_sinks: construction.selectors.sinks().len(),
                    #[cfg(test)]
                    emission_stats: construction.stats,
                    #[cfg(test)]
                    construction_emit_elapsed: construction.emit_elapsed,
                    #[cfg(test)]
                    construction_coherence_elapsed: construction.coherence_elapsed,
                    #[cfg(test)]
                    check_sat_count: solver.check_sat_count(),
                    #[cfg(test)]
                    hard_check_count: solver.hard_check_count(),
                    #[cfg(test)]
                    optimize_materialization_count: solver.optimize_materialization_count(),
                    #[cfg(test)]
                    lazy_plain_hard_check_count: solver.lazy_plain_hard_check_count(),
                    #[cfg(test)]
                    lazy_tracked_recheck_count: solver.lazy_tracked_recheck_count(),
                    #[cfg(test)]
                    lazy_plain_materialization_count: solver.lazy_plain_materialization_count(),
                    #[cfg(test)]
                    hard_check_elapsed: solver.hard_check_elapsed(),
                    #[cfg(test)]
                    optimize_materialization_elapsed: solver.optimize_materialization_elapsed(),
                    return_refined_links: refined_links,
                    #[cfg(test)]
                    planned_copy_marks: plan
                        .planned_marks
                        .iter()
                        .map(|mark| mark.key.clone())
                        .collect(),
                    #[cfg(test)]
                    producer_stats: plan.stats,
                },
                refined_links,
            ));
        }
        let selected_model_sha256 = model_digest(&baseline_model);
        return Ok((
            VerifiedBo {
                receipt: repair_keys(
                    &[&baseline_round_stats],
                    overlap_receipt(
                        mode,
                        &plan,
                        0,
                        0,
                        &selected_model_sha256,
                        &baseline_nullability,
                        &baseline_a14,
                    ),
                ),
                #[cfg(test)]
                mark_artifact: overlap_mark_artifact(
                    mode,
                    &plan,
                    &BTreeSet::new(),
                    &selected_model_sha256,
                ),
                #[cfg(test)]
                site_artifact: overlap_site_artifact(mode, &plan),
                #[cfg(test)]
                nullable_artifact: baseline_nullability.artifact.clone(),
                #[cfg(test)]
                field_ref_artifact: baseline_a14.artifact.clone(),
                #[cfg(test)]
                summary_artifact: plan.summary_artifact.clone(),
                baseline_model: baseline_model.clone(),
                model: baseline_model,
                #[cfg(test)]
                retained_copy_marks: BTreeSet::new(),
                retained_copy_plans: Vec::new(),
                #[cfg(test)]
                round_stats: baseline_round_stats,
                #[cfg(test)]
                esc_minimal: baseline_construction.esc_minimal.clone(),
                #[cfg(test)]
                selector_sources: baseline_construction.selectors.sources().len(),
                #[cfg(test)]
                selector_sinks: baseline_construction.selectors.sinks().len(),
                #[cfg(test)]
                emission_stats: baseline_construction.stats,
                #[cfg(test)]
                construction_emit_elapsed: baseline_construction.emit_elapsed,
                #[cfg(test)]
                construction_coherence_elapsed: baseline_construction.coherence_elapsed,
                #[cfg(test)]
                check_sat_count: baseline_solver.check_sat_count(),
                #[cfg(test)]
                hard_check_count: baseline_solver.hard_check_count(),
                #[cfg(test)]
                optimize_materialization_count: baseline_solver.optimize_materialization_count(),
                #[cfg(test)]
                lazy_plain_hard_check_count: baseline_solver.lazy_plain_hard_check_count(),
                #[cfg(test)]
                lazy_tracked_recheck_count: baseline_solver.lazy_tracked_recheck_count(),
                #[cfg(test)]
                lazy_plain_materialization_count: baseline_solver
                    .lazy_plain_materialization_count(),
                #[cfg(test)]
                hard_check_elapsed: baseline_solver.hard_check_elapsed(),
                #[cfg(test)]
                optimize_materialization_elapsed: baseline_solver
                    .optimize_materialization_elapsed(),
                return_refined_links: 0,
                #[cfg(test)]
                planned_copy_marks: plan
                    .planned_marks
                    .iter()
                    .map(|mark| mark.key.clone())
                    .collect(),
                #[cfg(test)]
                producer_stats: plan.stats,
            },
            0,
        ));
    }

    let solver = KindSolver::new(slots);
    crate::phase_log::mark("solve:precise_construction", "start", "");
    let (construction, refined_links) = if refined {
        construct_bo_into_a16_refined_with_esc(
            program,
            slots,
            origins,
            mut_facts,
            &solver,
            enable_esc_minimal,
        )
        .map_err(|error| {
            OverlapPreledgerDecline::from_error(
                OverlapPreledgerDeclineReason::PreciseConstruction,
                error,
            )
        })?
    } else {
        (
            if enable_esc_minimal {
                construct_bo_into(
                    program,
                    slots,
                    origins,
                    mut_facts,
                    &solver,
                    CopyLendMode::Baseline,
                )
            } else {
                construct_bo_overlap_reference(program, slots, origins, mut_facts, &solver)
            }
            .map_err(|error| {
                OverlapPreledgerDecline::from_error(
                    OverlapPreledgerDeclineReason::CoarseConstruction,
                    error,
                )
            })?,
            0,
        )
    };
    crate::phase_log::mark("solve:precise_construction", "end", "");
    let (model, round_stats) = match mode {
        OverlapMode::Baseline => unreachable!(),
        OverlapMode::PreciseReplay => {
            crate::phase_log::mark("solve:precise_verify", "start", "");
            let (model, stats) = verify_bo_construction_with_parameter_overlaps(
                program,
                slots,
                origins,
                &solver,
                &construction,
                mut_facts,
                &plan.effective_overlaps,
            );
            crate::phase_log::mark(
                "solve:precise_verify",
                "end",
                &format!("rounds={}", stats.rounds),
            );
            // The verification loop has seven `None` exits, each recorded in
            // `RoundStats`; without the detail a decline could not say which one
            // fired. Carry the cause in the decline's detail.
            let detail = precise_verification_cause(&stats);
            (
                model.ok_or_else(|| {
                    OverlapPreledgerDecline::with_detail(
                        OverlapPreledgerDeclineReason::PreciseVerification,
                        detail,
                    )
                })?,
                stats,
            )
        }
        OverlapMode::CoarseConstraint => {
            apply_coarse_constraints(mode, &solver, plan.coarse_pairs.iter().copied());
            let (model, stats) = verify_bo_construction_counting(
                program,
                slots,
                origins,
                &solver,
                &construction,
                mut_facts,
            );
            (
                model.ok_or_else(|| {
                    OverlapPreledgerDecline::at(OverlapPreledgerDeclineReason::CoarseVerification)
                })?,
                stats,
            )
        }
    };
    let retained_copy_marks = if mode == OverlapMode::PreciseReplay {
        plan.retained_marks(&model)
    } else {
        BTreeSet::new()
    };
    let retained_copy_plans = if mode == OverlapMode::PreciseReplay {
        plan.retained_mark_plans(&model)
    } else {
        Vec::new()
    };
    let selected_model_sha256 = model_digest(&model);
    let nullability = nullability_artifacts(&construction);
    let opacity = opacity_artifacts(&construction);
    Ok((
        VerifiedBo {
            receipt: repair_keys(
                &[&baseline_round_stats, &round_stats],
                overlap_receipt(
                    mode,
                    &plan,
                    retained_copy_marks.len(),
                    retained_copy_plans.len(),
                    &selected_model_sha256,
                    &nullability,
                    &opacity,
                ),
            ),
            #[cfg(test)]
            mark_artifact: overlap_mark_artifact(
                mode,
                &plan,
                &retained_copy_marks,
                &selected_model_sha256,
            ),
            #[cfg(test)]
            site_artifact: overlap_site_artifact(mode, &plan),
            #[cfg(test)]
            nullable_artifact: nullability.artifact,
            #[cfg(test)]
            field_ref_artifact: opacity.artifact,
            #[cfg(test)]
            summary_artifact: plan.summary_artifact.clone(),
            model,
            baseline_model,
            #[cfg(test)]
            retained_copy_marks,
            retained_copy_plans,
            #[cfg(test)]
            round_stats,
            #[cfg(test)]
            esc_minimal: construction.esc_minimal.clone(),
            #[cfg(test)]
            selector_sources: construction.selectors.sources().len(),
            #[cfg(test)]
            selector_sinks: construction.selectors.sinks().len(),
            #[cfg(test)]
            emission_stats: construction.stats,
            #[cfg(test)]
            construction_emit_elapsed: construction.emit_elapsed,
            #[cfg(test)]
            construction_coherence_elapsed: construction.coherence_elapsed,
            #[cfg(test)]
            check_sat_count: solver.check_sat_count(),
            #[cfg(test)]
            hard_check_count: solver.hard_check_count(),
            #[cfg(test)]
            optimize_materialization_count: solver.optimize_materialization_count(),
            #[cfg(test)]
            lazy_plain_hard_check_count: solver.lazy_plain_hard_check_count(),
            #[cfg(test)]
            lazy_tracked_recheck_count: solver.lazy_tracked_recheck_count(),
            #[cfg(test)]
            lazy_plain_materialization_count: solver.lazy_plain_materialization_count(),
            #[cfg(test)]
            hard_check_elapsed: solver.hard_check_elapsed(),
            #[cfg(test)]
            optimize_materialization_elapsed: solver.optimize_materialization_elapsed(),
            return_refined_links: refined_links,
            #[cfg(test)]
            planned_copy_marks: plan
                .planned_marks
                .iter()
                .map(|mark| mark.key.clone())
                .collect(),
            #[cfg(test)]
            producer_stats: plan.stats,
        },
        refined_links,
    ))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CopyLendSite {
    pub(crate) fn_did: LocalDefId,
    pub(crate) location: MirLocationKey,
    pub(crate) lhs: SlotRef,
    pub(crate) rhs: SlotRef,
    pub(crate) lhs_local: Local,
    pub(crate) rhs_local: Local,
}

impl CopyLendSite {
    fn sort_key(self) -> (u32, MirLocationKey, SlotKey, SlotKey) {
        (
            self.fn_did.local_def_index.as_u32(),
            self.location,
            SlotKey::of(self.lhs),
            SlotKey::of(self.rhs),
        )
    }
}

pub(crate) fn analyze_copy_lend_eligibility(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    mut_facts: &MutFacts,
    origin_flows: &OriginFlowResults,
) -> CopyLendEligibility {
    let mut eligible = CopyLendEligibility::default();
    for candidate in analyze_copy_lend_candidates(program, slots, mut_facts, origin_flows) {
        if candidate.drop.is_none() {
            eligible.pairs.insert(candidate.pair);
            eligible.sites.extend(candidate.sites);
        }
    }
    eligible.sites.sort_by_key(|site| site.sort_key());
    eligible
}

/// The copies the depth-0 relaxation may take. A bare copy `q = p` between locals is eligible
/// only when the destination's value never leaves the function: no store into a field, an
/// aggregate or an unresolved place, no return, no call argument but one whose formal the callee
/// provably never keeps (relay era-5c/269, `copy_relax_escape`) and no release over the
/// destination's depth-0 value-flow closure (the copy-lend arm's C3 and its free-destination
/// rule, on the destination alone). Under Tree Borrows the raw copy carries its source's tag,
/// and the merge liveness keeps the source's loans live only through the copy's uses in this
/// function and the calls it is lent to. With the sites, the `multi-view` rows of the calls an
/// admitted copy reaches (`copy_relax`'s module doc).
pub(crate) fn analyze_copy_relax_sites(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
) -> (
    FxHashMap<LocalDefId, FxHashSet<MirLocationKey>>,
    Vec<super::copy_relax::MultiView>,
) {
    let mut eligible: FxHashMap<LocalDefId, FxHashSet<MirLocationKey>> = FxHashMap::default();
    let mut multi_views = Vec::new();
    for &fn_did in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        let sites = collect_copy_sites(slots, fn_did, &body);
        if sites.is_empty() {
            continue;
        }
        let flows = origin_flows
            .get(&fn_did)
            .unwrap_or_else(|| panic!("missing origin flow for {fn_did:?}"));
        let value_flows = flows.body.depth0_value_flows();
        // By subject, the closures of its admitted copies (relay era-5c/269).
        let mut admitted: FxHashMap<Local, FxHashSet<SlotOwner>> = FxHashMap::default();
        for site in sites {
            let closure = copy_relax_closure(
                program.tcx,
                &body,
                owner_closure([SlotOwner::Local(site.lhs_local)], &value_flows),
            );
            let drop = if closure
                .iter()
                .any(|owner| matches!(owner, SlotOwner::Field(_)))
            {
                Some(CopyLendEligibilityDrop::C3FieldInClosure)
            } else if destination_flows_to_deallocator(program.tcx, &body, &closure) {
                Some(CopyLendEligibilityDrop::FreeDestination)
            } else {
                copy_relax_escape(program, slots, fn_did, &body, &closure)
            };
            if drop.is_none() {
                eligible.entry(fn_did).or_default().insert(site.location);
                admitted.entry(site.rhs_local).or_default().extend(closure);
            }
        }
        multi_views.extend(copy_relax_multi_views(
            program.tcx,
            &body,
            fn_did,
            &admitted,
        ));
    }
    (eligible, multi_views)
}

/// Relay era-5c/269 §1.3: the calls an admitted copy of a subject reaches as an argument where
/// two or more arguments are views of that subject (`copy_relax_views`), one row per (subject,
/// call).
fn copy_relax_multi_views<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
    fn_did: LocalDefId,
    admitted: &FxHashMap<Local, FxHashSet<SlotOwner>>,
) -> Vec<super::copy_relax::MultiView> {
    let argument = |operand: &Operand<'tcx>| {
        operand
            .place()
            .filter(|place| place.projection.is_empty())
            .map(|place| place.local)
    };
    let mut subjects: Vec<Local> = admitted.keys().copied().collect();
    subjects.sort();
    let mut rows = Vec::new();
    for subject in subjects {
        let reached = &admitted[&subject];
        let mut views: Option<FxHashSet<Local>> = None;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let Some(terminator) = data.terminator.as_ref() else {
                continue;
            };
            let Some(call) = terminator.as_call(tcx) else {
                continue;
            };
            if !call.args.iter().any(|arg| {
                argument(&arg.node).is_some_and(|local| reached.contains(&SlotOwner::Local(local)))
            }) {
                continue;
            }
            let views = views.get_or_insert_with(|| copy_relax_views(tcx, body, subject));
            let arguments: Vec<u32> = call
                .args
                .iter()
                .enumerate()
                .filter(|(_, arg)| argument(&arg.node).is_some_and(|local| views.contains(&local)))
                .map(|(j, _)| j as u32)
                .collect();
            if arguments.len() >= 2 {
                rows.push(super::copy_relax::MultiView {
                    function: fn_did,
                    subject,
                    call: Location {
                        block,
                        statement_index: data.statements.len(),
                    },
                    arguments,
                });
            }
        }
    }
    rows
}

/// The views of `subject`'s bytes in `body` (relay era-5c/269 §1.3): the subject and, to a
/// fixpoint, every local assigned a copy or a cast of a view, an address under one
/// (`&(*v).f`, `&raw (*v)[i]`, no further dereference), the pointer a core call returns on one
/// (a step, `wrapping_add`, slice `as_ptr` / `as_mut_ptr`; over-approximated: any core call
/// with a view first and a pointer result), or the destination `memcpy` / `memmove` /
/// `memset` return when one is their first argument. A pointer loaded through a view and the address of a
/// view's own storage are not views.
fn copy_relax_views<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
    subject: Local,
) -> FxHashSet<Local> {
    let mut views: FxHashSet<Local> = [subject].into_iter().collect();
    let whole = |operand: &Operand<'tcx>, views: &FxHashSet<Local>| {
        operand
            .place()
            .is_some_and(|place| place.projection.is_empty() && views.contains(&place.local))
    };
    loop {
        let mut changed = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                    continue;
                };
                let Some(dest) = lhs.as_local() else {
                    continue;
                };
                if !rvalue.ty(body, tcx).is_any_ptr() {
                    continue;
                }
                let view = match rvalue {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => whole(operand, &views),
                    Rvalue::CopyForDeref(place) => {
                        place.projection.is_empty() && views.contains(&place.local)
                    }
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        place.projection.first() == Some(&ProjectionElem::Deref)
                            && !place.projection[1..].contains(&ProjectionElem::Deref)
                            && views.contains(&place.local)
                    }
                    _ => false,
                };
                if view {
                    changed |= views.insert(dest);
                }
            }
            if let Some(terminator) = data.terminator.as_ref()
                && let Some(call) = terminator.as_call(tcx)
                && let Some(dest) = call.destination.as_local()
                && call
                    .args
                    .first()
                    .is_some_and(|arg| whole(&arg.node, &views))
                && ((matches!(call.func, CallKind::RustLib(_))
                    && body.local_decls[dest].ty.is_any_ptr())
                    || super::index_ranges::libc_row(&call.func)
                        .is_some_and(|(written, _, _)| written == 0))
            {
                changed |= views.insert(dest);
            }
        }
        if !changed {
            return views;
        }
    }
}

/// The relaxation's closure: the destination's value flows, plus every local assigned a
/// pointer computed from a member (a copy, a cast, an address of a member's place), the
/// result of a core pointer method called on one and (relay era-5c/269) the destination
/// `memcpy` / `memmove` / `memset` return when one is their first argument, to a fixpoint.
fn copy_relax_closure<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
    mut closure: FxHashSet<SlotOwner>,
) -> FxHashSet<SlotOwner> {
    loop {
        let mut changed = false;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                    continue;
                };
                let location = Location {
                    block,
                    statement_index,
                };
                if lhs.projection.is_empty()
                    && rvalue.ty(body, tcx).is_any_ptr()
                    && rvalue_mentions_closure(rvalue, location, &closure)
                {
                    changed |= closure.insert(SlotOwner::Local(lhs.local));
                }
            }
            if let Some(terminator) = data.terminator.as_ref()
                && let Some(call) = terminator.as_call(tcx)
                && call.destination.projection.is_empty()
                && call.args.iter().enumerate().any(|(j, arg)| {
                    arg.node
                        .place()
                        .is_some_and(|place| closure.contains(&SlotOwner::Local(place.local)))
                        && (matches!(call.func, CallKind::RustLib(_))
                            || super::index_ranges::libc_row(&call.func)
                                .is_some_and(|(written, _, _)| j == written))
                })
            {
                changed |= closure.insert(SlotOwner::Local(call.destination.local));
            }
        }
        if !changed {
            return closure;
        }
    }
}

/// Whether a member of the relaxation's closure leaves the function, wherever it is live: a store
/// into memory (a field, an aggregate, through a pointer, an unresolved place), a return, or an
/// argument of any call but a core pointer method, a local callee's formal it provably never
/// retains or a libc row's while no member's own storage is addressed (relay era-5c/269).
fn copy_relax_escape<'tcx>(
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    closure: &FxHashSet<SlotOwner>,
) -> Option<CopyLendEligibilityDrop> {
    // A copy INTO the return place (`_0 = p`, a `return p` in the source) escapes by its
    // destination itself.
    if closure.contains(&SlotOwner::Local(RETURN_PLACE)) {
        return Some(CopyLendEligibilityDrop::C3Return);
    }
    // Relay era-5c/269: is the storage of a member itself addressed (`&x`, `&raw const x`)?
    // And was a member lent to a call through the arm below?
    let mut lent = false;
    let addressed = body.basic_blocks.iter().any(|data| {
        data.statements.iter().any(|statement| {
            matches!(
                &statement.kind,
                StatementKind::Assign(box (_, Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)))
                    if closure.contains(&SlotOwner::Local(place.local))
                        && place.projection.first() != Some(&ProjectionElem::Deref)
            )
        })
    });
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                continue;
            };
            if !rvalue.ty(body, program.tcx).is_any_ptr()
                && !matches!(rvalue, Rvalue::Aggregate(..))
            {
                continue;
            }
            if !rvalue_mentions_closure(rvalue, location, closure) {
                continue;
            }
            if matches!(rvalue, Rvalue::Aggregate(..)) {
                return Some(CopyLendEligibilityDrop::C3AggregateStore);
            }
            if lhs
                .projection
                .iter()
                .any(|projection| matches!(projection, ProjectionElem::Field(..)))
            {
                return Some(CopyLendEligibilityDrop::C3FieldStore);
            }
            if lhs.local == RETURN_PLACE {
                return Some(CopyLendEligibilityDrop::C3Return);
            }
            if !lhs.projection.is_empty() {
                return Some(CopyLendEligibilityDrop::C3UnresolvedStore);
            }
            match resolve_place(slots, fn_did, body, *lhs, 0, None) {
                Some(ResolvedSlot::Local(_)) => {}
                Some(ResolvedSlot::Field(_)) => {
                    return Some(CopyLendEligibilityDrop::C3FieldStore);
                }
                None => return Some(CopyLendEligibilityDrop::C3UnresolvedStore),
            }
        }
        let Some(terminator) = data.terminator.as_ref() else {
            continue;
        };
        let Some(call) = terminator.as_call(program.tcx) else {
            continue;
        };
        if matches!(call.func, CallKind::RustLib(_)) {
            continue;
        }
        // Relay era-5c/269: an argument whose formal the callee provably never retains lets
        // nothing out (`index_ranges::never_retained`, fail closed: a recursive, foreign or
        // pointer callee, an incomplete summary, a formal handed on to a callee that may
        // retain it); `memcpy` / `memmove` / `memset` retain nothing and return their
        // destination, which the closure then follows. Not while a member's own storage is
        // addressed: the closure holds `&x` too, and a callee copying bytes out of it
        // (`memcpy(&g, &x, n)`) carries the copy's value out (the review's blocker).
        let kept = |j: usize, place: Place<'_>| {
            !addressed
                && place.projection.is_empty()
                && match &call.func {
                    CallKind::FreeStanding(callee) | CallKind::Impl(callee) => {
                        super::index_ranges::never_retained(*callee, j as u32)
                    }
                    CallKind::LibC(_) => super::index_ranges::libc_row(&call.func).is_some_and(
                        |(written, read, _)| {
                            (j == written && call.destination.projection.is_empty())
                                || Some(j) == read
                        },
                    ),
                    _ => false,
                }
        };
        let mut members = call.args.iter().enumerate().filter(|(_, arg)| {
            arg.node
                .place()
                .is_some_and(|place| closure.contains(&SlotOwner::Local(place.local)))
        });
        if members
            .clone()
            .any(|(j, arg)| !kept(j, arg.node.place().unwrap()))
        {
            return Some(match call.func {
                CallKind::FreeStanding(_) | CallKind::Impl(_) => {
                    CopyLendEligibilityDrop::C3OrdinaryCall
                }
                _ => CopyLendEligibilityDrop::C3OutwardUnknownCall,
            });
        }
        lent |= members.next().is_some();
    }
    // Relay era-5c/269, the second review: a copy lent through the call arm is admitted only
    // when nothing else lets its value out behind the summaries' back. The relaxation's escape
    // takes every core call and every non-pointer rvalue as staying in the function; a copy
    // that reaches no call keeps that rule (S39's), one lent to a call does not.
    if lent && copy_relax_lent_escape(program.tcx, body, closure) {
        return Some(CopyLendEligibilityDrop::C3OutwardUnknownCall);
    }
    None
}

/// Relay era-5c/269, the second review: does a member of a lent copy's closure reach a core
/// call other than a pointer step, slice `as_ptr` / `as_mut_ptr` or `is_null`
/// (`ptr::write_volatile(&raw mut g, x)`, C2Rust's volatile store), or a cast to a non-pointer
/// (`x as usize`, a transmute)?
fn copy_relax_lent_escape<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
    closure: &FxHashSet<SlotOwner>,
) -> bool {
    let member = |place: Place<'tcx>| closure.contains(&SlotOwner::Local(place.local));
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            if let StatementKind::Assign(box (_, Rvalue::Cast(_, operand, ty))) = &statement.kind
                && !ty.is_any_ptr()
                && operand.place().is_some_and(member)
            {
                return true;
            }
        }
        if let Some(terminator) = data.terminator.as_ref()
            && let rustc_middle::mir::TerminatorKind::Call { func, .. } = &terminator.kind
            && let Some(call) = terminator.as_call(tcx)
            && matches!(call.func, CallKind::RustLib(_))
            && call
                .args
                .iter()
                .any(|arg| arg.node.place().is_some_and(member))
            && super::index_ranges::core_pointer_step(tcx, &call.func).is_none()
            && !super::index_ranges::core_slice_buffer(tcx, body, func)
            && !super::index_ranges::core_is_null(tcx, &call.func)
        {
            return true;
        }
    }
    false
}

pub(crate) fn analyze_copy_lend_candidates(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    mut_facts: &MutFacts,
    origin_flows: &OriginFlowResults,
) -> Vec<CopyLendPairCandidate> {
    let mut answer = Vec::new();
    for &fn_did in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        let candidates = collect_copy_sites(slots, fn_did, &body);
        if candidates.is_empty() {
            continue;
        }
        let mut by_pair: FxHashMap<CopyLendPair, Vec<CopyLendSite>> = FxHashMap::default();
        for site in candidates {
            by_pair
                .entry(CopyLendPair::new(site.lhs, site.rhs))
                .or_default()
                .push(site);
        }
        let flows = origin_flows
            .get(&fn_did)
            .unwrap_or_else(|| panic!("missing origin flow for {fn_did:?}"));
        let value_flows = flows.body.depth0_value_flows();
        let live_before = live_before_by_location(program.tcx, &body);
        let caller_derived = super::caller_derived_locals(&body, program.tcx);

        for (pair, mut sites) in by_pair {
            sites.sort_by_key(|site| site.sort_key());
            let lhs_local = sites[0].lhs_local;
            let closure = owner_closure(
                [
                    SlotOwner::Local(sites[0].lhs_local),
                    SlotOwner::Local(sites[0].rhs_local),
                ],
                &value_flows,
            );
            let destination_flow =
                owner_closure([SlotOwner::Local(sites[0].lhs_local)], &value_flows);
            // A destination the facts call mutable is lent `&mut` when its window is clean; one
            // the facts do not cover stays at C2.
            let lent_mutably = mut_facts.is_mutable(fn_did, lhs_local)
                && !mut_facts.is_defaulted(fn_did, lhs_local);
            let pair = CopyLendPair {
                mutable: lent_mutably,
                ..pair
            };
            let drop = if mut_facts.is_mutable(fn_did, lhs_local) && !lent_mutably {
                Some(CopyLendEligibilityDrop::C2MutableOrMissingDestination)
            } else if lent_mutably
                && copy_lend_window_access(
                    &body,
                    &sites,
                    sites[0].lhs_local,
                    sites[0].rhs_local,
                    &value_flows,
                    &destination_flow,
                    &live_before,
                )
                .is_some()
            {
                Some(CopyLendEligibilityDrop::C2MutableWindowAccess)
            } else if closure
                .iter()
                .any(|owner| matches!(owner, SlotOwner::Field(_)))
            {
                Some(CopyLendEligibilityDrop::C3FieldInClosure)
            } else if destination_flows_to_deallocator(program.tcx, &body, &destination_flow) {
                Some(CopyLendEligibilityDrop::FreeDestination)
            } else {
                live_outward_event(program, slots, fn_did, &body, &closure, &live_before)
            };
            // Lend only an owner the function makes or releases itself.
            let rhs_local = sites[0].rhs_local;
            let drop = drop.or_else(|| {
                let released = destination_flows_to_deallocator(
                    program.tcx,
                    &body,
                    &owner_closure([SlotOwner::Local(rhs_local)], &value_flows),
                );
                (caller_derived.contains(&rhs_local) && !released)
                    .then_some(CopyLendEligibilityDrop::GuardCallerDerivedSource)
            });
            answer.push(CopyLendPairCandidate { pair, sites, drop });
        }
    }
    answer.sort_by_key(|candidate| {
        (
            SlotKey::of(candidate.pair.lhs),
            SlotKey::of(candidate.pair.rhs),
        )
    });
    answer
}

/// The window check of a mutable copy-lend, shared by measurement and production. From just
/// after each copy, every location where `q` may still be live is searched for a use of `p`
/// or of a copy of `p` that is not a copy of `q` (a read, a write, a reassignment, a release
/// or a pass to a call: any use of the local). Returns the first such
/// location. The replay's unique loan is the judge; this is its static twin.
fn copy_lend_window_access(
    body: &Body<'_>,
    sites: &[CopyLendSite],
    q: Local,
    p: Local,
    value_flows: &[(SlotOwner, SlotOwner)],
    destination_flow: &FxHashSet<SlotOwner>,
    live_before: &FxHashMap<Location, DenseBitSet<Local>>,
) -> Option<Location> {
    struct Touch<'a> {
        others: &'a FxHashSet<Local>,
        hit: bool,
    }
    impl<'tcx> Visitor<'tcx> for Touch<'_> {
        fn visit_local(&mut self, local: Local, context: PlaceContext, _: Location) {
            if self.others.contains(&local) && !matches!(context, PlaceContext::NonUse(_)) {
                self.hit = true;
            }
        }
    }
    let locals = |closure: FxHashSet<SlotOwner>| -> FxHashSet<Local> {
        closure
            .into_iter()
            .filter_map(|owner| match owner {
                SlotOwner::Local(local) => Some(local),
                _ => None,
            })
            .collect()
    };
    // `p` and every copy of `p` that is not a copy of `q`.
    let mut others = locals(owner_closure([SlotOwner::Local(p)], value_flows));
    for local in locals(destination_flow.clone()) {
        others.remove(&local);
    }
    others.insert(p);
    others.remove(&q);
    let successors = |l: Location| -> Vec<Location> {
        let data = &body.basic_blocks[l.block];
        if l.statement_index < data.statements.len() {
            vec![l.successor_within_block()]
        } else {
            data.terminator()
                .successors()
                .map(|block| Location {
                    block,
                    statement_index: 0,
                })
                .collect()
        }
    };
    for site in sites {
        let copy = Location {
            block: BasicBlock::from_u32(site.location.block),
            statement_index: site.location.statement_index,
        };
        let mut seen: FxHashSet<Location> = FxHashSet::default();
        let mut work = successors(copy);
        while let Some(l) = work.pop() {
            if !seen.insert(l) {
                continue;
            }
            if !live_before.get(&l).is_some_and(|live| live.contains(q)) {
                continue;
            }
            let data = &body.basic_blocks[l.block];
            let mut touch = Touch {
                others: &others,
                hit: false,
            };
            if l.statement_index < data.statements.len() {
                touch.visit_statement(&data.statements[l.statement_index], l);
            } else {
                touch.visit_terminator(data.terminator(), l);
            }
            if touch.hit {
                return Some(l);
            }
            work.extend(successors(l));
        }
    }
    None
}

fn collect_copy_sites(
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'_>,
) -> Vec<CopyLendSite> {
    let mut sites = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let StatementKind::Assign(box (lhs_place, rvalue)) = &statement.kind else {
                continue;
            };
            let rhs_place = match rvalue {
                Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs))
                | Rvalue::CopyForDeref(rhs) => rhs,
                _ => continue,
            };
            let (Some(ResolvedSlot::Local(lhs_slot)), Some(ResolvedSlot::Local(rhs_slot))) = (
                resolve_place(slots, fn_did, body, *lhs_place, 0, None),
                resolve_place(slots, fn_did, body, *rhs_place, 0, None),
            ) else {
                continue;
            };
            let universe = slots
                .fn_local_slots
                .get(&fn_did)
                .unwrap_or_else(|| panic!("missing local slots for {fn_did:?}"));
            let lhs_data = universe.slot(lhs_slot);
            let rhs_data = universe.slot(rhs_slot);
            if lhs_data.depth != 0
                || rhs_data.depth != 0
                || lhs_data.owner != SlotOwner::Local(lhs_place.local)
                || rhs_data.owner != SlotOwner::Local(rhs_place.local)
            {
                continue;
            }
            sites.push(CopyLendSite {
                fn_did,
                location: MirLocationKey::new(block.as_u32(), statement_index),
                lhs: SlotRef::Local(fn_did, lhs_slot),
                rhs: SlotRef::Local(fn_did, rhs_slot),
                lhs_local: lhs_place.local,
                rhs_local: rhs_place.local,
            });
        }
    }
    sites
}

fn owner_closure(
    roots: impl IntoIterator<Item = SlotOwner>,
    value_flows: &[(SlotOwner, SlotOwner)],
) -> FxHashSet<SlotOwner> {
    let mut closure: FxHashSet<_> = roots.into_iter().collect();
    let mut changed = true;
    while changed {
        changed = false;
        for &(source, target) in value_flows {
            if closure.contains(&source) {
                changed |= closure.insert(target);
            }
        }
    }
    closure
}

fn live_before_by_location<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> FxHashMap<Location, DenseBitSet<Local>> {
    let mut cursor = MaybeLiveLocals
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);
    let mut answer = FxHashMap::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let count = data.statements.len() + data.terminator.is_some() as usize;
        for statement_index in 0..count {
            let location = Location {
                block,
                statement_index,
            };
            cursor.seek_before_primary_effect(location);
            answer.insert(location, cursor.get().clone());
        }
    }
    answer
}

fn closure_live(closure: &FxHashSet<SlotOwner>, live: &DenseBitSet<Local>) -> bool {
    closure
        .iter()
        .any(|owner| matches!(owner, SlotOwner::Local(local) if live.contains(*local)))
}

fn rvalue_mentions_closure(
    rvalue: &Rvalue<'_>,
    location: Location,
    closure: &FxHashSet<SlotOwner>,
) -> bool {
    struct ClosureUse<'a> {
        closure: &'a FxHashSet<SlotOwner>,
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for ClosureUse<'_> {
        fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
            self.found |= self.closure.contains(&SlotOwner::Local(place.local));
            self.super_place(place, context, location);
        }
    }

    let mut visitor = ClosureUse {
        closure,
        found: false,
    };
    visitor.visit_rvalue(rvalue, location);
    visitor.found
}

fn known_deallocator(call: &crate::analyses::mir::terminator::MirFunctionCall<'_, '_>) -> bool {
    let CallKind::LibC(name) = &call.func else {
        return false;
    };
    boundary_table::lookup(name.as_str(), Matcher::ForeignC)
        .is_some_and(|entry| entry.roles.contains(&Role::Sink))
}

fn exact_free(call: &crate::analyses::mir::terminator::MirFunctionCall<'_, '_>) -> bool {
    let CallKind::LibC(name) = &call.func else {
        return false;
    };
    boundary_table::lookup(name.as_str(), Matcher::ForeignC)
        .is_some_and(|entry| entry.roles == [Role::Sink])
}

fn destination_flows_to_deallocator<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
    destination_flow: &FxHashSet<SlotOwner>,
) -> bool {
    body.basic_blocks.iter().any(|data| {
        let Some(terminator) = data.terminator.as_ref() else {
            return false;
        };
        let Some(call) = terminator.as_call(tcx) else {
            return false;
        };
        known_deallocator(&call)
            && call.args.first().is_some_and(|arg| {
                arg.node
                    .place()
                    .is_some_and(|place| destination_flow.contains(&SlotOwner::Local(place.local)))
            })
    })
}

fn boundary_call(call: &crate::analyses::mir::terminator::MirFunctionCall<'_, '_>) -> bool {
    match call.func {
        CallKind::FreeStanding(_) | CallKind::Impl(_) => true,
        CallKind::LibC(_) => !exact_free(call),
        CallKind::RustLib(_) | CallKind::Closure | CallKind::Dynamic => true,
    }
}

fn live_outward_event<'tcx>(
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    closure: &FxHashSet<SlotOwner>,
    live_before: &FxHashMap<Location, DenseBitSet<Local>>,
) -> Option<CopyLendEligibilityDrop> {
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            if !closure_live(closure, &live_before[&location]) {
                continue;
            }
            let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                continue;
            };
            if !rvalue.ty(body, program.tcx).is_any_ptr()
                && !matches!(rvalue, Rvalue::Aggregate(..))
            {
                continue;
            }
            if !rvalue_mentions_closure(rvalue, location, closure) {
                continue;
            }
            if matches!(rvalue, Rvalue::Aggregate(..)) {
                return Some(CopyLendEligibilityDrop::C3AggregateStore);
            }
            if lhs
                .projection
                .iter()
                .any(|projection| matches!(projection, ProjectionElem::Field(..)))
            {
                return Some(CopyLendEligibilityDrop::C3FieldStore);
            }
            if lhs.local == RETURN_PLACE {
                return Some(CopyLendEligibilityDrop::C3Return);
            }
            match resolve_place(slots, fn_did, body, *lhs, 0, None) {
                Some(ResolvedSlot::Local(_)) => {}
                Some(ResolvedSlot::Field(_)) => {
                    return Some(CopyLendEligibilityDrop::C3FieldStore);
                }
                None => return Some(CopyLendEligibilityDrop::C3UnresolvedStore),
            }
        }
        let Some(terminator) = data.terminator.as_ref() else {
            continue;
        };
        let location = Location {
            block,
            statement_index: data.statements.len(),
        };
        if !closure_live(closure, &live_before[&location]) {
            continue;
        }
        let Some(call) = terminator.as_call(program.tcx) else {
            continue;
        };
        if boundary_call(&call)
            && call.args.iter().any(|arg| {
                arg.node
                    .place()
                    .is_some_and(|place| closure.contains(&SlotOwner::Local(place.local)))
            })
        {
            return Some(match call.func {
                CallKind::FreeStanding(_) | CallKind::Impl(_) => {
                    CopyLendEligibilityDrop::C3OrdinaryCall
                }
                CallKind::LibC(_) if known_deallocator(&call) => {
                    CopyLendEligibilityDrop::C3ReallocSource
                }
                CallKind::LibC(_)
                | CallKind::RustLib(_)
                | CallKind::Closure
                | CallKind::Dynamic => CopyLendEligibilityDrop::C3OutwardUnknownCall,
            });
        }
    }
    None
}

#[cfg(test)]
mod mode_tests {
    use super::*;

    #[test]
    fn a5_preledger_decline_reason_labels_are_complete_and_stable() {
        assert_eq!(
            OverlapPreledgerDeclineReason::ALL.map(OverlapPreledgerDeclineReason::label),
            [
                "baseline-construction",
                "baseline-verification",
                "a5-plan-production",
                "refined-fallback-construction",
                "refined-fallback-verification",
                "precise-construction",
                "precise-verification",
                "coarse-construction",
                "coarse-verification",
            ]
        );
    }

    #[test]
    fn receipt_key_order_is_canonical_across_input_order() {
        let left = canonical_receipt("z=3\nschema=x\ndata=true\nstatus=ok\na=1\n".to_owned());
        let right = canonical_receipt("status=ok\na=1\ndata=true\nz=3\nschema=x\n".to_owned());
        assert_eq!(left, right);
        assert_eq!(left, "schema=x\nstatus=ok\ndata=true\na=1\nz=3\n");
    }
}
