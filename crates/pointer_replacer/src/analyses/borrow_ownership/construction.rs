#[cfg(test)]
use std::cell::Cell;
use std::{
    collections::BTreeSet,
    time::{Duration, Instant},
};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::{
    Body, Local, Location, Operand, Place, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind,
    visit::{PlaceContext, Visitor},
};
use rustc_mir_dataflow::Analysis;
use rustc_span::def_id::LocalDefId;
use sha2::{Digest, Sha256};

#[cfg(test)]
use super::borrow_verify::verify_l2_to_fixpoint_counting_impl;
#[cfg(test)]
use super::coherence::add_coherence_tagging_uses;
use super::{
    BoOwnEmissionStats, CrateCtxt, SlotKind,
    a5_overlap::{
        A5Mode, A5World, AbiGuardDisposition, C9MarkKey, WholeProgramAttestation,
        WitnessMarkability, apply_coarse_constraints, plan_c9_marks,
    },
    a5_producer::{A5Plan, PlannedC9Mark, produce_a5_plan},
    borrow_verify::{
        LoopBackend, verify_to_fixpoint_counting_with_flows,
        verify_to_fixpoint_counting_with_flows_impl,
    },
    boundary_table::{self, Matcher, Role},
    coherence::{
        CopyLendPair, FieldRefPlan, add_coherence, add_coherence_removal_only,
        add_coherence_with_copy_lends, constrain_field_ref_worthiness,
        positive_opaque_return_slots,
    },
    crate_slots::{CrateSlots, ptr_chain_depth},
    emit_crate_ownership_constraints, emit_crate_ownership_constraints_with_copy_lends,
    l2::{MirLocationKey, SlotKey},
    mutability_facts::MutFacts,
    origin_flow::OriginFlowResults,
    origin_summary::{OriginSummaries, SignatureRoot},
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

pub(crate) const A2_MODE_ENV: &str = "CRAT_BO_A2_MODE";

pub(crate) fn plan_a5_c9_marks(
    witnesses: impl IntoIterator<Item = (C9MarkKey, WitnessMarkability)>,
) -> BTreeSet<C9MarkKey> {
    plan_c9_marks(witnesses)
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum A2Mode {
    #[default]
    Off,
    DefinitelyOverwritten,
}

impl A2Mode {
    pub(crate) fn current() -> Self {
        #[cfg(test)]
        if let Some(mode) = A2_MODE_OVERRIDE.with(Cell::get) {
            return mode;
        }
        match std::env::var(A2_MODE_ENV) {
            Err(std::env::VarError::NotPresent) => Self::Off,
            Ok(value) => match value.as_str() {
                "off" => Self::Off,
                "definitely_overwritten" => Self::DefinitelyOverwritten,
                other => {
                    panic!("{A2_MODE_ENV} must be off or definitely_overwritten; got {other:?}")
                }
            },
            Err(error) => panic!("{A2_MODE_ENV} is not valid Unicode: {error}"),
        }
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::DefinitelyOverwritten => "definitely_overwritten",
        }
    }

    #[cfg(test)]
    pub(crate) fn with_override<T>(self, f: impl FnOnce() -> T) -> T {
        struct Restore(Option<A2Mode>);
        impl Drop for Restore {
            fn drop(&mut self) {
                A2_MODE_OVERRIDE.with(|slot| slot.set(self.0));
            }
        }
        let _restore = Restore(A2_MODE_OVERRIDE.with(|slot| slot.replace(Some(self))));
        f()
    }
}

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
        Self::Baseline
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
    static A2_MODE_OVERRIDE: Cell<Option<A2Mode>> = const { Cell::new(None) };
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct CopyLendEligibility {
    pub(crate) pairs: FxHashSet<CopyLendPair>,
    pub(crate) sites: Vec<CopyLendSite>,
}

/// Exact primary exclusion used by the retained A12 funnel diagnostic. The
/// production predicate and the diagnostic share this enum-returning
/// classifier, so measurement cannot silently reinterpret eligibility.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CopyLendEligibilityDrop {
    C2MutableOrMissingDestination,
    C3FieldInClosure,
    S22FreeDestination,
    C3AggregateStore,
    C3FieldStore,
    C3Return,
    C3UnresolvedStore,
    C3OrdinaryCall,
    C3ReallocSource,
    C3OutwardUnknownCall,
}

impl CopyLendEligibilityDrop {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::C2MutableOrMissingDestination => "c2-mutable-or-missing-destination",
            Self::C3FieldInClosure => "c3-field-in-closure",
            Self::S22FreeDestination => "s2-2-free-destination",
            Self::C3AggregateStore => "c3-aggregate-store",
            Self::C3FieldStore => "c3-field-store",
            Self::C3Return => "c3-return",
            Self::C3UnresolvedStore => "c3-unresolved-store",
            Self::C3OrdinaryCall => "c3-ordinary-call",
            Self::C3ReallocSource => "c3-realloc-source",
            Self::C3OutwardUnknownCall => "c3-outward-unknown-call",
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
    pub(crate) mode: CopyLendMode,
    pub(crate) nullability: super::nullability::NullabilityFacts,
    pub(crate) field_ref_plan: FieldRefPlan,
    pub(crate) a2_mode: A2Mode,
    pub(crate) a2_killed_memberships: usize,
    pub(crate) a2_opaque_result_guards: usize,
    pub(crate) selectors: Selectors,
    pub(crate) eligibility: CopyLendEligibility,
    pub(crate) esc_minimal: super::esc_minimal::EscMinimalSelection,
    pub(crate) stats: BoOwnEmissionStats,
    pub(crate) eligibility_elapsed: Duration,
    pub(crate) emit_elapsed: Duration,
    pub(crate) coherence_elapsed: Duration,
}

#[derive(Clone, Debug)]
pub(crate) struct VerifiedBo {
    pub(crate) model: FxHashMap<SlotRef, SlotKind>,
    pub(crate) baseline_model: FxHashMap<SlotRef, SlotKind>,
    pub(crate) retained_c9_marks: BTreeSet<C9MarkKey>,
    pub(crate) retained_c9_plans: Vec<PlannedC9Mark>,
    pub(crate) summary_artifact: super::a5_overlap::A5SummaryArtifact,
    pub(crate) mark_artifact: String,
    pub(crate) site_artifact: String,
    pub(crate) nullable_artifact: String,
    pub(crate) field_ref_artifact: String,
    pub(crate) receipt: String,
    pub(crate) round_stats: super::borrow_verify::RoundStats,
    pub(crate) selector_sources: usize,
    pub(crate) selector_sinks: usize,
    pub(crate) emission_stats: BoOwnEmissionStats,
    pub(crate) construction_emit_elapsed: Duration,
    pub(crate) construction_coherence_elapsed: Duration,
    pub(crate) check_sat_count: usize,
    pub(crate) hard_check_count: usize,
    pub(crate) optimize_materialization_count: usize,
    pub(crate) lazy_plain_hard_check_count: usize,
    pub(crate) lazy_tracked_recheck_count: usize,
    pub(crate) lazy_plain_materialization_count: usize,
    pub(crate) hard_check_elapsed: Duration,
    pub(crate) optimize_materialization_elapsed: Duration,
    pub(crate) a16_refined_links: usize,
    pub(crate) planned_c9_marks: BTreeSet<C9MarkKey>,
    pub(crate) producer_stats: super::a5_producer::A5ProducerStats,
}

/// Typed diagnostic for every `None` boundary before the production A5 worker
/// can write its model and T2/ESC ledgers. Production callers retain the
/// historical `Option` API; measurement callers use the reporting twin below.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum A5PreledgerDeclineReason {
    BaselineConstruction,
    BaselineVerification,
    A5PlanProduction,
    RefinedFallbackConstruction,
    RefinedFallbackVerification,
    PreciseConstruction,
    PreciseVerification,
    CoarseConstruction,
    CoarseVerification,
}

impl A5PreledgerDeclineReason {
    pub(crate) const ALL: [Self; 9] = [
        Self::BaselineConstruction,
        Self::BaselineVerification,
        Self::A5PlanProduction,
        Self::RefinedFallbackConstruction,
        Self::RefinedFallbackVerification,
        Self::PreciseConstruction,
        Self::PreciseVerification,
        Self::CoarseConstruction,
        Self::CoarseVerification,
    ];

    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::BaselineConstruction => "baseline-construction",
            Self::BaselineVerification => "baseline-verification",
            Self::A5PlanProduction => "a5-plan-production",
            Self::RefinedFallbackConstruction => "refined-fallback-construction",
            Self::RefinedFallbackVerification => "refined-fallback-verification",
            Self::PreciseConstruction => "precise-construction",
            Self::PreciseVerification => "precise-verification",
            Self::CoarseConstruction => "coarse-construction",
            Self::CoarseVerification => "coarse-verification",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct A5PreledgerDecline {
    reason: A5PreledgerDeclineReason,
    detail: Option<String>,
}

impl A5PreledgerDecline {
    fn at(reason: A5PreledgerDeclineReason) -> Self {
        Self {
            reason,
            detail: None,
        }
    }

    fn from_error(reason: A5PreledgerDeclineReason, error: impl std::fmt::Display) -> Self {
        Self {
            reason,
            detail: Some(error.to_string()),
        }
    }

    fn with_detail(reason: A5PreledgerDeclineReason, detail: String) -> Self {
        Self {
            reason,
            detail: Some(detail),
        }
    }

    pub(crate) fn reason(&self) -> A5PreledgerDeclineReason {
        self.reason
    }

    pub(crate) fn detail(&self) -> Option<&str> {
        self.detail.as_deref()
    }
}

const A5_PAIR_LEDGER_SHA256: &str =
    "16dac90cf269c5480e6f612e54733dd210e41393a879202c7138e93cd7d360e1";
const REPLAY_SAFE_DEFINITION: &str = "no incompatible access derived by precise replay with the effective parameter-overlap map injected; O2 closed-world frozen graph.";

struct NullabilityArtifacts {
    artifact: String,
    slots: usize,
    fields: usize,
}

impl NullabilityArtifacts {
    fn empty() -> Self {
        Self {
            artifact: String::from("variant\towner\tslot\tis_null_use\tnull_literal\tnullable\n"),
            slots: 0,
            fields: 0,
        }
    }
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

struct A14Artifacts {
    artifact: String,
    opaque_stores: usize,
    unresolved_unresolvable: usize,
    nullable_store_fields: usize,
}

impl A14Artifacts {
    fn empty() -> Self {
        Self {
            artifact: String::from(
                "variant\towner\tslot\topaque\tunresolved_unresolvable\tnullable\tsafe\n",
            ),
            opaque_stores: 0,
            unresolved_unresolvable: 0,
            nullable_store_fields: 0,
        }
    }
}

fn a14_artifacts(construction: &BoConstruction) -> A14Artifacts {
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
    A14Artifacts {
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

fn model_digest(model: &FxHashMap<SlotRef, SlotKind>) -> String {
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

fn summary_digest(plan: &A5Plan) -> String {
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

fn a5_mark_artifact(
    mode: A5Mode,
    plan: &A5Plan,
    retained: &BTreeSet<C9MarkKey>,
    selected_model_sha256: &str,
) -> String {
    let mut out = format!(
        "# a5_mode={}\n# a5_world={}\n# a5_abi_guard={}\n# a5_producer=rustc-mir-current-v1\n\
         # a5_pair_ledger_sha256={A5_PAIR_LEDGER_SHA256}\n# selected_model_sha256={selected_model_sha256}\n\
         caller\tblock\tstatement\tcallee\tleft_param\tright_param\tshared_side\tpointee_type\tretained\n",
        mode.label(),
        A5World::ClosedWorldFrozenGraph.label(),
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

pub(crate) fn a5_site_artifact(mode: A5Mode, plan: &A5Plan) -> String {
    let mut out = String::from(
        "caller\tblock\tstatement\ttarget\tleft_parameter\tright_parameter\tleft_variant\tleft_owner\tleft_slot\tright_variant\tright_owner\tright_slot\tclass\ta5_world\ta5_mode\ta5_abi_guard\n",
    );
    for site in &plan.site_ledger {
        let class = match site.class {
            super::a5_overlap::WitnessMutability::MutMut => "mut_mut",
            super::a5_overlap::WitnessMutability::MutReadOnly { .. } => "mut_read_only",
            super::a5_overlap::WitnessMutability::SharedShared => "shared_shared",
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
            A5World::ClosedWorldFrozenGraph.label(),
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

fn a5_receipt(
    mode: A5Mode,
    plan: &A5Plan,
    retained: usize,
    retained_sites: usize,
    selected_model_sha256: &str,
    nullability: &NullabilityArtifacts,
    a14: &A14Artifacts,
) -> String {
    canonical_receipt(format!(
        "schema=bo-construction-v1\nstatus=ok\ndata=true\ncopy_lend_mode=baseline\n\
         a2_mode=off\nsoundness_mode=a14\na5_mode={}\na5_world={}\nunknown_caller_seeding=false\n\
         a5_abi_guard={}\na5_raw_pairs={}\na5_effective_pairs={}\n\
         a5_raw_site_pairs={}\na5_raw_site_mut_mut={}\na5_raw_site_mut_read_only={}\n\
         a5_raw_site_shared_shared={}\n\
         a5_planned_marks={}\na5_retained_marks={}\na5_retained_mark_sites={}\n\
         a5_producer=rustc-mir-current-v1\n\
         a5_foster_producer=MutFacts::from_program(mutability_analysis+SourceVarGroups::postprocess_mut_res)\n\
         a5_pair_ledger_sha256={A5_PAIR_LEDGER_SHA256}\nselected_model_sha256={}\n\
         a5_summary_sha256={}\nnullable_slots={}\nnullable_fields={}\n\
         nullable_ledger_sha256={:x}\na14_opaque_stores={}\n\
         a14_unresolved_unresolvable={}\na14_nullable_store_fields={}\n\
         field_ref_ledger_sha256={:x}\nreplay_safe_definition={REPLAY_SAFE_DEFINITION}\n",
        mode.label(),
        A5World::ClosedWorldFrozenGraph.label(),
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
        a14.opaque_stores,
        a14.unresolved_unresolvable,
        a14.nullable_store_fields,
        Sha256::digest(a14.artifact.as_bytes()),
    ))
}

pub(crate) fn baseline_a5_receipt(model: &FxHashMap<SlotRef, SlotKind>) -> String {
    let plan = A5Plan::baseline();
    a5_receipt(
        A5Mode::Baseline,
        &plan,
        0,
        0,
        &model_digest(model),
        &NullabilityArtifacts::empty(),
        &A14Artifacts::empty(),
    )
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

fn construct_bo_a5_reference(
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
        CopyLendMode::Baseline,
        false,
    )
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
    let crate_ctxt = CrateCtxt::new(program);
    let esc_minimal = if enable_esc_minimal {
        super::esc_minimal::select(program, slots)
    } else {
        super::esc_minimal::EscMinimalSelection::default()
    };
    let t = Instant::now();
    let eligibility = if mode == CopyLendMode::LendArm {
        analyze_copy_lend_eligibility(program, slots, mut_facts, origins.native_flows())
    } else {
        CopyLendEligibility::default()
    };
    let eligibility_elapsed = t.elapsed();
    let t = Instant::now();
    let (stats, selectors) = match mode {
        CopyLendMode::LendArm => emit_crate_ownership_constraints_with_copy_lends(
            &crate_ctxt,
            slots,
            origins,
            solver,
            &eligibility.pairs,
        )?,
        CopyLendMode::Baseline | CopyLendMode::RemovalOnly => {
            emit_crate_ownership_constraints(&crate_ctxt, slots, origins, solver)?
        }
    };
    let emit_elapsed = t.elapsed();
    let t = Instant::now();
    if let Some(tracker) = solver.tracker() {
        tracker.set_context("coherence");
    }
    for &fn_did in &program.functions {
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
    }
    let nullability = super::nullability::analyze(program.tcx, &program.functions, slots);
    let field_ref_plan = constrain_field_ref_worthiness(
        solver,
        slots,
        program,
        origins.try_native_flows(),
        &nullability,
    );
    let coherence_elapsed = t.elapsed();
    Ok(BoConstruction {
        mode,
        nullability,
        field_ref_plan,
        a2_mode: A2Mode::Off,
        a2_killed_memberships: 0,
        a2_opaque_result_guards: 0,
        selectors,
        eligibility,
        esc_minimal,
        stats,
        eligibility_elapsed,
        emit_elapsed,
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

/// Accepted A16-REFINE construction: add one-way links only for
/// modeled-origin returns and report their exact site count.
pub(crate) fn construct_bo_into_a16_refined(
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
            CopyLendMode::Baseline,
        )?
    } else {
        construct_bo_a5_reference(program, slots, origins, mut_facts, solver)?
    };
    let links = add_refined_return_kind_links(program, slots, origins, solver);
    Ok((construction, links))
}

/// D1-authorized parked-census migration: shared construction, baseline mode, with the harness's
/// existing Use-family tracking preserved exactly. No eligibility or lend behavior is reachable.
#[cfg(test)]
pub(crate) fn construct_tracked_census_baseline(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
) -> anyhow::Result<BoConstruction> {
    let crate_ctxt = CrateCtxt::new(program);
    let t = Instant::now();
    let (stats, selectors) = emit_crate_ownership_constraints(&crate_ctxt, slots, origins, solver)?;
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
    Ok(BoConstruction {
        mode: CopyLendMode::Baseline,
        nullability: super::nullability::NullabilityFacts::default(),
        field_ref_plan: FieldRefPlan::default(),
        a2_mode: A2Mode::Off,
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
        guards += 1;
    }
    construction.a2_mode = A2Mode::DefinitelyOverwritten;
    construction.a2_killed_memberships = a2.killed_memberships;
    construction.a2_opaque_result_guards = guards;
    Ok(construction)
}

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
    verify_to_fixpoint_counting_with_flows(
        program,
        slots,
        origin_flows,
        solver,
        &construction.selectors,
        mut_facts,
    )
    .0
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
    assert_eq!(
        construction.mode,
        CopyLendMode::Baseline,
        "A5 focused replay must keep the independent CopyLend switch at baseline"
    );
    super::esc_minimal::with_presentations(&construction.esc_minimal, || {
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
    let copy_lends =
        (construction.mode == CopyLendMode::LendArm).then_some(&construction.eligibility.pairs);
    verify_to_fixpoint_counting_with_flows_impl(
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
    )
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
    super::esc_minimal::with_presentations(&construction.esc_minimal, || {
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
    super::esc_minimal::with_presentations(&construction.esc_minimal, || {
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

/// L2 twin of `verify_bo_construction_counting_for_test`, owned by the same
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
    super::esc_minimal::with_presentations(&construction.esc_minimal, || {
        verify_l2_to_fixpoint_counting_impl(
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

pub(crate) fn solve_bo_a5_config(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
) -> Option<VerifiedBo> {
    solve_bo_a5_config_reporting(program, slots, origins, mut_facts, mode, attestation).ok()
}

/// Diagnostic twin of `solve_bo_a5_config`: identical construction and solve,
/// with a typed reason at every historical pre-ledger `None` exit.
pub(crate) fn solve_bo_a5_config_reporting(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
) -> Result<VerifiedBo, A5PreledgerDecline> {
    // A16-REFINE is part of the accepted precise production semantics. The
    // retained Baseline mode is a diagnostic A5 control, not another
    // production configuration.
    let refined = mode == A5Mode::PreciseReplay;
    let (verified, _links) = solve_bo_a5_config_inner(
        program,
        slots,
        origins,
        mut_facts,
        mode,
        attestation,
        refined,
        true,
    )?;
    Ok(stamp_a16_refined_receipt(verified, refined))
}

/// Measurement reference: accepted A5/A16 production semantics with Phase-2
/// escaped-loan selection disabled in both the planning baseline and candidate
/// construction. This is the byte-equivalence path to c080.
pub(crate) fn solve_bo_a5_reference_reporting(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    attestation: Option<WholeProgramAttestation>,
) -> Result<VerifiedBo, A5PreledgerDecline> {
    let (verified, _links) = solve_bo_a5_config_inner(
        program,
        slots,
        origins,
        mut_facts,
        A5Mode::PreciseReplay,
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
            verified.a16_refined_links
        ));
    }
    verified
}

fn solve_bo_a5_config_inner(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
    refined: bool,
    enable_esc_minimal: bool,
) -> Result<(VerifiedBo, usize), A5PreledgerDecline> {
    assert_eq!(
        CopyLendMode::current(),
        CopyLendMode::Baseline,
        "the A5 loop-2 matrix keeps dormant CopyLend semantics at baseline"
    );

    let baseline_solver = KindSolver::new(slots);
    let baseline_construction =
        construct_bo_a5_reference(program, slots, origins, mut_facts, &baseline_solver).map_err(
            |error| {
                A5PreledgerDecline::from_error(
                    A5PreledgerDeclineReason::BaselineConstruction,
                    error,
                )
            },
        )?;
    let (baseline_model, baseline_round_stats) = verify_bo_construction_counting(
        program,
        slots,
        origins,
        &baseline_solver,
        &baseline_construction,
        mut_facts,
    );
    let baseline_model = baseline_model.ok_or_else(|| {
        let first = baseline_solver
            .round_model_failure()
            .map(|failure| failure.summary())
            .unwrap_or_else(|| "untyped-round-decline".to_owned());
        A5PreledgerDecline::with_detail(
            A5PreledgerDeclineReason::BaselineVerification,
            format!(
                "expected=accepted-model got={first} rounds={} commits={} selected_copy_lends={} dropped_sources={} dropped_sinks={} field_conflict={:?} field_kind={:?} cap_exhausted={} l2_decline={:?}",
                baseline_round_stats.rounds,
                baseline_round_stats.commits_conflict,
                baseline_round_stats.copy_lend_replay_selections,
                baseline_round_stats.dropped_sources,
                baseline_round_stats.dropped_sinks,
                baseline_round_stats.field_conflict_decline,
                baseline_round_stats.field_conflict_kind,
                baseline_round_stats.cap_exhausted,
                baseline_round_stats.l2_decline,
            ),
        )
    })?;
    let baseline_nullability = nullability_artifacts(&baseline_construction);
    let baseline_a14 = a14_artifacts(&baseline_construction);
    if mode == A5Mode::Baseline {
        let plan = if attestation == Some(WholeProgramAttestation::FrozenBenchmarkGraph) {
            A5Plan::baseline_attested()
        } else {
            A5Plan::baseline()
        };
        let selected_model_sha256 = model_digest(&baseline_model);
        return Ok((
            VerifiedBo {
                receipt: a5_receipt(
                    mode,
                    &plan,
                    0,
                    0,
                    &selected_model_sha256,
                    &baseline_nullability,
                    &baseline_a14,
                ),
                mark_artifact: a5_mark_artifact(
                    mode,
                    &plan,
                    &BTreeSet::new(),
                    &selected_model_sha256,
                ),
                site_artifact: a5_site_artifact(mode, &plan),
                nullable_artifact: baseline_nullability.artifact.clone(),
                field_ref_artifact: baseline_a14.artifact.clone(),
                summary_artifact: plan.summary_artifact.clone(),
                baseline_model: baseline_model.clone(),
                model: baseline_model,
                retained_c9_marks: BTreeSet::new(),
                retained_c9_plans: Vec::new(),
                round_stats: baseline_round_stats,
                selector_sources: baseline_construction.selectors.sources().len(),
                selector_sinks: baseline_construction.selectors.sinks().len(),
                emission_stats: baseline_construction.stats,
                construction_emit_elapsed: baseline_construction.emit_elapsed,
                construction_coherence_elapsed: baseline_construction.coherence_elapsed,
                check_sat_count: baseline_solver.check_sat_count(),
                hard_check_count: baseline_solver.hard_check_count(),
                optimize_materialization_count: baseline_solver.optimize_materialization_count(),
                lazy_plain_hard_check_count: baseline_solver.lazy_plain_hard_check_count(),
                lazy_tracked_recheck_count: baseline_solver.lazy_tracked_recheck_count(),
                lazy_plain_materialization_count: baseline_solver
                    .lazy_plain_materialization_count(),
                hard_check_elapsed: baseline_solver.hard_check_elapsed(),
                optimize_materialization_elapsed: baseline_solver
                    .optimize_materialization_elapsed(),
                a16_refined_links: 0,
                planned_c9_marks: BTreeSet::new(),
                producer_stats: plan.stats,
            },
            0,
        ));
    }

    let plan = produce_a5_plan(
        program,
        slots,
        origins.native_flows(),
        mut_facts,
        &baseline_model,
        mode,
        attestation,
    )
    .map_err(|error| {
        A5PreledgerDecline::from_error(A5PreledgerDeclineReason::A5PlanProduction, error)
    })?;
    if matches!(plan.abi_guard, AbiGuardDisposition::Refused { .. }) {
        if refined {
            // Refusing A5 promotion must not also disable the independently
            // accepted A16-REFINE constraint. Product/unattested mode keeps
            // the A5 guard's fallback while applying the same one-way return
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
                A5PreledgerDecline::from_error(
                    A5PreledgerDeclineReason::RefinedFallbackConstruction,
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
                A5PreledgerDecline::at(A5PreledgerDeclineReason::RefinedFallbackVerification)
            })?;
            let selected_model_sha256 = model_digest(&model);
            let nullability = nullability_artifacts(&construction);
            let a14 = a14_artifacts(&construction);
            return Ok((
                VerifiedBo {
                    receipt: a5_receipt(
                        mode,
                        &plan,
                        0,
                        0,
                        &selected_model_sha256,
                        &nullability,
                        &a14,
                    ),
                    mark_artifact: a5_mark_artifact(
                        mode,
                        &plan,
                        &BTreeSet::new(),
                        &selected_model_sha256,
                    ),
                    site_artifact: a5_site_artifact(mode, &plan),
                    nullable_artifact: nullability.artifact,
                    field_ref_artifact: a14.artifact,
                    summary_artifact: plan.summary_artifact.clone(),
                    baseline_model,
                    model,
                    retained_c9_marks: BTreeSet::new(),
                    retained_c9_plans: Vec::new(),
                    round_stats,
                    selector_sources: construction.selectors.sources().len(),
                    selector_sinks: construction.selectors.sinks().len(),
                    emission_stats: construction.stats,
                    construction_emit_elapsed: construction.emit_elapsed,
                    construction_coherence_elapsed: construction.coherence_elapsed,
                    check_sat_count: solver.check_sat_count(),
                    hard_check_count: solver.hard_check_count(),
                    optimize_materialization_count: solver.optimize_materialization_count(),
                    lazy_plain_hard_check_count: solver.lazy_plain_hard_check_count(),
                    lazy_tracked_recheck_count: solver.lazy_tracked_recheck_count(),
                    lazy_plain_materialization_count: solver.lazy_plain_materialization_count(),
                    hard_check_elapsed: solver.hard_check_elapsed(),
                    optimize_materialization_elapsed: solver.optimize_materialization_elapsed(),
                    a16_refined_links: refined_links,
                    planned_c9_marks: plan
                        .planned_marks
                        .iter()
                        .map(|mark| mark.key.clone())
                        .collect(),
                    producer_stats: plan.stats,
                },
                refined_links,
            ));
        }
        let selected_model_sha256 = model_digest(&baseline_model);
        return Ok((
            VerifiedBo {
                receipt: a5_receipt(
                    mode,
                    &plan,
                    0,
                    0,
                    &selected_model_sha256,
                    &baseline_nullability,
                    &baseline_a14,
                ),
                mark_artifact: a5_mark_artifact(
                    mode,
                    &plan,
                    &BTreeSet::new(),
                    &selected_model_sha256,
                ),
                site_artifact: a5_site_artifact(mode, &plan),
                nullable_artifact: baseline_nullability.artifact.clone(),
                field_ref_artifact: baseline_a14.artifact.clone(),
                summary_artifact: plan.summary_artifact.clone(),
                baseline_model: baseline_model.clone(),
                model: baseline_model,
                retained_c9_marks: BTreeSet::new(),
                retained_c9_plans: Vec::new(),
                round_stats: baseline_round_stats,
                selector_sources: baseline_construction.selectors.sources().len(),
                selector_sinks: baseline_construction.selectors.sinks().len(),
                emission_stats: baseline_construction.stats,
                construction_emit_elapsed: baseline_construction.emit_elapsed,
                construction_coherence_elapsed: baseline_construction.coherence_elapsed,
                check_sat_count: baseline_solver.check_sat_count(),
                hard_check_count: baseline_solver.hard_check_count(),
                optimize_materialization_count: baseline_solver.optimize_materialization_count(),
                lazy_plain_hard_check_count: baseline_solver.lazy_plain_hard_check_count(),
                lazy_tracked_recheck_count: baseline_solver.lazy_tracked_recheck_count(),
                lazy_plain_materialization_count: baseline_solver
                    .lazy_plain_materialization_count(),
                hard_check_elapsed: baseline_solver.hard_check_elapsed(),
                optimize_materialization_elapsed: baseline_solver
                    .optimize_materialization_elapsed(),
                a16_refined_links: 0,
                planned_c9_marks: plan
                    .planned_marks
                    .iter()
                    .map(|mark| mark.key.clone())
                    .collect(),
                producer_stats: plan.stats,
            },
            0,
        ));
    }

    let solver = KindSolver::new(slots);
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
            A5PreledgerDecline::from_error(A5PreledgerDeclineReason::PreciseConstruction, error)
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
                construct_bo_a5_reference(program, slots, origins, mut_facts, &solver)
            }
            .map_err(|error| {
                A5PreledgerDecline::from_error(A5PreledgerDeclineReason::CoarseConstruction, error)
            })?,
            0,
        )
    };
    let (model, round_stats) = match mode {
        A5Mode::Baseline => unreachable!(),
        A5Mode::PreciseReplay => {
            let (model, stats) = verify_bo_construction_with_parameter_overlaps(
                program,
                slots,
                origins,
                &solver,
                &construction,
                mut_facts,
                &plan.effective_overlaps,
            );
            (
                model.ok_or_else(|| {
                    A5PreledgerDecline::at(A5PreledgerDeclineReason::PreciseVerification)
                })?,
                stats,
            )
        }
        A5Mode::CoarseConstraint => {
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
                    A5PreledgerDecline::at(A5PreledgerDeclineReason::CoarseVerification)
                })?,
                stats,
            )
        }
    };
    let retained_c9_marks = if mode == A5Mode::PreciseReplay {
        plan.retained_marks(&model)
    } else {
        BTreeSet::new()
    };
    let retained_c9_plans = if mode == A5Mode::PreciseReplay {
        plan.retained_mark_plans(&model)
    } else {
        Vec::new()
    };
    let selected_model_sha256 = model_digest(&model);
    let nullability = nullability_artifacts(&construction);
    let a14 = a14_artifacts(&construction);
    Ok((
        VerifiedBo {
            receipt: a5_receipt(
                mode,
                &plan,
                retained_c9_marks.len(),
                retained_c9_plans.len(),
                &selected_model_sha256,
                &nullability,
                &a14,
            ),
            mark_artifact: a5_mark_artifact(
                mode,
                &plan,
                &retained_c9_marks,
                &selected_model_sha256,
            ),
            site_artifact: a5_site_artifact(mode, &plan),
            nullable_artifact: nullability.artifact,
            field_ref_artifact: a14.artifact,
            summary_artifact: plan.summary_artifact.clone(),
            model,
            baseline_model,
            retained_c9_marks,
            retained_c9_plans,
            round_stats,
            selector_sources: construction.selectors.sources().len(),
            selector_sinks: construction.selectors.sinks().len(),
            emission_stats: construction.stats,
            construction_emit_elapsed: construction.emit_elapsed,
            construction_coherence_elapsed: construction.coherence_elapsed,
            check_sat_count: solver.check_sat_count(),
            hard_check_count: solver.hard_check_count(),
            optimize_materialization_count: solver.optimize_materialization_count(),
            lazy_plain_hard_check_count: solver.lazy_plain_hard_check_count(),
            lazy_tracked_recheck_count: solver.lazy_tracked_recheck_count(),
            lazy_plain_materialization_count: solver.lazy_plain_materialization_count(),
            hard_check_elapsed: solver.hard_check_elapsed(),
            optimize_materialization_elapsed: solver.optimize_materialization_elapsed(),
            a16_refined_links: refined_links,
            planned_c9_marks: plan
                .planned_marks
                .iter()
                .map(|mark| mark.key.clone())
                .collect(),
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
            let drop = if mut_facts.is_mutable(fn_did, lhs_local) {
                Some(CopyLendEligibilityDrop::C2MutableOrMissingDestination)
            } else if closure
                .iter()
                .any(|owner| matches!(owner, SlotOwner::Field(_)))
            {
                Some(CopyLendEligibilityDrop::C3FieldInClosure)
            } else if destination_flows_to_deallocator(program.tcx, &body, &destination_flow) {
                Some(CopyLendEligibilityDrop::S22FreeDestination)
            } else {
                live_outward_event(program, slots, fn_did, &body, &closure, &live_before)
            };
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
            A5PreledgerDeclineReason::ALL.map(A5PreledgerDeclineReason::label),
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

    #[test]
    fn copy_lend_production_stays_dormant_without_an_environment_switch() {
        assert_eq!(CopyLendMode::default(), CopyLendMode::Baseline);
        assert_eq!(CopyLendMode::default().label(), "baseline");
        assert_eq!(CopyLendMode::current(), CopyLendMode::Baseline);
    }

    #[test]
    fn dormant_a2_defaults_off() {
        assert_eq!(A2Mode::default(), A2Mode::Off);
        assert_eq!(A2Mode::default().label(), "off");
        assert_eq!(A2Mode::Off.with_override(A2Mode::current), A2Mode::Off);
    }
}
