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
use super::coherence::add_coherence_tagging_uses;
use super::{
    BoOwnEmissionStats, CrateCtxt, SlotKind,
    a5_overlap::{
        A5Mode, A5World, AbiGuardDisposition, C9MarkKey, WholeProgramAttestation,
        WitnessMarkability, apply_coarse_constraints, plan_c9_marks,
    },
    a5_producer::{A5Plan, PlannedC9Mark, produce_a5_plan},
    borrow_verify::{
        verify_to_fixpoint_counting_with_flows,
        verify_to_fixpoint_counting_with_flows_and_copy_lends,
        verify_to_fixpoint_counting_with_flows_and_parameter_overlaps,
    },
    boundary_table::{self, Matcher, Role},
    coherence::{
        CopyLendPair, add_coherence, add_coherence_removal_only, add_coherence_with_copy_lends,
    },
    crate_slots::CrateSlots,
    emit_crate_ownership_constraints, emit_crate_ownership_constraints_with_copy_lends,
    l2::{MirLocationKey, SlotKey},
    mutability_facts::MutFacts,
    origin_flow::OriginFlowResults,
    origin_summary::OriginSummaries,
    resolve::{ResolvedSlot, resolve_place},
    slots::SlotOwner,
    solver::{KindSolver, Selectors, SlotRef},
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
    pub(crate) a2_mode: A2Mode,
    pub(crate) a2_killed_memberships: usize,
    pub(crate) a2_opaque_result_guards: usize,
    pub(crate) selectors: Selectors,
    pub(crate) eligibility: CopyLendEligibility,
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
    pub(crate) receipt: String,
    pub(crate) round_stats: super::borrow_verify::RoundStats,
    pub(crate) selector_sources: usize,
    pub(crate) selector_sinks: usize,
    pub(crate) emission_stats: BoOwnEmissionStats,
    pub(crate) construction_emit_elapsed: Duration,
    pub(crate) construction_coherence_elapsed: Duration,
    pub(crate) check_sat_count: usize,
    pub(crate) planned_c9_marks: BTreeSet<C9MarkKey>,
    pub(crate) producer_stats: super::a5_producer::A5ProducerStats,
}

const A5_PAIR_LEDGER_SHA256: &str =
    "16dac90cf269c5480e6f612e54733dd210e41393a879202c7138e93cd7d360e1";
const REPLAY_SAFE_DEFINITION: &str = "no incompatible access derived by precise replay with the effective parameter-overlap map injected; O2 closed-world frozen graph.";

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

fn a5_receipt(
    mode: A5Mode,
    plan: &A5Plan,
    retained: usize,
    retained_sites: usize,
    selected_model_sha256: &str,
) -> String {
    format!(
        "schema=bo-construction-v1\nstatus=ok\ndata=true\ncopy_lend_mode=baseline\n\
         a2_mode=off\na5_mode={}\na5_world={}\nunknown_caller_seeding=false\n\
         a5_abi_guard={}\na5_raw_pairs={}\na5_effective_pairs={}\n\
         a5_raw_site_pairs={}\na5_raw_site_mut_mut={}\na5_raw_site_mut_read_only={}\n\
         a5_raw_site_shared_shared={}\n\
         a5_planned_marks={}\na5_retained_marks={}\na5_retained_mark_sites={}\n\
         a5_producer=rustc-mir-current-v1\n\
         a5_foster_producer=MutFacts::from_program(mutability_analysis+SourceVarGroups::postprocess_mut_res)\n\
         a5_pair_ledger_sha256={A5_PAIR_LEDGER_SHA256}\nselected_model_sha256={}\n\
         a5_summary_sha256={}\nreplay_safe_definition={REPLAY_SAFE_DEFINITION}\n",
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
    )
}

pub(crate) fn baseline_a5_receipt(model: &FxHashMap<SlotRef, SlotKind>) -> String {
    let plan = A5Plan::baseline();
    a5_receipt(A5Mode::Baseline, &plan, 0, 0, &model_digest(model))
}

pub(crate) fn construct_bo_into(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    solver: &KindSolver,
    mode: CopyLendMode,
) -> anyhow::Result<BoConstruction> {
    let crate_ctxt = CrateCtxt::new(program);
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
    let coherence_elapsed = t.elapsed();
    Ok(BoConstruction {
        mode,
        a2_mode: A2Mode::Off,
        a2_killed_memberships: 0,
        a2_opaque_result_guards: 0,
        selectors,
        eligibility,
        stats,
        eligibility_elapsed,
        emit_elapsed,
        coherence_elapsed,
    })
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
        a2_mode: A2Mode::Off,
        a2_killed_memberships: 0,
        a2_opaque_result_guards: 0,
        selectors,
        eligibility: CopyLendEligibility::default(),
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
    verify_to_fixpoint_counting_with_flows_and_parameter_overlaps(
        program,
        slots,
        origins.native_flows(),
        solver,
        &construction.selectors,
        mut_facts,
        parameter_overlaps,
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
    match construction.mode {
        CopyLendMode::LendArm => verify_to_fixpoint_counting_with_flows_and_copy_lends(
            program,
            slots,
            origins.native_flows(),
            solver,
            &construction.selectors,
            mut_facts,
            &construction.eligibility.pairs,
        ),
        CopyLendMode::Baseline | CopyLendMode::RemovalOnly => {
            verify_to_fixpoint_counting_with_flows(
                program,
                slots,
                origins.native_flows(),
                solver,
                &construction.selectors,
                mut_facts,
            )
        }
    }
}

pub(crate) fn solve_bo_a5_config(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
) -> Option<VerifiedBo> {
    assert_eq!(
        CopyLendMode::current(),
        CopyLendMode::Baseline,
        "the A5 loop-2 matrix keeps dormant CopyLend semantics at baseline"
    );

    let baseline_solver = KindSolver::new(slots);
    let baseline_construction = construct_bo_into(
        program,
        slots,
        origins,
        mut_facts,
        &baseline_solver,
        CopyLendMode::Baseline,
    )
    .ok()?;
    let (baseline_model, baseline_round_stats) = verify_bo_construction_counting(
        program,
        slots,
        origins,
        &baseline_solver,
        &baseline_construction,
        mut_facts,
    );
    let baseline_model = baseline_model?;
    if mode == A5Mode::Baseline {
        let plan = if attestation == Some(WholeProgramAttestation::FrozenBenchmarkGraph) {
            A5Plan::baseline_attested()
        } else {
            A5Plan::baseline()
        };
        let selected_model_sha256 = model_digest(&baseline_model);
        return Some(VerifiedBo {
            receipt: a5_receipt(mode, &plan, 0, 0, &selected_model_sha256),
            mark_artifact: a5_mark_artifact(mode, &plan, &BTreeSet::new(), &selected_model_sha256),
            site_artifact: a5_site_artifact(mode, &plan),
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
            planned_c9_marks: BTreeSet::new(),
            producer_stats: plan.stats,
        });
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
    .ok()?;
    if matches!(plan.abi_guard, AbiGuardDisposition::Refused { .. }) {
        let selected_model_sha256 = model_digest(&baseline_model);
        return Some(VerifiedBo {
            receipt: a5_receipt(mode, &plan, 0, 0, &selected_model_sha256),
            mark_artifact: a5_mark_artifact(mode, &plan, &BTreeSet::new(), &selected_model_sha256),
            site_artifact: a5_site_artifact(mode, &plan),
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
            planned_c9_marks: plan
                .planned_marks
                .iter()
                .map(|mark| mark.key.clone())
                .collect(),
            producer_stats: plan.stats,
        });
    }

    let solver = KindSolver::new(slots);
    let construction = construct_bo_into(
        program,
        slots,
        origins,
        mut_facts,
        &solver,
        CopyLendMode::Baseline,
    )
    .ok()?;
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
            (model?, stats)
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
            (model?, stats)
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
    Some(VerifiedBo {
        receipt: a5_receipt(
            mode,
            &plan,
            retained_c9_marks.len(),
            retained_c9_plans.len(),
            &selected_model_sha256,
        ),
        mark_artifact: a5_mark_artifact(mode, &plan, &retained_c9_marks, &selected_model_sha256),
        site_artifact: a5_site_artifact(mode, &plan),
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
        planned_c9_marks: plan
            .planned_marks
            .iter()
            .map(|mark| mark.key.clone())
            .collect(),
        producer_stats: plan.stats,
    })
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
