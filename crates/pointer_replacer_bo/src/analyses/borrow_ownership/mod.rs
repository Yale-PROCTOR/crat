//! Experimental unified borrow/ownership analysis.
//!
//! This module is intentionally self-contained while it is being built out. The
//! existing `borrow` and `ownership` analyses remain the production baseline.

use std::ops::Range;

pub(crate) mod array_fields;
mod assoc;
pub(crate) mod borrow_engine;
pub(crate) mod borrow_verify;
pub(crate) mod boundary_table;
pub(crate) mod cache_contract;
mod call_graph;
#[cfg(test)]
pub(crate) mod code_fingerprint;
pub mod coherence;
pub(crate) mod comparison;
pub(crate) mod construction;
pub mod crate_slots;
pub(crate) mod demand_evidence;
#[cfg(test)]
mod dependency_ratchet;
mod domain;
pub(crate) mod esc_minimal;
pub(crate) mod execution_guard;
pub(crate) mod export;
mod infer;
pub(crate) mod overlap_producer;
pub(crate) mod overlap_snapshot_effects;
pub(crate) mod param_overlap;
// The call-result reseat destinations (`x = f(x)`) the exit finalization spares, for a
// MIR-walk count.
pub(crate) use infer::reseat_destinations;
#[cfg(test)]
mod copy_lend_guard_tests;
#[cfg(test)]
mod copy_lend_mut_tests;
pub(crate) mod copy_relax;
#[cfg(test)]
mod copy_relax_call_tests;
#[cfg(test)]
mod copy_relax_tests;
pub(crate) mod field_moves;
pub(crate) mod guarded_repair;
pub(crate) mod index_ranges;
#[cfg(test)]
mod index_ranges_tests;
#[cfg(test)]
mod kind_order_tests;
pub(crate) mod licensing;
pub(crate) mod model_cache;
pub(crate) mod move_store;
pub(crate) mod mutability_facts;
pub(crate) mod null_paths;
#[cfg(test)]
mod null_paths_tests;
pub(crate) mod nullability;
pub(crate) mod origin_evidence;
pub(crate) mod origin_flow;
pub(crate) mod origin_summary;
pub(crate) mod origins;
pub(crate) mod ownership_access;
pub(crate) mod ownership_boundary;
pub(crate) mod ownership_evidence;
pub(crate) mod ownership_occurrence;
pub(crate) mod portable_export;
pub(crate) mod proof_evidence;
pub(crate) mod protected_entry;
#[cfg(not(test))]
mod ptr;
#[cfg(test)]
pub(crate) mod ptr;
pub(crate) mod qualifier_facts;
pub(crate) mod raw_cause;
pub(crate) mod realloc;
pub(crate) mod realloc_ssa;
pub mod resolve;
pub(crate) mod retirement;
pub(crate) mod safety_mono;
pub(crate) mod slot_key;
pub mod slots;
pub mod solver;
pub(crate) mod source_events;
pub(crate) mod sources;
pub mod ssa;
pub(crate) mod strict_json;
mod struct_ctxt;
mod vec_vec;

#[allow(unused_imports)]
pub use domain::SlotKind;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir::{Body, Local, Location};
use z3::ast::Bool;

use crate::{
    analyses::borrow_ownership::{
        call_graph::FnSig,
        crate_slots::CrateSlots,
        infer::{FnSummary, InferCtxt},
        solver::{BoOwnDatabase, KindSolver, Selectors, SlotRef},
        ssa::{
            FnResults,
            constraint::{Database, Gen, GlobalAssumptions, Var, initialize_local},
            consume::{Consume, initial_definitions},
            dom::compute_dominance_frontier,
            state::SSAState,
        },
    },
    utils::rustc::RustProgram,
};

pub type Precision = u8;

/// BO analysis precision (pointer-chain depth modeled). At precision 2 a depth-1
/// pointer-chain ownership var exists, which the caller-side out-param escape
/// (`make(&raw mut local){ *out = malloc }`) flows through. The signature
/// (`INIT_PRECISION`), body (`B1_PRECISION`), and `struct_ctxt` (`max_ptr_chased`,
/// raised in `CrateCtxt::new`) MUST move in lockstep — the two consts alone are a
/// no-op against the `max_ptr_chased` cap. The `field ⟹ parent` suppression in
/// `GlobalAssumptionApplier::apply` is REQUIRED at precision ≥ 2 to avoid
/// over-claiming borrowed struct pointers whose fields are malloc'd.
const BO_PRECISION: Precision = 2;

/// STRONG ownership monotonicity (plumbing only): re-enable the
/// production `dominate`-style `own(deeper) ⇒ own(shallower)` push that
/// `infer::new_vars` deliberately dropped (the relaxation site). OFF by default;
/// the wiring exists so an ablation can flip it without a code change.
/// No behavior when false.
pub(crate) const STRONG_MONO: bool = false;

#[derive(Clone, Debug)]
enum Param<Var> {
    Output(Consume<Var>),
    Normal(Var),
}

#[cfg(not(debug_assertions))]
const _: () = assert!(
    std::mem::size_of::<
        Option<Param<std::ops::Range<crate::analyses::borrow_ownership::ssa::constraint::Var>>>,
    >() == 16
);

impl<Value> Param<Value> {
    #[inline]
    pub fn expect_normal(self) -> Value {
        match self {
            Param::Normal(sigs) => sigs,
            Param::Output(..) => panic!("expect normal parameter"),
        }
    }

    #[inline]
    pub fn into_input(self) -> Value {
        match self {
            Param::Output(Consume { r#use, .. }) => r#use,
            Param::Normal(normal) => normal,
        }
    }

    #[inline]
    pub fn into_output(self) -> Option<Value> {
        if let Param::Output(Consume { def, .. }) = self {
            Some(def)
        } else {
            None
        }
    }
}

pub(crate) trait AnalysisKind<'analysis, 'db, 'tcx> {
    /// Analysis results
    type Results;
    /// Interprocedural context
    type InterCtxt;
    type DB: Database;
}

type InterCtxt = FxHashMap<DefId, FnSig<Option<Param<Range<Var>>>>>;

struct BoOwnershipProbe;

impl<'analysis, 'db, 'tcx> AnalysisKind<'analysis, 'db, 'tcx> for BoOwnershipProbe {
    type DB = BoOwnDatabase<'db>;
    type InterCtxt = &'analysis InterCtxt;
    type Results = ();
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct BoOwnEmissionStats {
    pub z3_ast_len: usize,
    pub source_sink_emissions: usize,
}

/// Crate-level interprocedural emission. Builds the full `InterCtxt` (a
/// signature for every crate function) into one shared `BoOwnDatabase`, then
/// emits every function body's constraints into that shared `KindSolver`. The
/// shared signature vars are the interprocedural linkage — z3 resolves
/// cross-function (and recursive) ownership flow when the joint system is solved
/// via `model_kinds_relaxing`. Stats and the retractable selectors
/// (malloc SOURCES and free/realloc SINKS, typed-split in `Selectors`)
/// aggregate across all functions.
pub(crate) fn emit_crate_ownership_constraints<'tcx>(
    crate_ctxt: &CrateCtxt<'tcx>,
    slots: &CrateSlots,
    origins: &origin_summary::OriginSummaries,
    kind_solver: &KindSolver,
) -> anyhow::Result<(BoOwnEmissionStats, Selectors)> {
    emit_crate_ownership_constraints_impl(crate_ctxt, slots, origins, kind_solver, None)
}

pub(crate) fn emit_crate_ownership_constraints_with_copy_lends<'tcx>(
    crate_ctxt: &CrateCtxt<'tcx>,
    slots: &CrateSlots,
    origins: &origin_summary::OriginSummaries,
    kind_solver: &KindSolver,
    copy_lends: &FxHashSet<coherence::CopyLendPair>,
) -> anyhow::Result<(BoOwnEmissionStats, Selectors)> {
    emit_crate_ownership_constraints_impl(crate_ctxt, slots, origins, kind_solver, Some(copy_lends))
}

fn emit_crate_ownership_constraints_impl<'tcx>(
    crate_ctxt: &CrateCtxt<'tcx>,
    slots: &CrateSlots,
    origins: &origin_summary::OriginSummaries,
    kind_solver: &KindSolver,
    copy_lends: Option<&FxHashSet<coherence::CopyLendPair>>,
) -> anyhow::Result<(BoOwnEmissionStats, Selectors)> {
    let inventory = source_events::current().unwrap_or_else(|| {
        let program = RustProgram {
            tcx: crate_ctxt.tcx,
            functions: crate_ctxt
                .fns()
                .iter()
                .map(|did| did.expect_local())
                .collect(),
            structs: Vec::new(),
        };
        std::sync::Arc::new(source_events::collect(&program))
    });
    let _source_scope = source_events::enter_inventory(&inventory);
    crate::phase_log::mark("own:licensing_facts", "start", "");
    crate::analysis_budget::check("own:licensing_facts")?;
    let mut var_gen = Gen::new();
    // Hand the KindSolver's tracker (if any) to the database so the
    // ownership-version constraints are track-gated in tracked mode too.
    let mut database = BoOwnDatabase::new(kind_solver.optimize(), kind_solver.tracker());
    let facts_scope = database.activate_facts();
    let transfer_scope = ownership_occurrence::reset();
    let boundary_scope = ownership_boundary::call_arguments(None);
    let ownership_scope = ownership_evidence::construction();
    licensing::facts::record(|facts| {
        let program = RustProgram {
            tcx: crate_ctxt.tcx,
            functions: crate_ctxt
                .fns()
                .iter()
                .map(|did| did.expect_local())
                .collect(),
            structs: Vec::new(),
        };
        for &function in &program.functions {
            facts.source_occurrences.insert(
                program.tcx.def_path_str(function),
                origin_evidence::occurrences(&program, slots, function),
            );
        }
        crate::phase_log::mark("own:reader_inputs", "start", "");
        facts.reader_inputs = licensing::readers::Inputs::collect(&program, slots);
        crate::phase_log::mark("own:reader_inputs", "end", "");
        crate::phase_log::mark("own:reader_plan", "start", "");
        facts.reader_plan = licensing::readers::Plan::build(&facts.reader_inputs);
        crate::phase_log::mark("own:reader_plan", "end", "");
        crate::phase_log::mark("own:lend_plan", "start", "");
        facts.lend_plan = licensing::lend::collect(&program);
        crate::phase_log::mark("own:lend_plan", "end", "");
        crate::phase_log::mark("own:traversal_native", "start", "");
        facts.traversal_native = Some(licensing::traversal_native::collect(
            &program,
            slots,
            origins,
            &facts.reader_plan,
        ));
        crate::phase_log::mark("own:traversal_native", "end", "");
        crate::phase_log::mark("own:field_support_inputs", "start", "");
        facts.field_support_inputs = licensing::field_support::Inputs::collect(&program, slots);
        crate::phase_log::mark("own:field_support_inputs", "end", "");
        crate::phase_log::mark("own:fold_types", "start", "");
        facts.fold_types = Some(licensing::fold_types::Inputs::collect(&program));
        crate::phase_log::mark("own:fold_types", "end", "");
        facts.fold_declarations = Some(Vec::new());
        crate::phase_log::mark("own:caller_coverage", "start", "");
        facts.caller_coverage = Some(licensing::caller_coverage::Coverage::collect(&program));
        crate::phase_log::mark("own:caller_coverage", "end", "");
        crate::phase_log::mark("own:slot_refs", "start", "");
        facts.frame_attested = licensing::stack_entry::current_world()
            == licensing::stack_entry::CallWorld::ClosedProgram;
        for (&function, universe) in &slots.fn_local_slots {
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            facts.unit_locals.extend(
                body.local_decls
                    .iter_enumerated()
                    .filter(|(_, declaration)| declaration.ty.is_unit())
                    .map(|(local, _)| (program.tcx.def_path_str(function), local.as_u32())),
            );
            for index in 0..universe.len() {
                let id = slots::SlotId::from_u32(index.try_into().expect("slot index"));
                let slot = universe.slot(id);
                let slots::SlotOwner::Local(local) = slot.owner else { unreachable!() };
                let key = slot_key::local_key(program.tcx, function, local.as_usize(), slot.depth);
                if slot.depth == 0
                    && matches!(
                        body.local_decls[local].ty.kind(),
                        rustc_middle::ty::TyKind::RawPtr(..)
                    )
                {
                    facts
                        .raw_pointer_heads
                        .push(licensing::value_origins::RawHead {
                            function: program.tcx.def_path_str(function),
                            local: local.as_u32(),
                            slot_key: key.clone(),
                        });
                }
                assert!(
                    facts
                        .slot_refs
                        .insert(key, SlotRef::Local(function, id))
                        .is_none()
                );
            }
        }
        facts.unit_locals.sort();
        facts
            .raw_pointer_heads
            .sort_by(|a, b| a.slot_key.cmp(&b.slot_key));
        for index in 0..slots.field_slots.len() {
            let id = slots::SlotId::from_u32(index.try_into().expect("field slot index"));
            let slot = slots.field_slots.slot(id);
            let slots::SlotOwner::Field(field) = slot.owner else { unreachable!() };
            let key =
                slot_key::field_key(program.tcx, field.struct_did, field.field_index, slot.depth);
            assert!(facts.slot_refs.insert(key, SlotRef::Field(id)).is_none());
        }
        crate::phase_log::mark("own:slot_refs", "end", "");
    });
    crate::phase_log::mark("own:licensing_facts", "end", "");
    crate::phase_log::mark("own:global_assumptions", "start", "");
    crate::analysis_budget::check("own:global_assumptions")?;
    if let Some(tracker) = kind_solver.tracker() {
        tracker.set_context("global-assumptions");
    }
    let global_assumptions = GlobalAssumptions::new(crate_ctxt, &mut var_gen, &mut database);
    crate::phase_log::mark("own:global_assumptions", "end", "");
    crate::phase_log::mark("own:inter_ctxt", "start", "");
    crate::analysis_budget::check("own:inter_ctxt")?;

    // The full InterCtxt must be built (all signature vars allocated) before any
    // body is emitted, so a local call's `inter_ctxt[&callee]` resolves.
    let inter_ctxt = initial_crate_inter_ctxt(crate_ctxt, &mut var_gen, &mut database);
    crate::phase_log::mark("own:inter_ctxt", "end", "");
    crate::phase_log::mark("own:bodies", "start", "");
    crate::analysis_budget::check("own:bodies")?;
    let total = crate_ctxt.fns().len();

    // Emission order is irrelevant: bodies share the InterCtxt signature vars, so
    // z3 resolves cross-function (and recursive) flow when the joint system is
    // solved. No SCC iteration is needed at fixed precision 1.
    for (index, &did) in crate_ctxt.fns().iter().enumerate() {
        crate::analysis_budget::check("own:bodies")?;
        let probe = crate::phase_log::Probe::begin();
        if let Some(tracker) = kind_solver.tracker() {
            tracker.set_context(&crate_ctxt.tcx.def_path_str(did));
        }
        emit_fn_body_into(
            crate_ctxt,
            slots,
            kind_solver,
            &mut database,
            &mut var_gen,
            &global_assumptions,
            &inter_ctxt,
            did.expect_local(),
            copy_lends,
        )?;
        crate::phase_log::Probe::end(probe, "own:bodies", index, total, || {
            let body = crate_ctxt
                .tcx
                .mir_drops_elaborated_and_const_checked(did.expect_local())
                .borrow();
            format!(
                "{} {} z3_ast_len={}",
                crate_ctxt.tcx.def_path_str(did),
                crate::phase_log::body_size(&body),
                database.z3_ast_len()
            )
        });
    }
    crate::phase_log::mark(
        "own:bodies",
        "end",
        &format!("z3_ast_len={}", database.z3_ast_len()),
    );
    crate::phase_log::mark("own:malloc_sources", "start", "");
    crate::analysis_budget::check("own:malloc_sources")?;
    if let Some(tracker) = kind_solver.tracker() {
        tracker.set_context("nb0-eager-source");
    }

    // `¬ref(slot)` for every malloc-source slot, emitted
    // EAGERLY as a candidacy-independent domain invariant — a heap allocation is
    // owned memory, never a borrow, so no model (however early) may classify it
    // `Ref`. `Owning` and `Raw` both satisfy the clause: an unleaked source still
    // settles `Owning`, a leaked one `Raw`. Routed through `add_borrow_exclusion`
    // (NOT the BoOwnDatabase source/sink path), so `source_sink_emissions` and
    // the selector set are untouched. Emitted here rather than as a lazy per-round
    // commit in `verify_to_fixpoint`.
    let fns: Vec<_> = crate_ctxt.fns().iter().map(|d| d.expect_local()).collect();
    let malloc_sources = match copy_lends {
        Some(copy_lends) => sources::collect_malloc_source_slots_with_copy_lends(
            crate_ctxt.tcx,
            &fns,
            slots,
            copy_lends,
        ),
        None => sources::collect_malloc_source_slots(crate_ctxt.tcx, &fns, slots),
    };
    for slot in malloc_sources {
        kind_solver.add_borrow_exclusion(Some(slot), &[]);
        raw_cause::note_eager(&kind_solver, "allocation-source");
        comparison::record_guard(
            crate_ctxt.tcx,
            slots,
            slot,
            comparison::GuardRule::AllocationSource,
        );
    }

    // MAY-SUPPLY demotion over the NO-BORROW-ORIGIN set. A monotone `¬ref` on every
    // no-borrow-origin slot — base signature slots (args/returns) AND struct fields, per
    // `collect_no_borrow_origin_slots` (NO depth-0 arg tier — deferred). Emitted EAGERLY here
    // (candidacy-independent), mirroring the malloc-source `¬ref` loop above. `origins` is
    // THREADED in so CHECK_REAL, explain_unsat, and every test see the identical clause set.
    //
    // `¬ref`-ONLY, not `¬ref ∧ ¬own`: `summary.unknown` is "NO-BORROW-ORIGIN", not "opaque-poisoned"
    // (`opaque(out)` adds nothing to the set), so it also
    // holds owned-heap `*out = malloc()` / `return malloc()` transfers. `¬ref` is SELF-DISCRIMINATING:
    // an owned slot keeps `Owning` via its source selector; an opaque RESULT loses `Ref` → `Raw`. A
    // uniform `¬own` over-demoted the owned transfers (9 tests). The may-overwrite `¬own` is
    // un-targetable from this set (the overwrite is not in `summary.unknown`) and DEFERS to the
    // effect-row/opaque-interaction work.
    crate::phase_log::mark("own:malloc_sources", "end", "");
    if let Some(tracker) = kind_solver.tracker() {
        tracker.set_context("nb4-4c-may-supply-demotion");
    }
    crate::phase_log::mark("own:nullability", "start", "");
    crate::analysis_budget::check("own:nullability")?;
    let nullability = nullability::analyze(crate_ctxt.tcx, &fns, slots);
    crate::phase_log::mark("own:nullability", "end", "");
    crate::phase_log::mark("own:no_borrow_origin", "start", "");
    crate::analysis_budget::check("own:no_borrow_origin")?;
    for slot in origins::collect_no_borrow_origin_slots(origins, slots) {
        if !nullability.contains(&slot) {
            kind_solver.add_borrow_exclusion(Some(slot), &[]); // ¬ref (may-supply)
            raw_cause::note_eager(&kind_solver, "may-supply");
            comparison::record_guard(
                crate_ctxt.tcx,
                slots,
                slot,
                comparison::GuardRule::NoBorrowOrigin,
            );
        }
    }

    // Snapshot the Var -> Bool map before the database is dropped.
    crate::phase_log::mark("own:no_borrow_origin", "end", "");
    crate::phase_log::mark("own:reference_effect_obligations", "start", "");
    crate::analysis_budget::check("own:reference_effect_obligations")?;
    database.emit_reference_effect_obligations()?;
    crate::phase_log::mark("own:reference_effect_obligations", "end", "");
    crate::phase_log::mark("own:snapshot_version_asts", "start", "");
    crate::analysis_budget::check("own:snapshot_version_asts")?;
    database.snapshot_version_asts();
    crate::phase_log::mark("own:snapshot_version_asts", "end", "");

    let selectors = Selectors::new_with_keys(
        database.source_selectors().to_vec(),
        database.source_keys().to_vec(),
        database.sink_selectors().to_vec(),
        database.sink_keys().to_vec(),
    );
    let stats = BoOwnEmissionStats {
        z3_ast_len: database.z3_ast_len(),
        source_sink_emissions: database.source_sink_emissions(),
    };
    drop(ownership_scope);
    drop(boundary_scope);
    drop(transfer_scope);
    drop(facts_scope);
    crate::phase_log::mark("own:freeze_facts", "start", "");
    crate::analysis_budget::check("own:freeze_facts")?;
    let facts = database.freeze_facts()?;
    crate::phase_log::mark("own:freeze_facts", "end", "");
    crate::phase_log::mark("own:return_port", "start", "");
    crate::analysis_budget::check("own:return_port")?;
    if let Some(tracker) = kind_solver.tracker() {
        tracker.set_context("licensing-origin-admissibility");
    }
    // The licensing facts are still carried — the construction downstream
    // is built from them — but not one of the licensing constraints is emitted and
    // nothing is recorded into the entry. The gate sits at each emission site
    // rather than before them, because the facts themselves are structure, not
    // constraint.
    // The return-port rule. It is emitted here rather than beside the
    // `¬ref` at the `AllocationSource` loop because its premise is read from the
    // licensing facts, which exist only after `freeze_facts`. Emission order is
    // irrelevant (the bodies share the InterCtxt signature vars), so the loop
    // above is left untouched and this adds rows rather than changing any.
    if let Some(frozen) = facts.licensing.as_ref() {
        let _ = frozen;
        if let Some(tracker) = kind_solver.tracker() {
            tracker.set_context("r377-return-port");
        }
        // Relay main/388 walls 3+4 (R1363-1): `return_port:<sub>` marks inside this step only.
        let (admitted, _holds) = crate::phase_log::with_sub_marks(|| {
            let started = std::time::Instant::now();
            let origins = licensing::value_origins::ValueOrigins::build(&facts);
            crate::phase_log::sub("return_port:origins", "end", || {
                format!("wall={:.1}s", started.elapsed().as_secs_f64())
            });
            licensing::fold_caller::return_port_owning(&facts, &origins)
        });
        for slot_key in admitted {
            if let Some(&slot) = facts.slot_refs.get(&slot_key) {
                // The refusal machinery stays authoritative: a slot some other
                // rule refuses ownership for yields and keeps the pin's kind.
                kind_solver.require_own(&slot_key, slot);
            }
        }
    }
    crate::phase_log::mark("own:return_port", "end", "");
    for carrier in &facts
        .licensing
        .as_ref()
        .expect("frozen licensing facts")
        .no_ref_carriers
    {
        let slot = facts.slot_refs[&carrier.slot_key];
        // A no-ref carrier's exclusion is independent of endpoint/grant selection. A refused
        // fresh responsibility cannot acquire an invented borrow lifetime.
        kind_solver.add_borrow_exclusion(Some(slot), &[]);
        raw_cause::note_eager(&kind_solver, "no-ref-carrier");
    }
    crate::phase_log::mark("own:licensing_grants", "start", "");
    crate::analysis_budget::check("own:licensing_grants")?;
    kind_solver.apply_licensing_grants(&facts)?;
    crate::phase_log::mark("own:licensing_grants", "end", "");
    crate::phase_log::mark("own:block_incomplete_transfers", "start", "");
    crate::analysis_budget::check("own:block_incomplete_transfers")?;
    licensing::readers::block_incomplete_transfers(&facts, kind_solver);
    crate::phase_log::mark("own:block_incomplete_transfers", "end", "");
    crate::phase_log::mark("own:reader_field_support", "start", "");
    crate::analysis_budget::check("own:reader_field_support")?;
    kind_solver.constrain_reader_field_support(&facts)?;
    crate::phase_log::mark("own:reader_field_support", "end", "");
    crate::phase_log::mark("own:reference_field_effects", "start", "");
    crate::analysis_budget::check("own:reference_field_effects")?;
    kind_solver.constrain_reference_field_effects(&facts)?;
    crate::phase_log::mark("own:reference_field_effects", "end", "");
    crate::phase_log::mark("own:first_permissions", "start", "");
    crate::analysis_budget::check("own:first_permissions")?;
    kind_solver.constrain_first_permissions(&facts)?;
    crate::phase_log::mark("own:first_permissions", "end", "");
    crate::phase_log::mark("own:traversal_calls", "start", "");
    crate::analysis_budget::check("own:traversal_calls")?;
    kind_solver.constrain_traversal_calls(&facts)?;
    crate::phase_log::mark("own:traversal_calls", "end", "");
    crate::phase_log::mark("own:fold_callers", "start", "");
    crate::analysis_budget::check("own:fold_callers")?;
    kind_solver.constrain_fold_callers(&facts)?;
    crate::phase_log::mark("own:fold_callers", "end", "");
    crate::phase_log::mark("own:record_ownership_facts", "start", "");
    crate::analysis_budget::check("own:record_ownership_facts")?;
    export::record_ownership_facts(&facts);
    crate::phase_log::mark("own:record_ownership_facts", "end", "");
    kind_solver.set_ownership_facts(facts);
    Ok((stats, selectors))
}

/// Emit one function body's BO constraints into the shared `database`/`KindSolver`
/// and solidify its per-version ownership onto slots. The sole body-emission path,
/// called once per function by `emit_crate_ownership_constraints`; `inter_ctxt`
/// must already contain a signature for every callee this body can reach.
fn emit_fn_body_into<'tcx>(
    crate_ctxt: &CrateCtxt<'tcx>,
    slots: &CrateSlots,
    kind_solver: &KindSolver,
    database: &mut BoOwnDatabase<'_>,
    var_gen: &mut Gen,
    global_assumptions: &GlobalAssumptions,
    inter_ctxt: &InterCtxt,
    fn_did: LocalDefId,
    copy_lends: Option<&FxHashSet<coherence::CopyLendPair>>,
) -> anyhow::Result<()> {
    const B1_PRECISION: Precision = BO_PRECISION;
    let _ownership_function = ownership_evidence::function(|| crate_ctxt.tcx.def_path_str(fn_did));

    let body_ref = crate_ctxt
        .tcx
        .mir_drops_elaborated_and_const_checked(fn_did)
        .borrow();
    let body = &*body_ref;
    let mut definitions = initial_definitions(body, crate_ctxt);
    let inventory = source_events::current().expect("carried source inventory");
    let realloc_plans =
        realloc_ssa::plan_body(crate_ctxt, body, &mut definitions, &inventory.reallocations)
            .map_err(|error| anyhow::anyhow!("realloc ownership coverage: {error:?}"))?;
    realloc_ssa::constrain_coverage_holds(crate_ctxt, body, slots, kind_solver, &realloc_plans);
    let ssa_state = SSAState::new(body, &compute_dominance_frontier(body), definitions);
    let copy_lend_guards = copy_lends
        .map(|pairs| coherence::copy_lend_guards_for_body(kind_solver, slots, fn_did, body, pairs))
        .unwrap_or_default();
    let field_reader_guards = licensing::facts::read(|facts| {
        licensing::readers::guards_for_body(facts, kind_solver, fn_did, body)
    })
    .unwrap_or_default();

    let summary = {
        let mut rn = ssa::constraint::infer::Renamer::new(body, ssa_state, crate_ctxt.tcx)
            .with_realloc_plans(realloc_plans.clone());
        let mut infer_cx = InferCtxt::new(
            crate_ctxt,
            B1_PRECISION,
            body,
            database,
            var_gen,
            inter_ctxt,
            global_assumptions,
            &copy_lend_guards,
        )
        .with_realloc_plans(realloc_plans)
        .with_field_reader_guards(field_reader_guards);

        rn.go::<BoOwnershipProbe>(&mut infer_cx);
        FnSummary::new(rn, infer_cx)
    };

    licensing::coverage::record_body(
        body,
        &summary,
        ptr::Measurable::measure(
            &crate_ctxt.struct_ctxt.with_max_precision(B1_PRECISION),
            body.local_decls[rustc_middle::mir::RETURN_PLACE].ty,
            0,
        ) as usize,
    );

    // Solidify per-version ownership onto slots (depth 0; B1_PRECISION == 1).
    link_versions_to_slots(slots, fn_did, body, &summary, database, kind_solver);
    Ok(())
}

/// Solidification linking: tie each local pointer slot's `own` bit to the
/// disjunction of that slot's per-version ownership Bools — the faithful
/// OR-latch from `ownership::solidify`. Only depth 0 is emitted by the
/// precision-1 body driver (`B1_PRECISION`), so only depth 0 is linked; inner depths are carried by
/// `coherence`.
fn link_versions_to_slots<'tcx>(
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    summary: &FnSummary,
    database: &BoOwnDatabase<'_>,
    kind_solver: &KindSolver,
) {
    let Some(universe) = slots.fn_local_slots.get(&fn_did) else {
        return;
    };

    // Collect, per local, the depth-0 ownership Vars over every consume site
    // (mirrors solidify.rs:225-236: OR the `use`/`def` ownership across sites).
    let mut depth0_owns: FxHashMap<Local, Vec<Var>> = FxHashMap::default();
    for (block, bbdata) in body.basic_blocks.iter_enumerated() {
        // Statements plus the terminator location, matching production's bound
        // (`len + terminator.is_some()`); a block may lack a terminator.
        for statement_index in 0..bbdata.statements.len() + bbdata.terminator.is_some() as usize {
            let location = Location {
                block,
                statement_index,
            };
            for (local, consume) in summary.location_results(location) {
                let use_var = consume.r#use.clone().next();
                let def_var = consume.def.clone().next();
                // Capture: this loop already visits exactly the tuples the
                // export needs, and the `Location` association is discarded
                // immediately below when the vars are ORed into `depth0_owns`.
                // Recording-only; a no-op unless a capture scope is active.
                export::record_version_site(
                    fn_did,
                    local,
                    location,
                    use_var.filter(|var| !summary.realloc_ghosts.contains(var)),
                    def_var.filter(|var| !summary.realloc_ghosts.contains(var)),
                );
                for var in [use_var, def_var].into_iter().flatten() {
                    depth0_owns.entry(local).or_default().push(var);
                }
            }
        }
    }

    for version in &summary.realloc_versions {
        depth0_owns.entry(version.local).or_default().extend(
            version
                .use_var
                .into_iter()
                .chain(std::iter::once(version.def_var)),
        );
    }
    export::record(|capture| {
        capture
            .realloc_version_sites
            .extend(summary.realloc_versions.iter().cloned())
    });

    // Only locals with at least one collected version var are linked; a slot
    // whose local is never consumed is left free (the soft objective makes it
    // non-owning). Production's `Transient` baseline would hard-link such a slot
    // to `own=false`; we defer that parity refinement to avoid forcing UNSAT on
    // slots coherence might legitimately tie to an owning value.
    for (local, vars) in depth0_owns {
        let Some(slot_id) = universe.slot_for_local_depth(local, 0) else {
            continue;
        };
        let slot = SlotRef::Local(fn_did, slot_id);
        let owns: Vec<&Bool> = vars.iter().map(|&var| database.own_bool(var)).collect();
        kind_solver.link_own(slot, &Bool::or(&owns));
    }
}

/// Build a signature (ret + args) for *every* crate function into the
/// shared database, keyed by `DefId`. The `output_params` input is not used:
/// every pointer ARG is uniformly two-slot `Consume(use+def)` so the solver
/// decides escape natively (relaxed monotonicity), rather than a precomputed
/// output-param flag. The RETURN stays `Param::Normal` (single slot). These
/// signature vars are the interprocedural linkage consulted by
/// `Boundary::{call,entry,exit}`.
fn initial_crate_inter_ctxt<'tcx>(
    crate_ctxt: &CrateCtxt<'tcx>,
    var_gen: &mut Gen,
    database: &mut impl Database,
) -> InterCtxt {
    const INIT_PRECISION: Precision = BO_PRECISION;

    let mut fn_sigs = FxHashMap::default();
    fn_sigs.reserve(crate_ctxt.fns().len());
    for &did in crate_ctxt.fns() {
        let body_ref = crate_ctxt
            .tcx
            .mir_drops_elaborated_and_const_checked(did.expect_local())
            .borrow();
        let body = &*body_ref;

        let mut local_decls = body.local_decls.iter_enumerated();
        let (_, return_local_decl) = local_decls.next().unwrap();
        let ret = initialize_local(
            return_local_decl,
            var_gen,
            database,
            crate_ctxt.struct_ctxt.with_max_precision(INIT_PRECISION),
        )
        .map(Param::Normal);

        let args = local_decls
            .take(body.arg_count)
            .map(|(_local, local_decl)| {
                let r#use = initialize_local(
                    local_decl,
                    var_gen,
                    database,
                    crate_ctxt.struct_ctxt.with_max_precision(INIT_PRECISION),
                );
                let def = initialize_local(
                    local_decl,
                    var_gen,
                    database,
                    crate_ctxt.struct_ctxt.with_max_precision(INIT_PRECISION),
                );
                // No owning seed — escape is solved natively. A read-only
                // param settles to Ref via the soft objective; `*out = malloc`
                // settles to Ref-over-Owning. Hard-seeding here would force every
                // param Owning (regressing read-only/borrowed caller storage).
                r#use
                    .zip(def)
                    .map(|(r#use, def)| Param::Output(Consume { r#use, def }))
            })
            .collect();

        fn_sigs.insert(did, FnSig { ret, args });
    }

    fn_sigs
}

pub struct CrateCtxt<'tcx> {
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    fn_ctxt: call_graph::CallGraph,
    struct_ctxt: struct_ctxt::StructCtxt<'tcx>,
}

impl<'tcx> CrateCtxt<'tcx> {
    pub fn new(program: &RustProgram<'tcx>) -> Self {
        let fns = program
            .functions
            .iter()
            .map(|did| did.to_def_id())
            .collect::<Vec<_>>();
        let structs = program
            .structs
            .iter()
            .map(|did| did.to_def_id())
            .collect::<Vec<_>>();

        // Raise `max_ptr_chased` to `BO_PRECISION` so a depth-1 pointer-chain
        // ownership var is created for the caller-side out-param escape. `new`
        // already applies one `increase_precision` (→ depth 1), so bump the
        // remainder; the `INIT_PRECISION`/`B1_PRECISION` consts alone are a no-op
        // against this cap (see the `BO_PRECISION` docs).
        let mut struct_ctxt = struct_ctxt::StructCtxt::new(program.tcx, &structs);
        for _ in 1..BO_PRECISION {
            struct_ctxt.increase_precision(program.tcx);
        }
        CrateCtxt {
            tcx: program.tcx,
            fn_ctxt: call_graph::CallGraph::new(program.tcx, &fns),
            struct_ctxt,
        }
    }

    #[inline]
    pub fn fns(&self) -> &[rustc_hir::def_id::DefId] {
        self.fn_ctxt.fns()
    }
}

#[cfg(test)]
pub(crate) mod wrapper_fault_tests;

/// The locals whose value derives from a FORMAL --
/// the formals themselves, then anything assigned from them by `Use`/`Cast`
/// (including loads THROUGH a caller pointer, `x = copy (*p).f`), and the
/// result of a non-local call (`ptr::offset` and friends) taking one. These hold
/// the caller's storage; they are lends, never Box candidates.
fn caller_derived_locals<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
) -> rustc_data_structures::fx::FxHashSet<rustc_middle::mir::Local> {
    use rustc_middle::mir::{Rvalue, StatementKind, TerminatorKind};
    let mut caller: rustc_data_structures::fx::FxHashSet<rustc_middle::mir::Local> = (1..=body
        .arg_count)
        .map(rustc_middle::mir::Local::from_usize)
        .collect();
    let mut changed = true;
    while changed {
        changed = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else { continue };
                let (target, rvalue) = &**assign;
                let operand = match rvalue {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand,
                    _ => continue,
                };
                if let Some(source) = operand.place()
                    && target.projection.is_empty()
                    && caller.contains(&source.local)
                    && caller.insert(target.local)
                {
                    changed = true;
                }
            }
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &data.terminator().kind
                && destination.projection.is_empty()
                && func
                    .const_fn_def()
                    .is_some_and(|(callee, _)| !callee.is_local())
                && args
                    .iter()
                    .any(|arg| arg.node.place().is_some_and(|p| caller.contains(&p.local)))
                && caller.insert(destination.local)
            {
                changed = true;
            }
        }
    }
    let _ = tcx;
    caller
}
