//! Experimental unified borrow/ownership analysis.
//!
//! This module is intentionally self-contained while it is being built out. The
//! existing `borrow` and `ownership` analyses remain the production baseline.
#![allow(dead_code)]

use std::ops::Range;

pub(crate) mod a5_overlap;
pub(crate) mod a5_producer;
pub(crate) mod a5_snapshot_effects;
pub(crate) mod allocator_contract;
pub(crate) mod array_fields;
mod assoc;
pub(crate) mod borrow_engine;
pub(crate) mod borrow_verify;
pub(crate) mod boundary_table;
pub(crate) mod cache_contract;
mod call_graph;
pub mod coherence;
pub(crate) mod comparison;
pub(crate) mod construction;
pub mod crate_slots;
pub(crate) mod demand_evidence;
#[cfg(test)]
mod dependency_ratchet;
mod domain;
pub(crate) mod emission_guard;
pub(crate) mod era5_instruments;
#[cfg(test)]
mod era5_worker;
pub(crate) mod esc_minimal;
pub(crate) mod execution_guard;
pub(crate) mod export;
mod infer;
// era-5c report 040: the A1 spare-set, for the MIR-walk market count.
pub(crate) use infer::reseat_destinations;
pub(crate) mod l2;
pub(crate) mod licensing;
pub(crate) mod model_cache;
pub(crate) mod mutability_facts;
pub(crate) mod field_moves;
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
/// over-claiming borrowed struct pointers whose fields are malloc'd. See task doc
/// §9.11 (and §9.8 for the over-claim this avoids).
const BO_PRECISION: Precision = 2;

/// §NB1 — safety-monotonicity emission mode (the C1 cost ablation switch, A6).
/// `safe(x) ≡ ¬raw(x)`; safety monotonicity is `safe(target) ⇒ safe(each
/// traversed pointer layer)`, emitted PER ACCESS SITE (D2). It subsumes the
/// structural `i1-adjacency` chain clause (`¬(raw(d) ∧ own(d+1))`) — it also
/// forbids the `raw(shallow) ∧ ref(deep)` inversion the structural form permits
/// — and reaches the struct-field boundary the structural adjacency misses.
/// The three modes:
/// - `Off`: neither the chain clause nor the per-site walk.
/// - `Chain`: the structural `i1-adjacency` only — the pre-NB1 behavior.
/// - `PerSite` (default): the per-site walk, PLUS the structural `i1-adjacency`
///   kept alongside it PERMANENTLY. The walk does NOT subsume `i1-adjacency`:
///   the walk fires only on READ/borrow access sites (write destinations are
///   excluded — see `safety_mono`), so `i1-adjacency` still covers write-only
///   and never-dereferenced same-owner chains the walk never reaches. The
///   NB-plan's "delete `chain` after the differential confirms subsumption" is
///   therefore resolved the OTHER way — `chain` is load-bearing under `PerSite`
///   and stays. The ablation delta is still clean: `Chain` = `i1-adjacency`
///   only; `PerSite` = `i1-adjacency` + the read-site walk, so `per_site − chain`
///   isolates exactly the read-site walk's cost.
///
/// Read from the env var `CRAT_BO_SAFE_MONO ∈ {off, chain, per_site}`;
/// absent/unrecognized ⇒ the const default. Both the solver-build `i1-adjacency`
/// (`solver::add_universe`) and the per-body walk (`safety_mono::add_safety_mono`,
/// called from `coherence::add_coherence`) consult `current()`, so they always
/// agree. No test sets the env var, so fixtures always see the `PerSite` default
/// deterministically; the ablation sweep sets it in the shell for both runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SafeMonoMode {
    Off,
    Chain,
    PerSite,
}

impl SafeMonoMode {
    const DEFAULT: SafeMonoMode = SafeMonoMode::PerSite;

    pub(crate) fn current() -> SafeMonoMode {
        match std::env::var("CRAT_BO_SAFE_MONO").as_deref() {
            Ok("off") => SafeMonoMode::Off,
            Ok("chain") => SafeMonoMode::Chain,
            Ok("per_site") => SafeMonoMode::PerSite,
            _ => SafeMonoMode::DEFAULT,
        }
    }

    /// Stable label for reporting (bo_c1 row column).
    pub(crate) fn label(self) -> &'static str {
        match self {
            SafeMonoMode::Off => "off",
            SafeMonoMode::Chain => "chain",
            SafeMonoMode::PerSite => "per_site",
        }
    }
}

/// §NB1 (C4-ii, plumbing only) — STRONG ownership monotonicity: re-enable the
/// production `dominate`-style `own(deeper) ⇒ own(shallower)` push that
/// `infer::new_vars` deliberately dropped (the relaxation site). OFF by default;
/// the wiring exists so the C4-ii ablation can flip it without a code change.
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
    pub fn map<U>(self, f: impl Fn(Value) -> U) -> Param<U> {
        match self {
            Param::Output(output_param) => Param::Output(output_param.repack(f)),
            Param::Normal(param) => Param::Normal(f(param)),
        }
    }

    #[inline]
    pub fn expect_normal(self) -> Value {
        match self {
            Param::Normal(sigs) => sigs,
            Param::Output(..) => panic!("expect normal parameter"),
        }
    }

    #[cfg(test)]
    pub fn expect_output(self) -> Consume<Value> {
        match self {
            Param::Output(consume) => consume,
            Param::Normal(..) => panic!("expect output parameter"),
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
    fn analyze(crate_ctxt: CrateCtxt<'tcx>) -> anyhow::Result<Self::Results>;
}

type InterCtxt = FxHashMap<DefId, FnSig<Option<Param<Range<Var>>>>>;

struct BoOwnershipProbe;

impl<'analysis, 'db, 'tcx> AnalysisKind<'analysis, 'db, 'tcx> for BoOwnershipProbe {
    type DB = BoOwnDatabase<'db>;
    type InterCtxt = &'analysis InterCtxt;
    type Results = ();

    fn analyze(_crate_ctxt: CrateCtxt<'tcx>) -> anyhow::Result<Self::Results> {
        unimplemented!("B0 only forks ownership emission; B1 wires a real BO analysis")
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct BoOwnEmissionStats {
    pub z3_ast_len: usize,
    pub source_sink_emissions: usize,
}

/// B3b: crate-level interprocedural emission. Builds the full `InterCtxt` (a
/// signature for every crate function) into one shared `BoOwnDatabase`, then
/// emits every function body's constraints into that shared `KindSolver`. The
/// shared signature vars are the interprocedural linkage — z3 resolves
/// cross-function (and recursive) ownership flow when the joint system is solved
/// via `model_kinds_relaxing`. Stats and the retractable selectors (§NB-F:
/// malloc SOURCES and free/realloc SINKS, typed-split in `Selectors`)
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
    let mut var_gen = Gen::new();
    // §NB-R: hand the KindSolver's tracker (if any) to the database so the
    // ownership-version constraints are track-gated in tracked mode too.
    allocator_contract::prepare(
        crate_ctxt.tcx,
        &crate_ctxt
            .fns()
            .iter()
            .map(|did| did.expect_local())
            .collect::<Vec<_>>(),
    );
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
        facts.reader_inputs = licensing::readers::Inputs::collect(&program, slots);
        facts.reader_plan = licensing::readers::Plan::build(&facts.reader_inputs);
        facts.traversal_native = Some(licensing::traversal_native::collect(
            &program,
            slots,
            origins,
            &facts.reader_plan,
        ));
        facts.field_support_inputs = licensing::field_support::Inputs::collect(&program, slots);
        facts.fold_types = Some(licensing::fold_types::Inputs::collect(&program));
        facts.fold_declarations = Some(Vec::new());
        facts.caller_coverage = Some(licensing::caller_coverage::Coverage::collect(&program));
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
    });
    if let Some(tracker) = kind_solver.tracker() {
        tracker.set_context("global-assumptions");
    }
    let global_assumptions = GlobalAssumptions::new(crate_ctxt, &mut var_gen, &mut database);

    // The full InterCtxt must be built (all signature vars allocated) before any
    // body is emitted, so a local call's `inter_ctxt[&callee]` resolves.
    let inter_ctxt = initial_crate_inter_ctxt(crate_ctxt, &mut var_gen, &mut database);

    // Emission order is irrelevant: bodies share the InterCtxt signature vars, so
    // z3 resolves cross-function (and recursive) flow when the joint system is
    // solved. No SCC iteration is needed at fixed precision 1.
    for &did in crate_ctxt.fns() {
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
    }
    if let Some(tracker) = kind_solver.tracker() {
        tracker.set_context("nb0-eager-source");
    }

    // §NB0 (hoisted BB3-a): `¬ref(slot)` for every malloc-source slot, emitted
    // EAGERLY as a candidacy-independent domain invariant — a heap allocation is
    // owned memory, never a borrow, so no model (however early) may classify it
    // `Ref`. `Owning` and `Raw` both satisfy the clause: an unleaked source still
    // settles `Owning`, a leaked one `Raw`. Routed through `add_borrow_exclusion`
    // (NOT the BoOwnDatabase source/sink path), so `source_sink_emissions` and
    // the selector set are untouched. Replaces `verify_to_fixpoint`'s lazy
    // per-round BB3-a commit.
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
        comparison::record_guard(
            crate_ctxt.tcx,
            slots,
            slot,
            comparison::GuardRule::AllocationSource,
        );
    }

    // §NB4-4c: MAY-SUPPLY demotion over the NO-BORROW-ORIGIN set. A monotone `¬ref` on every
    // no-borrow-origin slot — base signature slots (args/returns) AND struct fields, per
    // `collect_no_borrow_origin_slots` (NO depth-0 arg tier — deferred). Emitted EAGERLY here
    // (candidacy-independent), mirroring the malloc-source `¬ref` loop above (the 3c-ii lesson).
    // `origins` is THREADED in (F3 split-brain fix): CHECK_REAL, explain_unsat, and every test see the
    // identical clause set.
    //
    // `¬ref`-ONLY, not `¬ref ∧ ¬own`: `summary.unknown` is "NO-BORROW-ORIGIN", not "opaque-poisoned"
    // (the malloc_only vs malloc_opaque ablation — `opaque(out)` adds nothing to the set), so it also
    // holds owned-heap `*out = malloc()` / `return malloc()` transfers. `¬ref` is SELF-DISCRIMINATING:
    // an owned slot keeps `Owning` via its source selector; an opaque RESULT loses `Ref` → `Raw`. A
    // uniform `¬own` over-demoted the owned transfers (9 tests). The may-overwrite `¬own` is
    // un-targetable from this set (the overwrite is not in `summary.unknown`) and DEFERS to the
    // effect-row/opaque-interaction bucket; see the task doc.
    if let Some(tracker) = kind_solver.tracker() {
        tracker.set_context("nb4-4c-may-supply-demotion");
    }
    let nullability = nullability::analyze(crate_ctxt.tcx, &fns, slots);
    for slot in origins::collect_no_borrow_origin_slots(origins, slots) {
        if !nullability.contains(&slot) {
            if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
                eprintln!("E5C may-supply-exclusion slot={slot:?}");
            }
            kind_solver.add_borrow_exclusion(Some(slot), &[]); // ¬ref (may-supply)
            comparison::record_guard(
                crate_ctxt.tcx,
                slots,
                slot,
                comparison::GuardRule::NoBorrowOrigin,
            );
        }
    }

    // E-R2: snapshot the Var -> Bool map before the database is dropped.
    database.emit_reference_effect_obligations()?;
    database.snapshot_version_asts();

    let selectors = Selectors::new_with_keys(
        database.source_selectors().to_vec(),
        database.source_keys().to_vec(),
        database.sink_selectors().to_vec(),
        database.sink_keys().to_vec(),
    );
    // L01^5 (i): a program with no sink can never be forced to own (W18). Under
    // the leak-parity waiver, prefer Box for its field slots. Pin-gated and
    // objective-only: no hard constraint changes, so nothing legal becomes illegal.
    if super::borrow_ownership::field_moves::leak_parity_admission()
        && selectors.sinks().is_empty()
    {
        kind_solver.prefer_owning_for_unsinked_fields(slots);
    }
    let stats = BoOwnEmissionStats {
        z3_ast_len: database.z3_ast_len(),
        source_sink_emissions: database.source_sink_emissions(),
    };
    drop(ownership_scope);
    drop(boundary_scope);
    drop(transfer_scope);
    drop(facts_scope);
    let facts = database.freeze_facts();
    if let Some(tracker) = kind_solver.tracker() {
        tracker.set_context("licensing-origin-admissibility");
    }
    // R351-3 pass 1: the facts are still carried — the construction downstream
    // is built from them — but not one of era-5b's constraints is emitted and
    // nothing is recorded into the entry. The gate sits at each emission site
    // rather than before them, because the facts themselves are structure, not
    // constraint.
    // R377-1: the return-port rule. It is emitted here rather than beside the
    // `¬ref` at the `AllocationSource` loop because its premise is read from the
    // licensing facts, which exist only after `freeze_facts`. Emission order is
    // irrelevant (the bodies share the InterCtxt signature vars), so the loop
    // above is left untouched and this adds rows rather than changing any.
    if licensing::facts::return_port()
        && let Some(frozen) = facts.licensing.as_ref()
    {
        let _ = frozen;
        if let Some(tracker) = kind_solver.tracker() {
            tracker.set_context("r377-return-port");
        }
        let origins = licensing::value_origins::ValueOrigins::build(&facts);
        let (admitted, _holds) = licensing::fold_caller::return_port_owning(&facts, &origins);
        for slot_key in admitted {
            if let Some(&slot) = facts.slot_refs.get(&slot_key) {
                // The refusal machinery stays authoritative: a slot some other
                // rule refuses ownership for yields and keeps the pin's kind.
                kind_solver.require_own(&slot_key, slot);
            }
        }
    }
    let joint = licensing::facts::Pass::current() == licensing::facts::Pass::Joint;
    let mut preferred_own = 0usize;
    for carrier in &facts
        .licensing
        .as_ref()
        .expect("frozen licensing facts")
        .no_ref_carriers
    {
        let slot = facts.slot_refs[&carrier.slot_key];
        // O-ORIGIN is independent of endpoint/grant selection. A refused
        // fresh responsibility cannot acquire an invented borrow lifetime.
        // R371-2: the repair arm withdraws this exclusion and leaves every
        // grant constraint below on.
        if joint
            && !licensing::facts::repair()
            && !std::env::var("CRAT_ERA5C_SKIP_FAMILY")
                .unwrap_or_default()
                .split(',')
                .any(|s| s.trim() == "no_ref_carriers")
        {
            kind_solver.add_borrow_exclusion(Some(slot), &[]);
            // L01⁶ (b) / R517-12: this slot's reference has just been refused,
            // so `raw ∨ own` is all that remains and only `raw` carries weight.
            // Prefer `own` where it is legal. Objective-only; report 034b §3
            // measured the market at 77 of 462 before the rule was written.
            if field_moves::own_prefer_local() {
                preferred_own += kind_solver.prefer_owning_for_refused_reference(slot) as usize;
            }
        }
    }
    // L01⁶ arm 3 half two (R518-2): with the finalization blanket gone, prefer
    // the NAMED locals as owners so the token is not smeared onto temporaries.
    if field_moves::finalize_soft() {
        let mut named = 0usize;
        for did in crate_ctxt.fns() {
            let fn_did = did.expect_local();
            let body = crate_ctxt
                .tcx
                .mir_drops_elaborated_and_const_checked(fn_did)
                .borrow();
            let Some(universe) = slots.fn_local_slots.get(&fn_did) else {
                continue;
            };
            let mut seen = rustc_data_structures::fx::FxHashSet::default();
            for info in &body.var_debug_info {
                let rustc_middle::mir::VarDebugInfoContents::Place(place) = info.value else {
                    continue;
                };
                if !place.projection.is_empty() || !seen.insert(place.local) {
                    continue;
                }
                if let Some(slot) = universe.slot_for_local_depth(place.local, 0)
                    && kind_solver.prefer_owning_for_named_local(SlotRef::Local(fn_did, slot))
                {
                    named += 1;
                }
            }
        }
        if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
            eprintln!("E5C l016-arm3: preferred own on {named} NAMED local slots");
        }
    }
    if field_moves::own_prefer_local() {
        // L01⁷ lever (b), report 043 / R536-4. L01⁶ preferred `own` on every
        // local slot and over-reached on CALLER-DERIVED values: tulip's 78
        // indicator-table formals (reached only through the `ti_indicators`
        // function-pointer table) and heman's seven exported write-then-return
        // formals with no caller settled Owning -- dragged there through local
        // copies (`_19 = copy _4`), returns (`_0 = copy pOut`) and pointers
        // loaded through them (`outputs[k]`). A formal with no allocation site
        // and no free is a LEND. So the preference skips every local whose
        // value derives from a formal; call RESULTS are not caller values, so a
        // caller receiving a constructor's allocation keeps the preference.
        let mut preferred_locals = 0usize;
        for did in crate_ctxt.fns() {
            let fn_did = did.expect_local();
            let Some(universe) = slots.fn_local_slots.get(&fn_did) else {
                continue;
            };
            let body = crate_ctxt.tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
            let caller = caller_derived_locals(&body, crate_ctxt.tcx);
            for index in 0..universe.len() {
                let id = slots::SlotId::from_u32(index.try_into().expect("slot index"));
                if let slots::SlotOwner::Local(local) = universe.slot(id).owner
                    && !caller.contains(&local)
                {
                    preferred_locals +=
                        kind_solver.prefer_owning_for_refused_reference(SlotRef::Local(fn_did, id))
                            as usize;
                }
            }
        }
        if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
            eprintln!(
                "E5C l016-b: preferred own on {preferred_own} refused-reference + {preferred_locals} non-caller local slots"
            );
        }
    }
    if field_moves::lend_formal() {
        // L01⁸, R545-2: a formal whose every closed-world actual is the address
        // of a stack or interior place is a LEND -- never `Owning`.
        let fns: Vec<_> = crate_ctxt
            .fns()
            .iter()
            .map(|did| did.expect_local())
            .collect();
        let mut forbidden = 0usize;
        for (fn_did, formal) in lend_formals(crate_ctxt.tcx, &fns) {
            let Some(universe) = slots.fn_local_slots.get(&fn_did) else {
                continue;
            };
            if let Some(id) = universe.slot_for_local_depth(formal, 0) {
                forbidden +=
                    kind_solver.forbid_lend_formal_own(SlotRef::Local(fn_did, id)) as usize;
            }
        }
        if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
            eprintln!("E5C lend-formal: forbade own on {forbidden} formal slots");
        }
    }
    if joint {
        // R467-2 (019 profile): per-family RSS, so libzahl says which joint-gated
        // family retains. Diagnosis only, behind CRAT_ERA5C_PROFILE.
        let profile = std::env::var_os("CRAT_ERA5C_PROFILE").is_some();
        let rss = || -> f64 {
            std::fs::read_to_string("/proc/self/statm")
                .ok()
                .and_then(|s| s.split_whitespace().nth(1).and_then(|p| p.parse::<f64>().ok()))
                .map(|pages| pages * 4096.0 / 1073741824.0)
                .unwrap_or(0.0)
        };
        let mut mark = rss();
        macro_rules! step {
            ($name:literal, $e:expr) => {{
                let value = $e;
                if profile {
                    let now = rss();
                    eprintln!("E5C_PROFILE {:<34} rss={:7.2} GiB  delta={:+7.2}", $name, now, now - mark);
                    mark = now;
                }
                value
            }};
        }
        // R467-2 diagnosis: CRAT_ERA5C_SKIP_FAMILY=<comma list> omits joint-gated
        // families so the one that drives the solver's blow-up can be named. Never
        // set in a measurement run; the verdicts are not valid with it on.
        let skipped = std::env::var("CRAT_ERA5C_SKIP_FAMILY").unwrap_or_default();
        let skip = |name: &str| skipped.split(',').any(|s| s.trim() == name);
        step!("start", ());
        if !skip("grants") {
            step!("apply_licensing_grants", kind_solver.apply_licensing_grants(&facts)?);
        }
        if !skip("transfers") {
            step!("block_incomplete_transfers", licensing::readers::block_incomplete_transfers(&facts, kind_solver));
        }
        if !skip("reader_field_support") {
            step!("constrain_reader_field_support", kind_solver.constrain_reader_field_support(&facts)?);
        }
        if !skip("reference_field_effects") {
            step!("constrain_reference_field_effects", kind_solver.constrain_reference_field_effects(&facts)?);
        }
        if !skip("first_permissions") {
            step!("constrain_first_permissions", kind_solver.constrain_first_permissions(&facts)?);
        }
        if !skip("traversal_calls") {
            step!("constrain_traversal_calls", kind_solver.constrain_traversal_calls(&facts)?);
        }
        if !skip("fold_callers") {
            step!("constrain_fold_callers", kind_solver.constrain_fold_callers(&facts)?);
        }
        // era-5c (R409-1): an allocation is released by its own allocator.
        step!("allocator_contract_pairing", kind_solver.constrain_allocator_contract_pairing(&facts));
        step!("record_ownership_facts", export::record_ownership_facts(&facts));
    }
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

    // B2: solidify per-version ownership onto slots (depth 0; B1_PRECISION == 1).
    link_versions_to_slots(slots, fn_did, body, &summary, database, kind_solver);
    Ok(())
}

/// B2 solidification linking: tie each local pointer slot's `own` bit to the
/// disjunction of that slot's per-version ownership Bools — the faithful
/// OR-latch from `ownership::solidify`. Only depth 0 is emitted by B1's
/// precision-1 driver, so only depth 0 is linked; inner depths are carried by
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
                // E-R2 capture: this loop already visits exactly the tuples the
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

/// B3b/B4: build a signature (ret + args) for *every* crate function into the
/// shared database, keyed by `DefId`. B4 retired the `output_params` input:
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
                // B4: no owning seed — escape is solved natively. A read-only
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
        // against this cap (see `BO_PRECISION` docs, §9.11).
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

/// L01⁷ lever (b), report 043: the locals whose value derives from a FORMAL --
/// the formals themselves, then anything assigned from them by `Use`/`Cast`
/// (including loads THROUGH a caller pointer, `x = copy (*p).f`), and the
/// result of a non-local call (`ptr::offset` and friends) taking one. These hold
/// the caller's storage; they are lends, never Box candidates.
/// era-5c R545-2: the closed-world LEND formals `(callee, formal)`. A formal
/// qualifies when its function is not `#[no_mangle]`, is never address-taken
/// (no fn-item constant outside a call's callee, in any fn body or static), is never reassigned, has at least one call site, and EVERY actual
/// traces back -- through single-definition copies and casts -- to the address
/// of a stack place or of an interior place: a field with index > 0 or a
/// constant index > 0 after the last `Deref`. `&*p`, a first field and a
/// runtime index are excluded: they may carry the allocation's own address,
/// which C may legally `free`.
pub(crate) fn lend_formals<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    fns: &[rustc_span::def_id::LocalDefId],
) -> Vec<(rustc_span::def_id::LocalDefId, rustc_middle::mir::Local)> {
    use rustc_data_structures::fx::{FxHashMap, FxHashSet};
    use rustc_hir::def::DefKind;
    use rustc_middle::{
        middle::codegen_fn_attrs::CodegenFnAttrFlags,
        mir::{
            Body, ConstOperand, Location, Operand, Place, ProjectionElem, Rvalue, StatementKind,
            Terminator, TerminatorKind, visit::Visitor,
        },
        ty::TyKind,
    };
    use rustc_span::def_id::{DefId, LocalDefId};

    struct AddressTaken<'a> {
        out: &'a mut FxHashSet<DefId>,
    }
    impl<'tcx> Visitor<'tcx> for AddressTaken<'_> {
        fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, _: Location) {
            if let TyKind::FnDef(def, _) = constant.const_.ty().kind() {
                self.out.insert(*def);
            }
        }

        fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
            if let TerminatorKind::Call { args, .. } = &terminator.kind {
                // the callee operand is a call, not an escape
                for arg in args.iter() {
                    self.visit_operand(&arg.node, location);
                }
            } else {
                self.super_terminator(terminator, location);
            }
        }
    }
    let mut address_taken = FxHashSet::default();
    for &f in fns {
        let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
        AddressTaken {
            out: &mut address_taken,
        }
        .visit_body(&body);
    }
    // Function-pointer tables are statics. Read their initializers from HIR:
    // building a static's CTFE MIR (`mir_for_ctfe`) STEALS its body, which later
    // passes read. Foreign statics have no initializer.
    struct FnPaths<'tcx, 'a> {
        typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
        out: &'a mut FxHashSet<DefId>,
    }
    impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for FnPaths<'tcx, '_> {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            if let rustc_hir::ExprKind::Path(qpath) = &expr.kind
                && let rustc_hir::def::Res::Def(DefKind::Fn, def) =
                    self.typeck.qpath_res(qpath, expr.hir_id)
            {
                self.out.insert(def);
            }
            rustc_hir::intravisit::walk_expr(self, expr);
        }
    }
    for def in tcx.hir_crate_items(()).definitions() {
        if matches!(tcx.def_kind(def), DefKind::Static { .. })
            && !tcx.is_foreign_item(def)
            && let Some(body_id) = tcx.hir_node_by_def_id(def).body_id()
        {
            let body = tcx.hir_body(body_id);
            let mut visitor = FnPaths {
                typeck: tcx.typeck(def),
                out: &mut address_taken,
            };
            rustc_hir::intravisit::Visitor::visit_expr(&mut visitor, body.value);
        }
    }

    fn assigned_once<'b, 'tcx>(
        body: &'b Body<'tcx>,
        local: rustc_middle::mir::Local,
    ) -> Option<&'b Rvalue<'tcx>> {
        let mut found = None;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                if let StatementKind::Assign(assign) = &statement.kind
                    && assign.0.local == local
                    && assign.0.projection.is_empty()
                {
                    if found.is_some() {
                        return None;
                    }
                    found = Some(&assign.1);
                }
            }
            if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
                && destination.local == local
            {
                return None;
            }
        }
        found
    }
    fn lend_place(place: &Place<'_>) -> bool {
        let last_deref = place
            .projection
            .iter()
            .rposition(|e| matches!(e, ProjectionElem::Deref));
        let Some(last_deref) = last_deref else {
            return true; // a stack place
        };
        // W49 fault (test builds only): the first-field exclusion dropped.
        #[cfg(test)]
        let first_field_counts =
            std::env::var("CRAT_E5C_W49_FAULT").as_deref() == Ok("first-field");
        #[cfg(not(test))]
        let first_field_counts = false;
        place.projection[last_deref + 1..].iter().any(|e| match e {
            ProjectionElem::Field(field, _) => field.index() > 0 || first_field_counts,
            ProjectionElem::ConstantIndex {
                offset, from_end, ..
            } => !from_end && *offset > 0,
            _ => false,
        })
    }
    fn actual_is_lend(body: &Body<'_>, actual: &Operand<'_>) -> bool {
        let (Operand::Copy(place) | Operand::Move(place)) = actual else {
            return false;
        };
        if !place.projection.is_empty() {
            return false;
        }
        let mut local = place.local;
        for _ in 0..16 {
            match assigned_once(body, local) {
                // `&raw mut *q` of a reference temporary `q = &mut (*h).f` (the
                // `&mut x as *mut` coercion): the address is q's -- follow it.
                Some(Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place))
                    if matches!(place.projection.as_slice(), [ProjectionElem::Deref])
                        && matches!(
                            assigned_once(body, place.local),
                            Some(Rvalue::RawPtr(..) | Rvalue::Ref(..))
                        ) =>
                {
                    local = place.local;
                }
                Some(Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place)) => {
                    return lend_place(place);
                }
                Some(
                    Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _)
                    | Rvalue::Use(Operand::Copy(p) | Operand::Move(p)),
                ) if p.projection.is_empty() => local = p.local,
                _ => return false,
            }
        }
        false
    }

    let local_fns: FxHashSet<LocalDefId> = fns.iter().copied().collect();
    let mut verdict: FxHashMap<(LocalDefId, usize), bool> = FxHashMap::default();
    for &caller in fns {
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        for data in body.basic_blocks.iter() {
            if let TerminatorKind::Call { func, args, .. } = &data.terminator().kind
                && let Some((def, _)) = func.const_fn_def()
                && let Some(callee) = def.as_local()
                && local_fns.contains(&callee)
            {
                for (index, arg) in args.iter().enumerate() {
                    let lend = actual_is_lend(&body, &arg.node);
                    *verdict.entry((callee, index)).or_insert(true) &= lend;
                }
            }
        }
    }
    let mut out: Vec<_> = verdict
        .into_iter()
        .filter(|&(_, lend)| lend)
        .filter_map(|((callee, index), _)| {
            if address_taken.contains(&callee.to_def_id())
                || tcx
                    .codegen_fn_attrs(callee)
                    .flags
                    .contains(CodegenFnAttrFlags::NO_MANGLE)
            {
                return None;
            }
            let body = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
            let formal = rustc_middle::mir::Local::from_usize(index + 1);
            let decl = body.local_decls.get(formal)?;
            if !decl.ty.is_raw_ptr() {
                return None;
            }
            let reassigned = body.basic_blocks.iter().any(|data| {
                data.statements.iter().any(|s| {
                    matches!(&s.kind, StatementKind::Assign(a)
                        if a.0.local == formal && a.0.projection.is_empty())
                }) || matches!(&data.terminator().kind,
                    TerminatorKind::Call { destination, .. } if destination.local == formal)
            });
            (!reassigned).then_some((callee, formal))
        })
        .collect();
    out.sort_by_key(|&(callee, formal)| (callee.local_def_index, formal));
    out
}

fn caller_derived_locals<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
) -> rustc_data_structures::fx::FxHashSet<rustc_middle::mir::Local> {
    use rustc_middle::mir::{Rvalue, StatementKind, TerminatorKind};
    let mut caller: rustc_data_structures::fx::FxHashSet<rustc_middle::mir::Local> =
        (1..=body.arg_count).map(rustc_middle::mir::Local::from_usize).collect();
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
            if let TerminatorKind::Call { func, args, destination, .. } = &data.terminator().kind
                && destination.projection.is_empty()
                && func.const_fn_def().is_some_and(|(callee, _)| !callee.is_local())
                && args.iter().any(|arg| arg.node.place().is_some_and(|p| caller.contains(&p.local)))
                && caller.insert(destination.local)
            {
                changed = true;
            }
        }
    }
    let _ = tcx;
    caller
}
