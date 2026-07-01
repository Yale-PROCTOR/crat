//! Experimental unified borrow/ownership analysis.
//!
//! This module is intentionally self-contained while it is being built out. The
//! existing `borrow` and `ownership` analyses remain the production baseline.
#![allow(dead_code)]

use std::ops::Range;

mod domain;
mod infer;
pub(crate) mod borrow_verify;
pub mod coherence;
pub mod crate_slots;
pub(crate) mod sources;
pub mod resolve;
pub mod solver;
pub mod slots;
mod assoc;
mod call_graph;
#[cfg(not(test))]
mod ptr;
#[cfg(test)]
pub(crate) mod ptr;
mod struct_ctxt;
mod vec_vec;
pub mod ssa;

#[allow(unused_imports)]
pub use domain::SlotKind;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir::{Body, Local, Location};
use z3::ast::Bool;

use crate::{
    analyses::{
        borrow_ownership::{
            call_graph::FnSig,
            crate_slots::CrateSlots,
            infer::{FnSummary, InferCtxt},
            solver::{BoOwnDatabase, KindSolver, SlotRef},
            ssa::{
                FnResults,
                constraint::{Database, Gen, GlobalAssumptions, Var, initialize_local},
                consume::{Consume, initial_definitions},
                dom::compute_dominance_frontier,
                state::SSAState,
            },
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
/// via `model_kinds_relaxing`. Stats and source selectors aggregate across all
/// functions.
pub(crate) fn emit_crate_ownership_constraints<'tcx>(
    crate_ctxt: &CrateCtxt<'tcx>,
    slots: &CrateSlots,
    kind_solver: &KindSolver,
) -> anyhow::Result<(BoOwnEmissionStats, Vec<Bool>)> {
    let mut var_gen = Gen::new();
    let mut database = BoOwnDatabase::new(kind_solver.optimize());
    let global_assumptions = GlobalAssumptions::new(crate_ctxt, &mut var_gen, &mut database);

    // The full InterCtxt must be built (all signature vars allocated) before any
    // body is emitted, so a local call's `inter_ctxt[&callee]` resolves.
    let inter_ctxt = initial_crate_inter_ctxt(crate_ctxt, &mut var_gen, &mut database);

    // Emission order is irrelevant: bodies share the InterCtxt signature vars, so
    // z3 resolves cross-function (and recursive) flow when the joint system is
    // solved. No SCC iteration is needed at fixed precision 1.
    for &did in crate_ctxt.fns() {
        emit_fn_body_into(
            crate_ctxt,
            slots,
            kind_solver,
            &mut database,
            &mut var_gen,
            &global_assumptions,
            &inter_ctxt,
            did.expect_local(),
        );
    }

    let source_selectors = database.source_selectors().to_vec();
    let stats = BoOwnEmissionStats {
        z3_ast_len: database.z3_ast_len(),
        source_sink_emissions: database.source_sink_emissions(),
    };
    Ok((stats, source_selectors))
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
) {
    const B1_PRECISION: Precision = BO_PRECISION;

    let body_ref = crate_ctxt
        .tcx
        .mir_drops_elaborated_and_const_checked(fn_did)
        .borrow();
    let body = &*body_ref;
    let ssa_state = initial_ssa_state(crate_ctxt, body);

    let summary = {
        let mut rn = ssa::constraint::infer::Renamer::new(body, ssa_state, crate_ctxt.tcx);
        let mut infer_cx = InferCtxt::new(
            crate_ctxt,
            B1_PRECISION,
            body,
            database,
            var_gen,
            inter_ctxt,
            global_assumptions,
        );

        rn.go::<BoOwnershipProbe>(&mut infer_cx);
        FnSummary::new(rn, infer_cx)
    };

    // B2: solidify per-version ownership onto slots (depth 0; B1_PRECISION == 1).
    link_versions_to_slots(slots, fn_did, body, &summary, database, kind_solver);
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
                for var in [consume.r#use.clone().next(), consume.def.clone().next()]
                    .into_iter()
                    .flatten()
                {
                    depth0_owns.entry(local).or_default().push(var);
                }
            }
        }
    }

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
                r#use.zip(def)
                    .map(|(r#use, def)| Param::Output(Consume { r#use, def }))
            })
            .collect();

        fn_sigs.insert(did, FnSig { ret, args });
    }

    fn_sigs
}

fn initial_ssa_state<'tcx>(crate_ctxt: &CrateCtxt<'tcx>, body: &Body<'tcx>) -> SSAState {
    let dominance_frontier = compute_dominance_frontier(body);
    let definitions = initial_definitions(body, crate_ctxt);
    SSAState::new(body, &dominance_frontier, definitions)
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
