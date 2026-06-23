//! Experimental unified borrow/ownership analysis.
//!
//! This module is intentionally self-contained while it is being built out. The
//! existing `borrow` and `ownership` analyses remain the production baseline.
#![allow(dead_code)]

use std::ops::Range;

mod domain;
mod infer;
pub mod coherence;
pub mod crate_slots;
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
                constraint::{Database, Debug, Gen, GlobalAssumptions, Var, initialize_local},
                consume::{Consume, initial_definitions},
                dom::compute_dominance_frontier,
                state::SSAState,
            },
        },
        output_params::OutputParams,
    },
    utils::rustc::RustProgram,
};

pub type Precision = u8;

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

    pub fn is_output(&self) -> bool {
        matches!(self, Param::Output(..))
    }
}

pub(crate) trait AnalysisKind<'analysis, 'db, 'tcx> {
    /// Analysis results
    type Results;
    /// Interprocedural context
    type InterCtxt;
    type DB: Database;
    fn analyze(
        crate_ctxt: CrateCtxt<'tcx>,
        output_params: &OutputParams,
    ) -> anyhow::Result<Self::Results>;
}

type InterCtxt = FxHashMap<DefId, FnSig<Option<Param<Range<Var>>>>>;

struct BoOwnershipProbe;

impl<'analysis, 'db, 'tcx> AnalysisKind<'analysis, 'db, 'tcx> for BoOwnershipProbe {
    type DB = BoOwnDatabase<'db>;
    type InterCtxt = &'analysis InterCtxt;
    type Results = ();

    fn analyze(
        _crate_ctxt: CrateCtxt<'tcx>,
        _output_params: &OutputParams,
    ) -> anyhow::Result<Self::Results> {
        unimplemented!("B0 only forks ownership emission; B1 wires a real BO analysis")
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct BoOwnEmissionStats {
    pub z3_ast_len: usize,
    pub source_sink_emissions: usize,
}

pub(crate) fn emit_single_fn_ownership_constraints<'tcx>(
    crate_ctxt: &CrateCtxt<'tcx>,
    output_params: &OutputParams,
    slots: &CrateSlots,
    kind_solver: &KindSolver,
    fn_did: LocalDefId,
) -> anyhow::Result<BoOwnEmissionStats> {
    if !crate_ctxt.fns().contains(&fn_did.to_def_id()) {
        anyhow::bail!(
            "function {} is not in borrow_ownership CrateCtxt",
            crate_ctxt.tcx.def_path_str(fn_did.to_def_id())
        );
    }

    const B1_PRECISION: Precision = 1;

    let body_ref = crate_ctxt
        .tcx
        .mir_drops_elaborated_and_const_checked(fn_did)
        .borrow();
    let body = &*body_ref;
    let mut var_gen = Gen::new();
    let mut database = BoOwnDatabase::new(kind_solver.optimize());
    let global_assumptions = GlobalAssumptions::new(crate_ctxt, &mut var_gen, &mut database);
    let inter_ctxt =
        initial_single_fn_inter_ctxt(crate_ctxt, output_params, body, &mut var_gen, &mut database);
    let ssa_state = initial_ssa_state(crate_ctxt, body);

    let summary = {
        let mut rn = ssa::constraint::infer::Renamer::new(body, ssa_state, crate_ctxt.tcx);
        let mut infer_cx = InferCtxt::new(
            crate_ctxt,
            B1_PRECISION,
            body,
            &mut database,
            &mut var_gen,
            &inter_ctxt,
            &global_assumptions,
        );

        rn.go::<BoOwnershipProbe>(&mut infer_cx);
        FnSummary::new(rn, infer_cx)
    };

    // B2: solidify per-version ownership onto slots (depth 0; B1_PRECISION == 1).
    link_versions_to_slots(slots, fn_did, body, &summary, &database, kind_solver);

    Ok(BoOwnEmissionStats {
        z3_ast_len: database.z3_ast_len(),
        source_sink_emissions: database.source_sink_emissions(),
    })
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

fn initial_single_fn_inter_ctxt<'tcx>(
    crate_ctxt: &CrateCtxt<'tcx>,
    output_params: &OutputParams,
    body: &Body<'tcx>,
    var_gen: &mut Gen,
    database: &mut impl Database,
) -> InterCtxt {
    const INIT_PRECISION: Precision = 1;

    let mut local_decls = body.local_decls.iter_enumerated();
    let (_, return_local_decl) = local_decls.next().unwrap();
    let ret = initialize_local(
        return_local_decl,
        var_gen,
        database,
        crate_ctxt.struct_ctxt.with_max_precision(INIT_PRECISION),
    )
    .map(Param::Normal);

    let output_params = output_params.get(&body.source.def_id().expect_local());
    let args = local_decls
        .take(body.arg_count)
        .map(|(local, local_decl)| {
            if output_params.is_some_and(|params| params.contains(local)) {
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
                r#use.zip(def).map(|(r#use, def)| {
                    database.push_assume::<Debug>((), r#use.start, true);
                    database.push_assume::<Debug>((), def.start, true);
                    Param::Output(Consume { r#use, def })
                })
            } else {
                initialize_local(
                    local_decl,
                    var_gen,
                    database,
                    crate_ctxt.struct_ctxt.with_max_precision(INIT_PRECISION),
                )
                .map(Param::Normal)
            }
        })
        .collect();

    let mut inter_ctxt = FxHashMap::default();
    inter_ctxt.insert(body.source.def_id(), FnSig { ret, args });
    inter_ctxt
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

        CrateCtxt {
            tcx: program.tcx,
            fn_ctxt: call_graph::CallGraph::new(program.tcx, &fns),
            struct_ctxt: struct_ctxt::StructCtxt::new(program.tcx, &structs),
        }
    }

    #[inline]
    pub fn fns(&self) -> &[rustc_hir::def_id::DefId] {
        self.fn_ctxt.fns()
    }
}
