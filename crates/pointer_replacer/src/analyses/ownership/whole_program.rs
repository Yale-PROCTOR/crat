mod state;

use std::{
    ops::Range,
    sync::atomic::{AtomicBool, Ordering},
};

use anyhow::bail;
use either::Either::{self, Left, Right};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, Local, Location};

use self::state::{initial_inter_ctxt, initial_ssa_state, refine_state};
use super::{AnalysisKind, Ownership, Precision, total_deref_level};
use crate::analyses::{
    output_params::OutputParams,
    ownership::{
        CrateCtxt, Param,
        call_graph::FnSig,
        infer::{FnSummary, InferCtxt},
        ptr::Measurable,
        ssa::{
            AnalysisResults, FnResults,
            constraint::{
                Database, Gen, GlobalAssumptions, SatDatabase, Var, infer::Renamer,
                initialize_local,
            },
            consume::Consume,
            state::SSAState,
        },
        struct_ctxt::{RestrictedStructCtxt, StructCtxt},
    },
};

/// whole program analysis
pub enum WholeProgramAnalysis {}

static VERBOSE: AtomicBool = AtomicBool::new(false);

pub struct VerboseGuard(bool);

pub fn set_verbose(enabled: bool) -> VerboseGuard {
    VerboseGuard(VERBOSE.swap(enabled, Ordering::Relaxed))
}

impl Drop for VerboseGuard {
    fn drop(&mut self) {
        VERBOSE.store(self.0, Ordering::Relaxed);
    }
}

#[inline]
fn verbose() -> bool {
    VERBOSE.load(Ordering::Relaxed)
}

impl<'analysis, 'db, 'tcx> AnalysisKind<'analysis, 'db, 'tcx> for WholeProgramAnalysis {
    type DB = SatDatabase;
    type InterCtxt = &'analysis InterCtxt;
    type Results = WholeProgramResults<'tcx>;

    fn analyze(
        mut crate_ctxt: CrateCtxt<'tcx>,
        output_params: &OutputParams,
    ) -> anyhow::Result<Self::Results> {
        let required_precision = std::cmp::min(
            crate_ctxt.fns().iter().copied().fold(0, |acc, did| {
                let body = &*crate_ctxt
                    .tcx
                    .mir_drops_elaborated_and_const_checked(did.expect_local())
                    .borrow();
                std::cmp::max(acc, total_deref_level(body) + 1)
            }),
            3,
        );

        let started = std::time::Instant::now();

        // first stage
        let mut results = solve_crate(&mut crate_ctxt, Left((output_params, required_precision)))?;
        let mut passes = 1;
        print_model(passes, &results.0);

        // second stage
        for _ in 1..2 * required_precision {
            results = solve_crate(&mut crate_ctxt, Right(results))?;
            passes += 1;
            print_model(passes, &results.0);
        }

        if verbose() {
            println!(
                "ownership analysis: {:.3} s, {passes} passes, {} vars",
                started.elapsed().as_secs_f64(),
                results.0.len() - 1
            );
        }

        let (model, fn_locals, struct_fields) = results;

        Ok(WholeProgramResults {
            model,
            fn_locals,
            struct_fields,
            struct_ctxt: crate_ctxt.struct_ctxt,
        })
    }
}

pub struct FnLocals {
    fn_sigs: InterCtxt,
    fn_summaries: indexmap::IndexMap<DefId, (FnSummary, Precision)>,
}

pub type IntermediateResults = (Vec<Ownership>, FnLocals, GlobalAssumptions);

pub struct WholeProgramResults<'tcx> {
    model: Vec<Ownership>,
    fn_locals: FnLocals,
    struct_fields: GlobalAssumptions,
    struct_ctxt: StructCtxt<'tcx>,
}

impl<'tcx> WholeProgramResults<'tcx> {
    pub fn fields<'a>(&'a self, r#struct: &DefId) -> impl Iterator<Item = &'a [Ownership]> + 'a {
        self.struct_fields
            .fields(&self.struct_ctxt, r#struct)
            .map(|range| &self.model[range.start.index()..range.end.index()])
    }

    #[cfg(test)]
    pub fn precision(&self, did: &DefId) -> Precision {
        self.fn_locals.fn_summaries[did].1
    }

    #[cfg(test)]
    pub fn model(&self) -> &[Ownership] {
        &self.model
    }
}

/// Under the verbose flag, one pass's model as one line: `O` owning, `T` transient, `?` unknown.
fn print_model(pass: usize, model: &[Ownership]) {
    if verbose() {
        let model: String = model
            .iter()
            .map(|value| match value {
                Ownership::Owning => 'O',
                Ownership::Transient => 'T',
                Ownership::Unknown => '?',
            })
            .collect();
        println!("ownership model pass {pass}: {model}");
    }
}

struct SolveBodyCtxt<'a, 'tcx> {
    crate_ctxt: &'a CrateCtxt<'tcx>,
    inter_ctxt: &'a InterCtxt,
    global_assumptions: &'a GlobalAssumptions,
    var_gen: &'a mut Gen,
    database: &'a mut SatDatabase,
}

fn solve_body<'tcx>(
    body: &Body<'tcx>,
    ssa_state: SSAState,
    precision: Precision,
    ctxt: SolveBodyCtxt<'_, 'tcx>,
) -> anyhow::Result<(FnSummary, Precision)> {
    if precision == 0 {
        return Ok((
            FnSummary {
                fn_body_sig: rustc_index::IndexVec::new(),
                ssa_state: ssa_state.mk_dummy(),
            },
            precision,
        ));
    }

    let SolveBodyCtxt {
        crate_ctxt,
        inter_ctxt,
        global_assumptions,
        var_gen,
        database,
    } = ctxt;

    database.open_scope();

    let mut rn = Renamer::new(body, ssa_state, crate_ctxt.tcx);

    if verbose() {
        print!(
            "Solving {} with precision {}... ",
            crate_ctxt.tcx.def_path_str(body.source.def_id()),
            std::cmp::min(precision, crate_ctxt.struct_ctxt.max_ptr_chased()),
        );
    }

    let mut infer_cx = InferCtxt::new(
        crate_ctxt,
        precision,
        body,
        database,
        var_gen,
        inter_ctxt,
        global_assumptions,
    );

    rn.go::<WholeProgramAnalysis>(&mut infer_cx);

    let results = FnSummary::new(rn, infer_cx);

    match database.check_scope() {
        Some(false) => {
            if verbose() {
                println!("\u{274C}");
            }
            database.close_scope(false);
            Ok((results, precision - 1))
        }
        None => bail!("sat status: unknown"),
        Some(true) => {
            if verbose() {
                println!("\u{2705}");
            }
            database.close_scope(true);
            Ok((results, precision))
        }
    }
}

fn solve_crate(
    crate_ctxt: &mut CrateCtxt,
    previous_results: Either<(&OutputParams, Precision), IntermediateResults>,
) -> anyhow::Result<IntermediateResults> {
    let mut var_gen = Gen::new();

    let mut database = <WholeProgramAnalysis as AnalysisKind>::DB::new();

    let global_assumptions = GlobalAssumptions::new(&*crate_ctxt, &mut var_gen, &mut database);

    let mut fn_summaries = indexmap::IndexMap::default();
    fn_summaries.reserve(crate_ctxt.fns().len());

    let fn_sigs = match previous_results {
        Left((noalias_params, required_precision)) => {
            let inter_ctxt =
                initial_inter_ctxt(crate_ctxt, noalias_params, &mut var_gen, &mut database);
            for &did in crate_ctxt.fn_ctxt.fns() {
                let body = &*crate_ctxt
                    .tcx
                    .mir_drops_elaborated_and_const_checked(did.expect_local())
                    .borrow();
                let ssa_state = initial_ssa_state(crate_ctxt, body);
                let fn_summary = solve_body(
                    body,
                    ssa_state,
                    required_precision,
                    SolveBodyCtxt {
                        crate_ctxt,
                        inter_ctxt: &inter_ctxt,
                        global_assumptions: &global_assumptions,
                        var_gen: &mut var_gen,
                        database: &mut database,
                    },
                )?;
                fn_summaries.insert(did, fn_summary);
            }
            inter_ctxt
        }
        Right(previous_results) => {
            crate_ctxt.struct_ctxt.increase_precision(crate_ctxt.tcx);
            let (inter_ctxt, fns) = previous_results.1.refine(
                previous_results.0,
                crate_ctxt,
                &mut var_gen,
                &mut database,
            );
            for (did, ssa_state, precision) in fns {
                let body = &*crate_ctxt
                    .tcx
                    .mir_drops_elaborated_and_const_checked(did.expect_local())
                    .borrow();
                let fn_summary = solve_body(
                    body,
                    ssa_state,
                    precision,
                    SolveBodyCtxt {
                        crate_ctxt,
                        inter_ctxt: &inter_ctxt,
                        global_assumptions: &global_assumptions,
                        var_gen: &mut var_gen,
                        database: &mut database,
                    },
                )?;
                fn_summaries.insert(did, fn_summary);
            }
            inter_ctxt
        }
    };

    let model = retrieve_model(database, var_gen)?;

    let fn_locals = FnLocals {
        fn_sigs,
        fn_summaries,
    };

    Ok((model, fn_locals, global_assumptions))
}

fn retrieve_model(mut database: SatDatabase, var_gen: Gen) -> anyhow::Result<Vec<Ownership>> {
    let values = database.model(var_gen.next())?;
    let mut model = Vec::with_capacity(var_gen.next().index());

    assert_eq!(Var::MIN.index(), 1);

    model.push(Ownership::Unknown);
    model.extend(values.into_iter().map(Ownership::from));

    Ok(model)
}

impl<'analysis_results, 'tcx: 'analysis_results> AnalysisResults<'analysis_results>
    for WholeProgramResults<'tcx>
{
    type FnResults = (
        &'analysis_results FnSummary,
        &'analysis_results [Ownership],
        RestrictedStructCtxt<'analysis_results, 'tcx>,
    );
    type Param = Param<&'analysis_results [Ownership]>;
    type Value = Ownership;

    type FnSig = impl Iterator<Item = Option<Self::Param>>;

    fn fn_results(&'analysis_results self, r#fn: DefId) -> Option<Self::FnResults> {
        let (fn_summary, precision) = self.fn_locals.fn_summaries.get(&r#fn)?;
        Some((
            fn_summary,
            &self.model[..],
            self.struct_ctxt.with_max_precision(*precision),
        ))
    }

    fn fn_sig(&'analysis_results self, r#fn: DefId) -> Self::FnSig {
        get_fn_sig(&self.model, &self.fn_locals, r#fn)
    }
}

fn get_fn_sig<'a>(
    model: &'a [Ownership],
    fn_locals: &'a FnLocals,
    r#fn: DefId,
) -> impl Iterator<Item = Option<Param<&'a [Ownership]>>> + 'a {
    let fn_sigs = &fn_locals.fn_sigs[&r#fn];
    let ret = fn_sigs
        .ret
        .clone()
        .map(|sigs| sigs.map(|sigs| &model[sigs.start.index()..sigs.end.index()]));

    let args = fn_sigs.args.iter().map(|arg| {
        arg.clone()
            .map(|sigs| sigs.map(|sigs| &model[sigs.start.index()..sigs.end.index()]))
    });

    std::iter::once(ret).chain(args)
}

impl<'a, 'tcx> FnResults<'a>
    for (
        &'a FnSummary,
        &'a [Ownership],
        RestrictedStructCtxt<'a, 'tcx>,
    )
{
    type LocalResult = &'a [Ownership];

    type LocationResults = impl Iterator<Item = (Local, Consume<&'a [Ownership]>)>;

    #[inline]
    fn local_result(&self, local: Local, location: Location) -> Option<Consume<Self::LocalResult>> {
        let local_result = self.0.local_result(local, location)?;
        Some(local_result.map_valid(|sigs| &self.1[sigs.start.index()..sigs.end.index()]))
    }

    #[inline]
    fn location_results(&'a self, location: Location) -> Self::LocationResults {
        self.0.location_results(location).map(|(local, result)| {
            (
                local,
                result.map_valid(|sigs| &self.1[sigs.start.index()..sigs.end.index()]),
            )
        })
    }
}

pub type InterCtxt = FxHashMap<DefId, FnSig<Option<Param<Range<Var>>>>>;

impl FnLocals {
    pub fn refine<'tcx>(
        self,
        model: Vec<Ownership>,
        crate_ctxt: &CrateCtxt<'tcx>,
        var_gen: &mut Gen,
        database: &mut SatDatabase,
    ) -> (
        InterCtxt,
        impl Iterator<Item = (DefId, SSAState, Precision)> + 'tcx,
    ) {
        let mut inter_ctxt = FxHashMap::default();
        inter_ctxt.reserve(self.fn_sigs.len());

        for (did, original) in self.fn_sigs.into_iter() {
            let body = &*crate_ctxt
                .tcx
                .mir_drops_elaborated_and_const_checked(did.expect_local())
                .borrow();
            let precision = self.fn_summaries[&did].1;

            let fn_sig = original
                .iter()
                .zip(&body.local_decls)
                .map(|(original, local_decl)| {
                    // let Some(original) = original else { return None; };
                    // FIXME correctness?
                    let original = original.as_ref()?;
                    match original {
                        Param::Output(_) => {
                            let r#use = initialize_local(
                                local_decl,
                                var_gen,
                                database,
                                crate_ctxt.struct_ctxt.with_max_precision(precision),
                            )?;
                            assert!(!r#use.is_empty());
                            database
                                .push_assume::<crate::analyses::ownership::ssa::constraint::Debug>(
                                    (),
                                    r#use.start,
                                    true,
                                );
                            let def = initialize_local(
                                local_decl,
                                var_gen,
                                database,
                                crate_ctxt.struct_ctxt.with_max_precision(precision),
                            )?;
                            assert!(!def.is_empty());
                            database
                                .push_assume::<crate::analyses::ownership::ssa::constraint::Debug>(
                                    (),
                                    def.start,
                                    true,
                                );

                            Some(Param::Output(Consume { r#use, def }))
                        }
                        Param::Normal(_) => {
                            let now = initialize_local(
                                local_decl,
                                var_gen,
                                database,
                                crate_ctxt.struct_ctxt.with_max_precision(precision),
                            )?;

                            Some(Param::Normal(now))
                        }
                    }
                })
                .collect();

            inter_ctxt.insert(did, fn_sig);
        }

        let tcx = crate_ctxt.tcx;

        let state_iter =
            self.fn_summaries
                .into_iter()
                .map(move |(did, (fn_summary, precision))| {
                    let body = &*tcx
                        .mir_drops_elaborated_and_const_checked(did.expect_local())
                        .borrow();
                    (did, refine_state(body, fn_summary, &model), precision)
                });

        (inter_ctxt, state_iter)
    }
}
