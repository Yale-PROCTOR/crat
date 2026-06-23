use std::ops::Range;

use itertools::izip;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::Body,
    ty::{Ty, TyCtxt, TyKind},
};

use super::{matcher, CallArgs, InferCtxt};
use crate::analyses::{
    borrow_ownership::{
        call_graph::Monotonicity,
        ptr::Measurable,
        ssa::{
            constraint::{infer::InferMode, Database, GlobalAssumptions, Var},
            consume::Consume,
        },
        struct_ctxt::StructCtxt,
        AnalysisKind, BoOwnershipProbe, CrateCtxt,
    },
    lattice::FlatSet,
};

mod libc;
mod library;

pub trait Boundary<'infercx, 'db, 'tcx>: AnalysisKind<'infercx, 'db, 'tcx> + Sized
where 'tcx: 'infercx
{
    fn call(
        infer_cx: &mut InferCtxt<'infercx, 'db, 'tcx, Self>,
        destination: Option<Consume<Range<Var>>>,
        args: &CallArgs,
        callee: DefId,
    );

    fn entry(
        crate_ctxt: &CrateCtxt<'tcx>,
        inter_ctxt: &Self::InterCtxt,
        global_assumptions: &GlobalAssumptions,
        database: &mut <Self as AnalysisKind<'infercx, 'db, 'tcx>>::DB,
        body: &Body<'tcx>,
        params: impl Iterator<Item = Option<Range<Var>>>,
    );

    fn exit(
        tcx: TyCtxt<'tcx>,
        inter_ctxt: &Self::InterCtxt,
        global_assumptions: &GlobalAssumptions,
        struct_ctxt: &StructCtxt<'tcx>,
        database: &mut Self::DB,
        body: &Body<'tcx>,
        args: impl Iterator<Item = Option<Range<Var>>>,
    );
}

impl<'infercx, 'db, 'tcx, Analysis> Boundary<'infercx, 'db, 'tcx> for Analysis
where
    'tcx: 'infercx,
    Analysis: AnalysisKind<'infercx, 'db, 'tcx>,
{
    default fn call(
        _: &mut InferCtxt<'infercx, 'db, 'tcx, Self>,
        _: Option<Consume<Range<Var>>>,
        _: &CallArgs,
        _: DefId,
    ) {
    }

    default fn entry(
        _: &CrateCtxt<'tcx>,
        _: &Analysis::InterCtxt,
        _: &GlobalAssumptions,
        _: &mut <Self as AnalysisKind<'infercx, 'db, 'tcx>>::DB,
        _: &Body<'tcx>,
        _: impl Iterator<Item = Option<Range<Var>>>,
    ) {
    }

    default fn exit(
        _: TyCtxt<'tcx>,
        _: &Self::InterCtxt,
        _: &GlobalAssumptions,
        _: &StructCtxt,
        _: &mut Self::DB,
        _: &Body<'tcx>,
        _: impl Iterator<Item = Option<Range<Var>>>,
    ) {
    }
}

impl<'infercx, 'db, 'tcx> Boundary<'infercx, 'db, 'tcx> for BoOwnershipProbe
where 'tcx: 'infercx
{
    fn call(
        infer_cx: &mut InferCtxt<'infercx, 'db, 'tcx, Self>,
        destination: Option<Consume<Range<Var>>>,
        args: &CallArgs,
        callee: DefId,
    ) {
        let fn_sig = infer_cx.tcx.fn_sig(callee).skip_binder();

        let mut params = infer_cx.inter_ctxt[&callee].iter();

        let ret = params.next().unwrap();

        // dest = ret ~> rho(dest) = 0, rho(dest') = rho(ret)
        if let Some(ret) = ret.clone()
            && let Some(dest) = destination
        {
            let output_ty = fn_sig.output().skip_binder();

            let ret = ret.expect_normal();

            matcher(
                output_ty,
                dest.transpose(),
                ret,
                infer_cx.struct_ctxt.unrestricted,
                infer_cx.database,
                |dest, ret, database| {
                    database
                        .push_assume::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                            (),
                            dest.r#use,
                            false,
                        );
                    database
                        .push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                            (),
                            dest.def,
                            ret,
                        );
                },
            );
        }

        let params_args = izip!(params, args, fn_sig.inputs().skip_binder()); // params.zip(args.iter());

        // para = arg ~> rho(para') + rho(arg') = rho(arg)
        for (param, arg, &ty) in params_args {
            if let Some(param) = param.clone()
                && let Some((arg, is_ref)) = arg.clone()
            {
                // B4: every arg is `Param::Output` (uniform two-slot Consume);
                // `Param::Normal` is only the RETURN (handled above). The old
                // `Param::Normal` arm — `push_linear` plus a c_void range-narrowing
                // "working around type cast" — became unreachable when
                // `output_params` was retired, so it is deleted. (If real-corpus
                // c_void local-call args ever need that narrowing for correct
                // classification, it must be re-added to this Output arm; the
                // `c_void_local_call_arg_emits` test guards that the path at least
                // stays panic-free and satisfiable.)
                let crate::analyses::borrow_ownership::Param::Output(output_param) = param else {
                    unreachable!("B4: call args are always Param::Output");
                };
                let mut output_param = output_param.transpose();
                assert!(output_param.size_hint().1.unwrap() > 0);
                let ty = if is_ref {
                    let _ = output_param.next().unwrap();
                    ty.builtin_deref(true).unwrap()
                } else {
                    ty
                };
                let arg = arg.transpose();

                matcher(
                    ty,
                    output_param,
                    arg,
                    infer_cx.struct_ctxt.unrestricted,
                    infer_cx.database,
                    |param, arg, database| {
                        database.push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                            (),
                            param.r#use,
                            arg.r#use,
                        );
                        database.push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                            (),
                            param.def,
                            arg.def,
                        );
                    },
                );
            }
        }
    }

    fn entry(
        crate_ctxt: &CrateCtxt<'tcx>,
        inter_ctxt: &<BoOwnershipProbe as AnalysisKind>::InterCtxt,
        global_assumptions: &GlobalAssumptions,
        database: &mut <BoOwnershipProbe as AnalysisKind>::DB,
        body: &Body<'tcx>,
        params: impl Iterator<Item = Option<Range<Var>>>,
    ) {
        let CrateCtxt {
            tcx,
            ref fn_ctxt,
            ref struct_ctxt,
        } = *crate_ctxt;
        let fn_sig = &inter_ctxt[&body.source.def_id()];

        for (input, sigs, ty) in itertools::izip!(
            params,
            fn_sig.iter().skip(1),
            body.args_iter().map(|local| body.local_decls[local].ty)
        ) {
            match (input, sigs) {
                (Some(input), Some(sigs)) => {
                    let input_sigs = sigs.clone().into_input();
                    assert_eq!(
                        input.size_hint().1.unwrap(),
                        input_sigs.size_hint().1.unwrap()
                    );
                    let measure = input.size_hint().1.unwrap() as u32;
                    let precision = struct_ctxt.absolute_precision(ty, measure);

                    for (input, sig) in input.clone().zip(input_sigs.clone()) {
                        database.push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                            (),
                            input,
                            sig,
                        )
                    }

                    // B4: every arg is `Param::Output`, so this is always the
                    // output path. The old `!is_output` branch (one global-assumption
                    // apply to the input, for non-output params) is unreachable after
                    // output_params retirement. These global assumptions are
                    // monotonicity-gated structural `EqMin` constraints — they SOLVE
                    // escape, they do not assert it.
                    let monotonicity = fn_ctxt.monotonicity(body.source.def_id());
                    let mut input_sigs = input_sigs;
                    let mut output_sigs = sigs.clone().into_output().unwrap();
                    let mut applier = GlobalAssumptionApplier {
                        global_assumptions,
                        struct_ctxt,
                        database,
                        tcx,
                    };

                    if !matches!(monotonicity, FlatSet::Bottom)
                        && !matches!(monotonicity, FlatSet::Elem(Monotonicity::Dealloc))
                    {
                        applier.apply(
                            ty,
                            None,
                            &mut std::iter::empty(),
                            &mut output_sigs,
                            precision,
                        );
                    }

                    if !matches!(monotonicity, FlatSet::Bottom)
                        && !matches!(monotonicity, FlatSet::Elem(Monotonicity::Alloc))
                    {
                        applier.apply(
                            ty,
                            None,
                            &mut std::iter::empty(),
                            &mut input_sigs,
                            precision,
                        );
                    }
                }
                (None, None) => {}
                _ => unreachable!(),
            }
        }
    }

    fn exit(
        tcx: TyCtxt<'tcx>,
        inter_ctxt: &Self::InterCtxt,
        global_assumptions: &GlobalAssumptions,
        struct_ctxt: &StructCtxt<'tcx>,
        database: &mut Self::DB,
        body: &Body<'tcx>,
        mut args: impl Iterator<Item = Option<Range<Var>>>,
    ) {
        let fn_sig = &inter_ctxt[&body.source.def_id()];

        let ret_arg = args.next().unwrap();
        let ret_param = fn_sig.ret.clone();

        if let Some((arg, param)) = ret_arg.zip(ret_param) {
            let param = param.expect_normal();
            assert_eq!(arg.size_hint().1.unwrap(), param.size_hint().1.unwrap());
            for (arg, param) in arg.zip(param.clone()) {
                database.push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                    (),
                    arg,
                    param,
                );
            }

            let mut param = param;
            let ty = body.return_ty();
            let measure = param.size_hint().1.unwrap() as u32;
            let precision = struct_ctxt.absolute_precision(ty, measure);

            GlobalAssumptionApplier {
                global_assumptions,
                struct_ctxt,
                database,
                tcx,
            }
            .apply(ty, None, &mut std::iter::empty(), &mut param, precision)
        }

        for (param, arg) in fn_sig.args.iter().cloned().zip(args) {
            if let Some((param, arg)) = param.zip(arg) {
                // B4: every arg is `Param::Output`, so `into_output()` is always
                // `Some` — write the actual back to the def signature var. The old
                // `else` finalize (`push_assume(arg, false)`) asserted escape=false
                // for non-output params; it was the load-bearing edit retired in
                // B4a (escape is now solved natively), and is unreachable here.
                let Some(param) = param.into_output() else {
                    unreachable!("B4: exit args are always Param::Output");
                };
                assert_eq!(arg.size_hint().1.unwrap(), param.size_hint().1.unwrap());
                for (arg, param) in arg.zip(param) {
                    database.push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                        (),
                        arg,
                        param,
                    );
                }
            }
        }
    }
}

impl<'infercx, 'db, 'tcx, Analysis> InferCtxt<'infercx, 'db, 'tcx, Analysis>
where
    'tcx: 'infercx,
    Analysis: AnalysisKind<'infercx, 'db, 'tcx>,
{
    fn unknown_call(&mut self, destination: Option<Consume<Range<Var>>>, args: &CallArgs) {
        if let Some(dest) = destination {
            <Analysis as InferMode>::borrow(self, dest);
        }
        for arg in args {
            if let Some((arg, _)) = arg.clone() {
                <Analysis as InferMode>::lend(self, arg);
            }
        }
    }
}

struct GlobalAssumptionApplier<'ga, 'sc, 'db, 'tcx, DB> {
    global_assumptions: &'ga GlobalAssumptions,
    struct_ctxt: &'sc StructCtxt<'tcx>,
    database: &'db mut DB,
    tcx: TyCtxt<'tcx>,
}

impl<'ga, 'sc, 'db, 'tcx, DB: Database> GlobalAssumptionApplier<'ga, 'sc, 'db, 'tcx, DB> {
    fn apply(
        &mut self,
        ty: Ty<'tcx>,
        mut dom: Option<Var>,
        field_ctxt: &mut dyn Iterator<Item = Var>,
        input: &mut impl Iterator<Item = Var>,
        mut precision: u8,
    ) {
        if precision == 0 {
            return;
        }

        let mut ty = ty;
        loop {
            if let Some(inner_ty) = ty.builtin_index() {
                ty = inner_ty;
                continue;
            }
            if let Some(ty_mut) = ty.builtin_deref(true) {
                let input = input.next().unwrap();
                if let Some((field, dom)) = field_ctxt.next().zip(dom) {
                    self.database
                        .push_eq_min::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                            (),
                            input,
                            field,
                            dom,
                        );
                }
                dom = Some(input);
                precision -= 1;
                if precision == 0 {
                    return;
                }
                ty = ty_mut;
                continue;
            }
            break;
        }

        if let TyKind::Adt(adt_def, subst) = ty.kind() {
            assert!(field_ctxt.next().is_none());
            if self.struct_ctxt.is_struct_of_concerned(&adt_def.did())
                && self.struct_ctxt.measure_adt(*adt_def, 0) > 0
            {
                let fields = self
                    .global_assumptions
                    .fields(self.struct_ctxt, &adt_def.did());
                for (mut field_ctxt, field_def) in itertools::izip!(fields, adt_def.all_fields()) {
                    let field_ty = field_def.ty(self.tcx, subst);
                    self.apply(field_ty, dom, &mut field_ctxt, input, precision)
                }
            }
        }
    }
}
