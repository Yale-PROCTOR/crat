use std::ops::Range;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, Body, ClearCrossCrate, Local, LocalInfo, Location, Operand,
        Place, PlaceElem, ProjectionElem,
    },
    ty::{AdtDef, Ty, TyCtxt, TyKind},
};
use rustc_span::source_map::Spanned;
use rustc_type_ir::TyKind::FnDef;
use smallvec::SmallVec;
use z3::ast::Bool;

use self::boundary::Boundary;
use super::{AnalysisKind, Precision};
use crate::analyses::borrow_ownership::{
    CrateCtxt,
    assoc::AssocExt,
    ptr::{Measurable, decompose_ty},
    solver::{OwnAssumeSite, with_own_assume_site},
    ssa::{
        FnResults,
        constraint::{
            Database, Gen, GlobalAssumptions, Var,
            infer::{InferMode, Renamer},
            initialize_local,
        },
        consume::Consume,
        join_points::PhiNode,
        state::{SSAIdx, SSAState},
    },
    struct_ctxt::{RestrictedStructCtxt, StructCtxt},
};

mod aggregate;
mod boundary;
mod realloc_transition;

pub type LocalSig = Range<Var>;
pub type FnBodySig<LocalSig> = IndexVec<Local, IndexVec<SSAIdx, LocalSig>>;

pub struct FnSummary {
    pub fn_body_sig: FnBodySig<LocalSig>,
    pub ssa_state: SSAState,
    pub(crate) realloc_versions: Vec<super::export::ReallocVersionSite>,
    pub(crate) realloc_ghosts: FxHashSet<Var>,
}

impl FnSummary {
    pub fn new<'analysis, 'db, 'tcx, Kind: AnalysisKind<'analysis, 'db, 'tcx>>(
        rn: Renamer,
        infer_cx: InferCtxt<'analysis, 'db, 'tcx, Kind>,
    ) -> Self {
        FnSummary {
            fn_body_sig: infer_cx.fn_body_sig,
            ssa_state: rn.state,
            realloc_versions: infer_cx.realloc_versions,
            realloc_ghosts: infer_cx.realloc_ghosts,
        }
    }
}

impl<'a> FnResults<'a> for FnSummary {
    type LocalResult = LocalSig;

    type LocationResults = impl Iterator<Item = (Local, Consume<LocalSig>)> + 'a;

    #[inline]
    fn local_result(&self, local: Local, location: Location) -> Option<Consume<LocalSig>> {
        let consume_chain = &self.ssa_state.consume_chain;
        let consumes = consume_chain.of_location(location);
        let consume = consumes.get_by_key(&local)?;
        Some(consume.map_valid(|ssa_idx| {
            self.fn_body_sig[local]
                .get(ssa_idx)
                .cloned()
                .or_else(|| {
                    tracing::debug!(
                        "missing local sig for {:?} at {:?} with ssa {:?}; falling back to last known sig",
                        local,
                        location,
                        ssa_idx
                    );
                    self.fn_body_sig[local].raw.last().cloned()
                })
                .unwrap_or_else(|| {
                    tracing::debug!(
                        "missing all local sigs for {:?} at {:?}; returning empty fallback range",
                        local,
                        location
                    );
                    Var::MIN..Var::MIN
                })
        }))
    }

    #[inline]
    fn location_results(&'a self, location: Location) -> Self::LocationResults {
        let consume_chain = &self.ssa_state.consume_chain;
        let consumes = consume_chain.of_location(location);
        consumes.iter().map(move |(local, consume)| {
            (
                *local,
                consume.map_valid(|ssa_idx| {
                    self.fn_body_sig[*local]
                        .get(ssa_idx)
                        .cloned()
                        .or_else(|| {
                            tracing::debug!(
                                "missing local sig for {:?} at {:?} with ssa {:?}; falling back to last known sig",
                                local,
                                location,
                                ssa_idx
                            );
                            self.fn_body_sig[*local].raw.last().cloned()
                        })
                        .unwrap_or_else(|| {
                            tracing::debug!(
                                "missing all local sigs for {:?} at {:?}; returning empty fallback range",
                                local,
                                location
                            );
                            Var::MIN..Var::MIN
                        })
                }),
            )
        })
    }
}

type CallArgs = SmallVec<[Option<(Consume<LocalSig>, bool)>; 4]>;

pub struct InferCtxt<'infercx, 'db, 'tcx, Analysis>
where
    'tcx: 'infercx,
    Analysis: AnalysisKind<'infercx, 'db, 'tcx>,
{
    tcx: TyCtxt<'tcx>,
    inter_ctxt: Analysis::InterCtxt,
    database: &'infercx mut Analysis::DB,
    var_gen: &'infercx mut Gen,
    struct_ctxt: RestrictedStructCtxt<'infercx, 'tcx>,
    fn_body_sig: FnBodySig<LocalSig>,
    deref_copy: Option<Consume<<Analysis as InferMode<'infercx, 'db, 'tcx>>::LocalSig>>,
    call_args: Vec<CallArg<<Analysis as InferMode<'infercx, 'db, 'tcx>>::LocalSig>>,
    call_arg_records: FxHashMap<Local, Option<usize>>,
    global_assumptions: &'infercx GlobalAssumptions,
    copy_lend_guards: &'infercx FxHashMap<Location, Bool>,
    field_reader_guards: FxHashMap<Location, Bool>,
    realloc_plans: Vec<super::realloc_ssa::ReallocSsaPlan>,
    realloc_inputs:
        std::collections::BTreeMap<super::l2::MirLocationKey, realloc_transition::ReallocInput>,
    realloc_versions: Vec<super::export::ReallocVersionSite>,
    realloc_ghosts: FxHashSet<Var>,
    /// era-5c: the function whose body this context infers.
    function: rustc_hir::def_id::DefId,
    /// era-5c: must-null facts per CFG edge; `Some` only under the arm.
    null_paths: Option<super::null_paths::NullPaths>,
    /// era-5c: per (join block, local, incoming version) the window components
    /// known null on EVERY edge that carries that version into the join.
    null_joins: FxHashMap<(BasicBlock, Local, SSAIdx), Vec<bool>>,
    /// L01^5 (ii): the proven strong-update field moves of this body. Empty
    /// unless `CRAT_ERA5C_FIELD_MOVE` is on.
    field_moves: super::field_moves::FieldMoves,
}

type CallArg<LocalSig> = (Local, (Consume<LocalSig>, bool));

impl<'infercx, 'db, 'tcx, Analysis> InferCtxt<'infercx, 'db, 'tcx, Analysis>
where
    'tcx: 'infercx,
    Analysis: AnalysisKind<'infercx, 'db, 'tcx>,
{
    pub fn new(
        crate_ctxt: &'infercx CrateCtxt<'tcx>,
        max_precision: Precision,
        body: &Body<'tcx>,
        database: &'infercx mut Analysis::DB,
        var_gen: &'infercx mut Gen,
        inter_ctxt: Analysis::InterCtxt,
        global_assumptions: &'infercx GlobalAssumptions,
        copy_lend_guards: &'infercx FxHashMap<Location, Bool>,
    ) -> Self {
        let struct_ctxt = crate_ctxt.struct_ctxt.with_max_precision(max_precision);
        let mut fn_body_sig = IndexVec::with_capacity(body.local_decls.len());

        for local_decl in body.local_decls.iter() {
            if let Some(sigs) = initialize_local(local_decl, var_gen, database, struct_ctxt) {
                fn_body_sig.push(IndexVec::from_raw(vec![sigs]));
            } else {
                fn_body_sig.push(IndexVec::default());
            }
        }

        <Analysis as Boundary>::entry(
            crate_ctxt,
            &inter_ctxt,
            global_assumptions,
            database,
            body,
            fn_body_sig
                .iter()
                .skip(1)
                .take(body.arg_count)
                .map(|vec| vec.raw.first().cloned()),
        );

        InferCtxt {
            tcx: crate_ctxt.tcx,
            inter_ctxt,
            database,
            var_gen,
            struct_ctxt,
            fn_body_sig,
            deref_copy: None,
            call_args: Vec::new(),
            call_arg_records: FxHashMap::default(),
            global_assumptions,
            copy_lend_guards,
            field_reader_guards: FxHashMap::default(),
            realloc_plans: Vec::new(),
            realloc_inputs: std::collections::BTreeMap::new(),
            realloc_versions: Vec::new(),
            realloc_ghosts: FxHashSet::default(),
            function: body.source.def_id(),
            null_paths: super::null_paths::move_tracking()
                .then(|| super::null_paths::NullPaths::compute(crate_ctxt.tcx, body)),
            null_joins: FxHashMap::default(),
            field_moves: super::field_moves::compute(body),
        }
    }

    pub(crate) fn function(&self) -> rustc_hir::def_id::DefId {
        self.function
    }

    fn copy_lend_guard(&self, location: Location) -> Option<Bool> {
        self.copy_lend_guards.get(&location).cloned()
    }

    pub(crate) fn with_field_reader_guards(mut self, guards: FxHashMap<Location, Bool>) -> Self {
        self.field_reader_guards = guards;
        self
    }

    /// Dominance property
    fn new_vars(&mut self, ty: Ty<'tcx>) -> Range<Var> {
        let measure = self.struct_ctxt.measure(ty, 0);
        let vars = self.database.new_vars(self.var_gen, measure);
        let precision = self.struct_ctxt.max_ptr_chased();
        fn dominate<'tcx>(
            ty: Ty<'tcx>,
            mut dom: Option<Var>,
            vars: &mut Range<Var>,
            mut precision: u8,
            database: &mut impl Database,
            struct_ctxt: &StructCtxt,
            tcx: TyCtxt<'tcx>,
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
                    let var = vars.next().unwrap();
                    // §NB1 (C4-ii, plumbing only) — STRONG ownership monotonicity.
                    // BO deliberately dropped the production `dominate`'s
                    // `own(deeper) ⇒ own(shallower)` push (the relaxation site
                    // D2/`STRONG_MONO`). Re-enabled here behind the const so the
                    // C4-ii ablation can flip it; OFF by default (dead code, no
                    // behavior). Shape copied verbatim from
                    // `analyses::ownership::infer::new_vars::dominate`.
                    if super::STRONG_MONO
                        && let Some(dom) = dom
                    {
                        database.push_less_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                            (),
                            var,
                            dom,
                        );
                    }
                    dom = Some(var);

                    precision -= 1;
                    if precision == 0 {
                        return;
                    }
                    ty = ty_mut;
                    continue;
                }
                break;
            }

            if let TyKind::Adt(adt_def, subst) = ty.kind()
                && struct_ctxt.is_struct_of_concerned(&adt_def.did())
            {
                for field_def in adt_def.all_fields() {
                    let field_ty = field_def.ty(tcx, subst);
                    dominate(field_ty, dom, vars, precision, database, struct_ctxt, tcx)
                }
            }
        }

        dominate(
            ty,
            None,
            vars.clone().by_ref(),
            precision,
            self.database,
            self.struct_ctxt.unrestricted,
            self.tcx,
        );

        vars
    }

    fn project_deeper(
        base: Consume<<Analysis as InferMode<'infercx, 'db, 'tcx>>::LocalSig>,
        ty: Ty<'tcx>,
        projection: &[PlaceElem<'tcx>],
        infer_cx: &mut Self,
    ) -> Option<Consume<<Analysis as InferMode<'infercx, 'db, 'tcx>>::LocalSig>> {
        let mut base_ty = ty;

        let base_measure = base.r#use.size_hint().1.unwrap() as u32;
        // if base_measure == 0 { return None; }
        let precision = infer_cx
            .struct_ctxt
            .absolute_precision(base_ty, base_measure) as u32;
        let max_ptr_chased = infer_cx.struct_ctxt.max_ptr_chased() as u32;

        // let mut ptr_chased = 0;
        let mut ptr_chased = max_ptr_chased - precision;

        let mut proj_start_offset = 0;

        // let mut deref_var = None;

        for projection_elem in projection {
            match projection_elem {
                // do not track pointers behind dereferences for now
                ProjectionElem::Deref => {
                    // No need to set up threshold. Consumption of indirect places are processed
                    // only if definitions contain them, which happen in phases where threshold.
                    // Furthermore, mir places contain only at most one indirection.

                    // let ptr = base.r#use.start + proj_start_offset;
                    // if ptr < base.r#use.end {
                    //     infer_cx
                    //         .database
                    //         .push_assume::<crate::analyses::borrow_ownership::ssa::constraint::Debug>((), ptr, true);
                    // } else {
                    //     break;
                    // }
                    // deref_var = Some(ptr);

                    proj_start_offset += 1;
                    base_ty = base_ty.builtin_deref(true).unwrap();
                    ptr_chased += 1;
                }
                ProjectionElem::Field(field, ty) => {
                    let TyKind::Adt(adt_def, _) = base_ty.kind() else { unreachable!() };
                    proj_start_offset +=
                        infer_cx
                            .struct_ctxt
                            .field_offset(*adt_def, field.index(), ptr_chased);
                    base_ty = *ty;
                }
                // [ty] is equivalent to ty
                ProjectionElem::Index(_) => base_ty = base_ty.builtin_index().unwrap(),
                ProjectionElem::ConstantIndex { .. } => {
                    unreachable!("unexpected constant index");
                }
                ProjectionElem::Subslice { .. } => {
                    unreachable!("unexpected subslicing")
                }
                ProjectionElem::OpaqueCast(_) => unreachable!("unexpected opaque cast"),
                ProjectionElem::UnwrapUnsafeBinder(ty) | ProjectionElem::Subtype(ty) => {
                    base_ty = *ty;
                }
                ProjectionElem::Downcast(..) => unreachable!("unexpected downcasting"),
            }
        }

        if base.r#use.start + proj_start_offset >= base.r#use.end {
            for (pre, post) in base.r#use.zip(base.def) {
                infer_cx
                    .database
                    .push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                        (),
                        pre,
                        post,
                    );
            }
            return None;
        }

        // FIXME: this is currently buggy. What we really want to do is to enable consumption only
        // for pointers that are known to be owning. However, here we enforce a stricter constraint,
        // that once outtermost pointer is proven to be owning, not only does its consumption is
        // enabled, but also every further dereferences are enforced to be owning.
        // if let Some(ptr) = deref_var {
        //     infer_cx
        //         .database
        //         .push_assume::<crate::analyses::borrow_ownership::ssa::constraint::Debug>((), ptr, true);
        // }

        // TODO if proj to invalid, should the following constraints be emitted?

        for (pre, post) in (base.r#use.start..base.r#use.start + proj_start_offset)
            .zip(base.def.start..base.def.start + proj_start_offset)
        {
            infer_cx
                .database
                .push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                    (),
                    pre,
                    post,
                );
        }

        let proj_end_offset = proj_start_offset + infer_cx.struct_ctxt.measure(base_ty, ptr_chased);

        #[cfg(debug_assertions)]
        assert!(
            base.r#use.start + proj_end_offset <= base.r#use.end,
            "{ty}: {} ~> {base_ty}: {}, with projection: {:?}, chased: {ptr_chased}",
            base.r#use.end.index() - base.r#use.start.index(),
            proj_end_offset - proj_start_offset,
            projection
        );
        #[cfg(not(debug_assertions))]
        assert!(base.r#use.start + proj_end_offset <= base.r#use.end);

        for (pre, post) in (base.r#use.start + proj_end_offset..base.r#use.end)
            .zip(base.def.start + proj_end_offset..base.def.end)
        {
            infer_cx
                .database
                .push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                    (),
                    pre,
                    post,
                );
        }

        Some(Consume {
            r#use: base.r#use.start + proj_start_offset..base.r#use.start + proj_end_offset,
            def: base.def.start + proj_start_offset..base.def.start + proj_end_offset,
        })
    }
}

impl<'infercx, 'db, 'tcx, Analysis> InferMode<'infercx, 'db, 'tcx> for Analysis
where
    'tcx: 'infercx,
    Analysis: AnalysisKind<'infercx, 'db, 'tcx>,
    <Analysis as AnalysisKind<'infercx, 'db, 'tcx>>::DB: 'infercx,
{
    type Ctxt = InferCtxt<'infercx, 'db, 'tcx, Analysis>;
    type LocalSig = LocalSig;

    fn realloc_edge(
        infer_cx: &mut Self::Ctxt,
        plan: &super::realloc_ssa::ReallocSsaPlan,
        outcome: super::realloc::ReallocOutcome,
        edge: rustc_middle::mir::BasicBlock,
        operation: &super::realloc_ssa::ReallocEdgeOperation,
        versions: &[(Local, Consume<SSAIdx>)],
        body: &Body<'tcx>,
    ) {
        infer_cx.apply_realloc_edge(plan, outcome, edge, operation, versions, body);
    }

    #[inline]
    fn call_arg(
        infer_cx: &mut Self::Ctxt,
        temp: Local,
        arg: Consume<Self::LocalSig>,
        is_ref: bool,
    ) {
        let registration = super::ownership_boundary::register_proxy(temp.as_u32(), &arg, is_ref);
        if super::licensing::facts::active() {
            infer_cx.call_arg_records.insert(temp, registration);
        }
        if let Some(existing) = infer_cx.call_args.get_by_key_mut(&temp) {
            *existing = (arg, is_ref);
        } else {
            infer_cx.call_args.push((temp, (arg, is_ref)));
        }
    }

    #[inline]
    fn define_phi_node(
        infer_cx: &mut InferCtxt<'infercx, 'db, 'tcx, Analysis>,
        local: Local,
        ty: Ty<'tcx>,
        def: SSAIdx,
    ) {
        // let measure = infer_cx.fn_ctxt.measure(ty, 0);
        // let sigs = infer_cx.new_vars(measure);
        let sigs = infer_cx.new_vars(ty);
        while infer_cx.fn_body_sig[local].next_index() < def {
            // Keep indices aligned with SSA by inserting conservative fillers.
            let filler = infer_cx.new_vars(ty);
            infer_cx.fn_body_sig[local].push(filler);
        }

        if infer_cx.fn_body_sig[local].next_index() == def {
            infer_cx.fn_body_sig[local].push(sigs);
        } else {
            tracing::debug!(
                "overwriting phi node sig for {:?} at {:?}: next_index={:?}",
                local,
                def,
                infer_cx.fn_body_sig[local].next_index()
            );
            infer_cx.fn_body_sig[local][def] = sigs;
        }
    }

    fn phi_edge(
        infer_cx: &mut InferCtxt<'infercx, 'db, 'tcx, Analysis>,
        pred: BasicBlock,
        succ: BasicBlock,
        local: Local,
        ty: Ty<'tcx>,
        rhs: SSAIdx,
    ) {
        let Some(null_paths) = infer_cx.null_paths.as_ref() else {
            return;
        };
        let facts = null_paths.local_facts_on_edge(pred, succ, local);
        let window = infer_cx
            .fn_body_sig
            .get(local)
            .and_then(|versions| versions.get(rhs))
            .map(|sigs| sigs.end.as_u32() - sigs.start.as_u32())
            .unwrap_or_else(|| infer_cx.struct_ctxt.measure(ty, 0));
        let vacuous = super::null_paths::vacuous_components_with(
            infer_cx.tcx,
            &infer_cx.struct_ctxt,
            ty,
            window,
            &facts,
        );
        // Every edge carrying this version must agree: intersect.
        infer_cx
            .null_joins
            .entry((succ, local, rhs))
            .and_modify(|known| {
                for (known, now) in known.iter_mut().zip(vacuous.iter()) {
                    *known = *known && *now;
                }
                known.truncate(vacuous.len().min(known.len()));
            })
            .or_insert(vacuous);
    }

    fn join_phi_nodes<'a>(
        infer_cx: &'a mut InferCtxt<'infercx, 'db, 'tcx, Analysis>,
        bb: BasicBlock,
        phi_nodes: impl Iterator<Item = (Local, &'a mut PhiNode)>,
    ) {
        for (local, phi_node) in phi_nodes {
            // This is not necessary if phi nodes have been prune
            phi_node.rhs.sort();
            phi_node.rhs.dedup();
            let lhs = phi_node.lhs;
            for rhs in phi_node.rhs.iter().copied() {
                if lhs == rhs {
                    continue;
                }
                let Some(lhs_sigs) = infer_cx.fn_body_sig[local].get(lhs).cloned() else {
                    tracing::debug!(
                        "missing lhs phi sig for {:?} at {:?}; skipping phi equality",
                        local,
                        lhs
                    );
                    continue;
                };
                let Some(rhs_sigs) = infer_cx.fn_body_sig[local].get(rhs).cloned() else {
                    tracing::debug!(
                        "missing rhs phi sig for {:?} at {:?}; skipping phi equality",
                        local,
                        rhs
                    );
                    continue;
                };
                let vacuous = infer_cx.null_joins.get(&(bb, local, rhs)).cloned();
                for (index, (lhs_sig, rhs_sig)) in lhs_sigs.zip(rhs_sigs).enumerate() {
                    if vacuous
                        .as_ref()
                        .is_some_and(|vacuous| vacuous.get(index).copied().unwrap_or(false))
                    {
                        // era-5c: the incoming pointer is null on every edge
                        // that carries this version here — its token guards
                        // nothing and may be dropped at the join.
                        infer_cx.database.push_null_join::<
                            crate::analyses::borrow_ownership::ssa::constraint::Debug,
                        >((), lhs_sig, rhs_sig);
                        continue;
                    }
                    infer_cx
                        .database
                        .push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                            (),
                            lhs_sig,
                            rhs_sig,
                        )
                }
            }
        }
    }

    fn interpret_consume(
        infer_cx: &mut InferCtxt<'infercx, 'db, 'tcx, Analysis>,
        body: &Body<'tcx>,
        place: &Place<'tcx>,
        consume: Option<Consume<SSAIdx>>,
    ) -> Option<Consume<Self::LocalSig>> {
        let occurrence_ssa = consume.clone();
        let base = place.local;
        let base_ty = body.local_decls[base].ty;

        let base = if let Some(consume) = consume {
            let base_offset = infer_cx.struct_ctxt.measure(base_ty, 0);

            tracing::debug!("interpretting consume for {:?} with {:?}", place, consume);

            while infer_cx.fn_body_sig[base].next_index() <= consume.r#use {
                let filler = infer_cx.new_vars(base_ty);
                infer_cx.fn_body_sig[base].push(filler);
            }
            let r#use = infer_cx.fn_body_sig[base][consume.r#use].clone();
            let def = infer_cx.new_vars(base_ty);
            if r#use
                .clone()
                .any(|var| infer_cx.realloc_ghosts.contains(&var))
            {
                infer_cx.realloc_ghosts.extend(def.clone());
            }
            if base_offset != r#use.end.as_u32() - r#use.start.as_u32() {
                tracing::debug!(
                    "mismatched base measure for {:?}: expected {}, got {}",
                    place,
                    base_offset,
                    r#use.end.as_u32() - r#use.start.as_u32()
                );
            }

            while infer_cx.fn_body_sig[base].next_index() < consume.def {
                let filler = infer_cx.new_vars(base_ty);
                infer_cx.fn_body_sig[base].push(filler);
            }
            if infer_cx.fn_body_sig[base].next_index() == consume.def {
                infer_cx.fn_body_sig[base].push(def.clone());
            } else {
                tracing::debug!(
                    "overwriting consume def sig for {:?} at {:?}: next_index={:?}",
                    base,
                    consume.def,
                    infer_cx.fn_body_sig[base].next_index()
                );
                infer_cx.fn_body_sig[base][consume.def] = def.clone();
            }

            // let base = Consume { r#use, def };
            Consume { r#use, def }
        } else if matches!(
            body.local_decls[base].local_info.as_ref(),
            ClearCrossCrate::Set(local_info) if matches!(local_info.as_ref(), LocalInfo::DerefTemp)
        ) {
            let Some(base) = infer_cx.deref_copy.take() else {
                super::ownership_occurrence::record_consume(
                    infer_cx.tcx,
                    body,
                    *place,
                    occurrence_ssa.as_ref(),
                    None,
                    None,
                    &infer_cx.struct_ctxt,
                    "deref-copy provider unavailable",
                );
                return None;
            };
            base
        } else {
            super::ownership_occurrence::record_consume(
                infer_cx.tcx,
                body,
                *place,
                occurrence_ssa.as_ref(),
                None,
                None,
                &infer_cx.struct_ctxt,
                "no SSA consume",
            );
            return None;
        };

        let observed_base = base.clone();
        let projected = InferCtxt::project_deeper(base, base_ty, place.projection, infer_cx);
        super::ownership_occurrence::record_consume(
            infer_cx.tcx,
            body,
            *place,
            occurrence_ssa.as_ref(),
            Some(&observed_base),
            projected.as_ref(),
            &infer_cx.struct_ctxt,
            "projection outside represented ownership window",
        );
        projected
    }

    fn copy_for_deref(
        infer_cx: &mut Self::Ctxt,
        consume: Option<Consume<Self::LocalSig>>,
        location: Location,
    ) {
        if let Some(lend) = infer_cx.copy_lend_guard(location)
            && let Some(consume) = consume.as_ref()
        {
            for (source_use, source_def) in consume.r#use.clone().zip(consume.def.clone()) {
                infer_cx
                    .database
                    .push_guarded_lend_source(&lend, source_def, source_use);
            }
        }
        if infer_cx.deref_copy.is_some() {
            tracing::debug!("overwriting stale deref_copy consume");
        }
        infer_cx.deref_copy = consume
    }

    fn aggregate(
        infer_cx: &mut Self::Ctxt,
        body: &Body<'tcx>,
        place: Place<'tcx>,
        kind: &AggregateKind<'tcx>,
        destination: Option<Consume<Self::LocalSig>>,
        operands: &[(&Operand<'tcx>, Option<Consume<Self::LocalSig>>)],
    ) {
        infer_cx.aggregate(body, place, kind, destination, operands);
    }

    fn transfer<const ENSURE_MOVE: bool>(
        infer_cx: &mut InferCtxt<'infercx, 'db, 'tcx, Analysis>,
        ty: Ty<'tcx>,
        lhs_result: Consume<Self::LocalSig>,
        rhs_result: Consume<Self::LocalSig>,
        location: Option<Location>,
    ) {
        tracing::debug!("transfer relation: {:?} ~ {:?}", lhs_result, rhs_result);
        if rhs_result
            .r#use
            .clone()
            .any(|var| infer_cx.realloc_ghosts.contains(&var))
        {
            infer_cx.realloc_ghosts.extend(lhs_result.def.clone());
            infer_cx.realloc_ghosts.extend(rhs_result.def.clone());
        }

        let copy_lend_guard = location.and_then(|location| infer_cx.copy_lend_guard(location));
        let field_reader_guard =
            location.and_then(|location| infer_cx.field_reader_guards.get(&location).cloned());
        let reader_windows = field_reader_guard
            .as_ref()
            .map(|_| (lhs_result.clone(), rhs_result.clone()));
        with_own_assume_site(OwnAssumeSite::SsaTransfer, || {
            // L01^5 (ii): a proven strong-update field load MOVES the token —
            // the destination takes it and the source component goes vacuous —
            // instead of the split a copy would get. `field_moves` is empty
            // unless CRAT_ERA5C_FIELD_MOVE is on.
            let ensure_move = ENSURE_MOVE
                || location.is_some_and(|location| infer_cx.field_moves.is_move(location));
            let mut matched_depth = 0usize;
            let mut reader_destinations = std::collections::BTreeSet::new();
            let mut reader_sources = std::collections::BTreeSet::new();
            matcher(
                ty,
                lhs_result.transpose(),
                rhs_result.transpose(),
                infer_cx.struct_ctxt,
                infer_cx.database,
                |lhs, rhs, database| {
                    let _transfer = super::ownership_occurrence::transfer(&lhs, &rhs, ensure_move);
                    database
                        .push_assume::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                            (),
                            lhs.r#use,
                            false,
                        );
                    if let Some(reader) = field_reader_guard.as_ref() {
                        reader_destinations.insert(lhs.def);
                        reader_sources.insert(rhs.def);
                        database.push_guarded_field_reader(
                            reader,
                            lhs.def,
                            rhs.def,
                            rhs.r#use,
                            ENSURE_MOVE,
                        );
                    } else if matched_depth == 0
                        && let Some(lend) = copy_lend_guard.as_ref()
                    {
                        database.push_guarded_copy(lend, lhs.def, rhs.def, rhs.r#use, ENSURE_MOVE);
                    } else if ensure_move {
                        database.push_equal::<
                            crate::analyses::borrow_ownership::ssa::constraint::Debug,
                        >((), lhs.def, rhs.r#use);
                        database.push_assume::<
                            crate::analyses::borrow_ownership::ssa::constraint::Debug,
                        >((), rhs.def, false);
                    } else {
                        database.push_linear::<
                            crate::analyses::borrow_ownership::ssa::constraint::Debug,
                        >((), lhs.def, rhs.def, rhs.r#use)
                    }
                    matched_depth += 1;
                },
            );
            if let (Some(reader), Some((destination, source))) =
                (field_reader_guard.as_ref(), reader_windows)
            {
                // Structural matching can omit deeper components at a precision
                // boundary. The certified view still owns no represented part,
                // and the source keeps every represented responsibility. The
                // ordinary transfer arm retains its existing precision behavior.
                for (window, matched, source_tail) in [
                    (destination, reader_destinations, false),
                    (source, reader_sources, true),
                ] {
                    for component in window.transpose() {
                        if !matched.contains(&component.def) {
                            infer_cx.database.push_guarded_field_reader_tail(
                                reader,
                                component.def,
                                component.r#use,
                                source_tail,
                            );
                        }
                    }
                }
            }
        })
    }

    fn cast<const ENSURE_MOVE: bool>(
        infer_cx: &mut InferCtxt<'infercx, 'db, 'tcx, Analysis>,
        ty: Ty<'tcx>,
        lhs: Consume<Self::LocalSig>,
        rhs: Consume<Self::LocalSig>,
        location: Option<Location>,
    ) {
        if ty.is_raw_ptr() || ty.is_box() || ty.is_ref() {
            let lhs = lhs.repack(|sigs| sigs.start..sigs.start + 1u32);
            let rhs = rhs.repack(|sigs| sigs.start..sigs.start + 1u32);
            Self::transfer::<ENSURE_MOVE>(infer_cx, ty, lhs, rhs, location)
        } else {
            todo!("handling casts between structs are not supported")
        }
    }

    #[inline]
    fn unknown_sink(
        infer_cx: &mut InferCtxt<'infercx, 'db, 'tcx, Analysis>,
        consume: Consume<Self::LocalSig>,
    ) {
        for (r#use, def) in consume.r#use.zip(consume.def) {
            infer_cx
                .database
                .push_less_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                    (),
                    def,
                    r#use,
                );
        }
    }

    #[inline]
    fn lend(infer_cx: &mut Self::Ctxt, consume: Consume<Self::LocalSig>) {
        for (r#use, def) in consume.r#use.zip(consume.def) {
            infer_cx
                .database
                .push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                    (),
                    r#use,
                    def,
                )
        }
    }

    fn mutable_reference(
        infer_cx: &mut Self::Ctxt,
        destination: Consume<Self::LocalSig>,
        source: Option<Consume<Self::LocalSig>>,
    ) {
        if let Some(source) = source.as_ref()
            && infer_cx
                .database
                .try_original_cell_frame(&destination, source)
        {
            return;
        }
        if let Some(source) = source.as_ref()
            && infer_cx
                .database
                .try_reference_field_effect(&destination, source)
        {
            return;
        }
        Self::borrow(infer_cx, destination);
        if let Some(source) = source {
            Self::lend(infer_cx, source);
        }
    }

    fn source(infer_cx: &mut Self::Ctxt, result: Consume<Self::LocalSig>) {
        infer_cx.database.record_source_sink();
        Self::assume(infer_cx, result.r#use, false);
        if let Some(sig) = result.def.clone().next() {
            // Retractable owning: hard by default, selector-gated for BO so the
            // on-UNSAT relax loop can leak a conflicting allocation (B3a).
            infer_cx.database.push_source_owning(sig)
        }
    }

    fn sink(infer_cx: &mut Self::Ctxt, result: Consume<Self::LocalSig>) {
        infer_cx.database.record_source_sink();
        if let Some(sig) = result.r#use.clone().next() {
            // §NB-F retractable owning (option (a) of the NB-R gate): hard by
            // default, selector-gated for BO — the sink twin of `source` above.
            // The relax loop may drop the selector to LEAK THE FREE (an
            // unprovable free stays a raw-pointer free) instead of declining;
            // NB-R showed the hard sink was the forced-owning pole of every
            // Family-A corpus UNSAT.
            infer_cx.database.push_sink_owning(sig)
        }
        Self::assume(infer_cx, result.def, false);
    }

    #[inline]
    fn assume(
        infer_cx: &mut InferCtxt<'infercx, 'db, 'tcx, Analysis>,
        result: Self::LocalSig,
        value: bool,
    ) {
        for sig in result {
            infer_cx
                .database
                .push_assume::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                    (),
                    sig,
                    value,
                )
        }
    }

    fn call(
        infer_cx: &mut InferCtxt<'infercx, 'db, 'tcx, Analysis>,
        destination: Option<Consume<Self::LocalSig>>,
        args: &[Spanned<Operand<'tcx>>],
        callee: &Operand<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) {
        let mut registrations = super::licensing::facts::active().then(Vec::new);
        let args = args
            .iter()
            .map(|operand| {
                let proxy = operand.node.place().and_then(|operand| operand.as_local());
                let arg = proxy.and_then(|proxy| infer_cx.call_args.get_by_key(&proxy));
                if let Some(registrations) = &mut registrations {
                    registrations.push(arg.and_then(|(_, by_reference)| {
                        proxy.map(|proxy| super::ownership_boundary::SelectedProxy {
                            proxy_local: proxy.as_u32(),
                            registration: infer_cx.call_arg_records.get(&proxy).copied().flatten(),
                            by_reference: *by_reference,
                        })
                    }));
                }
                arg.cloned()
            })
            .collect::<SmallVec<_>>();
        let _boundary_arguments = super::ownership_boundary::call_arguments(registrations);

        if let Some(func) = callee.constant() {
            let ty = func.ty();
            let &FnDef(callee, substs) = ty.kind() else { unreachable!() };
            if let Some(local_did) = callee.as_local() {
                match infer_cx.tcx.hir_node_by_def_id(local_did) {
                    // this crate
                    rustc_hir::Node::Item(_) => {
                        with_own_assume_site(OwnAssumeSite::LocalWrapper, || {
                            <Analysis as Boundary>::call(infer_cx, destination, &args, callee)
                        })
                    }
                    // extern
                    rustc_hir::Node::ForeignItem(foreign_item) => {
                        with_own_assume_site(OwnAssumeSite::LibcRule, || {
                            // E-R3 capture: the callee-name half of the call
                            // cursor, joined with the location half at the
                            // selector push site.
                            crate::analyses::borrow_ownership::export::with_callee(
                                foreign_item.ident.as_str(),
                                || {
                                    infer_cx.libc_call(
                                        destination,
                                        &args,
                                        callee,
                                        foreign_item.ident,
                                    )
                                },
                            )
                        })
                    }
                    // in libxml2.rust/src/xmlschemastypes.rs/{} impl_xmlSchemaValDate/set_mon
                    rustc_hir::Node::ImplItem(_) => { /* TODO */ }
                    _ => unreachable!(),
                }
            } else {
                // library
                infer_cx.library_call(destination, &args, callee, substs)
            }
        } else {
            // closure or fn ptr
            // TODO (default arm: nothing is emitted and the result floats —
            // the objective then settles it Owning with no evidence).
            //
            // era-5c (R409-1, R412-12): under the frame an indirect call's
            // result is OPAQUE — an unknown call: destination borrowed,
            // arguments lent — and the named allocator contract is the only
            // route to Owning for such a result: a call through `alloc_func`
            // is a receipted source, through `free_func` a sink.
            if super::null_paths::move_tracking() || super::allocator_contract::enabled() {
                let class = super::allocator_contract::classify(infer_cx.tcx, body, location);
                if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
                    eprintln!(
                        "E5C contract-call {:?} at {location:?}: {class:?} callee-ty={:?}",
                        infer_cx.tcx.def_path_str(body.source.def_id()),
                        callee.ty(body, infer_cx.tcx)
                    );
                }
                match class {
                    Some(super::allocator_contract::ContractCall::Alloc) => {
                        super::allocator_contract::note_producer(body.source.def_id());
                        with_own_assume_site(OwnAssumeSite::LibcRule, || {
                            super::export::with_callee(super::allocator_contract::CONTRACT, || {
                                if let Some(destination) = destination {
                                    Self::source(infer_cx, destination);
                                }
                            })
                        })
                    }
                    Some(super::allocator_contract::ContractCall::Free) => {
                        with_own_assume_site(OwnAssumeSite::LibcRule, || {
                            super::export::with_callee(super::allocator_contract::CONTRACT, || {
                                if let Some(Some((arg, is_ref))) = args.get(1) {
                                    assert!(!is_ref);
                                    Self::sink(infer_cx, arg.clone());
                                }
                            })
                        })
                    }
                    None => infer_cx.unknown_call(destination, &args),
                }
            }
        }
    }

    fn r#return<'a>(
        infer_cx: &mut Self::Ctxt,
        locals: impl Iterator<Item = (Local, Option<SSAIdx>)> + 'a,
        body: &'a Body<'tcx>,
    ) {
        let mut locals_collected = Vec::new();
        for (local, ssa_idx) in locals {
            let sigs = if let Some(ssa_idx) = ssa_idx {
                let ty = body.local_decls[local].ty;
                while infer_cx.fn_body_sig[local].next_index() <= ssa_idx {
                    let filler = infer_cx.new_vars(ty);
                    infer_cx.fn_body_sig[local].push(filler);
                }
                infer_cx.fn_body_sig[local].get(ssa_idx).cloned()
            } else {
                None
            };
            super::ownership_occurrence::record_terminal(
                infer_cx.tcx,
                body,
                local,
                ssa_idx,
                sigs.as_ref(),
                &infer_cx.struct_ctxt,
            );
            locals_collected.push((local, sigs));
        }

        // L01⁷-A1 (R525-5). The loop below is commented "finalize temporaries",
        // but it walks EVERY non-parameter local -- named ones included. Report
        // 037 §3 measured `main_0::root` sitting in that set directly, which is
        // why bst's driver collapses: the blanket asserts `own = false` on the
        // very local the source named as the owner.
        //
        // A1 spares exactly those. Uniqueness is preserved by construction and
        // the argument is direct: every ANONYMOUS temporary stays pinned to
        // non-owning, so within each `own-equal` class at most the named local
        // can hold the token -- which is the conclusion the blanket exists to
        // support. On bst that is 5 named locals spared out of 159.
        //
        // R526-3 narrows this from "every named local" to the CALL-RESULT
        // RE-SEAT destination only. The wide form took the analyses suite from
        // 1,112/6 to 1,005/113 -- the fold/custody/gate certificates rely on the
        // final zero of a live local as an inference device, and
        // `ol19_return_transfers_but_live_local_finalization_is_not_relaxed` is
        // a purpose-named counter-witness that is NOT re-pinned. So the spare
        // set is exactly `x = f(x)`: a named local that is both an argument of a
        // call and the destination of that call's result, directly
        // (`x = f(x)`) or through the result temporary (`t = f(x); x = t`).
        let named_locals: rustc_data_structures::fx::FxHashSet<Local> =
            if super::field_moves::reseat_a1() {
                reseat_destinations(body)
            } else {
                Default::default()
            };
        let spared: Vec<Local> = locals_collected
            .iter()
            .skip(body.arg_count + 1)
            .filter(|(local, _)| named_locals.contains(local))
            .map(|(local, _)| *local)
            .collect();
        if !spared.is_empty() && std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
            eprintln!(
                "E5C a1-spared fn={} locals={:?}",
                infer_cx.tcx.def_path_str(body.source.def_id()),
                spared.iter().map(|l| l.as_u32()).collect::<Vec<_>>()
            );
        }

        let mut locals = locals_collected.into_iter().skip(0);

        <Analysis as Boundary>::exit(
            infer_cx.tcx,
            &infer_cx.inter_ctxt,
            infer_cx.global_assumptions,
            infer_cx.struct_ctxt.unrestricted,
            infer_cx.database,
            body,
            locals
                .by_ref()
                .take(body.arg_count + 1)
                .map(|(_, sigs)| sigs),
        );

        // finalize temporaries
        //
        // R510-1(1) COUNTERFACTUAL PIN -- NEVER LANDS. era-5c report 033 found
        // `own-assume[temporary-finalization]` in all nine relaxation cores of
        // the bst driver variant while the corpus form has none. This gate drops
        // the family so the seat can see whether removing it RECOVERS the model
        // (the caller re-seat rule is then sufficient) or exposes a second wall.
        // Diagnosis only: `CRAT_ERA5C_SKIP_FAMILY=temporary-finalization`.
        let skip_finalization = super::field_moves::finalize_soft()
            || std::env::var("CRAT_ERA5C_SKIP_FAMILY")
                .unwrap_or_default()
                .split(',')
                .any(|name| name.trim() == "temporary-finalization");
        with_own_assume_site(OwnAssumeSite::TemporaryFinalization, || {
            if skip_finalization {
                return;
            }
            for (local, vars) in locals {
                let Some(vars) = vars else {
                    continue;
                };
                // A1: a named local live at exit keeps its ownership bit free.
                if named_locals.contains(&local) {
                    continue;
                }
                for var in vars {
                    infer_cx
                        .database
                        .push_assume::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
                            (),
                            var,
                            false,
                        )
                }
            }
        });
    }

    fn cast_to_c_void(
        infer_cx: &mut Self::Ctxt,
        consume: Consume<Self::LocalSig>,
    ) -> Consume<Self::LocalSig> {
        consume.repack(|sigs| {
            let (outter, inner) = (sigs.start..sigs.start + 1u32, sigs.start + 1u32..sigs.end);
            with_own_assume_site(OwnAssumeSite::CastOrDepth, || {
                Self::assume(infer_cx, inner, false);
            });
            outter
        })
    }
}

/// [`measure`] could be either [`FnCtxt`] or [`StructTopology`]. This is because
/// ptr_chased is relative but precision is absolute.
fn fit<'tcx, T, U>(
    adt_def: AdtDef,
    mut fitter: impl Iterator<Item = T>,
    fitter_precision: Precision,
    mut fittee: impl Iterator<Item = U>,
    delta: Precision,
    measurable: impl Measurable<'tcx>,
    mut on_matched: impl FnMut(T, U),
) {
    let fitter_ptr_chased = measurable.max_ptr_chased() - fitter_precision;

    let fitter_leaf_nodes = measurable.leaf_nodes(adt_def, fitter_ptr_chased as u32);

    let mut count = 0;
    for &(leaf_ext_ty, offset_to_be) in fitter_leaf_nodes {
        while count < offset_to_be {
            let (Some(fitter), Some(fittee)) = (fitter.next(), fittee.next()) else {
                tracing::debug!(
                    "fit: ran out of iterator items before offset alignment (count={count}, target={offset_to_be})"
                );
                return;
            };
            on_matched(fitter, fittee);
            count += 1;
        }

        let leaf_ext_measure =
            measurable.measure(leaf_ext_ty, (measurable.max_ptr_chased() - delta) as u32);

        for _ in 0..leaf_ext_measure {
            if fittee.next().is_none() {
                tracing::debug!(
                    "fit: fittee exhausted while skipping leaf extension measure ({leaf_ext_measure})"
                );
                return;
            }
        }
    }

    if fitter.next().is_some() || fittee.next().is_some() {
        tracing::debug!(
            "fit: non-empty iterator tail after structural fit; ignoring trailing items"
        );
    }
}

fn matcher<'tcx, T, U, DB>(
    ty: Ty<'tcx>,
    mut lhs_result: impl Iterator<Item = T>,
    mut rhs_result: impl Iterator<Item = U>,
    measurable: impl Measurable<'tcx>,
    database: &mut DB,
    mut on_matched: impl FnMut(T, U, &mut DB),
) {
    let lhs_measure = lhs_result.size_hint().1.unwrap() as u32;
    let rhs_measure = rhs_result.size_hint().1.unwrap() as u32;

    let lhs_precision = measurable.absolute_precision(ty, lhs_measure);
    let rhs_precision = measurable.absolute_precision(ty, rhs_measure);

    tracing::debug!("precision: lhs = {lhs_precision}, rhs = {rhs_precision}");

    let (ptr_depth, adt_def) = decompose_ty(ty);

    if ptr_depth as u8 > lhs_precision
        || ptr_depth as u8 > rhs_precision
        || lhs_precision == rhs_precision
    {
        for (lhs, rhs) in lhs_result.zip(rhs_result) {
            on_matched(lhs, rhs, database);
        }
    } else {
        for (lhs, rhs) in lhs_result
            .by_ref()
            .zip(rhs_result.by_ref())
            .take(ptr_depth as usize)
        {
            on_matched(lhs, rhs, database);
        }

        let lhs_precision = lhs_precision - ptr_depth as u8;
        let rhs_precision = rhs_precision - ptr_depth as u8;

        let delta = lhs_precision.abs_diff(rhs_precision);

        let adt_def = adt_def.unwrap();
        if lhs_precision < rhs_precision {
            fit(
                adt_def,
                lhs_result,
                lhs_precision,
                rhs_result,
                delta,
                measurable,
                |lhs, rhs| on_matched(lhs, rhs, database),
            )
        } else {
            fit(
                adt_def,
                rhs_result,
                rhs_precision,
                lhs_result,
                delta,
                measurable,
                |rhs, lhs| on_matched(lhs, rhs, database),
            )
        }
    }
}

/// L01⁷-A1's spare set (R526-3): the named locals that are the DESTINATION of a
/// call-result re-seat `x = f(x)`, directly or through the result temporary,
/// with each argument resolved back through `Use(Copy|Move)` chains (bst's
/// `root = insert(root, k)` passes a copy of `root`). Lifted out of `r#return`
/// so a MIR-only walk can count the market without running a solve.
pub(crate) fn reseat_destinations(
    body: &rustc_middle::mir::Body<'_>,
) -> rustc_data_structures::fx::FxHashSet<Local> {
    let named: rustc_data_structures::fx::FxHashSet<Local> = body
        .var_debug_info
        .iter()
        .filter_map(|info| {
            let rustc_middle::mir::VarDebugInfoContents::Place(place) = info.value else {
                return None;
            };
            place.projection.is_empty().then_some(place.local)
        })
        .collect();
    let mut reseated = rustc_data_structures::fx::FxHashSet::default();
    if std::env::var_os("CRAT_ERA5C_RESEAT_DUMP").is_some() {
        eprintln!("E5C_MIR_FN {:?}", body.source.def_id());
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for st in &data.statements {
                if let rustc_middle::mir::StatementKind::Assign(a) = &st.kind {
                    eprintln!("E5C_MIR {:?} {:?} = {:?}", block, a.0, a.1);
                }
            }
            if let rustc_middle::mir::TerminatorKind::Call {
                args,
                destination,
                func,
                ..
            } = &data.terminator().kind
            {
                eprintln!(
                    "E5C_MIR {:?} CALL dest={:?} func={:?} args={:?}",
                    block,
                    destination,
                    func,
                    args.iter().map(|a| a.node.place()).collect::<Vec<_>>()
                );
            }
        }
    }
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let rustc_middle::mir::TerminatorKind::Call {
            args,
            destination,
            func,
            ..
        } = &data.terminator().kind
        else {
            continue;
        };
        // R526-3's callee condition, its necessary half: the callee is a
        // function OF THIS PROGRAM. Report 040 measured the syntactic form
        // matching ~2,300 calls corpus-wide, all but a handful of them
        // `wrapping_*` arithmetic and `ptr::offset` cursor advances
        // (`output = output.offset(1)` is a call in MIR). A cursor's
        // `own = false` finalization is protective -- a cursor must never
        // become the owner of the interior of an allocation -- so those
        // are excluded here, not merely counted.
        let Some((callee, _)) = func.const_fn_def() else {
            continue;
        };
        if !callee.is_local() {
            continue;
        }
        // the locals this call consumes as arguments
        let mut argument_locals = rustc_data_structures::fx::FxHashSet::default();
        for arg in args.iter() {
            if let Some(place) = arg.node.place()
                && place.projection.is_empty()
            {
                argument_locals.insert(place.local);
            }
        }
        if argument_locals.is_empty() || !destination.projection.is_empty() {
            continue;
        }
        let result = destination.local;
        // The argument is normally a COPY of the re-seated local --
        // bst's `root = insert(root, k)` is `_4 = copy _2;
        // _3 = insert(_4, _5); _2 = move _3` -- so resolve each argument
        // back through `Use(Copy|Move)` chains to the locals it reads.
        let mut argument_sources = argument_locals.clone();
        let mut changed = true;
        while changed {
            changed = false;
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let rustc_middle::mir::StatementKind::Assign(assign) = &statement.kind else {
                        continue;
                    };
                    let (target, rvalue) = &**assign;
                    let rustc_middle::mir::Rvalue::Use(operand) = rvalue else { continue };
                    let Some(source) = operand.place() else { continue };
                    if target.projection.is_empty()
                        && source.projection.is_empty()
                        && argument_sources.contains(&target.local)
                        && argument_sources.insert(source.local)
                    {
                        changed = true;
                    }
                }
            }
        }
        // direct form: `x = f(x)`
        if named.contains(&result) && argument_sources.contains(&result) {
            reseated.insert(result);
            if std::env::var_os("CRAT_ERA5C_RESEAT_WHY").is_some() {
                let rustc_middle::mir::TerminatorKind::Call { func, .. } = &data.terminator().kind
                else {
                    unreachable!()
                };
                eprintln!("E5C_RESEAT_WHY direct _{} {:?}", result.as_u32(), func);
            }
        }
        // through the result temporary: `t = f(x); x = move t`
        for (_, later) in body
            .basic_blocks
            .iter_enumerated()
            .filter(|(b, _)| *b >= block)
        {
            for statement in &later.statements {
                let rustc_middle::mir::StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (target, rvalue) = &**assign;
                let rustc_middle::mir::Rvalue::Use(operand) = rvalue else { continue };
                let Some(source) = operand.place() else { continue };
                if target.projection.is_empty()
                    && source.projection.is_empty()
                    && source.local == result
                    && named.contains(&target.local)
                    && argument_sources.contains(&target.local)
                {
                    reseated.insert(target.local);
                    if std::env::var_os("CRAT_ERA5C_RESEAT_WHY").is_some() {
                        let rustc_middle::mir::TerminatorKind::Call { func, .. } =
                            &data.terminator().kind
                        else {
                            unreachable!()
                        };
                        eprintln!(
                            "E5C_RESEAT_WHY via-temp _{} {:?}",
                            target.local.as_u32(),
                            func
                        );
                    }
                }
            }
        }
    }
    reseated
}
