use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    ExprKind, HirId, QPath, TyKind,
    def::{DefKind, Res},
    intravisit::{Visitor, walk_expr},
};
use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind};
use rustc_span::def_id::LocalDefId;

use super::{
    Analysis,
    decision::{PtrKind, SigDecisions},
};
use crate::{rewriter::decision::DecisionMaker, utils::rustc::RustProgram};

pub fn collect_diffs<'tcx>(
    rust_program: &RustProgram<'tcx>,
    analysis: &Analysis,
    sig_decs: &SigDecisions,
    fn_ptr_groups: &crate::analyses::fn_ptr_groups::FnPtrGroups,
) -> FxHashMap<HirId, PtrKind> {
    let mut ptr_kinds = FxHashMap::default();
    let non_outermost_owning_locals = collect_non_outermost_owning_hir_locals(rust_program);

    let fn_ptrs = collect_fn_ptrs(rust_program);

    for did in rust_program.functions.iter() {
        let decision_maker = DecisionMaker::new(analysis, *did, rust_program.tcx);

        let hir_to_mir = utils::ir::map_thir_to_mir(*did, false, rust_program.tcx);
        let local_to_binding: FxHashMap<Local, HirId> = hir_to_mir
            .binding_to_local
            .into_iter()
            .map(|(k, v)| (v, k))
            .collect();

        let body = &*rust_program
            .tcx
            .mir_drops_elaborated_and_const_checked(did)
            .borrow();

        let used_as_fn_ptr = fn_ptrs.contains(did);
        let input_len = rust_program
            .tcx
            .fn_sig(*did)
            .skip_binder()
            .inputs()
            .skip_binder()
            .len();

        let aliases = analysis.aliases.get(did);
        let returned_output_locals = sig_decs
            .data
            .get(did)
            .and_then(|sig_dec| sig_dec.output_dec)
            .filter(|kind| matches!(kind, PtrKind::Ref(_) | PtrKind::OptRef(_)))
            .map(|kind| collect_returned_output_locals(body, kind))
            .unwrap_or_default();

        for (local, decl) in body.local_decls.iter_enumerated().skip(1) {
            let is_input = local.index() <= input_len;
            let sig_input_dec = local
                .index()
                .checked_sub(1)
                .filter(|idx| *idx < input_len)
                .and_then(|idx| {
                    sig_decs
                        .data
                        .get(did)?
                        .input_decs
                        .get(idx)
                        .copied()
                        .flatten()
                });
            let aliases = aliases.and_then(|aliases| aliases.get(&local));

            let group_input_dec = if is_input && used_as_fn_ptr {
                fn_ptr_groups
                    .fn_to_group
                    .get(did)
                    .and_then(|rep| fn_ptr_groups.group_decisions.get(rep))
                    .and_then(|decs| decs.get(local.index() - 1).copied())
                    .flatten()
            } else {
                None
            };

            let decision = if is_input && used_as_fn_ptr {
                sig_input_dec.or(group_input_dec)
            } else {
                sig_input_dec
                    .or_else(|| returned_output_locals.get(&local).copied())
                    .or_else(|| decision_maker.decide(local, decl, aliases))
            };

            if let Some(mut ptr_kind) = decision
                && let Some(hir_id) = local_to_binding.get(&local)
            {
                if non_outermost_owning_locals.contains(hir_id) && ptr_kind.is_owning_box_like() {
                    ptr_kind = PtrKind::Raw(ptr_kind.is_mut());
                }
                ptr_kinds.insert(*hir_id, ptr_kind);
            }
        }
    }

    ptr_kinds
}

fn collect_returned_output_locals(
    body: &rustc_middle::mir::Body<'_>,
    output_kind: PtrKind,
) -> FxHashMap<Local, PtrKind> {
    let mut locals = FxHashMap::default();
    locals.insert(Local::from_u32(0), output_kind);

    loop {
        let mut changed = false;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                    continue;
                };
                let Some(destination) = place.as_local() else {
                    continue;
                };
                if !locals.contains_key(&destination) {
                    continue;
                }
                let Rvalue::Use(Operand::Copy(source) | Operand::Move(source)) = rvalue else {
                    continue;
                };
                let Some(source) = source.as_local() else {
                    continue;
                };
                changed |= locals.insert(source, output_kind).is_none();
            }
        }
        if !changed {
            break;
        }
    }

    locals.remove(&Local::from_u32(0));
    locals
}

fn collect_non_outermost_owning_hir_locals(rust_program: &RustProgram) -> FxHashSet<HirId> {
    fn local_path_id(expr: &rustc_hir::Expr<'_>) -> Option<HirId> {
        if let ExprKind::Path(QPath::Resolved(_, path)) = expr.kind
            && let Res::Local(hir_id) = path.res
        {
            Some(hir_id)
        } else if let ExprKind::Cast(inner, _) = expr.kind {
            local_path_id(inner)
        } else {
            None
        }
    }

    struct NonOutermostCollector {
        locals: FxHashSet<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for NonOutermostCollector {
        fn visit_expr(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>) -> Self::Result {
            if let ExprKind::Assign(lhs, rhs, _) = ex.kind
                && !matches!(lhs.kind, ExprKind::Path(QPath::Resolved(_, path)) if matches!(path.res, Res::Local(_)))
                && let Some(hir_id) = local_path_id(rhs)
            {
                self.locals.insert(hir_id);
            }
            walk_expr(self, ex);
        }
    }

    let mut collector = NonOutermostCollector {
        locals: FxHashSet::default(),
    };
    for def_id in rust_program.functions.iter() {
        let body = rust_program.tcx.hir_body_owned_by(*def_id);
        collector.visit_body(body);
    }
    collector.locals
}

pub fn collect_fn_ptrs(rust_program: &RustProgram) -> FxHashSet<LocalDefId> {
    struct FnPtrCollector<'tcx> {
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        pub fn_ptrs: FxHashSet<LocalDefId>,
    }

    impl<'tcx> Visitor<'tcx> for FnPtrCollector<'tcx> {
        fn visit_expr(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>) -> Self::Result {
            let mut maybe_local_fn = None;
            if let ExprKind::Path(ref qpath) = ex.kind
                && let QPath::Resolved(_, path) = qpath
                && let Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) = path.res
            {
                maybe_local_fn = def_id.as_local();
            } else if let ExprKind::Cast(inner, ty) = ex.kind
                && let TyKind::BareFn(_) = ty.kind
                && let ExprKind::Path(ref qpath) = inner.kind
                && let QPath::Resolved(_, path) = qpath
                && let Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) = path.res
            {
                maybe_local_fn = def_id.as_local();
            }

            if let Some(def_id) = maybe_local_fn {
                let typeck = self.tcx.typeck(ex.hir_id.owner);
                if matches!(
                    typeck.expr_ty_adjusted(ex).kind(),
                    rustc_middle::ty::TyKind::FnPtr(..)
                ) {
                    self.fn_ptrs.insert(def_id);
                }
            }
            walk_expr(self, ex);
        }
    }

    let mut collector = FnPtrCollector {
        tcx: rust_program.tcx,
        fn_ptrs: FxHashSet::default(),
    };

    for def_id in rust_program.functions.iter() {
        let body = rust_program.tcx.hir_body_owned_by(*def_id);
        collector.visit_body(body);
    }

    collector.fn_ptrs
}
