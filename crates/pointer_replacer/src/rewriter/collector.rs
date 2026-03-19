use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    ExprKind, HirId, QPath, TyKind,
    def::{DefKind, Res},
    intravisit::{Visitor, walk_expr},
};
use rustc_middle::mir::Local;
use rustc_span::def_id::LocalDefId;

use super::{Analysis, decision::PtrKind};
use crate::{rewriter::decision::DecisionMaker, utils::rustc::RustProgram};

pub fn collect_diffs<'tcx>(
    rust_program: &RustProgram<'tcx>,
    analysis: &Analysis,
) -> FxHashMap<HirId, PtrKind> {
    let mut ptr_kinds = FxHashMap::default();

    let fn_ptrs = collect_fn_ptrs(rust_program);

    // collect each HIR variable's before/after pointer kinds
    for did in rust_program.functions.iter() {
        let decision_maker = DecisionMaker::new(analysis, *did, rust_program.tcx);

        // Assume every mir local has one or less corresponding hir id
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
        let input_skip_len = rust_program
            .tcx
            .fn_sig(*did)
            .skip_binder()
            .inputs()
            .skip_binder()
            .len();

        let aliases = analysis.aliases.get(did);

        for (local, decl) in body
            .local_decls
            .iter_enumerated()
            .skip(1 + input_skip_len * (used_as_fn_ptr as usize))
        // skip inputs if used as fn ptr
        {
            let aliases = aliases.and_then(|aliases| aliases.get(&local));
            if let Some(ptr_kind) = decision_maker.decide(local, decl, aliases)
                && let Some(hir_id) = local_to_binding.get(&local)
            {
                ptr_kinds.insert(*hir_id, ptr_kind);
            }
        }
    }

    ptr_kinds
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
