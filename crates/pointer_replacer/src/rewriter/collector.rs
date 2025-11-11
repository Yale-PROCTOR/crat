use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_hir::{
    ExprKind, HirId, QPath, TyKind,
    def::{DefKind, Res},
    intravisit::{Visitor, walk_expr},
};
use rustc_middle::{mir::Local, ty::TyCtxt};
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
        let decision_maker = DecisionMaker::new(analysis, did);

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
    struct FnPtrCollector {
        pub fn_ptrs: FxHashSet<LocalDefId>,
    }

    impl<'tcx> Visitor<'tcx> for FnPtrCollector {
        fn visit_expr(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>) -> Self::Result {
            if let ExprKind::Cast(inner, ty) = ex.kind
                && let TyKind::BareFn(_) = ty.kind
                && let ExprKind::Path(ref qpath) = inner.kind
                && let QPath::Resolved(_, path) = qpath
                && let Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) = path.res
                && let Some(def_id) = def_id.as_local()
            {
                self.fn_ptrs.insert(def_id);
            }
            walk_expr(self, ex);
        }
    }

    let mut collector = FnPtrCollector {
        fn_ptrs: FxHashSet::default(),
    };

    for def_id in rust_program.functions.iter() {
        let body = rust_program.tcx.hir_body_owned_by(*def_id);
        collector.visit_body(body);
    }

    collector.fn_ptrs
}

struct OffsetVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    params: FxHashMap<LocalDefId, Vec<HirId>>,
    offsets: FxHashSet<HirId>,
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for OffsetVisitor<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_fn(
        &mut self,
        kind: hir::intravisit::FnKind<'tcx>,
        decl: &'tcx hir::FnDecl<'tcx>,
        body_id: hir::BodyId,
        _: rustc_span::Span,
        def_id: LocalDefId,
    ) {
        let body = self.tcx.hir_body(body_id);
        let params = body
            .params
            .iter()
            .map(|param| {
                let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else { panic!() };
                hir_id
            })
            .collect();
        self.params.insert(def_id, params);
        hir::intravisit::walk_fn(self, kind, decl, body_id, def_id);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::MethodCall(seg, e, _, _) = expr.kind
            && seg.ident.name == rustc_span::sym::offset
            && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = unwrap_hir_expr(e).kind
            && let Res::Local(hir_id) = path.res
        {
            self.offsets.insert(hir_id);
        }
        hir::intravisit::walk_expr(self, expr);
    }
}

fn unwrap_hir_expr<'tcx>(expr: &'tcx hir::Expr<'tcx>) -> &'tcx hir::Expr<'tcx> {
    if let hir::ExprKind::Cast(expr, _) | hir::ExprKind::DropTemps(expr) = &expr.kind {
        unwrap_hir_expr(expr)
    } else {
        expr
    }
}
