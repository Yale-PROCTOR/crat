use rustc_ast::{mut_visit::MutVisitor as _, *};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};

pub fn replace_static(tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let mut statics = FxHashSet::default();
    for def_id in tcx.hir_body_owners() {
        if matches!(tcx.def_kind(def_id), DefKind::Static { .. }) {
            statics.insert(def_id);
        }
    }

    let mut visitor = HirVisitor {
        tcx,
        statics: FxHashMap::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

    let mut immutables = FxHashSet::default();
    for (def_id, exprs) in visitor.statics {
        if exprs.iter().any(|(_, mutated)| *mutated) {
            continue;
        }
        immutables.insert(def_id);
    }

    let mut visitor = AstVisitor {
        ast_to_hir,
        immutables,
    };
    visitor.visit_crate(&mut krate);

    pprust::crate_to_string_for_macros(&krate)
}

struct AstVisitor {
    ast_to_hir: utils::ir::AstToHir,
    immutables: FxHashSet<LocalDefId>,
}

impl mut_visit::MutVisitor for AstVisitor {
    fn visit_item(&mut self, item: &mut Item) {
        if let ItemKind::Static(box static_item) = &mut item.kind
            && let Some(def_id) = self.ast_to_hir.global_map.get(&item.id)
            && self.immutables.contains(def_id)
        {
            static_item.mutability = Mutability::Not;
        }
        mut_visit::walk_item(self, item);
    }
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    statics: FxHashMap<LocalDefId, Vec<(&'tcx hir::Expr<'tcx>, bool)>>,
}

impl<'tcx> HirVisitor<'tcx> {
    fn find_context(&self, mut expr: &'tcx hir::Expr<'tcx>) -> (&'tcx hir::Expr<'tcx>, bool) {
        let mut mutated = false;
        for (_, node) in self.tcx.hir_parent_iter(expr.hir_id) {
            match node {
                hir::Node::Expr(parent) => match parent.kind {
                    hir::ExprKind::MethodCall(method, receiver, _, _) => {
                        if receiver.hir_id == expr.hir_id {
                            let method = method.ident.name.as_str();
                            match method {
                                "as_mut_ptr" => {
                                    expr = parent;
                                    mutated = true;
                                }
                                "as_ptr" => {
                                    expr = parent;
                                }
                                _ if method.starts_with("wrapping_") => {}
                                _ => panic!("{method}"),
                            }
                        }
                        break;
                    }
                    hir::ExprKind::DropTemps(..)
                    | hir::ExprKind::Field(..)
                    | hir::ExprKind::Index(..) => {
                        expr = parent;
                    }
                    hir::ExprKind::AddrOf(_, mutability, _) => {
                        mutated |= mutability.is_mut();
                        expr = parent;
                        break;
                    }
                    hir::ExprKind::Assign(lhs, _, _) | hir::ExprKind::AssignOp(_, lhs, _) => {
                        if lhs.hir_id == expr.hir_id {
                            expr = parent;
                            mutated = true;
                        }
                        break;
                    }
                    _ => break,
                },
                hir::Node::Item(..)
                | hir::Node::ExprField(..)
                | hir::Node::Stmt(..)
                | hir::Node::Block(..)
                | hir::Node::LetStmt(..) => break,
                _ => panic!("{node:?}"),
            }
        }
        (expr, mutated)
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Path(hir::QPath::Resolved(None, path)) = expr.kind
            && let Res::Def(DefKind::Static { .. }, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
        {
            let context = self.find_context(expr);
            self.statics.entry(def_id).or_default().push(context);
        }

        intravisit::walk_expr(self, expr);
    }
}
