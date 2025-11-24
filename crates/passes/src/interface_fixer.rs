use std::fmt::Write as _;

use rustc_ast::{mut_visit::MutVisitor as _, ptr::P, *};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_hir::{
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit,
};
use rustc_middle::{hir::nested_filter, ty, ty::TyCtxt};
use rustc_span::Symbol;
use serde::Deserialize;
use utils::ir::AstToHir;

#[derive(Debug, Default, Clone, Deserialize)]
pub struct Config {
    pub c_exposed_fns: FxHashSet<String>,
}

pub fn fix_interfaces(config: &Config, tcx: TyCtxt<'_>) -> String {
    let mut expanded_ast = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut expanded_ast, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut expanded_ast);

    let mut hir_visitor = HirVisitor {
        tcx,
        config,
        fixes: FxHashMap::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut hir_visitor);

    let mut visitor = AstVisitor {
        tcx,
        ast_to_hir,
        fixes: hir_visitor.fixes,
    };
    visitor.visit_crate(&mut expanded_ast);

    pprust::crate_to_string_for_macros(&expanded_ast)
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    fixes: FxHashMap<LocalDefId, (FxHashMap<usize, ParamFix<'tcx>>, Symbol)>,
}

impl mut_visit::MutVisitor for AstVisitor<'_> {
    fn flat_map_item(&mut self, item: P<Item>) -> smallvec::SmallVec<[P<Item>; 1]> {
        let id = item.id;
        let mut items = mut_visit::walk_flat_map_item(self, item);

        if let Some(def_id) = self.ast_to_hir.global_map.get(&id)
            && let Some((fixes, name)) = self.fixes.get(def_id)
        {
            let mut new_item = items[0].clone();
            let ItemKind::Fn(f) = &mut new_item.kind else { panic!() };
            let mut call = format!("{name}(");
            for (i, param) in f.sig.decl.inputs.iter_mut().enumerate() {
                let PatKind::Ident(_, ident, _) = &param.pat.kind else { panic!() };
                let x = ident.name;
                if let Some(fix) = fixes.get(&i) {
                    let m = if fix.mutability.is_mut() {
                        "mut"
                    } else {
                        "const"
                    };
                    let ty = utils::ir::mir_ty_to_string(fix.ty, self.tcx);
                    *param.ty = utils::ty!("*{m} {ty}");
                    write!(
                        call,
                        "if {x}.is_null() {{ &{}[] }} else {{ std::slice::from_raw_parts{}({x}, 1024) }}, ",
                        if fix.mutability.is_mut() { "mut " } else { "" },
                        if fix.mutability.is_mut() { "_mut" } else { "" },
                    ).unwrap();
                } else {
                    write!(call, "{x}, ").unwrap();
                }
            }
            call.push(')');
            let body = f.body.as_mut().unwrap();
            body.stmts.clear();
            let stmt = utils::stmt!("{call}");
            body.stmts.push(stmt);
            items.push(new_item);

            let ItemKind::Fn(f) = &mut items[0].kind else { panic!() };
            f.ident.name = *name;
        }

        items
    }

    fn visit_item(&mut self, item: &mut Item) {
        mut_visit::walk_item(self, item);

        let id = item.id;
        if let ItemKind::Use(tree) = &mut item.kind
            && let Some(seg) = tree.prefix.segments.last_mut()
            && let Some(hir_item) = self.ast_to_hir.get_item(id, self.tcx)
            && let hir::ItemKind::Use(path, _) = &hir_item.kind
            && let Some(Res::Def(DefKind::Fn, def_id)) = path.res.value_ns
            && let Some(def_id) = def_id.as_local()
            && let Some((_, name)) = self.fixes.get(&def_id)
        {
            seg.ident.name = *name;
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        let id = expr.id;
        if let ExprKind::Path(_, path) = &mut expr.kind
            && let Some(hir_expr) = self.ast_to_hir.get_expr(id, self.tcx)
            && let hir::ExprKind::Path(hir::QPath::Resolved(_, hir_path)) = &hir_expr.kind
            && let Res::Def(DefKind::Fn, def_id) = hir_path.res
            && let Some(def_id) = def_id.as_local()
            && let Some((_, name)) = self.fixes.get(&def_id)
        {
            path.segments.last_mut().unwrap().ident.name = *name;
        }
    }
}

#[derive(Clone, Copy)]
struct ParamFix<'tcx> {
    mutability: ty::Mutability,
    ty: ty::Ty<'tcx>,
}

struct HirVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    config: &'a Config,
    fixes: FxHashMap<LocalDefId, (FxHashMap<usize, ParamFix<'tcx>>, Symbol)>,
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        if let hir::ItemKind::Fn { ident, body, .. } = item.kind
            && let name = ident.name.as_str()
            && self.config.c_exposed_fns.contains(name)
        {
            let body = self.tcx.hir_body(body);
            let typeck = self.tcx.typeck(item.owner_id.def_id);
            let mut fixes = FxHashMap::default();
            for (i, param) in body.params.iter().enumerate() {
                let ty = typeck.node_type(param.pat.hir_id);
                let ty::TyKind::Ref(_, inner_ty, m) = ty.kind() else { continue };
                let ty::TyKind::Slice(inner_ty) = inner_ty.kind() else { continue };
                fixes.insert(
                    i,
                    ParamFix {
                        mutability: *m,
                        ty: *inner_ty,
                    },
                );
            }
            if !fixes.is_empty() {
                let new_name = format!("{name}_internal");
                let new_name = Symbol::intern(&new_name);
                self.fixes.insert(item.owner_id.def_id, (fixes, new_name));
            }
        }

        intravisit::walk_item(self, item);
    }
}
