use std::ops::ControlFlow;

use etrace::some_or;
use rustc_ast::{
    self as ast,
    mut_visit::{self, MutVisitor},
    ptr::P,
    visit::{self, Visitor},
};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_hir::{
    self as hir, QPath, def::Res, def_id::LocalDefId, intravisit, intravisit::Visitor as _,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::{Symbol, kw, sym};
use smallvec::{SmallVec, smallvec};
use utils::{attr, expr};

use crate::{ast_utils, ir_utils};

pub fn unexpand(tcx: TyCtxt<'_>) -> String {
    let mut krate = ast_utils::expanded_ast(tcx);
    let ast_to_hir = ast_utils::make_ast_to_hir(&mut krate, tcx);
    ast_utils::remove_unnecessary_items_from_ast(&mut krate);

    krate.attrs.retain(|attr| {
        if let ast::AttrKind::Normal(attr) = &attr.kind
            && attr.item.path.segments.last().unwrap().ident.name == sym::feature
            && let Some(arg) = ast_utils::get_attr_arg(&attr.item.args)
            && let arg = arg.as_str()
            && (arg == "derive_clone_copy" || arg == "hint_must_use" || arg == "panic_internals")
        {
            return false;
        }
        true
    });

    let mut pre_visitor = Previsitor {
        tcx,
        ast_to_hir,
        ctx: Ctx::default(),
    };
    pre_visitor.visit_crate(&krate);

    let mut visitor = AstVisitor {
        tcx,
        ast_to_hir: pre_visitor.ast_to_hir,
        ctx: pre_visitor.ctx,
    };
    visitor.visit_crate(&mut krate);

    pprust::crate_to_string_for_macros(&krate)
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: ir_utils::AstToHir,
    ctx: Ctx,
}

impl MutVisitor for AstVisitor<'_> {
    fn flat_map_item(&mut self, item: P<ast::Item>) -> SmallVec<[P<ast::Item>; 1]> {
        if ast_utils::is_automatically_derived(&item.attrs) {
            return smallvec![];
        }
        mut_visit::walk_flat_map_item(self, item)
    }

    fn visit_item(&mut self, item: &mut ast::Item) {
        if let ast::ItemKind::Struct(_, _, vd) | ast::ItemKind::Union(_, _, vd) = &mut item.kind {
            let local_def_id = self.ast_to_hir.global_map.get(&item.id).unwrap();
            if let Some(traits) = self.ctx.derived_traits.get(local_def_id) {
                for t in traits {
                    let attr = ast_utils::make_outer_attribute(sym::derive, *t, self.tcx);
                    item.attrs.push(attr);
                }
            }
            if let Some(bitfields) = self.ctx.bitfields.get(local_def_id) {
                let ast::VariantData::Struct { fields, .. } = vd else { panic!() };
                for field in fields {
                    let bitfields = some_or!(bitfields.get(&field.ident.unwrap().name), continue);
                    for bitfield in bitfields {
                        let BitField { name, ty, l, r } = bitfield;
                        let attrs = attr!(
                            "#[bitfield(name = \"{name}\", ty = \"{ty}\", bits = \"{l}..={r}\")]"
                        );
                        field.attrs.extend(attrs);
                    }
                }
            }
        }
        mut_visit::walk_item(self, item);
    }

    fn visit_expr(&mut self, expr: &mut ast::Expr) {
        if let ast::ExprKind::Call(callee, args) = &expr.kind
            && let ast::ExprKind::Path(None, callee) = &callee.kind
            && let [.., md, func] = &callee.segments[..]
        {
            let md = md.ident.name;
            let func = func.ident.name;
            if md == sym::panicking {
                if func.as_str() == "panic_explicit" {
                    *expr = expr!("panic!()");
                } else if func == sym::panic
                    && let [arg] = &args[..]
                {
                    if let ast::ExprKind::Lit(lit) = &arg.kind
                        && lit.symbol.as_str() == "internal error: entered unreachable code"
                    {
                        *expr = expr!("unreachable!()");
                    } else {
                        panic!("{}", pprust::expr_to_string(arg))
                    }
                } else {
                    panic!("{func}");
                }
            } else if md == sym::hint {
                if func == sym::must_use {
                    let [arg] = &args[..] else { panic!() };
                    *expr = (**arg).clone();
                } else {
                    panic!("{func}");
                }
            } else if md == sym::fmt {
                if func == sym::format {
                    let [arg] = &args[..] else { panic!() };
                    let arg = pprust::expr_to_string(arg);
                    let arg = arg
                        .strip_prefix("format_args!(")
                        .unwrap()
                        .strip_suffix(')')
                        .unwrap();
                    *expr = expr!("format!({arg})");
                } else {
                    panic!("{func}");
                }
            }
        }
        mut_visit::walk_expr(self, expr);
    }
}

#[derive(Default)]
struct Ctx {
    derived_traits: FxHashMap<LocalDefId, Vec<Symbol>>,
    bitfields: FxHashMap<LocalDefId, FxHashMap<Symbol, Vec<BitField>>>,
}

struct BitField {
    name: Symbol,
    ty: String,
    l: u128,
    r: u128,
}

struct Previsitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: ir_utils::AstToHir,
    ctx: Ctx,
}

impl<'ast> Visitor<'ast> for Previsitor<'_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        if ast_utils::is_automatically_derived(&item.attrs)
            && matches!(item.kind, ast::ItemKind::Impl(_))
        {
            let hir_item = self.ast_to_hir.get_item(item.id, self.tcx).unwrap();
            let hir::ItemKind::Impl(imp) = hir_item.kind else { panic!() };
            let hir::TyKind::Path(QPath::Resolved(_, self_ty)) = imp.self_ty.kind else { panic!() };
            let Res::Def(_, def_id) = self_ty.res else { panic!() };
            let def_id = def_id.expect_local();
            if let Some(of_trait) = imp.of_trait {
                let of_trait = of_trait.path.segments.last().unwrap().ident.name;
                self.ctx
                    .derived_traits
                    .entry(def_id)
                    .or_default()
                    .push(of_trait);
            } else {
                self.ctx
                    .derived_traits
                    .entry(def_id)
                    .or_default()
                    .push(Symbol::intern("BitfieldStruct"));
                let source_map = self.tcx.sess.source_map();
                for item in imp.items {
                    let impl_item = self.tcx.hir_impl_item(item.id);
                    let hir::ImplItemKind::Fn(sig, body_id) = &impl_item.kind else { continue };
                    let name = impl_item.ident.name;
                    if name.as_str().starts_with("set_") {
                        continue;
                    }
                    let hir::FnRetTy::Return(ty) = sig.decl.output else { panic!() };
                    let ty = source_map.span_to_snippet(ty.span).unwrap();
                    let body = self.tcx.hir_body(*body_id);
                    let mut visitor = HirBodyVisitor {
                        tcx: self.tcx,
                        field: None,
                    };
                    let (l, r) = visitor.visit_expr(body.value).break_value().unwrap();
                    let field = visitor.field.unwrap();
                    let bit_field = BitField { name, ty, l, r };
                    self.ctx
                        .bitfields
                        .entry(def_id)
                        .or_default()
                        .entry(field)
                        .or_default()
                        .push(bit_field);
                }
            }
        }
        visit::walk_item(self, item);
    }
}

struct HirBodyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    field: Option<Symbol>,
}

impl<'tcx> intravisit::Visitor<'tcx> for HirBodyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type Result = ControlFlow<(u128, u128)>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_local(&mut self, local: &'tcx hir::LetStmt<'tcx>) -> Self::Result {
        if let Some(init) = local.init {
            if let hir::ExprKind::AddrOf(hir::BorrowKind::Ref, ast::Mutability::Not, e) = init.kind
                && let hir::ExprKind::Field(e, f) = e.kind
                && let hir::ExprKind::Path(QPath::Resolved(_, p)) = e.kind
                && p.segments.last().unwrap().ident.name == kw::SelfLower
            {
                assert!(self.field.is_none());
                self.field = Some(f.name);
            } else if let hir::ExprKind::Tup([l, r]) = init.kind
                && let hir::ExprKind::Lit(l) = l.kind
                && let ast::LitKind::Int(l, _) = l.node
                && let hir::ExprKind::Lit(r) = r.kind
                && let ast::LitKind::Int(r, _) = r.node
            {
                assert!(self.field.is_some());
                return ControlFlow::Break((l.get(), r.get()));
            }
        }
        intravisit::walk_local(self, local)
    }
}
