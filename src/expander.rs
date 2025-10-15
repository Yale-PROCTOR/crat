use std::sync::Arc;

use rustc_ast::{
    self as ast,
    mut_visit::{self, MutVisitor},
};
use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;
use rustc_span::{Symbol, kw, sym};
use utils::expr;

use crate::ast_utils;

pub fn expand(tcx: TyCtxt<'_>) -> String {
    let (_, mut krate) = tcx.resolver_for_lowering().steal();
    let krate = Arc::get_mut(&mut krate).unwrap();
    ast_utils::remove_unnecessary_items_from_ast(krate);
    krate.attrs.clear();
    krate.attrs.extend([
        ast_utils::make_inner_attribute(sym::warn, Symbol::intern("mutable_transmutes"), tcx),
        ast_utils::make_inner_attribute(sym::feature, sym::c_variadic, tcx),
        ast_utils::make_inner_attribute(sym::feature, sym::extern_types, tcx),
        ast_utils::make_inner_attribute(sym::feature, sym::linkage, tcx),
        ast_utils::make_inner_attribute(sym::feature, sym::rustc_private, tcx),
        ast_utils::make_inner_attribute(sym::feature, sym::thread_local, tcx),
        ast_utils::make_inner_attribute(sym::feature, Symbol::intern("core_intrinsics"), tcx),
        ast_utils::make_inner_attribute(sym::feature, Symbol::intern("derive_clone_copy"), tcx),
        ast_utils::make_inner_attribute(sym::feature, Symbol::intern("hint_must_use"), tcx),
        ast_utils::make_inner_attribute(sym::feature, Symbol::intern("panic_internals"), tcx),
    ]);
    AstVisitor.visit_crate(krate);
    pprust::crate_to_string_for_macros(krate)
}

struct AstVisitor;

impl MutVisitor for AstVisitor {
    fn visit_item(&mut self, item: &mut ast::Item) {
        if let ast::ItemKind::Mod(_, ident, _) = &mut item.kind
            && ident.name == kw::Mod
        {
            ident.name = Symbol::intern("rmod");
        }
        mut_visit::walk_item(self, item);
    }

    fn visit_expr(&mut self, expr: &mut ast::Expr) {
        if let ast::ExprKind::Path(None, path) = &mut expr.kind
            && let [_, _, seg] = &path.segments[..]
        {
            let name = seg.ident.name;
            if name == sym::must_use {
                *expr = expr!("std::hint::must_use");
            } else if name == sym::format {
                *expr = expr!("std::fmt::format");
            }
        }
        mut_visit::walk_expr(self, expr);
    }

    fn visit_field_def(&mut self, fd: &mut ast::FieldDef) {
        fd.attrs.retain(|attr| {
            let ast::AttrKind::Normal(attr) = &attr.kind else { return true };
            let seg = attr.item.path.segments.last().unwrap();
            seg.ident.name.as_str() != "bitfield"
        });
        mut_visit::walk_field_def(self, fd);
    }
}
