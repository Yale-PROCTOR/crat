use std::sync::Arc;

use rustc_ast::{
    self as ast,
    mut_visit::{self, MutVisitor},
};
use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;
use rustc_span::{Symbol, kw, sym};
use serde::Deserialize;
use utils::expr;

#[derive(Debug, Default, Clone, Copy, Deserialize)]
pub struct Config {
    pub keep_allows: bool,
}

pub fn expand(config: Config, tcx: TyCtxt<'_>) -> String {
    let (_, mut krate) = tcx.resolver_for_lowering().steal();
    let krate = Arc::get_mut(&mut krate).unwrap();
    utils::ast::remove_unnecessary_items_from_ast(krate);
    krate.attrs.clear();
    krate.attrs.extend([
        utils::ast::make_inner_attribute(sym::warn, Symbol::intern("mutable_transmutes"), tcx),
        utils::ast::make_inner_attribute(sym::allow, Symbol::intern("non_camel_case_types"), tcx),
        utils::ast::make_inner_attribute(sym::allow, Symbol::intern("non_snake_case"), tcx),
        utils::ast::make_inner_attribute(sym::allow, Symbol::intern("non_upper_case_globals"), tcx),
        utils::ast::make_inner_attribute(sym::feature, sym::c_variadic, tcx),
        utils::ast::make_inner_attribute(sym::feature, sym::extern_types, tcx),
        utils::ast::make_inner_attribute(sym::feature, sym::linkage, tcx),
        utils::ast::make_inner_attribute(sym::feature, sym::rustc_private, tcx),
        utils::ast::make_inner_attribute(sym::feature, sym::thread_local, tcx),
        utils::ast::make_inner_attribute(sym::feature, Symbol::intern("core_intrinsics"), tcx),
        utils::ast::make_inner_attribute(sym::feature, Symbol::intern("derive_clone_copy"), tcx),
        utils::ast::make_inner_attribute(sym::feature, Symbol::intern("hint_must_use"), tcx),
        utils::ast::make_inner_attribute(sym::feature, Symbol::intern("panic_internals"), tcx),
    ]);
    if config.keep_allows {
        krate.attrs.extend([
            utils::ast::make_inner_attribute(sym::allow, Symbol::intern("dead_code"), tcx),
            utils::ast::make_inner_attribute(sym::allow, Symbol::intern("unused_assignments"), tcx),
            utils::ast::make_inner_attribute(sym::allow, Symbol::intern("unused_mut"), tcx),
        ]);
    }

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
