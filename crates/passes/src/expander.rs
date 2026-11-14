use std::sync::Arc;

use rustc_ast::{
    self as ast,
    mut_visit::{self, MutVisitor},
};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashSet;
use rustc_middle::ty::TyCtxt;
use rustc_span::{Ident, Symbol, kw, sym};
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
    let mut features = krate
        .attrs
        .iter()
        .filter(|attribute| attribute.has_name(sym::feature))
        .flat_map(|attribute| attribute.meta_item_list().unwrap())
        .map(|feature| feature.ident().unwrap().name)
        .collect::<Vec<_>>();
    features.extend([
        sym::c_variadic,
        sym::extern_types,
        sym::linkage,
        sym::rustc_private,
        sym::thread_local,
        sym::builtin_syntax,
        sym::coverage_attribute,
        Symbol::intern("core_intrinsics"),
        Symbol::intern("derive_clone_copy"),
        Symbol::intern("hint_must_use"),
        Symbol::intern("panic_internals"),
        Symbol::intern("rt"),
        Symbol::intern("libstd_sys_internals"),
        Symbol::intern("structural_match"),
        Symbol::intern("thread_local_internals"),
        Symbol::intern("never_type"),
        Symbol::intern("fmt_helpers_for_derive"),
        Symbol::intern("derive_eq"),
    ]);
    krate.attrs.clear();
    krate.attrs.extend([
        utils::ast::make_inner_attribute(sym::warn, Symbol::intern("mutable_transmutes"), tcx),
        utils::ast::make_inner_attribute(sym::allow, Symbol::intern("non_camel_case_types"), tcx),
        utils::ast::make_inner_attribute(sym::allow, Symbol::intern("non_snake_case"), tcx),
        utils::ast::make_inner_attribute(sym::allow, Symbol::intern("non_upper_case_globals"), tcx),
    ]);
    let mut emitted = FxHashSet::default();
    for feature in features {
        if emitted.insert(feature) {
            krate
                .attrs
                .push(utils::ast::make_inner_attribute(sym::feature, feature, tcx));
        }
    }
    if config.keep_allows {
        krate.attrs.extend([
            utils::ast::make_inner_attribute(sym::allow, Symbol::intern("dead_code"), tcx),
            utils::ast::make_inner_attribute(sym::allow, Symbol::intern("unused_assignments"), tcx),
            utils::ast::make_inner_attribute(sym::allow, Symbol::intern("unused_mut"), tcx),
        ]);
    }

    AstVisitor { tcx }.visit_crate(krate);
    pprust::crate_to_string_for_macros(krate)
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl MutVisitor for AstVisitor<'_> {
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

    fn visit_path(&mut self, path: &mut ast::Path) {
        mut_visit::walk_path(self, path);
        let [root, module, ..] = path.segments.as_slice() else { return };
        if root.ident.name != kw::DollarCrate {
            return;
        }
        let Some(def_id) = root.ident.span.ctxt().outer_expn_data().macro_def_id else {
            return;
        };
        if def_id.is_local() || !self.tcx.is_diagnostic_item(sym::vec_macro, def_id) {
            return;
        }
        // Printed paths lose the macro hygiene that makes `$crate` accessible.
        match (module.ident.name.as_str(), path.segments.len()) {
            ("vec", _) => {}
            ("boxed", 3) if path.segments[2].ident.name.as_str() == "box_new" => {
                let function = &mut path.segments[2];
                let mut boxed = ast::PathSegment::from_ident(Ident::new(
                    Symbol::intern("Box"),
                    function.ident.span,
                ));
                boxed.args = function.args.take();
                function.ident.name = sym::new;
                path.segments.insert(2, boxed);
            }
            _ => return,
        }
        path.segments[0].ident.name = sym::std;
        path.segments
            .insert(0, ast::PathSegment::path_root(path.span));
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

#[cfg(test)]
mod tests;
