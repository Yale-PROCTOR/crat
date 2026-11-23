use std::sync::Arc;

use rustc_ast::{
    self as ast,
    mut_visit::{self, MutVisitor},
    visit::{self, Visitor},
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def::Res;
use rustc_middle::ty::{ResolverAstLowering, TyCtxt};
use rustc_span::{Ident, Symbol, kw, sym};
use serde::Deserialize;
use utils::expr;

#[derive(Debug, Default, Clone, Copy, Deserialize)]
pub struct Config {
    pub keep_allows: bool,
}

pub fn expand(config: Config, tcx: TyCtxt<'_>) -> String {
    let (resolver, mut krate) = tcx.resolver_for_lowering().steal();
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

    let binding_names = macro_binding_names(krate, &resolver);
    AstVisitor {
        tcx,
        resolver: &resolver,
        binding_names,
    }
    .visit_crate(krate);
    crate::preparer::remove_empty_statements(krate);
    pprust::crate_to_string_for_macros(krate)
}

fn resolution(resolver: &ResolverAstLowering, node: ast::NodeId) -> Option<Res<ast::NodeId>> {
    resolver.partial_res_map.get(&node)?.full_res()
}

struct ValueNames<'a> {
    resolver: &'a ResolverAstLowering,
    owner: ast::NodeId,
    occupied: FxHashSet<Symbol>,
    values: FxHashMap<(ast::NodeId, Symbol), FxHashMap<Res<ast::NodeId>, bool>>,
}

impl ValueNames<'_> {
    fn record(&mut self, node: ast::NodeId, ident: Ident) {
        if let Some(res @ (Res::Local(_) | Res::Def(..))) = resolution(self.resolver, node) {
            let hygienic = ident.span.normalize_to_macro_rules().from_expansion();
            *self
                .values
                .entry((self.owner, ident.name))
                .or_default()
                .entry(res)
                .or_default() |= hygienic;
        }
    }
}

impl<'ast> Visitor<'ast> for ValueNames<'_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        let previous = std::mem::replace(&mut self.owner, item.id);
        visit::walk_item(self, item);
        self.owner = previous;
    }

    fn visit_ident(&mut self, ident: &'ast Ident) {
        self.occupied.insert(ident.name);
    }

    fn visit_expr(&mut self, expr: &'ast ast::Expr) {
        if let ast::ExprKind::Path(None, path) = &expr.kind
            && let [segment] = path.segments.as_slice()
        {
            self.record(expr.id, segment.ident);
        }
        visit::walk_expr(self, expr);
    }

    fn visit_pat(&mut self, pat: &'ast ast::Pat) {
        if let ast::PatKind::Ident(_, ident, _) = pat.kind {
            self.record(pat.id, ident);
        }
        visit::walk_pat(self, pat);
    }
}

fn macro_binding_names(
    krate: &ast::Crate,
    resolver: &ResolverAstLowering,
) -> FxHashMap<ast::NodeId, Symbol> {
    let mut names = ValueNames {
        resolver,
        owner: ast::CRATE_NODE_ID,
        occupied: FxHashSet::default(),
        values: FxHashMap::default(),
    };
    names.visit_crate(krate);

    let mut bindings = Vec::new();
    for resolutions in names.values.into_values().filter(|values| values.len() > 1) {
        // A hygienic use can refer to a local from the macro's definition site.
        // It can also bypass a local that would shadow an item in printed Rust.
        let hygienic_item = resolutions
            .iter()
            .any(|(res, &hygienic)| hygienic && matches!(res, Res::Def(..)));
        for (res, hygienic) in resolutions {
            if let Res::Local(binding) = res
                && (hygienic || hygienic_item)
            {
                bindings.push(binding);
            }
        }
    }
    bindings.sort_unstable_by_key(|binding| binding.as_u32());
    bindings.dedup();
    let mut suffixes = 0..;
    bindings
        .into_iter()
        .map(|binding| {
            let name = suffixes
                .by_ref()
                .map(|suffix| Symbol::intern(&format!("__crat_macro_{suffix}")))
                .find(|&name| names.occupied.insert(name))
                .unwrap();
            (binding, name)
        })
        .collect()
}

struct AstVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    resolver: &'a ResolverAstLowering,
    binding_names: FxHashMap<ast::NodeId, Symbol>,
}

impl AstVisitor<'_, '_> {
    fn binding_name(&self, node: ast::NodeId) -> Option<Symbol> {
        let Res::Local(binding) = resolution(self.resolver, node)? else {
            return None;
        };
        self.binding_names.get(&binding).copied()
    }
}

impl MutVisitor for AstVisitor<'_, '_> {
    fn flat_map_stmt(&mut self, statement: ast::Stmt) -> smallvec::SmallVec<[ast::Stmt; 1]> {
        if let ast::StmtKind::Item(item) = &statement.kind
            && matches!(item.kind, ast::ItemKind::MacroDef(..))
            && !item
                .attrs
                .iter()
                .any(|attr| attr.has_name(sym::macro_export))
        {
            return smallvec::smallvec![];
        }
        mut_visit::walk_flat_map_stmt(self, statement)
    }

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
            && let [segment] = path.segments.as_mut_slice()
            && let Some(name) = self.binding_name(expr.id)
        {
            segment.ident.name = name;
        }
        if let ast::ExprKind::Struct(structure) = &mut expr.kind {
            for field in &mut structure.fields {
                if field.is_shorthand && self.binding_name(field.expr.id).is_some() {
                    field.is_shorthand = false;
                }
            }
        }
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

    fn visit_pat(&mut self, pat: &mut ast::Pat) {
        match &mut pat.kind {
            ast::PatKind::Ident(_, ident, _) => {
                if let Some(name) = self.binding_name(pat.id) {
                    ident.name = name;
                }
            }
            ast::PatKind::Struct(_, _, fields, _) => {
                for field in fields {
                    if field.is_shorthand && self.binding_name(field.pat.id).is_some() {
                        field.is_shorthand = false;
                    }
                }
            }
            _ => {}
        }
        mut_visit::walk_pat(self, pat);
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

    fn visit_variant(&mut self, variant: &mut ast::Variant) {
        variant.attrs.retain(|attr| !attr.has_name(kw::Default));
        mut_visit::walk_variant(self, variant);
    }
}

#[cfg(test)]
mod tests;
