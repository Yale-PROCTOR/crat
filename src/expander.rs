use std::sync::Arc;

use rustc_ast::{
    self as ast,
    mut_visit::{self, MutVisitor},
};
use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;
use rustc_span::{DUMMY_SP, Symbol, sym};

use crate::ast_util;

pub fn expand(tcx: TyCtxt<'_>) -> String {
    let (_, mut krate) = tcx.resolver_for_lowering().steal();
    let krate = Arc::get_mut(&mut krate).unwrap();
    ast_util::remove_unnecessary_items_from_ast(krate);
    krate.attrs.clear();
    krate.attrs.extend([
        make_attribute(sym::warn, Symbol::intern("mutable_transmutes"), tcx),
        make_attribute(sym::feature, sym::c_variadic, tcx),
        make_attribute(sym::feature, sym::extern_types, tcx),
        make_attribute(sym::feature, sym::linkage, tcx),
        make_attribute(sym::feature, sym::rustc_private, tcx),
        make_attribute(sym::feature, sym::thread_local, tcx),
        make_attribute(sym::feature, Symbol::intern("core_intrinsics"), tcx),
        make_attribute(sym::feature, Symbol::intern("derive_clone_copy"), tcx),
        make_attribute(sym::feature, Symbol::intern("hint_must_use"), tcx),
        make_attribute(sym::feature, Symbol::intern("panic_internals"), tcx),
    ]);
    AstVisitor.visit_crate(krate);
    pprust::crate_to_string_for_macros(krate)
}

fn make_attribute(outer: Symbol, inner: Symbol, tcx: TyCtxt<'_>) -> ast::Attribute {
    let g = &tcx.sess.psess.attr_id_generator;
    ast::attr::mk_attr_nested_word(
        g,
        ast::AttrStyle::Inner,
        ast::Safety::Default,
        outer,
        inner,
        DUMMY_SP,
    )
}

#[allow(unused)]
fn get_attr_arg(args: &ast::AttrArgs) -> Option<Symbol> {
    let ast::AttrArgs::Delimited(args) = args else { return None };
    let mut tokens = args.tokens.iter();
    let first = tokens.next()?;
    let ast::tokenstream::TokenTree::Token(token, _) = first else { return None };
    let ast::token::TokenKind::Ident(sym, _) = token.kind else { return None };
    Some(sym)
}

struct AstVisitor;

impl MutVisitor for AstVisitor {
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
