use std::path::PathBuf;

use etrace::some_or;
use rustc_ast::{ptr::P, *};
use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;
use rustc_parse::parser::{AttemptLocalParseRecovery, ForceCollect, Parser};
use rustc_session::parse::ParseSess;
use rustc_span::{DUMMY_SP, FileName, RealFileName, Symbol, sym};
use thin_vec::ThinVec;

use crate::ir;

/// Returns the expanded AST. The returned AST contains only dummay `NodeId`.
///
/// Note that the function will panic if called after the HIR is built.
pub fn expanded_ast(tcx: TyCtxt<'_>) -> Crate {
    tcx.resolver_for_lowering().borrow().1.as_ref().clone()
}

/// The first argument should be the `Crate` returned by `expanded_ast`.
///
/// Each AST node will get a unique `NodeId` while this function is running.
pub fn make_ast_to_hir(krate: &mut Crate, tcx: TyCtxt<'_>) -> ir::AstToHir {
    let mut mapper = ir::AstToHirMapper::new(tcx);
    let module = tcx.hir_root_module();
    mapper.map_crate_to_mod(krate, module, true);
    mapper.ast_to_hir
}

/// This function removes the following items, which make the program incompilable when
/// pretty-printed back to source code, from the expanded AST:
///
/// ```rust,ignore
/// #[prelude_import]
/// use std::prelude::rust_2021::*;
/// #[macro_use]
/// extern crate std;
/// ```
///
/// If mapping is needed, this function should be called after `make_ast_to_hir`.
pub fn remove_unnecessary_items_from_ast(krate: &mut Crate) {
    krate.items.retain(|item| match item.kind {
        ItemKind::ExternCrate(_, ident) => ident.name != sym::std,
        ItemKind::Use(_) => !item.attrs.iter().any(|attr| {
            let AttrKind::Normal(attr) = &attr.kind else { return false };
            attr.item.path.segments.last().unwrap().ident.name == sym::prelude_import
        }),
        _ => true,
    });
}

pub fn make_inner_attribute(outer: Symbol, inner: Symbol, tcx: TyCtxt<'_>) -> Attribute {
    let g = &tcx.sess.psess.attr_id_generator;
    attr::mk_attr_nested_word(g, AttrStyle::Inner, Safety::Default, outer, inner, DUMMY_SP)
}

pub fn make_outer_attribute(outer: Symbol, inner: Symbol, tcx: TyCtxt<'_>) -> Attribute {
    let g = &tcx.sess.psess.attr_id_generator;
    attr::mk_attr_nested_word(g, AttrStyle::Outer, Safety::Default, outer, inner, DUMMY_SP)
}

pub fn is_automatically_derived(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let AttrKind::Normal(attr) = &attr.kind else { return false };
        let path = attr.item.path.segments.last().unwrap().ident.name;
        path == rustc_span::sym::automatically_derived
    })
}

pub fn get_attr_arg(args: &AttrArgs) -> Option<Symbol> {
    let AttrArgs::Delimited(args) = args else { return None };
    let mut tokens = args.tokens.iter();
    let first = tokens.next()?;
    let tokenstream::TokenTree::Token(token, _) = first else { return None };
    let token::TokenKind::Ident(sym, _) = token.kind else { return None };
    Some(sym)
}

pub fn unwrap_paren(expr: &Expr) -> &Expr {
    if let ExprKind::Paren(e) = &expr.kind {
        unwrap_paren(e)
    } else {
        expr
    }
}

pub fn unwrap_paren_mut(expr: &mut Expr) -> &mut Expr {
    if matches!(&expr.kind, ExprKind::Paren(_)) {
        let ExprKind::Paren(e) = &mut expr.kind else { unreachable!() };
        unwrap_paren_mut(e)
    } else {
        expr
    }
}

pub fn unwrap_cast_and_paren(e: &Expr) -> &Expr {
    if let ExprKind::Cast(e, _) | ExprKind::Paren(e) = &e.kind {
        unwrap_cast_and_paren(e)
    } else {
        e
    }
}

pub fn unwrap_cast_and_paren_mut(expr: &mut Expr) -> &mut Expr {
    if matches!(&expr.kind, ExprKind::Paren(_) | ExprKind::Cast(_, _)) {
        let (ExprKind::Paren(e) | ExprKind::Cast(e, _)) = &mut expr.kind else { unreachable!() };
        unwrap_paren_mut(e)
    } else {
        expr
    }
}

#[derive(Debug)]
pub struct TransformationResult(pub Vec<(PathBuf, String)>);

impl TransformationResult {
    pub fn apply(&self) {
        for (path, content) in &self.0 {
            std::fs::write(path, content).unwrap();
        }
    }
}

pub fn foreach_crate<F: std::ops::FnMut(Crate)>(mut f: F, tcx: TyCtxt<'_>) {
    tcx.resolver_for_lowering();

    let source_map = tcx.sess.source_map();
    let parse_sess = new_parse_sess();

    for file in source_map.files().iter() {
        if !matches!(
            file.name,
            FileName::Real(RealFileName::LocalPath(_)) | FileName::Custom(_)
        ) {
            continue;
        }
        let src = some_or!(file.src.as_ref(), continue);
        let mut parser = rustc_parse::new_parser_from_source_str(
            &parse_sess,
            file.name.clone(),
            src.to_string(),
        )
        .unwrap();
        let krate = parser.parse_crate_mod().unwrap();
        f(krate);
    }
}

pub fn transform_ast<F: std::ops::FnMut(&mut Crate) -> bool>(
    mut f: F,
    tcx: TyCtxt<'_>,
) -> TransformationResult {
    tcx.resolver_for_lowering();

    let source_map = tcx.sess.source_map();
    let parse_sess = new_parse_sess();

    let mut v = vec![];
    for file in source_map.files().iter() {
        let p = match &file.name {
            FileName::Real(RealFileName::LocalPath(p)) => p.clone(),
            FileName::Custom(p) => PathBuf::from(p),
            _ => continue,
        };
        let src = some_or!(file.src.as_ref(), continue);
        let mut parser = rustc_parse::new_parser_from_source_str(
            &parse_sess,
            file.name.clone(),
            src.to_string(),
        )
        .unwrap();
        let mut krate = parser.parse_crate_mod().unwrap();
        if f(&mut krate) {
            let s = pprust::crate_to_string_for_macros(&krate);
            v.push((p, s));
        }
    }
    TransformationResult(v)
}

#[inline]
pub fn new_parse_sess() -> ParseSess {
    ParseSess::with_fatal_emitter(vec![], "".to_string())
}

#[inline]
pub fn new_parser_from_str(parse_sess: &ParseSess, s: String) -> Parser<'_> {
    let file_name = FileName::Custom("main.rs".to_string());
    rustc_parse::new_parser_from_source_str(parse_sess, file_name, s).unwrap()
}

#[inline]
pub fn parse_crate(krate: String) -> Crate {
    let parse_sess = new_parse_sess();
    let mut parser = new_parser_from_str(&parse_sess, krate);
    parser.parse_crate_mod().unwrap()
}

#[macro_export]
macro_rules! krate {
    ($($arg:tt)*) => {{
        parse_crate(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_item(item: String) -> Item {
    let parse_sess = new_parse_sess();
    let mut parser = new_parser_from_str(&parse_sess, item);
    *parser.parse_item(ForceCollect::No).unwrap().unwrap()
}

#[macro_export]
macro_rules! item {
    ($($arg:tt)*) => {{
        $crate::ast::parse_item(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_items(items: String) -> ThinVec<P<Item>> {
    let krate = parse_crate(items);
    krate.items
}

#[macro_export]
macro_rules! items {
    ($($arg:tt)*) => {{
        $crate::ast::parse_items(format!($($arg)*))
    }};
}

pub fn parse_ty_param(param: String) -> GenericParam {
    let item = item!("fn f<{}>() {{}}", param);
    let ItemKind::Fn(box mut f) = item.kind else { panic!() };
    f.generics.params.pop().unwrap()
}

#[macro_export]
macro_rules! ty_param {
    ($($arg:tt)*) => {{
        $crate::ast::parse_ty_param(format!($($arg)*))
    }};
}

pub fn parse_param(param: String) -> Param {
    let item = item!("fn f({}) {{}}", param);
    let ItemKind::Fn(box mut f) = item.kind else { panic!() };
    f.sig.decl.inputs.pop().unwrap()
}

#[macro_export]
macro_rules! param {
    ($($arg:tt)*) => {{
        $crate::ast::parse_param(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_stmt(stmt: String) -> Stmt {
    let parse_sess = new_parse_sess();
    let mut parser = new_parser_from_str(&parse_sess, stmt);
    parser
        .parse_full_stmt(AttemptLocalParseRecovery::No)
        .unwrap()
        .unwrap()
}

#[macro_export]
macro_rules! stmt {
    ($($arg:tt)*) => {{
        $crate::ast::parse_stmt(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_expr(expr: String) -> Expr {
    let parse_sess = new_parse_sess();
    let mut parser = new_parser_from_str(&parse_sess, expr);
    *parser.parse_expr().unwrap()
}

#[macro_export]
macro_rules! expr {
    ($($arg:tt)*) => {{
        $crate::ast::parse_expr(format!($($arg)*))
    }};
}

pub fn parse_path(path: String) -> Path {
    let ExprKind::Path(_, path) = parse_expr(path).kind else { panic!() };
    path
}

#[macro_export]
macro_rules! path {
    ($($arg:tt)*) => {{
        $crate::ast::parse_path(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_pat(pat: String) -> Pat {
    let parse_sess = new_parse_sess();
    let mut parser = new_parser_from_str(&parse_sess, pat);
    *parser
        .parse_pat_allow_top_guard(
            None,
            rustc_parse::parser::RecoverComma::No,
            rustc_parse::parser::RecoverColon::No,
            rustc_parse::parser::CommaRecoveryMode::LikelyTuple,
        )
        .unwrap()
}

#[macro_export]
macro_rules! pat {
    ($($arg:tt)*) => {{
        $crate::ast::parse_pat(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_ty(ty: String) -> Ty {
    let parse_sess = new_parse_sess();
    let mut parser = new_parser_from_str(&parse_sess, ty);
    *parser.parse_ty().unwrap()
}

#[macro_export]
macro_rules! ty {
    ($($arg:tt)*) => {{
        $crate::ast::parse_ty(format!($($arg)*))
    }};
}

pub fn parse_attr(attr: String) -> ThinVec<Attribute> {
    let item = item!("{attr} mod a;");
    item.attrs
}

#[macro_export]
macro_rules! attr {
    ($($arg:tt)*) => {{
        $crate::ast::parse_attr(format!($($arg)*))
    }};
}
