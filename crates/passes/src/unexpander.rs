use std::ops::ControlFlow;

use etrace::some_or;
use rustc_ast::{
    mut_visit::{self, MutVisitor},
    ptr::P,
    visit::{self, Visitor},
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, QPath, def::Res, def_id::LocalDefId, intravisit, intravisit::Visitor as _,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::{DUMMY_SP, Symbol, kw, sym};
use serde::Deserialize;
use smallvec::{SmallVec, smallvec};
use thin_vec::thin_vec;
use utils::{
    ast::{unwrap_paren, unwrap_paren_mut},
    attr, expr, item,
};

#[derive(Debug, Default, Clone, Copy, Deserialize)]
pub struct Config {
    pub use_print: bool,
}

pub fn unexpand(config: Config, tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

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
        config,
    };
    visitor.visit_crate(&mut krate);

    let mut unnecessary_attributes: FxHashSet<_> = [
        "derive_clone_copy",
        "hint_must_use",
        "never_type",
        "panic_internals",
        "thread_local_internals",
        "coverage_attribute",
    ]
    .into_iter()
    .collect();
    if !visitor.ctx.use_intrinsics {
        unnecessary_attributes.insert("core_intrinsics");
    }

    krate.attrs.retain(|attr| {
        if let AttrKind::Normal(attr) = &attr.kind
            && attr.item.path.segments.last().unwrap().ident.name == sym::feature
            && let Some(arg) = utils::ast::get_attr_arg(&attr.item.args)
            && let arg = arg.as_str()
            && unnecessary_attributes.contains(arg)
        {
            return false;
        }
        if !visitor.ctx.use_transmute
            && let AttrKind::Normal(attr) = &attr.kind
            && attr.item.path.segments.last().unwrap().ident.name == sym::warn
            && let Some(arg) = utils::ast::get_attr_arg(&attr.item.args)
            && arg.as_str() == "mutable_transmutes"
        {
            return false;
        }
        true
    });

    pprust::crate_to_string_for_macros(&krate)
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: utils::ir::AstToHir,
    ctx: Ctx,
    config: Config,
}

impl MutVisitor for AstVisitor<'_> {
    fn flat_map_item(&mut self, item: P<Item>) -> SmallVec<[P<Item>; 1]> {
        if utils::ast::is_automatically_derived(&item.attrs) {
            return smallvec![];
        }
        mut_visit::walk_flat_map_item(self, item)
    }

    fn visit_item(&mut self, item: &mut Item) {
        if matches!(
            item.kind,
            ItemKind::Struct(..) | ItemKind::Union(..) | ItemKind::Enum(..)
        ) {
            let local_def_id = self.ast_to_hir.global_map.get(&item.id).unwrap();
            if let Some(traits) = self.ctx.derived_traits.get(local_def_id) {
                for t in traits {
                    if *t == sym::StructuralPartialEq {
                        continue;
                    }
                    let attr = utils::ast::make_outer_attribute(sym::derive, *t, self.tcx);
                    item.attrs.push(attr);
                }
            }
        }
        match &mut item.kind {
            ItemKind::Struct(_, _, vd) => {
                let local_def_id = self.ast_to_hir.global_map.get(&item.id).unwrap();
                if let Some(bitfields) = self.ctx.bitfields.get(local_def_id) {
                    let VariantData::Struct { fields, .. } = vd else { panic!() };
                    for field in fields {
                        let bitfields =
                            some_or!(bitfields.get(&field.ident.unwrap().name), continue);
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
            ItemKind::Const(const_item) => {
                if let TyKind::Path(_, path) = &const_item.ty.kind
                    && let Some(seg) = path.segments.last()
                    && seg.ident.name == sym::LocalKey
                    && let Some(box GenericArgs::AngleBracketed(args)) = &seg.args
                    && let [AngleBracketedArg::Arg(GenericArg::Type(ty))] = &args.args[..]
                    && let Some(init) = &const_item.expr
                    && let ExprKind::Block(block, _) = &init.kind
                    && let [stmt, ..] = &block.stmts[..]
                    && let StmtKind::Item(stmt_item) = &stmt.kind
                    && let ItemKind::Const(inner_item) = &stmt_item.kind
                    && inner_item.ident.name.as_str() == "__INIT"
                    && let Some(init) = &inner_item.expr
                    && let ExprKind::Block(block, _) = &init.kind
                    && let [stmt] = &block.stmts[..]
                    && let StmtKind::Expr(init) = &stmt.kind
                {
                    let name = const_item.ident.name;
                    let ty = pprust::ty_to_string(ty);
                    let init = pprust::expr_to_string(init);
                    *item = item!("thread_local! {{ static {name}: {ty} = const {{ {init} }}; }}");
                }
            }
            _ => {}
        }
        mut_visit::walk_item(self, item);
    }

    fn flat_map_stmt(&mut self, stmt: Stmt) -> SmallVec<[Stmt; 1]> {
        let mut stmts = mut_visit::walk_flat_map_stmt(self, stmt);
        for stmt in &mut stmts {
            // { use std::io::Write; print!(..) }; => print!(..);
            if let StmtKind::Semi(e) = &mut stmt.kind
                && let ExprKind::Block(block, _) = &mut e.kind
                && let [stmt1, stmt2] = &mut block.stmts[..]
                && let StmtKind::Item(item) = &stmt1.kind
                && matches!(item.kind, ItemKind::Use(_))
                && let StmtKind::Expr(expr) = &mut stmt2.kind
                && let expr = unwrap_paren_mut(expr)
                && let ExprKind::MacCall(mac) = &expr.kind
                && let name = mac.path.segments.last().unwrap().ident.name.as_str()
                && (name == "print" || name == "eprint")
            {
                let dummy = Expr {
                    id: DUMMY_NODE_ID,
                    kind: ExprKind::Dummy,
                    span: DUMMY_SP,
                    attrs: thin_vec![],
                    tokens: None,
                };
                let expr: Expr = std::mem::replace(expr, dummy);
                **e = expr;
            }
        }
        stmts
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        if let ExprKind::Call(callee, args) = &expr.kind
            && let ExprKind::Path(None, callee) = &callee.kind
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
                    if let ExprKind::Lit(lit) = &arg.kind
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
        } else if let ExprKind::Match(scrutinee, arms, _) = &mut expr.kind
            && let scrutinee = unwrap_paren_mut(scrutinee)
            && let ExprKind::MethodCall(call) = &scrutinee.kind
            && call.seg.ident.name == rustc_span::sym::write_fmt
            && let [arg] = &call.args[..]
            && let arg = unwrap_paren(arg)
            && matches!(arg.kind, ExprKind::FormatArgs(_))
        {
            let is_empty = arms.iter().all(|arm| {
                if let ExprKind::Block(block, _) = &arm.body.as_ref().unwrap().kind {
                    block.stmts.is_empty()
                } else {
                    false
                }
            });
            let receiver = unwrap_addr_of(&call.receiver);
            let name = if let ExprKind::Call(callee, args) = &receiver.kind
                && args.is_empty()
                && let ExprKind::Path(_, path) = &unwrap_paren(callee).kind
            {
                Some(path.segments.last().unwrap().ident.name)
            } else {
                None
            };
            let format = pprust::expr_to_string(arg);
            let format = format.strip_prefix("format_args!(").unwrap();
            if self.config.use_print
                && is_empty
                && let Some(name) = name
                && name.as_str() == "stdout"
            {
                *expr = utils::expr!("print!({format}");
            } else if self.config.use_print
                && is_empty
                && let Some(name) = name
                && name.as_str() == "stderr"
            {
                *expr = utils::expr!("eprint!({format}");
            } else {
                let receiver = pprust::expr_to_string(&call.receiver);
                *scrutinee = utils::expr!("write!({receiver}, {format}");
            }
        }
        mut_visit::walk_expr(self, expr);
    }
}

fn unwrap_addr_of(expr: &Expr) -> &Expr {
    if let ExprKind::AddrOf(_, _, e) | ExprKind::Paren(e) = &expr.kind {
        unwrap_addr_of(e)
    } else {
        expr
    }
}

#[derive(Default)]
struct Ctx {
    derived_traits: FxHashMap<LocalDefId, Vec<Symbol>>,
    bitfields: FxHashMap<LocalDefId, FxHashMap<Symbol, Vec<BitField>>>,
    use_intrinsics: bool,
    use_transmute: bool,
}

struct BitField {
    name: Symbol,
    ty: String,
    l: u128,
    r: u128,
}

struct Previsitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: utils::ir::AstToHir,
    ctx: Ctx,
}

impl<'ast> Visitor<'ast> for Previsitor<'_> {
    fn visit_item(&mut self, item: &'ast Item) {
        if utils::ast::is_automatically_derived(&item.attrs)
            && matches!(item.kind, ItemKind::Impl(_))
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

    fn visit_path(&mut self, path: &'ast ast::Path) {
        if let [pre @ .., _] = &path.segments[..]
            && pre.iter().any(|s| s.ident.name == sym::intrinsics)
        {
            self.ctx.use_intrinsics = true;
        }
        if path.segments.last().unwrap().ident.name == sym::transmute {
            self.ctx.use_transmute = true;
        }
        visit::walk_path(self, path);
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

#[cfg(test)]
mod tests {
    fn run_test(code: &str, includes: &[&str], excludes: &[&str]) {
        let config = super::Config { use_print: true };
        let s = utils::compilation::run_compiler_on_str(code, |tcx| super::unexpand(config, tcx))
            .unwrap();
        utils::compilation::run_compiler_on_str(&s, utils::type_check).expect(&s);
        for include in includes {
            assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
        }
        for exclude in excludes {
            assert!(
                !s.contains(exclude),
                "Expected not to find `{exclude}` in:\n{s}"
            );
        }
    }

    #[test]
    fn test_print() {
        run_test(
            r#"
fn f() {
    use std::io::Write;
    match (&mut std::io::stdout()).write_fmt(format_args!("")) {
        Ok(_) => {}
        Err(_) => {}
    };
}
            "#,
            &["print!"],
            &["stdout", "write_fmt", "format_args"],
        )
    }

    #[test]
    fn test_eprint() {
        run_test(
            r#"
fn f() {
    use std::io::Write;
    match (&mut std::io::stderr()).write_fmt(format_args!("")) {
        Ok(_) => {}
        Err(_) => {}
    };
}
            "#,
            &["eprint!"],
            &["stdout", "write_fmt", "format_args"],
        )
    }

    #[test]
    fn test_write() {
        run_test(
            r#"
fn f() {
    use std::io::Write;
    let x: i32 = match (&mut std::io::stdout()).write_fmt(format_args!("")) {
        Ok(_) => (0, 0),
        Err(_) => (-1, 1),
    }.0;
}
            "#,
            &["write!"],
            &["write_fmt", "format_args"],
        )
    }
}
