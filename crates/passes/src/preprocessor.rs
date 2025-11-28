//! Preprocessor
//!
//! # Deduplicate asserts
//!
//! C2Rust may generate code like below:
//!
//! ```rust,ignore
//! if cond {
//! } else {
//!     __assert_fail();
//! }
//! 'c: {
//!     if cond {
//!     } else {
//!         __assert_fail();
//!     }
//! }
//! ```
//!
//! We deduplicate such asserts as follows:
//!
//! ```rust,ignore
//! if cond {
//! } else {
//!     __assert_fail();
//! }
//! 'c: {}
//! ```
//! Remove unreachable
//!
//! Some code may exist after non-returning expressions, like below:
//!
//! ```rust,ignore
//! __assert_fail();
//! 'c: {
//!     __assert_fail();
//! }
//! ```
//!
//! We remove such unreachable code as follows:
//!
//! ```rust,ignore
//! __assert_fail();
//! ```
//!
//! # Remove dead code
//!
//! Some code contains dead code like below:
//!
//! ```rust,ignore
//! if 0 != 0 {
//!     foo();
//! }
//! ```
//!
//! We remove such dead code as follows:
//!
//! ```rust,ignore
//! {}
//! ```
//!
//! # Simplify `Some`-`unwrap`
//!
//! C2Rust may generate code like below:
//!
//! ```rust,ignore
//! (Some(p.unwrap())).unwrap()();
//! ```
//!
//! We simplify such code as follows:
//!
//! ```rust,ignore
//! p.unwrap()();
//! ```
//!
//! # Remove parameter-assigned variables
//!
//! Some functions assign parameters to variables and never use the parameters again, like below:
//!
//! ```rust,ignore
//! fn foo(x: i32) {
//!     let y = x;
//!     bar(y);
//! }
//! ```
//!
//! We remove such variables as follows:
//!
//! ```rust,ignore
//! fn foo(x: i32) {
//!     {}
//!     bar(x);
//! }
//! ```
//!
//! # Hoist pointer arguments
//!
//! Some function calls use the same pointer arguments multiple times, like below:
//!
//! ```rust,ignore
//! foo(p, bar(p, 0));
//! ```
//!
//! We hoist such pointer arguments as follows:
//!
//! ```rust,ignore
//! {
//!     let __arg_1 = bar(p, 0);
//!     foo(p, __arg_1)
//! };
//! ```
//!
//! Some I/O API function calls use conditional arguments, like below:
//!
//! ```rust,ignore
//! fgetc(if cond { p } else { q });
//! ```
//!
//! We hoist such arguments as follows:
//!
//! ```rust,ignore
//! {
//!     let __arg_1 = if cond { p } else { q };
//!     fgetc(__arg_1);
//! };
//! ```
//!
//! # Replace file function pointer type aliases
//!
//! Some type aliases contain function pointers types with `FILE *`, like below:
//!
//! ```rust,ignore
//! type func = Option::<fn(*mut FILE)>;
//! fn foo(x: func) {}
//! ```
//!
//! We replace such type aliases with corresponding types as follows:
//!
//! ```rust,ignore
//! fn foo(x: Option::<fn(*mut FILE)>) {}
//! ```
//!
//! # Remove `let ref`
//!
//! C2Rust may generate code like below:
//!
//! ```rust,ignore
//! let ref mut fresh0 = *p.offset(0 as libc::c_int as isize);
//! *fresh0 += 1;
//! ```
//!
//! We replace such code with the following code:
//!
//! ```rust,ignore
//! *p.offset(0 as libc::c_int as isize) += 1;
//! ```
//!
//! # Remove `transmute`
//!
//! C2Rust may generate code like below:
//!
//! ```rust,ignore
//! *::std::mem::transmute::<
//!     &[u8; 2],
//!     &mut [libc::c_char; 2],
//! >(b"a\0");
//! ```
//!
//! We replace such code with the following code:
//!
//! ```rust,ignore
//! [b'a' as i8, b'\0' as i8];
//! ```
//!
//! C2Rust may generate code like below:
//!
//! ```rust,ignore
//! ::std::mem::transmute::<
//!     [u8; 2],
//!     [libc::c_char; 2],
//! >(*b"a\0");
//! ```
//!
//! We replace such code with the following code:
//!
//! ```rust,ignore
//! [b'a' as i8, b'\0' as i8];
//! ```
//!
//! # Remove `fresh`
//!
//! C2Rust may generate code like below:
//!
//! ```rust,ignore
//! let fresh0 = p;
//! p = p.offset(1);
//! *fresh0;
//! ```
//!
//! We replace such code with the following code:
//!
//! ```rust,ignore
//! let fresh0 = *p;
//! p = p.offset(1);
//! fresh0;
//! ```
//!
//! C2Rust may generate code like below:
//!
//! ```rust,ignore
//! let fresh0 = p;
//! p = p.offset(1);
//! *fresh0 = 0;
//! *fresh0;
//! ```
//!
//! We replace such code with the following code:
//!
//! ```rust,ignore
//! *p = 0;
//! let fresh0 = *p;
//! p = p.offset(1);
//! fresh0;
//! ```

use std::fmt::Write as _;

use etrace::some_or;
use rustc_ast::{mut_visit::MutVisitor as _, *};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_hir::{
    HirId, QPath,
    def::{DefKind, Res},
    intravisit,
};
use rustc_middle::{hir::nested_filter, ty, ty::TyCtxt};
use rustc_span::{Span, Symbol, sym};
use utils::{
    expr,
    ir::{AstToHir, mir_ty_to_string},
    ty,
};

pub fn preprocess(tcx: TyCtxt<'_>) -> String {
    let mut expanded_ast = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut expanded_ast, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut expanded_ast);

    let mut visitor = HirVisitor {
        tcx,
        ctx: HirCtx::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

    let mut lets_to_remove = FxHashSet::default();
    let mut vars_to_replace = FxHashMap::default();
    let mut params_to_be_mut = FxHashSet::default();
    for (rhs, lhs) in &visitor.ctx.rhs_to_lhs {
        if lhs.len() > 1 || visitor.ctx.used_vars.contains(rhs) {
            continue;
        }
        let name = some_or!(visitor.ctx.params.get(rhs), continue);
        let lhs = lhs[0];
        let is_in_loop = tcx.hir_parent_iter(lhs.let_stmt).any(|(_, node)| {
            let hir::Node::Expr(expr) = node else { return false };
            matches!(expr.kind, hir::ExprKind::Loop(..))
        });
        if is_in_loop {
            continue;
        }
        lets_to_remove.insert(lhs.let_stmt);
        params_to_be_mut.insert(*rhs);
        vars_to_replace.insert(lhs.variable, *name);
    }

    let mut fresh_pointers = FxHashSet::default();
    let mut fresh_pointer_renames = FxHashMap::default();
    let mut stmt_swaps: FxHashMap<_, Vec<_>> = FxHashMap::default();
    for lhs in visitor.ctx.rhs_to_lhs.values() {
        for lhs in lhs {
            if lhs.is_mutable {
                continue;
            }
            let pointer_uses = some_or!(visitor.ctx.pointer_uses.get(&lhs.variable), continue);
            if pointer_uses.iter().all(|u| *u == PointerUse::RvalueDeref) {
                fresh_pointers.insert(lhs.variable);
            } else if let [PointerUse::LvalueDeref, rems @ ..] = &pointer_uses[..]
                && rems.iter().all(|u| *u == PointerUse::RvalueDeref)
                && let Some(fresh_let) = visitor.ctx.fresh_lets.get(&lhs.variable)
            {
                fresh_pointers.insert(lhs.variable);
                stmt_swaps
                    .entry(fresh_let.block)
                    .or_default()
                    .push(fresh_let.stmt_idx);
                let symbol = if let Some(symbol) = vars_to_replace.get(&fresh_let.rhs) {
                    *symbol
                } else {
                    tcx.hir_name(fresh_let.rhs)
                };
                fresh_pointer_renames.insert(lhs.variable, symbol);
            }
        }
    }

    let mut visitor = AstVisitor {
        tcx,
        ast_to_hir,
        lets_to_remove,
        vars_to_replace,
        params_to_be_mut,
        call_to_if_args: visitor.ctx.call_to_if_args,
        call_to_nested_args: visitor.ctx.call_to_nested_args,
        let_ref_exprs: FxHashMap::default(),
        fresh_pointers,
        fresh_pointer_renames,
        stmt_swaps,
    };

    visitor.visit_crate(&mut expanded_ast);
    pprust::crate_to_string_for_macros(&expanded_ast)
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    lets_to_remove: FxHashSet<HirId>,
    params_to_be_mut: FxHashSet<HirId>,
    vars_to_replace: FxHashMap<HirId, Symbol>,
    call_to_if_args: FxHashMap<HirId, Vec<ArgIdx>>,
    call_to_nested_args: FxHashMap<HirId, Vec<ArgIdx>>,
    let_ref_exprs: FxHashMap<HirId, Expr>,
    fresh_pointers: FxHashSet<HirId>,
    fresh_pointer_renames: FxHashMap<HirId, Symbol>,
    stmt_swaps: FxHashMap<HirId, Vec<usize>>,
}

impl mut_visit::MutVisitor for AstVisitor<'_> {
    fn visit_ty(&mut self, ty: &mut Ty) {
        mut_visit::walk_ty(self, ty);

        if let Some(hir_ty) = self.ast_to_hir.get_ty(ty.id, self.tcx)
            && let hir::TyKind::Path(QPath::Resolved(_, path)) = hir_ty.kind
            && let Res::Def(DefKind::TyAlias, def_id) = path.res
        {
            let mir_ty = self.tcx.type_of(def_id).skip_binder();
            if utils::file::file_param_index(mir_ty, self.tcx).is_some()
                || mir_ty.is_numeric() && is_libc_ty(path.segments.last().unwrap().ident.as_str())
            {
                *ty = ty!("{}", mir_ty_to_string(mir_ty, self.tcx));
            }
        }
    }

    fn visit_block(&mut self, b: &mut Block) {
        if let Some((i, _)) = b.stmts.iter().enumerate().find(|(_, stmt)| {
            let StmtKind::Semi(e) = &stmt.kind else { return false };
            let hir_expr = self.ast_to_hir.get_expr(e.id, self.tcx).unwrap();
            let typeck = self.tcx.typeck(hir_expr.hir_id.owner.def_id);
            typeck.expr_ty(hir_expr).is_never()
        }) {
            b.stmts.truncate(i + 1);
        }

        let mut assert = false;
        for stmt in &mut b.stmts {
            if assert {
                assert = false;
                let StmtKind::Semi(e) = &mut stmt.kind else { continue };
                let ExprKind::Block(b, Some(_)) = &mut e.kind else { continue };
                let [stmt] = &b.stmts[..] else { continue };
                if is_assert_stmt(stmt) {
                    b.stmts.clear();
                }
            } else {
                assert = is_assert_stmt(stmt);
            }
        }

        mut_visit::walk_block(self, b);

        if let Some(hir_block) = self.ast_to_hir.get_block(b.id, self.tcx)
            && let Some(indices) = self.stmt_swaps.get(&hir_block.hir_id)
        {
            for i in indices {
                b.stmts.swap(*i + 1, *i + 2);
                b.stmts.swap(*i, *i + 1);
            }
        }

        b.stmts.retain(|stmt| {
            if let StmtKind::Let(local) = &stmt.kind
                && let Some(hir_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx)
                && self.lets_to_remove.contains(&hir_stmt.hir_id)
            {
                false
            } else {
                true
            }
        });
    }

    fn visit_local(&mut self, local: &mut Local) {
        mut_visit::walk_local(self, local);

        if let Some(hir_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx)
            && let hir::PatKind::Binding(mode, id, _, _) = hir_stmt.pat.kind
            && let LocalKind::Init(box e) = &mut local.kind
        {
            if matches!(mode, hir::BindingMode(hir::ByRef::Yes(_), _))
                && matches!(e.kind, ExprKind::Unary(UnOp::Deref, _))
            {
                self.let_ref_exprs.insert(id, e.clone());
                self.lets_to_remove.insert(hir_stmt.hir_id);
            } else if self.fresh_pointers.contains(&id) {
                *e = expr!("*{}", pprust::expr_to_string(e));
            }
        }
    }

    fn visit_param(&mut self, param: &mut Param) {
        if let PatKind::Ident(mode, _, _) = &mut param.pat.kind
            && let Some(hir_param) = self.ast_to_hir.get_param(param.id, self.tcx)
            && let hir::PatKind::Binding(_, hir_id, _, _) = hir_param.pat.kind
            && self.params_to_be_mut.contains(&hir_id)
        {
            mode.1 = Mutability::Mut;
        }

        mut_visit::walk_param(self, param);
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::Path(_, _) => {
                if let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx)
                    && let hir::ExprKind::Path(QPath::Resolved(_, path)) = hir_expr.kind
                    && let Res::Local(hir_id) = path.res
                    && let Some(name) = self.vars_to_replace.get(&hir_id)
                {
                    *expr = expr!("{name}");
                }
            }
            ExprKind::If(c, t, f) => {
                if let Some(Value::Bool(b)) = eval_expr(c) {
                    if b {
                        let e = Expr {
                            id: DUMMY_NODE_ID,
                            kind: ExprKind::Block(t.clone(), None),
                            span: expr.span,
                            attrs: expr.attrs.clone(),
                            tokens: expr.tokens.clone(),
                        };
                        *expr = e;
                    } else if let Some(f) = f {
                        *expr = *f.clone();
                    } else {
                        *expr = expr!("{{}}");
                    }
                }
            }
            ExprKind::Unary(UnOp::Deref, e) => {
                if let Some(hir_e) = self.ast_to_hir.get_expr(e.id, self.tcx)
                    && let hir::ExprKind::Path(QPath::Resolved(_, path)) = hir_e.kind
                    && let Res::Local(hir_id) = path.res
                    && self.fresh_pointers.contains(&hir_id)
                {
                    if let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx)
                        && is_lhs(hir_expr, self.tcx)
                    {
                        let sym = self.fresh_pointer_renames[&hir_id];
                        **e = expr!("{sym}");
                    } else {
                        *expr = (**e).clone();
                    }
                } else if let ExprKind::Call(callee, args) = &e.kind
                    && let ExprKind::Path(_, path) = &callee.kind
                    && let [.., seg] = &path.segments[..]
                    && seg.ident.name == sym::transmute
                    && let [arg] = &args[..]
                    && let ExprKind::Lit(lit) = &arg.kind
                    && matches!(lit.kind, token::LitKind::ByteStr)
                    && let Some(hir_e) = self.ast_to_hir.get_expr(e.id, self.tcx)
                    && let typeck = self.tcx.typeck(hir_e.hir_id.owner)
                    && let e_ty = typeck.expr_ty(hir_e)
                    && let ty::TyKind::Ref(_, inner_ty, _) = e_ty.kind()
                    && let ty::TyKind::Array(elem_ty, _) = inner_ty.kind()
                    && let ty::TyKind::Int(ty::IntTy::I8) | ty::TyKind::Uint(ty::UintTy::U8) =
                        elem_ty.kind()
                {
                    *expr = transmute_expr(lit.symbol.as_str(), *elem_ty);
                }
            }
            _ => {}
        }

        mut_visit::walk_expr(self, expr);

        let expr_id = expr.id;
        match &mut expr.kind {
            ExprKind::Call(callee, args) => {
                if let ExprKind::Path(_, path) = &callee.kind
                    && let [.., seg] = &path.segments[..]
                    && seg.ident.name == sym::transmute
                    && let [arg] = &args[..]
                    && let ExprKind::Unary(UnOp::Deref, arg) = &arg.kind
                    && let ExprKind::Lit(lit) = &arg.kind
                    && matches!(lit.kind, token::LitKind::ByteStr)
                    && let Some(hir_expr) = self.ast_to_hir.get_expr(expr_id, self.tcx)
                    && let typeck = self.tcx.typeck(hir_expr.hir_id.owner)
                    && let e_ty = typeck.expr_ty(hir_expr)
                    && let ty::TyKind::Array(elem_ty, _) = e_ty.kind()
                    && let ty::TyKind::Int(ty::IntTy::I8) | ty::TyKind::Uint(ty::UintTy::U8) =
                        elem_ty.kind()
                {
                    *expr = transmute_expr(lit.symbol.as_str(), *elem_ty);
                    return;
                }
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let mut indices: Vec<ArgIdx> = vec![];
                if let Some(if_args) = self.call_to_if_args.get(&hir_expr.hir_id) {
                    indices.extend(if_args);
                }
                if let Some(nested_args) = self.call_to_nested_args.get(&hir_expr.hir_id) {
                    indices.extend(nested_args);
                }
                if !indices.is_empty() {
                    indices.sort();
                    indices.dedup();
                    let mut new_expr = "{".to_string();
                    for i in indices {
                        let i = i.0;
                        ref_to_ptr_in_if(&mut args[i]);
                        let a = pprust::expr_to_string(&args[i]);
                        write!(new_expr, "let __arg_{i} = {a};").unwrap();
                        *args[i] = expr!("__arg_{i}");
                    }
                    new_expr.push_str(&pprust::expr_to_string(expr));
                    new_expr.push('}');
                    *expr = expr!("{new_expr}");
                }
            }
            ExprKind::MethodCall(box call) => {
                if call.seg.ident.name.as_str() != "unwrap" {
                    return;
                }
                let ExprKind::Paren(e) = &call.receiver.kind else { return };
                let ExprKind::Call(callee, e) = &e.kind else { return };
                let ExprKind::Path(_, path) = &callee.kind else { return };
                if path.segments.last().unwrap().ident.name.as_str() != "Some" {
                    return;
                }
                let [arg] = &e[..] else { return };
                let ExprKind::MethodCall(box call) = &arg.kind else { return };
                if call.seg.ident.name.as_str() != "unwrap" {
                    return;
                }
                let arg = pprust::expr_to_string(arg);
                *expr = expr!("{arg}");
            }
            ExprKind::Unary(UnOp::Deref, e) => {
                if !matches!(e.kind, ExprKind::Path(_, _)) {
                    return;
                }
                let hir_expr = some_or!(self.ast_to_hir.get_expr(e.id, self.tcx), return);
                let hir::ExprKind::Path(QPath::Resolved(_, path)) = hir_expr.kind else { panic!() };
                let Res::Local(hir_id) = path.res else { return };
                let v = some_or!(self.let_ref_exprs.get(&hir_id), return);
                *expr = v.clone();
            }
            _ => {}
        }
    }
}

fn transmute_expr(s: &str, elem_ty: ty::Ty<'_>) -> Expr {
    let is_signed = elem_ty.is_signed();
    let mut buf = Vec::with_capacity(s.len());
    rustc_literal_escaper::unescape_unicode(
        s,
        rustc_literal_escaper::Mode::ByteStr,
        &mut |_, c| buf.push(rustc_literal_escaper::byte_from_char(c.unwrap())),
    );
    let mut array = "[".to_string();
    for c in buf {
        write!(array, "b'").unwrap();
        match c {
            b'\0' => write!(array, "\\0").unwrap(),
            b'\'' => write!(array, "\\'").unwrap(),
            b'\\' => write!(array, "\\\\").unwrap(),
            b'\n' => write!(array, "\\n").unwrap(),
            b'\r' => write!(array, "\\r").unwrap(),
            b'\t' => write!(array, "\\t").unwrap(),
            _ => {
                if c.is_ascii_alphanumeric() || c.is_ascii_graphic() || c == b' ' {
                    write!(array, "{}", c as char).unwrap();
                } else if c < 0x10 {
                    write!(array, "\\x0{c:x}").unwrap();
                } else {
                    write!(array, "\\x{c:x}").unwrap();
                }
            }
        }
        if is_signed {
            write!(array, "' as i8, ").unwrap();
        } else {
            write!(array, "', ").unwrap();
        }
    }
    write!(array, "]").unwrap();
    expr!("{array}")
}

fn is_assert_stmt(stmt: &Stmt) -> bool {
    let StmtKind::Expr(e) = &stmt.kind else { return false };
    let ExprKind::If(_, t, f) = &e.kind else { return false };
    if !t.stmts.is_empty() {
        return false;
    }
    let f = some_or!(f.as_ref(), return false);
    let ExprKind::Block(b, None) = &f.kind else { return false };
    let [s] = &b.stmts[..] else { return false };
    let StmtKind::Semi(e) = &s.kind else { return false };
    let ExprKind::Call(e, _) = &e.kind else { return false };
    let ExprKind::Path(_, path) = &e.kind else { return false };
    let [segment] = &path.segments[..] else { return false };
    segment.ident.name.as_str() == "__assert_fail"
}

fn ref_to_ptr_in_if(expr: &mut Expr) {
    let ExprKind::If(_, t, Some(f)) = &mut expr.kind else { return };
    ref_to_ptr(t);
    match &mut f.kind {
        ExprKind::If(_, _, _) => ref_to_ptr_in_if(f),
        ExprKind::Block(f, _) => ref_to_ptr(f),
        _ => panic!(),
    }
}

fn ref_to_ptr(block: &mut Block) {
    if let Some(s) = block.stmts.last_mut()
        && let StmtKind::Expr(e) = &mut s.kind
        && let ExprKind::AddrOf(BorrowKind::Ref, m, _) = &e.kind
    {
        let e_str = pprust::expr_to_string(e);
        let m = if m.is_mut() { "mut" } else { "const" };
        **e = expr!("({e_str}) as *{m} _");
    }
}

fn is_libc_ty(ty: &str) -> bool {
    if ty.starts_with("c_") {
        return true;
    }
    if ty.ends_with("_t")
        && (ty.starts_with("int")
            || ty.starts_with("__int")
            || ty.starts_with("uint")
            || ty.starts_with("__uint")
            || ty.starts_with("off")
            || ty.starts_with("__off")
            || ty.starts_with("size")
            || ty.starts_with("__size")
            || ty.starts_with("isize")
            || ty.starts_with("__isize"))
    {
        return true;
    }
    false
}

#[allow(variant_size_differences)]
enum Value {
    Bool(bool),
    Int(usize),
}

fn eval_expr(expr: &Expr) -> Option<Value> {
    use Value::*;
    match &expr.kind {
        ExprKind::Binary(op, l, r) => match op.node {
            BinOpKind::And => match (eval_expr(l), eval_expr(r)) {
                (Some(Bool(true)), Some(Bool(true))) => Some(Bool(true)),
                (Some(Bool(false)), _) | (_, Some(Bool(false))) => Some(Bool(false)),
                _ => None,
            },
            BinOpKind::Or => match (eval_expr(l), eval_expr(r)) {
                (Some(Bool(true)), _) | (_, Some(Bool(true))) => Some(Bool(true)),
                (Some(Bool(false)), Some(Bool(false))) => Some(Bool(false)),
                _ => None,
            },
            BinOpKind::Eq => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l == r)),
                _ => None,
            },
            BinOpKind::Ne => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l != r)),
                _ => None,
            },
            BinOpKind::Gt => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l > r)),
                _ => None,
            },
            BinOpKind::Ge => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l >= r)),
                _ => None,
            },
            BinOpKind::Lt => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l < r)),
                _ => None,
            },
            BinOpKind::Le => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l <= r)),
                _ => None,
            },
            BinOpKind::Add => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l + r)),
                _ => None,
            },
            BinOpKind::Sub => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l - r)),
                _ => None,
            },
            BinOpKind::Mul => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l * r)),
                _ => None,
            },
            BinOpKind::Div => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l / r)),
                _ => None,
            },
            BinOpKind::Rem => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l % r)),
                _ => None,
            },
            BinOpKind::BitAnd => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l & r)),
                _ => None,
            },
            BinOpKind::BitOr => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l | r)),
                _ => None,
            },
            BinOpKind::BitXor => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l ^ r)),
                _ => None,
            },
            BinOpKind::Shl => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l << r)),
                _ => None,
            },
            BinOpKind::Shr => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l >> r)),
                _ => None,
            },
        },
        ExprKind::Cast(e, ty) => {
            let v = eval_expr(e)?;
            let TyKind::Path(_, path) = &ty.kind else {
                return None;
            };
            match path.segments.last()?.ident.name.as_str() {
                "bool" => match v {
                    Bool(b) => Some(Bool(b)),
                    Int(i) => Some(Bool(i != 0)),
                },
                "u8" | "u16" | "u32" | "u64" | "usize" | "i8" | "i16" | "i32" | "i64" | "isize"
                | "c_char" | "c_int" | "c_long" | "c_longlong" | "c_schar" | "c_short"
                | "c_uchar" | "c_uint" | "c_ulong" | "c_ulonglong" | "c_ushort" => match v {
                    Bool(b) => Some(Int(b as usize)),
                    Int(i) => Some(Int(i)),
                },
                _ => None,
            }
        }
        ExprKind::Lit(l) => {
            if matches!(l.kind, token::LitKind::Integer) {
                l.symbol.as_str().parse().ok().map(Int)
            } else {
                None
            }
        }
        ExprKind::Unary(op, v) => {
            if *op == UnOp::Not {
                if let Some(Bool(b)) = eval_expr(v) {
                    Some(Bool(!b))
                } else {
                    None
                }
            } else {
                None
            }
        }
        ExprKind::Paren(expr) => eval_expr(expr),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy)]
struct BoundOccurrence {
    var_id: HirId,
    expr_id: HirId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ArgIdx(usize);

#[allow(clippy::enum_variant_names)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PointerUse {
    LvalueDeref,
    RvalueDeref,
    NonDeref,
}

#[derive(Debug, Clone, Copy)]
struct Lhs {
    variable: HirId,
    let_stmt: HirId,
    is_mutable: bool,
}

/// ```rust,ignore
/// ...
/// let lhs = rhs;
/// rhs = rhs.offset(n);
/// *lhs = ...;
/// ```
///
/// `rhs`: HirId of the rhs variable
/// `block`: HirId of the block containing the statements
/// `stmt_idx`: index of `let lhs = rhs;` in the block
#[derive(Debug, Clone, Copy)]
struct LhsFreshLet {
    rhs: HirId,
    block: HirId,
    stmt_idx: usize,
}

#[derive(Default)]
struct HirCtx {
    call_to_args: FxHashMap<HirId, Vec<(Span, Vec<BoundOccurrence>)>>,
    call_to_nested_args: FxHashMap<HirId, Vec<ArgIdx>>,
    call_to_if_args: FxHashMap<HirId, Vec<ArgIdx>>,

    /// function param hir_id to ident symbol
    params: FxHashMap<HirId, Symbol>,
    /// let stmt rhs variable hir_id to lhs
    rhs_to_lhs: FxHashMap<HirId, Vec<Lhs>>,
    /// hir_ids of variables used, excluding let stmt rhs
    used_vars: FxHashSet<HirId>,
    /// variable hir_id to bound occurrence hir_ids
    bound_occurrences: FxHashMap<HirId, Vec<HirId>>,
    /// integer-pointer-type variable to uses
    pointer_uses: FxHashMap<HirId, Vec<PointerUse>>,
    /// integer-pointer-type fresh variable used for deref in lhs
    fresh_lets: FxHashMap<HirId, LhsFreshLet>,
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ctx: HirCtx,
}

impl HirVisitor<'_> {
    fn find_call_parent(&self, hir_id: HirId) -> HirId {
        for (hir_id, node) in self.tcx.hir_parent_iter(hir_id) {
            if matches!(
                node,
                hir::Node::Expr(hir::Expr {
                    kind: hir::ExprKind::Call(_, _),
                    ..
                })
            ) {
                return hir_id;
            }
        }
        panic!()
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_block(&mut self, block: &'tcx hir::Block<'tcx>) {
        intravisit::walk_block(self, block);

        for (i, stmts) in block.stmts.windows(3).enumerate() {
            let [stmt0, stmt1, stmt2] = stmts else { unreachable!() };

            // let lhs = rhs;
            // rhs = rhs.offset(n);
            // *lhs = ...;
            if let hir::StmtKind::Let(let0) = stmt0.kind
                && let hir::PatKind::Binding(
                    hir::BindingMode(hir::ByRef::No, hir::Mutability::Not),
                    lhs_id,
                    _,
                    _,
                ) = let0.pat.kind
                && let Some(init) = let0.init
                && let hir::ExprKind::Path(QPath::Resolved(_, path)) = init.kind
                && let Res::Local(rhs_id) = path.res
                && let hir::StmtKind::Semi(expr1) = stmt1.kind
                && let hir::ExprKind::Assign(l, r, _) = expr1.kind
                && let hir::ExprKind::Path(QPath::Resolved(_, path)) = l.kind
                && let Res::Local(id) = path.res
                && id == rhs_id
                && let hir::ExprKind::MethodCall(seg, receiver, [arg], _) = r.kind
                && seg.ident.name == sym::offset
                && let hir::ExprKind::Path(QPath::Resolved(_, path)) = receiver.kind
                && let Res::Local(id) = path.res
                && id == rhs_id
                && matches!(arg.kind, hir::ExprKind::Lit(_))
                && let hir::StmtKind::Semi(expr2) = stmt2.kind
                && let hir::ExprKind::Assign(l, _, _) | hir::ExprKind::AssignOp(_, l, _) =
                    expr2.kind
                && let hir::ExprKind::Unary(UnOp::Deref, inner) = lhs_base(l).kind
                && let hir::ExprKind::Path(QPath::Resolved(_, path)) = inner.kind
                && let Res::Local(id) = path.res
                && id == lhs_id
            {
                let fresh_let = LhsFreshLet {
                    rhs: rhs_id,
                    block: block.hir_id,
                    stmt_idx: i,
                };
                self.ctx.fresh_lets.insert(lhs_id, fresh_let);
            }
        }
    }

    fn visit_local(&mut self, let_stmt: &'tcx hir::LetStmt<'tcx>) {
        intravisit::walk_local(self, let_stmt);

        let hir::PatKind::Binding(mode, lhs_id, _, _) = let_stmt.pat.kind else { return };
        let init = some_or!(let_stmt.init, return);
        let hir::ExprKind::Path(QPath::Resolved(_, path)) = init.kind else { return };
        let Res::Local(rhs_id) = path.res else { return };
        let lhs = Lhs {
            variable: lhs_id,
            let_stmt: let_stmt.hir_id,
            is_mutable: mode.1.is_mut(),
        };
        self.ctx.rhs_to_lhs.entry(rhs_id).or_default().push(lhs);
    }

    fn visit_param(&mut self, param: &'tcx hir::Param<'tcx>) {
        intravisit::walk_param(self, param);

        let hir::PatKind::Binding(_, id, ident, _) = param.pat.kind else { return };
        self.ctx.params.insert(id, ident.name);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        match expr.kind {
            hir::ExprKind::Call(callee, args) => {
                if let hir::ExprKind::Path(QPath::Resolved(_, path)) = callee.kind
                    && let Res::Def(DefKind::Fn, def_id) = path.res
                    && utils::file::api_list::is_def_id_api(def_id, self.tcx)
                {
                    let mut if_args = vec![];
                    for (i, arg) in args.iter().enumerate() {
                        if !matches!(arg.kind, hir::ExprKind::If(_, _, _)) {
                            continue;
                        }
                        let typeck = self.tcx.typeck(expr.hir_id.owner.def_id);
                        let ty = typeck.expr_ty(arg);
                        if utils::file::contains_file_ty(ty, self.tcx) {
                            if_args.push(ArgIdx(i));
                        }
                    }
                    if !if_args.is_empty() {
                        self.ctx.call_to_if_args.insert(expr.hir_id, if_args);
                    }
                }

                let args = args.iter().map(|arg| (arg.span, vec![])).collect();
                self.ctx.call_to_args.insert(expr.hir_id, args);
            }
            hir::ExprKind::Path(QPath::Resolved(_, path)) => {
                if let Res::Local(hir_id) = path.res {
                    let typeck = self.tcx.typeck(expr.hir_id.owner.def_id);
                    let ty = typeck.expr_ty(expr);
                    if ty.is_raw_ptr() {
                        for v in self.ctx.call_to_args.values_mut() {
                            for (span, v) in v {
                                if span.contains(expr.span) {
                                    v.push(BoundOccurrence {
                                        var_id: hir_id,
                                        expr_id: expr.hir_id,
                                    });
                                }
                            }
                        }
                    }

                    self.ctx
                        .bound_occurrences
                        .entry(hir_id)
                        .or_default()
                        .push(expr.hir_id);

                    let (_, parent) = self.tcx.hir_parent_iter(expr.hir_id).next().unwrap();
                    if !matches!(parent, hir::Node::LetStmt(_)) {
                        self.ctx.used_vars.insert(hir_id);
                    }

                    if ty.is_raw_ptr() {
                        let pointer_use = if let hir::Node::Expr(parent) = parent
                            && let hir::ExprKind::Unary(hir::UnOp::Deref, _) = parent.kind
                        {
                            if is_lhs(parent, self.tcx) {
                                PointerUse::LvalueDeref
                            } else {
                                PointerUse::RvalueDeref
                            }
                        } else {
                            PointerUse::NonDeref
                        };
                        self.ctx
                            .pointer_uses
                            .entry(hir_id)
                            .or_default()
                            .push(pointer_use);
                    }
                }
            }
            _ => {}
        }

        intravisit::walk_expr(self, expr);

        if let hir::ExprKind::Call(_, args) = expr.kind {
            let arg_bound_ids = self.ctx.call_to_args.remove(&expr.hir_id).unwrap();
            let nested_args: Vec<_> = arg_bound_ids
                .iter()
                .enumerate()
                .filter_map(|(i, (_, ids))| {
                    for boi in ids {
                        if self.find_call_parent(boi.expr_id) == expr.hir_id {
                            continue;
                        }
                        for ((_, ids), arg) in arg_bound_ids.iter().zip(args) {
                            if !matches!(arg.kind, hir::ExprKind::Path(QPath::Resolved(_, _))) {
                                continue;
                            }
                            if ids.is_empty() {
                                continue;
                            }
                            let [boj] = &ids[..] else { panic!() };
                            if boi.var_id == boj.var_id {
                                return Some(ArgIdx(i));
                            }
                        }
                    }
                    None
                })
                .collect();
            if !nested_args.is_empty() {
                self.ctx
                    .call_to_nested_args
                    .insert(expr.hir_id, nested_args);
            }
        }
    }
}

fn lhs_base<'a, 'tcx>(expr: &'a hir::Expr<'tcx>) -> &'a hir::Expr<'tcx> {
    if let hir::ExprKind::Field(l, _) | hir::ExprKind::Index(l, _, _) = expr.kind {
        lhs_base(l)
    } else {
        expr
    }
}

fn is_lhs<'tcx>(mut expr: &hir::Expr<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    for (_, parent) in tcx.hir_parent_iter(expr.hir_id) {
        let hir::Node::Expr(parent) = parent else { return false };
        match parent.kind {
            hir::ExprKind::Assign(l, _, _) | hir::ExprKind::AssignOp(_, l, _)
                if l.hir_id == expr.hir_id =>
            {
                return true;
            }
            hir::ExprKind::Field(_, _) => {}
            hir::ExprKind::Index(l, _, _) if l.hir_id == expr.hir_id => {}
            _ => return false,
        }
        expr = parent;
    }
    panic!()
}

#[cfg(test)]
mod tests {
    fn run_test(code: &str, includes: &[&str], excludes: &[&str]) {
        let s = utils::compilation::run_compiler_on_str(code, super::preprocess).unwrap();
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
    fn test_assert() {
        run_test(
            r#"
use ::libc;
extern "C" {
    fn __assert_fail(
        __assertion: *const libc::c_char,
        __file: *const libc::c_char,
        __line: libc::c_uint,
        __function: *const libc::c_char,
    ) -> !;
}
pub unsafe extern "C" fn g() -> libc::c_int {
    return 1 as libc::c_int;
}
pub unsafe extern "C" fn f() {
    if g() != 0 {} else {
        __assert_fail(
            b"0 == 0\0" as *const u8 as *const libc::c_char,
            b"a.c\0" as *const u8 as *const libc::c_char,
            5 as libc::c_int as libc::c_uint,
            (*::std::mem::transmute::<&[u8; 11], &[libc::c_char; 11]>(b"void foo()\0"))
                .as_ptr(),
        );
    }
    'c_561: {
        if g() != 0 {} else {
            __assert_fail(
                b"0 == 0\0" as *const u8 as *const libc::c_char,
                b"a.c\0" as *const u8 as *const libc::c_char,
                5 as libc::c_int as libc::c_uint,
                (*::std::mem::transmute::<
                    &[u8; 11],
                    &[libc::c_char; 11],
                >(b"void foo()\0"))
                    .as_ptr(),
            );
        }
    };
}
            "#,
            &["g()", "'c_561: {}"],
            &[],
        )
    }

    #[test]
    fn test_unreachable() {
        run_test(
            r#"
use ::libc;
extern "C" {
    fn __assert_fail(
        __assertion: *const libc::c_char,
        __file: *const libc::c_char,
        __line: libc::c_uint,
        __function: *const libc::c_char,
    ) -> !;
}
pub unsafe extern "C" fn g() -> libc::c_int {
    return 1 as libc::c_int;
}
pub unsafe extern "C" fn f() {
    if g() != 0 {
        __assert_fail(
            b"0\0" as *const u8 as *const libc::c_char,
            b"a.c\0" as *const u8 as *const libc::c_char,
            15 as libc::c_int as libc::c_uint,
            (*::std::mem::transmute::<&[u8; 9], &[libc::c_char; 9]>(b"void f()\0"))
                .as_ptr(),
        );
        'c_3530: {
            __assert_fail(
                b"0\0" as *const u8 as *const libc::c_char,
                b"a.c\0" as *const u8 as *const libc::c_char,
                15 as libc::c_int as libc::c_uint,
                (*::std::mem::transmute::<&[u8; 9], &[libc::c_char; 9]>(b"void f()\0"))
                    .as_ptr(),
            );
        };
    }
}
            "#,
            &["g()", "__assert_fail"],
            &["'c3530"],
        )
    }

    #[test]
    fn test_dead() {
        run_test(
            r#"
use ::libc;
extern "C" {
    fn printf(_: *const libc::c_char, _: ...) -> libc::c_int;
}
pub unsafe extern "C" fn f() {
    if 0 as libc::c_int == 1 as libc::c_int {
        printf(b"\0" as *const u8 as *const libc::c_char);
    }
}
            "#,
            &["{}"],
            &["printf(b"],
        );
    }

    #[test]
    fn test_some_unwrap() {
        run_test(
            r#"
use ::libc;
pub unsafe extern "C" fn f() {
    let mut p: Option::<unsafe extern "C" fn() -> libc::c_int> = None;
    ::std::mem::transmute::<_, fn() -> libc::c_int>((Some(p.unwrap())).unwrap())();
}
            "#,
            &["(p.unwrap())()"],
            &["(Some(p.unwrap())).unwrap()"],
        );
    }

    #[test]
    fn test_param() {
        run_test(
            r#"
use ::libc;
pub unsafe extern "C" fn f(x: libc::c_int) {
    let mut y: libc::c_int = x;
    let mut z: libc::c_int = y + y;
}
            "#,
            &["mut x", "x + x"],
            &["let mut y: libc::c_int = x;"],
        );
    }

    #[test]
    fn test_nested_arg() {
        run_test(
            r#"
pub unsafe extern "C" fn g(mut x: *mut libc::c_int, mut y: libc::c_int) -> libc::c_int {
    return *x + y;
}
pub unsafe extern "C" fn f(mut x: libc::c_int, mut p: *mut libc::c_int) {
    g(p, g(p, 0 as libc::c_int));
}
            "#,
            &[" = g(p, 0 as libc::c_int);"],
            &["p, g(p, 0 as libc::c_int)"],
        );
    }

    #[test]
    fn test_cond_arg() {
        run_test(
            r#"
#![feature(derive_clone_copy)]
#![feature(extern_types)]
use ::libc;
extern "C" {
    pub type _IO_wide_data;
    pub type _IO_codecvt;
    pub type _IO_marker;
    fn fgetc(__stream: *mut FILE) -> libc::c_int;
}
pub type size_t = libc::c_ulong;
pub type __off_t = libc::c_long;
pub type __off64_t = libc::c_long;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct _IO_FILE {
    pub _flags: libc::c_int,
    pub _IO_read_ptr: *mut libc::c_char,
    pub _IO_read_end: *mut libc::c_char,
    pub _IO_read_base: *mut libc::c_char,
    pub _IO_write_base: *mut libc::c_char,
    pub _IO_write_ptr: *mut libc::c_char,
    pub _IO_write_end: *mut libc::c_char,
    pub _IO_buf_base: *mut libc::c_char,
    pub _IO_buf_end: *mut libc::c_char,
    pub _IO_save_base: *mut libc::c_char,
    pub _IO_backup_base: *mut libc::c_char,
    pub _IO_save_end: *mut libc::c_char,
    pub _markers: *mut _IO_marker,
    pub _chain: *mut _IO_FILE,
    pub _fileno: libc::c_int,
    pub _flags2: libc::c_int,
    pub _old_offset: __off_t,
    pub _cur_column: libc::c_ushort,
    pub _vtable_offset: libc::c_schar,
    pub _shortbuf: [libc::c_char; 1],
    pub _lock: *mut libc::c_void,
    pub _offset: __off64_t,
    pub _codecvt: *mut _IO_codecvt,
    pub _wide_data: *mut _IO_wide_data,
    pub _freeres_list: *mut _IO_FILE,
    pub _freeres_buf: *mut libc::c_void,
    pub __pad5: size_t,
    pub _mode: libc::c_int,
    pub _unused2: [libc::c_char; 20],
}
pub type _IO_lock_t = ();
pub type FILE = _IO_FILE;
pub unsafe extern "C" fn f(mut c: libc::c_int) {
    let mut p: *mut FILE = 0 as *mut FILE;
    let mut q: *mut FILE = 0 as *mut FILE;
    fgetc(if c != 0 { p } else { q });
}
            "#,
            &[" = if c != 0 { p } else { q };"],
            &["(if c != 0 { p } else { q })"],
        );
    }

    #[test]
    fn test_file_ty_alias() {
        run_test(
            r#"
#![feature(derive_clone_copy)]
#![feature(extern_types)]
use ::libc;
extern "C" {
    pub type _IO_wide_data;
    pub type _IO_codecvt;
    pub type _IO_marker;
}
pub type size_t = libc::c_ulong;
pub type __off_t = libc::c_long;
pub type __off64_t = libc::c_long;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct _IO_FILE {
    pub _flags: libc::c_int,
    pub _IO_read_ptr: *mut libc::c_char,
    pub _IO_read_end: *mut libc::c_char,
    pub _IO_read_base: *mut libc::c_char,
    pub _IO_write_base: *mut libc::c_char,
    pub _IO_write_ptr: *mut libc::c_char,
    pub _IO_write_end: *mut libc::c_char,
    pub _IO_buf_base: *mut libc::c_char,
    pub _IO_buf_end: *mut libc::c_char,
    pub _IO_save_base: *mut libc::c_char,
    pub _IO_backup_base: *mut libc::c_char,
    pub _IO_save_end: *mut libc::c_char,
    pub _markers: *mut _IO_marker,
    pub _chain: *mut _IO_FILE,
    pub _fileno: libc::c_int,
    pub _flags2: libc::c_int,
    pub _old_offset: __off_t,
    pub _cur_column: libc::c_ushort,
    pub _vtable_offset: libc::c_schar,
    pub _shortbuf: [libc::c_char; 1],
    pub _lock: *mut libc::c_void,
    pub _offset: __off64_t,
    pub _codecvt: *mut _IO_codecvt,
    pub _wide_data: *mut _IO_wide_data,
    pub _freeres_list: *mut _IO_FILE,
    pub _freeres_buf: *mut libc::c_void,
    pub __pad5: size_t,
    pub _mode: libc::c_int,
    pub _unused2: [libc::c_char; 20],
}
pub type _IO_lock_t = ();
pub type FILE = _IO_FILE;
pub type int_func = Option::<unsafe extern "C" fn(*mut FILE) -> libc::c_int>;
pub unsafe extern "C" fn g(mut x: *mut FILE) -> libc::c_int {
    return 0 as libc::c_int;
}
pub unsafe extern "C" fn f() -> libc::c_int {
    let mut h: int_func = Some(g as unsafe extern "C" fn(*mut FILE) -> libc::c_int);
    return h.unwrap()(0 as *mut FILE);
}
            "#,
            &["h: Option"],
            &["h: int_func"],
        );
    }

    #[test]
    fn test_let_ref_1() {
        run_test(
            r#"
pub unsafe extern "C" fn f(mut p: *mut libc::c_int) {
    let ref mut fresh0 = *p.offset(0 as libc::c_int as isize);
    *fresh0 += 1;
    *fresh0;
}
            "#,
            &["*p.offset(0 as libc::c_int as isize)"],
            &["fresh0"],
        );
    }

    #[test]
    fn test_let_ref_2() {
        run_test(
            r#"
pub unsafe extern "C" fn f(mut p: *mut libc::c_uint) {
    let ref mut fresh0 = *p.offset(0 as libc::c_int as isize);
    *fresh0 = (*fresh0).wrapping_add(1);
    *fresh0;
}
            "#,
            &["*p.offset(0 as libc::c_int as isize)"],
            &["fresh0"],
        );
    }

    #[test]
    fn test_transmute_1() {
        run_test(
            r#"
#![allow(mutable_transmutes)]
pub unsafe extern "C" fn f() {
    let mut buf: [libc::c_char; 9] = *::std::mem::transmute::<
        &[u8; 9],
        &mut [libc::c_char; 9],
    >(b"a\"'\n\r\t\x02\xC2\0");
}
            "#,
            &[
                "b'a'", "b'\"'", "b'\\\''", "b'\\n'", "b'\\r'", "b'\\t'", "b'\\x02'", "b'\\xc2'",
                "b'\\0'",
            ],
            &["::transmute"],
        );
    }

    #[test]
    fn test_transmute_2() {
        run_test(
            r#"
#![allow(mutable_transmutes)]
pub unsafe extern "C" fn f() {
    let mut buf: [libc::c_uchar; 9] = *::std::mem::transmute::<
        &[u8; 9],
        &mut [libc::c_uchar; 9],
    >(b"a\"'\n\r\t\x02\xC2\0");
}
            "#,
            &[
                "b'a'", "b'\"'", "b'\\\''", "b'\\n'", "b'\\r'", "b'\\t'", "b'\\x02'", "b'\\xc2'",
                "b'\\0'",
            ],
            &["::transmute"],
        );
    }

    #[test]
    fn test_transmute_3() {
        run_test(
            r#"
pub unsafe extern "C" fn f() {
    let mut buf: [libc::c_char; 9] = ::std::mem::transmute::<
        [u8; 9],
        [libc::c_char; 9],
    >(*b"a\"'\n\r\t\x02\xC2\0");
}
            "#,
            &[
                "b'a'", "b'\"'", "b'\\\''", "b'\\n'", "b'\\r'", "b'\\t'", "b'\\x02'", "b'\\xc2'",
                "b'\\0'",
            ],
            &["::transmute"],
        );
    }

    #[test]
    fn test_transmute_4() {
        run_test(
            r#"
pub unsafe extern "C" fn f() {
    let mut buf: [libc::c_uchar; 9] = ::std::mem::transmute::<
        [u8; 9],
        [libc::c_uchar; 9],
    >(*b"a\"'\n\r\t\x02\xC2\0");
}
            "#,
            &[
                "b'a'", "b'\"'", "b'\\\''", "b'\\n'", "b'\\r'", "b'\\t'", "b'\\x02'", "b'\\xc2'",
                "b'\\0'",
            ],
            &["::transmute"],
        );
    }

    #[test]
    fn test_fresh_1() {
        run_test(
            r#"
pub unsafe extern "C" fn f(mut p: *mut libc::c_int) -> libc::c_int {
    let fresh0 = p;
    p = p.offset(1);
    return *fresh0;
}
            "#,
            &["fresh0 = *p", "return fresh0"],
            &["fresh0 = p", "return *fresh0"],
        );
    }

    #[test]
    fn test_fresh_2() {
        run_test(
            r#"
pub unsafe extern "C" fn f(mut p: *mut libc::c_int) -> libc::c_int {
    let fresh0 = p;
    p = p.offset(1);
    *fresh0 = 0 as libc::c_int;
    return *fresh0;
}
            "#,
            &["fresh0 = *p", "*p = 0", "return fresh0"],
            &["fresh0 = p", "*fresh0 = 0", "return *fresh0"],
        );
    }

    #[test]
    fn test_fresh_3() {
        run_test(
            r#"
pub unsafe extern "C" fn f(
    mut p: *mut libc::c_int,
    mut q: *mut libc::c_int,
) -> libc::c_int {
    let fresh0 = q;
    q = q.offset(1);
    let fresh1 = p;
    p = p.offset(1);
    *fresh1 = *fresh0;
    return *fresh1;
}
            "#,
            &["fresh0 = *q", "fresh1 = *p", "*p = fresh0", "return fresh1"],
            &[
                "fresh0 = q",
                "fresh1 = p",
                "*fresh1 = *fresh0",
                "return *fresh1",
            ],
        );
    }

    #[test]
    fn test_fresh_4() {
        run_test(
            r#"
pub unsafe extern "C" fn f(mut p: *mut libc::c_int) -> libc::c_int {
    let fresh0 = p;
    p = p.offset(1);
    *fresh0 += 1 as libc::c_int;
    return *fresh0;
}
            "#,
            &["fresh0 = *p", "*p += 1", "return fresh0"],
            &["fresh0 = p", "*fresh0 += 1", "return *fresh0"],
        );
    }

    #[test]
    fn test_fresh_5() {
        run_test(
            r#"
pub unsafe extern "C" fn f(
    mut p: *mut libc::c_int,
    mut q: *mut libc::c_int,
) -> libc::c_int {
    let fresh0 = q;
    q = q.offset(1);
    let fresh1 = p;
    p = p.offset(1);
    *fresh1 += *fresh0;
    return *fresh1;
}
            "#,
            &[
                "fresh0 = *q",
                "fresh1 = *p",
                "*p += fresh0",
                "return fresh1",
            ],
            &[
                "fresh0 = q",
                "fresh1 = p",
                "*fresh1 += *fresh0",
                "return *fresh1",
            ],
        );
    }

    #[test]
    fn test_fresh_6() {
        run_test(
            r#"
#[no_mangle]
pub unsafe extern "C" fn f(
    mut a: *mut libc::c_int,
    mut b: *mut libc::c_int,
) -> libc::c_int {
    let mut p: *mut libc::c_int = a;
    let mut q: *mut libc::c_int = b;
    let fresh0 = q;
    q = q.offset(1);
    let fresh1 = p;
    p = p.offset(1);
    *fresh1 += *fresh0;
    return *fresh1;
}
            "#,
            &[
                "fresh0 = *b",
                "fresh1 = *a",
                "*a += fresh0",
                "return fresh1",
            ],
            &[
                "fresh0 = q",
                "fresh1 = p",
                "*fresh1 += *fresh0",
                "return *fresh1",
            ],
        );
    }

    #[test]
    fn test_fresh_7() {
        run_test(
            r#"
#![feature(derive_clone_copy)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct s {
    pub x: libc::c_int,
}
#[no_mangle]
pub unsafe extern "C" fn f(mut p: *mut s, mut q: *mut s) -> s {
    let fresh0 = q;
    q = q.offset(1);
    let fresh1 = p;
    p = p.offset(1);
    *fresh1 = *fresh0;
    return *fresh1;
}
            "#,
            &["fresh0 = *q", "fresh1 = *p", "*p = fresh0", "return fresh1"],
            &[
                "fresh0 = q",
                "fresh1 = p",
                "*fresh1 = *fresh0",
                "return *fresh1",
            ],
        );
    }

    #[test]
    fn test_fresh_8() {
        run_test(
            r#"
#![feature(derive_clone_copy)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct s {
    pub x: libc::c_int,
}
#[no_mangle]
pub unsafe extern "C" fn f(mut p: *mut s) -> libc::c_int {
    let fresh0 = p;
    p = p.offset(1);
    (*fresh0).x = 1 as libc::c_int;
    return (*fresh0).x;
}
            "#,
            &["fresh0 = *p", "(*p).x = 1", "return (fresh0).x"],
            &["fresh0 = p", "(*fresh0).x = 1", "return (*fresh0).x"],
        );
    }
}
