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
//! # Merge multiple pointer offsets
//!
//! C2Rust may generate code like below:
//!
//! ```rust,ignore
//! p.offset(a as isize).offset(-(1 as core::ffi::c_int as isize));
//! ```
//!
//! We merge such offsets into one offset:
//!
//! ```rust,ignore
//! p.offset((a as isize) + (-(1 as core::ffi::c_int as isize)));
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
//!
//! # Replace `as_mut_ptr` with `as_ptr`
//!
//! C2Rust may generate code like below:
//!
//! ```rust,ignore
//! strcmp(s.as_mut_ptr(), t.as_mut_ptr());
//! ```
//!
//! We replace such code with the following code:
//!
//! ```rust,ignore
//! strcmp(s.as_ptr(), t.as_ptr());
//! ```
//!
//! # Hoist bitfield setter arguments
//!
//! C2Rust may generate code like below:
//!
//! ```rust,ignore
//! (*p).set_x(((*p).x() + 1 as c_int) as c_int);
//! ```
//!
//! We hoist such arguments as follows:
//!
//! ```rust,ignore
//! { let __arg_0 = ((*p).x() + 1 as c_int) as c_int; (*p).set_x(__arg_0) }
//! ```

use std::fmt::Write as _;

use etrace::some_or;
use rustc_ast::{mut_visit::MutVisitor as _, ptr::P, visit, visit::Visitor as _, *};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_hir::{
    HirId, QPath,
    def::{DefKind, Res},
    intravisit,
};
use rustc_middle::{hir::nested_filter, ty, ty::TyCtxt};
use rustc_span::{DUMMY_SP, Span, Symbol, def_id::LocalDefId, sym};
use thin_vec::ThinVec;
use utils::{
    ast::{has_side_effects, unwrap_cast_and_paren, unwrap_paren},
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

    visitor
        .ctx
        .string_literal_statics
        .retain(|def_id| !visitor.ctx.string_literal_static_excludes.contains(def_id));
    visitor.ctx.array_string_literal_statics.retain(|def_id| {
        !visitor
            .ctx
            .array_string_literal_static_excludes
            .contains(def_id)
    });
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
        non_pointer_uses: visitor.ctx.non_pointer_uses,
        string_literal_statics: visitor.ctx.string_literal_statics,
        array_string_literal_statics: visitor.ctx.array_string_literal_statics,
    };

    visitor.visit_crate(&mut expanded_ast);
    replace_inline_extern_fns(&mut expanded_ast.items);
    pprust::crate_to_string_for_macros(&expanded_ast)
}

const INLINE_EXTERN_FUNCTIONS: &[&str] = &["atoi", "atol", "atof"];

fn replace_inline_extern_fns(items: &mut ThinVec<P<Item>>) {
    // Recurse into submodules first
    for item in items.iter_mut() {
        if let ItemKind::Mod(_, _, ModKind::Loaded(sub_items, _, _, _)) = &mut item.kind {
            replace_inline_extern_fns(sub_items);
        }
    }

    // Collect extern declarations from matching inline functions
    let mut extern_decls: Vec<String> = Vec::new();
    let mut to_remove: Vec<usize> = Vec::new();

    for (i, item) in items.iter().enumerate() {
        let ItemKind::Fn(box Fn { ident, sig, .. }) = &item.kind else { continue };
        if !INLINE_EXTERN_FUNCTIONS.contains(&ident.name.as_str()) {
            continue;
        }
        if !item.attrs.iter().any(|attr| {
            let AttrKind::Normal(attr) = &attr.kind else { return false };
            attr.item.path.segments.last().unwrap().ident.name == sym::inline
        }) {
            continue;
        }

        // Build extern declaration string
        let mut decl = format!("fn {}(", ident.name);
        for (j, param) in sig.decl.inputs.iter().enumerate() {
            if j > 0 {
                decl.push_str(", ");
            }
            // Extract param name, stripping mut
            if let PatKind::Ident(_, ident, _) = &param.pat.kind {
                write!(decl, "{}: ", ident.name).unwrap();
            } else {
                write!(decl, "_: ").unwrap();
            }
            decl.push_str(&pprust::ty_to_string(&param.ty));
        }
        decl.push(')');
        if let FnRetTy::Ty(ty) = &sig.decl.output {
            write!(decl, " -> {}", pprust::ty_to_string(ty)).unwrap();
        }
        decl.push(';');
        extern_decls.push(decl);
        to_remove.push(i);
    }

    if extern_decls.is_empty() {
        return;
    }

    // Find the first extern "C" block and append declarations
    if let Some(foreign_mod_item) = items
        .iter_mut()
        .find(|item| matches!(&item.kind, ItemKind::ForeignMod(fm) if fm.safety == Safety::Default))
    {
        let ItemKind::ForeignMod(fm) = &mut foreign_mod_item.kind else { unreachable!() };
        for decl_str in extern_decls {
            // Parse as: extern "C" { fn ...; }
            let mut parsed = utils::ast::parse_items(format!("extern \"C\" {{ {decl_str} }}"));
            let ItemKind::ForeignMod(parsed_fm) = &mut parsed[0].kind else { panic!() };
            fm.items.append(&mut parsed_fm.items);
        }
    }

    // Remove matched inline functions (in reverse order to preserve indices)
    for i in to_remove.into_iter().rev() {
        items.remove(i);
    }
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
    non_pointer_uses: FxHashSet<HirId>,
    string_literal_statics: FxHashSet<LocalDefId>,
    array_string_literal_statics: FxHashSet<LocalDefId>,
}

impl mut_visit::MutVisitor for AstVisitor<'_> {
    fn visit_item(&mut self, item: &mut Item) {
        mut_visit::walk_item(self, item);

        // Replace *const i8 string literal statics with [i8; N] arrays
        if let ItemKind::Static(box ref mut static_item) = item.kind
            && let Some(def_id) = self.ast_to_hir.global_map.get(&item.id)
            && self.string_literal_statics.contains(def_id)
            && let Some(ref init_expr) = static_item.expr
        {
            let inner = unwrap_cast_and_paren(init_expr);
            if let ExprKind::Lit(lit) = &inner.kind
                && matches!(lit.kind, token::LitKind::ByteStr)
            {
                let array_expr = transmute_expr(lit.symbol.as_str(), self.tcx.types.i8);
                let len = byte_string_len(lit.symbol.as_str());
                static_item.expr = Some(P(array_expr));
                static_item.ty = Box::new(ty!("[i8; {len}]"));
            }
        }

        // Replace [*const i8; N] array string literal statics with [&[i8]; N]
        if let ItemKind::Static(box ref mut static_item) = item.kind
            && let Some(def_id) = self.ast_to_hir.global_map.get(&item.id)
            && self.array_string_literal_statics.contains(def_id)
            && let Some(ref init_expr) = static_item.expr
            && let ExprKind::Array(ref elems) = init_expr.kind
        {
            let new_elems: Vec<_> = elems
                .iter()
                .filter_map(|elem| {
                    let inner = unwrap_cast_and_paren(elem);
                    if let ExprKind::Lit(lit) = &inner.kind
                        && matches!(lit.kind, token::LitKind::ByteStr)
                    {
                        let array_expr = transmute_expr(lit.symbol.as_str(), self.tcx.types.i8);
                        let array_str = pprust::expr_to_string(&array_expr);
                        Some(P(expr!("&{array_str}")))
                    } else {
                        None
                    }
                })
                .collect();
            if new_elems.len() == elems.len() {
                let n = new_elems.len();
                static_item.expr = Some(P(Expr {
                    id: DUMMY_NODE_ID,
                    kind: ExprKind::Array(new_elems.into_iter().collect()),
                    span: DUMMY_SP,
                    attrs: Default::default(),
                    tokens: None,
                }));
                static_item.ty = Box::new(ty!("[&[i8]; {n}]"));
            }
        }

        // remove unnecessary unsafe blocks after removing transmute
        let expr = match &mut item.kind {
            ItemKind::Static(item) => item.expr.as_mut(),
            ItemKind::Const(item) => item.expr.as_mut(),
            _ => None,
        };
        if let Some(expr) = expr
            && let ExprKind::Block(block, _) = &mut expr.kind
            && block.rules == BlockCheckMode::Unsafe(UnsafeSource::UserProvided)
            && let [stmt] = &mut block.stmts[..]
            && let StmtKind::Expr(e) = &mut stmt.kind
        {
            let is_safe = match &e.kind {
                ExprKind::Array(es) => es.iter().all(|e| is_lit(e)),
                ExprKind::Repeat(e, _) => is_lit(e),
                _ => false,
            };
            if is_safe {
                **expr = utils::ast::take_expr(e);
            }
        }
    }

    fn visit_ty(&mut self, ty: &mut Ty) {
        mut_visit::walk_ty(self, ty);

        if let Some(hir_ty) = self.ast_to_hir.get_ty(ty.id, self.tcx)
            && let hir::TyKind::Path(QPath::Resolved(_, path)) = hir_ty.kind
            && let Res::Def(DefKind::TyAlias, def_id) = path.res
        {
            let mir_ty = self.tcx.type_of(def_id).skip_binder();
            if utils::file::file_param_index(mir_ty, self.tcx).is_some() {
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
                && (matches!(e.kind, ExprKind::Unary(UnOp::Deref, _))
                    || (matches!(e.kind, ExprKind::Field(_, _))
                        && !self.non_pointer_uses.contains(&id)))
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
                {
                    if let Res::Local(hir_id) = path.res
                        && let Some(name) = self.vars_to_replace.get(&hir_id)
                    {
                        *expr = expr!("{name}");
                    } else if let Res::Def(DefKind::Static { .. }, def_id) = path.res
                        && let Some(local_def_id) = def_id.as_local()
                        && self.string_literal_statics.contains(&local_def_id)
                    {
                        let path_str = pprust::expr_to_string(expr);
                        *expr = expr!("{path_str}.as_ptr()");
                    }
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

        if let Some(replacement) = self.try_replace_offsetof(expr) {
            *expr = replacement;
        }

        mut_visit::walk_expr(self, expr);

        if let Some(replacement) = self.try_merge_pointer_offsets(expr) {
            *expr = replacement;
        }

        let expr_id = expr.id;
        match &mut expr.kind {
            ExprKind::Assign(l, _, _) | ExprKind::AssignOp(_, l, _) => {
                let mut idx_counter = 0;
                let mut let_stmts = vec![];
                hoist_self_ref_place_expr(l, &mut idx_counter, &mut let_stmts);
                if !let_stmts.is_empty() {
                    let mut new_expr = "{".to_string();
                    for s in let_stmts {
                        new_expr.push_str(&s);
                    }
                    new_expr.push_str(&pprust::expr_to_string(expr));
                    new_expr.push('}');
                    *expr = expr!("{new_expr}");
                }
            }
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
                // Replace as_mut_ptr with as_ptr for printf/fprintf arguments
                if let ExprKind::Path(_, path) = &callee.kind
                    && let [.., seg] = &path.segments[..]
                {
                    let skip = if seg.ident.name.as_str() == "printf" {
                        Some(1)
                    } else if seg.ident.name.as_str() == "fprintf" {
                        Some(2)
                    } else {
                        None
                    };
                    if let Some(skip) = skip {
                        for arg in args.iter_mut().skip(skip) {
                            if let ExprKind::MethodCall(box call) = &mut arg.kind
                                && call.seg.ident.name.as_str() == "as_mut_ptr"
                            {
                                call.seg.ident.name = sym::as_ptr;
                            }
                        }
                    }
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
            ExprKind::MethodCall(box call)
                if call.seg.ident.name.as_str().starts_with("set_") && call.args.len() == 1 =>
            {
                let arg = &call.args[0];
                if let Some(base) = receiver_base_ident(&call.receiver)
                    && expr_contains_ident(arg, base)
                {
                    let arg_str = pprust::expr_to_string(arg);
                    let recv_str = pprust::expr_to_string(&call.receiver);
                    let new_expr = format!(
                        "{{ let __arg_0 = {arg_str}; {recv_str}.{}(__arg_0) }}",
                        call.seg.ident.name
                    );
                    *expr = expr!("{new_expr}");
                }
            }
            ExprKind::MethodCall(box call) if call.seg.ident.name.as_str() == "as_mut_ptr" => {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                let ty = typeck.expr_ty_adjusted(hir_expr);
                if let ty::TyKind::RawPtr(_, ty::Mutability::Not) = ty.kind() {
                    call.seg.ident.name = sym::as_ptr;
                }
            }
            ExprKind::MethodCall(box call) if call.seg.ident.name.as_str() == "unwrap" => {
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
            ExprKind::Index(base, _, _) => {
                if let ExprKind::Path(_, _) = &base.kind
                    && let Some(hir_expr) = self.ast_to_hir.get_expr(base.id, self.tcx)
                    && let hir::ExprKind::Path(QPath::Resolved(_, path)) = hir_expr.kind
                    && let Res::Def(DefKind::Static { .. }, def_id) = path.res
                    && let Some(local_def_id) = def_id.as_local()
                    && self.array_string_literal_statics.contains(&local_def_id)
                {
                    let index_str = pprust::expr_to_string(expr);
                    *expr = expr!("{index_str}.as_ptr()");
                }
            }
            _ => {}
        }
    }
}

impl<'tcx> AstVisitor<'tcx> {
    /// Detect `&[mut] (*(0 as *mut T)).field as *mut/const _ as usize`
    /// and replace with `core::mem::offset_of!(T, field)`.
    fn try_replace_offsetof(&self, expr: &Expr) -> Option<Expr> {
        let ExprKind::Cast(inner, _) = &expr.kind else { return None };

        let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx)?;
        let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
        if typeck.expr_ty(hir_expr) != self.tcx.types.usize {
            return None;
        }

        let inner = unwrap_cast_and_paren(inner);
        let ExprKind::AddrOf(_, _, field_expr) = &inner.kind else { return None };

        let ExprKind::Field(base, field_ident) = &field_expr.kind else { return None };
        let deref_expr = unwrap_paren(base);
        let ExprKind::Unary(UnOp::Deref, null_cast) = &deref_expr.kind else { return None };

        let ExprKind::Cast(zero_lit, _) = &unwrap_paren(null_cast).kind else { return None };
        let ExprKind::Lit(lit) = &unwrap_cast_and_paren(zero_lit).kind else { return None };
        if lit.kind != token::LitKind::Integer || lit.symbol.as_str() != "0" {
            return None;
        }

        let hir_deref = self.ast_to_hir.get_expr(deref_expr.id, self.tcx)?;
        let struct_ty = typeck.expr_ty(hir_deref);
        let ty_str = mir_ty_to_string(struct_ty, self.tcx);
        let field_name = field_ident.name;

        Some(expr!("core::mem::offset_of!({ty_str}, {field_name})"))
    }

    fn try_merge_pointer_offsets(&self, expr: &Expr) -> Option<Expr> {
        let ExprKind::MethodCall(box call) = &expr.kind else { return None };
        if call.seg.ident.name != sym::offset || call.args.len() != 1 {
            return None;
        }

        let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx)?;
        let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
        if !typeck.expr_ty(hir_expr).is_raw_ptr() {
            return None;
        }

        let mut args = vec![pprust::expr_to_string(&call.args[0])];
        let mut base = &*call.receiver;
        loop {
            let ExprKind::MethodCall(box inner) = &base.kind else { break };
            if inner.seg.ident.name != sym::offset || inner.args.len() != 1 {
                break;
            }
            args.push(pprust::expr_to_string(&inner.args[0]));
            base = &inner.receiver;
        }
        if args.len() < 2 {
            return None;
        }

        args.reverse();
        let mut combined = String::new();
        for (i, arg) in args.iter().enumerate() {
            if i > 0 {
                combined.push_str(" + ");
            }
            write!(combined, "({arg})").unwrap();
        }

        let base = pprust::expr_to_string(base);
        Some(expr!("{base}.offset({combined})"))
    }
}

fn receiver_base_ident(expr: &Expr) -> Option<Symbol> {
    match &expr.kind {
        ExprKind::Path(_, path) => path.segments.last().map(|s| s.ident.name),
        ExprKind::Unary(_, e) | ExprKind::Paren(e) | ExprKind::Field(e, _) => {
            receiver_base_ident(e)
        }
        _ => None,
    }
}

fn expr_contains_ident(expr: &Expr, name: Symbol) -> bool {
    struct Finder {
        name: Symbol,
        found: bool,
    }
    impl<'ast> visit::Visitor<'ast> for Finder {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            if let ExprKind::Path(_, path) = &expr.kind
                && path.segments.iter().any(|s| s.ident.name == self.name)
            {
                self.found = true;
                return;
            }
            visit::walk_expr(self, expr);
        }
    }
    let mut finder = Finder { name, found: false };
    finder.visit_expr(expr);
    finder.found
}

fn is_hoistable_self_ref_arg(expr: &Expr) -> bool {
    if !has_side_effects(expr) {
        return true;
    }
    match &expr.kind {
        ExprKind::Paren(e) | ExprKind::Cast(e, _) | ExprKind::Unary(_, e) => {
            is_hoistable_self_ref_arg(e)
        }
        ExprKind::Binary(_, l, r) => is_hoistable_self_ref_arg(l) && is_hoistable_self_ref_arg(r),
        ExprKind::Index(base, idx, _) => {
            is_hoistable_self_ref_arg(base) && is_hoistable_self_ref_arg(idx)
        }
        ExprKind::MethodCall(box call)
            if call.seg.ident.name.as_str().starts_with("wrapping_")
                && is_hoistable_self_ref_arg(&call.receiver)
                && call.args.iter().all(|arg| is_hoistable_self_ref_arg(arg)) =>
        {
            true
        }
        _ => false,
    }
}

fn hoist_self_ref_place_expr(
    expr: &mut Expr,
    idx_counter: &mut usize,
    let_stmts: &mut Vec<String>,
) {
    match &mut expr.kind {
        ExprKind::Index(base, idx, _) => {
            hoist_self_ref_place_expr(base, idx_counter, let_stmts);

            if let Some(base_name) = receiver_base_ident(base)
                && expr_contains_ident(idx, base_name)
                && is_hoistable_self_ref_arg(idx)
            {
                let idx_str = pprust::expr_to_string(idx);
                let temp_name = format!("__idx_{idx_counter}");
                *idx_counter += 1;
                let_stmts.push(format!("let {temp_name} = {idx_str};"));
                **idx = expr!("{temp_name}");
            }
        }
        ExprKind::MethodCall(box call)
            if call.seg.ident.name.as_str() == "offset" && call.args.len() == 1 =>
        {
            hoist_self_ref_place_expr(&mut call.receiver, idx_counter, let_stmts);

            if let Some(base_name) = receiver_base_ident(&call.receiver)
                && expr_contains_ident(&call.args[0], base_name)
                && is_hoistable_self_ref_arg(&call.args[0])
            {
                let arg_str = pprust::expr_to_string(&call.args[0]);
                let temp_name = format!("__idx_{idx_counter}");
                *idx_counter += 1;
                let_stmts.push(format!("let {temp_name} = {arg_str};"));
                call.args[0] = P(expr!("{temp_name}"));
            }
        }
        ExprKind::Unary(_, e)
        | ExprKind::Paren(e)
        | ExprKind::Cast(e, _)
        | ExprKind::AddrOf(_, _, e)
        | ExprKind::Field(e, _) => hoist_self_ref_place_expr(e, idx_counter, let_stmts),
        _ => {}
    }
}

#[inline]
fn is_lit(e: &Expr) -> bool {
    matches!(unwrap_cast_and_paren(e).kind, ExprKind::Lit(_))
}

fn is_all_byte_string_array_init(expr: &hir::Expr<'_>) -> bool {
    if let hir::ExprKind::Array(elems) = &expr.kind {
        !elems.is_empty() && elems.iter().all(|e| is_byte_string_init(e))
    } else {
        false
    }
}

fn is_byte_string_init(expr: &hir::Expr<'_>) -> bool {
    match &expr.kind {
        hir::ExprKind::Cast(inner, _) => is_byte_string_init(inner),
        hir::ExprKind::Lit(lit) => matches!(lit.node, rustc_ast::LitKind::ByteStr(..)),
        _ => false,
    }
}

fn byte_string_len(s: &str) -> usize {
    let mut len = 0;
    rustc_literal_escaper::unescape_unicode(
        s,
        rustc_literal_escaper::Mode::ByteStr,
        &mut |_, _| len += 1,
    );
    len
}

fn transmute_expr(s: &str, elem_ty: ty::Ty<'_>) -> Expr {
    let is_signed = elem_ty.is_signed();
    let mut buf = Vec::with_capacity(s.len());
    rustc_literal_escaper::unescape_unicode(
        s,
        rustc_literal_escaper::Mode::ByteStr,
        &mut |_, c| buf.push(rustc_literal_escaper::byte_from_char(c.unwrap())),
    );
    let all_same = buf.first().is_some_and(|c1| buf.iter().all(|c2| c1 == c2));
    let mut array = "[".to_string();
    let len = buf.len();
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
        if all_same && len > 1 {
            if is_signed {
                write!(array, "' as i8; ").unwrap();
            } else {
                write!(array, "'; ").unwrap();
            }
            write!(array, "{len}").unwrap();
            break;
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
    /// variables used without deref
    non_pointer_uses: FxHashSet<HirId>,
    /// static def_ids whose type is *const i8 and initializer is a byte string literal
    string_literal_statics: FxHashSet<LocalDefId>,
    string_literal_static_excludes: FxHashSet<LocalDefId>,
    /// static def_ids whose type is [*const i8; N] with all byte string literal elements,
    /// where every use is an index expression
    array_string_literal_statics: FxHashSet<LocalDefId>,
    array_string_literal_static_excludes: FxHashSet<LocalDefId>,
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

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        intravisit::walk_item(self, item);

        if let hir::ItemKind::Static(_, _, _, body_id) = item.kind {
            let def_id = item.owner_id.def_id;
            let mir_ty = self.tcx.type_of(def_id).skip_binder();
            if let ty::TyKind::RawPtr(inner, ty::Mutability::Not) = mir_ty.kind()
                && (*inner == self.tcx.types.i8)
            {
                let body = self.tcx.hir_body(body_id);
                if is_byte_string_init(body.value) {
                    self.ctx.string_literal_statics.insert(def_id);
                }
            }
            if let ty::TyKind::Array(elem_ty, _) = mir_ty.kind()
                && let ty::TyKind::RawPtr(inner, ty::Mutability::Not) = elem_ty.kind()
                && (*inner == self.tcx.types.i8)
            {
                let body = self.tcx.hir_body(body_id);
                if is_all_byte_string_array_init(body.value) {
                    self.ctx.array_string_literal_statics.insert(def_id);
                }
            }
        }
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

                    if let hir::Node::Expr(parent) = parent
                        && let hir::ExprKind::Unary(hir::UnOp::Deref, _) = parent.kind
                    {
                        if ty.is_raw_ptr() {
                            let pointer_use = if is_lhs(parent, self.tcx) {
                                PointerUse::LvalueDeref
                            } else {
                                PointerUse::RvalueDeref
                            };
                            self.ctx
                                .pointer_uses
                                .entry(hir_id)
                                .or_default()
                                .push(pointer_use);
                        }
                    } else {
                        if ty.is_raw_ptr() {
                            self.ctx
                                .pointer_uses
                                .entry(hir_id)
                                .or_default()
                                .push(PointerUse::NonDeref);
                        }
                        self.ctx.non_pointer_uses.insert(hir_id);
                    }
                }

                if let Res::Def(DefKind::Static { .. }, def_id) = path.res
                    && let Some(local_def_id) = def_id.as_local()
                {
                    let (_, parent) = self.tcx.hir_parent_iter(expr.hir_id).next().unwrap();
                    if let hir::Node::Expr(
                        parent_expr @ hir::Expr {
                            kind: hir::ExprKind::Index(..),
                            ..
                        },
                    ) = parent
                    {
                        if is_lhs_or_addr_of(parent_expr, self.tcx) {
                            self.ctx
                                .array_string_literal_static_excludes
                                .insert(local_def_id);
                        }
                    } else {
                        self.ctx
                            .array_string_literal_static_excludes
                            .insert(local_def_id);
                    }
                }

                if let Res::Def(DefKind::Static { .. }, def_id) = path.res
                    && let Some(local_def_id) = def_id.as_local()
                    && is_lhs_or_addr_of(expr, self.tcx)
                {
                    self.ctx.string_literal_static_excludes.insert(local_def_id);
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

fn is_lhs_or_addr_of<'tcx>(mut expr: &hir::Expr<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    for (_, parent) in tcx.hir_parent_iter(expr.hir_id) {
        let hir::Node::Expr(parent) = parent else { return false };
        match parent.kind {
            hir::ExprKind::Assign(l, _, _) | hir::ExprKind::AssignOp(_, l, _)
                if l.hir_id == expr.hir_id =>
            {
                return true;
            }
            hir::ExprKind::AddrOf(_, _, _) => return true,
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
            &["let mut y: i32 = x;"],
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
    fn test_self_ref_index_assign() {
        run_test(
            r#"
pub unsafe extern "C" fn f(mut s_inc: [u8; 65]) {
    s_inc[s_inc[64 as usize] as usize] =
        (s_inc[s_inc[64 as usize] as usize] as core::ffi::c_int ^ 0x1f as core::ffi::c_int)
            as u8;
}
            "#,
            &["let __idx_0", "s_inc[__idx_0]"],
            &["s_inc[s_inc[64 as usize] as usize] ="],
        );
    }

    #[test]
    fn test_self_ref_wrapping_index_assign() {
        run_test(
            r#"
pub unsafe extern "C" fn f(mut s_inc: [u64; 26], mut i: usize, mut x: u64) {
    s_inc[((s_inc[25 as usize]).wrapping_add(i as u64) >> 3 as usize) as usize] = x;
}
            "#,
            &["let __idx_0", "s_inc[__idx_0] = x"],
            &["s_inc[((s_inc[25 as usize]).wrapping_add(i as u64) >> 3 as usize) as usize] = x"],
        );
    }

    #[test]
    fn test_self_ref_offset_assign() {
        run_test(
            r#"
pub unsafe extern "C" fn f(mut s_inc: *mut core::ffi::c_uchar) {
    *s_inc.offset((*s_inc.offset(64 as isize) as isize) as isize) = 0 as core::ffi::c_uchar;
}
            "#,
            &["let __idx_0", "s_inc.offset(__idx_0)"],
            &["s_inc.offset((*s_inc.offset(64 as isize) as isize) as isize)"],
        );
    }

    #[test]
    fn test_merge_offset_chain() {
        run_test(
            r#"
pub unsafe extern "C" fn f(mut p: *mut core::ffi::c_int, mut a: core::ffi::c_int) -> *mut core::ffi::c_int {
    p.offset(a as isize).offset(-(1 as core::ffi::c_int as isize))
}
            "#,
            &["p.offset((a as isize) + (-(1 as core::ffi::c_int as isize)))"],
            &["p.offset(a as isize).offset(-(1 as core::ffi::c_int as isize))"],
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

    #[test]
    fn test_as_mut_ptr() {
        run_test(
            r#"
extern "C" {
    fn strcmp(
        __s1: *const core::ffi::c_char,
        __s2: *const core::ffi::c_char,
    ) -> core::ffi::c_int;
}
unsafe fn f() {
    let mut x: [core::ffi::c_char; 1] = [0; 1];
    let mut y: [core::ffi::c_char; 1] = [0; 1];
    strcmp(x.as_mut_ptr(), y.as_mut_ptr());
}
            "#,
            &["as_ptr"],
            &["as_mut_ptr"],
        );
    }

    #[test]
    fn test_offset_of() {
        run_test(
            r#"
#[repr(C)]
struct test {
    a: i32,
    b: i32,
}
unsafe fn f(i: *mut i32) -> *mut test {
    (i as *mut i8)
        .offset(-(&mut (*(0 as *mut test)).a as *mut i32 as usize as isize))
        as *mut test
}
unsafe fn g(i: *mut i32) -> *mut test {
    (i as *mut i8)
        .offset(-(&mut (*(0 as *mut test)).b as *mut i32 as usize as isize))
        as *mut test
}
            "#,
            &["offset_of!(crate::test, a)", "offset_of!(crate::test, b)"],
            &["*(0 as"],
        )
    }

    #[test]
    fn test_printf_as_mut_ptr() {
        run_test(
            r#"
extern "C" {
    fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
}
unsafe fn f() {
    let mut buf: [core::ffi::c_char; 10] = [0; 10];
    printf(b"%s\0" as *const u8 as *const core::ffi::c_char, buf.as_mut_ptr());
}
            "#,
            &["as_ptr"],
            &["as_mut_ptr"],
        );
    }

    #[test]
    fn test_fprintf_as_mut_ptr() {
        run_test(
            r#"
#[repr(C)]
struct FILE;
extern "C" {
    fn fprintf(__stream: *mut FILE, __format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
}
unsafe fn f() {
    let mut stream: *mut FILE = 0 as *mut FILE;
    let mut buf: [core::ffi::c_char; 10] = [0; 10];
    fprintf(stream, b"%s\0" as *const u8 as *const core::ffi::c_char, buf.as_mut_ptr());
}
            "#,
            &["as_ptr"],
            &["as_mut_ptr"],
        );
    }

    #[test]
    fn test_bitfield_setter() {
        run_test(
            r#"
#[repr(C)]
pub struct s {
    pub data: [u8; 4],
}
impl s {
    pub fn x(&self) -> core::ffi::c_int { 0 }
    pub fn set_x(&mut self, _val: core::ffi::c_int) {}
}
pub unsafe extern "C" fn foo(mut p: *mut s) {
    (*p).set_x(((*p).x() + 1 as core::ffi::c_int) as core::ffi::c_int);
}
            "#,
            &["let __arg_0"],
            &[],
        )
    }

    #[test]
    fn test_inline_extern() {
        run_test(
            r#"
extern "C" {
    fn strtod(__nptr: *const core::ffi::c_char, __endptr: *mut *mut core::ffi::c_char) -> core::ffi::c_double;
    fn strtol(__nptr: *const core::ffi::c_char, __endptr: *mut *mut core::ffi::c_char, __base: core::ffi::c_int) -> core::ffi::c_long;
}
pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
#[inline]
unsafe extern "C" fn atoi(mut __nptr: *const core::ffi::c_char) -> core::ffi::c_int {
    return strtol(__nptr, NULL as *mut *mut core::ffi::c_char, 10 as core::ffi::c_int) as core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn foo(mut c: *mut core::ffi::c_char) -> core::ffi::c_int {
    return atoi(c);
}
            "#,
            &["fn atoi("],
            &["#[inline]", "return strtol("],
        )
    }

    #[test]
    fn test_string_literal_static() {
        run_test(
            r#"
extern "C" {
    fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
}
#[no_mangle]
pub static mut s: *const core::ffi::c_char = b"Hello, World!\0" as *const u8
    as *const core::ffi::c_char;
#[no_mangle]
pub unsafe extern "C" fn foo() {
    printf(b"%s\n\0" as *const u8 as *const core::ffi::c_char, s);
}
            "#,
            &["[i8;", "as_ptr()"],
            &["*const core::ffi::c_char ="],
        );
    }

    #[test]
    fn test_array_string_literal_static() {
        run_test(
            r#"
extern "C" {
    fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
}
#[no_mangle]
pub static mut s: [*const core::ffi::c_char; 2] = [
    b"Hello\0" as *const u8 as *const core::ffi::c_char,
    b"World\0" as *const u8 as *const core::ffi::c_char,
];
#[no_mangle]
pub unsafe extern "C" fn foo() {
    printf(
        b"%s %s\n\0" as *const u8 as *const core::ffi::c_char,
        s[0 as core::ffi::c_int as usize],
        s[1 as core::ffi::c_int as usize],
    );
}
            "#,
            &["[&[i8]; 2]", "as_ptr()"],
            &["[*const core::ffi::c_char; 2]"],
        );
    }

    #[test]
    fn test_string_literal_static_assign() {
        run_test(
            r#"
#[no_mangle]
pub static mut s: *const core::ffi::c_char = b"Hello, World!\0" as *const u8
    as *const core::ffi::c_char;
#[no_mangle]
pub unsafe extern "C" fn foo() {
    s = b"Hi\0" as *const u8 as *const core::ffi::c_char;
}
            "#,
            &["*const core::ffi::c_char ="],
            &["[i8;"],
        );
    }

    #[test]
    fn test_array_string_literal_static_assign() {
        run_test(
            r#"
#[no_mangle]
pub static mut s: [*const core::ffi::c_char; 2] = [
    b"Hello\0" as *const u8 as *const core::ffi::c_char,
    b"World\0" as *const u8 as *const core::ffi::c_char,
];
#[no_mangle]
pub unsafe extern "C" fn foo() {
    s[0 as core::ffi::c_int as usize] = b"Hi\0" as *const u8 as *const core::ffi::c_char;
}
            "#,
            &["[*const core::ffi::c_char; 2]"],
            &["[&[i8]; 2]"],
        );
    }

    #[test]
    fn test_string_literal_static_addr_taken() {
        run_test(
            r#"
#[no_mangle]
pub static mut s: *const core::ffi::c_char = b"Hello, World!\0" as *const u8
    as *const core::ffi::c_char;
#[no_mangle]
pub unsafe extern "C" fn foo() {
    &s;
}
            "#,
            &["*const core::ffi::c_char ="],
            &["[i8;"],
        );
    }

    #[test]
    fn test_array_string_literal_static_addr_taken() {
        run_test(
            r#"
#[no_mangle]
pub static mut s: [*const core::ffi::c_char; 2] = [
    b"Hello\0" as *const u8 as *const core::ffi::c_char,
    b"World\0" as *const u8 as *const core::ffi::c_char,
];
#[no_mangle]
pub unsafe extern "C" fn foo() {
    &s[0 as core::ffi::c_int as usize];
}
            "#,
            &["[*const core::ffi::c_char; 2]"],
            &["[&[i8]; 2]"],
        );
    }
}
