use rustc_ast::{mut_visit::MutVisitor as _, *};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit,
    lang_items::LangItem,
};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::{
    hir::nested_filter,
    ty::{self, Ty, TyCtxt},
};
use rustc_span::{DUMMY_SP, Symbol, sym};
use rustc_trait_selection::traits;
use serde::Deserialize;
use utils::{expr, item};

use crate::return_escape;

#[derive(Clone, Debug, Default, Deserialize)]
pub struct Config {
    pub c_exposed_statics: FxHashSet<String>,
}

pub fn replace_static(config: &Config, tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let mut statics = FxHashSet::default();
    for def_id in tcx.hir_body_owners() {
        if matches!(tcx.def_kind(def_id), DefKind::Static { .. }) {
            statics.insert(def_id);
        }
    }
    let returned_statics = return_escape::statics_returned_by_non_raw_address(tcx);

    let mut visitor = HirVisitor {
        tcx,
        statics: FxHashMap::default(),
        static_initializer_references: FxHashSet::default(),
        static_initializer_address_references: FxHashSet::default(),
        current_static_initializer: None,
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);
    let static_initializer_references = visitor.static_initializer_references;
    let static_initializer_address_references = visitor.static_initializer_address_references;

    let mut immutables = FxHashSet::default();
    let mut cells = FxHashSet::default();
    let mut refcells = FxHashSet::default();
    for (def_id, exprs) in visitor.statics {
        if !statics.contains(&def_id) {
            continue;
        }
        if returned_statics.contains(&def_id) {
            continue;
        }
        if is_c_exposed_static(config, tcx, def_id) {
            continue;
        }
        let immutable =
            exprs.iter().all(|(_, mutated)| !*mutated) && static_ty_is_sync(tcx, def_id);
        if static_initializer_references.contains(&def_id) {
            if immutable && !static_initializer_address_references.contains(&def_id) {
                immutables.insert(def_id);
            }
        } else if immutable {
            immutables.insert(def_id);
        } else if exprs
            .iter()
            .all(|(e, mutated)| cell_eligible_static_context(def_id, e, *mutated))
        {
            cells.insert(def_id);
        } else {
            refcells.insert(def_id);
        }
    }

    if !cells.is_empty() || !refcells.is_empty() {
        krate.attrs.extend([
            utils::ast::make_inner_attribute(sym::feature, sym::never_type, tcx),
            utils::ast::make_inner_attribute(
                sym::feature,
                Symbol::intern("thread_local_internals"),
                tcx,
            ),
            utils::ast::make_inner_attribute(
                sym::feature,
                Symbol::intern("as_array_of_cells"),
                tcx,
            ),
        ]);
    }

    let mut visitor = AstVisitor {
        tcx,
        ast_to_hir,
        immutables,
        cells,
        refcells,
        borrows: FxHashMap::default(),
        protected_borrows: Vec::new(),
    };
    visitor.visit_crate(&mut krate);

    pprust::crate_to_string_for_macros(&krate)
}

fn is_c_exposed_static(config: &Config, tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let name = tcx.item_name(def_id.to_def_id());
    config.c_exposed_statics.contains(name.as_str())
        || tcx
            .get_attrs(def_id.to_def_id(), sym::export_name)
            .any(|attr| {
                attr.value_str()
                    .is_some_and(|s| config.c_exposed_statics.contains(s.as_str()))
            })
}

fn static_ty_is_sync<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> bool {
    let ty = tcx.type_of(def_id).instantiate_identity();
    let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);
    let (infcx, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
    let sync_trait = tcx.require_lang_item(LangItem::Sync, DUMMY_SP);
    traits::type_known_to_meet_bound_modulo_regions(&infcx, param_env, ty, sync_trait)
}

fn initializer_use_needs_static_mut(expr: &hir::Expr<'_>, mutated: bool) -> bool {
    mutated
        || matches!(
            expr.kind,
            hir::ExprKind::AddrOf(_, _, _) | hir::ExprKind::MethodCall(_, _, _, _)
        )
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: utils::ir::AstToHir,
    immutables: FxHashSet<LocalDefId>,
    cells: FxHashSet<LocalDefId>,
    refcells: FxHashSet<LocalDefId>,
    borrows: FxHashMap<Symbol, bool>,
    protected_borrows: Vec<FxHashSet<Symbol>>,
}

impl<'tcx> AstVisitor<'tcx> {
    fn protected_borrow_names(&self, protected: &FxHashMap<Symbol, bool>) -> FxHashSet<Symbol> {
        let mut names: FxHashSet<_> = protected.keys().copied().collect();
        for protected in &self.protected_borrows {
            names.extend(protected.iter().copied());
        }
        names
    }

    fn merge_borrows(&mut self, borrows: FxHashMap<Symbol, bool>) {
        for (x, is_mut) in borrows {
            *self.borrows.entry(x).or_default() |= is_mut;
        }
    }

    fn introduce_borrow(&mut self, expr: &mut Expr, protected: &FxHashMap<Symbol, bool>) {
        let protected = self.protected_borrow_names(protected);
        let mut borrows = FxHashMap::default();
        self.borrows.retain(|x, is_mut| {
            if protected.contains(x) {
                true
            } else {
                borrows.insert(*x, *is_mut);
                false
            }
        });

        for (x, is_mut) in borrows {
            let method = if is_mut {
                "with_borrow_mut"
            } else {
                "with_borrow"
            };
            let e = pprust::expr_to_string(expr);
            *expr = expr!("{x}.{method}(|{x}_ref| {e})");
        }
    }

    fn has_unprotected_borrows(&self, protected: &FxHashMap<Symbol, bool>) -> bool {
        let protected = self.protected_borrow_names(protected);
        self.borrows.keys().any(|x| !protected.contains(x))
    }

    fn hir_expr_type_contains_ref_or_raw_ptr(&self, expr: &hir::Expr<'_>) -> bool {
        let typeck = self.tcx.typeck(expr.hir_id.owner);
        ty_contains_ref_or_raw_ptr(typeck.expr_ty(expr))
    }

    fn is_value_boundary_parent(&self, parent: &hir::Node<'_>, child: &hir::Expr<'_>) -> bool {
        match parent {
            hir::Node::Expr(parent) => match parent.kind {
                hir::ExprKind::Call(_, args) => args.iter().any(|arg| arg.hir_id == child.hir_id),
                hir::ExprKind::MethodCall(_, receiver, args, _) => {
                    receiver.hir_id != child.hir_id
                        && args.iter().any(|arg| arg.hir_id == child.hir_id)
                }
                hir::ExprKind::Array(exprs) | hir::ExprKind::Tup(exprs) => {
                    exprs.iter().any(|expr| expr.hir_id == child.hir_id)
                }
                hir::ExprKind::Repeat(expr, _) => expr.hir_id == child.hir_id,
                hir::ExprKind::Struct(_, _, hir::StructTailExpr::Base(base)) => {
                    base.hir_id == child.hir_id
                }
                hir::ExprKind::Binary(op, lhs, rhs) => {
                    matches!(op.node, hir::BinOpKind::And | hir::BinOpKind::Or)
                        && (lhs.hir_id == child.hir_id || rhs.hir_id == child.hir_id)
                }
                _ => false,
            },
            hir::Node::ExprField(_) => true,
            _ => false,
        }
    }

    fn introduce_borrow_at_value_boundary(
        &mut self,
        expr: &mut Expr,
        hir_expr: &hir::Expr<'_>,
        parent: &hir::Node<'_>,
        protected: &FxHashMap<Symbol, bool>,
    ) {
        if self.has_unprotected_borrows(protected)
            && self.is_value_boundary_parent(parent, hir_expr)
            && !self.hir_expr_type_contains_ref_or_raw_ptr(hir_expr)
        {
            self.introduce_borrow(expr, protected);
        }
    }

    fn get_hir_parent(&self, hir_id: HirId) -> hir::Node<'tcx> {
        for (_, node) in self.tcx.hir_parent_iter(hir_id) {
            if let hir::Node::Expr(e) = node
                && matches!(e.kind, hir::ExprKind::DropTemps(_))
            {
                continue;
            }
            return node;
        }
        panic!()
    }
}

impl mut_visit::MutVisitor for AstVisitor<'_> {
    fn visit_item(&mut self, item: &mut Item) {
        mut_visit::walk_item(self, item);

        if let ItemKind::Static(box static_item) = &mut item.kind
            && let Some(def_id) = self.ast_to_hir.global_map.get(&item.id)
        {
            if self.immutables.contains(def_id) {
                static_item.mutability = Mutability::Not;
            } else if self.cells.contains(def_id) {
                let name = static_item.ident.name;
                let vis = pprust::vis_to_string(&item.vis);
                let ty = pprust::ty_to_string(&static_item.ty);
                let init = pprust::expr_to_string(static_item.expr.as_ref().unwrap());
                *item = item!(
                    "thread_local! {{
                        {vis} static {name}: std::cell::Cell<{ty}> =
                            const {{ std::cell::Cell::new({init}) }};
                    }}"
                );
            } else if self.refcells.contains(def_id) {
                let name = static_item.ident.name;
                let vis = pprust::vis_to_string(&item.vis);
                let ty = pprust::ty_to_string(&static_item.ty);
                let init = pprust::expr_to_string(static_item.expr.as_ref().unwrap());
                *item = item!(
                    "thread_local! {{
                        {vis} static {name}: std::cell::RefCell<{ty}> =
                            const {{ std::cell::RefCell::new({init}) }};
                    }}"
                );
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        let outer_borrows = std::mem::take(&mut self.borrows);
        self.protected_borrows
            .push(outer_borrows.keys().copied().collect());
        mut_visit::walk_expr(self, expr);
        self.protected_borrows.pop();

        if let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx) {
            match &mut expr.kind {
                ExprKind::Path(_, _) => {
                    if let Some(def_id) = get_static_from_hir_expr(hir_expr) {
                        let x = self.tcx.item_name(def_id.to_def_id());
                        if self.cells.contains(&def_id) {
                            if !find_context(hir_expr, self.tcx).1 {
                                *expr = expr!("{x}.get()");
                            }
                        } else if self.refcells.contains(&def_id)
                            && let (ctx, is_mut) = find_context(hir_expr, self.tcx)
                            && matches!(ctx.kind, hir::ExprKind::Path(..))
                        {
                            *self.borrows.entry(x).or_default() |= is_mut;
                            *expr = expr!("*{x}_ref");
                        }
                    }
                }
                ExprKind::Index(base, idx, _) => {
                    let hir::ExprKind::Index(hir_base, _, _) = &hir_expr.kind else {
                        panic!("{hir_expr:?}");
                    };
                    if let Some(def_id) = get_static_from_hir_expr(hir_base) {
                        let x = self.tcx.item_name(def_id.to_def_id());
                        if self.cells.contains(&def_id) {
                            if !find_context(hir_expr, self.tcx).1 {
                                let idx = pprust::expr_to_string(idx);
                                *expr =
                                    expr!("{x}.with(|__v| __v.as_array_of_cells()[{idx}].get())");
                            }
                        } else if self.refcells.contains(&def_id) {
                            let is_mut = find_context(hir_expr, self.tcx).1;
                            *self.borrows.entry(x).or_default() |= is_mut;
                            **base = expr!("{x}_ref");
                        }
                    }
                }
                ExprKind::Field(e, _) => {
                    let hir::ExprKind::Field(hir_base, _) = &hir_expr.kind else {
                        panic!("{hir_expr:?}");
                    };
                    if let Some(def_id) = get_static_from_hir_expr(hir_base)
                        && self.refcells.contains(&def_id)
                    {
                        let m = find_context(hir_expr, self.tcx).1;
                        let x = self.tcx.item_name(def_id.to_def_id());
                        *self.borrows.entry(x).or_default() |= m;
                        **e = expr!("{x}_ref");
                    }
                }
                ExprKind::Assign(lhs, rhs, _) => {
                    let hir::ExprKind::Assign(hir_lhs, _, _) = &hir_expr.kind else {
                        panic!("{hir_expr:?}");
                    };
                    if let Some(def_id) = get_static_from_hir_expr(hir_lhs) {
                        let x = self.tcx.item_name(def_id.to_def_id());
                        if self.cells.contains(&def_id) {
                            let rhs = pprust::expr_to_string(rhs);
                            *expr = expr!("{x}.set({rhs})");
                        } else if self.refcells.contains(&def_id) {
                            *self.borrows.entry(x).or_default() |= true;
                            **lhs = expr!("*{x}_ref");
                        }
                    } else if let hir::ExprKind::Index(hir_base, _, _) = hir_lhs.kind
                        && let Some(def_id) = get_static_from_hir_expr(hir_base)
                        && self.cells.contains(&def_id)
                    {
                        let x = self.tcx.item_name(def_id.to_def_id());
                        let rhs = pprust::expr_to_string(rhs);
                        let ExprKind::Index(_, idx, _) = &lhs.kind else { panic!("{lhs:?}") };
                        let idx = pprust::expr_to_string(idx);
                        *expr = expr!("{x}.with(|__v| __v.as_array_of_cells()[{idx}].set({rhs}))");
                    }
                }
                ExprKind::AssignOp(op, lhs, rhs) => {
                    let hir::ExprKind::AssignOp(_, hir_lhs, _) = &hir_expr.kind else {
                        panic!("{hir_expr:?}");
                    };
                    let op = match op.node {
                        AssignOpKind::AddAssign => "+",
                        AssignOpKind::SubAssign => "-",
                        AssignOpKind::MulAssign => "*",
                        AssignOpKind::DivAssign => "/",
                        AssignOpKind::RemAssign => "%",
                        AssignOpKind::BitXorAssign => "^",
                        AssignOpKind::BitAndAssign => "&",
                        AssignOpKind::BitOrAssign => "|",
                        AssignOpKind::ShlAssign => "<<",
                        AssignOpKind::ShrAssign => ">>",
                    };
                    if let Some(def_id) = get_static_from_hir_expr(hir_lhs) {
                        let x = self.tcx.item_name(def_id.to_def_id());
                        if self.cells.contains(&def_id) {
                            let rhs = pprust::expr_to_string(rhs);
                            *expr = expr!("{x}.set({x}.get() {op} ({rhs}))");
                        } else if self.refcells.contains(&def_id) {
                            *self.borrows.entry(x).or_default() |= true;
                            **lhs = expr!("*{x}_ref");
                        }
                    } else if let hir::ExprKind::Index(hir_base, _, _) = hir_lhs.kind
                        && let Some(def_id) = get_static_from_hir_expr(hir_base)
                        && self.cells.contains(&def_id)
                    {
                        let x = self.tcx.item_name(def_id.to_def_id());
                        let rhs = pprust::expr_to_string(rhs);
                        let ExprKind::Index(_, idx, _) = &lhs.kind else { panic!("{lhs:?}") };
                        let idx = pprust::expr_to_string(idx);
                        *expr = expr!(
                            "{x}.with(|__v| {{
                                let __v = &__v.as_array_of_cells()[{idx}];
                                __v.set(__v.get() {op} ({rhs}));
                            }})"
                        );
                    }
                }
                ExprKind::AddrOf(kind, mutability, _) => {
                    let hir::ExprKind::AddrOf(_, _, hir_e) = &hir_expr.kind else {
                        panic!("{hir_expr:?}");
                    };
                    if let Some(def_id) = get_static_from_hir_expr(hir_e)
                        && self.refcells.contains(&def_id)
                    {
                        let x = self.tcx.item_name(def_id.to_def_id());
                        *self.borrows.entry(x).or_default() |= mutability.is_mut();
                        *expr = match (kind, mutability) {
                            (BorrowKind::Ref, _) => expr!("{x}_ref"),
                            (BorrowKind::Raw, Mutability::Not) => expr!("({x}_ref as *const _)"),
                            (BorrowKind::Raw, Mutability::Mut) => expr!("({x}_ref as *mut _)"),
                        };
                    }
                }
                ExprKind::MethodCall(call) => {
                    let hir::ExprKind::MethodCall(_, hir_receiver, _, _) = &hir_expr.kind else {
                        panic!("{hir_expr:?}");
                    };
                    if let Some(def_id) = get_static_from_hir_expr(hir_receiver)
                        && self.refcells.contains(&def_id)
                        && let name = call.seg.ident.name.as_str()
                        && (name == "as_mut_ptr"
                            || name == "as_ptr"
                            || name == "as_mut"
                            || name == "take"
                            || name == "copy_from_slice"
                            || name == "fill")
                    {
                        let x = self.tcx.item_name(def_id.to_def_id());
                        *self.borrows.entry(x).or_default() |= true;
                        *expr = expr!("{x}_ref.{name}()");
                    }
                }
                ExprKind::Call(box callee, args) => {
                    if let Some(box arg) = args.first()
                        && pprust::expr_to_string(arg).ends_with("_ref")
                    {
                        let callee_name = pprust::expr_to_string(callee);

                        if callee_name.ends_with("SliceCursor::new") {
                            assert!(args.len() == 1);
                            let arg = pprust::expr_to_string(&args[0]);
                            *expr = expr!(
                                "crate::slice_cursor::SliceCursor::new(unsafe {{ std::slice::from_raw_parts(({arg}).as_ptr(), ({arg}).len()) }})"
                            );
                        } else if callee_name.ends_with("SliceCursorMut::new") {
                            assert!(args.len() == 1);
                            let arg = pprust::expr_to_string(&args[0]);
                            *expr = expr!(
                                "crate::slice_cursor::SliceCursorMut::new(unsafe {{ std::slice::from_raw_parts_mut(({arg}).as_mut_ptr(), ({arg}).len()) }})"
                            );
                        } else if callee_name.ends_with("SliceCursor::with_pos") {
                            assert!(args.len() == 2);
                            let arg = pprust::expr_to_string(&args[0]);
                            let pos = pprust::expr_to_string(&args[1]);
                            *expr = expr!(
                                "crate::slice_cursor::SliceCursor::with_pos(unsafe {{ std::slice::from_raw_parts(({arg}).as_ptr(), ({arg}).len()) }}, {pos})"
                            );
                        } else if callee_name.ends_with("SliceCursorMut::with_pos") {
                            assert!(args.len() == 2);
                            let arg = pprust::expr_to_string(&args[0]);
                            let pos = pprust::expr_to_string(&args[1]);
                            *expr = expr!(
                                "crate::slice_cursor::SliceCursorMut::with_pos(unsafe {{ std::slice::from_raw_parts_mut(({arg}).as_mut_ptr(), ({arg}).len()) }}, {pos})"
                            );
                        }
                    }
                }
                _ => {}
            }

            let parent = self.get_hir_parent(hir_expr.hir_id);
            self.introduce_borrow_at_value_boundary(expr, hir_expr, &parent, &outer_borrows);

            match parent {
                hir::Node::Expr(e) => {
                    if let hir::ExprKind::If(p, _, _) | hir::ExprKind::Ret(Some(p)) = e.kind
                        && std::iter::once(hir_expr.hir_id)
                            .chain(self.tcx.hir_parent_id_iter(hir_expr.hir_id))
                            .any(|id| id == p.hir_id)
                    {
                        // Don't introduce borrows at If condition boundary when
                        // the If is embedded in a larger expression — the Stmt
                        // boundary will wrap the whole statement instead.
                        // But do NOT skip for else-if: the inner If is in the
                        // else branch and its condition is a separate scope.
                        let parent_of_if = self.get_hir_parent(e.hir_id);
                        let is_else_if = if let hir::Node::Expr(pe) = parent_of_if
                            && let hir::ExprKind::If(cond, _, _) = &pe.kind
                        {
                            e.hir_id != cond.hir_id
                                && !self
                                    .tcx
                                    .hir_parent_id_iter(e.hir_id)
                                    .any(|id| id == cond.hir_id)
                        } else {
                            false
                        };
                        let skip = matches!(e.kind, hir::ExprKind::If(..))
                            && !is_else_if
                            && !matches!(
                                parent_of_if,
                                hir::Node::Stmt(_) | hir::Node::LetStmt(_) | hir::Node::Block(_)
                            );
                        if !skip {
                            self.introduce_borrow(expr, &outer_borrows);
                        }
                    }
                }
                hir::Node::Stmt(_) | hir::Node::LetStmt(_) => {
                    self.introduce_borrow(expr, &outer_borrows);
                }
                hir::Node::Block(block) => {
                    let mut parent = self.get_hir_parent(block.hir_id);
                    if let hir::Node::Expr(e) = parent
                        && matches!(e.kind, hir::ExprKind::Block(..))
                    {
                        parent = self.get_hir_parent(e.hir_id);
                    }
                    if !matches!(parent, hir::Node::Expr(e) if matches!(e.kind, hir::ExprKind::If(..)))
                    {
                        self.introduce_borrow(expr, &outer_borrows);
                    }
                }
                _ => {}
            }
        }

        self.merge_borrows(outer_borrows);
    }
}

fn ty_contains_ref_or_raw_ptr(ty: Ty<'_>) -> bool {
    match ty.kind() {
        ty::Ref(..) | ty::RawPtr(..) => true,
        ty::Array(ty, _) | ty::Slice(ty) => ty_contains_ref_or_raw_ptr(*ty),
        ty::Tuple(tys) => tys.iter().any(ty_contains_ref_or_raw_ptr),
        ty::Adt(_, args) => args.types().any(ty_contains_ref_or_raw_ptr),
        _ => false,
    }
}

fn get_static_from_hir_expr(expr: &hir::Expr<'_>) -> Option<LocalDefId> {
    if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = &expr.kind
        && let Res::Def(DefKind::Static { .. }, def_id) = path.res
        && let Some(def_id) = def_id.as_local()
    {
        Some(def_id)
    } else {
        None
    }
}

fn cell_eligible_static_context(def_id: LocalDefId, ctx: &hir::Expr<'_>, mutated: bool) -> bool {
    if !mutated {
        return is_static_path(def_id, ctx) || is_direct_static_index(def_id, ctx);
    }

    match ctx.kind {
        hir::ExprKind::Assign(lhs, _, _) | hir::ExprKind::AssignOp(_, lhs, _) => {
            is_static_path(def_id, lhs) || is_direct_static_index(def_id, lhs)
        }
        _ => false,
    }
}

fn is_static_path(def_id: LocalDefId, expr: &hir::Expr<'_>) -> bool {
    get_static_from_hir_expr(expr) == Some(def_id)
}

fn is_direct_static_index(def_id: LocalDefId, expr: &hir::Expr<'_>) -> bool {
    matches!(
        expr.kind,
        hir::ExprKind::Index(base, _, _) if is_static_path(def_id, base)
    )
}

fn find_context<'a, 'tcx>(
    mut expr: &'a hir::Expr<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> (&'a hir::Expr<'tcx>, bool) {
    let mut mutated = false;
    for (_, node) in tcx.hir_parent_iter(expr.hir_id) {
        match node {
            hir::Node::Expr(parent) => match parent.kind {
                hir::ExprKind::MethodCall(method, receiver, _, _) => {
                    if receiver.hir_id == expr.hir_id {
                        let method = method.ident.name.as_str();
                        match method {
                            "as_ref" | "as_mut" | "as_mut_ptr" | "copy_from_slice" | "fill"
                            | "take" => {
                                expr = parent;
                                mutated = true;
                            }
                            "as_ptr" | "offset" => {
                                expr = parent;
                            }
                            "is_null" | "is_none" | "is_some" | "unwrap" | "expect" => {}
                            _ if method.starts_with("wrapping_") => {}
                            _ => panic!("{method}"),
                        }
                    }
                    break;
                }
                hir::ExprKind::DropTemps(..) => {}
                hir::ExprKind::Field(..) | hir::ExprKind::Index(..) => {
                    expr = parent;
                }
                hir::ExprKind::AddrOf(_, mutability, _) => {
                    mutated |= mutability.is_mut();
                    expr = parent;
                    break;
                }
                hir::ExprKind::Assign(lhs, _, _) | hir::ExprKind::AssignOp(_, lhs, _) => {
                    if lhs.hir_id == expr.hir_id {
                        expr = parent;
                        mutated = true;
                    }
                    break;
                }
                _ => break,
            },
            hir::Node::Item(..)
            | hir::Node::ExprField(..)
            | hir::Node::Stmt(..)
            | hir::Node::Block(..)
            | hir::Node::LetStmt(..) => break,
            _ => panic!("{node:?}"),
        }
    }
    (expr, mutated)
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    statics: FxHashMap<LocalDefId, Vec<(&'tcx hir::Expr<'tcx>, bool)>>,
    static_initializer_references: FxHashSet<LocalDefId>,
    static_initializer_address_references: FxHashSet<LocalDefId>,
    current_static_initializer: Option<LocalDefId>,
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        if let hir::ItemKind::Static(_, _, _, _) = item.kind {
            let previous = self
                .current_static_initializer
                .replace(item.owner_id.def_id);
            intravisit::walk_item(self, item);
            self.current_static_initializer = previous;
        } else {
            intravisit::walk_item(self, item);
        }
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let Some(def_id) = get_static_from_hir_expr(expr) {
            let context = find_context(expr, self.tcx);
            self.statics.entry(def_id).or_default().push(context);
            if self
                .current_static_initializer
                .is_some_and(|current| current != def_id)
            {
                self.static_initializer_references.insert(def_id);
                if initializer_use_needs_static_mut(context.0, context.1) {
                    self.static_initializer_address_references.insert(def_id);
                }
            }
        }

        intravisit::walk_expr(self, expr);
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashSet;

    fn run_test(code: &str, includes: &[&str], excludes: &[&str]) {
        run_test_with_exposed_statics(code, &[], includes, excludes);
    }

    fn run_test_with_exposed_statics(
        code: &str,
        c_exposed_statics: &[&str],
        includes: &[&str],
        excludes: &[&str],
    ) {
        let c_exposed_statics =
            FxHashSet::from_iter(c_exposed_statics.iter().map(|s| s.to_string()));
        let s = utils::compilation::run_compiler_on_str(code, |tcx| {
            let config = super::Config { c_exposed_statics };
            super::replace_static(&config, tcx)
        })
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
    fn test_exposed_cell_candidate_stays_static_mut() {
        let code = r#"
static mut X: u32 = 0;
unsafe fn f(x: u32) { X = X + x; }
"#;
        run_test_with_exposed_statics(
            code,
            &["X"],
            &["static mut X"],
            &[
                "thread_local",
                "std::cell::Cell",
                "std::cell::RefCell",
                "X.get()",
                "X.set(",
            ],
        );
    }

    #[test]
    fn test_exposed_refcell_candidate_stays_static_mut() {
        let code = r#"
struct S { x: u32 }
static mut X: S = S { x: 0 };
unsafe fn f(x: u32) { X.x = x; }
"#;
        run_test_with_exposed_statics(
            code,
            &["X"],
            &["static mut X"],
            &[
                "thread_local",
                "std::cell::Cell",
                "std::cell::RefCell",
                "with_borrow",
            ],
        );
    }

    #[test]
    fn test_immutable() {
        let code = r#"
static mut X: u32 = 0;
unsafe fn f() -> u32 { X }
"#;
        run_test(code, &["static X"], &["static mut"]);
    }

    #[test]
    fn test_non_sync_immutable_candidate_does_not_become_plain_static() {
        let code = r#"
static mut X: *mut u8 = 0 as *mut u8;
unsafe fn f() -> *mut u8 { X }
"#;
        run_test(code, &["std::cell::Cell<*mut u8>", "X.get()"], &[]);
    }

    #[test]
    fn test_static_initializer_raw_addr_dependency_keeps_target_const_addressable() {
        let code = r#"
struct Opt { value: *mut core::ffi::c_void }
impl Copy for Opt {}
impl Clone for Opt { fn clone(&self) -> Self { *self } }
static mut TARGET: i32 = 0;
static mut OPTS: [Opt; 1] = unsafe {
    [{
        let mut init = Opt { value: &raw const TARGET as *mut core::ffi::c_void };
        init
    }]
};
unsafe fn f() -> *const Opt {
    TARGET = 1;
    OPTS.as_ptr()
}
"#;
        run_test(
            code,
            &["static mut TARGET", "std::cell::RefCell<[Opt; 1]>"],
            &["TARGET.with_borrow"],
        );
    }

    #[test]
    fn test_static_initializer_method_dependency_keeps_target_const_addressable() {
        let code = r#"
struct GitStr { ptr: *mut i8, asize: usize, size: usize }
impl Copy for GitStr {}
impl Clone for GitStr { fn clone(&self) -> Self { *self } }
struct Dir { buf: GitStr }
impl Copy for Dir {}
impl Clone for Dir { fn clone(&self) -> Self { *self } }
static mut INIT: [i8; 1] = [0; 1];
static mut DIRS: [Dir; 1] = unsafe {
    [{
        let mut init = Dir {
            buf: {
                let mut init = GitStr { ptr: INIT.as_ptr().cast_mut(), asize: 0, size: 0 };
                init
            }
        };
        init
    }]
};
unsafe fn f() -> *const Dir {
    INIT[0] = 1;
    DIRS.as_ptr()
}
"#;
        run_test(
            code,
            &["static mut INIT", "std::cell::RefCell<[Dir; 1]>"],
            &["INIT.with_borrow"],
        );
    }

    #[test]
    fn test_cell_assign() {
        let code = r#"
static mut X: u32 = 0;
unsafe fn f(x: u32) { X = X + x; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::Cell", ".get()", ".set"],
            &["static mut"],
        );
    }

    #[test]
    fn test_cell_assign_op() {
        let code = r#"
static mut X: u32 = 0;
unsafe fn f(x: u32) { X += x; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::Cell", ".get()", ".set"],
            &["static mut"],
        );
    }

    #[test]
    fn test_public_cell_keeps_visibility() {
        let code = r#"
pub mod globals {
    pub static mut X: u32 = 0;
}
pub mod user {
    use crate::globals::X;
    unsafe fn f(x: u32) { X = X + x; }
}
"#;
        run_test(code, &["pub static X"], &["static mut"]);
    }

    #[test]
    fn test_cell_array_assign() {
        let code = r#"
static mut X: [u32; 1] = [0; 1];
unsafe fn f(i: usize, x: u32) { X[i] = X[i] + x; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::Cell", ".get()", ".set"],
            &["static mut"],
        );
    }

    #[test]
    fn test_cell_array_assign_op() {
        let code = r#"
static mut X: [u32; 1] = [0; 1];
unsafe fn f(i: usize, x: u32) { X[i] += x; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::Cell", ".get()", ".set"],
            &["static mut"],
        );
    }

    #[test]
    fn test_cell_struct_field_assign_uses_refcell() {
        let code = r#"
struct S { x: u32 }
static mut X: S = S { x: 0 };
unsafe fn f(x: u32) { X.x = x; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut", "std::cell::Cell<"],
        );
    }

    #[test]
    fn test_cell_struct_field_assign_op_uses_refcell() {
        let code = r#"
struct S { x: u32 }
static mut X: S = S { x: 0 };
unsafe fn f(x: u32) { X.x += x; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut", "std::cell::Cell<"],
        );
    }

    #[test]
    fn test_cell_nested_struct_field_assign_uses_refcell() {
        let code = r#"
struct Inner { value: u32 }
struct Outer { inner: Inner }
static mut X: Outer = Outer { inner: Inner { value: 0 } };
unsafe fn f(value: u32) { X.inner.value = value; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut", "std::cell::Cell<"],
        );
    }

    #[test]
    fn test_cell_tuple_field_assign_uses_refcell() {
        let code = r#"
static mut X: (u32, u32) = (0, 0);
unsafe fn f(x: u32) { X.0 = x; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut", "std::cell::Cell<"],
        );
    }

    #[test]
    fn test_cell_non_sync_struct_field_read_uses_refcell() {
        let code = r#"
struct S { ptr: *mut u8 }
static mut X: S = S { ptr: 0 as *mut u8 };
unsafe fn f() -> *mut u8 { X.ptr }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow("],
            &["static mut", "std::cell::Cell<"],
        );
    }

    #[test]
    fn test_cell_array_element_assign_stays_cell_with_projected_static() {
        let code = r#"
struct S { x: u32 }
static mut X: S = S { x: 0 };
static mut A: [u32; 2] = [0; 2];
unsafe fn f(i: usize, x: u32) {
    X.x = x;
    A[i] = x;
}
"#;
        run_test(
            code,
            &[
                "std::cell::RefCell<S>",
                "std::cell::Cell<[u32; 2]>",
                "as_array_of_cells",
            ],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_ref() {
        let code = r#"
static mut X: i32 = 0;
unsafe fn f() { g(&mut X); h(&X); }
unsafe fn g(x: &mut i32) { *x = 1; }
unsafe fn h(x: &i32) -> i32 { *x }
"#;
        run_test(
            code,
            &[
                "thread_local",
                "std::cell::RefCell",
                ".with_borrow_mut(",
                ".with_borrow(",
            ],
            &["static mut"],
        );
    }

    #[test]
    fn test_public_refcell_keeps_visibility() {
        let code = r#"
pub mod globals {
    pub static mut X: i32 = 0;
}
pub mod user {
    use crate::globals::X;
    unsafe fn f() { g(&mut X); }
    unsafe fn g(x: &mut i32) { *x = 1; }
}
"#;
        run_test(code, &["pub static X"], &["static mut"]);
    }

    #[test]
    fn test_refcell_raw_ptr() {
        let code = r#"
static mut X: i32 = 0;
unsafe fn f() { g(&raw mut X); h(&raw const X); }
unsafe fn g(x: *mut i32) { *x = 1; }
unsafe fn h(x: *const i32) -> i32 { *x }
"#;
        run_test(
            code,
            &[
                "thread_local",
                "std::cell::RefCell",
                ".with_borrow_mut(",
                ".with_borrow(",
            ],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_path() {
        let code = r#"
static mut X: i32 = 0;
unsafe fn f() { g(&mut X); if X == 1 { h(X); } }
unsafe fn g(x: &mut i32) { *x = 1; }
unsafe fn h(x: i32) -> i32 { x }
"#;
        run_test(
            code,
            &[
                "thread_local",
                "std::cell::RefCell",
                ".with_borrow_mut(",
                ".with_borrow(",
            ],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_assign() {
        let code = r#"
static mut X: i32 = 0;
unsafe fn f() { g(&mut X); X = 1; }
unsafe fn g(x: &mut i32) { *x = 1; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_assign_op() {
        let code = r#"
static mut X: i32 = 0;
unsafe fn f() { g(&mut X); X += 1; }
unsafe fn g(x: &mut i32) { *x = 1; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_array() {
        let code = r#"
static mut X: [i32; 1] = [0; 1];
unsafe fn f(i: usize) { g(X.as_mut_ptr()); let _ = X[i]; }
unsafe fn g(x: *mut i32) { *x = 1; }
"#;
        run_test(
            code,
            &[
                "thread_local",
                "std::cell::RefCell",
                ".with_borrow_mut(",
                ".with_borrow(",
            ],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_array_assign() {
        let code = r#"
static mut X: [i32; 1] = [0; 1];
unsafe fn f(i: usize) { g(X.as_mut_ptr()); X[i] = 1; }
unsafe fn g(x: *mut i32) { *x = 1; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_array_assign_op() {
        let code = r#"
static mut X: [i32; 1] = [0; 1];
unsafe fn f(i: usize) { g(X.as_mut_ptr()); X[i] += 1; }
unsafe fn g(x: *mut i32) { *x = 1; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_struct() {
        let code = r#"
struct S { x: i32, y: i32 }
static mut X: S = S { x: 0, y: 0 };
unsafe fn f() { g(&mut X); h(X.x, X.y); }
unsafe fn g(x: &mut S) { x.x = 1; x.y = 2; }
unsafe fn h(x: i32, y: i32) -> i32 { x + y }
"#;
        run_test(
            code,
            &[
                "thread_local",
                "std::cell::RefCell",
                ".with_borrow_mut(",
                ".with_borrow(",
            ],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_struct_assign() {
        let code = r#"
struct S { x: i32, y: i32 }
static mut X: S = S { x: 0, y: 0 };
unsafe fn f() { g(&mut X); X.x = 1; X.y = 2; }
unsafe fn g(x: &mut S) { x.x = 1; x.y = 2; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_return() {
        let code = r#"
static mut X: i32 = 0;
unsafe fn f() -> *mut i32 { X = 1; return &raw mut X; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut"],
        );
    }

    #[test]
    fn test_reference_return_keeps_static_mut() {
        let code = r#"
unsafe fn f<'a>(outer: &'a mut i32) -> &'a mut i32 {
    static mut X: i32 = 1;
    if *outer >= X {
        X += *outer;
        return (Some(&mut X)).unwrap();
    } else {
        *outer += X;
        return outer;
    }
}
"#;
        run_test(
            code,
            &["static mut X"],
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
        );
    }

    #[test]
    fn test_refcell_multiple() {
        let code = r#"
static mut X: i32 = 0;
static mut Y: i32 = 0;
unsafe fn f() { g(&mut X, &mut Y); }
unsafe fn g(x: &mut i32, y: &mut i32) { *x = 1; *y = 2; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_if_assign() {
        let code = r#"
static mut X: [i32; 10] = [0; 10];
unsafe fn f() { g(X.as_mut_ptr()); X[0] = if X[1] != 0 { 1 } else { 0 }; }
unsafe fn g(x: *mut i32) { *x = 1; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_if_call() {
        let code = r#"
static mut S: [i32; 10] = [0; 10];
unsafe fn f() {
    h(S.as_mut_ptr());
    g(S[0], if S[1] != 0 { 1 } else { 0 });
}
unsafe fn g(x: i32, y: i32) {}
unsafe fn h(x: *mut i32) { *x = 1; }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_option_methods() {
        let code = r#"
static mut S: Option<i32> = None;
unsafe fn f() {
    S = Some(1);
    if S.as_mut().is_some() {}
    let _x = S.take();
}
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow_mut("],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_field_offset() {
        let code = r#"
struct S { p: *const u8, i: usize }
static mut S: S = S { p: 0 as *const u8, i: 0 };
unsafe fn f() -> *const u8 {
    S.i = 1;
    S.p.offset(S.i as isize)
}
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow("],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_short_circuit_while_field_lhs_rhs_block() {
        let code = r#"
struct Registry { length: usize, items: [i32; 4] }
static mut REG: Registry = Registry { length: 4, items: [0; 4] };
unsafe fn f(mut i: usize) -> i32 {
    touch(&mut REG);
    let mut value = 0;
    while i < REG.length && { value = REG.items[i]; true } {
        i += 1;
    }
    value
}
unsafe fn touch(_r: &mut Registry) {}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "REG.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_short_circuit_loop_break_field_lhs_rhs_block() {
        let code = r#"
struct Registry { length: usize, items: [i32; 4] }
static mut REG: Registry = Registry { length: 4, items: [0; 4] };
unsafe fn f(mut i: usize) -> i32 {
    touch(&mut REG);
    let mut value = 0;
    loop {
        if !(i < REG.length && { value = REG.items[i]; true }) {
            break;
        }
        i += 1;
    }
    value
}
unsafe fn touch(_r: &mut Registry) {}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "REG.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_short_circuit_rhs_assignment_block() {
        let code = r#"
struct Registry { length: usize, items: [i32; 4] }
static mut REG: Registry = Registry { length: 4, items: [1; 4] };
unsafe fn f() -> i32 {
    touch(&mut REG);
    let mut value = 0;
    if REG.length != 0 && { value = REG.items[0]; value != 0 } {
        value += 1;
    }
    value
}
unsafe fn touch(_r: &mut Registry) {}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "REG.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_short_circuit_two_reads_same_static() {
        let code = r#"
struct Registry { length: usize, items: [i32; 4] }
static mut REG: Registry = Registry { length: 4, items: [1; 4] };
unsafe fn f() -> bool {
    touch(&mut REG);
    REG.length != 0 && { REG.items[0] != 0 }
}
unsafe fn touch(_r: &mut Registry) {}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "REG.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_short_circuit_or_lhs_field_rhs_block() {
        let code = r#"
struct Registry { length: usize, items: [i32; 4] }
static mut REG: Registry = Registry { length: 4, items: [0; 4] };
unsafe fn f() -> i32 {
    touch(&mut REG);
    let mut value = 0;
    if REG.length == 0 || { value = REG.items[0]; false } {
        value += 1;
    }
    value
}
unsafe fn touch(_r: &mut Registry) {}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "REG.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_short_circuit_nested_condition() {
        let code = r#"
struct Registry { length: usize, items: [i32; 4] }
static mut REG: Registry = Registry { length: 4, items: [1; 4] };
unsafe fn f(ready: bool, i: usize) -> i32 {
    touch(&mut REG);
    let mut value = 0;
    if ready && (i < REG.length && { value = REG.items[i]; true }) {
        value += 1;
    }
    value
}
unsafe fn touch(_r: &mut Registry) {}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "REG.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_short_circuit_static_array_index_lhs_rhs_block() {
        let code = r#"
static mut ARR: [i32; 4] = [1; 4];
unsafe fn f(i: usize) -> i32 {
    touch(ARR.as_mut_ptr());
    let mut value = 0;
    if ARR[0] != 0 && { value = ARR[i]; true } {
        value += 1;
    }
    value
}
unsafe fn touch(_p: *mut i32) {}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "ARR.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_short_circuit_call_arg_scope_is_not_widened() {
        let code = r#"
struct Registry { length: usize, items: [i32; 4] }
static mut REG: Registry = Registry { length: 4, items: [1; 4] };
unsafe fn f(i: usize) -> i32 {
    touch(&mut REG);
    choose(REG.length, if i < REG.length && { REG.items[i] != 0 } { 1 } else { 0 })
}
unsafe fn touch(_r: &mut Registry) {}
unsafe fn choose(length: usize, flag: i32) -> i32 { length as i32 + flag }
"#;
        run_test(
            code,
            &["std::cell::RefCell", "choose(REG.with_borrow("],
            &["static mut", "REG.with_borrow(|REG_ref| choose("],
        );
    }

    #[test]
    fn test_refcell_reference_call_arg_keeps_block_arg_in_scope() {
        let code = r#"
static mut S: [i32; 2] = [1; 2];
unsafe fn f() -> i32 {
    touch(S.as_mut_ptr());
    h(std::slice::from_ref(&S[0]), { S[1] })
}
unsafe fn touch(_p: *mut i32) {}
unsafe fn h(x: &[i32], y: i32) -> i32 { x[0] + y }
"#;
        run_test(
            code,
            &[
                "std::cell::RefCell",
                "S.with_borrow(|S_ref| h(std::slice::from_ref(&S_ref[0]), { S_ref[1] }))",
            ],
            &[
                "static mut",
                "h(std::slice::from_ref(&S.with_borrow(",
                "{ S.with_borrow(|S_ref| S_ref[1]) }",
            ],
        );
    }

    #[test]
    fn test_refcell_return_tuple_keeps_backing_local_read_outside_static_borrow() {
        let code = r#"
struct Registry { field: i32 }
static mut REG: Registry = Registry { field: 1 };
unsafe fn f(flag: bool) -> (usize, Option<usize>) {
    touch(&mut REG);
    let mut pos___v = 0usize;
    let pos: &mut [usize] = std::slice::from_mut(&mut pos___v);
    return (search(pos, std::slice::from_ref(&REG.field)), if flag { Some(pos___v) } else { None });
}
unsafe fn touch(_r: &mut Registry) {}
fn search(pos: &mut [usize], needle: &[i32]) -> usize {
    pos[0] += needle[0] as usize;
    pos[0]
}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "REG.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_let_tuple_keeps_backing_local_read_outside_static_borrow() {
        let code = r#"
struct Registry { field: i32 }
static mut REG: Registry = Registry { field: 1 };
unsafe fn f(flag: bool) -> (usize, Option<usize>) {
    touch(&mut REG);
    let mut pos___v = 0usize;
    let pos: &mut [usize] = std::slice::from_mut(&mut pos___v);
    let out = (search(pos, std::slice::from_ref(&REG.field)), if flag { Some(pos___v) } else { None });
    out
}
unsafe fn touch(_r: &mut Registry) {}
fn search(pos: &mut [usize], needle: &[i32]) -> usize {
    pos[0] += needle[0] as usize;
    pos[0]
}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "REG.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_later_tuple_element_keeps_backing_local_read_outside_static_borrow() {
        let code = r#"
struct Registry { field: i32 }
static mut REG: Registry = Registry { field: 1 };
unsafe fn f(flag: bool) -> (usize, usize, Option<usize>) {
    touch(&mut REG);
    let mut pos___v = 0usize;
    let pos: &mut [usize] = std::slice::from_mut(&mut pos___v);
    return (7, search(pos, std::slice::from_ref(&REG.field)), if flag { Some(pos___v) } else { None });
}
unsafe fn touch(_r: &mut Registry) {}
fn search(pos: &mut [usize], needle: &[i32]) -> usize {
    pos[0] += needle[0] as usize;
    pos[0]
}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "REG.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_array_keeps_backing_local_read_outside_static_borrow() {
        let code = r#"
struct Registry { field: i32 }
static mut REG: Registry = Registry { field: 1 };
unsafe fn f(flag: bool) -> [usize; 2] {
    touch(&mut REG);
    let mut pos___v = 0usize;
    let pos: &mut [usize] = std::slice::from_mut(&mut pos___v);
    return [search(pos, std::slice::from_ref(&REG.field)), if flag { pos___v } else { 0 }];
}
unsafe fn touch(_r: &mut Registry) {}
fn search(pos: &mut [usize], needle: &[i32]) -> usize {
    pos[0] += needle[0] as usize;
    pos[0]
}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "REG.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_nested_struct_tuple_keeps_backing_local_read_outside_static_borrow() {
        let code = r#"
struct Registry { field: i32 }
struct Out { found: usize, pos: Option<usize> }
static mut REG: Registry = Registry { field: 1 };
unsafe fn f(flag: bool) -> (Out, usize) {
    touch(&mut REG);
    let mut pos___v = 0usize;
    let pos: &mut [usize] = std::slice::from_mut(&mut pos___v);
    return (Out {
        found: search(pos, std::slice::from_ref(&REG.field)),
        pos: if flag { Some(pos___v) } else { None },
    }, 0);
}
unsafe fn touch(_r: &mut Registry) {}
fn search(pos: &mut [usize], needle: &[i32]) -> usize {
    pos[0] += needle[0] as usize;
    pos[0]
}
"#;
        run_test(
            code,
            &["std::cell::RefCell", "REG.with_borrow"],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_tuple_boundary_keeps_reference_call_args_together() {
        let code = r#"
static mut S: [i32; 2] = [1; 2];
unsafe fn f(local: i32) -> (i32, i32) {
    touch(S.as_mut_ptr());
    (h(std::slice::from_ref(&S[0]), S[1]), local)
}
unsafe fn touch(_p: *mut i32) {}
unsafe fn h(x: &[i32], y: i32) -> i32 { x[0] + y }
"#;
        run_test(
            code,
            &[
                "std::cell::RefCell",
                "S.with_borrow(|S_ref| h(std::slice::from_ref(&S_ref[0]), S_ref[1]))",
            ],
            &[
                "static mut",
                "S.with_borrow(|S_ref| (h(std::slice::from_ref(&S_ref[0]), S_ref[1]), local))",
                "h(std::slice::from_ref(&S.with_borrow(",
                "S.with_borrow(|S_ref| S_ref[1])",
            ],
        );
    }

    #[test]
    fn test_refcell_else_if() {
        let code = r#"
static mut S: [i32; 10] = [0; 10];
unsafe fn f(y: i32) -> i32 {
    if y != 0 {
        return 0
    } else if S[0] != 0 {
        return 1
    }
    return g(&mut S);
}
unsafe fn g(x: &mut [i32; 10]) -> i32 { x[0] }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", ".with_borrow("],
            &["static mut"],
        );
    }

    #[test]
    fn test_refcell_call_arg_read() {
        let code = r#"
struct Node { id: i32, active: i32 }
impl Copy for Node {}
impl Clone for Node { fn clone(&self) -> Self { *self } }
static mut S: [Node; 10] = [Node { id: 0, active: 0 }; 10];
unsafe fn f() -> *mut Node { S.as_mut_ptr() }
unsafe fn g() -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i < 10 {
        if S[i].active != 0 {
            sum += h(S[i].id);
        }
        i += 1;
    }
    sum
}
unsafe fn h(x: i32) -> i32 { x }
"#;
        run_test(
            code,
            &["thread_local", "std::cell::RefCell", "h(S.with_borrow("],
            &["static mut", "S.with_borrow(|S_ref| sum += h"],
        );
    }

    #[test]
    fn test_refcell_option_ref_call_arg() {
        let code = r#"
struct Hooks { allocate: Option<unsafe fn(usize) -> *mut u8> }
static mut global_hooks: Hooks = Hooks { allocate: None };
unsafe fn f() -> usize {
    global_hooks.allocate = None;
    new_item(Some(&global_hooks))
}
unsafe fn new_item(hooks: Option<&Hooks>) -> usize {
    if hooks.is_some() { 1 } else { 0 }
}
"#;
        run_test(
            code,
            &[
                "thread_local",
                "std::cell::RefCell",
                "global_hooks.with_borrow(|global_hooks_ref|",
                "new_item(Some(global_hooks_ref))",
            ],
            &[
                "static mut",
                "new_item(global_hooks.with_borrow(|global_hooks_ref| Some(global_hooks_ref)))",
            ],
        );
    }

    #[test]
    fn test_refcell_function_pointer_field_call() {
        let code = r#"
struct Hooks { deallocate: Option<unsafe fn(*mut u8)> }
static mut global_hooks: Hooks = Hooks { deallocate: None };
unsafe fn f(ptr: *mut u8) {
    touch(&mut global_hooks);
    global_hooks.deallocate = None;
    if global_hooks.deallocate.is_some() {
        (global_hooks.deallocate).unwrap()(ptr);
    }
}
unsafe fn touch(hooks: &mut Hooks) {}
"#;
        run_test(
            code,
            &[
                "thread_local",
                "std::cell::RefCell",
                "global_hooks.with_borrow(|global_hooks_ref|",
                "(global_hooks_ref.deallocate).unwrap()(ptr)",
            ],
            &[
                "static mut",
                "(global_hooks_ref.deallocate).unwrap()(global_hooks.with_borrow(",
            ],
        );
    }

    #[test]
    fn test_refcell_reference_arg_keeps_later_args_in_scope() {
        let code = r#"
static mut S: [i32; 2] = [0; 2];
unsafe fn f() {
    g(S.as_mut_ptr());
    h(std::slice::from_ref(&S[0]), S[1]);
}
unsafe fn g(x: *mut i32) { *x = 1; }
unsafe fn h(x: &[i32], y: i32) -> i32 { x[0] + y }
"#;
        run_test(
            code,
            &[
                "thread_local",
                "std::cell::RefCell",
                "S.with_borrow(|S_ref| h(std::slice::from_ref(&S_ref[0]), S_ref[1]))",
            ],
            &[
                "static mut",
                "h(std::slice::from_ref(&S.with_borrow(",
                "S.with_borrow(|S_ref| S_ref[1])",
            ],
        );
    }
}
