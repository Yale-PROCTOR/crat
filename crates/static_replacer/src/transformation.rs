use etrace::some_or;
use rustc_ast::{mut_visit::MutVisitor as _, *};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::{Symbol, sym};
use utils::{expr, item};

pub fn replace_static(tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let mut statics = FxHashSet::default();
    for def_id in tcx.hir_body_owners() {
        if matches!(tcx.def_kind(def_id), DefKind::Static { .. }) {
            statics.insert(def_id);
        }
    }

    let mut visitor = HirVisitor {
        tcx,
        statics: FxHashMap::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

    let mut immutables = FxHashSet::default();
    let mut cells = FxHashSet::default();
    let mut refcells = FxHashSet::default();
    for (def_id, exprs) in visitor.statics {
        if !statics.contains(&def_id) {
            continue;
        }
        if exprs.iter().all(|(_, mutated)| !*mutated) {
            immutables.insert(def_id);
        } else if exprs.iter().all(|(e, _)| {
            !matches!(
                e.kind,
                hir::ExprKind::AddrOf(_, _, _) | hir::ExprKind::MethodCall(_, _, _, _)
            )
        }) {
            cells.insert(def_id);
        } else {
            refcells.insert(def_id);
        }
    }

    if !cells.is_empty() {
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
    };
    visitor.visit_crate(&mut krate);

    pprust::crate_to_string_for_macros(&krate)
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: utils::ir::AstToHir,
    immutables: FxHashSet<LocalDefId>,
    cells: FxHashSet<LocalDefId>,
    refcells: FxHashSet<LocalDefId>,
    borrows: FxHashMap<Symbol, bool>,
}

impl<'tcx> AstVisitor<'tcx> {
    fn introduce_borrow(&mut self, expr: &mut Expr) {
        let mut borrows = self.borrows.drain();
        if let Some((x, is_mut)) = borrows.next() {
            let method = if is_mut {
                "with_borrow_mut"
            } else {
                "with_borrow"
            };
            let e = pprust::expr_to_string(expr);
            *expr = expr!("{x}.{method}(|{x}_ref| {e})");
        }
        assert_eq!(borrows.next(), None);
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
                let ty = pprust::ty_to_string(&static_item.ty);
                let init = pprust::expr_to_string(static_item.expr.as_ref().unwrap());
                *item = item!(
                    "thread_local! {{
                        static {name}: std::cell::Cell<{ty}> =
                            const {{ std::cell::Cell::new({init}) }};
                    }}"
                );
            } else if self.refcells.contains(def_id) {
                let name = static_item.ident.name;
                let ty = pprust::ty_to_string(&static_item.ty);
                let init = pprust::expr_to_string(static_item.expr.as_ref().unwrap());
                *item = item!(
                    "thread_local! {{
                        static {name}: std::cell::RefCell<{ty}> =
                            const {{ std::cell::RefCell::new({init}) }};
                    }}"
                );
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        let hir_expr = some_or!(self.ast_to_hir.get_expr(expr.id, self.tcx), return);
        match &mut expr.kind {
            ExprKind::Path(_, _) => {
                if let Some(def_id) = get_static_from_hir_expr(hir_expr) {
                    let x = self.tcx.item_name(def_id.to_def_id());
                    if self.cells.contains(&def_id) && !find_context(hir_expr, self.tcx).1 {
                        *expr = expr!("{x}.get()");
                    } else if self.refcells.contains(&def_id)
                        && let (ctx, is_mut) = find_context(hir_expr, self.tcx)
                        && matches!(ctx.kind, hir::ExprKind::Path(..))
                    {
                        *self.borrows.entry(x).or_default() |= is_mut;
                        *expr = expr!("*{x}_ref");
                    }
                }
            }
            ExprKind::Index(_, idx, _) => {
                let hir::ExprKind::Index(hir_base, _, _) = &hir_expr.kind else {
                    panic!("{hir_expr:?}");
                };
                if let Some(def_id) = get_static_from_hir_expr(hir_base)
                    && self.cells.contains(&def_id)
                    && !find_context(hir_expr, self.tcx).1
                {
                    let x = self.tcx.item_name(def_id.to_def_id());
                    let idx = pprust::expr_to_string(idx);
                    *expr = expr!("{x}.with(|__v| __v.as_array_of_cells()[{idx}].get())");
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
                if let Some(def_id) = get_static_from_hir_expr(hir_lhs)
                    && self.cells.contains(&def_id)
                {
                    let x = self.tcx.item_name(def_id.to_def_id());
                    let rhs = pprust::expr_to_string(rhs);
                    *expr = expr!("{x}.set({x}.get() {op} ({rhs}))");
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
            _ => {}
        }

        match self.get_hir_parent(hir_expr.hir_id) {
            hir::Node::Expr(e) => {
                if let hir::ExprKind::If(c, _, _) = e.kind
                    && self
                        .tcx
                        .hir_parent_id_iter(hir_expr.hir_id)
                        .any(|id| id == c.hir_id)
                {
                    self.introduce_borrow(expr);
                }
            }
            hir::Node::Stmt(_) | hir::Node::LetStmt(_) => {
                self.introduce_borrow(expr);
            }
            _ => {}
        }
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
                            "as_mut_ptr" => {
                                expr = parent;
                                mutated = true;
                            }
                            "as_ptr" => {
                                expr = parent;
                            }
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
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let Some(def_id) = get_static_from_hir_expr(expr) {
            let context = find_context(expr, self.tcx);
            self.statics.entry(def_id).or_default().push(context);
        }

        intravisit::walk_expr(self, expr);
    }
}

#[cfg(test)]
mod tests {
    fn run_test(code: &str, includes: &[&str], excludes: &[&str]) {
        let s = utils::compilation::run_compiler_on_str(code, super::replace_static).unwrap();
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
    fn test_immutable() {
        let code = r#"
static mut X: u32 = 0;
unsafe fn f() -> u32 { X }
"#;
        run_test(code, &["static X"], &["static mut"]);
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
}
