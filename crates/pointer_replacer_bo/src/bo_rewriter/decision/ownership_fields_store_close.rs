//! R622-3 (Extension X §5.2): the depth witness for a store into an owning
//! field. W6F-3's safe-base arm asks, per store, whether the payload the
//! assignment drops is recursive and, when it is, whether the old value is
//! provably `None` there; `lifecycle::store_close` decides.
use std::collections::BTreeMap;

use rustc_hir::{
    Block, Expr, ExprKind, HirId, LetStmt, Node, QPath, Stmt, StmtKind,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TypeckResults};
use rustc_span::{Span, def_id::LocalDefId};

use crate::bo_rewriter::ownership_fields::{
    OwnerId,
    lifecycle::{self, NoneWitness, StoreClose},
};

/// `owning_fields`: every owning field as `(struct, field index)`; `moved`:
/// the spans of the field expressions the caller renders as a move out
/// (`take()`). A store this cannot read closes as a leak.
///
/// The witnesses read the input program's statements; each holds on every
/// execution of the emitted program free of aliasing UB, because the only
/// other path to the base's pointee would be derived from the base (the
/// owner's `Box` / `&mut` form asserts that) and so would name it.
pub(crate) fn store_close(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    assign_span: Span,
    owning_fields: &[(LocalDefId, usize)],
    moved: &[Span],
) -> StoreClose {
    let typeck = tcx.typeck(owner);
    let mut find = FindAssign(assign_span, None);
    find.visit_body(tcx.hir_body_owned_by(owner));
    let Some(assign) = find.1 else { return StoreClose::Leak };
    let ExprKind::Assign(place, value, _) = assign.kind else { return StoreClose::Leak };
    let Some((base, stored)) = field_place(typeck, place) else { return StoreClose::Leak };
    let pointee = |field: (LocalDefId, usize)| -> Option<LocalDefId> {
        let def = tcx.adt_def(field.0).all_fields().nth(field.1)?;
        let rustc_middle::ty::TyKind::RawPtr(inner, _) = tcx.type_of(def.did).skip_binder().kind()
        else {
            return None;
        };
        inner.ty_adt_def()?.did().as_local()
    };
    let id = |did: LocalDefId| OwnerId(did.local_def_index.as_u32());
    let Some(payload) = pointee(stored) else { return StoreClose::Drop };
    let mut owning = BTreeMap::<OwnerId, Vec<OwnerId>>::new();
    for field in owning_fields {
        if let Some(target) = pointee(*field) {
            owning.entry(id(field.0)).or_default().push(id(target));
        }
    }
    let is_moved = |expr: &Expr<'_>| {
        let expr = peel(expr);
        moved.contains(&expr.span) && field_place(typeck, expr) == Some((base, stored))
    };
    let witness = taken_in_value(value, base, &is_moved)
        .or_else(|| block_witness(tcx, typeck, assign, value, base, stored, &is_moved));
    lifecycle::store_close(id(payload), &owning, witness)
}

struct FindAssign<'tcx>(Span, Option<&'tcx Expr<'tcx>>);
impl<'tcx> Visitor<'tcx> for FindAssign<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if expr.span == self.0 && matches!(expr.kind, ExprKind::Assign(..)) {
            self.1 = Some(expr);
        }
        intravisit::walk_expr(self, expr);
    }
}

fn peel<'a, 'tcx>(mut expr: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) = expr.kind {
        expr = inner;
    }
    expr
}

fn local(expr: &Expr<'_>) -> Option<HirId> {
    match peel(expr).kind {
        ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::Local(binding) => Some(binding),
            _ => None,
        },
        _ => None,
    }
}

/// `(*b).f` — the base local and the field.
fn field_place(
    typeck: &TypeckResults<'_>,
    expr: &Expr<'_>,
) -> Option<(HirId, (LocalDefId, usize))> {
    let ExprKind::Field(base, _) = expr.kind else { return None };
    let ExprKind::Unary(rustc_hir::UnOp::Deref, pointer) = base.kind else { return None };
    let index = typeck.opt_field_index(expr.hir_id)?;
    let adt = typeck.expr_ty(base).ty_adt_def()?.did().as_local()?;
    Some((local(pointer)?, (adt, index.as_usize())))
}

fn mentions(expr: &Expr<'_>, binding: HirId) -> usize {
    struct Count(HirId, usize);
    impl<'tcx> Visitor<'tcx> for Count {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if local(expr) == Some(self.0) && matches!(expr.kind, ExprKind::Path(..)) {
                self.1 += 1;
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut count = Count(binding, 0);
    count.visit_expr(expr);
    count.1
}

fn statement_mentions(statement: &Stmt<'_>, binding: HirId) -> usize {
    match statement.kind {
        StmtKind::Let(LetStmt { init, els, .. }) => {
            init.map_or(0, |e| mentions(e, binding))
                + els.map_or(0, |b| {
                    b.stmts
                        .iter()
                        .map(|s| statement_mentions(s, binding))
                        .sum::<usize>()
                        + b.expr.map_or(0, |e| mentions(e, binding))
                })
        }
        StmtKind::Expr(e) | StmtKind::Semi(e) => mentions(e, binding),
        StmtKind::Item(_) => 0,
    }
}

/// `p.f = callee(.., p.f /* moved */, ..)`: the arguments are evaluated before
/// the store, so the take has run; nothing else in the value names the base.
fn taken_in_value(
    value: &Expr<'_>,
    base: HirId,
    is_moved: &dyn Fn(&Expr<'_>) -> bool,
) -> Option<NoneWitness> {
    let ExprKind::Call(_, arguments) = peel(value).kind else { return None };
    (arguments.iter().any(|a| is_moved(a)) && mentions(value, base) == 1)
        .then_some(NoneWitness::TakenInValue)
}

/// The store is a statement of a block; scanning back from it, the first
/// statement that names the base decides.
fn block_witness<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    assign: &'tcx Expr<'tcx>,
    value: &Expr<'_>,
    base: HirId,
    stored: (LocalDefId, usize),
    is_moved: &dyn Fn(&Expr<'_>) -> bool,
) -> Option<NoneWitness> {
    if mentions(value, base) != 0 {
        return None;
    }
    let Node::Stmt(statement) = tcx.parent_hir_node(assign.hir_id) else { return None };
    let Node::Block(Block { stmts, .. }) = tcx.parent_hir_node(statement.hir_id) else {
        return None;
    };
    let at = stmts.iter().position(|s| s.hir_id == statement.hir_id)?;
    let mut fresh_only = true;
    for earlier in stmts[..at].iter().rev() {
        let defines =
            matches!(earlier.kind, StmtKind::Let(LetStmt { pat, .. }) if pat.hir_id == base);
        if !defines && statement_mentions(earlier, base) == 0 {
            continue;
        }
        match earlier.kind {
            // TakenBefore: the nearest mention moves the place out whole —
            // `let x = p.f;` or `x = p.f;`.
            StmtKind::Let(LetStmt {
                init: Some(init),
                els: None,
                ..
            }) if fresh_only && is_moved(init) && mentions(init, base) == 1 => {
                return Some(NoneWitness::TakenBefore);
            }
            StmtKind::Semi(e) | StmtKind::Expr(e)
                if fresh_only
                    && matches!(e.kind, ExprKind::Assign(lhs, rhs, _)
                        if is_moved(rhs) && mentions(lhs, base) == 0 && mentions(rhs, base) == 1) =>
            {
                return Some(NoneWitness::TakenBefore);
            }
            // FreshLiteral: the base's own definition by a libc allocation,
            // with only stores to its OTHER fields between.
            StmtKind::Let(LetStmt {
                pat,
                init: Some(init),
                els: None,
                ..
            }) if pat.hir_id == base && allocation(tcx, init) => {
                return Some(NoneWitness::FreshLiteral);
            }
            StmtKind::Semi(e) | StmtKind::Expr(e)
                if matches!(e.kind, ExprKind::Assign(lhs, rhs, _)
                    if field_place(typeck, lhs).is_some_and(|(b, f)| b == base && f != stored)
                        && mentions(rhs, base) == 0) =>
            {
                fresh_only = false;
            }
            _ => return None,
        }
    }
    None
}

/// `malloc(..)` / `calloc(..)` from libc, through pointer casts: the base's
/// owner renders it as a literal whose owning fields are `None`.
fn allocation(tcx: TyCtxt<'_>, init: &Expr<'_>) -> bool {
    let ExprKind::Call(callee, _) = peel(init).kind else { return false };
    let ExprKind::Path(QPath::Resolved(None, path)) = callee.kind else { return false };
    let Res::Def(_, did) = path.res else { return false };
    did.as_local()
        .is_some_and(|local| matches!(tcx.hir_node_by_def_id(local), Node::ForeignItem(_)))
        && matches!(
            tcx.codegen_fn_attrs(did)
                .link_name
                .unwrap_or_else(|| tcx.item_name(did))
                .as_str(),
            "malloc" | "calloc"
        )
}

#[cfg(test)]
mod tests {
    use rustc_hir::{
        Expr, ExprKind, LetStmt,
        def::DefKind,
        intravisit::{self, Visitor},
    };
    use rustc_middle::ty::TyCtxt;
    use rustc_span::{Span, def_id::LocalDefId};

    use crate::bo_rewriter::ownership_fields::lifecycle::{
        NoneWitness::{FreshLiteral, TakenBefore, TakenInValue},
        StoreClose::{self, Drop, Leak, Witnessed},
    };

    /// Every store into an owning field of `function`, classified. `owning`
    /// names the owning fields `(struct, field)`. The moved set stands in for
    /// W6F-3's move edits: an owning field read as a `let` initializer, as the
    /// value of an assignment to a local, or as an argument of a callee in
    /// `movers` (the callees whose formal is `Owning`) is moved out.
    fn closes(
        source: &str,
        function: &str,
        owning: &[(&str, &str)],
        movers: &[&str],
    ) -> Vec<(String, StoreClose)> {
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let mut fields = Vec::new();
            for did in tcx.hir_crate_items(()).definitions() {
                if tcx.def_kind(did) != DefKind::Struct {
                    continue;
                }
                let name = tcx.item_name(did.to_def_id());
                for (index, field) in tcx.adt_def(did).all_fields().enumerate() {
                    if owning.contains(&(name.as_str(), field.name.as_str())) {
                        fields.push((did, index));
                    }
                }
            }
            let owner = tcx
                .hir_body_owners()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == function)
                .unwrap_or_else(|| panic!("no function {function}"));
            let mut walk = Walk {
                tcx,
                owner,
                fields: &fields,
                movers,
                stores: Vec::new(),
                moved: Vec::new(),
            };
            walk.visit_body(tcx.hir_body_owned_by(owner));
            walk.stores
                .iter()
                .map(|span| {
                    let text = tcx.sess.source_map().span_to_snippet(*span).unwrap();
                    let close = super::store_close(tcx, owner, *span, &fields, &walk.moved);
                    (text.split_whitespace().collect::<Vec<_>>().join(" "), close)
                })
                .collect()
        })
        .unwrap()
    }

    struct Walk<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        fields: &'a [(LocalDefId, usize)],
        movers: &'a [&'a str],
        stores: Vec<Span>,
        moved: Vec<Span>,
    }

    impl<'tcx> Walk<'_, 'tcx> {
        fn owning(&self, expr: &Expr<'_>) -> bool {
            let ExprKind::Field(base, _) = expr.kind else { return false };
            let typeck = self.tcx.typeck(self.owner);
            let Some(index) = typeck.opt_field_index(expr.hir_id) else { return false };
            let Some(adt) = typeck.expr_ty(base).ty_adt_def() else { return false };
            adt.did()
                .as_local()
                .is_some_and(|did| self.fields.contains(&(did, index.as_usize())))
        }
    }

    impl<'tcx> Visitor<'tcx> for Walk<'_, 'tcx> {
        fn visit_local(&mut self, local: &'tcx LetStmt<'tcx>) {
            if let Some(init) = local.init
                && self.owning(init)
            {
                self.moved.push(init.span);
            }
            intravisit::walk_local(self, local);
        }

        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            match expr.kind {
                ExprKind::Assign(lhs, rhs, _) => {
                    if self.owning(lhs) {
                        self.stores.push(expr.span);
                    } else if self.owning(rhs) {
                        self.moved.push(rhs.span);
                    }
                }
                ExprKind::Call(callee, args) => {
                    let mover = matches!(callee.kind,
                        ExprKind::Path(rustc_hir::QPath::Resolved(None, path))
                            if path
                                .segments
                                .last()
                                .is_some_and(|s| self.movers.contains(&s.ident.name.as_str())));
                    for arg in args.iter().filter(|_| mover) {
                        if self.owning(arg) {
                            self.moved.push(arg.span);
                        }
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }

    const AVL: &str = include_str!("../wave6f_fixture_avl.rs");
    const BST: &str = include_str!("../wave6f_fixture_bst.rs");
    const AVL_OWNING: &[(&str, &str)] = &[("Node", "left"), ("Node", "right")];
    const AVL_MOVERS: &[&str] = &["insert", "leftRotate", "rightRotate"];

    fn avl(function: &str) -> Vec<(String, StoreClose)> {
        closes(
            &format!("{AVL}\n{AVL_VARIANTS}"),
            function,
            AVL_OWNING,
            AVL_MOVERS,
        )
    }

    /// Each one construct away from avl's own shapes.
    const AVL_VARIANTS: &str = "
pub unsafe extern \"C\" fn graft(mut n: *mut Node, mut key: i32) {
    (*n).left = newNode(key);
}
pub unsafe extern \"C\" fn touch(mut n: *mut Node) {}
pub unsafe extern \"C\" fn pass(mut c: *mut Node, mut n: *mut Node) -> *mut Node {
    return c;
}
pub unsafe extern \"C\" fn taken_then_named(mut y: *mut Node) -> *mut Node {
    let mut x = (*y).left;
    touch(y);
    (*y).left = 0 as *mut Node;
    return x;
}
pub unsafe extern \"C\" fn viewed_not_taken(mut y: *mut Node) {
    let mut h = height((*y).left);
    (*y).left = 0 as *mut Node;
}
pub unsafe extern \"C\" fn value_names_base(mut n: *mut Node) {
    (*n).left = pass((*n).left, n);
}
pub unsafe extern \"C\" fn passed_not_moved(mut n: *mut Node) {
    (*n).left = pass((*n).left, 0 as *mut Node);
}
pub unsafe extern \"C\" fn fresh_escaped(mut key: i32) -> *mut Node {
    let mut n = malloc(::std::mem::size_of::<Node>() as u64) as *mut Node;
    touch(n);
    (*n).left = 0 as *mut Node;
    return n;
}
pub unsafe extern \"C\" fn fresh_written_twice(mut key: i32) -> *mut Node {
    let mut n = malloc(::std::mem::size_of::<Node>() as u64) as *mut Node;
    (*n).left = newNode(key);
    (*n).left = 0 as *mut Node;
    return n;
}
";

    /// **R622-3 — the live overwrite leaks.** `(*n).left = newNode(key)` with
    /// no earlier take overwrites a subtree C leaks; a plain assignment drops
    /// it recursively. Today every store is the plain drop.
    #[test]
    fn r622_a_live_overwrite_of_a_recursive_field_leaks() {
        assert_eq!(
            avl("graft"),
            [("(*n).left = newNode(key)".to_owned(), Leak)]
        );
        let leaked = Leak.render("(*n).left", "Some(newNode(key))").unwrap();
        assert_eq!(
            leaked,
            "::std::mem::forget(::std::mem::replace(&mut (*n).left, Some(newNode(key))))"
        );
        assert_eq!(Leak.receipt(), Some("waiver-leak(recursive-drop)"));
        assert_eq!(
            Witnessed(TakenBefore).receipt(),
            Some("depth-witness(none)")
        );
        assert_eq!(Witnessed(TakenBefore).render("p", "v"), None);
    }

    /// The controls: avl's own stores are each witnessed, and so stay plain
    /// assignments — `newNode` by the fresh literal, the rotations by their
    /// earlier take, `insert` by the take inside the stored call.
    #[test]
    fn r622_avls_own_stores_are_witnessed_none() {
        assert_eq!(
            avl("newNode"),
            [
                (
                    "(*node).left = 0 as *mut Node".to_owned(),
                    Witnessed(FreshLiteral)
                ),
                (
                    "(*node).right = 0 as *mut Node".to_owned(),
                    Witnessed(FreshLiteral)
                ),
            ]
        );
        for rotation in ["rightRotate", "leftRotate"] {
            let closes = avl(rotation);
            assert_eq!(closes.len(), 2, "{closes:?}");
            assert!(
                closes.iter().all(|(_, c)| *c == Witnessed(TakenBefore)),
                "{closes:?}"
            );
        }
        let insert = avl("insert");
        assert_eq!(insert.len(), 4, "{insert:?}");
        assert!(
            insert.iter().all(|(_, c)| *c == Witnessed(TakenInValue)),
            "{insert:?}"
        );
    }

    /// bst's stores, `deleteNode`'s three included, are witnessed the same way.
    #[test]
    fn r622_bsts_own_stores_are_witnessed_none() {
        let bst = |function| {
            closes(
                BST,
                function,
                &[("node", "left"), ("node", "right")],
                &["insert", "deleteNode"],
            )
        };
        let new_node = bst("newNode");
        assert_eq!(new_node.len(), 2, "{new_node:?}");
        assert!(new_node.iter().all(|(_, c)| *c == Witnessed(FreshLiteral)));
        for function in ["insert", "deleteNode"] {
            let closes = bst(function);
            assert!(!closes.is_empty());
            assert!(
                closes.iter().all(|(_, c)| *c == Witnessed(TakenInValue)),
                "{function}: {closes:?}"
            );
        }
        assert_eq!(bst("deleteNode").len(), 3);
    }

    /// Each witness, broken by one construct, leaks: the base named between
    /// the take and the store, a view where a move was needed (in a `let`
    /// and as the argument of a callee that does not own it), the base
    /// passed beside the taken value, a fresh base that escaped, and a fresh
    /// base's field overwritten a second time.
    #[test]
    fn r622_a_broken_witness_leaks() {
        for function in [
            "taken_then_named",
            "viewed_not_taken",
            "value_names_base",
            "passed_not_moved",
            "fresh_escaped",
        ] {
            let closes = avl(function);
            assert_eq!(closes.len(), 1, "{function}: {closes:?}");
            assert_eq!(closes[0].1, Leak, "{function}: {closes:?}");
        }
        // The first store still overwrites the literal's `None`; the second
        // overwrites the subtree the first stored.
        assert_eq!(
            avl("fresh_written_twice"),
            [
                (
                    "(*n).left = newNode(key)".to_owned(),
                    Witnessed(FreshLiteral)
                ),
                ("(*n).left = 0 as *mut Node".to_owned(), Leak),
            ]
        );
    }

    const LISTS: &str = "
#[repr(C)] pub struct Leaf { pub v: i32 }
#[repr(C)] pub struct Holder { pub leaf: *mut Leaf }
#[repr(C)] pub struct Cell { pub next: *mut Cell }
#[repr(C)] pub struct List { pub head: *mut Cell }
pub unsafe fn set_leaf(h: *mut Holder, l: *mut Leaf) { (*h).leaf = l; }
pub unsafe fn set_head(l: *mut List, c: *mut Cell) { (*l).head = c; }
";

    /// Recursion is over OWNING edges, reached from the payload: a leaf
    /// payload drops as before; a list head's payload is recursive through
    /// `Cell::next` when that field owns, and not when it does not.
    #[test]
    fn r622_recursion_follows_owning_edges_from_the_payload() {
        assert_eq!(
            closes(LISTS, "set_leaf", &[("Holder", "leaf")], &[]),
            [("(*h).leaf = l".to_owned(), Drop)]
        );
        assert_eq!(
            closes(
                LISTS,
                "set_head",
                &[("List", "head"), ("Cell", "next")],
                &[]
            ),
            [("(*l).head = c".to_owned(), Leak)]
        );
        assert_eq!(
            closes(LISTS, "set_head", &[("List", "head")], &[]),
            [("(*l).head = c".to_owned(), Drop)]
        );
    }
}
