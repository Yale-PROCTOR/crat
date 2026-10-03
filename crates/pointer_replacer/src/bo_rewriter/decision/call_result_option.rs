//! **W6L-A8-1 (relay 026, R480-4): the receiver-side null adapter.**
//!
//! The `return-not-adapted` row's largest shape is an UNANNOTATED local that
//! takes a LOCAL callee's RAW pointer return, null-tests it, and reads or
//! writes the pointee — lil `add_func`/`lil_register`, binn
//! `binn_alloc_item`, urlparser `url_get_protocol` (11 of the 15 readable
//! rows at batch 18). The form selection above already calls such a subject
//! `Opt` by the program's own null test; what is missing is a DECLARATION
//! channel, so the ladder's residual gate degrades it and
//! [`super::residual_reason`] names the owed capability from the constructor:
//! a call result, hence `return-not-adapted`.
//!
//! This is that channel, and it owes nothing to the callee: the value is the
//! raw pointer's own `as_mut()` / `as_ref()` — the null-to-Option API, already
//! in the glue vocabulary as [`seam::GlueCore::RawOption`] — and the
//! declaration is `Option<&mut T>` / `Option<&T>`. The callee keeps its raw
//! return, so no class of the callee's moves.
//!
//! **The view is untied** (`as_mut()` infers an unbounded lifetime), which is
//! R401-8's shape and carries R401-8's guard: the local may not escape. Here
//! the guard is stated positively as a closed use vocabulary — the null test,
//! a deref, a field access — so a returned, stored or handed-on local is
//! refused rather than manufactured. That keeps the untied view inside the
//! frame that created it, which is what makes it safe on a UB-free input.
//!
//! **Review r1 of R785: the view must also be QUIET.** The frame is not
//! enough: the view exists from the declaration on, where the input had only
//! a raw pointer, so a write to the pointee through another pointer before a
//! use (or a read through another pointer between two writes through the
//! view) makes the output's access UB under Tree Borrows. [`quiet_window`]
//! refuses both.

use rustc_hash::FxHashSet;
use rustc_hir::{
    Expr, ExprKind, HirId, LetStmt, Node, PatKind, QPath, StmtKind, UnOp,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{Ctx, Decision, DeclShape, Subject, SubjectKind, declaration, seam};
use crate::bo_rewriter::{additive::FamilyStage, bridge_receipt::SignatureClassId};

pub(crate) struct CallResultValue {
    pub(crate) initializer: Span,
    pub(crate) pointee: String,
    pub(crate) callee: LocalDefId,
}

fn peel<'a>(mut expr: &'a Expr<'a>) -> &'a Expr<'a> {
    while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) | ExprKind::Type(inner, _) =
        expr.kind
    {
        expr = inner;
    }
    expr
}

/// The initializer is an exact direct call to a function with a body in this
/// crate. An indirect call (a function pointer) and a foreign callee are both
/// refused: the first has no single callee to reason about, and the second is
/// the allocator families' value, not this one's.
fn local_callee(tcx: TyCtxt<'_>, expr: &Expr<'_>) -> Option<LocalDefId> {
    let ExprKind::Call(function, _) = peel(expr).kind else { return None };
    let ExprKind::Path(QPath::Resolved(_, path)) = function.kind else { return None };
    let Res::Def(DefKind::Fn, did) = path.res else { return None };
    let local = did.as_local()?;
    // A declaration inside `unsafe extern "C" { .. }` is `DefKind::Fn` and IS
    // `as_local` — the extern block belongs to this crate. "Local" here means
    // a function with a BODY (wave-6a's R410-9 (b) rule, same words): a
    // foreign result carries a contract this arm does not read, and belongs to
    // the contract families. Measured: without this, libtree's `strchr` row
    // types itself (`w6l_a8_foreign_callee_result_is_refused`).
    tcx.hir_node_by_def_id(local).body_id().map(|_| local)
}

/// The closed use vocabulary. Every use of the local must be one the Option
/// form has an image for AND one that keeps the view inside this frame: the
/// null test, a dereference (`*cmd`, `(*cmd).field`), or a field access. A
/// `return`, a store, a cast and a call argument are all refused here.
struct Uses<'tcx> {
    tcx: TyCtxt<'tcx>,
    binding: HirId,
    ok: bool,
    seen_null_test: bool,
}

impl<'tcx> Uses<'tcx> {
    fn is_the_local(&self, expr: &Expr<'_>) -> bool {
        matches!(expr.kind, ExprKind::Path(QPath::Resolved(_, path))
            if matches!(path.res, Res::Local(hir) if hir == self.binding))
    }
}

impl<'tcx> Visitor<'tcx> for Uses<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::MethodCall(segment, receiver, args, _)
                if self.is_the_local(receiver) && segment.ident.name.as_str() == "is_null" =>
            {
                self.seen_null_test = true;
                for arg in args {
                    intravisit::walk_expr(self, arg);
                }
                return;
            }
            ExprKind::Unary(UnOp::Deref, inner) if self.is_the_local(inner) => return,
            ExprKind::Field(base, _) if self.is_the_local(base) => return,
            // Review of the quiet window, finding 3: a pointer taken from the
            // view (`&raw mut (*q).f`, `addr_of_mut!`, `&mut (*q).f as *mut _`)
            // carries the view's tag past its last use.
            ExprKind::AddrOf(_, _, inner) if through(self.binding, inner) => {
                self.ok = false;
                return;
            }
            _ => {}
        }
        if self.is_the_local(expr) {
            // A use this vocabulary does not name.
            self.ok = false;
            return;
        }
        intravisit::walk_expr(self, expr);
    }
}

fn uses_are_closed(tcx: TyCtxt<'_>, subject: &Subject) -> bool {
    let Some(body_id) = tcx.hir_node_by_def_id(subject.fn_did).body_id() else { return false };
    let mut uses = Uses {
        tcx,
        binding: subject.hir_id,
        ok: true,
        seen_null_test: false,
    };
    uses.visit_body(tcx.hir_body(body_id));
    uses.ok && uses.seen_null_test
}

/// Every use of `binding` in a body, by a walk that never stops early, and the
/// locals whose address the body takes (their memory may be the pointee).
struct AllUses {
    binding: HirId,
    spans: Vec<Span>,
    closure: bool,
    borrowed: FxHashSet<HirId>,
    /// The end of the assignment whose written place is being walked: a use
    /// there takes effect when the assignment does, after its right side.
    in_written_place: Option<rustc_span::BytePos>,
    /// Where the view's last use takes effect.
    last_point: rustc_span::BytePos,
}

impl<'tcx> Visitor<'tcx> for AllUses {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Closure(..) => self.closure = true,
            ExprKind::Path(QPath::Resolved(_, path)) => {
                if let Res::Local(hir) = path.res
                    && hir == self.binding
                {
                    self.spans.push(expr.span);
                    let point = self.in_written_place.unwrap_or(expr.span.hi());
                    self.last_point = self.last_point.max(point);
                }
            }
            ExprKind::AddrOf(_, _, inner) => {
                if let Some(hir) = place_root_local(inner) {
                    self.borrowed.insert(hir);
                }
            }
            ExprKind::Assign(lhs, rhs, _) | ExprKind::AssignOp(_, lhs, rhs) => {
                self.visit_expr(rhs);
                let outer = self.in_written_place.replace(expr.span.hi());
                self.visit_expr(lhs);
                self.in_written_place = outer;
                return;
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

/// The local a place expression is rooted at, through fields and indexing
/// only (`x`, `x.f`, `x[i].g`) — not through a dereference.
fn place_root_local(mut expr: &Expr<'_>) -> Option<HirId> {
    loop {
        match expr.kind {
            ExprKind::Field(base, _) | ExprKind::Index(base, _, _) => expr = base,
            ExprKind::Path(QPath::Resolved(_, path)) => {
                return match path.res {
                    Res::Local(hir) => Some(hir),
                    _ => None,
                };
            }
            _ => return None,
        }
    }
}

/// A place written THROUGH the local: `*l`, `(*l).f`, `(*l).a[i]`.
fn through(binding: HirId, mut expr: &Expr<'_>) -> bool {
    loop {
        match expr.kind {
            ExprKind::Field(base, _) | ExprKind::Index(base, _, _) => expr = base,
            ExprKind::Unary(UnOp::Deref, inner) => {
                return matches!(inner.kind, ExprKind::Path(QPath::Resolved(_, path))
                    if matches!(path.res, Res::Local(hir) if hir == binding));
            }
            _ => return false,
        }
    }
}

/// Raw-pointer methods that compute an address and touch no memory.
const ADDRESS_METHODS: &[&str] = &[
    "is_null",
    "offset",
    "add",
    "sub",
    "wrapping_offset",
    "wrapping_add",
    "wrapping_sub",
    "offset_from",
    "cast",
    "cast_mut",
    "cast_const",
];

/// The window's checker: what may run between the declaration and the last
/// use, and where the view's writes and the other memory reads lie.
struct Window<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
    binding: HirId,
    borrowed: &'a FxHashSet<HirId>,
    ok: bool,
    /// The point (end of the assignment) of each write through the view.
    writes: Vec<rustc_span::BytePos>,
    /// Each read of memory the view may share: a dereference of another
    /// pointer, or an address-taken local.
    foreign_reads: Vec<Span>,
    /// Where the view's last use takes effect: what starts after it cannot
    /// reach the view.
    cut: rustc_span::BytePos,
}

impl<'a, 'tcx> Window<'a, 'tcx> {
    /// A local whose memory the view cannot reach: never address-taken and of
    /// a scalar type (an array or a struct can decay or be referenced without
    /// an `&` in HIR).
    fn private_scalar(&self, hir: HirId) -> bool {
        let ty = self.typeck.node_type(hir);
        !self.borrowed.contains(&hir)
            && (ty.is_integral()
                || ty.is_floating_point()
                || ty.is_bool()
                || ty.is_char()
                || ty.is_raw_ptr())
    }

    fn is_the_local(&self, expr: &Expr<'_>) -> bool {
        matches!(expr.kind, ExprKind::Path(QPath::Resolved(_, path))
            if matches!(path.res, Res::Local(hir) if hir == self.binding))
    }

    fn pure_method(
        &self,
        expr: &Expr<'tcx>,
        segment: &rustc_hir::PathSegment<'_>,
        receiver: &Expr<'tcx>,
    ) -> bool {
        let Some(method) = self.typeck.type_dependent_def_id(expr.hir_id) else { return false };
        if method.is_local() {
            return false;
        }
        let ty = self.typeck.expr_ty(receiver);
        let name = segment.ident.name.as_str();
        if ty.is_raw_ptr() {
            return ADDRESS_METHODS.contains(&name);
        }
        // `Option::is_some` / `is_none` read their receiver only.
        if let TyKind::Adt(adt, _) = ty.kind()
            && self
                .tcx
                .is_diagnostic_item(rustc_span::sym::Option, adt.did())
        {
            return matches!(name, "is_some" | "is_none");
        }
        ty.is_integral() || ty.is_floating_point() || ty.is_bool() || ty.is_char()
    }
}

impl<'a, 'tcx> Visitor<'tcx> for Window<'a, 'tcx> {
    fn visit_stmt(&mut self, stmt: &'tcx rustc_hir::Stmt<'tcx>) {
        if stmt.span.lo() >= self.cut {
            return;
        }
        if let StmtKind::Item(..) = stmt.kind {
            self.ok = false;
            return;
        }
        intravisit::walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if !self.ok || expr.span.lo() >= self.cut {
            return;
        }
        // Review of the quiet window, findings 4 and 5: a macro expansion's
        // span is not in the window's text order, and an overloaded operator
        // runs code.
        if matches!(
            expr.span.ctxt().outer_expn_data().kind,
            rustc_span::hygiene::ExpnKind::Macro(..)
        ) || (matches!(
            expr.kind,
            ExprKind::Binary(..)
                | ExprKind::AssignOp(..)
                | ExprKind::Unary(..)
                | ExprKind::Index(..)
        ) && self.typeck.is_method_call(expr))
        {
            self.ok = false;
            return;
        }
        match expr.kind {
            ExprKind::Loop(..) | ExprKind::Closure(..) | ExprKind::InlineAsm(..) => {
                self.ok = false;
            }
            ExprKind::Call(function, args) => {
                // A constructor (`Some(..)`) runs no code; every other call may
                // write anything.
                let constructor = matches!(function.kind, ExprKind::Path(QPath::Resolved(_, path))
                    if matches!(path.res, Res::Def(DefKind::Ctor(..), _)));
                if !constructor {
                    self.ok = false;
                    return;
                }
                for arg in args {
                    self.visit_expr(arg);
                }
            }
            ExprKind::MethodCall(segment, receiver, args, _) => {
                if self.is_the_local(receiver) && segment.ident.name.as_str() == "is_null" {
                    return;
                }
                if !self.pure_method(expr, segment, receiver) {
                    self.ok = false;
                    return;
                }
                intravisit::walk_expr(self, expr);
            }
            ExprKind::Assign(lhs, rhs, _) | ExprKind::AssignOp(_, lhs, rhs) => {
                self.visit_expr(rhs);
                if through(self.binding, lhs) {
                    // The place's own index expressions are reads like any other.
                    self.visit_place_operands(lhs);
                    self.writes.push(expr.span.hi());
                } else if let Some(hir) = place_root_local(lhs)
                    && hir != self.binding
                    && self.private_scalar(hir)
                {
                    self.visit_place_operands(lhs);
                } else {
                    self.ok = false;
                }
            }
            ExprKind::Unary(UnOp::Deref, inner) => {
                if !self.is_the_local(inner) {
                    self.foreign_reads.push(expr.span);
                    self.visit_expr(inner);
                }
            }
            ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                // Review of the quiet window, finding 1: memory the view may
                // point into — an address-taken local, any non-scalar local
                // (an array decays by `as_mut_ptr()` with no `&` in HIR), or a
                // static (finding 2).
                Res::Local(hir) if hir != self.binding && !self.private_scalar(hir) => {
                    self.foreign_reads.push(expr.span);
                }
                Res::Def(DefKind::Static { .. }, _) => self.foreign_reads.push(expr.span),
                _ => {}
            },
            _ => intravisit::walk_expr(self, expr),
        }
    }
}

impl<'a, 'tcx> Window<'a, 'tcx> {
    /// The operands of a written place other than its root: index expressions.
    fn visit_place_operands(&mut self, mut expr: &'tcx Expr<'tcx>) {
        loop {
            match expr.kind {
                ExprKind::Field(base, _) => expr = base,
                ExprKind::Index(base, index, _) => {
                    self.visit_expr(index);
                    expr = base;
                }
                ExprKind::Unary(UnOp::Deref, _) | ExprKind::Path(..) => return,
                _ => {
                    self.visit_expr(expr);
                    return;
                }
            }
        }
    }
}

/// **The quiet window (review r1 of R785).**
///
/// `as_mut()` makes the `&mut T` at the DECLARATION; the input made no
/// reference at all, only accesses through the raw pointer where it is used.
/// Under Tree Borrows that early reference is disabled by a write to its
/// pointee through any other pointer, and frozen by a read through another
/// pointer once it has been written through — after which an access through
/// it is UB although the input's accesses were defined. So the view is
/// admitted only when every use of the local lies in its `let`'s block, in the
/// statements from the `let` to the last statement that uses it, and that
/// window — cut where the last use takes effect (a use in an assignment's
/// written place takes effect at the assignment's end, after its right side),
/// since nothing after that can reach the view —
/// - runs no call but a constructor, and no method but an address
///   computation on a raw pointer, arithmetic on a scalar, an `Option`'s
///   discriminant test, or the local's own null test;
/// - assigns only through the local, or to a local whose address the body
///   never takes;
/// - does not loop (so the window's text order is its execution order); and
/// - reads no other pointer's memory between two writes through the view.
///
/// Then nothing but the view itself writes the pointee while the view lives,
/// and nothing reads it while the view is Active and about to be written.
fn quiet_window(tcx: TyCtxt<'_>, subject: &Subject, local: &LetStmt<'_>) -> bool {
    let Some(body_id) = tcx.hir_node_by_def_id(subject.fn_did).body_id() else { return false };
    let mut all = AllUses {
        binding: subject.hir_id,
        spans: Vec::new(),
        closure: false,
        borrowed: FxHashSet::default(),
        in_written_place: None,
        last_point: rustc_span::BytePos(0),
    };
    all.visit_body(tcx.hir_body(body_id));
    if all.closure || all.borrowed.contains(&subject.hir_id) {
        return false;
    }
    let Node::Stmt(stmt) = tcx.parent_hir_node(local.hir_id) else { return false };
    let Node::Block(block) = tcx.parent_hir_node(stmt.hir_id) else { return false };
    let Some(position) = block.stmts.iter().position(|s| s.hir_id == stmt.hir_id) else {
        return false;
    };
    enum Item<'hir> {
        Stmt(&'hir rustc_hir::Stmt<'hir>),
        Tail(&'hir Expr<'hir>),
    }
    let items = block.stmts[position + 1..]
        .iter()
        .map(Item::Stmt)
        .chain(block.expr.map(Item::Tail))
        .collect::<Vec<_>>();
    let span_of = |item: &Item<'_>| match item {
        Item::Stmt(stmt) => stmt.span,
        Item::Tail(expr) => expr.span,
    };
    let Some(last) = items
        .iter()
        .rposition(|item| all.spans.iter().any(|use_| span_of(item).contains(*use_)))
    else {
        return false;
    };
    let window = &items[..=last];
    if !all
        .spans
        .iter()
        .all(|use_| window.iter().any(|item| span_of(item).contains(*use_)))
    {
        return false;
    }
    let typeck = tcx.typeck(subject.fn_did);
    let mut checker = Window {
        tcx,
        cut: all.last_point,
        typeck,
        binding: subject.hir_id,
        borrowed: &all.borrowed,
        ok: true,
        writes: Vec::new(),
        foreign_reads: Vec::new(),
    };
    for item in window {
        match item {
            Item::Stmt(stmt) => checker.visit_stmt(stmt),
            Item::Tail(expr) => checker.visit_expr(expr),
        }
    }
    checker.ok
        && !checker.foreign_reads.iter().any(|read| {
            checker.writes.iter().any(|&w| w <= read.lo())
                && checker.writes.iter().any(|&w| w >= read.hi())
        })
}

/// The `null` test of `binding`: `binding.is_null()`.
fn is_null_test(binding: HirId, expr: &Expr<'_>) -> bool {
    let expr = peel(expr);
    matches!(expr.kind, ExprKind::MethodCall(segment, receiver, [], _)
        if segment.ident.name.as_str() == "is_null"
            && matches!(receiver.kind, ExprKind::Path(QPath::Resolved(_, path))
                if matches!(path.res, Res::Local(hir) if hir == binding)))
}

/// A block that never falls through: it ends in `return`.
fn diverges(block: &rustc_hir::Block<'_>) -> bool {
    match block.expr {
        Some(expr) => matches!(peel(expr).kind, ExprKind::Ret(..)),
        None => block.stmts.last().is_some_and(|stmt| {
            matches!(stmt.kind, StmtKind::Semi(expr) | StmtKind::Expr(expr)
                if matches!(peel(expr).kind, ExprKind::Ret(..)))
        }),
    }
}

/// The expression an item of a block evaluates (a `let`'s initializer).
fn item_expr<'hir>(stmt: &'hir rustc_hir::Stmt<'hir>) -> Option<&'hir Expr<'hir>> {
    match stmt.kind {
        StmtKind::Let(local) => local.init,
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => Some(expr),
        StmtKind::Item(..) => None,
    }
}

/// Whether `expr` can leave its block (`return`, `break`, `continue`) anywhere.
fn may_exit(expr: &Expr<'_>) -> bool {
    struct Exits(bool);
    impl<'tcx> Visitor<'tcx> for Exits {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if matches!(
                expr.kind,
                ExprKind::Ret(..) | ExprKind::Break(..) | ExprKind::Continue(..)
            ) {
                self.0 = true;
                return;
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut exits = Exits(false);
    exits.visit_expr(expr);
    exits.0
}

/// **R791-4 (b): a dereference of `binding` that `expr` evaluates on EVERY
/// path through it** — not under an `if` / `match` arm, the right side of
/// `&&` / `||`, a loop or a closure, and not after a statement that may leave.
/// A whole-argument hand-off to a local callee (R785) counts: the call's
/// reborrow dereferences.
struct Unconditional<'tcx> {
    tcx: TyCtxt<'tcx>,
    binding: HirId,
    found: bool,
    stopped: bool,
}

impl<'tcx> Unconditional<'tcx> {
    fn is_the_local(&self, expr: &Expr<'_>) -> bool {
        matches!(expr.kind, ExprKind::Path(QPath::Resolved(_, path))
            if matches!(path.res, Res::Local(hir) if hir == self.binding))
    }
}

impl<'tcx> Visitor<'tcx> for Unconditional<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if self.found || self.stopped {
            return;
        }
        match expr.kind {
            ExprKind::Unary(UnOp::Deref, inner) if self.is_the_local(inner) => self.found = true,
            ExprKind::Call(_, args)
                if local_callee(self.tcx, expr).is_some()
                    && args.iter().any(|arg| self.is_the_local(arg)) =>
            {
                self.found = true;
            }
            ExprKind::If(cond, ..) => self.visit_expr(cond),
            ExprKind::Match(scrutinee, ..) => self.visit_expr(scrutinee),
            ExprKind::Binary(op, left, _)
                if matches!(
                    op.node,
                    rustc_hir::BinOpKind::And | rustc_hir::BinOpKind::Or
                ) =>
            {
                self.visit_expr(left);
            }
            ExprKind::Loop(..) | ExprKind::Closure(..) => {}
            ExprKind::Block(block, _) => {
                for stmt in block.stmts {
                    let Some(item) = item_expr(stmt) else { continue };
                    self.visit_expr(item);
                    if self.found || may_exit(item) {
                        self.stopped = !self.found;
                        return;
                    }
                }
                if let Some(tail) = block.expr {
                    self.visit_expr(tail);
                }
            }
            _ => intravisit::walk_expr(self, expr),
        }
    }
}

fn dereferences_unconditionally<'tcx>(
    tcx: TyCtxt<'tcx>,
    binding: HirId,
    expr: &'tcx Expr<'tcx>,
) -> bool {
    let mut walk = Unconditional {
        tcx,
        binding,
        found: false,
        stopped: false,
    };
    walk.visit_expr(expr);
    walk.found
}

/// **R791-4 (b), ruled without a premise.** `as_mut()` asserts that the pointer
/// is dereferenceable at the DECLARATION, on every non-null path; the input
/// only dereferences where it does. So the view is kept only where every
/// non-null path dereferences it before anything else can run (the quiet
/// window refuses calls): either
/// - the item right after the `let` is `if q.is_null() { .. return .. }` and
///   the next item dereferences `q` unconditionally, or
/// - the item right after the `let` holds, where it is evaluated
///   unconditionally, an `if` on `q`'s own null test whose non-null branch
///   dereferences `q` unconditionally.
fn dereferenced_on_every_non_null_path(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    local: &LetStmt<'_>,
) -> bool {
    let binding = subject.hir_id;
    let Node::Stmt(stmt) = tcx.parent_hir_node(local.hir_id) else { return false };
    let Node::Block(block) = tcx.parent_hir_node(stmt.hir_id) else { return false };
    let Some(position) = block.stmts.iter().position(|s| s.hir_id == stmt.hir_id) else {
        return false;
    };
    let items = block.stmts[position + 1..]
        .iter()
        .filter_map(item_expr)
        .chain(block.expr)
        .collect::<Vec<_>>();
    let Some(first) = items.first() else { return false };
    // Shape (i): the early-returning null test, then a dereference.
    if let ExprKind::If(cond, then, None) = peel(first).kind
        && is_null_test(binding, cond)
        && matches!(then.kind, ExprKind::Block(then, _) if diverges(then))
    {
        return items
            .get(1)
            .is_some_and(|next| dereferences_unconditionally(tcx, binding, next));
    }
    // Shape (ii): an unconditionally evaluated `if` on the null test.
    struct GuardedIf<'tcx> {
        tcx: TyCtxt<'tcx>,
        binding: HirId,
        ok: bool,
        done: bool,
    }
    impl<'tcx> Visitor<'tcx> for GuardedIf<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if self.done {
                return;
            }
            match expr.kind {
                ExprKind::If(cond, then, otherwise) => {
                    let cond = peel(cond);
                    let non_null = if is_null_test(self.binding, cond) {
                        otherwise
                    } else if let ExprKind::Unary(UnOp::Not, inner) = cond.kind
                        && is_null_test(self.binding, inner)
                    {
                        Some(then)
                    } else {
                        // An `if` on anything else: its branches are
                        // conditional; only its condition is evaluated.
                        self.visit_expr(cond);
                        return;
                    };
                    self.done = true;
                    self.ok = non_null.is_some_and(|arm| {
                        dereferences_unconditionally(self.tcx, self.binding, arm)
                    });
                }
                ExprKind::Match(scrutinee, ..) => self.visit_expr(scrutinee),
                ExprKind::Binary(op, left, _)
                    if matches!(
                        op.node,
                        rustc_hir::BinOpKind::And | rustc_hir::BinOpKind::Or
                    ) =>
                {
                    self.visit_expr(left);
                }
                ExprKind::Loop(..) | ExprKind::Closure(..) => {}
                _ => intravisit::walk_expr(self, expr),
            }
        }
    }
    let mut guarded = GuardedIf {
        tcx,
        binding,
        ok: false,
        done: false,
    };
    guarded.visit_expr(first);
    guarded.ok
}

/// **R791-4 (a), ruled without a premise (until the retained-alias phase 2).**
/// The declaration's retag reads the WHOLE pointee; the input read only the
/// fields it touched. A live pointer into the pointee may therefore be frozen
/// (or, written later, invalidated) by the declaration alone. So no other
/// binding declared before the view, of pointer type, whose pointee the type
/// route (`disjoint_pointees`, R609-3 under R542) does not prove disjoint from
/// the view's, may be used after the declaration.
fn no_other_pointer_live_across<'tcx>(
    tcx: TyCtxt<'tcx>,
    subject: &Subject,
    local: &LetStmt<'_>,
    pointee: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    let Some(body_id) = tcx.hir_node_by_def_id(subject.fn_did).body_id() else { return false };
    let body = tcx.hir_body(body_id);
    let typeck = tcx.typeck(subject.fn_did);
    struct Bindings(Vec<(HirId, Span)>);
    impl<'tcx> Visitor<'tcx> for Bindings {
        fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
            if let PatKind::Binding(_, hir, ..) = pat.kind {
                self.0.push((hir, pat.span));
            }
            intravisit::walk_pat(self, pat);
        }
    }
    let mut bindings = Bindings(Vec::new());
    bindings.visit_body(body);
    let declared = local.span.lo();
    let after = local.span.hi();
    let suspects = bindings
        .0
        .into_iter()
        .filter(|&(hir, span)| {
            hir != subject.hir_id
                && span.lo() < declared
                && match typeck.node_type(hir).kind() {
                    TyKind::RawPtr(other, _) | TyKind::Ref(_, other, _) => {
                        crate::analyses::borrow_ownership::retirement::discharge::disjoint_pointees(
                            tcx, *other, pointee,
                        )
                        .is_none()
                    }
                    _ => false,
                }
        })
        .map(|(hir, _)| hir)
        .collect::<FxHashSet<_>>();
    struct UsedAfter<'a> {
        suspects: &'a FxHashSet<HirId>,
        after: rustc_span::BytePos,
        used: bool,
    }
    impl<'a, 'tcx> Visitor<'tcx> for UsedAfter<'a> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = expr.kind
                && let Res::Local(hir) = path.res
                && self.suspects.contains(&hir)
                && expr.span.lo() >= self.after
            {
                self.used = true;
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut used = UsedAfter {
        suspects: &suspects,
        after,
        used: false,
    };
    used.visit_body(body);
    !used.used
}

pub(crate) fn value(tcx: TyCtxt<'_>, subject: &Subject) -> Option<CallResultValue> {
    if subject.kind != SubjectKind::Local
        || subject.ty_span.is_some()
        || subject.decl_shape != DeclShape::RawPtr
        || subject.ptr_depth != 1
        || subject.null_init
        || subject.binding_span.from_expansion()
    {
        return None;
    }
    let Node::LetStmt(local) = tcx.parent_hir_node(subject.hir_id) else { return None };
    let PatKind::Binding(mode, hir, _, None) = local.pat.kind else { return None };
    if hir != subject.hir_id || mode.0 != rustc_hir::ByRef::No || local.ty.is_some() {
        return None;
    }
    let initializer = local.init?;
    if initializer.span.from_expansion() {
        return None;
    }
    let typeck = tcx.typeck(subject.fn_did);
    let TyKind::RawPtr(pointee, _) = typeck.pat_ty(local.pat).kind() else { return None };
    if typeck.expr_ty(initializer) != typeck.pat_ty(local.pat)
        || !declaration::pointee_is_nameable(tcx, subject.fn_did, *pointee)
    {
        return None;
    }
    let callee = local_callee(tcx, initializer)?;
    // The callee's own return must still be RAW. A converted return is the
    // return receiver's value (`raw_receiver`), and re-adapting it with
    // `as_mut()` would be ill-typed.
    let signature = tcx.fn_sig(callee.to_def_id()).skip_binder().skip_binder();
    if !matches!(signature.output().kind(), TyKind::RawPtr(..)) {
        return None;
    }
    if !uses_are_closed(tcx, subject)
        || !quiet_window(tcx, subject, local)
        || !dereferenced_on_every_non_null_path(tcx, subject, local)
        || !no_other_pointer_live_across(tcx, subject, local, *pointee)
    {
        return None;
    }
    Some(CallResultValue {
        initializer: initializer.span,
        pointee: declaration::pointee_source(tcx, *pointee),
        callee,
    })
}

fn thin_optional(decision: &Decision) -> Option<bool> {
    match decision {
        Decision::Opt {
            mutable,
            slice: false,
            ..
        } => Some(*mutable),
        Decision::Opt { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => None,
    }
}

pub(super) fn permits(ctx: &Ctx<'_, '_>, subject: &Subject) -> bool {
    ctx.family_policy
        .enabled(subject.fn_did, FamilyStage::Declaration)
        && value(ctx.tcx, subject).is_some()
}

pub(super) fn complete(tcx: TyCtxt<'_>, table: &super::DecisionTable, plan: &mut seam::SeamPlan) {
    for (subject, decision) in &table.entries {
        let Some(mutable) = thin_optional(decision) else { continue };
        let Some(value) = value(tcx, subject) else { continue };
        let node = (subject.fn_did, subject.hir_id);
        if plan.raw_boundary_atom_groups.contains_key(&node) {
            continue;
        }
        let Some(emitted_type) = declaration::emitted_type(decision, &value.pointee, None) else {
            continue;
        };
        // The Option family already renders this initializer's value — the raw
        // pointer's own `as_mut()` under a cast to the pointee. Only the
        // declaration is missing, so only the declaration is planned here; a
        // second adapter would compose over the first (measured: a doubled
        // `as_mut()`, `E0605`).
        if plan
            .explicit_declarations
            .iter()
            .any(|site| site.node == Some(node))
        {
            continue;
        }
        let owner_class = SignatureClassId::of(subject.fn_did);
        let _ = (mutable, value.callee);
        plan.explicit_declarations
            .push(seam::ExplicitDeclarationSite {
                owner_class,
                caller: subject.fn_did,
                node: Some(node),
                span: Some(subject.binding_span.shrink_to_hi()),
                category: "local",
                replacement: Some(format!(": {emitted_type}")),
                emitted_type,
                arm: "surface",
            });
    }
}

pub(crate) fn has_declaration(table: &super::DecisionTable, subject: &Subject) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    subject.ty_span.is_none()
        && table.seams.explicit_declarations.iter().any(|site| {
            site.node == Some(node)
                && site.category == "local"
                && site.owner_class == SignatureClassId::of(subject.fn_did)
        })
}
