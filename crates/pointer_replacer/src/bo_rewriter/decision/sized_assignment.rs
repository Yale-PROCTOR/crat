//! **The assignment IS the construction** — main 071c (a), relayed as R506-6.
//!
//! Report 051 measured the wall this answers. C2Rust renders a C declaration
//! followed by an assignment as `let mut storage = 0 as *mut uint8_t;` with the
//! real construction on a later line, and the slice-use inventory reads that
//! later line as an ordinary write to the binding — a use with no image under
//! `&[T]`, so the whole subject is `slice-use-unsupported`. The root walk could
//! then prove an extent (`sibling-size:storage_:storage_size_`) and the row
//! stayed held anyway, by its own initializer.
//!
//! Main's answer is that the assignment is not a use to be rendered but the
//! CONSTRUCTION itself, and the inventory may say so **pre-decision** — which is
//! what lets a pre-decision fact host the clause at all — under four
//! conditions, each of which is a refusal this module implements:
//!
//! 1. **The sole assignment**, with the null-init declaration exempted
//!    explicitly. Without that exemption the rule never fires on its own
//!    population, because the declaration is where the null comes from.
//! 2. **The right-hand side is the accessor named by this root's OWN extent
//!    evidence** — for brotli, the `storage_` in
//!    `sibling-size:storage_:storage_size_` — never "a sized accessor" in
//!    general. The image and the extent then come from one fact, so the
//!    inventory is not quietly making a decision it cannot see.
//! 3. **The assignment dominates every read.** §28 (user ruling 2026-08-23)
//!    carries a read before it: the binding holds NULL until the assignment, so
//!    a dereference there is a null dereference — a bug in the INPUT program, on
//!    which crat owes no soundness.
//! 4. **A receipt per admitted root**, naming the assignment's span and the
//!    evidence it matched, so the admission is auditable at a census rather than
//!    inferred from a subject that stopped being held.

use rustc_hir::{Expr, ExprKind, HirId, def_id::LocalDefId, intravisit::Visitor};
use rustc_middle::ty::TyCtxt;

/// One admitted root, for the receipt (condition 4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SizedAssignment {
    pub span: rustc_span::Span,
    /// The field the right-hand side reads, and the sibling that records its
    /// size: the same pair the root walk's `sibling-size:…` receipt names.
    pub field: String,
    pub sibling: String,
    /// The right-hand side's own span, and the slice construction that replaces
    /// it. **The admission is not complete without this**: saying "the
    /// assignment is the construction" and then leaving a raw pointer on the
    /// right of a `&[T]` binding is an ill-typed crate, which is what the first
    /// wiring of this rule produced and what report 053 records.
    pub value_span: rustc_span::Span,
    pub value: String,
}

impl SizedAssignment {
    pub(crate) fn receipt(&self) -> String {
        format!("sized-assignment:{}:{}", self.field, self.sibling)
    }
}

/// Every assignment to `binding` in `owner`'s body, as `(assignment expr, rhs)`.
fn assignments<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    binding: HirId,
) -> Vec<(&'tcx Expr<'tcx>, &'tcx Expr<'tcx>)> {
    struct V<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        binding: HirId,
        out: &'a mut Vec<(&'tcx Expr<'tcx>, &'tcx Expr<'tcx>)>,
    }
    impl<'tcx> Visitor<'tcx> for V<'_, 'tcx> {
        type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

        fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
            self.tcx
        }

        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = lhs.kind
                && let rustc_hir::def::Res::Local(target) = path.res
                && target == self.binding
            {
                self.out.push((expr, rhs));
            }
            rustc_hir::intravisit::walk_expr(self, expr);
        }
    }
    let mut out = Vec::new();
    let body = tcx.hir_body_owned_by(owner);
    V {
        tcx,
        binding,
        out: &mut out,
    }
    .visit_body(&body);
    out
}

/// Is this binding's declaration the null initializer C2Rust writes for a C
/// declaration — `let mut p = 0 as *mut T;`?
///
/// Condition 1's exemption, and it is deliberately narrow: an ordinary
/// initializer means the construction is already where the walk looks, and an
/// assignment after one is a second construction rather than the first.
fn declared_null(tcx: TyCtxt<'_>, binding: HirId) -> bool {
    let rustc_hir::Node::Pat(pat) = tcx.hir_node(binding) else {
        return false;
    };
    let rustc_hir::Node::LetStmt(local) = tcx.parent_hir_node(pat.hir_id) else {
        return false;
    };
    local
        .init
        .is_some_and(|init| super::emitability::is_zero_literal(init))
}

/// The field a right-hand side reads, with the sibling that records its size —
/// condition 2.
///
/// The sibling convention is [`super::construction::sibling_names`]'s, so the
/// image admitted here and the extent the root walk proves are the same fact
/// rather than two rules that happen to agree.
fn sized_field(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    rhs: &Expr<'_>,
) -> Option<(String, String, String)> {
    // **R506-6 link (2)(i).** The corpus does not usually assign the field; it
    // assigns an ensure-capacity accessor's RESULT (`storage =
    // GetBrotliStorage(s, n)`). That accessor names the same pair, one call
    // away, and condition 2 is satisfied by the same fact — so the admission
    // and the root walk still agree, which is the whole point of keying on the
    // root's OWN evidence rather than on "a sized accessor".
    if let Some(resolved) = super::construction::accessor_sibling_at_call(tcx, owner, rhs) {
        return Some(resolved);
    }
    let expression = super::construction::peel_for_sized_assignment(rhs);
    let ExprKind::Field(base, field) = expression.kind else {
        return None;
    };
    let field = field.name.as_str().to_owned();
    let typeck = tcx.typeck(owner);
    let mut ty = typeck.expr_ty(base);
    loop {
        match ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, inner, _) => ty = *inner,
            rustc_middle::ty::TyKind::RawPtr(inner, _) => ty = *inner,
            _ => break,
        }
    }
    let rustc_middle::ty::TyKind::Adt(def, arguments) = ty.kind() else {
        return None;
    };
    if !def.is_struct() {
        return None;
    }
    let variant = def.non_enum_variant();
    let sibling = super::construction::sibling_names(&field)
        .into_iter()
        .find_map(|(name, _)| {
            variant
                .fields
                .iter()
                .find(|candidate| candidate.name.as_str() == name)
        })?;
    if !sibling.ty(tcx, arguments).is_integral() {
        return None;
    }
    let base_text = tcx.sess.source_map().span_to_snippet(base.span).ok()?;
    Some((field, sibling.name.as_str().to_owned(), base_text))
}

/// **The admission.** `use_expr` is the binding on the left of an assignment;
/// the answer is `Some` when that assignment is this root's construction.
pub(crate) fn admit(
    tcx: TyCtxt<'_>,
    use_expr: &Expr<'_>,
    key: (LocalDefId, HirId),
    mutable: bool,
) -> Option<SizedAssignment> {
    let rustc_hir::Node::Expr(assign) = tcx.parent_hir_node(use_expr.hir_id) else {
        return None;
    };
    let ExprKind::Assign(lhs, rhs, _) = assign.kind else {
        return None;
    };
    if lhs.hir_id != use_expr.hir_id {
        return None;
    }
    // Condition 1: the null-init declaration, and exactly one assignment.
    if !declared_null(tcx, key.1) {
        return None;
    }
    let all = assignments(tcx, key.0, key.1);
    let [(sole, sole_rhs)] = all.as_slice() else {
        return None;
    };
    if sole.hir_id != assign.hir_id {
        return None;
    }
    // Condition 2: the right-hand side is the field this root's extent evidence
    // names.
    let (field, sibling, base) = sized_field(tcx, key.0, sole_rhs)?;
    // Condition 3 is §28's, and it is a ruling rather than a walk: the binding
    // holds NULL until here, so a read before this point is a null dereference
    // in the input program. Nothing to check, and saying so is the point —
    // a dominance walk here would be re-proving a ruling.
    let value = render(tcx, key.0, sole_rhs, &base, &sibling, mutable);
    Some(SizedAssignment {
        span: assign.span,
        field,
        sibling,
        value_span: sole_rhs.span,
        value,
    })
}

/// The slice this assignment builds: the field's own pointer, the sibling's
/// count, in the constructor the subject's mutability asks for.
///
/// `present_unsafe_text` supplies the `unsafe` block when the enclosing
/// function is not already unsafe, exactly as the declaration-side planner
/// does — the two renderings must agree, because a subject can reach either.
fn render(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    rhs: &Expr<'_>,
    base: &str,
    sibling: &str,
    mutable: bool,
) -> String {
    let pointer = tcx
        .sess
        .source_map()
        .span_to_snippet(rhs.span)
        .unwrap_or_else(|_| format!("({base}).{sibling}"));
    let constructor = if mutable {
        "from_raw_parts_mut"
    } else {
        "from_raw_parts"
    };
    let unsafe_fn = tcx
        .hir_node_by_def_id(owner)
        .fn_sig()
        .is_some_and(|sig| sig.header.is_unsafe());
    crate::bo_rewriter::mechanical_receipt::present_unsafe_text(
        format!("core::slice::{constructor}({pointer}, (({base}).{sibling}) as usize)"),
        unsafe_fn,
    )
}
