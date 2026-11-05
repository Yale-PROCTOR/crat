//! **W6S-16 (R609-4, wave-6s 088 N1a) — a null-initialised C-string receiver
//! of a raw-returning local callee.**
//!
//! lil's `fnc_charat::str`, `fnc_rename::oldname`, `fnc_reflect::target`, … :
//!
//! ```text
//! let mut s = 0 as *const c_char;          let mut s: Option<&[c_char]> = None;
//! s = lil_to_string(v);               ->   s = { let t: *const c_char = lil_to_string(v);
//! if index >= strlen(s) { .. }                   if t.is_null() { None } else { Some(
//! *s.offset(index as isize)                        from_raw_parts(t, CStr::from_ptr(t).len() + 1)) } };
//! ```
//!
//! The form selection already calls such a local an optional SLICE (it is
//! indexed and handed to string functions); what kept it `null-init` is the
//! assignment clause of [`super::slice_local_construction::refuses`] — a local
//! callee's result is the return family's, because a constructor over a
//! CONVERTED return is E0308. Where the callee's return stays raw and no
//! receiver plan exists, that reason does not hold, and the refusal yields for
//! exactly this receiver.
//!
//! **The extent is the string's own, never fabricated** (R491-7): the body
//! passes the very pointer to a libc function whose contract requires a
//! terminated string ([`super::local_callee_extent::caller_establishes_nul`]),
//! so on a UB-free input (§28) the terminator is there and `strlen + 1` is the
//! object the program reads. The slice is built from the RAW temporary, not
//! from a one-element reference's provenance.

use rustc_hir::{
    Expr, ExprKind, HirId, Node, QPath,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{IntTy, TyCtxt, TyKind, UintTy};

use super::{Ctx, DecisionTable, Subject, SubjectKind};

/// The receipt's evidence for the extent.
pub(crate) const EVIDENCE: &str = "c-string:strlen+1";

fn peel<'a>(mut expr: &'a Expr<'a>) -> &'a Expr<'a> {
    while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) = expr.kind {
        expr = inner;
    }
    expr
}

/// A direct call to a function with a BODY in this crate whose declared return
/// is a raw pointer (an `extern "C"` item is a local `DefId` too, and is not
/// one).
fn raw_local_callee(tcx: TyCtxt<'_>, expr: &Expr<'_>) -> Option<LocalDefId> {
    let ExprKind::Call(function, _) = peel(expr).kind else { return None };
    let ExprKind::Path(QPath::Resolved(_, path)) = function.kind else { return None };
    let Res::Def(DefKind::Fn, did) = path.res else { return None };
    let local = did.as_local()?;
    tcx.hir_node_by_def_id(local).body_id()?;
    let output = tcx.fn_sig(did).skip_binder().skip_binder().output();
    matches!(output.kind(), TyKind::RawPtr(..)).then_some(local)
}

fn null(expr: &Expr<'_>) -> bool {
    super::emitability::is_zero_literal(expr)
}

/// Every assignment to the binding: a null literal or a raw-returning local
/// call; the callees of the calls, or `None` when any assignment is anything
/// else or there is no call at all.
fn assigned_callees(tcx: TyCtxt<'_>, subject: &Subject) -> Option<Vec<LocalDefId>> {
    struct Assignments<'tcx> {
        tcx: TyCtxt<'tcx>,
        binding: HirId,
        callees: Vec<LocalDefId>,
        other: bool,
    }
    impl<'tcx> Visitor<'tcx> for Assignments<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let ExprKind::Path(QPath::Resolved(_, path)) = lhs.kind
                && path.res == Res::Local(self.binding)
            {
                if let Some(callee) = raw_local_callee(self.tcx, rhs) {
                    self.callees.push(callee);
                } else if !null(rhs) {
                    self.other = true;
                }
            }
            // The address of the binding (an out-parameter) is a write this
            // shape does not describe.
            if let ExprKind::AddrOf(_, _, inner) = expr.kind
                && let ExprKind::Path(QPath::Resolved(_, path)) = inner.kind
                && path.res == Res::Local(self.binding)
            {
                self.other = true;
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let body = tcx.hir_node_by_def_id(subject.fn_did).body_id()?;
    let mut assignments = Assignments {
        tcx,
        binding: subject.hir_id,
        callees: Vec::new(),
        other: false,
    };
    assignments.visit_body(tcx.hir_body(body));
    (!assignments.other && !assignments.callees.is_empty()).then_some(assignments.callees)
}

/// A shared byte pointer (`*const c_char` / `*const u8`): the only pointee a
/// C string's length describes.
fn shared_byte_pointer(tcx: TyCtxt<'_>, subject: &Subject) -> bool {
    let Node::Pat(pattern) = tcx.hir_node(subject.hir_id) else { return false };
    matches!(
        tcx.typeck(subject.fn_did).pat_ty(pattern).kind(),
        TyKind::RawPtr(pointee, rustc_middle::ty::Mutability::Not)
            if matches!(pointee.kind(), TyKind::Int(IntTy::I8) | TyKind::Uint(UintTy::U8))
    )
}

/// The receiver shape and its licence, from the binding's own body.
fn licensed(tcx: TyCtxt<'_>, subject: &Subject) -> Option<Vec<LocalDefId>> {
    if !matches!(subject.kind, SubjectKind::Local)
        || subject.ty_span.is_some()
        || !subject.null_init
        || subject.mutable
        || !shared_byte_pointer(tcx, subject)
        || !super::local_callee_extent::caller_establishes_nul(tcx, subject)
    {
        return None;
    }
    assigned_callees(tcx, subject)
}

/// Decision time: the licence, no receiver plan, and no callee whose return
/// this run converts (the receiver carrier's value, which a constructor over it
/// would mistype).
pub(crate) fn admits(ctx: &Ctx<'_, '_>, subject: &Subject) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    licensed(ctx.tcx, subject).is_some_and(|callees| {
        ctx.return_receivers
            .is_none_or(|receivers| !receivers.plans.contains_key(&node))
            && callees.iter().all(|callee| {
                !ctx.lifetime_eligibility
                    .is_some_and(|eligibility| eligibility.thin_return_permit(*callee))
            })
    })
}

/// The receiver shape and its licence, whatever the callees' returns became.
/// The value planner reads this to HOLD such a receiver it does not admit,
/// rather than let it reach the fallback extent.
pub(crate) fn licensed_receiver(tcx: TyCtxt<'_>, subject: &Subject) -> bool {
    licensed(tcx, subject).is_some()
}

/// Plan time: the same receiver on the settled table — no receiver plan, and
/// no callee whose return interface this run converted.
pub(crate) fn admitted_on(tcx: TyCtxt<'_>, table: &DecisionTable, subject: &Subject) -> bool {
    licensed(tcx, subject).is_some_and(|callees| {
        !table
            .return_receivers
            .plans
            .contains_key(&(subject.fn_did, subject.hir_id))
            && callees
                .iter()
                .all(|callee| !table.return_interfaces.functions.contains_key(callee))
    })
}

/// A composed edit nested in the call (an argument's own bridge, e.g.
/// `*argv.offset(0)` → `.as_ref()`) is written for the AST layer, which
/// parenthesizes its receiver; spliced as TEXT it must carry the parentheses
/// itself, or `*argv.offset(0).as_ref()` derefs the wrong thing. Only a
/// replacement that extends its original with a method call, over an original
/// of lower precedence than a method receiver, is rewritten.
pub(crate) fn parenthesize_receiver(original: &str, replacement: &str) -> String {
    let original = original.trim();
    let low_precedence = original.starts_with(['*', '&', '-', '!']) || original.contains(" as ");
    match replacement.strip_prefix(original) {
        Some(rest) if low_precedence && rest.starts_with('.') => format!("({original}){rest}"),
        _ => replacement.to_owned(),
    }
}

/// The assignment's value: the call bound once to a raw temporary, `None` when
/// it is null, otherwise the slice over the string and its terminator.
pub(crate) fn render_value(
    initializer: &str,
    element_type: &str,
    enclosing_unsafe_fn: bool,
    local_index: u32,
) -> String {
    let temp = format!("__crat_cstr_ptr_{local_index}");
    let body = format!(
        "{{ let {temp}: *const {element_type} = {initializer}; if {temp}.is_null() {{ None }} else {{ Some(core::slice::from_raw_parts({temp}, core::ffi::CStr::from_ptr({temp} as *const core::ffi::c_char).to_bytes().len().wrapping_add(1))) }} }}"
    );
    crate::bo_rewriter::mechanical_receipt::present_unsafe_text(body, enclosing_unsafe_fn)
}
