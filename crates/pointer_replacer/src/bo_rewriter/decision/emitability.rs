//! **A1 emitability facts.** Static preconditions for emitting a reference,
//! gathered from HIR before any decision is made.
//!
//! # Why this exists
//!
//! S1 decided `Ref` on the BO slot kind alone and let the emitted crate fail
//! the type-check gate. That produced one anonymous whole-crate string with no
//! site and no subject, which is useless as attribution and — worse — made the
//! envelope-demotion counters wrong by construction: a parameter that was
//! decided `Ref` and then killed at the gate is recorded as a *success* by the
//! decision phase.
//!
//! A1 moves those preconditions to where the decision is made, so a subject
//! that cannot be emitted is degraded **with its own site and reason**.
//!
//! # What is modelled at S2a
//!
//! 1. **Raw-pointer-only operations on the parameter** (`p.is_null()`,
//!    `p.offset(..)`, and friends). A `&T` has no such method, so emitting a
//!    reference makes the body ill-typed. This is the g02 class.
//! 2. **In-crate callers.** `plan` rewrites a signature but not its call sites,
//!    so any direct in-crate call makes the crate ill-typed. This is the g06
//!    class, and it is a *temporary* precondition: S3 adds call-site
//!    adaptation, at which point this fact stops forcing a degradation.

use rustc_hash::FxHashMap;
use rustc_hir::{
    Expr, ExprKind, HirId, QPath,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

/// Methods that exist on raw pointers and not on references.
///
/// Deliberately a small, exact list rather than a heuristic: a false positive
/// here degrades a parameter that could have been emitted (a lost rewrite), and
/// a false negative lets the old anonymous gate failure back in. Both are
/// visible, which is why the list is allowed to grow from evidence rather than
/// from guessing.
const RAW_ONLY_METHODS: &[&str] = &[
    "is_null",
    "offset",
    "wrapping_offset",
    "add",
    "sub",
    "wrapping_add",
    "wrapping_sub",
    "offset_from",
    "read",
    "write",
    "read_volatile",
    "write_volatile",
    "copy_to",
    "copy_from",
    "as_ref",
    "as_mut",
];

#[derive(Debug, Default)]
pub(crate) struct EmitabilityFacts {
    /// `callee -> (caller, call span)`. Non-empty means a signature change
    /// would break an unadapted call site.
    pub callers: FxHashMap<LocalDefId, Vec<(LocalDefId, Span)>>,
    /// `(fn, param HirId) -> (method name, use span)` — first raw-only use.
    pub raw_only_uses: FxHashMap<(LocalDefId, HirId), (String, Span)>,
}

/// Gather A1 facts for the whole crate in one HIR pass per function body.
pub(crate) fn collect(tcx: TyCtxt<'_>, functions: &[LocalDefId]) -> EmitabilityFacts {
    let mut facts = EmitabilityFacts::default();
    let local: Vec<LocalDefId> = functions.to_vec();
    for &fn_did in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
            continue;
        };
        let body = tcx.hir_body(body_id);
        let mut visitor = BodyFacts {
            tcx,
            fn_did,
            locals: &local,
            facts: &mut facts,
        };
        visitor.visit_body(body);
    }
    facts
}

struct BodyFacts<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    locals: &'a [LocalDefId],
    facts: &'a mut EmitabilityFacts,
}

impl<'a, 'tcx> BodyFacts<'a, 'tcx> {
    /// The `HirId` of the binding a path expression resolves to, if it is a
    /// local. That is how a use is attributed to a specific parameter rather
    /// than to a name that might be shadowed.
    fn resolved_local(expr: &Expr<'_>) -> Option<HirId> {
        let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind else {
            return None;
        };
        match path.res {
            Res::Local(hir_id) => Some(hir_id),
            _ => None,
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for BodyFacts<'a, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match &expr.kind {
            // (1) raw-pointer-only method on a local
            ExprKind::MethodCall(segment, receiver, _, _) => {
                let method = segment.ident.name.to_string();
                if RAW_ONLY_METHODS.contains(&method.as_str())
                    && let Some(hir_id) = Self::resolved_local(receiver)
                {
                    self.facts
                        .raw_only_uses
                        .entry((self.fn_did, hir_id))
                        .or_insert((method, expr.span));
                }
            }
            // (2) in-crate call
            ExprKind::Call(callee, _) => {
                if let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind
                    && let Res::Def(_, def_id) = path.res
                    && let Some(local_did) = def_id.as_local()
                    && self.locals.contains(&local_did)
                {
                    self.facts
                        .callers
                        .entry(local_did)
                        .or_default()
                        .push((self.fn_did, expr.span));
                }
            }
            // (3) a cast of a local to a raw pointer or integer keeps it raw
            ExprKind::Cast(inner, _) => {
                if let Some(hir_id) = Self::resolved_local(inner) {
                    self.facts
                        .raw_only_uses
                        .entry((self.fn_did, hir_id))
                        .or_insert(("as-cast".to_owned(), expr.span));
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

impl EmitabilityFacts {
    /// Render a span as `file:line:col` so a degradation record can leave the
    /// compiler session. Sites are for humans and for counters, not for lookup.
    pub(crate) fn site(tcx: TyCtxt<'_>, span: Span) -> String {
        tcx.sess.source_map().span_to_diagnostic_string(span)
    }
}
