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
    /// `callee -> reference spans`. Non-empty means a signature change would
    /// break an unadapted USE — not only a call.
    ///
    /// **F1:** this was `ExprKind::Call` only, which missed the C2Rust
    /// callback-table shape (`descent as unsafe extern "C" fn(..)`): the
    /// function is never *called* directly, so its signature was rewritten
    /// while a fn-item cast still referred to the old type, and the crate died
    /// at the anonymous whole-crate gate — the exact class A1 exists to retire.
    /// Any path reference to a local fn now counts, which subsumes direct
    /// calls, address-taking, and fn-pointer casts uniformly.
    pub referenced: FxHashMap<LocalDefId, Vec<Span>>,
    /// `(fn, param HirId) -> every raw-only use, in HIR walk order`.
    ///
    /// **A `Vec`, not a first-wins entry, since S3.2′-2.** Attribution still
    /// takes `.first()` — the reported op and site are unchanged, byte for byte.
    /// What the vector adds is the question the slice arm has to ask and a
    /// first-wins map cannot answer: *are ALL of this subject's raw-only uses
    /// arithmetic?*
    ///
    /// The hazard is concrete. A subject carrying both `offset` and `is_null`
    /// records whichever the walk met first. If that is `offset`, a first-wins
    /// reading says "arithmetic, emit a slice" — and `p.is_null()` on `&[T]`
    /// does not compile. The slice arm needs the whole set or it is unsound.
    pub raw_only_uses: FxHashMap<(LocalDefId, HirId), Vec<(String, Span)>>,
    /// **F5:** `(fn, param HirId) -> comparison span`.
    ///
    /// A pointer comparison is a blocking precondition in BOTH directions, and
    /// the second is the dangerous one: `p > limit` on two raw pointers
    /// compares ADDRESSES, while the same expression on two references
    /// compares POINTEES. That version type-checks, passes the gate, and
    /// silently inverts a bounds check — so it must be refused at decision
    /// time, not discovered by a behavioral test that does not exist yet.
    pub ptr_comparisons: FxHashMap<(LocalDefId, HirId), Span>,
}

/// Gather A1 facts for the whole crate in one HIR pass per function body.
pub(crate) fn collect(tcx: TyCtxt<'_>, functions: &[LocalDefId]) -> EmitabilityFacts {
    let mut facts = EmitabilityFacts::default();
    let local: Vec<LocalDefId> = functions.to_vec();
    // EVERY body in the crate, not only the functions under consideration:
    // a `static` initializer holding a callback table references functions
    // (F1) and would otherwise never be visited at all.
    for owner in tcx.hir_body_owners() {
        let body = tcx.hir_body_owned_by(owner);
        let mut visitor = BodyFacts {
            fn_did: owner,
            locals: &local,
            facts: &mut facts,
        };
        visitor.visit_body(body);
    }
    facts
}

/// Note the absent `tcx`: this visitor works entirely on HIR nodes and
/// resolutions. It *did* carry a `TyCtxt` that nothing ever read — dead weight
/// that the module-wide `allow(dead_code)` hid, and that the lint reported the
/// moment the blanket came off.
struct BodyFacts<'a> {
    fn_did: LocalDefId,
    locals: &'a [LocalDefId],
    facts: &'a mut EmitabilityFacts,
}

impl BodyFacts<'_> {
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

impl<'tcx> Visitor<'tcx> for BodyFacts<'_> {
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
                        .or_default()
                        .push((method, expr.span));
                }
            }
            // (2) ANY reference to a local fn — call, address-taken, or the
            // operand of a fn-pointer cast. F1: matching only `Call` missed the
            // callback-table shape entirely.
            ExprKind::Path(QPath::Resolved(_, path)) => {
                if let Res::Def(rustc_hir::def::DefKind::Fn, def_id) = path.res
                    && let Some(local_did) = def_id.as_local()
                    && self.locals.contains(&local_did)
                {
                    self.facts
                        .referenced
                        .entry(local_did)
                        .or_default()
                        .push(expr.span);
                }
            }
            // (4) pointer comparison — F5.
            ExprKind::Binary(op, lhs, rhs) => {
                use rustc_hir::BinOpKind::*;
                if matches!(op.node, Lt | Le | Gt | Ge | Eq | Ne) {
                    for side in [lhs, rhs] {
                        if let Some(hir_id) = Self::resolved_local(side) {
                            self.facts
                                .ptr_comparisons
                                .entry((self.fn_did, hir_id))
                                .or_insert(expr.span);
                        }
                    }
                }
            }
            // (3) a cast of a local to a raw pointer or integer keeps it raw
            ExprKind::Cast(inner, _) => {
                if let Some(hir_id) = Self::resolved_local(inner) {
                    self.facts
                        .raw_only_uses
                        .entry((self.fn_did, hir_id))
                        .or_default()
                        .push(("as-cast".to_owned(), expr.span));
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

/// The arithmetic ops a borrowed-slice form can absorb.
///
/// A strict subset of [`RAW_ONLY_METHODS`], and deliberately narrower than the
/// §1(g) op table: only the two the addressable market actually carries. Adding
/// a member is adding a rewrite rule, so the list grows from evidence like its
/// parent does.
pub(crate) const SLICE_ARITHMETIC_OPS: &[&str] = &["offset", "offset_from"];

/// One rewritable use of a slice subject: the span to replace, and the text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct UseEdit {
    pub span: Span,
    pub replacement: String,
}

/// What a subject's uses permit.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SliceUses {
    pub rewrites: Vec<UseEdit>,
    /// A use that is **not** `*p.offset(e)`.
    ///
    /// Any such use blocks the whole subject. `&[T]` changes the type at every
    /// occurrence, so a rewrite that fixes the uses it recognizes and leaves the
    /// rest is not a partial win — it is an ill-typed crate.
    pub unsupported: Option<Span>,
}

/// Collect, per binding, the `*p.offset(e)` uses and whether anything else uses
/// the binding at all.
///
/// **Total over uses, not over recognized uses** — the distinction is the whole
/// soundness argument. The walk visits every path expression resolving to a
/// local and classifies it; a use that does not match the rewritable shape sets
/// `unsupported` rather than being skipped.
pub(crate) fn collect_slice_uses(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    name_of: &FxHashMap<(LocalDefId, HirId), String>,
) -> FxHashMap<(LocalDefId, HirId), SliceUses> {
    struct V<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        fn_did: LocalDefId,
        out: &'a mut FxHashMap<(LocalDefId, HirId), SliceUses>,
        name_of: &'a FxHashMap<(LocalDefId, HirId), String>,
    }
    impl<'tcx> Visitor<'tcx> for V<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && let Res::Local(hir_id) = path.res
            {
                let key = (self.fn_did, hir_id);
                // Classify BEFORE taking the entry: `classify` reads `self`, and
                // holding the map entry across it would be a borrow conflict.
                let classified = self.classify(expr, key);
                let entry = self.out.entry(key).or_default();
                match classified {
                    Some(edit) => entry.rewrites.push(edit),
                    None => {
                        if entry.unsupported.is_none() {
                            entry.unsupported = Some(expr.span);
                        }
                    }
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    impl V<'_, '_> {
        /// `*p.offset(e)` — and nothing else — yields an edit.
        fn classify(
            &self,
            use_expr: &Expr<'_>,
            key: (LocalDefId, HirId),
        ) -> Option<UseEdit> {
            let name = self.name_of.get(&key)?;
            // parent must be `p.offset(e)` with THIS expression as receiver
            let parent = self.tcx.parent_hir_node(use_expr.hir_id);
            let rustc_hir::Node::Expr(call) = parent else {
                return None;
            };
            let ExprKind::MethodCall(seg, receiver, args, _) = &call.kind else {
                return None;
            };
            if receiver.hir_id != use_expr.hir_id
                || !SLICE_ARITHMETIC_OPS.contains(&seg.ident.name.to_string().as_str())
            {
                return None;
            }
            let [arg] = args else { return None };
            // grandparent must be the deref
            let rustc_hir::Node::Expr(deref) = self.tcx.parent_hir_node(call.hir_id) else {
                return None;
            };
            if !matches!(deref.kind, ExprKind::Unary(rustc_hir::UnOp::Deref, _)) {
                return None;
            }
            let index = self.index_text(arg)?;
            Some(UseEdit {
                span: deref.span,
                replacement: format!("{name}[{index}]"),
            })
        }

        /// The index expression's source text, as a `usize`.
        ///
        /// C2Rust writes `p.offset(i as isize)`; the `as isize` exists only to
        /// satisfy `offset`, so stripping it recovers the author's index rather
        /// than inventing a conversion. Anything else is parenthesised and cast,
        /// which is always well-typed but never pretty — and never silent.
        fn index_text(&self, arg: &Expr<'_>) -> Option<String> {
            let sm = self.tcx.sess.source_map();
            if let ExprKind::Cast(inner, ty) = &arg.kind
                && let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, p)) = &ty.kind
                && p.segments.last().is_some_and(|s| s.ident.name.as_str() == "isize")
            {
                return sm.span_to_snippet(inner.span).ok();
            }
            sm.span_to_snippet(arg.span).ok().map(|t| format!("({t}) as usize"))
        }
    }

    let mut out = FxHashMap::default();
    for &fn_did in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
            continue;
        };
        let mut v = V { tcx, fn_did, out: &mut out, name_of };
        v.visit_body(tcx.hir_body(body_id));
    }
    out
}
