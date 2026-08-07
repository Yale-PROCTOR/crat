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

/// The index expression's source text, **typed as a `usize`**.
///
/// C2Rust writes `p.offset(i as isize)`; the `as isize` exists only to satisfy
/// `offset`, so stripping it recovers the author's index rather than inventing
/// a conversion.
///
/// # Stripping is not enough, and the corpus said so
///
/// The real idiom is a **double** cast — `p.offset(1 as libc::c_int as isize)` —
/// so stripping the outer cast leaves a `c_int`, and a slice indexed by `i32` is
/// `error[E0277]`. Measured: all 14 decided slices reverted, taking two sibling
/// `Ref` emissions down with them, because revert granularity is per function.
///
/// So the stripped expression's TYPE decides. Already `usize` — the shape
/// g11/g12 pin — renders bare, which is what keeps the ratified golden text
/// untouched rather than bending spec around a defect. Anything else is
/// parenthesised and cast: parenthesised because `i + 1 as usize` parses as
/// `i + (1 as usize)`.
///
/// **S3.2′-3: lifted out of the slice collector unchanged**, so the optional
/// slice twin renders indices by the same rule rather than by a second copy of
/// it. One canonicalizer, the standing rule.
fn index_text(tcx: TyCtxt<'_>, arg: &Expr<'_>) -> Option<String> {
    /// Is this expression already a `usize`?
    ///
    /// Asked of the type checker rather than of the syntax: `i`, `n as usize`
    /// and a `usize`-returning call are all bare-renderable and no syntactic
    /// test recognises the three.
    fn is_usize(tcx: TyCtxt<'_>, expr: &Expr<'_>) -> bool {
        let owner = expr.hir_id.owner.def_id;
        tcx.typeck(owner)
            .expr_ty_adjusted_opt(expr)
            .is_some_and(|t| {
                matches!(
                    t.kind(),
                    rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::Usize)
                )
            })
    }

    let sm = tcx.sess.source_map();
    if let ExprKind::Cast(inner, ty) = &arg.kind
        && let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, p)) = &ty.kind
        && p.segments.last().is_some_and(|s| s.ident.name.as_str() == "isize")
    {
        let text = sm.span_to_snippet(inner.span).ok()?;
        return Some(if is_usize(tcx, inner) {
            text
        } else {
            format!("({text}) as usize")
        });
    }
    let text = sm.span_to_snippet(arg.span).ok()?;
    Some(if is_usize(tcx, arg) {
        text
    } else {
        format!("({text}) as usize")
    })
}

/// How many of a binding's uses are **not** the null test.
///
/// The multiplicity half of the idiom rule, needed *before* the collector runs
/// because it decides which accessor the collector substitutes. Counting the
/// same walk twice is the price of that ordering, and it is a cheap HIR pass —
/// the alternative is a collector that rewrites its own output after the fact.
pub(crate) fn non_test_use_count(tcx: TyCtxt<'_>, fn_did: LocalDefId, binding: HirId) -> usize {
    struct V<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        binding: HirId,
        count: &'a mut usize,
    }
    impl<'tcx> Visitor<'tcx> for V<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && let Res::Local(hir_id) = path.res
                && hir_id == self.binding
            {
                let is_null_test = matches!(
                    self.tcx.parent_hir_node(expr.hir_id),
                    rustc_hir::Node::Expr(p)
                        if matches!(
                            &p.kind,
                            ExprKind::MethodCall(seg, receiver, _, _)
                                if receiver.hir_id == expr.hir_id
                                    && seg.ident.name.as_str() == "is_null"
                        )
                );
                if !is_null_test {
                    *self.count += 1;
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
        return 0;
    };
    let mut count = 0;
    let mut v = V {
        tcx,
        binding,
        count: &mut count,
    };
    v.visit_body(tcx.hir_body(body_id));
    count
}

/// The two spellings one optional subject needs, because `unwrap()` and
/// `as_mut()` unwrap to different depths.
///
/// `Option<&T>::unwrap()` yields `&T` — one deref to the pointee.
/// `Option<&mut T>::as_mut().unwrap()` yields `&mut &mut T` — two. So the
/// dereferencing position needs an extra `*` in the second case, while the
/// indexing position needs none in either (indexing auto-derefs). Carrying both
/// spellings is what keeps that asymmetry out of the call sites.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Accessor {
    /// Substituted for the binding at a `*p` position.
    pub deref: String,
    /// The base, for `…[i]`.
    pub index: String,
}

/// **S3.2′-3 — what an OPTIONAL subject's uses permit.**
///
/// Same all-or-nothing contract as [`SliceUses`], and for a stronger reason:
/// `Option<&T>` changes the type at *every* occurrence, including the plain
/// `*p` a reference form left alone. There is no partial optional rewrite.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct OptUses {
    pub rewrites: Vec<UseEdit>,
    /// A use with no image under the wrapper.
    pub unsupported: Option<Span>,
    /// Uses that are not the null test — the multiplicity half of the idiom
    /// rule (micro-plan §9c).
    pub non_test_uses: usize,
}

/// Collect, per binding, the uses an **optional** form must rewrite.
///
/// # The two ratified idioms, and why the choice is not stylistic
///
/// - `Option<&T>` is `Copy`, so `unwrap()` may be spelled at every use.
/// - `Option<&mut T>` is **not**. `unwrap()` moves it — fine exactly once, which
///   is g02's ratified text, and ill-typed twice. More than one use therefore
///   takes `as_mut()`, which is g05's.
///
/// # One substitution, three positions
///
/// The edit replaces the **binding's own path expression**, not the enclosing
/// expression, so a single replacement text serves every dereferencing position:
///
/// | source | replacement of `p` | result |
/// |---|---|---|
/// | `*p` | `p.unwrap()` | `*p.unwrap()` |
/// | `*p = e` | `p.unwrap()` | `*p.unwrap() = e` |
/// | `(*p).f` | `p.unwrap()` | `(*p.unwrap()).f` |
/// | `*p` (mut, multi-use) | `*p.as_mut().unwrap()` | `**p.as_mut().unwrap()` |
///
/// The null test is the one exception: it replaces the whole call, because
/// `is_null` and `is_none` are different names — and `!p.is_null()` collapses to
/// `p.is_some()`, g05's spelling, rather than the correct-but-graceless
/// `!p.is_none()`.
pub(crate) fn collect_opt_uses(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    name_of: &FxHashMap<(LocalDefId, HirId), String>,
    accessor_of: &FxHashMap<(LocalDefId, HirId), Accessor>,
    fat: &rustc_hash::FxHashSet<(LocalDefId, HirId)>,
) -> FxHashMap<(LocalDefId, HirId), OptUses> {
    struct V<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        fn_did: LocalDefId,
        out: &'a mut FxHashMap<(LocalDefId, HirId), OptUses>,
        name_of: &'a FxHashMap<(LocalDefId, HirId), String>,
        accessor_of: &'a FxHashMap<(LocalDefId, HirId), Accessor>,
        fat: &'a rustc_hash::FxHashSet<(LocalDefId, HirId)>,
    }
    impl<'tcx> Visitor<'tcx> for V<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && let Res::Local(hir_id) = path.res
                && self.name_of.contains_key(&(self.fn_did, hir_id))
            {
                let key = (self.fn_did, hir_id);
                let classified = self.classify(expr, key);
                let entry = self.out.entry(key).or_default();
                match classified {
                    Some((edit, is_non_test)) => {
                        entry.rewrites.push(edit);
                        entry.non_test_uses += usize::from(is_non_test);
                    }
                    None => {
                        entry.non_test_uses += 1;
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
        /// `Some((edit, is_a_non_test_use))`, or `None` for a use with no image.
        fn classify(
            &self,
            use_expr: &Expr<'_>,
            key: (LocalDefId, HirId),
        ) -> Option<(UseEdit, bool)> {
            let name = self.name_of.get(&key)?;
            let accessor = self.accessor_of.get(&key)?;
            let rustc_hir::Node::Expr(p) = self.tcx.parent_hir_node(use_expr.hir_id) else {
                return None;
            };
            match &p.kind {
                ExprKind::MethodCall(seg, receiver, _, _)
                    if receiver.hir_id == use_expr.hir_id
                        && seg.ident.name.as_str() == "is_null" =>
                {
                    if let rustc_hir::Node::Expr(not) = self.tcx.parent_hir_node(p.hir_id)
                        && matches!(not.kind, ExprKind::Unary(rustc_hir::UnOp::Not, _))
                    {
                        return Some((
                            UseEdit {
                                span: not.span,
                                replacement: format!("{name}.is_some()"),
                            },
                            false,
                        ));
                    }
                    Some((
                        UseEdit {
                            span: p.span,
                            replacement: format!("{name}.is_none()"),
                        },
                        false,
                    ))
                }
                ExprKind::Unary(rustc_hir::UnOp::Deref, _) => Some((
                    UseEdit {
                        span: use_expr.span,
                        replacement: accessor.deref.clone(),
                    },
                    true,
                )),
                // **The fat twin's arithmetic position.** `*p.offset(e)` on an
                // `Option<&[T]>` is `p.unwrap()[e]` — the -2 rewrite with the
                // wrapper's accessor in front of it, which is why the index is
                // rendered by the SAME `index_text` and not a second copy.
                //
                // Admitted only for subjects fatness licensed: on a thin
                // optional this position has no image, and falling through to
                // `None` is the correct refusal.
                ExprKind::MethodCall(seg, receiver, args, _)
                    if receiver.hir_id == use_expr.hir_id
                        && self.fat.contains(&key)
                        && SLICE_ARITHMETIC_OPS.contains(&seg.ident.name.to_string().as_str()) =>
                {
                    let [arg] = args else { return None };
                    let rustc_hir::Node::Expr(deref) = self.tcx.parent_hir_node(p.hir_id) else {
                        return None;
                    };
                    if !matches!(deref.kind, ExprKind::Unary(rustc_hir::UnOp::Deref, _)) {
                        return None;
                    }
                    // -2's accept-set restoration carries over verbatim: a
                    // BORROW of the deref is a third position, and it is not in
                    // scope here either.
                    if matches!(
                        self.tcx.parent_hir_node(deref.hir_id),
                        rustc_hir::Node::Expr(e) if matches!(e.kind, ExprKind::AddrOf(..))
                    ) {
                        return None;
                    }
                    let index = index_text(self.tcx, arg)?;
                    Some((
                        UseEdit {
                            span: deref.span,
                            replacement: format!("{}[{index}]", accessor.index),
                        },
                        true,
                    ))
                }
                _ => None,
            }
        }
    }

    let mut out = FxHashMap::default();
    for &fn_did in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
            continue;
        };
        let mut v = V {
            tcx,
            fn_did,
            out: &mut out,
            name_of,
            accessor_of,
            fat,
        };
        v.visit_body(tcx.hir_body(body_id));
    }
    out
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
            // **SCOPE RESTORATION.** Amendment 1 authorises exactly two
            // positions — the deref READ and the deref WRITE. A BORROW of the
            // deref is a third, and this classifier accepted it because it
            // tested the deref's shape without testing its context.
            //
            // Measured on the corpus: `lodepng_chunk_data` reads
            // `return &mut *chunk.offset(8) as *mut c_uchar`, and rewriting it
            // gave `error[E0596]: cannot borrow chunk[_] as mutable, as it is
            // behind a & reference`.
            //
            // **Scope is whatever the classifier accepts.** The approved scope
            // and the accept-set are the same object, so the accept-set is
            // witnessed against the scope — positive controls for both
            // authorised positions, a negative control for each known
            // neighbour (borrow-of-deref, rebind, self-advance).
            if matches!(
                self.tcx.parent_hir_node(deref.hir_id),
                rustc_hir::Node::Expr(e) if matches!(e.kind, ExprKind::AddrOf(..))
            ) {
                return None;
            }
            let index = self.index_text(arg)?;
            Some(UseEdit {
                span: deref.span,
                replacement: format!("{name}[{index}]"),
            })
        }

        /// The index expression's source text, **typed as a `usize`**.
        ///
        /// C2Rust writes `p.offset(i as isize)`; the `as isize` exists only to
        /// satisfy `offset`, so stripping it recovers the author's index rather
        /// than inventing a conversion.
        ///
        /// # Stripping is not enough, and the corpus said so
        ///
        /// The real idiom is a **double** cast — `p.offset(1 as libc::c_int as
        /// isize)` — so stripping the outer cast leaves a `c_int`, and a slice
        /// indexed by `i32` is `error[E0277]`. Measured: all 14 decided slices
        /// reverted, taking two sibling `Ref` emissions down with them, because
        /// revert granularity is per function.
        ///
        /// So the stripped expression's TYPE decides. Already `usize` — the
        /// shape g11/g12 pin — renders bare, which is what keeps the ratified
        /// golden text untouched rather than bending spec around a defect.
        /// Anything else is parenthesised and cast: parenthesised because
        /// `i + 1 as usize` parses as `i + (1 as usize)`.
        fn index_text(&self, arg: &Expr<'_>) -> Option<String> {
            index_text(self.tcx, arg)
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
