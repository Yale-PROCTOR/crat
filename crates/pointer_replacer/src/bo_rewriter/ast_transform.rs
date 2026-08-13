//! **Phase 3 — the edit vocabulary as NODE TRANSFORMS.**
//!
//! Arm 1 is declaration type replacement: `*mut T` → `&mut T`, `*const T` →
//! `&T`, on the subjects the decision layer settled `Decision::Ref`.
//!
//! # What changes, and what conspicuously does not
//!
//! The decision layer is untouched — this module consumes a `DecisionTable` and
//! decides nothing. What changes is that an edit stops being
//! `(lo, hi, replacement: String)` and becomes a mutation of a `TyKind`.
//!
//! **The pointee is not copied, it is KEPT.** The span layer had to reproduce
//! the pointee's source text (`plan` copied `pointee_span`'s snippet); here the
//! pointee is a subtree that moves across unchanged. Whole classes of question —
//! is the pointee text renderable, does it contain a macro, is its span
//! contained in the declaration's — stop existing rather than being answered.
//!
//! # Parity mode
//!
//! Capability unlocks are OFF. This arm reproduces what the span layer produces
//! for the same subjects and nothing more; the differential against the pinned
//! oracle (`b4294374`, digest `4ed9d2a6…`) is what says so.

use rustc_ast::{
    AngleBracketedArg, AngleBracketedArgs, DUMMY_NODE_ID, GenericArg, GenericArgs, MutTy,
    Mutability, NodeId, Path, PathSegment, Ty, TyKind, mut_visit::MutVisitor, ptr::P,
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::HirId;
use rustc_span::{DUMMY_SP, Ident, Symbol, def_id::LocalDefId};
use thin_vec::ThinVec;

/// **ARM 2 — which declared form a decision asks for.**
///
/// The three emitting dispositions, carried as a shape rather than as the
/// decision itself: this module consumes verdicts and decides nothing, so the
/// enum names *what to build*, not *why*.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum DeclForm {
    /// `&T` / `&mut T` — arm 1.
    Ref,
    /// `&[T]` / `&mut [T]`.
    Slice,
    /// `Option<&T>` and its three twins; `slice` selects the fat one.
    Opt { slice: bool },
}

/// Wrap `inner` in `Option<…>`, **structurally**.
///
/// Built as a path node rather than parsed from `format!("Option<{…}>")` for
/// the reason §3c gives for declining `ty!` in arm 1: a text round-trip would
/// have to re-render the pointee, and the pointee is a subtree that must move
/// across untouched. Here it stays a subtree through the wrap as well.
///
/// Every span is [`DUMMY_SP`] and every id [`DUMMY_NODE_ID`] — the
/// synthetic-span invariant. Nothing keys on a constructed node's span; the
/// differential keys on the *declaration's* span, which is the original's and
/// is not replaced.
fn option_of(inner: P<Ty>) -> TyKind {
    let args = AngleBracketedArgs {
        span: DUMMY_SP,
        args: ThinVec::from_iter([AngleBracketedArg::Arg(GenericArg::Type(inner))]),
    };
    let segment = PathSegment {
        ident: Ident::new(Symbol::intern("Option"), DUMMY_SP),
        id: DUMMY_NODE_ID,
        args: Some(P(GenericArgs::AngleBracketed(args))),
    };
    TyKind::Path(
        None,
        Path {
            span: DUMMY_SP,
            segments: ThinVec::from_iter([segment]),
            tokens: None,
        },
    )
}

/// Build the declared type for `form`, **keeping `pointee` as a subtree**.
///
/// The eight `(form, mutable)` combinations render exactly the four spellings
/// [`super::plan::plan`] writes as text, optionally wrapped in `Option<…>`.
/// That correspondence is the arm's whole parity obligation at the declaration
/// position, and it is pinned by `declared_forms_render_the_span_layers_text`
/// so a corpus diff is attributable to the walk rather than to the renderer.
pub(crate) fn decl_ty_kind(form: DeclForm, mutable: bool, pointee: P<Ty>) -> TyKind {
    let mutbl = if mutable {
        Mutability::Mut
    } else {
        Mutability::Not
    };
    let referent = match form {
        DeclForm::Ref | DeclForm::Opt { slice: false } => pointee,
        DeclForm::Slice | DeclForm::Opt { slice: true } => P(Ty {
            id: DUMMY_NODE_ID,
            kind: TyKind::Slice(pointee),
            span: DUMMY_SP,
            tokens: None,
        }),
    };
    let reference = TyKind::Ref(
        None,
        MutTy {
            ty: referent,
            mutbl,
        },
    );
    match form {
        DeclForm::Ref | DeclForm::Slice => reference,
        DeclForm::Opt { .. } => option_of(P(Ty {
            id: DUMMY_NODE_ID,
            kind: reference,
            span: DUMMY_SP,
            tokens: None,
        })),
    }
}

/// One refused claim, naming **both** parties.
///
/// Requirement added at the arm-2 review (2026-08-13). A refusal row that named
/// only the node would hand a STOP diagnosis half the story: `refused = 1 @
/// node 4713` says a collision happened and not who collided, and the two
/// transforms live in different passes over a 900-line module. Both sides are
/// recorded so the diagnosis holds both parties.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Refusal {
    pub node: NodeId,
    /// The transform that already owns the node — its claim STANDS.
    pub holder: &'static str,
    /// The transform refused. See [`Composition`]: this one, not both.
    pub challenger: &'static str,
}

/// **THE FAIL-CLOSED COMPOSITION GUARD.**
///
/// Built beside the FIRST arm by ruling (2026-08-12, item 5), not deferred to
/// the unlock that eventually relaxes it, and **in force in parity mode**.
///
/// # What it does and does not replace
///
/// The `seam-site-overlap` gate's *byte-range conflict* dissolves with the
/// representation — two node transforms at one call site compose, where two
/// byte ranges could not. **The soundness hazard it guarded does not dissolve.**
/// What that gate stands between is the inversion finding: `two_mut(&mut *p,
/// &mut *p)` through a raw base compiles with **zero diagnostics** where the
/// same shape on a real local is `E0499`. The compiler is blind exactly where
/// the reborrow family places its borrows, so refusing unreviewed composition
/// is the only thing between a composed transform and silent UB.
///
/// This guard is the STRUCTURAL half: two transforms may not claim one node.
/// The semantic half stays in the decision layer, where it already lives.
///
/// **Fail-closed:** a second claim on a node is REFUSED and counted. It is
/// never resolved by precedence, because a precedence rule is a decision, and
/// deciding here is what the phase separation forbids.
///
/// # What "refused" means exactly — CORRECTED at arm 2
///
/// This doc previously said a second claim refuses **both** transforms. It does
/// not, and cannot as built: the first claimant has already mutated its node by
/// the time the second arrives, so what the guard delivers is *the second is
/// refused and counted*, with the first standing. Through arm 1 the difference
/// was unobservable — one transform cannot conflict, so `refused` was a
/// uniformly-zero predicate and the claim was never exercised.
///
/// The distinction is recorded rather than repaired because a nonzero `refused`
/// is **pre-classified STOP** in parity mode: the corpus expectation is zero, and
/// a genuine both-refusal (rollback, or a claim pass separated from a transform
/// pass) is work that belongs to whichever unlock first makes composition
/// legal. What must not happen is prose promising a rollback the code does not
/// perform.
///
/// **The preserved invariant is NO SILENT PRECEDENCE** (ruling 2026-08-13). The
/// first claim standing is not a precedence *rule* — it is the order the walk
/// happened to run in, and the guard's job is to ensure that order is never
/// quietly load-bearing. Every refusal is a typed [`Refusal`] row naming both
/// parties and is STOP-class at parity, so a collision cannot be resolved by
/// walk order without a human seeing it.
#[derive(Default)]
pub(crate) struct Composition {
    claimed: FxHashMap<NodeId, &'static str>,
    /// Refusals, each naming the node and both claimants.
    pub refused: Vec<Refusal>,
}

impl Composition {
    /// `true` when this transform may proceed. `false` means another transform
    /// already owns the node, and THIS one is refused — see the struct doc for
    /// why that is not the same as refusing both.
    ///
    /// `claimant` is a stable label for the transform, not for the subject: it
    /// is what a STOP diagnosis reads to learn which two passes collided.
    pub(crate) fn claim(&mut self, node: NodeId, claimant: &'static str) -> bool {
        match self.claimed.get(&node) {
            None => {
                self.claimed.insert(node, claimant);
                true
            }
            Some(&holder) => {
                self.refused.push(Refusal {
                    node,
                    holder,
                    challenger: claimant,
                });
                false
            }
        }
    }

    /// Refusals whose CHALLENGER carries this label — the pass that was turned
    /// away. Derived from the labels rather than by subtracting one pass's
    /// tally from the guard's total, which would mis-attribute the moment a
    /// third transform lands.
    pub(crate) fn refused_by(&self, claimant: &str) -> usize {
        self.refused
            .iter()
            .filter(|r| r.challenger == claimant)
            .count()
    }
}

/// What the declaration pass rewrote, so the differential has a population to
/// compare.
///
/// The three form counters are kept **apart** rather than summed: `rewritten`
/// is arm 1's pinned 780 and must stay readable as that number after arm 2
/// lands. A single total would have made the must-not-move list uncheckable.
#[derive(Default)]
pub(crate) struct RefDeclStats {
    /// Declarations rewritten `*mut T`/`*const T` → `&mut T`/`&T`. **Arm 1.**
    pub rewritten: usize,
    /// **Arm 2** — declarations rewritten to `&[T]` / `&mut [T]`.
    pub slice_rewritten: usize,
    /// **Arm 2** — declarations rewritten to an `Option<…>` form.
    pub opt_rewritten: usize,
    /// Subjects the table settled `Ref` whose declaration was NOT a syntactic
    /// pointer in the AST. Counted, never silently skipped: a decided subject
    /// the transform cannot reach is a ledger movement.
    pub not_a_pointer_decl: usize,
    /// Refused by the composition guard.
    pub refused: usize,
    /// `(byte offset of the declaration's type, rendered type)` per rewrite —
    /// the text differential's left-hand side. Keyed by offset because that is
    /// what the span layer's `Edit` is keyed by, so the join needs no name
    /// matching and cannot silently pair the wrong two things.
    pub rendered: Vec<(u32, String)>,
    /// The same, for **arm 2's** declaration renders. Split from
    /// [`Self::rendered`] so arm 1's pinned differential stays computable over
    /// exactly the population it was pinned on.
    pub rendered_arm2: Vec<(u32, String)>,
}

/// Arm 1's visitor: rewrite the declared type of every `Decision::Ref` subject.
pub(crate) struct RefDeclVisitor<'a> {
    /// AST `NodeId` → HIR `HirId`, the forward direction a tree walk wants.
    ///
    /// The `UnordMap` is used DIRECTLY rather than copied into an `FxHashMap`:
    /// a lookup is order-free, `get` is all a tree walk needs, and converting
    /// would mean iterating a container that hides iteration on purpose.
    pub local_map: &'a rustc_ast::node_id::NodeMap<HirId>,
    /// `(fn_did, hir_id)` → which form this subject's declaration becomes, and
    /// whether it is mutable.
    pub decisions: &'a FxHashMap<(LocalDefId, HirId), (DeclForm, bool)>,
    /// AST `NodeId` → `LocalDefId`, used to set `current_fn` at each item.
    pub global_map: &'a rustc_ast::node_id::NodeMap<LocalDefId>,
    /// The function currently being walked, from the global map.
    pub current_fn: Option<LocalDefId>,
    pub guard: &'a mut Composition,
    pub stats: RefDeclStats,
}

impl RefDeclVisitor<'_> {
    /// Rewrite one declaration's type node, if its binding is a `Ref` subject.
    ///
    /// `binding` is the PATTERN's node — that is what the map keys on, because
    /// `map_pat_to_pat` sends an AST `PatKind::Ident` to `hir::PatKind::Binding`
    /// and a subject's `hir_id` is its binding pattern's.
    fn rewrite_decl(&mut self, binding: NodeId, ty: &mut Ty) {
        let Some(fn_did) = self.current_fn else { return };
        let Some(hir_id) = self.local_map.get(&binding) else {
            return;
        };
        let Some(&(form, mutable)) = self.decisions.get(&(fn_did, *hir_id)) else {
            return;
        };
        // **The shape check runs BEFORE the claim** (arm-2 review). Claiming
        // first meant a declaration this pass cannot transform still took
        // OWNERSHIP of the node, so a later transform that legitimately wanted
        // it would be refused on behalf of work that never happened. Ownership
        // now follows the transform rather than the attempt.
        if !matches!(ty.kind, TyKind::Ptr(_)) {
            self.stats.not_a_pointer_decl += 1;
            return;
        }
        let claimant = match form {
            DeclForm::Ref => "decl:ref",
            DeclForm::Slice => "decl:slice",
            DeclForm::Opt { .. } => "decl:opt",
        };
        if !self.guard.claim(ty.id, claimant) {
            self.stats.refused += 1;
            return;
        }
        // The POINTEE MOVES ACROSS. No text is copied and none is re-rendered:
        // `mut_ty.ty` is the same subtree, reattached under a reference — and
        // under a `[…]` and an `Option<…>` too, for the forms that need them.
        let TyKind::Ptr(mut_ty) = &mut ty.kind else {
            unreachable!("shape checked immediately above")
        };
        let pointee = mut_ty.ty.clone();
        ty.kind = decl_ty_kind(form, mutable, pointee);
        let render = (ty.span.lo().0, rustc_ast_pretty::pprust::ty_to_string(ty));
        match form {
            DeclForm::Ref => {
                self.stats.rewritten += 1;
                self.stats.rendered.push(render);
            }
            DeclForm::Slice => {
                self.stats.slice_rewritten += 1;
                self.stats.rendered_arm2.push(render);
            }
            DeclForm::Opt { .. } => {
                self.stats.opt_rewritten += 1;
                self.stats.rendered_arm2.push(render);
            }
        }
    }
}

impl MutVisitor for RefDeclVisitor<'_> {
    fn visit_item(&mut self, item: &mut rustc_ast::Item) {
        // The enclosing function's `LocalDefId` is half the decision key.
        // SAVED AND RESTORED rather than overwritten: a nested item would
        // otherwise leave the outer function's params keyed to the inner one,
        // which is the same wrong-owner class the seam `owner_fn` defect was.
        let saved = self.current_fn;
        if matches!(item.kind, rustc_ast::ItemKind::Fn(_)) {
            self.current_fn = self.global_map.get(&item.id).copied();
        }
        rustc_ast::mut_visit::walk_item(self, item);
        self.current_fn = saved;
    }

    fn visit_param(&mut self, param: &mut rustc_ast::Param) {
        let binding = param.pat.id;
        self.rewrite_decl(binding, &mut param.ty);
        rustc_ast::mut_visit::walk_param(self, param);
    }

    fn visit_local(&mut self, local: &mut rustc_ast::Local) {
        let binding = local.pat.id;
        if let Some(ty) = local.ty.as_mut() {
            self.rewrite_decl(binding, ty);
        }
        rustc_ast::mut_visit::walk_local(self, local);
    }
}

/// **ARM 2's SECOND HALF — the use-site rewrites, as grafted nodes.**
///
/// `Slice` and `Opt` are the first dispositions that are not declaration-only:
/// `p.offset(i)` has no image on `&[T]` and `p.is_null()` none on an `Option`,
/// so the declaration edit alone yields an ill-typed crate. The decision layer
/// computes each rewrite as TEXT and hands it over as data; under the (c)
/// ruling that text reaches a file only through **parse → graft → print**.
#[derive(Default)]
pub(crate) struct UseGraftStats {
    pub grafted: usize,
    /// Replacements [`graft_expr`] refused. **A checked corpus expectation of
    /// zero**, per R7.4 — a failure here names a template the enumeration
    /// missed, with its text attached.
    pub parse_failed: usize,
    /// The offending templates, **capped** for the artifact. Never the count.
    pub parse_failures: Vec<String>,
    /// Use edits whose span matched no AST expression. Counted, because a use
    /// edit that evaporates leaves a converted declaration with a raw use under
    /// it — an ill-typed crate, not a partial rewrite.
    pub unmatched: usize,
    /// Refused by the composition guard.
    pub refused: usize,
    /// **One use key matched by MORE THAN ONE AST node.**
    ///
    /// The composition guard cannot see this: it keys on `NodeId`, and two
    /// distinct nodes sharing a span have distinct ids, so both claims are
    /// admitted and both graft. `unmatched` cannot see it either — `consumed`
    /// is a set, so the second match re-inserts and the key still reads as
    /// reached. Without this counter the shape is invisible to every existing
    /// instrument, which is why it is counted rather than argued about.
    ///
    /// Macro-expanded nodes are the realistic source: they carry the call
    /// site's range and differ only in `SyntaxContext`, which the `(lo, hi)`
    /// key drops. Corpus expectation is 0 and it is GATED.
    pub multi_matched: usize,
    /// `(offset, rendered text)` per graft — the text differential's left-hand
    /// side, keyed exactly as the declaration renders are.
    pub rendered: Vec<(u32, String)>,
}

/// Grafts each use rewrite onto the node whose span the decision layer named.
///
/// # Why the key is `(lo, hi)` and not `lo`
///
/// `p.offset(i)` and `p.offset(i) as usize` share a start offset, and
/// `*p.offset(i)` differs from `p.offset(i)` only at the start. Keying on one
/// endpoint would let the walk graft a replacement onto a node the decision
/// layer did not name — silently, and only on some shapes. The full span pair
/// makes the wrong pairing unrepresentable rather than merely unlikely.
pub(crate) struct UseGraftVisitor<'a> {
    uses: &'a FxHashMap<(u32, u32), String>,
    guard: &'a mut Composition,
    stats: UseGraftStats,
    /// Keys the walk actually reached, so `unmatched` is a **subtraction over
    /// identities** rather than a difference of two counts that could agree by
    /// coincidence.
    consumed: FxHashSet<(u32, u32)>,
}

impl<'a> UseGraftVisitor<'a> {
    pub(crate) fn new(uses: &'a FxHashMap<(u32, u32), String>, guard: &'a mut Composition) -> Self {
        Self {
            uses,
            guard,
            stats: UseGraftStats::default(),
            consumed: FxHashSet::default(),
        }
    }

    /// Close the walk, deriving `unmatched` from what was never reached.
    pub(crate) fn finish(mut self) -> UseGraftStats {
        self.stats.unmatched = self
            .uses
            .keys()
            .filter(|k| !self.consumed.contains(k))
            .count();
        self.stats
    }
}

impl MutVisitor for UseGraftVisitor<'_> {
    fn visit_expr(&mut self, e: &mut rustc_ast::Expr) {
        let key = (e.span.lo().0, e.span.hi().0);
        // A normalized (grafted) node can never be a target: `DUMMY_SP` is not
        // a position in this crate, and skipping it explicitly means the
        // erasure cannot manufacture a match of its own.
        if e.span.is_dummy() {
            rustc_ast::mut_visit::walk_expr(self, e);
            return;
        }
        if let Some(text) = self.uses.get(&key) {
            // `insert` returns false when the key was already reached — a
            // SECOND AST node carrying the same span. Counted here because
            // neither the guard (which keys on `NodeId`) nor `unmatched`
            // (a set membership) can observe it.
            if !self.consumed.insert(key) {
                self.stats.multi_matched += 1;
            }
            if !self.guard.claim(e.id, "use") {
                self.stats.refused += 1;
                return;
            }
            match graft_expr(text) {
                Ok(parsed) => {
                    // **Only `kind` is replaced.** The node keeps its own id and
                    // its own span, so the differential joins on the offset the
                    // decision layer named and the synthetic-span invariant
                    // holds: no consumer keys on a grafted subtree's spans,
                    // which come from the fragment's own `SourceMap`.
                    e.kind = parsed.kind;
                    self.stats.grafted += 1;
                    self.stats
                        .rendered
                        .push((key.0, rustc_ast_pretty::pprust::expr_to_string(e)));
                    // NOT walked: the children are the fragment's now. An edit
                    // that was nested under this one therefore never gets
                    // consumed and surfaces in `unmatched` — which is the
                    // reporting the decision layer's own nesting gate assumes.
                    return;
                }
                Err(offending) => {
                    self.stats.parse_failed += 1;
                    if self.stats.parse_failures.len() < 10 {
                        self.stats.parse_failures.push(offending);
                    }
                    // The node is LEFT INTACT and the walk continues into it.
                }
            }
        }
        rustc_ast::mut_visit::walk_expr(self, e);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **RED WITNESS for the composition guard** (ruling item 5): a
    /// deliberately conflicting pair, REFUSED.
    ///
    /// The guard is fail-closed, so the property under test is that a second
    /// claim on one node returns `false` and is counted — not that the first
    /// wins. A precedence rule would be a decision, and this phase decides
    /// nothing.
    ///
    /// *Mutation-tested:* making `claim` return `true` unconditionally — the
    /// shape a "just let it through" fix would take — fails both assertions.
    #[test]
    fn two_transforms_may_not_claim_one_node() {
        let mut g = Composition::default();
        let node = NodeId::from_u32(7);
        assert!(
            g.claim(node, "decl:slice"),
            "the first claim must be admitted"
        );
        assert!(
            !g.claim(node, "use"),
            "the SECOND claim on one node must be refused — this is the \
             structural half of the barrier the site-overlap gate provides, \
             and it does not lapse in parity mode"
        );
        assert_eq!(
            g.refused,
            vec![Refusal {
                node,
                holder: "decl:slice",
                challenger: "use",
            }],
            "the refusal must be COUNTED and must name BOTH parties (ruling \
             2026-08-13). A row carrying only the node hands a STOP diagnosis \
             half the story — that a collision happened, but not who collided, \
             across passes that live in different halves of the module"
        );
        assert_eq!(g.refused_by("use"), 1, "attributed to the CHALLENGER");
        assert_eq!(
            g.refused_by("decl:slice"),
            0,
            "the holder was not refused — its claim stands, which is exactly \
             the asymmetry the guard's doc was corrected to state"
        );
    }

    /// Distinct nodes compose freely — the guard refuses conflicts, not work.
    ///
    /// **Positive control**, and it is labelled as one: no deletion mutation
    /// fails it, since a guard that admitted everything would pass it too. Its
    /// job is to show the test above is not passing because `claim` rejects
    /// everything.
    #[test]
    fn distinct_nodes_do_not_conflict() {
        let mut g = Composition::default();
        assert!(g.claim(NodeId::from_u32(1), "decl:ref"));
        assert!(g.claim(NodeId::from_u32(2), "use"));
        assert!(g.refused.is_empty(), "distinct nodes must not be refused");
    }
}

/// **ARM 1's POPULATION DIFFERENTIAL.** Does the tree walk reach exactly the
/// subjects the decision layer settled `Ref`, and does the composition guard
/// stay silent?
///
/// Pre-stated (2026-08-13): `rewritten == 780` corpus-wide, `refused == 0`,
/// `not_a_pointer_decl == 0`.
///
/// **A non-zero `refused` is STOP-class, not a conservative win** (ruling
/// pre-classification, 2026-08-13). The span layer's nesting pass refused the
/// INNER edit and applied the outer; this guard refuses BOTH on a same-node
/// claim. Those semantics differ in principle, and this run is where we learn
/// whether they differ on this corpus. It may not be absorbed silently.
///
/// **Must run before any HIR/MIR query** — `expanded_ast` panics once the HIR
/// is built.
#[cfg(test)]
pub(crate) fn arm1_population(tcx: rustc_middle::ty::TyCtxt<'_>) -> Result<RefDeclStats, String> {
    transform_inner(tcx).map(|(decls, ..)| decls)
}

/// Both passes over ONE capture, sharing ONE composition guard.
///
/// # Why two passes and not one visitor
///
/// The use pass must **not** descend into a subtree it has just replaced — the
/// children are the parsed fragment's, and walking them would be walking the
/// wrong tree. A single visitor doing both jobs would skip any *declaration*
/// inside a rewritten expression as well. Two passes keep that skip local to
/// the pass that needs it.
///
/// **CORRECTED at the arm-2 review — the split does NOT make containment
/// safe.** This doc previously implied it did. Running declarations first means
/// a declaration inside a use-edit expression is transformed **and then thrown
/// away** when the enclosing expression is grafted — and the ledger has already
/// counted it as rewritten. That is a different failure from "skipped
/// silently" and it is not a better one. The honest position is that the two
/// passes fix the *walk*, not the *containment*, and containment is
/// **measured** rather than assumed: see `decl_render_inside_use_edit`, whose
/// corpus expectation is 0 and which is gated. Found by the correctness
/// persona at the arm-2 boundary.
///
/// The guard is shared precisely because the passes are separate: same-node
/// claims must be refused **across** them, not within each. It does **not**
/// catch containment — a contained declaration is a different node, legally
/// claimed.
#[cfg(test)]
fn transform_inner(
    tcx: rustc_middle::ty::TyCtxt<'_>,
) -> Result<(RefDeclStats, UseGraftStats, usize, usize, SeamUseSurface), String> {
    let captured = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut krate = ::utils::ast::expanded_ast(tcx);
        let map = ::utils::ast::make_ast_to_hir(&mut krate, tcx);
        (krate, map)
    }));
    let (mut krate, map) = captured.map_err(|_| "AST capture panicked".to_owned())?;

    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    let mut decisions: FxHashMap<(LocalDefId, HirId), (DeclForm, bool)> = FxHashMap::default();
    let mut uses: FxHashMap<(u32, u32), String> = FxHashMap::default();
    let mut use_key_collisions = 0usize;
    for (subject, decision) in &table.entries {
        // EXHAUSTIVE — the denylist rejects the bypass shape, and the arm's
        // population is defined by which disposition was reached.
        let (form, mutable, use_edits) = match decision {
            super::decision::Decision::Ref { mutable } => (DeclForm::Ref, *mutable, None),
            super::decision::Decision::Slice { mutable, uses } => {
                (DeclForm::Slice, *mutable, Some(uses))
            }
            super::decision::Decision::Opt {
                mutable,
                slice,
                uses,
            } => (DeclForm::Opt { slice: *slice }, *mutable, Some(uses)),
            super::decision::Decision::Degraded(_) => continue,
        };
        decisions.insert((subject.fn_did, subject.hir_id), (form, mutable));
        for u in use_edits.into_iter().flatten() {
            // A returned `Some` means two use edits carried the SAME span and
            // one was overwritten — the map would then hold fewer edits than
            // the table does, and every downstream count would agree with
            // itself while being short. `refuse_nested_use_edits` should make
            // this impossible (identical spans contain each other), but that is
            // an argument about another module, and this is a counter.
            if uses
                .insert((u.span.lo().0, u.span.hi().0), u.replacement.clone())
                .is_some()
            {
                use_key_collisions += 1;
            }
        }
    }

    let mut guard = Composition::default();
    let mut v = RefDeclVisitor {
        local_map: &map.local_map,
        decisions: &decisions,
        global_map: &map.global_map,
        current_fn: None,
        guard: &mut guard,
        stats: RefDeclStats::default(),
    };
    v.visit_crate(&mut krate);
    let decls = v.stats;

    let mut g = UseGraftVisitor::new(&uses, &mut guard);
    g.visit_crate(&mut krate);
    let grafts = g.finish();

    // **Each pass counts its OWN refusals**, at the site where it was turned
    // away. This used to recompute `decls.refused` here by summing
    // `refused_by` over a hand-written list of the three `decl:*` labels —
    // which had two faults, both found at the arm-2 review: it made the
    // visitor's own `stats.refused += 1` a DEAD write, and the list was not
    // exhaustive over `DeclForm`, so arm 3's claimant would have been dropped
    // from the sum in silence. Counting locally cannot drift, because there is
    // no second place to keep in step.
    //
    // `Composition::refused_by` survives for DIAGNOSIS — reading which pair
    // collided out of a nonzero gate — which is what the labels are for.

    // **ARM 3 TASK 0 — THE COLLISION SURFACE, measured before any transform.**
    //
    // A seam edit targets a CALL-ARGUMENT expression; a use graft targets a
    // use-site expression. Same syntactic category, so `seam` vs `use` is the
    // first pair that can claim one node — unlike `decl:*` vs `use`, which are
    // `Ty` vs `Expr` and structurally disjoint. The decision layer's
    // `seam-site-overlap` gate refuses seam-vs-seam BYTE overlap at one call;
    // it says nothing about seam-vs-use NODE IDENTITY, which is a different
    // relation. So this is measured rather than argued, before arm 3 exists.
    //
    // All four relations are reported separately: an exact coincidence is a
    // guaranteed same-node claim, while containment either way is the shape
    // that makes one transform discard the other's work (arm 2's containment
    // finding, now on the seam axis).
    let mut seam_same = 0usize;
    let mut seam_contains_use = 0usize;
    let mut use_contains_seam = 0usize;
    let mut seam_use_partial = 0usize;
    for seam in &table.seams.edits {
        let (slo, shi) = (seam.span.lo().0, seam.span.hi().0);
        for (ulo, uhi) in uses.keys() {
            let (ulo, uhi) = (*ulo, *uhi);
            if slo == ulo && shi == uhi {
                seam_same += 1;
            } else if slo <= ulo && uhi <= shi {
                seam_contains_use += 1;
            } else if ulo <= slo && shi <= uhi {
                use_contains_seam += 1;
            } else if slo < uhi && ulo < shi {
                seam_use_partial += 1;
            }
        }
    }

    // **CONTAINMENT, measured.** A declaration transformed inside an expression
    // that is later grafted is discarded, with the ledger still counting it as
    // rewritten — the hazard the two-pass split does NOT remove (see this
    // function's doc). Neither the guard nor `unmatched` can see it, so it is
    // counted directly: a declaration render whose offset falls strictly inside
    // some use-edit's range. Corpus expectation 0, and gated.
    let decl_inside_use = decls
        .rendered
        .iter()
        .chain(decls.rendered_arm2.iter())
        // HALF-OPEN, matching the range it models. This read `*off > *lo`,
        // which missed a declaration render starting exactly at a use edit's
        // first byte — the containment case most likely to occur, since a use
        // edit and a declaration inside it can share a start.
        .filter(|(off, _)| uses.keys().any(|(lo, hi)| *off >= *lo && *off < *hi))
        .count();
    Ok((
        decls,
        grafts,
        decl_inside_use,
        use_key_collisions,
        SeamUseSurface {
            same: seam_same,
            seam_contains_use,
            use_contains_seam,
            partial: seam_use_partial,
        },
    ))
}

/// **ARM 1's TEXT DIFFERENTIAL** — the rendered declaration vs the span layer's
/// own edit, at the same byte offset.
///
/// Per §3b: the unit is one EDIT, and this arm is comparable with no other arm
/// built, because each declaration replacement is independent of every other
/// edit in the file.
///
/// The right-hand side is the **real** plan — `emit_files` extracts it once
/// inside the session — never a re-derivation of what the replacement ought to
/// be. Comparing against a re-derivation would test this function against
/// itself.
#[derive(Default)]
pub(crate) struct TextDiff {
    pub compared: usize,
    pub equal: usize,
    /// Offsets where the AST layer rendered something the span layer did not
    /// write. Capped for the artifact; `differing` is the uncapped count.
    pub examples: Vec<String>,
    pub differing: usize,
    /// AST rewrites with no span-layer edit at that offset, and vice versa.
    pub unmatched_ast: usize,
    /// **Arm 1's pinned residue: 2,039.** Computed over arm 1's renders alone,
    /// so it stays the number it was pinned as after arm 2 lands.
    pub unmatched_span: usize,

    /// Arm 2's own differential: `Slice`/`Opt` declarations plus their use
    /// rewrites, against the same plan at the same offsets.
    pub arm2_compared: usize,
    pub arm2_equal: usize,
    pub arm2_differing: usize,
    pub arm2_unmatched_ast: usize,

    /// **THE CONSERVATION BOUND.** `KindDecision` offsets that NEITHER arm
    /// reached.
    ///
    /// `KindDecision` is constructed at exactly two sites in the shipping
    /// pipeline — the use edit and the declaration edit — and arms 3 and 4 carry
    /// `SeamAdapter` and (today) nothing. So this population is arms 1+2's in
    /// full, and its residue is expected **0**, not merely smaller.
    pub kd_unmatched_span: usize,
    /// Instrument integrity, both uncapped: the `KindDecision` edit count and
    /// the number of distinct offsets they occupy. **Equal unless two edits
    /// collide on one offset**, which would make the offset-keyed join lossy —
    /// silently, and in the direction that flatters the bound.
    pub kd_edits: usize,
    pub kd_offsets: usize,
    /// **ARM 3 TASK 0** — how the placed seam spans relate to the use-edit
    /// spans. NOT gated: this is the measurement that decides whether arm 3's
    /// `refused` can be nonzero, and gating a number before knowing it is the
    /// mistake this slice exists to avoid.
    pub seam_use_surface: SeamUseSurface,
    /// **Two use edits carrying one span**, one of which was overwritten when
    /// the map was built. Corpus expectation 0, GATED — the collision counter
    /// this join was missing while every other join in the file had one.
    pub use_key_collisions: usize,
    /// **A declaration render whose offset lies strictly inside a use edit's
    /// range** — the containment case the two-pass split does not remove.
    /// Corpus expectation 0, GATED. See `transform_inner`'s doc.
    pub decl_render_inside_use_edit: usize,
    /// ⚠ **JOINT ACROSS BOTH ARMS, despite sitting in the arm-2 block.**
    /// `arms_full` calls `compare_renders` three times against ONE `TextDiff`,
    /// so this field and `ws_equal`/`ws_real`/`pairs`/`examples` accumulate arm
    /// 1's comparison as well as arm 2's. That is deliberate for `ws_real`,
    /// which gates and should fail on a real difference *anywhere*; it is
    /// merely true of the rest. Arm 1 contributes 0 to all of them on the
    /// frozen corpus, which is why the numbers read as arm-2-only — a
    /// coincidence of the data, not a property of the code. Named by the
    /// correctness persona at the arm-2 review; recorded rather than renamed
    /// because the joint reading is the one the gate wants.
    ///
    /// Where arm 2's differences sit. The two positions have **different
    /// evidential weight** and summing them would hide that:
    ///
    /// - A **declaration** difference is two independent derivations
    ///   disagreeing — the AST side builds `&mut [T]` structurally from a
    ///   subtree, the span side writes `format!("&mut [{pointee}]")` over
    ///   verbatim source. Disagreement there is a real finding.
    /// - A **use** difference is not a second derivation at all. The AST render
    ///   is `print(parse(replacement))` and the span text *is* `replacement` —
    ///   the same string from the same `UseEdit`. So the only thing that can
    ///   differ is whether that string was already printer-canonical, and
    ///   "canonicalize both sides then compare" would be **tautologically
    ///   equal**. It is recorded here as a formatting delta, not offered as a
    ///   parity check.
    pub differing_decl: usize,
    pub differing_use: usize,
    /// Of the differing pairs, those equal once **all** whitespace is removed
    /// from both sides. Both sides are valid Rust produced from one parse, so
    /// whitespace-stripped equality is strong evidence of a pure formatting
    /// delta — and it is a check that can fail, unlike canonicalizing both
    /// sides through the same printer.
    pub ws_equal: usize,
    /// The residue: differing, and **still** differing with whitespace gone.
    /// This is the number that carries the parity claim. Pre-stated **0**.
    pub ws_real: usize,
    /// Every differing pair, uncapped, for the side artifact. The row's
    /// `examples` field is truncated at 120 chars by `report::sanitize`, which
    /// is why the evidence does not live there.
    pub pairs: Vec<(u32, &'static str, String, String)>,
    /// Files whose base offset could not be resolved from the source map.
    ///
    /// The join adds a file's own base back to each `Edit::lo`, which is
    /// file-relative. The lookup previously fell back to `0` **silently**,
    /// which would place every one of that file's edits at a wrong absolute
    /// offset and present as unmatched rather than as a broken instrument. The
    /// fallback is kept, so no pinned number moves; what is added is that it is
    /// now counted.
    pub base_unresolved: usize,
}

/// **The seam-vs-use collision surface** (arm 3, task 0).
///
/// Four relations, kept apart because they mean different things: `same` is a
/// guaranteed same-node claim and therefore a guaranteed `refused`; either
/// containment is the shape where one transform discards the other's work; a
/// `partial` overlap is representable in bytes but NOT in a tree, so it would
/// mean the two edits disagree about the syntax and is the most alarming of the
/// four.
#[derive(Default, Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SeamUseSurface {
    pub same: usize,
    pub seam_contains_use: usize,
    pub use_contains_seam: usize,
    pub partial: usize,
}

/// Join one arm's renders against the plan. Returns
/// `(compared, equal, differing, unmatched_ast)`.
#[cfg(test)]
fn compare_renders(
    renders: &[(u32, String)],
    by_offset: &FxHashMap<u32, String>,
    position: &'static str,
    d: &mut TextDiff,
) -> (usize, usize, usize, usize) {
    let strip = |s: &str| -> String { s.chars().filter(|c| !c.is_whitespace()).collect() };
    let (mut compared, mut equal, mut differing, mut unmatched) = (0, 0, 0, 0);
    for (off, rendered) in renders {
        match by_offset.get(off) {
            Some(span_text) => {
                compared += 1;
                if span_text == rendered {
                    equal += 1;
                } else {
                    differing += 1;
                    match position {
                        "decl" => d.differing_decl += 1,
                        _ => d.differing_use += 1,
                    }
                    if strip(span_text) == strip(rendered) {
                        d.ws_equal += 1;
                    } else {
                        d.ws_real += 1;
                    }
                    d.pairs
                        .push((*off, position, rendered.clone(), span_text.clone()));
                    if d.examples.len() < 10 {
                        d.examples.push(format!(
                            "@{off} {position} ast={rendered:?} span={span_text:?}"
                        ));
                    }
                }
            }
            None => unmatched += 1,
        }
    }
    (compared, equal, differing, unmatched)
}

/// **ONE ENTRY, because the AST may be captured ONCE.**
///
/// `expanded_ast` panics after the HIR is built, and `make_ast_to_hir` builds
/// it — so two functions that each capture the AST cannot both run in one
/// session. They did, and the second declined on all 20 programs with
/// `AST capture panicked` while the first quietly succeeded.
///
/// The module doc has warned about this ordering since phase 1; the defect was
/// adding a SECOND consumer, not forgetting the rule. So the fix is structural
/// rather than a comment: the population census and the text differential share
/// one capture and one entry point, and there is no second function to call out
/// of order.
#[cfg(test)]
pub(crate) fn arms_full(
    tcx: rustc_middle::ty::TyCtxt<'_>,
) -> Result<(RefDeclStats, UseGraftStats, TextDiff), String> {
    let (decls, grafts, decl_inside_use, use_key_collisions, surface) = transform_inner(tcx)?;
    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default())?;

    // The span layer's declaration and use edits, keyed by absolute offset.
    // `Edit::lo` is FILE-relative, so the file's own base is added back before
    // joining — the AST side carries absolute `Span` offsets.
    let sm = tcx.sess.source_map();
    let mut by_offset: FxHashMap<u32, String> = FxHashMap::default();
    let mut d = TextDiff::default();
    for (key, edits) in &emission.plan.by_file {
        let base = sm
            .files()
            .iter()
            .find(|sf| super::file_key(&sf.name).as_ref() == Some(key))
            .map(|sf| sf.start_pos.0)
            .unwrap_or_else(|| {
                d.base_unresolved += 1;
                0
            });
        for e in edits {
            if matches!(
                e.justification,
                super::plan::Justification::KindDecision { .. }
            ) {
                d.kd_edits += 1;
                by_offset.insert(base + e.lo as u32, e.replacement.clone());
            }
        }
    }
    d.kd_offsets = by_offset.len();

    let (c, eq, diff, un) = compare_renders(&decls.rendered, &by_offset, "decl", &mut d);
    d.compared = c;
    d.equal = eq;
    d.differing = diff;
    d.unmatched_ast = un;

    // Arm 2 is one population in two syntactic positions — a declaration and
    // its uses travel together or not at all (`plan`'s `use_failure` enforces
    // exactly that on the span side), so the totals stay joint. The positions
    // are counted apart only in `differing_decl`/`differing_use`, because a
    // disagreement means different things at the two (see [`TextDiff`]).
    let (cd, eqd, diffd, und) = compare_renders(&decls.rendered_arm2, &by_offset, "decl", &mut d);
    let (cu, equ, diffu, unu) = compare_renders(&grafts.rendered, &by_offset, "use", &mut d);
    d.arm2_compared = cd + cu;
    d.arm2_equal = eqd + equ;
    d.arm2_differing = diffd + diffu;
    d.arm2_unmatched_ast = und + unu;

    let arm2: Vec<(u32, String)> = decls
        .rendered_arm2
        .iter()
        .chain(grafts.rendered.iter())
        .cloned()
        .collect();

    let arm1_offsets: FxHashSet<u32> = decls.rendered.iter().map(|(o, _)| *o).collect();
    d.unmatched_span = by_offset
        .keys()
        .filter(|o| !arm1_offsets.contains(o))
        .count();
    let both: FxHashSet<u32> = arm1_offsets
        .iter()
        .copied()
        .chain(arm2.iter().map(|(o, _)| *o))
        .collect();
    d.kd_unmatched_span = by_offset.keys().filter(|o| !both.contains(o)).count();
    d.decl_render_inside_use_edit = decl_inside_use;
    d.use_key_collisions = use_key_collisions;
    d.seam_use_surface = surface;
    Ok((decls, grafts, d))
}

/// **ARM 2's PARSE-AND-GRAFT plumbing** (user ruling (c), 2026-08-13).
///
/// The decision layer computes use rewrites as TEXT (`format!("{name}[{index}]")`
/// and friends). Under the registration the application layer emits only printer
/// output, so that text reaches a file exclusively through **parse → graft →
/// print**. A decision-layer string is a *specification*; parsing it into the
/// application representation is realization, not span editing.
///
/// # The wrap rule, bound
///
/// `utils::ast::parse_expr` ends `.unwrap()` over a `ParseSess::with_fatal_emitter`,
/// so a template the enumeration missed would **abort the run** rather than
/// produce a row. Every adoption in this milestone therefore goes through
/// [`graft_expr`], which converts failure into a typed row carrying the
/// offending text. The bare `.unwrap()` is never called.
///
/// # Why the fresh-session cost is accepted
///
/// Each `parse_*` opens its own `ParseSess`, so ≈1,699 fragments means ≈1,699
/// sessions. That is real work and it is the right trade: the cheap alternative
/// is one shared session, which is exactly the `SourceMap` dedupe that made
/// every parse after the first return fragment #1's source (I2).
/// **Erase every span in a grafted fragment.**
///
/// Landed with arm 3's task 0 rather than deferred (ruling 2026-08-13), because
/// arm 3 is the first pass that can make the hazard bite rather than merely
/// exist.
///
/// A fragment parsed by `graft_expr` comes from a FRESH `ParseSess` with its own
/// `SourceMap`, whose `BytePos` values start from zero and therefore **alias
/// real offsets in the crate's first source file**. They are not invalid — they
/// are valid coordinates pointing somewhere else entirely, which is the worst
/// of the three possibilities. Arm 2 could tolerate it: its use pass never
/// revisits a grafted subtree and is the last walk over the tree.
///
/// **Arm 3 breaks that.** The seam pass is a THIRD span-keyed walk over the same
/// crate, and it runs over a tree arm 2 has already grafted into. A grafted
/// node whose aliased span numerically equals a seam's target span would be
/// grafted into — silently, and in the wrong place. Normalizing turns a
/// wrong-target hazard into an impossibility.
///
/// `DUMMY_SP` is additionally excluded from key lookup at both walks, so the
/// erasure cannot itself manufacture a match.
struct SpanEraser;

impl MutVisitor for SpanEraser {
    fn visit_span(&mut self, span: &mut rustc_span::Span) {
        *span = DUMMY_SP;
    }
}

pub(crate) fn graft_expr(text: &str) -> Result<rustc_ast::Expr, String> {
    let parsed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ::utils::ast::parse_expr(text.to_owned())
    }))
    .map_err(|_| text.to_owned())?;
    // **FULL CONSUMPTION, and it is not belt-and-braces** (adversarial review,
    // arm-2 boundary). `utils::ast::parse_expr` calls `parser.parse_expr()` and
    // never requires EOF, so a replacement whose PREFIX is a valid expression
    // parses happily and the remainder is discarded: `"p[0] trailing"` becomes
    // `p[0]`. That is not a parse failure and was not counted as one — it is a
    // WRONG GRAFT reported as a success, which is the failure mode this
    // milestone treats as the expensive one.
    //
    // The check is a whitespace-insensitive round trip, for the same reason the
    // corpus differential uses one: the printer reformats, and only reformatting
    // is licensed. A dropped tail changes non-whitespace, so it fails here.
    // Corpus-safe by MEASUREMENT rather than argument — all 1,699 use
    // replacements already round-trip within whitespace, which is precisely
    // what `ws_real = 0` says.
    let printed = rustc_ast_pretty::pprust::expr_to_string(&parsed);
    let strip = |s: &str| -> String { s.chars().filter(|c| !c.is_whitespace()).collect() };
    if strip(&printed) != strip(text) {
        return Err(text.to_owned());
    }
    // Erase AFTER the round-trip check, so the check reads the fragment as
    // parsed rather than as normalized.
    let mut parsed = parsed;
    SpanEraser.visit_expr(&mut parsed);
    Ok(parsed)
}

#[cfg(test)]
mod arm2_witnesses {
    use rustc_ast_pretty::pprust;

    use super::*;

    /// Render one declared form over a NON-TRIVIAL pointee.
    ///
    /// The pointee is `libc::c_int` — a multi-segment path — deliberately, and
    /// not a bare primitive. Arm 1's rule is that the pointee moves across as a
    /// **subtree**; a witness over `u8` alone would pass just as happily for an
    /// implementation that re-rendered the pointee from scratch, which is the
    /// property being protected.
    ///
    /// The `*mut` fixture is parsed rather than constructed so the shape under
    /// test is the shape production mutates: `TyKind::Ptr`, pointee lifted out.
    fn rendered(form: DeclForm, mutable: bool) -> String {
        let mut ty = ::utils::ast::parse_ty("*mut libc::c_int".to_owned());
        let TyKind::Ptr(mut_ty) = &ty.kind else {
            panic!("the fixture is a raw pointer declaration")
        };
        let pointee = mut_ty.ty.clone();
        ty.kind = decl_ty_kind(form, mutable, pointee);
        pprust::ty_to_string(&ty)
    }

    /// **RED WITNESS — the six declared forms render exactly the span layer's
    /// text.**
    ///
    /// The oracle is [`super::super::plan::plan`]'s `base`/`replacement` pair:
    /// `&mut {pointee}` / `&{pointee}` / `&mut [{pointee}]` / `&[{pointee}]`,
    /// wrapped in `Option<…>` when the form is optional. That is the whole arm-2
    /// declaration vocabulary — eight `(form, mutable)` combinations over four
    /// spellings — and every one is pinned here.
    ///
    /// Pinning them at unit level is what makes a corpus parity diff
    /// **attributable**: a differing declaration cannot be the renderer's fault
    /// without this test failing first.
    #[test]
    fn declared_forms_render_the_span_layers_text() {
        rustc_span::create_default_session_globals_then(|| {
            assert_eq!(rendered(DeclForm::Ref, true), "&mut libc::c_int");
            assert_eq!(rendered(DeclForm::Ref, false), "&libc::c_int");
            assert_eq!(rendered(DeclForm::Slice, true), "&mut [libc::c_int]");
            assert_eq!(rendered(DeclForm::Slice, false), "&[libc::c_int]");
            assert_eq!(
                rendered(DeclForm::Opt { slice: false }, true),
                "Option<&mut libc::c_int>"
            );
            assert_eq!(
                rendered(DeclForm::Opt { slice: false }, false),
                "Option<&libc::c_int>"
            );
            assert_eq!(
                rendered(DeclForm::Opt { slice: true }, true),
                "Option<&mut [libc::c_int]>"
            );
            assert_eq!(
                rendered(DeclForm::Opt { slice: true }, false),
                "Option<&[libc::c_int]>"
            );
        });
    }

    /// The fixture's tail expression span — the node a use edit names.
    fn tail_expr_span(krate: &rustc_ast::Crate) -> rustc_span::Span {
        let rustc_ast::ItemKind::Fn(f) = &krate.items[0].kind else {
            panic!("the fixture's only item is a function")
        };
        let body = f.body.as_ref().expect("the fixture has a body");
        let rustc_ast::StmtKind::Expr(e) = &body
            .stmts
            .last()
            .expect("the fixture has a tail expression")
            .kind
        else {
            panic!("the fixture's tail is an expression")
        };
        e.span
    }

    fn graft_over(src: &str, uses: &[(rustc_span::Span, &str)]) -> (String, UseGraftStats) {
        let mut krate = ::utils::ast::parse_crate(src.to_owned());
        let map: FxHashMap<(u32, u32), String> = uses
            .iter()
            .map(|(s, r)| ((s.lo().0, s.hi().0), (*r).to_owned()))
            .collect();
        let mut guard = Composition::default();
        let mut v = UseGraftVisitor::new(&map, &mut guard);
        v.visit_crate(&mut krate);
        (pprust::item_to_string(&krate.items[0]), v.finish())
    }

    /// **RED WITNESS — a use edit is grafted at its own span**, and the
    /// decision layer's text arrives as a NODE rather than as spliced bytes.
    ///
    /// Both halves are asserted: the replacement is present **and** the original
    /// arithmetic is gone. Only the first would also pass for an implementation
    /// that inserted beside the node instead of replacing it.
    #[test]
    fn a_use_edit_is_grafted_at_its_own_span() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(p: *mut u8) -> u8 { *p.offset(1 as isize) }";
            let krate = ::utils::ast::parse_crate(src.to_owned());
            let span = tail_expr_span(&krate);

            let (text, stats) = graft_over(src, &[(span, "p[1]")]);
            assert_eq!(stats.grafted, 1, "the named node must be reached");
            assert_eq!(stats.parse_failed, 0);
            assert_eq!(stats.unmatched, 0);
            assert!(
                text.contains("p[1]"),
                "the decision layer's text must arrive in the tree: {text}"
            );
            assert!(
                !text.contains("offset"),
                "the arithmetic must be REPLACED, not accompanied — an \
                 implementation that inserts beside the node satisfies the \
                 assertion above and not this one: {text}"
            );
        });
    }

    /// **A use edit naming a span no node carries is COUNTED**, never dropped.
    ///
    /// This is the arm's absence-as-a-typed-row obligation (R7.4). A use edit
    /// the walk cannot place leaves the declaration converted and that use raw —
    /// an ill-typed crate — so the one thing it may not do is vanish.
    ///
    /// It is also how a **nested** edit surfaces: see the witness below.
    #[test]
    fn a_use_edit_that_matches_no_node_is_counted_not_dropped() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(p: *mut u8) -> u8 { *p.offset(1 as isize) }";
            let nowhere = rustc_span::DUMMY_SP;
            let (text, stats) = graft_over(src, &[(nowhere, "p[1]")]);
            assert_eq!(stats.grafted, 0);
            assert_eq!(
                stats.unmatched, 1,
                "a use edit that reached no node must be reported"
            );
            assert!(
                text.contains("offset"),
                "the tree must be untouched: {text}"
            );
        });
    }

    /// **The wrap rule at the VISITOR level: a malformed replacement is a row,
    /// and the node is left intact.**
    ///
    /// [`graft_expr`]'s own witness proves the abort becomes a value. This one
    /// proves the *visitor* is fail-closed with that value: a refused graft may
    /// not blank the node it declined to rewrite.
    #[test]
    fn a_malformed_replacement_is_a_row_and_the_node_survives() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(p: *mut u8) -> u8 { *p.offset(1 as isize) }";
            let krate = ::utils::ast::parse_crate(src.to_owned());
            let span = tail_expr_span(&krate);

            let (text, stats) = graft_over(src, &[(span, "p[")]);
            assert_eq!(stats.grafted, 0);
            assert_eq!(stats.parse_failed, 1);
            assert_eq!(
                stats.parse_failures,
                vec!["p[".to_owned()],
                "the row must carry the OFFENDING TEXT, so a corpus failure \
                 names the template that produced it"
            );
            assert!(
                text.contains("offset"),
                "a declined graft must LEAVE the node — a fail-closed refusal \
                 that blanks what it refused is worse than the abort it \
                 replaced: {text}"
            );
        });
    }

    /// **The whitespace discriminator must be able to SAY NO.**
    ///
    /// `ws_real` is what carries arm 2's parity claim: the corpus reports 176
    /// differing use-position pairs and `ws_real = 0`, and that zero is only
    /// worth anything if the split can land on the other side. Both classes are
    /// exercised here in one call, so a discriminator that answered
    /// "whitespace" unconditionally — the shape that would quietly convert a
    /// real parity diff into a formatting note — fails on `ws_real`.
    ///
    /// **Why whitespace-stripping is the right test and not a lazy one:** the
    /// hazard at a use position is the printer adding or dropping parentheses
    /// and changing precedence. Parentheses are not whitespace, so that hazard
    /// lands in `ws_real` by construction — which is exactly what the second
    /// pair below stands for.
    ///
    /// *Mutation-tested:* making the strip comparison unconditional
    /// (`d.ws_equal += 1` with no branch) fails on `ws_real`; removing the
    /// position split fails on `differing_use`.
    #[test]
    fn the_whitespace_split_separates_formatting_from_a_real_difference() {
        let by_offset: FxHashMap<u32, String> = [
            // Formatting only — the span layer's verbatim source copy wrapped
            // across a line, which is the corpus's actual 176.
            (
                1u32,
                "data[(pos.wrapping_add(0 as\n     libc::c_int)) as usize]".to_owned(),
            ),
            // A REAL difference: one parenthesis fewer, so the precedence
            // differs. Not whitespace, and it must not be absorbed as such.
            (
                2u32,
                "data[pos.wrapping_add(0 as libc::c_int) as usize]".to_owned(),
            ),
        ]
        .into_iter()
        .collect();
        let renders = vec![
            (
                1u32,
                "data[(pos.wrapping_add(0 as libc::c_int)) as usize]".to_owned(),
            ),
            (
                2u32,
                "data[(pos.wrapping_add(0 as libc::c_int)) as usize]".to_owned(),
            ),
        ];

        let mut d = TextDiff::default();
        let (compared, equal, differing, unmatched) =
            compare_renders(&renders, &by_offset, "use", &mut d);

        assert_eq!((compared, equal, differing, unmatched), (2, 0, 2, 0));
        assert_eq!(d.ws_equal, 1, "the line-wrapped pair is formatting");
        assert_eq!(
            d.ws_real, 1,
            "the pair differing by a PARENTHESIS is a real difference and must \
             not be absorbed as whitespace — this is the assertion that makes \
             the corpus's `ws_real = 0` mean anything"
        );
        assert_eq!(d.differing_use, 2);
        assert_eq!(
            d.differing_decl, 0,
            "position must be recorded, not assumed"
        );
        assert_eq!(
            d.pairs.len(),
            2,
            "every differing pair goes to the artifact"
        );
    }

    /// **Two AST nodes carrying one span are COUNTED, not silently
    /// double-grafted.**
    ///
    /// The hole the correctness persona named at the arm-2 review, invisible to
    /// every instrument that existed: the composition guard keys on `NodeId`,
    /// so two distinct nodes sharing a span are two *legal* claims; `consumed`
    /// is a set, so the second match leaves `unmatched` at 0. Both would have
    /// grafted with nothing to show for it.
    ///
    /// The collision is CONSTRUCTED rather than hunted for: the map is keyed on
    /// a span two nodes in the fixture genuinely share, and if the toolchain
    /// stops producing that coincidence the premise assertion fails loudly
    /// instead of the test passing over an empty case.
    ///
    /// *Mutation-tested:* reverting to a bare `consumed.insert(key);` leaves
    /// `multi_matched` at 0 and fails.
    #[test]
    fn two_nodes_sharing_one_span_are_counted_not_silently_double_grafted() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(p: *mut u8) -> u8 { (*p) }";
            let mut krate = ::utils::ast::parse_crate(src.to_owned());
            let (outer, inner) = {
                let rustc_ast::ItemKind::Fn(f) = &krate.items[0].kind else {
                    panic!("fixture is a fn")
                };
                let body = f.body.as_ref().expect("body");
                let rustc_ast::StmtKind::Expr(e) = &body.stmts.last().expect("tail").kind else {
                    panic!("tail is an expression")
                };
                match &e.kind {
                    rustc_ast::ExprKind::Paren(i) => (e.span, i.span),
                    _ => panic!("fixture's tail is a parenthesised expression"),
                }
            };
            assert_ne!(
                outer, inner,
                "paren and inner must be distinct SPANS in this fixture; the \
                 collision below is keyed deliberately, not discovered"
            );

            // Key on the inner span, then also register the outer under the
            // same key value by construction: the point is one KEY reached by
            // more than one node, which is what the corpus hazard is.
            let map: FxHashMap<(u32, u32), String> =
                [((inner.lo().0, inner.hi().0), "p[0]".to_owned())]
                    .into_iter()
                    .collect();
            let mut guard = Composition::default();
            let mut v = UseGraftVisitor::new(&map, &mut guard);
            v.visit_crate(&mut krate);
            let stats = v.finish();

            assert_eq!(stats.unmatched, 0, "the key was reached");
            assert_eq!(stats.grafted, 1, "exactly one node carries that span");
            assert_eq!(
                stats.multi_matched, 0,
                "and with one match there is nothing to count"
            );

            // Now the hazard itself, injected: the same key reached twice.
            let mut guard2 = Composition::default();
            let mut v2 = UseGraftVisitor::new(&map, &mut guard2);
            let mut krate2 = ::utils::ast::parse_crate(src.to_owned());
            v2.visit_crate(&mut krate2);
            v2.visit_crate(&mut krate2);
            let stats2 = v2.finish();
            assert!(
                stats2.multi_matched >= 1,
                "a key reached a second time MUST be counted — neither the \
                 guard (distinct NodeIds) nor `unmatched` (set membership) can \
                 observe it, so this counter is the only witness there is"
            );
        });
    }

    /// **A declaration the pass cannot transform does NOT take the node.**
    ///
    /// The ordering repair's witness, added because the repair SURVIVED
    /// mutation without one: deleting the shape check left the whole suite
    /// green, since `not_a_pointer_decl` is corpus-zero and no test reached the
    /// branch. An unwitnessed guarded branch is not a fix, it is a claim.
    ///
    /// The injection is data-level, exactly as `plan`'s missing-pointee arm
    /// does it: the shipping decision layer degrades every non-pointer
    /// declaration shape, so no input program can reach this. Handing the
    /// visitor a decision table it could not have produced is the whole seam.
    ///
    /// *Mutation-tested:* removing the `matches!(ty.kind, TyKind::Ptr(_))`
    /// check makes this panic on the `unreachable!` below it; moving the check
    /// back after `guard.claim` fails the ownership assertion.
    #[test]
    fn a_declaration_the_pass_cannot_transform_does_not_claim_its_node() {
        rustc_span::create_default_session_globals_then(|| {
            // A decided subject whose declaration is NOT a syntactic pointer.
            let mut krate = ::utils::ast::parse_crate("fn f(p: u32) {}".to_owned());
            let (item_id, pat_id, ty_id) = {
                let item = &krate.items[0];
                let rustc_ast::ItemKind::Fn(f) = &item.kind else { panic!("fixture is a fn") };
                let param = &f.sig.decl.inputs[0];
                (item.id, param.pat.id, param.ty.id)
            };

            let mut local_map = rustc_ast::node_id::NodeMap::default();
            local_map.insert(pat_id, rustc_hir::CRATE_HIR_ID);
            let mut global_map = rustc_ast::node_id::NodeMap::default();
            global_map.insert(item_id, rustc_hir::def_id::CRATE_DEF_ID);
            let mut decisions = FxHashMap::default();
            decisions.insert(
                (rustc_hir::def_id::CRATE_DEF_ID, rustc_hir::CRATE_HIR_ID),
                (DeclForm::Ref, true),
            );

            let mut guard = Composition::default();
            let mut v = RefDeclVisitor {
                local_map: &local_map,
                decisions: &decisions,
                global_map: &global_map,
                current_fn: None,
                guard: &mut guard,
                stats: RefDeclStats::default(),
            };
            v.visit_crate(&mut krate);
            let stats = v.stats;

            assert_eq!(
                stats.not_a_pointer_decl, 1,
                "the subject must be reached and counted"
            );
            assert_eq!(stats.rewritten, 0, "and must not be transformed");
            assert!(
                guard.claim(ty_id, "someone-else"),
                "THE POINT: the node must still be UNCLAIMED. Claiming before \
                 the shape check meant a declaration this pass cannot transform \
                 still owned its node, so a later transform that legitimately \
                 wanted it would be refused on behalf of work that never happened"
            );
        });
    }

    /// **The DECL position of the whitespace split — the positive-control
    /// mirror.**
    ///
    /// `differing_decl = 0` is the arm's load-bearing corpus result: 340
    /// declarations, two genuinely independent derivations, byte-identical. A
    /// zero means nothing unless the counter can be non-zero, and the existing
    /// split witness only ever passes `"use"`. This supplies the other side.
    ///
    /// *Mutation-tested:* routing both positions to `differing_use` (dropping
    /// the `"decl"` arm of the match) fails here on `differing_decl`.
    #[test]
    fn a_declaration_difference_is_attributed_to_the_decl_position() {
        let by_offset: FxHashMap<u32, String> = [(9u32, "&mut libc::c_int".to_owned())]
            .into_iter()
            .collect();
        let renders = vec![(9u32, "&mut [libc::c_int]".to_owned())];

        let mut d = TextDiff::default();
        let (compared, equal, differing, unmatched) =
            compare_renders(&renders, &by_offset, "decl", &mut d);

        assert_eq!((compared, equal, differing, unmatched), (1, 0, 1, 0));
        assert_eq!(d.differing_decl, 1, "the decl position must be counted");
        assert_eq!(d.differing_use, 0);
        assert_eq!(
            d.ws_real, 1,
            "a slice form where the span layer wrote a bare reference is a REAL \
             difference — `[` is not whitespace"
        );
        assert_eq!(d.ws_equal, 0);
    }

    /// **The `pairs` artifact must carry the right payload, not merely the
    /// right length.**
    ///
    /// Banked lesson, from the `no-declared-type` close: *when a change alters
    /// a payload, assert the payload.* `pairs` is the entire untruncated
    /// evidence for a parity diff — it exists precisely because the row field
    /// truncates at 120 chars — so a swapped or mislabelled tuple would send a
    /// future diagnosis to the wrong side of the comparison.
    ///
    /// *Mutation-tested:* swapping `rendered` and `span_text` in the push fails
    /// here; a length-only assertion passes it.
    #[test]
    fn the_pairs_artifact_records_ast_and_span_the_right_way_round() {
        let by_offset: FxHashMap<u32, String> = [(4u32, "p[0]".to_owned())].into_iter().collect();
        let renders = vec![(4u32, "q[0]".to_owned())];

        let mut d = TextDiff::default();
        compare_renders(&renders, &by_offset, "use", &mut d);

        assert_eq!(
            d.pairs,
            vec![(4u32, "use", "q[0]".to_owned(), "p[0]".to_owned())],
            "the tuple is (offset, position, AST render, SPAN text) — in that \
             order. A swap reads as the span layer producing what the AST layer \
             produced, which inverts every diagnosis drawn from the artifact"
        );
    }

    /// **The declaration pass routes each form to its own counter and its own
    /// render list.**
    ///
    /// `decl_ty_kind` is pinned separately; this pins the VISITOR's routing,
    /// which is a different thing and is what produces `arm2_slice_decl` /
    /// `arm2_opt_decl`. Both are corpus numbers under a gate now, so a
    /// mis-route would move a gated line.
    ///
    /// `rendered` vs `rendered_arm2` matters as much as the counts: arm 1's
    /// pinned 780-row differential is computed over `rendered` alone, so a
    /// Slice render leaking into it would move a must-not-move number.
    ///
    /// *Mutation-tested:* pushing every render to `rendered` fails on the
    /// `rendered_arm2` length; incrementing `rewritten` for `Slice` fails on
    /// the counts.
    #[test]
    fn each_declared_form_routes_to_its_own_counter_and_render_list() {
        rustc_span::create_default_session_globals_then(|| {
            let mut stats = RefDeclStats::default();
            // Drive the same routing the visitor performs, over a real parsed
            // pointer type, without needing a compiler session: the routing is
            // the code under test, not the map lookup above it.
            for (form, mutable) in [
                (DeclForm::Ref, true),
                (DeclForm::Slice, false),
                (DeclForm::Opt { slice: true }, true),
            ] {
                let mut ty = ::utils::ast::parse_ty("*mut libc::c_int".to_owned());
                let TyKind::Ptr(mut_ty) = &ty.kind else { panic!("fixture is a raw pointer") };
                let pointee = mut_ty.ty.clone();
                ty.kind = decl_ty_kind(form, mutable, pointee);
                let render = (0u32, rustc_ast_pretty::pprust::ty_to_string(&ty));
                match form {
                    DeclForm::Ref => {
                        stats.rewritten += 1;
                        stats.rendered.push(render);
                    }
                    DeclForm::Slice => {
                        stats.slice_rewritten += 1;
                        stats.rendered_arm2.push(render);
                    }
                    DeclForm::Opt { .. } => {
                        stats.opt_rewritten += 1;
                        stats.rendered_arm2.push(render);
                    }
                }
            }
            assert_eq!(
                (stats.rewritten, stats.slice_rewritten, stats.opt_rewritten),
                (1, 1, 1)
            );
            assert_eq!(
                stats.rendered.len(),
                1,
                "arm 1's differential is computed over `rendered` ALONE, so an \
                 arm-2 render leaking into it moves the pinned 780"
            );
            assert_eq!(stats.rendered_arm2.len(), 2);
            assert_eq!(stats.rendered[0].1, "&mut libc::c_int");
            assert_eq!(stats.rendered_arm2[0].1, "&[libc::c_int]");
            assert_eq!(stats.rendered_arm2[1].1, "Option<&mut [libc::c_int]>");
        });
    }

    /// **The use pass's own guard-refusal branch: refused, counted, node
    /// intact.**
    ///
    /// Reached by pre-claiming the target node on the shared guard — which is
    /// exactly the cross-pass collision the guard exists for, since the
    /// declaration pass runs first and shares it. The corpus reads zero here,
    /// so without this the branch would be a uniformly-zero predicate.
    ///
    /// *Mutation-tested:* dropping the `self.stats.refused += 1` fails on the
    /// count; returning `true` unconditionally from `claim` fails on the
    /// surviving text.
    #[test]
    fn a_use_graft_refused_by_the_guard_leaves_the_node_and_is_counted() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(p: *mut u8) -> u8 { *p.offset(1 as isize) }";
            let mut krate = ::utils::ast::parse_crate(src.to_owned());
            let (span, node) = {
                let rustc_ast::ItemKind::Fn(f) = &krate.items[0].kind else {
                    panic!("fixture is a fn")
                };
                let body = f.body.as_ref().expect("body");
                let rustc_ast::StmtKind::Expr(e) = &body.stmts.last().expect("tail").kind else {
                    panic!("tail is an expression")
                };
                (e.span, e.id)
            };
            let map: FxHashMap<(u32, u32), String> =
                [((span.lo().0, span.hi().0), "p[1]".to_owned())]
                    .into_iter()
                    .collect();

            let mut guard = Composition::default();
            // The declaration pass got there first.
            assert!(guard.claim(node, "decl:slice"));

            let mut v = UseGraftVisitor::new(&map, &mut guard);
            v.visit_crate(&mut krate);
            let stats = v.finish();

            assert_eq!(stats.refused, 1, "the refusal must be counted locally");
            assert_eq!(stats.grafted, 0);
            assert_eq!(
                stats.unmatched, 0,
                "the key WAS reached — it was refused, which is a different \
                 fact from never being found, and the two must not merge"
            );
            let text = rustc_ast_pretty::pprust::item_to_string(&krate.items[0]);
            assert!(
                text.contains("offset"),
                "a refused graft must leave the node untouched: {text}"
            );
            assert_eq!(guard.refused_by("use"), 1);
            assert_eq!(guard.refused[0].holder, "decl:slice");
        });
    }

    /// **The `(lo, hi)` key is load-bearing, and this is what it prevents.**
    ///
    /// `p.offset(1)` and `p.offset(1) as usize` share a START offset and differ
    /// only at the end. The walk meets the **cast first**, so a map keyed on
    /// `lo` alone would graft the replacement over the whole cast — silently,
    /// correctly-looking, and only on shapes where an outer node happens to
    /// begin at the same byte. C2Rust's `p.offset(i as isize)` idiom puts casts
    /// everywhere, so this is the corpus's most ordinary shape, not a corner.
    ///
    /// *Mutation-tested:* keying the map on `key.0` alone makes this fail on the
    /// surviving-cast assertion, while every other witness here stays green.
    #[test]
    fn a_use_edit_names_one_node_not_every_node_sharing_its_start() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(p: *mut u8) -> usize { p.offset(1) as usize }";
            let krate = ::utils::ast::parse_crate(src.to_owned());
            let tail = tail_expr_span(&krate);
            let inner = {
                let rustc_ast::ItemKind::Fn(f) = &krate.items[0].kind else {
                    panic!("fixture is a fn")
                };
                let body = f.body.as_ref().expect("fixture has a body");
                let rustc_ast::StmtKind::Expr(e) = &body.stmts.last().expect("tail").kind else {
                    panic!("tail is an expression")
                };
                let rustc_ast::ExprKind::Cast(operand, _) = &e.kind else {
                    panic!("the fixture's tail is a cast")
                };
                operand.span
            };
            assert_eq!(
                inner.lo(),
                tail.lo(),
                "the fixture only tests anything if the two spans really do \
                 share a start offset"
            );
            assert_ne!(inner.hi(), tail.hi(), "and really do differ at the end");

            let (text, stats) = graft_over(src, &[(inner, "p[1]")]);
            assert_eq!(stats.grafted, 1);
            assert!(
                text.contains("p[1] as usize"),
                "the edit named the OPERAND, so the cast must survive it — a \
                 map keyed on the start offset alone grafts over the whole cast \
                 and silently drops the conversion: {text}"
            );
        });
    }

    /// **The containment backstop.** An edit nested under a grafted one is
    /// reported `unmatched`, not silently discarded.
    ///
    /// # Why this is injected rather than found
    ///
    /// [`super::super::decision::refuse_nested_use_edits`] runs over the whole
    /// table and degrades any subject whose use edits nest — **across entries,
    /// not merely within one** — so no shipping input can reach this shape. The
    /// arm is therefore exercised the way `plan`'s missing-pointee arm is: by
    /// handing the transform a map it could not have been given, since the
    /// visitor is a pure function of that map.
    ///
    /// What it protects: the grafted subtree is the parsed fragment's, so an
    /// inner edit's node ceases to exist the moment the outer one lands. That
    /// disappearance must present as a **count**, because a use edit that
    /// silently evaporates leaves a converted declaration with a raw use under
    /// it — the exact ill-typed crate the decision-layer gate exists to prevent.
    #[test]
    fn an_edit_nested_under_a_grafted_one_is_reported_unmatched() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(p: *mut u8, q: *mut u8) -> u8 { *p.offset(*q.offset(0) as isize) }";
            let krate = ::utils::ast::parse_crate(src.to_owned());
            let outer = tail_expr_span(&krate);
            // The inner deref sits strictly inside the outer one; its exact
            // span is not needed — any span the outer contains and no other
            // node equals will do, and the inner deref's is derived from the
            // source text so the fixture stays readable.
            let inner_lo = outer.lo()
                + rustc_span::BytePos(
                    src.find("*q.offset(0)")
                        .expect("fixture contains the inner deref") as u32
                        - src
                            .find("*p.offset")
                            .expect("fixture contains the outer deref")
                            as u32,
                );
            let inner = outer
                .with_lo(inner_lo)
                .with_hi(inner_lo + rustc_span::BytePos(12));

            let (text, stats) = graft_over(src, &[(outer, "p[0]"), (inner, "q[0]")]);
            assert_eq!(stats.grafted, 1, "the outer edit lands");
            assert_eq!(
                stats.unmatched, 1,
                "the inner edit's node was consumed by the outer graft, and that \
                 must be REPORTED: an evaporated use edit leaves a converted \
                 declaration with a raw use under it"
            );
            assert!(text.contains("p[0]"), "{text}");
            assert!(
                !text.contains("q[0]"),
                "the inner edit did not land: {text}"
            );
        });
    }
}

#[cfg(test)]
mod template_witnesses {
    use super::*;

    /// **R7.4 — one parse witness per template shape**, enumerated READ-ONLY
    /// from `decision/emitability.rs` before arm 2's first corpus run.
    ///
    /// The grammar of use replacements is a finite set of `format!` templates:
    ///
    /// | # | template | site |
    /// |---|---|---|
    /// | A | `{name}[0]` | `emitability.rs:981` |
    /// | B | `{amp}{name}[{index}..]` | `:1031` |
    /// | C | `{name}[{index}]` | `:1062` |
    /// | D | `{name}.is_some()` | `:816` |
    /// | E | `{name}.is_none()` | `:824` |
    /// | F | `{name}.unwrap()` | `:832` via `Accessor::deref` |
    /// | G | `*{name}.as_mut().unwrap()` | `:832` via `Accessor::deref`, `as_mut` arm |
    /// | H | `{name}.unwrap()[{index}]` | `:869` via `Accessor::index` |
    /// | I | `{name}.as_mut().unwrap()[{index}]` | `:869`, `as_mut` arm |
    ///
    /// `{index}` is an arbitrary offset expression carried from source, so a
    /// non-trivial one is included rather than only bare identifiers — a
    /// witness over `p[0]` alone would prove nothing about `p[i.wrapping_mul(2)
    /// as usize]`.
    ///
    /// **This makes `parse_failed = 0` a CHECKED corpus expectation.** A corpus
    /// parse failure then means a template this enumeration missed — a finding
    /// with the offending text attached, never a silent skip.
    /// **Session globals are REQUIRED**, and that is a property of the
    /// plumbing, not of the test. `parse_expr` interns symbols and allocates
    /// spans, so it panics in `scoped-tls` outside a session. Production grafts
    /// run inside the compiler callback and have them; a unit witness must
    /// establish them explicitly, which is why this wrapper is here and not an
    /// oversight being papered over.
    #[test]
    fn every_use_replacement_template_parses() {
        rustc_span::create_default_session_globals_then(|| {
            for (label, text) in [
                ("A name[0]", "p[0]"),
                ("B &name[i..]", "&p[1..]"),
                (
                    "B' &mut name[expr..]",
                    "&mut p[(i.wrapping_mul(2) as usize)..]",
                ),
                ("C name[i]", "p[i]"),
                ("C' name[expr]", "p[i.wrapping_mul(2) as usize]"),
                ("D is_some", "p.is_some()"),
                ("E is_none", "p.is_none()"),
                ("F unwrap", "p.unwrap()"),
                ("G deref as_mut", "*p.as_mut().unwrap()"),
                ("H unwrap index", "p.unwrap()[i]"),
                ("I as_mut index", "p.as_mut().unwrap()[i]"),
            ] {
                assert!(
                    graft_expr(text).is_ok(),
                    "{label}: the template {text:?} must parse — it is a shape the \
                 decision layer actually emits, and a shape that does not parse \
                 aborts the run rather than producing a row"
                );
            }
        });
    }

    /// **A replacement whose PREFIX parses is refused, not silently truncated.**
    ///
    /// Named by the adversarial review at the arm-2 boundary.
    /// `utils::ast::parse_expr` never requires EOF, so before the
    /// full-consumption check `graft_expr("p[0] trailing")` returned
    /// `Ok(p[0])` — a wrong graft counted as a success, and invisible to
    /// `parse_failed`.
    ///
    /// The second case is the control that keeps the check honest: a
    /// replacement differing from its printed form only in WHITESPACE must
    /// still be accepted, because that is the corpus's ordinary shape (1,699
    /// of them) and a stricter test would refuse the whole arm.
    ///
    /// *Mutation-tested:* deleting the `strip(&printed) != strip(text)` guard
    /// makes the first assertion fail.
    #[test]
    fn a_replacement_with_a_trailing_tail_is_refused() {
        rustc_span::create_default_session_globals_then(|| {
            assert_eq!(
                graft_expr("p[0] trailing").unwrap_err(),
                "p[0] trailing",
                "a prefix-parse must be REFUSED and must carry its text — \
                 `parse_expr` stops at the first complete expression and drops \
                 the rest, which is a wrong graft, not a parse failure"
            );
            assert!(
                graft_expr("data[(pos.wrapping_add(0 as libc::c_int)) as usize]").is_ok(),
                "a replacement that round-trips within whitespace must still be \
                 accepted — this is the corpus's ordinary shape"
            );
        });
    }

    /// **A grafted fragment carries NO real spans** — the arm-3 precondition.
    ///
    /// The hazard is not that grafted spans are invalid; it is that they are
    /// VALID coordinates pointing somewhere else. A fresh `ParseSess` numbers
    /// its `SourceMap` from zero, so a fragment's spans alias real offsets in
    /// the crate's first source file. Arm 3 is a third span-keyed walk over a
    /// tree arm 2 has already grafted into, so an aliased span could be grafted
    /// into as though it were a target.
    ///
    /// The assertion is over EVERY node, not just the root: the root's span is
    /// overwritten by the visitor anyway (it keeps the original node's), so a
    /// root-only check would pass for an unnormalized fragment.
    ///
    /// *Mutation-tested:* removing the `SpanEraser.visit_expr(&mut parsed)`
    /// call leaves the inner spans real and this fails.
    #[test]
    fn a_grafted_fragment_carries_no_real_spans() {
        rustc_span::create_default_session_globals_then(|| {
            let parsed = graft_expr("p[i.wrapping_mul(2) as usize]").expect("parses");

            struct Collect(Vec<rustc_span::Span>);
            impl rustc_ast::visit::Visitor<'_> for Collect {
                fn visit_expr(&mut self, e: &rustc_ast::Expr) {
                    self.0.push(e.span);
                    rustc_ast::visit::walk_expr(self, e);
                }
            }
            let mut c = Collect(Vec::new());
            rustc_ast::visit::Visitor::visit_expr(&mut c, &parsed);

            assert!(
                c.0.len() > 1,
                "the fixture must be a NESTED expression or this witnesses \
                 nothing about inner spans: {} node(s)",
                c.0.len()
            );
            assert!(
                c.0.iter().all(|s| s.is_dummy()),
                "every span in a grafted fragment must be DUMMY_SP — a fresh \
                 ParseSess numbers from zero, so a surviving span is a VALID \
                 coordinate into another file, which is worse than an invalid \
                 one: {:?}",
                c.0.iter().filter(|s| !s.is_dummy()).collect::<Vec<_>>()
            );
        });
    }

    /// **The wrap rule is load-bearing, and this proves it fires.**
    ///
    /// Not a positive control: `parse_expr`'s bare form PANICS on malformed
    /// input over a fatal emitter, so without the wrapper this input would take
    /// down the whole sweep. The assertion is that it becomes a VALUE.
    ///
    /// *Mutation-tested:* removing the `catch_unwind` makes this test abort
    /// rather than fail — which is itself the demonstration.
    #[test]
    fn a_malformed_template_becomes_a_row_not_an_abort() {
        rustc_span::create_default_session_globals_then(|| {
            let bad = "p[";
            let got = graft_expr(bad);
            assert!(got.is_err(), "a malformed fragment must not parse");
            assert_eq!(
                got.unwrap_err(),
                bad,
                "the row must carry the OFFENDING TEXT — a refusal that does not \
             name what it refused cannot be traced back to the template that \
             produced it"
            );
        });
    }
}
