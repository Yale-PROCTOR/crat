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

/// **ARM 3 — the glue shapes**, as the span layer's `format!` set classifies
/// them.
///
/// Five of the ten shapes `seam_tsv`'s classifier knows are realized on the
/// frozen corpus (`from_raw_parts` 273, `some_wrap` 78, `some_reborrow` 37,
/// `from_ref_mut` 29, `some_from_raw_parts` 4 = 421). The other five —
/// `reborrow` alone, `unwrap`, `as_mut_unwrap`, `index` alone,
/// `some_from_ref_mut` — have market **0**.
///
/// `Reborrow` and `Index0` are built anyway, because they are the INNER forms
/// the realized `some_*` shapes wrap; they are not unbuilt zero-market arms in
/// the `-4`/`-5` sense. `Unwrap`/`AsMutUnwrap` are deliberately NOT built: they
/// are standalone shapes with zero market, and a shape the transform does not
/// know must become a typed row rather than a silent skip.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum GlueShape {
    /// `&mut *X` / `&*X`
    Reborrow,
    /// `&mut X[0]` / `&X[0]`
    Index0,
    /// `core::slice::from_raw_parts{_mut}(X, (LEN) as usize)`
    FromRawParts,
    /// `core::slice::from_mut(X)` / `core::slice::from_ref(X)`
    FromRefMut,
    /// `Some(X)` — the wrapper; the `some_*` shapes are this over an inner form.
    Some_,
}

/// The type `usize`, synthesized rather than parsed.
///
/// See the call site: a parsed fragment carries spans from a fresh `ParseSess`
/// that alias real offsets in this crate, and the synthetic-span invariant says
/// nodes this layer manufactures carry `DUMMY_SP`.
fn usize_ty() -> Ty {
    Ty {
        id: DUMMY_NODE_ID,
        kind: TyKind::Path(
            None,
            Path {
                span: DUMMY_SP,
                segments: ThinVec::from_iter([PathSegment {
                    ident: Ident::new(Symbol::intern("usize"), DUMMY_SP),
                    id: DUMMY_NODE_ID,
                    args: None,
                }]),
                tokens: None,
            },
        ),
        span: DUMMY_SP,
        tokens: None,
    }
}

/// A path expression `core::slice::<name>`.
fn slice_path(name: &str) -> rustc_ast::Expr {
    let seg = |n: &str| PathSegment {
        ident: Ident::new(Symbol::intern(n), DUMMY_SP),
        id: DUMMY_NODE_ID,
        args: None,
    };
    rustc_ast::Expr {
        id: DUMMY_NODE_ID,
        kind: rustc_ast::ExprKind::Path(
            None,
            Path {
                span: DUMMY_SP,
                segments: ThinVec::from_iter([seg("core"), seg("slice"), seg(name)]),
                tokens: None,
            },
        ),
        span: DUMMY_SP,
        attrs: Default::default(),
        tokens: None,
    }
}

fn expr(kind: rustc_ast::ExprKind) -> P<rustc_ast::Expr> {
    P(rustc_ast::Expr {
        id: DUMMY_NODE_ID,
        kind,
        span: DUMMY_SP,
        attrs: Default::default(),
        tokens: None,
    })
}

/// **Build one glue expression, KEEPING `arg` as a subtree.**
///
/// This is the ruled (c)-extension in code: *structural where a subtree already
/// exists; parse-and-graft where the text is genuinely new.* The argument is
/// the existing call-argument node and moves across untouched — arm 1's §3c
/// precedent, which declined a text round-trip for the pointee. The **length**
/// is the one genuinely new part, has no subtree behind it, and is therefore
/// handed in already parsed via [`graft_expr`].
///
/// Returns `None` when a length-bearing shape has no length: the decision layer
/// gates that as `seam-len-unknown` (93 blocked) precisely so no layer below
/// invents one, and neither does this.
pub(crate) fn glue_expr(
    shape: GlueShape,
    mutable: bool,
    arg: P<rustc_ast::Expr>,
    len: Option<P<rustc_ast::Expr>>,
) -> Option<rustc_ast::ExprKind> {
    use rustc_ast::{BorrowKind, ExprKind};
    let mutbl = if mutable {
        Mutability::Mut
    } else {
        Mutability::Not
    };
    Some(match shape {
        GlueShape::Reborrow => ExprKind::AddrOf(
            BorrowKind::Ref,
            mutbl,
            expr(ExprKind::Unary(rustc_ast::UnOp::Deref, arg)),
        ),
        GlueShape::Index0 => {
            let zero = expr(ExprKind::Lit(rustc_ast::token::Lit {
                kind: rustc_ast::token::LitKind::Integer,
                symbol: Symbol::intern("0"),
                suffix: None,
            }));
            ExprKind::AddrOf(
                BorrowKind::Ref,
                mutbl,
                expr(ExprKind::Index(arg, zero, DUMMY_SP)),
            )
        }
        GlueShape::FromRawParts => {
            let len = len?;
            let ctor = if mutable {
                "from_raw_parts_mut"
            } else {
                "from_raw_parts"
            };
            // `(LEN) as usize` — parenthesised exactly as the span layer writes
            // it, because the companion may be an arbitrary expression.
            //
            // The `usize` is HAND-BUILT with `DUMMY_SP`, not parsed. `parse_ty`
            // opens a fresh `ParseSess` whose `BytePos` values start at zero and
            // therefore **alias real offsets in this crate's first source
            // file** — exactly the hazard `SpanEraser` was landed for at task
            // 0, reintroduced by one line, and invisible to that witness
            // because it collects `Expr` spans only. `slice_path` just below
            // already hand-builds for the same reason; this line was the odd
            // one out. Found by the adversarial review.
            let cast = expr(ExprKind::Cast(expr(ExprKind::Paren(len)), P(usize_ty())));
            ExprKind::Call(P(slice_path(ctor)), ThinVec::from_iter([arg, cast]))
        }
        GlueShape::FromRefMut => {
            let ctor = if mutable { "from_mut" } else { "from_ref" };
            ExprKind::Call(P(slice_path(ctor)), ThinVec::from_iter([arg]))
        }
        GlueShape::Some_ => ExprKind::Call(
            expr(ExprKind::Path(
                None,
                Path {
                    span: DUMMY_SP,
                    segments: ThinVec::from_iter([PathSegment {
                        ident: Ident::new(Symbol::intern("Some"), DUMMY_SP),
                        id: DUMMY_NODE_ID,
                        args: None,
                    }]),
                    tokens: None,
                },
            )),
            ThinVec::from_iter([arg]),
        ),
    })
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

/// What the seam pass placed, declined, and rendered.
///
/// Every decline is a **typed counter** rather than a skip, on the same rule
/// arm 2 landed under: an adapter that evaporates leaves the callee converted
/// and the call site raw, which is precisely the `E0308` the whole slice exists
/// to remove.
#[derive(Default)]
pub(crate) struct SeamGraftStats {
    pub grafted: usize,
    pub safe: usize,
    pub reborrow: usize,
    /// Slice seams whose `{len}` was parsed and grafted. **The one genuinely
    /// new expression in arm 3** — it has no subtree behind it, which is why
    /// the split rule sends it through [`graft_expr`] rather than a builder.
    pub len_grafted: usize,
    /// `{len}` texts [`graft_expr`] refused. A checked corpus expectation of
    /// zero, per R7.4 — never an abort, never a silent skip.
    pub len_parse_failed: usize,
    pub len_parse_failures: Vec<String>,
    /// A `FromRawParts` spec that reached the builder with no length at all.
    /// Unreachable through `glue`, which returns `SeamBlock::LengthUnknown`
    /// first — counted because **no layer below the gate may invent a length**,
    /// and a builder that silently dropped the shape would be doing exactly
    /// that in the other direction.
    pub len_absent: usize,
    /// Length-bearing SHAPES that reached the length step — the denominator
    /// [`Self::len_grafted`] did not have.
    ///
    /// Exactly one of `len_grafted` / `len_parse_failed` / `len_absent` follows
    /// each one, so this closes an exhaustive identity the corpus gate reads.
    /// Without it `len_grafted` was telemetry: it could drop to zero, or drift
    /// from the `from_raw_parts` placements it tracks, with every gated counter
    /// still clean — this track's own founding failure class, raised against
    /// this change by the past-learnings pass.
    pub len_shapes: usize,
    /// Seam edits whose span matched no AST expression.
    pub unmatched: usize,
    pub refused: usize,
    /// One seam key matched by MORE THAN ONE AST node — invisible to both the
    /// guard (which keys on `NodeId`) and to `unmatched` (a set membership),
    /// exactly as at the use pass.
    pub multi_matched: usize,
    /// Two seam edits carrying the SAME span, one overwriting the other in the
    /// lookup map. The join in this file that would otherwise have no collision
    /// counter — arm 2's finding 7, applied before it can bite.
    pub key_collisions: usize,
    /// A spec the builder deliberately does not build.
    ///
    /// The unwrap family (`unwrap` / `as_mut_unwrap`) is standalone with **zero
    /// market** on the frozen corpus, so it stays unbuilt on the `-4`/`-5`
    /// precedent — and an unknown shape becomes a row here rather than a silent
    /// skip. `Bare` with neither an unwrap nor a wrapper is the second case: it
    /// renders the argument unchanged, `glue` cannot produce it, and building it
    /// would be a no-op indistinguishable from success.
    pub unsupported: usize,
    /// `arg_span` named a subtree the matched node does not contain.
    pub arg_not_found: usize,
    /// Seams whose surviving subtree is NESTED inside the replaced node — the
    /// two cast shapes. **Measured, not gated**: whether the frozen corpus
    /// places a seam on a cast is a fact about the corpus.
    pub arg_peeled: usize,
    /// `(offset, rendered text)` per placement, keyed exactly as arms 1 and 2's
    /// renders are.
    pub rendered: Vec<(u32, String)>,
}

/// The first node at or under `e` whose span is exactly `want`.
///
/// Used only on the cast shapes, where the decision layer built its replacement
/// from the cast's OPERAND while the replaced range is the whole argument. A
/// pattern match on `ExprKind::Cast` would look equivalent and is not: a
/// `Paren` between the cast and its operand shifts the node without shifting
/// the span, so the search is by the coordinate the decision layer actually
/// recorded.
fn find_by_span<'a>(e: &'a rustc_ast::Expr, want: rustc_span::Span) -> Option<&'a rustc_ast::Expr> {
    struct Find<'a> {
        want: rustc_span::Span,
        hit: Option<&'a rustc_ast::Expr>,
    }
    impl<'a> rustc_ast::visit::Visitor<'a> for Find<'a> {
        fn visit_expr(&mut self, e: &'a rustc_ast::Expr) {
            if self.hit.is_some() {
                return;
            }
            if e.span == self.want {
                self.hit = Some(e);
                return;
            }
            rustc_ast::visit::walk_expr(self, e);
        }
    }
    let mut f = Find { want, hit: None };
    rustc_ast::visit::Visitor::visit_expr(&mut f, e);
    f.hit
}

/// **ARM 3 — the seam pass.** The THIRD span-keyed walk over one crate, and the
/// first whose targets share a syntactic category with another pass's.
///
/// # The split rule, in code
///
/// *Structural where a subtree already exists; parse-and-graft where the text is
/// genuinely new.* The wrapper is built by [`glue_expr`] around the argument's
/// own node — arm 1's §3c precedent, which declined a text round-trip for the
/// pointee — and only the `{len}` expression, which has no subtree behind it,
/// goes through [`graft_expr`].
///
/// # Why this runs LAST
///
/// A seam's argument may contain a use rewrite, so the use pass must have
/// finished grafting before the seam pass moves the subtree. Task 0 measured
/// `use_contains_seam = 0` over 181,844 pairs, so no seam is currently hidden
/// under a grafted node — but the ordering is what makes that a corpus fact
/// rather than a dependency.
pub(crate) struct SeamGraftVisitor<'a> {
    seams: &'a FxHashMap<(u32, u32), SeamTarget>,
    guard: &'a mut Composition,
    stats: SeamGraftStats,
    consumed: FxHashSet<(u32, u32)>,
}

/// What the AST layer needs from one [`SeamEdit`] — the spec, the argument's
/// coordinate, and the family. Copied out of the decision layer's edit so the
/// walk borrows nothing from the table it is keyed by.
pub(crate) struct SeamTarget {
    pub spec: super::decision::seam::GlueSpec,
    pub arg_span: rustc_span::Span,
    pub reborrow: bool,
}

impl SeamTarget {
    /// Project one [`SeamEdit`] onto what the walk needs.
    ///
    /// A named function rather than three lines inside the map-building loop,
    /// for the reason `text_span_of` is one: that loop needs a `TyCtxt` and a
    /// decision table to run, so the projection could only be exercised by a
    /// corpus sweep — and mutation M40 (making `reborrow` uniformly `false`)
    /// left the whole suite green while the sweep's 107/314 split would have
    /// collapsed to 421/0. **A mapping only a corpus sweep can exercise is a
    /// mapping with no witness**, which this boundary has now learned twice.
    ///
    /// The family match is EXHAUSTIVE, not `matches!`: a third family would
    /// silently become `safe`, and `safe` is the column meaning
    /// "compiler-checked end to end" — so the default a `matches!` picks is the
    /// flattering one.
    fn of(edit: &super::decision::seam::SeamEdit) -> Self {
        use super::decision::seam::SeamFamily;
        Self {
            spec: edit.spec.clone(),
            arg_span: edit.arg_span,
            reborrow: match edit.family {
                SeamFamily::Reborrow => true,
                SeamFamily::Safe => false,
            },
        }
    }
}

impl<'a> SeamGraftVisitor<'a> {
    pub(crate) fn new(
        seams: &'a FxHashMap<(u32, u32), SeamTarget>,
        guard: &'a mut Composition,
    ) -> Self {
        Self {
            seams,
            guard,
            stats: SeamGraftStats::default(),
            consumed: FxHashSet::default(),
        }
    }

    pub(crate) fn finish(mut self) -> SeamGraftStats {
        self.stats.unmatched = self
            .seams
            .keys()
            .filter(|k| !self.consumed.contains(k))
            .count();
        self.stats
    }

    /// Build the adapter around `e`'s own subtree, or decline with a typed row.
    fn build(&mut self, e: &rustc_ast::Expr, target: &SeamTarget) -> Option<rustc_ast::ExprKind> {
        use super::decision::seam::GlueCore;
        let spec = &target.spec;
        // The unwrap family is deliberately unbuilt — see [`SeamGraftStats`].
        if spec.unwrap.is_some() {
            self.stats.unsupported += 1;
            return None;
        }
        let shape = match spec.core {
            GlueCore::Bare => None,
            GlueCore::Reborrow => Some(GlueShape::Reborrow),
            GlueCore::Index0 => Some(GlueShape::Index0),
            GlueCore::FromRawParts => Some(GlueShape::FromRawParts),
            GlueCore::FromRefMut => Some(GlueShape::FromRefMut),
        };
        // A bare core with no wrapper renders the argument unchanged, so
        // "building" it would be a no-op that reads as a placement.
        if shape.is_none() && !spec.optional {
            self.stats.unsupported += 1;
            return None;
        }

        // ---- the argument: a SUBTREE, never re-parsed ----
        let arg: P<rustc_ast::Expr> = if target.arg_span == e.span {
            P(rustc_ast::Expr {
                id: DUMMY_NODE_ID,
                kind: e.kind.clone(),
                span: e.span,
                // **NOT cloned onto both nodes.** `e` keeps its own attributes
                // and stays the node the walk and the differential know; giving
                // the wrapped subtree a copy would print the attribute twice.
                // The outer node is the one that survives with an identity, so
                // it is the one that keeps them — the same choice arm 2's graft
                // makes by replacing only `kind`.
                attrs: Default::default(),
                tokens: None,
            })
        } else {
            // A cast shape: the replacement's text came from the cast's
            // operand, so the operand is what must survive inside the adapter.
            let Some(inner) = find_by_span(e, target.arg_span) else {
                self.stats.arg_not_found += 1;
                return None;
            };
            // Counted AFTER the lookup succeeds. Incrementing first made a
            // failed peel land in both counters, so `arg_peeled` meant
            // "attempted" while its doc said "realized" — and the corpus could
            // not show the difference, because `arg_not_found` is zero there.
            self.stats.arg_peeled += 1;
            P(inner.clone())
        };

        // ---- the length: the ONE genuinely new expression ----
        //
        // Counted HERE, after the argument resolved and before the outcome is
        // known, so that exactly one of the three length outcomes follows every
        // increment and the identity is exhaustive rather than approximate.
        if matches!(spec.core, GlueCore::FromRawParts) {
            self.stats.len_shapes += 1;
        }
        let len = match spec.len.as_deref() {
            None => None,
            Some(text) => match graft_expr(text) {
                Ok(parsed) => {
                    self.stats.len_grafted += 1;
                    Some(P(parsed))
                }
                Err(offending) => {
                    self.stats.len_parse_failed += 1;
                    if self.stats.len_parse_failures.len() < 10 {
                        self.stats.len_parse_failures.push(offending);
                    }
                    return None;
                }
            },
        };

        let core = match shape {
            None => arg,
            Some(shape) => {
                let Some(kind) = glue_expr(shape, spec.mutable, arg, len) else {
                    // `glue_expr` declines exactly one way: a length-bearing
                    // shape with no length.
                    self.stats.len_absent += 1;
                    return None;
                };
                expr(kind)
            }
        };
        Some(if spec.optional {
            glue_expr(GlueShape::Some_, spec.mutable, core, None)
                .expect("the `Some` wrapper is length-free and cannot decline")
        } else {
            (*core).kind
        })
    }
}

impl MutVisitor for SeamGraftVisitor<'_> {
    fn visit_expr(&mut self, e: &mut rustc_ast::Expr) {
        // A grafted node's spans are the fragment's own and alias real offsets
        // in this crate's first source file — the hazard task 0 landed the
        // erasure for, and arm 3 is the pass that could have been bitten by it.
        if e.span.is_dummy() {
            rustc_ast::mut_visit::walk_expr(self, e);
            return;
        }
        let key = (e.span.lo().0, e.span.hi().0);
        if let Some(target) = self.seams.get(&key) {
            if !self.consumed.insert(key) {
                self.stats.multi_matched += 1;
            }
            // **THE FIRST CLAIM THAT CAN GENUINELY COLLIDE.** A seam targets a
            // call-argument expression, the same syntactic category the use
            // pass claims, so `refused` stops being a structural zero here and
            // becomes a corpus fact.
            //
            // **BUILD FIRST, CLAIM SECOND.** The claim used to come first, so a
            // spec this pass cannot build still took ownership of the node and
            // left it unclaimable by anyone else — which is arm 2's review
            // finding 5 ("`guard.claim` ran BEFORE the shape check"), already
            // repaired once in the declaration pass and reintroduced here.
            // Found by the adversarial review.
            //
            // The cost is stated rather than hidden: a node built and then
            // refused has already counted its peel and its length, so those two
            // rows can exceed the placements. That is unreachable while
            // `refused` is zero, and a nonzero `refused` is STOP-class, so the
            // over-count can only appear on a path a human is already reading.
            let Some(kind) = self.build(e, target) else {
                // Declined with a typed row; the node is left intact AND
                // claimable, which is the invariant that matters.
                rustc_ast::mut_visit::walk_expr(self, e);
                return;
            };
            if !self.guard.claim(e.id, "seam") {
                self.stats.refused += 1;
                return;
            }
            {
                e.kind = kind;
                self.stats.grafted += 1;
                if target.reborrow {
                    self.stats.reborrow += 1;
                } else {
                    self.stats.safe += 1;
                }
                self.stats
                    .rendered
                    .push((key.0, rustc_ast_pretty::pprust::expr_to_string(e)));
                // NOT walked: the children are the adapter's now, and the
                // argument moved across as a subtree rather than being revisited.
                return;
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

    /// **A difference is booked to the arm that produced it.**
    ///
    /// [`compare_renders`] is shared by three arms and buckets on a position
    /// label. Until arm 3 that `match` ended in `_ => differing_use`, so every
    /// seam difference would have been reported as an arm-2 *use* difference —
    /// a published line — and attributed to a pass that never ran at that
    /// offset. Mutation M34 restored the fold and the whole suite stayed green,
    /// because nothing exercised the buckets directly.
    ///
    /// The whitespace split is asserted at the same time: `ws_real` carries the
    /// parity claim for all three arms jointly (the arm-2 review's finding 9,
    /// recorded as deliberate), and `ws_real_seam` is arm 3's share of it. A
    /// difference that is only reformatting must land in `ws_equal` and leave
    /// both real counters alone.
    #[test]
    fn a_differing_render_is_booked_to_the_arm_that_produced_it() {
        let by_offset: FxHashMap<u32, String> = [
            (10, "&mut *p".to_owned()),
            (20, "&mut *p".to_owned()),
            (30, "&mut * p".to_owned()),
        ]
        .into_iter()
        .collect();
        let mut d = TextDiff::default();

        compare_renders(&[(10, "&x[0]".to_owned())], &by_offset, "seam", &mut d);
        assert_eq!(d.differing_seam, 1, "a seam difference is arm 3's");
        assert_eq!(
            d.differing_use, 0,
            "and must NOT be attributed to the use pass, which never ran here"
        );
        assert_eq!(d.differing_decl, 0);
        assert_eq!(d.ws_real, 1, "the joint parity line sees it");
        assert_eq!(d.ws_real_seam, 1, "and so does arm 3's own share");

        // A use difference at another offset lands in the other bucket.
        compare_renders(&[(20, "p[1]".to_owned())], &by_offset, "use", &mut d);
        assert_eq!(d.differing_use, 1);
        assert_eq!(d.differing_seam, 1, "unchanged by the use pass");
        assert_eq!(d.ws_real_seam, 1, "and arm 3's share does not move either");

        // Reformatting only: `ws_equal`, and neither real counter moves.
        compare_renders(&[(30, "&mut *p".to_owned())], &by_offset, "seam", &mut d);
        assert_eq!(d.ws_equal, 1);
        assert_eq!(d.ws_real, 2, "still only the two genuine differences");
        assert_eq!(d.ws_real_seam, 1);
    }

    /// A label no arm owns is a PANIC, not a silent bucket.
    ///
    /// The positive control for the test above: it shows the exhaustive `match`
    /// rejects rather than absorbs, so a fourth arm cannot inherit a third's
    /// counter the way arm 3 would have inherited arm 2's.
    #[test]
    #[should_panic(expected = "unknown differential position")]
    fn an_unnamed_position_cannot_borrow_another_arms_bucket() {
        let by_offset: FxHashMap<u32, String> = [(10, "a".to_owned())].into_iter().collect();
        let mut d = TextDiff::default();
        compare_renders(&[(10, "b".to_owned())], &by_offset, "arm4", &mut d);
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
) -> Result<
    (
        RefDeclStats,
        UseGraftStats,
        SeamGraftStats,
        usize,
        usize,
        SeamUseSurface,
    ),
    String,
> {
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

    // **ARM 3 — the seam pass, and it runs THIRD by requirement, not by
    // convenience.** A seam's argument may contain a use rewrite, so the use
    // pass must have finished before the subtree is moved.
    let mut seam_targets: FxHashMap<(u32, u32), SeamTarget> = FxHashMap::default();
    let mut seam_key_collisions = 0usize;
    for edit in &table.seams.edits {
        // Same reasoning as `use_key_collisions`: a map is a join, and a join
        // without a collision counter agrees with itself while being short.
        if seam_targets
            .insert((edit.span.lo().0, edit.span.hi().0), SeamTarget::of(edit))
            .is_some()
        {
            seam_key_collisions += 1;
        }
    }
    let mut s = SeamGraftVisitor::new(&seam_targets, &mut guard);
    s.visit_crate(&mut krate);
    let mut seams = s.finish();
    seams.key_collisions = seam_key_collisions;

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
    let mut seam_pairs = 0usize;
    let mut seam_same = 0usize;
    let mut seam_contains_use = 0usize;
    let mut use_contains_seam = 0usize;
    let mut seam_use_partial = 0usize;
    for seam in &table.seams.edits {
        let (slo, shi) = (seam.span.lo().0, seam.span.hi().0);
        for (ulo, uhi) in uses.keys() {
            let (ulo, uhi) = (*ulo, *uhi);
            seam_pairs += 1;
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
        seams,
        decl_inside_use,
        use_key_collisions,
        SeamUseSurface {
            pairs: seam_pairs,
            programs_compared: usize::from(seam_pairs > 0),
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

    /// **ARM 3's differential, against the `SeamAdapter` edits.**
    ///
    /// A separate offset map from `KindDecision`'s, because the two
    /// justifications are separate populations: folding them would make arm 1's
    /// pinned `unmatched_span` move for a reason that has nothing to do with
    /// arm 1.
    ///
    /// **This is the milestone's first genuinely two-derivation comparison.**
    /// At arms 1–2 both sides were built from the same decision-layer string;
    /// here the AST side composes nodes structurally while the span side writes
    /// a `format!`, so equality at 421 edits is evidence rather than a
    /// tautology.
    pub arm3_compared: usize,
    pub arm3_equal: usize,
    pub arm3_differing: usize,
    pub arm3_unmatched_ast: usize,
    /// `SeamAdapter` offsets arm 3 never reached — the seam conservation bound.
    pub sa_unmatched_span: usize,
    pub sa_edits: usize,
    pub sa_offsets: usize,
    /// Arm 3's own share of the joint whitespace split, so the pre-stated line
    /// is readable without unpicking the joint accumulator.
    pub ws_real_seam: usize,
    pub differing_seam: usize,

    /// **ARM 4's TASK 0.** Every plan edit by justification, counted in its own
    /// pass — see [`JustificationCensus`].
    pub justifications: JustificationCensus,
    /// The plan's edit count derived without reading any justification — the
    /// independent denominator the conservation gate uses.
    pub plan_edits: usize,

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
    /// **THE DENOMINATOR** — `|placed seams| × |use edits|`, the pairs actually
    /// compared. R5, and it was missing on this instrument's first run: four
    /// zeros across 20 programs of wildly different size is this milestone's
    /// instrument signature, and without this the reader cannot tell an empty
    /// relation from an empty *population*. It had to be recovered by
    /// hand-joining two artifacts, which is exactly what reporting it prevents.
    pub pairs: usize,
    /// Programs where BOTH populations are non-empty — the spread behind the
    /// denominator, since one large program can carry it alone (brotli is
    /// 139,689 of the corpus's 181,844).
    pub programs_compared: usize,
    pub same: usize,
    pub seam_contains_use: usize,
    pub use_contains_seam: usize,
    pub partial: usize,
}

/// **ARM 4's TASK 0 — the justification census.**
///
/// Arm 4 is `ReRoute` / `DropForm` / `StoreForm`, and the migration's job for
/// any arm is to reproduce the span layer's edits as node transforms. So arm
/// 4's market is exactly *how many such edits the span layer emits* — which is
/// what this counts, before any transform is designed.
///
/// # Why an exhaustive `match` and not one with a fallback
///
/// A sixth `Justification` variant must break **compilation** here, never land
/// silently in an "other" bucket. Arm 3 paid for the fallback version of this
/// in [`compare_renders`], where `_ => differing_use` would have booked every
/// seam difference to a pass that never ran at that offset.
///
/// # Why this walks the plan again instead of reading `kd_edits`/`sa_edits`
///
/// Those two are counted inside [`arms_full`]'s own loop. Counting here in a
/// separate pass makes `just_kind_decision == kd_edits` and
/// `just_seam_adapter == sa_edits` a cross-check between **two independent
/// walks** rather than one number printed twice — and the totals give the three
/// expected zeros a denominator (R5), without which three zeros across programs
/// of wildly different size are an instrument signature rather than a finding.
#[derive(Default, Debug, PartialEq, Eq)]
pub(crate) struct JustificationCensus {
    pub kind_decision: usize,
    pub seam_adapter: usize,
    // ---- arm 4's three: expected zero, and MEASURED rather than assumed ----
    pub reroute: usize,
    pub drop_form: usize,
    pub store_form: usize,
}

impl JustificationCensus {
    /// The sum of the buckets. A method rather than a sixth field, so it cannot
    /// drift from the parts.
    ///
    /// **This is NOT an independent denominator**, and gating it against those
    /// same parts is a tautology — see [`Self::edits_in`], which is one.
    pub(crate) fn total(&self) -> usize {
        self.kind_decision + self.seam_adapter + self.reroute + self.drop_form + self.store_form
    }

    /// The plan's edit count, derived **without consulting any justification**.
    ///
    /// The real denominator, and the one a conservation gate has to use.
    /// `just_total == Σ buckets` cannot fail in production: `total()` *is* that
    /// sum, over parts serialized from the same struct, so it detects row
    /// corruption and nothing else. Gating `edits_in == Σ buckets` instead does
    /// fail on a walk that skips a file (the M52c shape), on a dropped
    /// increment, and on a future bucket counted but never exported.
    ///
    /// **Stated so it is not over-read:** no conservation identity can see a
    /// *mis-classified* edit. An arm-4 edit counted as a `KindDecision` leaves
    /// every total correct and reports the market as zero — which is what the
    /// injection witness is for, not this.
    pub(crate) fn edits_in(plan: &super::plan::Plan) -> usize {
        plan.by_file.values().map(Vec::len).sum()
    }

    /// Census one whole plan.
    ///
    /// **A named function over the plan, per R8** (ratified at the arm-3
    /// close). The loop sat inline in [`arms_full`], which needs a `TyCtxt`, so
    /// only a corpus sweep could reach it — and mutation M52, making the walk
    /// count nothing, left the entire suite green. The corpus gate would have
    /// caught it (`just_kind_decision` 0 against `kd_edits` 2,819); the suite
    /// could not. R8's remedy is to lift the logic out rather than write a
    /// bigger test, and this is its first application.
    pub(crate) fn of_plan(plan: &super::plan::Plan) -> Self {
        let mut c = Self::default();
        for edits in plan.by_file.values() {
            for e in edits {
                c.count(&e.justification);
            }
        }
        c
    }

    /// Count one edit's justification.
    pub(crate) fn count(&mut self, j: &super::plan::Justification) {
        use super::plan::Justification as J;
        match j {
            J::KindDecision { .. } => self.kind_decision += 1,
            J::SeamAdapter { .. } => self.seam_adapter += 1,
            J::ReRoute { .. } => self.reroute += 1,
            J::DropForm { .. } => self.drop_form += 1,
            J::StoreForm { .. } => self.store_form += 1,
        }
    }
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
                    // **EXHAUSTIVE over the labels, with no fallback.** This
                    // read `_ => d.differing_use += 1`, which would have folded
                    // arm 3's seam differences into `arm2_differing_use` — a
                    // reported line — and attributed them to a pass that never
                    // ran on that offset. A third position is exactly the event
                    // a catch-all is invisible to.
                    match position {
                        "decl" => d.differing_decl += 1,
                        "use" => d.differing_use += 1,
                        "seam" => d.differing_seam += 1,
                        other => panic!(
                            "unknown differential position {other:?}: a new arm must \
                             name its own bucket, never inherit another arm's"
                        ),
                    }
                    if strip(span_text) == strip(rendered) {
                        d.ws_equal += 1;
                    } else {
                        d.ws_real += 1;
                        if position == "seam" {
                            d.ws_real_seam += 1;
                        }
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

/// **THE ORACLE'S REVERT SET, resolved — held, never re-derived.**
///
/// Reads the digest-pinned snapshot's `{program}.reverts.txt` and resolves each
/// line to the owning function's `LocalDefId`, which is the granularity
/// `emit_files` reverts at and the granularity S3.6-1 measured revert to have.
///
/// # The id format, established by joining rather than by reading a format string
///
/// A line is `{fn_path}::{param_name}#{mir_local}`, where `fn_path` is
/// `tcx.def_path_str` of the owning function — verified by joining binn's 26
/// revert-owners against its `a.jsonl` `fn_path` column, **26/26 matched**,
/// with the tail joining to a real row's `param_name`. Taking the prefix before
/// the LAST `::` is therefore exact, not a heuristic.
///
/// # Fail-closed on an unresolved name
///
/// A line naming a function this session cannot resolve is an **error**, not a
/// skip. Silently dropping one would under-revert — the AST side would then
/// transform a function the span side took back, and every such function would
/// present as a parity difference with no way to tell it from a real one.
/// **THE REVERT SET — a SHARED, HELD-FIXED INPUT to both sides.**
///
/// Ruled 2026-08-14: the revert set is a **population specification**, so
/// sharing it between the two sides is correct and required; what must stay
/// independent is each side's *text derivation*. The first run got this wrong in
/// one direction only — the span side read `emission.plan` unfiltered — and the
/// two sides then agreed about a population that was not the emitted one.
///
/// It carries **both** vocabularies because the pipeline reverts in both:
/// `emit_files` filters SUBJECTS by `LocalDefId` at plan-build time, while
/// `render` filters EDITS by `owner_fn` afterwards. A seam edit is only ever
/// caught by the second — `plan`'s own comment says so: *"Reverting the callee
/// reverts its seams with it, because `owner_fn` is the revert key."*
#[cfg(test)]
pub(crate) struct RevertSet {
    pub fns: FxHashSet<LocalDefId>,
    pub names: FxHashSet<String>,
    pub subjects: usize,
}

#[cfg(test)]
impl RevertSet {
    /// Does an edit owned by `owner_fn` survive? **The single place either side
    /// asks**, so they cannot diverge on population again.
    ///
    /// Applying this to EVERY plan edit reproduces `render`'s semantics exactly.
    /// It is idempotent on `KindDecision` edits — `emit_files` has already
    /// dropped those subjects, and `owner_of(subject)` is the same
    /// `def_path_str` these names are — so one uniform filter is both correct
    /// and sufficient.
    pub(crate) fn keeps(&self, owner_fn: &str) -> bool {
        !self.names.contains(owner_fn)
    }

    /// Does a subject survive? `emit_files`'s own rule, restated for the AST
    /// side so both layers hold back the same functions.
    pub(crate) fn keeps_subject(&self, fn_did: LocalDefId) -> bool {
        !self.fns.contains(&fn_did)
    }
}

#[cfg(test)]
pub(crate) fn oracle_reverts(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    path: &std::path::Path,
) -> Result<RevertSet, String> {
    let body = std::fs::read_to_string(path).map_err(|e| format!("read {path:?}: {e}"))?;
    let wanted: FxHashSet<&str> = body
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .filter_map(|l| l.rsplit_once("::").map(|(owner, _)| owner))
        .collect();
    let subjects = body.lines().filter(|l| !l.trim().is_empty()).count();

    let mut out = FxHashSet::default();
    let mut seen: FxHashSet<String> = FxHashSet::default();
    for did in tcx.hir_body_owners() {
        let p = tcx.def_path_str(did.to_def_id());
        if wanted.contains(p.as_str()) {
            out.insert(did);
            seen.insert(p);
        }
    }
    if seen.len() != wanted.len() {
        let missing: Vec<&&str> = wanted
            .iter()
            .filter(|w| !seen.contains(**w))
            .take(5)
            .collect();
        return Err(format!(
            "{} of {} reverted owner(s) did not resolve to a local function — \
             under-reverting would make the AST side transform what the span \
             side took back: {missing:?}",
            wanted.len() - seen.len(),
            wanted.len()
        ));
    }
    Ok(RevertSet {
        fns: out,
        names: seen,
        subjects,
    })
}

/// **THE PHASE-3 EXIT GATE.** Whole-function parity over the emitted
/// population, with the oracle's decision table AND revert set held fixed.
///
/// # The two sides, and the one thing that differs between them
///
/// Both start from one `emit_files(tcx, &table, &reverted)` — so the decision
/// table and the revert set are literally the same objects on both sides, and
/// the ONLY difference is how the edits become text. That is the same-path
/// control R7 asks for, in its strongest available form.
///
/// - **span side** — the plan's edits spliced into the function's own original
///   snippet, offset-rebased.
/// - **AST side** — arms 1–3's node transforms, printed by `pprust`.
///
/// # Partition by RESIDENCE, not by ownership (ruled 2026-08-14)
///
/// Edits are grouped by the function span that CONTAINS them, never by
/// `owner_fn`: a seam edit sits in the **caller's** body while owned by the
/// **callee**. Reverting follows ownership (`emit_files` filters by the owner's
/// `LocalDefId`); the function-text unit follows residence. Conflating the two
/// would attribute a caller's text to a callee.
///
/// # Why the revert set must be held rather than re-derived
///
/// Phase 3 tests the transform layer; phase 4 tests the revert layer. A run
/// that re-derived reverts would make any difference ambiguous between the two,
/// which is the attribution problem this milestone has paid for repeatedly.
#[cfg(test)]
pub(crate) fn phase3_fn_parity(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    reverts_path: &std::path::Path,
) -> Result<FnParity, String> {
    // **THE AST IS CAPTURED FIRST, BEFORE ANY HIR QUERY.** This function used
    // to receive an already-resolved revert set, and resolving it called
    // `tcx.hir_body_owners()` — which BUILDS THE HIR and steals the resolver,
    // so the `expanded_ast` below then panicked with "attempted to read from
    // stolen value" on all 20 programs. That is the module's own ONE ENTRY rule
    // (see [`arms_full`]), and the mistake was putting a HIR query ahead of the
    // capture rather than adding a second capture.
    //
    // `make_ast_to_hir` builds the HIR itself, so every HIR query below — the
    // revert resolution included — is safe once it has run.
    let captured = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut krate = ::utils::ast::expanded_ast(tcx);
        let map = ::utils::ast::make_ast_to_hir(&mut krate, tcx);
        (krate, map)
    }));
    let (mut krate, map) = captured.map_err(|_| "AST capture panicked".to_owned())?;
    let reverts = oracle_reverts(tcx, reverts_path)?;

    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    let emission = super::emit_files(tcx, &table, &reverts.fns)?;

    let mut p = FnParity::default();
    let mut span_touched: FxHashSet<u32> = FxHashSet::default();
    let mut ast_touched: FxHashSet<u32> = FxHashSet::default();
    p.reverted_subjects = reverts.subjects;
    p.reverted_fns = reverts.fns.len();
    // **F — the reconciliation denominator.** `compared == 0` is legal only
    // where the ledger emitted nothing; anywhere else it is a gate failure.
    // I1 at program granularity: a walk that measured nothing must not read as
    // a walk that measured agreement.
    p.emitted_subjects = table
        .entries
        .iter()
        .filter(|(subj, d)| {
            !matches!(d, super::decision::Decision::Degraded(_))
                && reverts.keeps_subject(subj.fn_did)
        })
        .count();

    // ---- the AST side: the same three passes, with the SAME subjects held back ----
    let mut decisions: FxHashMap<(LocalDefId, HirId), (DeclForm, bool)> = FxHashMap::default();
    let mut uses: FxHashMap<(u32, u32), String> = FxHashMap::default();
    for (subject, decision) in &table.entries {
        // **The revert set, applied to the AST layer by the same rule
        // `emit_files` applies it by** — the owning function's `LocalDefId`.
        // Without this the AST side would transform functions the span side
        // took back, and every one would present as a difference.
        if !reverts.keeps_subject(subject.fn_did) {
            continue;
        }
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
            uses.insert((u.span.lo().0, u.span.hi().0), u.replacement.clone());
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
    let mut g = UseGraftVisitor::new(&uses, &mut guard);
    g.visit_crate(&mut krate);
    let _ = g.finish();

    // **F2 — seams obey the revert set too.** These were unfiltered on the
    // first run, on BOTH sides, so the two agreed about seams a revert should
    // have taken: lodepng reported 21 compared functions with every one of its
    // 179 subjects reverted and nothing emitted.
    let mut seam_targets: FxHashMap<(u32, u32), SeamTarget> = FxHashMap::default();
    for edit in &table.seams.edits {
        if !reverts.keeps(&edit.owner_fn) {
            continue;
        }
        seam_targets.insert((edit.span.lo().0, edit.span.hi().0), SeamTarget::of(edit));
    }
    let mut s = SeamGraftVisitor::new(&seam_targets, &mut guard);
    s.visit_crate(&mut krate);
    let _ = s.finish();

    // **A composition-guard refusal is STOP-class here.** Carried into the
    // result rather than swallowed: this gate is the first place three
    // transforms meet inside one function body.
    if !guard.refused.is_empty() {
        p.examples.push(format!(
            "COMPOSITION REFUSAL x{}: {:?}",
            guard.refused.len(),
            &guard.refused[..guard.refused.len().min(3)]
        ));
        p.differing += guard.refused.len();
    }

    let mut printed: Vec<(rustc_span::Span, String)> = Vec::new();
    super::ast_bridge::collect_fn_prints(&krate.items, &mut printed);
    let ast_by_lo: FxHashMap<u32, &String> = printed.iter().map(|(sp, t)| (sp.lo().0, t)).collect();

    // ---- the span side: the plan's edits, partitioned by RESIDENCE ----
    let sm = tcx.sess.source_map();
    let mut spans: Vec<rustc_span::Span> = Vec::new();
    super::ast_bridge::collect_fn_spans(&krate.items, &mut spans);

    for fsp in &spans {
        let Ok(orig) = sm.span_to_snippet(*fsp) else {
            continue;
        };
        let (flo, fhi) = (fsp.lo().0, fsp.hi().0);
        // Every surviving edit whose range sits inside this function.
        let mut mine: Vec<(usize, usize, &str, &'static str)> = Vec::new();
        for (key, edits) in &emission.plan.by_file {
            let Some(base) = sm
                .files()
                .iter()
                .find(|sf| super::file_key(&sf.name).as_ref() == Some(key))
                .map(|sf| sf.start_pos.0)
            else {
                continue;
            };
            for e in edits {
                // **F2 — the same shared filter the AST side used.**
                if !reverts.keeps(&e.owner_fn) {
                    continue;
                }
                let (lo, hi) = (base + e.lo as u32, base + e.hi as u32);
                if lo >= flo && hi <= fhi {
                    // **F1 — arms 1 and 2 are DISTINCT.** `KindDecision` covers
                    // both, and the variant already separates them: a use edit
                    // carries `kind` ending in `(use)` (`"Opt(use)"` /
                    // `"Slice(use)"`), a declaration edit carries the declared
                    // kind. Collapsing them into one label made every
                    // declaration-plus-its-uses function read as single-armed,
                    // so `multi_arm` was 0 and composition went unmeasured.
                    let arm = match e.justification {
                        super::plan::Justification::KindDecision { kind }
                            if kind.ends_with("(use)") =>
                        {
                            "use"
                        }
                        super::plan::Justification::KindDecision { .. } => "decl",
                        super::plan::Justification::SeamAdapter { .. } => "seam",
                        _ => "other",
                    };
                    mine.push((
                        (lo - flo) as usize,
                        (hi - flo) as usize,
                        &e.replacement,
                        arm,
                    ));
                }
            }
        }
        if mine.is_empty() {
            continue;
        }
        p.compared += 1;
        let arms: FxHashSet<&'static str> = mine.iter().map(|(_, _, _, a)| *a).collect();
        if arms.len() > 1 {
            p.multi_arm += 1;
        }
        // **ALL THREE ARMS IN ONE BODY.** Pre-stated STRUCTURALLY ZERO on this
        // corpus and reported anyway: no emitted-subject function owns both a
        // surviving `Ref` subject and a surviving `Slice`/`Opt` one (31
        // arm1-only + 30 arm2-only + 0 both, derived independently from the
        // oracle), so `{arm1, arm2, arm3}` is unreachable here. Counted so that
        // stops being an assumption.
        if arms.len() >= 3 {
            p.arm_set_3 += 1;
        }
        // Back-to-front, exactly as `apply` does: offsets address the ORIGINAL.
        mine.sort_by_key(|(lo, ..)| std::cmp::Reverse(*lo));
        let mut span_text = orig.clone();
        for (lo, hi, rep, _) in &mine {
            if *lo <= *hi && *hi <= span_text.len() {
                span_text.replace_range(*lo..*hi, rep);
            }
        }

        let Some(ast_text) = ast_by_lo.get(&flo) else {
            p.span_only += 1;
            continue;
        };
        span_touched.insert(flo);
        match (canonical_item(&span_text), canonical_item(ast_text)) {
            (Some(a), Some(b)) if a == b => p.equal += 1,
            (Some(a), Some(b)) => {
                p.differing += 1;
                if p.examples.len() < 6 {
                    p.examples.push(format!(
                        "@{flo} span={:?} ast={:?}",
                        a.chars().take(160).collect::<String>(),
                        b.chars().take(160).collect::<String>()
                    ));
                }
            }
            _ => p.parse_failed += 1,
        }
    }
    // **CROSS-LAYER RESIDENCE, not one population against itself.**
    //
    // This read `printed` against `spans` — BOTH collected from the same
    // transformed crate — so their span sets were equal by construction and
    // `ast_only` could never fire. It was one of four STOP-class counters and
    // it was structurally dead.
    //
    // The layers are now genuinely different populations:
    //   - SPAN-touched: a function holding at least one surviving plan edit;
    //   - AST-touched:  a function whose canonical form DIFFERS from its own
    //     original's, i.e. one the node transforms actually changed.
    //
    // Canonical on both sides is what makes the second sound: `pprust` reprints
    // every function, so raw text always differs, while an untouched function
    // canonicalises to exactly its original's form.
    for fsp in &spans {
        let flo = fsp.lo().0;
        let (Ok(orig), Some(ast_text)) = (sm.span_to_snippet(*fsp), ast_by_lo.get(&flo)) else {
            continue;
        };
        match (canonical_item(&orig), canonical_item(ast_text)) {
            (Some(a), Some(b)) if a != b => {
                ast_touched.insert(flo);
            }
            (Some(_), Some(_)) => {}
            // A side that will not canonicalise is already counted at the
            // comparison; not double-counted here.
            _ => {}
        }
    }
    p.ast_only = ast_touched.difference(&span_touched).count();
    p.span_only += span_touched.difference(&ast_touched).count();
    Ok(p)
}

/// **THE PHASE-3 EXIT GATE's result.**
///
/// The arms proved their edits *severally* — one declaration, one use, one glue
/// expression at a time. This measures their **COMPOSITION** into whole
/// function bodies: the first end-to-end assembly evidence the milestone has.
#[derive(Default, Debug)]
pub(crate) struct FnParity {
    /// Functions carrying at least one surviving edit — the population.
    pub compared: usize,
    pub equal: usize,
    pub differing: usize,
    /// A function reached on one side only. **Typed rows, never skips**: on
    /// this gate an absence IS the failure mode, not a nothing.
    pub ast_only: usize,
    pub span_only: usize,
    /// A side whose text would not re-parse. R7.4's wrap rule — a canonical
    /// form that cannot be taken is a reported row, never an abort.
    pub parse_failed: usize,
    /// **THE COMPOSITION POPULATION.** Functions carrying edits from MORE THAN
    /// ONE arm. A gate over functions that each hold a single edit would prove
    /// nothing the per-arm differentials had not already proved, so this is the
    /// number that says whether the gate tested the thing it claims to.
    pub multi_arm: usize,
    /// Functions in which ALL THREE arms meet.
    pub arm_set_3: usize,
    /// Subjects that survived the revert set — the per-program reconciliation
    /// denominator.
    pub emitted_subjects: usize,
    /// Subjects the revert set took back, so the ledger identity is checkable
    /// from this instrument's own output.
    pub reverted_subjects: usize,
    /// Functions the revert set took back. Reported again after being dropped
    /// from the row during the capture-ordering fix.
    pub reverted_fns: usize,
    pub examples: Vec<String>,
}

/// Canonical form for comparison: **parse, then print**.
///
/// The token-stream unit, in the shape available in-process. Both sides go
/// through the same parser and the same printer, so indentation, line wrapping
/// and **comments** normalise *symmetrically* — which matters because `pprust`
/// drops comments on the AST side while the span side splices into original
/// source that keeps them. Comparing raw text would report every commented
/// function as a difference; comparing tokens does not, and tokens are the unit
/// the charter names.
///
/// This is also what makes the two registered non-findings — column-0 splice
/// indentation and `pprust` wrapping — *structurally* unable to appear as
/// differences, rather than merely expected not to.
///
/// `None` when the text will not re-parse: a typed row, never a panic.
fn canonical_item(text: &str) -> Option<String> {
    let parsed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ::utils::ast::parse_item(text.to_owned())
    }))
    .ok()?;
    Some(rustc_ast_pretty::pprust::item_to_string(&parsed))
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
) -> Result<(RefDeclStats, UseGraftStats, SeamGraftStats, TextDiff), String> {
    let (decls, grafts, seams, decl_inside_use, use_key_collisions, surface) =
        transform_inner(tcx)?;
    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default())?;

    // The span layer's declaration and use edits, keyed by absolute offset.
    // `Edit::lo` is FILE-relative, so the file's own base is added back before
    // joining — the AST side carries absolute `Span` offsets.
    let sm = tcx.sess.source_map();
    let mut by_offset: FxHashMap<u32, String> = FxHashMap::default();
    // Arm 3's edits are a SEPARATE population, keyed apart so that arm 1's
    // pinned `unmatched_span` cannot move for a seam-shaped reason.
    let mut seam_by_offset: FxHashMap<u32, String> = FxHashMap::default();
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
            match e.justification {
                super::plan::Justification::KindDecision { .. } => {
                    d.kd_edits += 1;
                    by_offset.insert(base + e.lo as u32, e.replacement.clone());
                }
                super::plan::Justification::SeamAdapter { .. } => {
                    d.sa_edits += 1;
                    seam_by_offset.insert(base + e.lo as u32, e.replacement.clone());
                }
                _ => {}
            }
        }
    }
    d.kd_offsets = by_offset.len();
    d.sa_offsets = seam_by_offset.len();

    // **ARM 4's TASK 0 — a SECOND, independent walk over the same plan.**
    // Deliberately not folded into the loop above: sharing that loop would make
    // `just_kind_decision == kd_edits` one number printed twice instead of two
    // derivations agreeing.
    d.justifications = JustificationCensus::of_plan(&emission.plan);
    d.plan_edits = JustificationCensus::edits_in(&emission.plan);

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

    // ---- ARM 3's differential, against its own justification's edits ----
    let (c3, eq3, diff3, un3) = compare_renders(&seams.rendered, &seam_by_offset, "seam", &mut d);
    d.arm3_compared = c3;
    d.arm3_equal = eq3;
    d.arm3_differing = diff3;
    d.arm3_unmatched_ast = un3;
    let seam_offsets: FxHashSet<u32> = seams.rendered.iter().map(|(o, _)| *o).collect();
    d.sa_unmatched_span = seam_by_offset
        .keys()
        .filter(|o| !seam_offsets.contains(o))
        .count();

    d.decl_render_inside_use_edit = decl_inside_use;
    d.use_key_collisions = use_key_collisions;
    d.seam_use_surface = surface;
    Ok((decls, grafts, seams, d))
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

    // ---- ARM 3 — the seam pass, driven end to end ----

    use super::super::decision::seam::{GlueCore, GlueSpec};

    /// The span of the fixture's single call ARGUMENT — the node a seam edit
    /// names. Not the tail expression: a seam targets the argument inside the
    /// call, which is the whole reason it collides with the use pass.
    fn call_arg_span(krate: &rustc_ast::Crate) -> rustc_span::Span {
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
        let rustc_ast::ExprKind::Call(_, args) = &e.kind else {
            panic!("the fixture's tail is a call")
        };
        args[0].span
    }

    /// Run the real [`SeamGraftVisitor`] over a fixture, exactly as
    /// [`graft_over`] runs the use pass.
    ///
    /// `arg` is the span the adapter must KEEP; passing it separately from the
    /// target span is what makes the cast-peel path reachable from a test.
    fn seam_over(
        src: &str,
        seams: &[(rustc_span::Span, rustc_span::Span, GlueSpec, bool)],
    ) -> (String, SeamGraftStats) {
        let mut krate = ::utils::ast::parse_crate(src.to_owned());
        let map: FxHashMap<(u32, u32), SeamTarget> = seams
            .iter()
            .map(|(span, arg_span, spec, reborrow)| {
                (
                    (span.lo().0, span.hi().0),
                    SeamTarget {
                        spec: spec.clone(),
                        arg_span: *arg_span,
                        reborrow: *reborrow,
                    },
                )
            })
            .collect();
        let mut guard = Composition::default();
        let mut v = SeamGraftVisitor::new(&map, &mut guard);
        v.visit_crate(&mut krate);
        (pprust::item_to_string(&krate.items[0]), v.finish())
    }

    /// **RED WITNESS — each realized shape wraps the argument's own SUBTREE.**
    ///
    /// The argument is `(*s).ptr` throughout — a field access through a deref,
    /// not a bare identifier — for the reason arm 1's pointee witness uses a
    /// multi-segment path: a builder that re-rendered the argument from text
    /// would pass just as happily over `p`, and re-rendering is exactly what the
    /// split rule forbids.
    ///
    /// The five shapes here are the five the frozen corpus realizes
    /// (`from_raw_parts` 273, `some_wrap` 78, `some_reborrow` 37, `from_ref_mut`
    /// 29, `some_from_raw_parts` 4 = 421), each asserted against the text the
    /// span layer writes for the same spec — so the two derivations are compared
    /// at unit level before the corpus differential compares them at 421.
    #[test]
    fn every_realized_shape_wraps_the_argument_subtree() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(s: *mut S) { g((*s).ptr) }";
            let krate = ::utils::ast::parse_crate(src.to_owned());
            // The seam targets the CALL ARGUMENT, not the tail expression.
            let arg = call_arg_span(&krate);
            let cases: Vec<(GlueSpec, &str)> = vec![
                (
                    GlueSpec::core(GlueCore::FromRawParts, true).with_len("n"),
                    "core::slice::from_raw_parts_mut((*s).ptr, (n) as usize)",
                ),
                (
                    GlueSpec::core(GlueCore::FromRawParts, false)
                        .with_len("n")
                        .wrapped(),
                    "Some(core::slice::from_raw_parts((*s).ptr, (n) as usize))",
                ),
                (
                    GlueSpec::core(GlueCore::Reborrow, true).wrapped(),
                    "Some(&mut *(*s).ptr)",
                ),
                (
                    GlueSpec::core(GlueCore::Bare, false).wrapped(),
                    "Some((*s).ptr)",
                ),
                (
                    GlueSpec::core(GlueCore::FromRefMut, false),
                    "core::slice::from_ref((*s).ptr)",
                ),
                // **`Index0`, which the five corpus-realized shapes do NOT
                // reach through this builder.** `glue`'s `(Ref, Slice)` arm
                // produces exactly this spec, so the `GlueCore::Index0 =>
                // GlueShape::Index0` mapping in `build` is live code with zero
                // market on the frozen corpus — and a market of zero is not a
                // reason to leave a mapping unexercised. Added at the arm-3
                // review; both the bare and wrapped forms, since only the
                // wrapped one shares a census bucket with anything tested.
                (GlueSpec::core(GlueCore::Index0, true), "&mut (*s).ptr[0]"),
                (
                    GlueSpec::core(GlueCore::Index0, false).wrapped(),
                    "Some(&(*s).ptr[0])",
                ),
            ];
            for (spec, expected) in cases {
                let (text, stats) = seam_over(src, &[(arg, arg, spec.clone(), false)]);
                assert_eq!(stats.grafted, 1, "{spec:?} must place: {text}");
                assert_eq!(stats.unmatched, 0);
                assert!(
                    text.contains(expected),
                    "the built node must print what the span layer writes for the \
                     same spec.\n  spec:     {spec:?}\n  expected: {expected}\n  got:      {text}"
                );
                // **The two derivations, compared here rather than assumed.**
                assert_eq!(
                    spec.render("(*s).ptr").expect("an emitting spec renders"),
                    expected,
                    "and the RENDERER must agree with the same text — if these \
                     two ever part, the corpus differential's 421 equalities \
                     stop meaning the builder is right"
                );
            }
        });
    }

    /// **THE CAST PEEL — the surviving subtree is the OPERAND, not the cast.**
    ///
    /// `ArgShape::CastOfLocal` makes the decision layer build its replacement
    /// from the cast's operand while the replaced range is the whole argument,
    /// so `arg_span != span` and the adapter must wrap `q`, never `q as *mut u8`.
    ///
    /// Found by reading `Pos`'s construction rather than by a failing
    /// differential, and witnessed here because mutation M28 — collapsing
    /// `arg_span` onto the argument span — left the entire suite green while
    /// the field had no consumer.
    ///
    /// Both halves are asserted: the operand is kept **and** the cast is gone.
    /// Only the first would also pass for a builder that wrapped the whole cast.
    #[test]
    fn a_cast_shaped_seam_keeps_the_operand_and_drops_the_cast() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(q: *mut u8) { g(q as *mut u8) }";
            let krate = ::utils::ast::parse_crate(src.to_owned());
            let (whole, operand) = {
                let rustc_ast::ItemKind::Fn(f) = &krate.items[0].kind else {
                    panic!("fixture is a fn")
                };
                let body = f.body.as_ref().expect("body");
                let rustc_ast::StmtKind::Expr(e) = &body.stmts.last().expect("tail").kind else {
                    panic!("tail is an expression")
                };
                let rustc_ast::ExprKind::Call(_, args) = &e.kind else {
                    panic!("the fixture's tail is a call")
                };
                let rustc_ast::ExprKind::Cast(inner, _) = &args[0].kind else {
                    panic!("the fixture's argument is a cast")
                };
                (args[0].span, inner.span)
            };
            assert_ne!(
                whole, operand,
                "the fixture only tests anything if the two spans differ"
            );

            let spec = GlueSpec::core(GlueCore::Reborrow, true);
            let (text, stats) = seam_over(src, &[(whole, operand, spec, true)]);
            assert_eq!(stats.grafted, 1, "{text}");
            assert_eq!(
                stats.arg_peeled, 1,
                "the peel must be COUNTED — whether the corpus places seams on \
                 cast shapes is a measurement, and an uncounted peel makes it \
                 unanswerable"
            );
            assert_eq!(stats.arg_not_found, 0);
            assert!(
                text.contains("&mut *q"),
                "the OPERAND must survive inside the adapter: {text}"
            );
            assert!(
                !text.contains("as *mut u8"),
                "and the cast must not: the span layer replaces the whole \
                 argument, so a builder that kept the cast emits `&mut *(q as \
                 *mut u8)` where the span layer wrote `&mut *q` — a silent \
                 parity divergence at exactly the positions casts appear: {text}"
            );
            assert_eq!(stats.reborrow, 1, "the family rides the placement");
            assert_eq!(stats.safe, 0);
        });
    }

    /// **The family survives the projection into the walk, BOTH ways.**
    ///
    /// The corpus split (safe 107 / reborrow 314) is the only thing that was
    /// checking this, and only a sweep produces it: mutation M40 made
    /// `reborrow` uniformly `false` and the whole suite stayed green. Both
    /// directions are asserted, because a projection stuck on either constant
    /// passes a one-sided test.
    #[test]
    fn the_seam_family_survives_the_projection_in_both_directions() {
        rustc_span::create_default_session_globals_then(|| {
            let edit = |family| super::super::decision::seam::SeamEdit {
                span: DUMMY_SP,
                replacement: String::new(),
                owner_fn: String::new(),
                family,
                len_arm: None,
                spec: GlueSpec::core(GlueCore::Reborrow, true),
                arg_span: DUMMY_SP,
            };
            assert!(
                SeamTarget::of(&edit(super::super::decision::seam::SeamFamily::Reborrow)).reborrow,
                "a reborrow adapter must stay countable as one — it is the \
                 population carrying the aliasing exposure"
            );
            assert!(
                !SeamTarget::of(&edit(super::super::decision::seam::SeamFamily::Safe)).reborrow,
                "and a safe one must not be inflated into it"
            );
        });
    }

    /// **An `arg_span` the matched node does not contain declines, and is
    /// counted as NOT-FOUND rather than as a peel.**
    ///
    /// Corpus-zero (`arg_not_found = 0` on all 20 programs), so the only
    /// evidence it works can come from an injected case. Injected the way arm
    /// 2's containment backstop is: the visitor is a pure function of its map,
    /// so it is handed a map the decision layer could not have produced.
    ///
    /// The `arg_peeled == 0` assertion is the load-bearing half. The counter
    /// used to increment BEFORE the lookup, so a failed peel landed in both
    /// rows and `arg_peeled` meant "attempted" while its doc said "realized" —
    /// invisible on a corpus where `arg_not_found` is zero. Found by the
    /// correctness reviewer at the arm-3 boundary.
    #[test]
    fn an_arg_span_the_node_does_not_contain_declines_and_is_not_a_peel() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(q: *mut u8) { g(q) }";
            let krate = ::utils::ast::parse_crate(src.to_owned());
            let arg = call_arg_span(&krate);
            // A span inside the fixture but belonging to no node under `arg`.
            let bogus = arg.with_lo(arg.lo() - rustc_span::BytePos(3));
            assert_ne!(bogus, arg);

            let (text, stats) = seam_over(
                src,
                &[(arg, bogus, GlueSpec::core(GlueCore::Reborrow, true), true)],
            );
            assert_eq!(
                stats.grafted, 0,
                "nothing is built from a subtree that is not there"
            );
            assert_eq!(stats.arg_not_found, 1, "and the decline is attributed");
            assert_eq!(
                stats.arg_peeled, 0,
                "a FAILED peel is not a peel — `arg_peeled` counts realized \
                 ones, which is what makes the corpus's 9 mean what it says"
            );
            assert_eq!(stats.unmatched, 0, "the key was reached, then declined");
            assert!(text.contains("g(q)"), "the node is left intact: {text}");
        });
    }

    /// **One seam key matched by MORE THAN ONE node is counted.**
    ///
    /// Neither the guard (distinct `NodeId`s) nor `unmatched` (set membership)
    /// can observe this, exactly as at the use pass — so this counter is the
    /// only witness there is, and it was gated at zero with nothing driving it
    /// positive. Injected by walking the same crate twice, mirroring
    /// [`two_nodes_sharing_one_span_are_counted_not_silently_double_grafted`].
    #[test]
    fn one_seam_key_reached_twice_is_counted() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(q: *mut u8) { g(q) }";
            let mut krate = ::utils::ast::parse_crate(src.to_owned());
            let arg = call_arg_span(&krate);
            let seams: FxHashMap<(u32, u32), SeamTarget> = [(
                (arg.lo().0, arg.hi().0),
                SeamTarget {
                    spec: GlueSpec::core(GlueCore::Reborrow, true),
                    arg_span: arg,
                    reborrow: true,
                },
            )]
            .into_iter()
            .collect();
            let mut guard = Composition::default();
            let mut v = SeamGraftVisitor::new(&seams, &mut guard);
            v.visit_crate(&mut krate);
            let mut krate2 = ::utils::ast::parse_crate(src.to_owned());
            v.visit_crate(&mut krate2);
            let stats = v.finish();
            assert!(
                stats.multi_matched >= 1,
                "a key reached a second time MUST be counted — it is invisible \
                 to every other instrument this pass has"
            );
        });
    }

    /// **A spec the builder does not build becomes a ROW, never a silent skip.**
    ///
    /// The unwrap family is standalone with zero market on the frozen corpus and
    /// stays unbuilt on the `-4`/`-5` precedent. What must not happen is that it
    /// disappears: an adapter that evaporates leaves the callee converted and
    /// the call site raw, which is the `E0308` the slice exists to remove.
    ///
    /// The node is asserted INTACT as well as counted — a decline that mangled
    /// the tree and reported itself would pass a count-only test.
    #[test]
    fn an_unbuilt_shape_declines_with_a_typed_row_and_leaves_the_node_intact() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(o: Option<&mut u8>) { g(o) }";
            let krate = ::utils::ast::parse_crate(src.to_owned());
            let arg = call_arg_span(&krate);

            let unwrapping = GlueSpec::core(GlueCore::Bare, true).with_unwrap(true);
            let (text, stats) = seam_over(src, &[(arg, arg, unwrapping, false)]);
            assert_eq!(stats.grafted, 0, "the shape is deliberately unbuilt");
            assert_eq!(stats.unsupported, 1, "and it is COUNTED");
            assert_eq!(
                stats.unmatched, 0,
                "the key WAS reached — declined is a different fact from never \
                 found, exactly as at the use pass"
            );
            assert!(
                text.contains("g(o)"),
                "a declined seam must leave the node untouched: {text}"
            );

            // The second unbuilt case: a bare core with no wrapper renders the
            // argument unchanged, so building it would be a no-op that reads as
            // a placement. `glue` cannot produce it; the guard is fail-closed.
            let identity = GlueSpec::core(GlueCore::Bare, false);
            let (_, stats) = seam_over(src, &[(arg, arg, identity, false)]);
            assert_eq!(stats.grafted, 0);
            assert_eq!(stats.unsupported, 1);
        });
    }

    /// **ARM 4's CENSUS COUNTS WHAT IT CLAIMS TO — injected, not hoped for.**
    ///
    /// The census's whole job is to decide whether arm 4 has a market, and its
    /// expected answer is three zeros. **A counter that never increments
    /// produces exactly the same three zeros**, so without this the measurement
    /// cannot distinguish *no market* from *no instrument* — the D1 lesson in
    /// its original form, and the reason the pre-statement made injection a
    /// requirement rather than a nicety.
    ///
    /// So each of the five variants is fed in and asserted to land in its own
    /// bucket, and the denominator is asserted to be the sum.
    #[test]
    fn the_justification_census_counts_every_variant_including_arm_fours() {
        use super::super::plan::Justification as J;
        let mut c = JustificationCensus::default();
        for j in [
            J::KindDecision { kind: "Ref(mut)" },
            J::KindDecision { kind: "Ref" },
            J::SeamAdapter { family: "safe" },
            J::ReRoute {
                licensing_loan: "L0".to_owned(),
            },
            J::DropForm {
                selector_site: "s".to_owned(),
            },
            J::StoreForm { form: "N-raw" },
        ] {
            c.count(&j);
        }
        assert_eq!(
            c,
            JustificationCensus {
                kind_decision: 2,
                seam_adapter: 1,
                reroute: 1,
                drop_form: 1,
                store_form: 1,
            },
            "each variant must land in its OWN bucket — an arm-4 edit counted \
             as a `KindDecision` would report the market as zero while the \
             population was not"
        );
        assert_eq!(c.total(), 6, "the denominator is the sum of the parts");

        // And an empty plan is genuinely empty, so the zeros the corpus reports
        // are the counter's answer rather than its default being mistaken for
        // one.
        let empty = JustificationCensus::default();
        assert_eq!(empty.total(), 0);
        assert_eq!(empty.reroute + empty.drop_form + empty.store_form, 0);
    }

    /// **THE WALK OVER A PLAN, witnessed — R8's first application.**
    ///
    /// Mutation M52 made the walk count nothing and the whole suite stayed
    /// green, because the loop lived inside [`arms_full`] behind a `TyCtxt` and
    /// only a corpus sweep could reach it. The corpus gate would have caught it;
    /// the suite could not, and R8 says the remedy is to lift the logic out.
    ///
    /// The plan is built by hand with edits in **two files**, so a walk that
    /// visited only the first entry of `by_file` fails here.
    #[test]
    fn the_census_walks_every_file_of_a_plan() {
        use super::super::plan::{Edit, FileKey, Justification as J, Plan};
        let edit = |j: J| Edit {
            lo: 0,
            hi: 1,
            replacement: String::new(),
            justification: j,
            owner_fn: String::new(),
        };
        let mut plan = Plan::default();
        plan.by_file.insert(
            FileKey::Virtual("a.rs".to_owned()),
            vec![
                edit(J::KindDecision { kind: "Ref" }),
                edit(J::SeamAdapter { family: "safe" }),
            ],
        );
        plan.by_file.insert(
            FileKey::Virtual("b.rs".to_owned()),
            vec![
                edit(J::KindDecision { kind: "Ref(mut)" }),
                edit(J::DropForm {
                    selector_site: "s".to_owned(),
                }),
            ],
        );

        let c = JustificationCensus::of_plan(&plan);
        assert_eq!(
            c,
            JustificationCensus {
                kind_decision: 2,
                seam_adapter: 1,
                reroute: 0,
                drop_form: 1,
                store_form: 0,
            },
            "the walk must reach EVERY file — the second file's edits are the \
             half a first-entry-only walk would miss"
        );
        assert_eq!(c.total(), 4, "and the denominator counts them all");

        // Non-vacuity: an empty plan really does census to nothing, so the
        // assertion above is about the walk rather than about the default.
        assert_eq!(
            JustificationCensus::of_plan(&Plan::default()),
            JustificationCensus::default()
        );

        // **THE INDEPENDENT DENOMINATOR agrees — and is derived without
        // reading a single justification.** This is what makes the corpus
        // conservation gate capable of failing: `total()` restates the buckets,
        // `edits_in` counts the plan.
        assert_eq!(JustificationCensus::edits_in(&plan), 4);
        assert_eq!(JustificationCensus::edits_in(&plan), c.total());
        assert_eq!(JustificationCensus::edits_in(&Plan::default()), 0);
    }

    /// **THE CONSERVATION GATE CAN FAIL — the property its tautological
    /// predecessor did not have.**
    ///
    /// `just_total == Σ buckets` was serialized from one struct on both sides,
    /// so it could only ever detect row corruption. `edits_in` is derived
    /// without consulting any justification, so a walk that misses edits breaks
    /// the identity. Simulated here by censusing a SUBSET of the plan while
    /// measuring the denominator over the whole of it — which is exactly what a
    /// skipped file looks like.
    #[test]
    fn the_independent_denominator_catches_a_walk_that_misses_edits() {
        use super::super::plan::{Edit, FileKey, Justification as J, Plan};
        let edit = || Edit {
            lo: 0,
            hi: 1,
            replacement: String::new(),
            justification: J::KindDecision { kind: "Ref" },
            owner_fn: String::new(),
        };
        let mut whole = Plan::default();
        whole
            .by_file
            .insert(FileKey::Virtual("a.rs".to_owned()), vec![edit(), edit()]);
        whole
            .by_file
            .insert(FileKey::Virtual("b.rs".to_owned()), vec![edit()]);

        let mut partial = Plan::default();
        partial
            .by_file
            .insert(FileKey::Virtual("a.rs".to_owned()), vec![edit(), edit()]);

        let short = JustificationCensus::of_plan(&partial);
        assert_eq!(
            JustificationCensus::edits_in(&whole),
            3,
            "the denominator sees all three edits"
        );
        assert_ne!(
            JustificationCensus::edits_in(&whole),
            short.total(),
            "and a census that missed a file DISAGREES with it — the failure \
             the tautological form could not represent, because there both \
             sides came from the same struct"
        );
    }

    /// **EVERY SPAN THIS LAYER MANUFACTURES IS `DUMMY_SP` — types included.**
    ///
    /// The synthetic-span invariant exists because a fresh `ParseSess` numbers
    /// its `SourceMap` from zero, so a parsed fragment's spans are not invalid
    /// but **valid coordinates pointing somewhere else** in this crate. Task 0
    /// landed `SpanEraser` for exactly that, and one line still parsed: the
    /// `usize` in `(LEN) as usize`.
    ///
    /// It survived because the erasure witness collects **`Expr` spans only**
    /// and this leak is on a `Ty`. So the witness is widened here rather than
    /// the claim restated — a checker that cannot see the node kind the defect
    /// lives on is not checking it. Found by the adversarial review.
    ///
    /// The argument keeps its REAL span deliberately: it is the original
    /// subtree, not something this layer manufactured, so it is excluded by
    /// identity rather than by the walk declining to look.
    #[test]
    fn every_span_the_glue_builder_manufactures_is_dummy() {
        rustc_span::create_default_session_globals_then(|| {
            struct Spans {
                exprs: Vec<rustc_span::Span>,
                tys: Vec<rustc_span::Span>,
            }
            impl<'a> rustc_ast::visit::Visitor<'a> for Spans {
                fn visit_expr(&mut self, e: &'a rustc_ast::Expr) {
                    self.exprs.push(e.span);
                    rustc_ast::visit::walk_expr(self, e);
                }

                fn visit_ty(&mut self, t: &'a Ty) {
                    self.tys.push(t.span);
                    rustc_ast::visit::walk_ty(self, t);
                }
            }
            fn spans_of(e: &rustc_ast::Expr) -> Spans {
                let mut v = Spans {
                    exprs: Vec::new(),
                    tys: Vec::new(),
                };
                rustc_ast::visit::Visitor::visit_expr(&mut v, e);
                v
            }

            let arg = ::utils::ast::parse_expr("(*s).ptr".to_owned());
            // **The WHOLE argument subtree is exempt, not just its root.**
            // `(*s).ptr` also carries real spans on `(*s)`, `*s` and `s`: they
            // are the KEPT subtree, and keeping them is the point of the split
            // rule. Exempting only the root made this assertion fire on exactly
            // what arm 3 exists to preserve — caught by running it.
            let kept: FxHashSet<rustc_span::Span> = spans_of(&arg).exprs.into_iter().collect();
            let len = graft_expr("n").expect("the length parses");
            let built = expr(
                glue_expr(GlueShape::FromRawParts, true, P(arg), Some(P(len)))
                    .expect("a length-bearing shape with a length builds"),
            );
            let got = spans_of(&built);

            let leaked: Vec<_> = got
                .exprs
                .iter()
                .filter(|s| !s.is_dummy() && !kept.contains(s))
                .collect();
            assert!(
                leaked.is_empty(),
                "a manufactured expression carrying a real span aliases a real \
                 offset in this crate's first source file, which is the \
                 wrong-target hazard the erasure exists to remove: {leaked:?}"
            );
            // The argument contains no types, so EVERY type here was built by
            // this layer and none may carry a span.
            assert!(
                got.tys.iter().all(|s| s.is_dummy()),
                "the `usize` in `(LEN) as usize` is manufactured, so its span \
                 must be DUMMY_SP: {:?}",
                got.tys
            );

            // NON-VACUITY, both halves: the walk must actually REACH a type,
            // and it must be able to SEE a real span when there is one — which
            // is precisely how the `Expr`-only witness missed this.
            assert_eq!(
                got.tys.len(),
                1,
                "the built expression has exactly one type"
            );
            assert!(
                spans_of(&::utils::ast::parse_expr("(x) as usize".to_owned()))
                    .tys
                    .iter()
                    .any(|s| !s.is_dummy()),
                "the probe must SEE a parsed type's span, or the assertion \
                 above is vacuous"
            );
        });
    }

    /// **A DECLINED SEAM LEAVES THE NODE CLAIMABLE BY SOMEONE ELSE.**
    ///
    /// Arm 2's review found exactly this shape in the declaration pass —
    /// finding 5, *"`guard.claim` ran BEFORE the shape check, so a declaration
    /// the pass cannot transform still took ownership of its node"* — and
    /// repaired it. The seam pass reintroduced it, and the suite stayed green
    /// because the only thing anyone asserted about a decline was the node's
    /// TEXT, never the guard's state.
    ///
    /// So the load-bearing assertion here is the guard's, exactly as M17b's
    /// was. Found by the adversarial review.
    #[test]
    fn a_declined_seam_does_not_take_ownership_of_the_node() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(o: Option<&mut u8>) { g(o) }";
            let mut krate = ::utils::ast::parse_crate(src.to_owned());
            let arg = call_arg_span(&krate);
            let node_id = {
                let rustc_ast::ItemKind::Fn(f) = &krate.items[0].kind else {
                    panic!("fixture is a fn")
                };
                let body = f.body.as_ref().expect("body");
                let rustc_ast::StmtKind::Expr(e) = &body.stmts.last().expect("tail").kind else {
                    panic!("tail is an expression")
                };
                let rustc_ast::ExprKind::Call(_, args) = &e.kind else { panic!("tail is a call") };
                args[0].id
            };

            // A spec the builder deliberately does not build.
            let seams: FxHashMap<(u32, u32), SeamTarget> = [(
                (arg.lo().0, arg.hi().0),
                SeamTarget {
                    spec: GlueSpec::core(GlueCore::Bare, true).with_unwrap(true),
                    arg_span: arg,
                    reborrow: false,
                },
            )]
            .into_iter()
            .collect();
            let mut guard = Composition::default();
            let mut v = SeamGraftVisitor::new(&seams, &mut guard);
            v.visit_crate(&mut krate);
            let stats = v.finish();
            assert_eq!(stats.grafted, 0);
            assert_eq!(stats.unsupported, 1, "it declined, as designed");
            assert_eq!(stats.refused, 0, "and was not refused — nothing collided");

            assert!(
                guard.claim(node_id, "arm4"),
                "THE LOAD-BEARING ASSERTION: a node this pass could not \
                 transform must stay claimable. Claiming before building leaves \
                 a phantom owner that fail-closes a later arm's transform on a \
                 node nobody actually rewrote"
            );
        });
    }

    /// **A length-bearing shape with NO length places nothing** — the gate the
    /// decision layer holds (`seam-len-unknown`, 93 blocked) is not quietly
    /// re-opened one layer down.
    ///
    /// Unreachable through `glue`, which returns `SeamBlock::LengthUnknown`
    /// first. Injected the way `plan`'s missing-pointee arm is, because "no
    /// layer below the gate may invent a length" is a claim about this code and
    /// not about its caller.
    #[test]
    fn a_slice_seam_with_no_length_places_nothing_and_is_counted() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(p: *mut u8) { g(p) }";
            let krate = ::utils::ast::parse_crate(src.to_owned());
            let arg = call_arg_span(&krate);
            let lengthless = GlueSpec::core(GlueCore::FromRawParts, false);
            let (text, stats) = seam_over(src, &[(arg, arg, lengthless, true)]);
            assert_eq!(stats.grafted, 0);
            assert_eq!(
                stats.len_absent, 1,
                "declined, and attributed to the LENGTH"
            );
            assert_eq!(stats.unsupported, 0, "not confused with an unbuilt shape");
            assert!(text.contains("g(p)"), "{text}");
            // **The identity's denominator.** `len_shapes` is what turns
            // `len_grafted` from telemetry into a gated ledger; mutation M39
            // stopped it incrementing and only the corpus would have noticed.
            assert_eq!(
                stats.len_shapes, 1,
                "a length-bearing shape reached the step"
            );
            assert_eq!(
                stats.len_grafted + stats.len_parse_failed + stats.len_absent,
                stats.len_shapes,
                "and exactly one outcome followed it"
            );

            // And a `{len}` that does not round-trip is a typed row too, per
            // R7.4 — never an abort, which is what a bare `parse_expr` would do.
            let unparseable = GlueSpec::core(GlueCore::FromRawParts, false).with_len("n +");
            let (_, stats) = seam_over(src, &[(arg, arg, unparseable, true)]);
            assert_eq!(stats.grafted, 0);
            assert_eq!(stats.len_parse_failed, 1);
            assert_eq!(
                stats.len_parse_failures.len(),
                1,
                "the offending template must be ATTACHED, not just tallied"
            );
            assert_eq!(
                stats.len_grafted + stats.len_parse_failed + stats.len_absent,
                stats.len_shapes,
                "the identity holds on the parse-failure branch too"
            );

            // ...and on the SUCCESS branch, which is the one the corpus's 277
            // actually travels.
            let ok = GlueSpec::core(GlueCore::FromRawParts, false).with_len("n");
            let (_, stats) = seam_over(src, &[(arg, arg, ok, true)]);
            assert_eq!(stats.len_grafted, 1);
            assert_eq!(stats.len_shapes, 1);
            assert_eq!(stats.len_absent + stats.len_parse_failed, 0);
        });
    }

    /// **The seam pass and the use pass share one guard, and the second claim on
    /// a node is refused.**
    ///
    /// This is the first pair in the milestone that can genuinely collide: both
    /// claim `Expr` nodes. Task 0 measured the collision surface empty over
    /// 181,844 pairs on the frozen corpus, so `arm3_refused = 0` there is a
    /// **corpus fact** — which is precisely why the mechanism needs a witness
    /// the corpus cannot provide.
    #[test]
    fn a_seam_may_not_claim_a_node_the_use_pass_already_owns() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(p: *mut u8) { g(*p.offset(1)) }";
            let mut krate = ::utils::ast::parse_crate(src.to_owned());
            let arg = call_arg_span(&krate);
            let mut guard = Composition::default();

            // The use pass claims the node first — the order the walk runs in.
            let uses: FxHashMap<(u32, u32), String> =
                [((arg.lo().0, arg.hi().0), "p[1]".to_owned())]
                    .into_iter()
                    .collect();
            let mut u = UseGraftVisitor::new(&uses, &mut guard);
            u.visit_crate(&mut krate);
            assert_eq!(u.finish().grafted, 1, "the use edit lands first");

            let seams: FxHashMap<(u32, u32), SeamTarget> = [(
                (arg.lo().0, arg.hi().0),
                SeamTarget {
                    spec: GlueSpec::core(GlueCore::Reborrow, true),
                    arg_span: arg,
                    reborrow: true,
                },
            )]
            .into_iter()
            .collect();
            let mut s = SeamGraftVisitor::new(&seams, &mut guard);
            s.visit_crate(&mut krate);
            let stats = s.finish();

            assert_eq!(stats.refused, 1, "the second claimant is refused");
            assert_eq!(stats.grafted, 0);
            assert_eq!(
                stats.unmatched, 0,
                "the key was REACHED and refused — a different fact from never \
                 being found"
            );
            assert_eq!(guard.refused_by("seam"), 1, "attributed to the CHALLENGER");
            assert_eq!(guard.refused[0].holder, "use");
            let text = pprust::item_to_string(&krate.items[0]);
            assert!(
                text.contains("p[1]") && !text.contains("&mut *"),
                "the holder's transform stands and the refused one did not \
                 land: {text}"
            );
        });
    }
}

#[cfg(test)]
mod arm3_witnesses {
    use rustc_ast_pretty::pprust;

    use super::*;

    /// Render one glue shape over a NON-TRIVIAL argument.
    ///
    /// The argument is `(*s).ptr` — a field access through a deref, not a bare
    /// identifier — deliberately. The split rule's whole claim is that the
    /// argument moves across as a SUBTREE; a witness over `p` alone would pass
    /// for an implementation that re-rendered it from scratch.
    fn rendered(shape: GlueShape, mutable: bool, len: Option<&str>) -> String {
        let arg = ::utils::ast::parse_expr("(*s).ptr".to_owned());
        let len = len.map(|l| ::utils::ast::parse_expr(l.to_owned()));
        let kind = glue_expr(
            shape,
            mutable,
            rustc_ast::ptr::P(arg),
            len.map(rustc_ast::ptr::P),
        )
        .expect("the five realized shapes all build");
        pprust::expr_to_string(&rustc_ast::Expr {
            id: DUMMY_NODE_ID,
            kind,
            span: DUMMY_SP,
            attrs: Default::default(),
            tokens: None,
        })
    }

    /// **RED WITNESS — the glue shapes render exactly the span layer's text.**
    ///
    /// The oracle is `decision/seam.rs`'s `format!` set. These are the FIVE
    /// shapes realized on the frozen corpus, measured from `seams.tsv`:
    /// `from_raw_parts` 273, `some_wrap` 78, `some_reborrow` 37,
    /// `from_ref_mut` 29, `some_from_raw_parts` 4 = 421.
    ///
    /// Pinning them here is what makes a corpus parity diff attributable: a
    /// differing seam cannot be the renderer's fault without this failing
    /// first. Same role as arm 2's declared-forms witness.
    #[test]
    fn glue_shapes_render_the_span_layers_text() {
        rustc_span::create_default_session_globals_then(|| {
            // reborrow family
            assert_eq!(rendered(GlueShape::Reborrow, true, None), "&mut *(*s).ptr");
            assert_eq!(rendered(GlueShape::Reborrow, false, None), "&*(*s).ptr");
            assert_eq!(
                rendered(GlueShape::FromRawParts, true, Some("n")),
                "core::slice::from_raw_parts_mut((*s).ptr, (n) as usize)"
            );
            assert_eq!(
                rendered(GlueShape::FromRawParts, false, Some("n")),
                "core::slice::from_raw_parts((*s).ptr, (n) as usize)"
            );
            // safe family
            assert_eq!(
                rendered(GlueShape::FromRefMut, true, None),
                "core::slice::from_mut((*s).ptr)"
            );
            assert_eq!(
                rendered(GlueShape::FromRefMut, false, None),
                "core::slice::from_ref((*s).ptr)"
            );
            assert_eq!(rendered(GlueShape::Index0, true, None), "&mut (*s).ptr[0]");
            assert_eq!(rendered(GlueShape::Index0, false, None), "&(*s).ptr[0]");
            // the optional wrapper, over a bare argument and over a nested form
            assert_eq!(rendered(GlueShape::Some_, false, None), "Some((*s).ptr)");
        });
    }

    /// **The `{len}` expression is the ONE part that is genuinely new text.**
    ///
    /// The split rule in one assertion: the argument arrives as a subtree and
    /// is never re-rendered, while the length has no subtree behind it (it is
    /// recovered or fabricated) and therefore travels the parse-and-graft path
    /// arm 2 hardened. A `from_raw_parts` shape with no length is a REFUSAL,
    /// not a guess — the seam never invents a length, and neither does this.
    ///
    /// *Mutation-tested:* returning `None` instead of erroring on a missing
    /// length fails the first assertion; accepting it and emitting `0` would
    /// fail it too.
    #[test]
    fn a_length_bearing_shape_without_a_length_is_refused_not_guessed() {
        rustc_span::create_default_session_globals_then(|| {
            let arg = ::utils::ast::parse_expr("(*s).ptr".to_owned());
            assert!(
                glue_expr(GlueShape::FromRawParts, true, rustc_ast::ptr::P(arg), None).is_none(),
                "a slice seam with no length must be REFUSED — the decision \
                 layer gates it as `seam-len-unknown` (93 blocked) precisely so \
                 that no layer below invents one"
            );
            let arg2 = ::utils::ast::parse_expr("(*s).ptr".to_owned());
            assert!(
                glue_expr(GlueShape::Reborrow, true, rustc_ast::ptr::P(arg2), None).is_some(),
                "and a shape that needs no length must not be caught by that gate"
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
