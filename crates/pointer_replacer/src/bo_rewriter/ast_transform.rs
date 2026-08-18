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

// The length's provenance is a DECISION-layer type: `finish_len` is the only
// place in this file that branches on it, and it branches on the carried value
// rather than on a re-derivation of it.
use super::decision::seam::SeamLen;

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
/// Returns `None` when a length-bearing shape has no length. After the
/// fabrication ruling the decision layer no longer *gates* on a missing length —
/// it fabricates a tagged one — but the principle this arm encodes is unchanged
/// and is now the whole of it: **no layer below the gate invents a length**, and
/// neither does this.
/// **Finish a `from_raw_parts` length expression — the ONE place the two arms
/// diverge in the AST layer** (R8: a decidable mapping, lifted out).
///
/// A licensed companion becomes `(LEN) as usize`, because the C spelling may be
/// `size_t`/`c_int`/`c_ulong` and `from_raw_parts` takes `usize`. A **fabricated**
/// extent is left bare: the named const is already `usize`, and casting it would
/// make a fabricated site textually indistinguishable from a licensed one whose
/// companion happened to be a path.
///
/// Extracted rather than written inline in the visitor because the arm-3
/// differential renders through this too. Building the cast in the test harness
/// instead would have made the harness a **second implementation** of the
/// production rule — the class this milestone's parity work exists to prevent,
/// and the shape M28/M40 were banked for.
///
/// The `usize` is HAND-BUILT with `DUMMY_SP`, never parsed: `parse_ty` opens a
/// fresh `ParseSess` whose `BytePos` values start at zero and therefore alias
/// real offsets in this crate's first source file — the hazard `SpanEraser` was
/// landed for at task 0, invisible to that witness because it collects `Expr`
/// spans only.
pub(crate) fn finish_len(seam_len: &SeamLen, parsed: rustc_ast::Expr) -> P<rustc_ast::Expr> {
    match seam_len {
        SeamLen::Licensed(_) => expr(rustc_ast::ExprKind::Cast(
            expr(rustc_ast::ExprKind::Paren(P(parsed))),
            P(usize_ty()),
        )),
        SeamLen::Fabricated => P(parsed),
    }
}

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
            // **`len` arrives FINISHED** (2026-08-12): the caller applied
            // `(LEN) as usize` for a licensed companion and left a fabricated
            // extent bare, because only the caller holds the provenance that
            // decides between them. Building the cast here would have cast the
            // named const too, making a fabricated site textually
            // indistinguishable from a licensed one.
            //
            // The hand-built `usize` (now at the caller) stays hand-built with
            // `DUMMY_SP`: `parse_ty` opens a fresh `ParseSess` whose `BytePos`
            // values start at zero and therefore **alias real offsets in this
            // crate's first source file** — the hazard `SpanEraser` was landed
            // for at task 0, invisible to that witness because it collects
            // `Expr` spans only. Found by the adversarial review; preserved
            // across the move.
            ExprKind::Call(P(slice_path(ctor)), ThinVec::from_iter([arg, len]))
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
    /// **THE CHANGED-SET, recorded where the change is claimed.**
    ///
    /// A function is reprinted iff one of these spans falls inside it. Recorded
    /// at `claim` rather than derived later, because "which functions changed"
    /// is exactly the kind of fact that grows a second derivation and drifts —
    /// and the alternative here (compare reprint text against the original) is
    /// the derivation the fix ruling explicitly forbade.
    edited: Vec<rustc_span::Span>,
    /// **THE CLAIMANT OF EACH `edited` SPAN, index-parallel to it.**
    ///
    /// Exists so a diagnostic can report an edit's KIND (`decl:*` / `use` /
    /// `seam`) without re-deriving that classification from the AST. Production
    /// already decides it at [`Composition::claim`]; a second derivation in an
    /// instrument is this module's founding defect class, and putting it inside
    /// the thing you debug WITH is the worst place for it (ruled 2026-08-18).
    ///
    /// Parallel rather than a `Vec<(Span, &str)>` so `edited_spans` stays a
    /// borrow of a contiguous slice and the retain filter is untouched. The
    /// pairing is therefore an INVARIANT, not a type guarantee — hence the
    /// `debug_assert` at the single push site.
    claimants: Vec<&'static str>,
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
    pub(crate) fn claim(
        &mut self,
        node: NodeId,
        span: rustc_span::Span,
        claimant: &'static str,
    ) -> bool {
        match self.claimed.get(&node) {
            None => {
                self.claimed.insert(node, claimant);
                self.edited.push(span);
                self.claimants.push(claimant);
                // The two vectors are index-parallel by construction; this is
                // the ONLY site that grows either, so the invariant is local.
                debug_assert_eq!(
                    self.edited.len(),
                    self.claimants.len(),
                    "edited spans and their claimants must stay index-parallel"
                );
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

    /// The spans this transform actually edited. Empty means the transform
    /// changed nothing — and then nothing is reprinted, which is the correct
    /// answer, not a degenerate one.
    pub(crate) fn edited_spans(&self) -> &[rustc_span::Span] {
        &self.edited
    }

    /// The same edits, each carrying the claimant that made it.
    ///
    /// Diagnostic-only: nothing in the emission path reads this, so it cannot
    /// change what is spliced. It reports the classification production
    /// already made rather than recomputing one.
    pub(crate) fn edited_with_claimants(
        &self,
    ) -> impl Iterator<Item = (rustc_span::Span, &'static str)> + '_ {
        self.edited
            .iter()
            .copied()
            .zip(self.claimants.iter().copied())
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
    /// **THE IDENTITIES the walk actually rewrote**, one per realized rewrite.
    ///
    /// A `Vec` and not a set on purpose: the *duplicate* is itself a failure
    /// class (one key rewritten twice), and a set would absorb it silently at
    /// the point of collection — which is the shape the count-based ledger was
    /// faulted for. The de-duplication happens at the reconciliation, where the
    /// difference between the two lengths is a reported row.
    pub placed_ids: Vec<(LocalDefId, HirId)>,
    /// Decided subjects the **site** revert check declined. Diagnostic, and the
    /// denominator that makes `reverted_placed`'s zero mean something: a zero
    /// here would mean the check never ran, and the observability the F2 repair
    /// bought would be back to a construction.
    ///
    /// ⚠ **A COUNT, and the claim no longer rests on it** (round 4). Codex's
    /// round-3 [high]: if two AST declarations resolve to reverted subject `A`
    /// while subject `B` is never reached, this scalar still equals the two
    /// oracle lines — so *"every reverted subject's declaration was reached"* was
    /// never established by it. The identities are in
    /// [`Self::withheld_ids`]; this stays as the term the oracle's LINE COUNT is
    /// checked against, which is a different source from `reverted_ids`.
    pub reverted_withheld: usize,
    /// **THE IDENTITIES the site revert check declined**, one per decline.
    ///
    /// A `Vec` for [`Self::placed_ids`]' reason and it is the same reason: the
    /// duplicate is itself the failure class — the exact compensating pair that
    /// keeps the scalar equal while the *set* is wrong — and a set would absorb
    /// it at the point of collection.
    pub withheld_ids: Vec<(LocalDefId, HirId)>,
    /// **THE ORPHAN CLASS — a subject whose declaration the walk reached with
    /// no owning function.**
    ///
    /// [`MutVisitor::visit_item`] sets `current_fn` only on a top-level
    /// `ItemKind::Fn`, and `visit_assoc_item` is **not** overridden — so an
    /// `impl` method's params arrive here with `current_fn` unset and used to
    /// return with no trace. Exact rather than approximate: it counts only
    /// bindings whose `HirId` is a KNOWN SURVIVOR, which the hir-only index
    /// makes decidable without the `fn_did` half of the key.
    ///
    /// Corpus-zero would be **structural, not evidential**, so it ships with an
    /// injection witness (`an_impl_method_subject_is_counted_not_skipped`)
    /// rather than an argument.
    pub orphan_subject: usize,
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
    /// **THE REVERT SET, CONSULTED AT THE SITE** — the F2 repair.
    ///
    /// Phase 4's whole property is *"a reverted subtree is not transformed"*,
    /// and the first repair could not observe it: `decisions` was built WITH the
    /// revert filter, so `placed ⊆ survivors` held **by construction** and
    /// `reverted_placed` was empty for a reason no bug could disturb. The
    /// reconciliation was comparing a lookup key against itself.
    ///
    /// Moving the filter here makes the withholding a **checked behaviour**
    /// instead of a pre-filtered population: the walk now sees every decided
    /// subject and declines the reverted ones at this line. Delete that check
    /// and `reverted_placed` fires — which is what "observable" means.
    ///
    /// **Behaviour is unchanged**: previously a reverted subject missed the
    /// `decisions` lookup and returned; now it is found and declined. Neither
    /// path rewrites, claims a node, or renders — so the emitted AST is
    /// identical and every phase-3 line is untouched.
    ///
    /// Empty for [`transform_inner`], which applies no revert set.
    pub reverted_fns: &'a FxHashSet<LocalDefId>,
    /// **The survivors' `HirId`s alone** — the half of the decision key that is
    /// available when `current_fn` is not.
    ///
    /// **No longer derivable from [`Self::decisions`]** now that the revert
    /// filter moved to the site: `decisions` carries every decided subject
    /// while this carries only the ones a placement is OWED for. The
    /// maintainability review flagged the old shape as a projection recomputed
    /// at each construction site; the two sets are genuinely different now, so
    /// passing both is information rather than duplication.
    ///
    /// Sound as an identity because a binding's `HirId.owner` **is** its body
    /// owner: for a param or local of `F`, the owner is `F`, so a `HirId` in
    /// this index determines the `fn_did` half it came with. That is what makes
    /// [`RefDeclStats::orphan_subject`] an exact count rather than a heuristic
    /// over "raw-pointer declarations we did not transform".
    pub subject_hirs: &'a FxHashSet<HirId>,
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
        // **THE HIR LOOKUP MOVED AHEAD OF THE OWNER LOOKUP**, and the reorder is
        // the whole point: with `current_fn` checked first, an `impl` method's
        // subject returned before anything could tell it apart from the many
        // declarations that are simply not subjects. Both paths still return —
        // this is instrument-only — but the orphan class is now decidable.
        let Some(&hir_id) = self.local_map.get(&binding) else {
            // A `local_map` miss cannot be attributed here: without a `HirId`
            // there is no key to test membership with. It is not left
            // unmeasured — the identity reconciliation reports the exact
            // subject that went missing, by name, and
            // `missing_unattributed` is the residue after the classes that CAN
            // be named at the site are subtracted.
            return;
        };
        let Some(fn_did) = self.current_fn else {
            if self.subject_hirs.contains(&hir_id) {
                self.stats.orphan_subject += 1;
            }
            return;
        };
        let Some(&(form, mutable)) = self.decisions.get(&(fn_did, hir_id)) else {
            return;
        };
        // **THE REVERT CHECK, AT THE SITE.** Before the shape check and before
        // the claim, so a withheld declaration behaves exactly as it did when
        // the population was pre-filtered: untouched, unclaimed, unrendered.
        // The difference is that it is now a CHECK a mutation can break, rather
        // than a set membership no bug could disturb.
        if self.reverted_fns.contains(&fn_did) {
            self.stats.reverted_withheld += 1;
            // **THE IDENTITY, beside the count.** The count alone cannot say
            // WHICH subjects were reached; round 4's item 2, and the mirror of
            // what `placed_ids` does three returns below.
            self.stats.withheld_ids.push((fn_did, hir_id));
            return;
        }
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
        if !self.guard.claim(ty.id, ty.span, claimant) {
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
        // **RECORDED AT THE REALIZED REWRITE, not at the attempt.** Every early
        // return above is a non-placement, so this list and the three form
        // counters move together or the instrument is broken — an equality the
        // gate asserts rather than assumes.
        self.stats.placed_ids.push((fn_did, hir_id));
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
            if !self.guard.claim(e.id, e.span, "use") {
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
    /// **Fabricated lengths actually PLACED** — not built (repaired 2026-08-15,
    /// adversarial finding ADV-FAB-04).
    ///
    /// It was incremented in `build`, beside `len_grafted`, where a node can
    /// still be refused by the claim guard afterwards. That over-count was
    /// benign while it was telemetry; it stopped being benign when it became the
    /// condition for emitting a **crate-level item**, because a built-then-
    /// refused fabricated seam would have produced a const with no reference —
    /// the dead item the whole derivation exists to prevent. `arm3_refused` is
    /// deliberately NOT zero-gated (its zero is a corpus fact, not a structure),
    /// so this could not rest on it.
    ///
    /// A subset, not a sibling: the exhaustive
    /// `len_grafted + len_parse_failed + len_absent == len_shapes` identity is
    /// deliberately untouched, so this counter cannot drift the ledger. It
    /// exists because "how many of the placed lengths were invented" must be
    /// answerable from **this** layer's own stats and not only from the seam
    /// census — the ruling's separate-count requirement, applied where the
    /// expression is actually built.
    pub len_fabricated: usize,
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
        use super::decision::seam::{GlueCore, SeamLen};
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
        // **The length expression is finished HERE, not in `glue_expr`**
        // (2026-08-12). A licensed companion is `(TEXT) as usize` because the C
        // spelling may be `size_t`/`c_int`/`c_ulong`; a FABRICATED extent is the
        // named const, already `usize`, and casting it would make a fabricated
        // site textually indistinguishable from a licensed one whose companion
        // happened to be a path. Two renderings, so the builder that knows WHICH
        // is the one that must decide — `glue_expr` receives a finished node.
        let len = match spec.len.as_ref() {
            None => None,
            Some(seam_len) => match graft_expr(seam_len.text()) {
                Ok(parsed) => {
                    self.stats.len_grafted += 1;
                    Some(finish_len(seam_len, parsed))
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
            if !self.guard.claim(e.id, e.span, "seam") {
                self.stats.refused += 1;
                return;
            }
            {
                e.kind = kind;
                self.stats.grafted += 1;
                // **COUNTED AT THE PLACEMENT, past the claim guard** — the
                // condition for emitting the crate-level const, so it may not
                // count a node that was built and then refused (ADV-FAB-04).
                if target
                    .spec
                    .len
                    .as_ref()
                    .is_some_and(super::decision::seam::SeamLen::is_fabricated)
                {
                    self.stats.len_fabricated += 1;
                }
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
            g.claim(node, rustc_span::DUMMY_SP, "decl:slice"),
            "the first claim must be admitted"
        );
        assert!(
            !g.claim(node, rustc_span::DUMMY_SP, "use"),
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
        assert!(g.claim(NodeId::from_u32(1), rustc_span::DUMMY_SP, "decl:ref"));
        assert!(g.claim(NodeId::from_u32(2), rustc_span::DUMMY_SP, "use"));
        assert!(g.refused.is_empty(), "distinct nodes must not be refused");
    }

    /// **The claimant travels with its span, in order, and REFUSALS DO NOT
    /// ENTER.**
    ///
    /// Both halves matter and they fail to different mutations. The spans are
    /// DISTINCT on purpose: with `DUMMY_SP` everywhere, any mispairing still
    /// compares equal, so the test would pass under its own defect.
    ///
    /// *Mutation-tested*, each reverted by `git checkout`:
    /// - **M-A (pairing)** — `.zip(self.claimants.iter().rev().copied())`:
    ///   claimants pair with the wrong spans. FAILS.
    /// - **M-B (exclusion)** — hoist `claimants.push` out of the admitted arm:
    ///   a REFUSED claim, which edited nothing, records a claimant, and the
    ///   parallel invariant reports a changed-set longer than its edits. FAILS.
    /// - **M-C (constant)** — push a fixed `"decl:ref"` instead of the
    ///   parameter: every edit reports the same kind, which is what a
    ///   diagnostic reading this would silently believe. FAILS.
    ///
    /// Note what is NOT a discriminating mutation: swapping the two `push`
    /// calls. Both append, so the pairing is unchanged — recorded because it
    /// was the first mutation reached for, and it witnesses nothing.
    #[test]
    fn each_edited_span_carries_the_claimant_that_made_it() {
        use rustc_span::{BytePos, Span, SyntaxContext};
        let sp =
            |lo: u32, hi: u32| Span::new(BytePos(lo), BytePos(hi), SyntaxContext::root(), None);
        let mut g = Composition::default();
        let (a, b, c) = (sp(10, 20), sp(30, 40), sp(50, 60));
        assert!(g.claim(NodeId::from_u32(1), a, "decl:ref"));
        assert!(g.claim(NodeId::from_u32(2), b, "use"));
        assert!(g.claim(NodeId::from_u32(3), c, "seam"));
        // Refused: node 1 is already held, so this must add NOTHING.
        assert!(!g.claim(NodeId::from_u32(1), sp(70, 80), "seam"));

        assert_eq!(
            g.edited_with_claimants().collect::<Vec<_>>(),
            vec![(a, "decl:ref"), (b, "use"), (c, "seam")],
            "each edited span must carry the claimant that made it, in the              order the claims were admitted, and a REFUSED claim must not              appear — it edited nothing"
        );
        assert_eq!(
            g.edited_spans().len(),
            g.edited_with_claimants().count(),
            "the parallel vectors must agree in length — the invariant the              debug_assert in `claim` states"
        );
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
    transform_inner(tcx, &RevertSet::default()).map(|(decls, ..)| decls)
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
fn transform_inner(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    reverts: &RevertSet,
) -> Result<
    (
        RefDeclStats,
        UseGraftStats,
        SeamGraftStats,
        usize,
        usize,
        usize,
        SeamUseSurface,
        rustc_ast::Crate,
        // **THE CHANGED-SET, EACH EDIT WITH ITS CLAIMANT.** Carried as pairs
        // rather than two parallel vectors so the pairing cannot come apart at
        // this boundary; the emission sites project the spans back out, which
        // is order-preserving and classifies nothing.
        Vec<(rustc_span::Span, &'static str)>,
    ),
    String,
> {
    let capture = capture_ast(tcx)?;
    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    transform_with(&capture, &table, reverts)
}

/// **THE ONE AST CAPTURE PER SESSION** (M-2/A).
///
/// `expanded_ast` **panics once the HIR is built** — it clones a resolver that
/// lowering has already consumed — and `make_ast_to_hir` builds the HIR. So this
/// may be called **exactly once per compiler session, before any HIR/MIR
/// query**, and the pristine krate it yields is the only one there will be.
///
/// That is why the verify/revert loop clones rather than re-captures: a second
/// call is not expensive, it is a panic.
pub(crate) struct AstCapture {
    /// The pristine, untransformed crate. **Cloned per revert round**, never
    /// mutated in place — the loop needs a fresh copy for each revert set, and
    /// `rustc_ast::Crate: Clone` is what makes A possible at all.
    pub krate: rustc_ast::Crate,
    pub map: ::utils::ir::AstToHir,
}

pub(crate) fn capture_ast(tcx: rustc_middle::ty::TyCtxt<'_>) -> Result<AstCapture, String> {
    let captured = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut krate = ::utils::ast::expanded_ast(tcx);
        let map = ::utils::ast::make_ast_to_hir(&mut krate, tcx);
        AstCapture { krate, map }
    }));
    captured.map_err(|_| "AST capture panicked".to_owned())
}

/// One transform pass over a CLONE of the pristine capture, under one revert
/// set. Called once per verify/revert round.
fn transform_with(
    capture: &AstCapture,
    table: &super::decision::DecisionTable,
    reverts: &RevertSet,
) -> Result<
    (
        RefDeclStats,
        UseGraftStats,
        SeamGraftStats,
        usize,
        usize,
        usize,
        SeamUseSurface,
        rustc_ast::Crate,
        // **THE CHANGED-SET, EACH EDIT WITH ITS CLAIMANT.** Carried as pairs
        // rather than two parallel vectors so the pairing cannot come apart at
        // this boundary; the emission sites project the spans back out, which
        // is order-preserving and classifies nothing.
        Vec<(rustc_span::Span, &'static str)>,
    ),
    String,
> {
    let mut krate = capture.krate.clone();
    let map = &capture.map;
    let mut decisions: FxHashMap<(LocalDefId, HirId), (DeclForm, bool)> = FxHashMap::default();
    let mut uses: FxHashMap<(u32, u32), String> = FxHashMap::default();
    let mut use_key_collisions = 0usize;
    let mut decision_key_collisions = 0usize;
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
        // **ITEM 7 — the registered finding, repaired.** This join fed
        // `arms_full` and the RECON gate with no collision counter while its
        // `uses` and `seams` siblings both had one. Fixing the instance in
        // `phase3_fn_parity` and leaving the class here is the pattern the
        // phase-4 boundary was about.
        insert_counting(
            &mut decisions,
            (subject.fn_did, subject.hir_id),
            (form, mutable),
            &mut decision_key_collisions,
        );
        for u in use_edits.into_iter().flatten() {
            // A returned `Some` means two use edits carried the SAME span and
            // one was overwritten — the map would then hold fewer edits than
            // the table does, and every downstream count would agree with
            // itself while being short. `refuse_nested_use_edits` should make
            // this impossible (identical spans contain each other), but that is
            // an argument about another module, and this is a counter.
            insert_counting(
                &mut uses,
                (u.span.lo().0, u.span.hi().0),
                u.replacement.clone(),
                &mut use_key_collisions,
            );
        }
    }

    // The hir-only index of the population, so an `impl`-method subject that
    // reaches the walk with no owning function is COUNTED rather than dropped.
    // `arms_full` applies no revert set, so here the population is every
    // decided subject.
    let subject_hirs: FxHashSet<HirId> = decisions.keys().map(|(_, h)| *h).collect();
    // **ARM 1 takes the revert set through its own site check** (M-2). Callers
    // that want the un-reverted population — `arms_full` and the parity gates —
    // pass an EMPTY `RevertSet`, which is a statement rather than an omission.
    let mut guard = Composition::default();
    let mut v = RefDeclVisitor {
        local_map: &map.local_map,
        decisions: &decisions,
        global_map: &map.global_map,
        reverted_fns: &reverts.fns,
        subject_hirs: &subject_hirs,
        current_fn: None,
        guard: &mut guard,
        stats: RefDeclStats::default(),
    };
    v.visit_crate(&mut krate);
    let decls = v.stats;

    // **ARMS 2 AND 3 CONSUME THE SHARED BUILDER** (M-2). Their visitors carry no
    // site check, so their revert semantics live entirely in how these maps are
    // built — and production builds them in exactly ONE place.
    let filtered = filtered_inputs(&table, reverts);
    let uses = filtered.uses;
    let use_key_collisions = use_key_collisions + filtered.use_key_collisions;
    let mut g = UseGraftVisitor::new(&uses, &mut guard);
    g.visit_crate(&mut krate);
    let grafts = g.finish();

    // **ARM 3 — the seam pass, and it runs THIRD by requirement, not by
    // convenience.** A seam's argument may contain a use rewrite, so the use
    // pass must have finished before the subtree is moved.
    let seam_targets = filtered.seams;
    let seam_key_collisions = filtered.seam_key_collisions;
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
        decision_key_collisions,
        SeamUseSurface {
            pairs: seam_pairs,
            programs_compared: usize::from(seam_pairs > 0),
            same: seam_same,
            seam_contains_use,
            use_contains_seam,
            partial: seam_use_partial,
        },
        krate,
        guard.edited_with_claimants().collect(),
    ))
}

/// **THE SWITCHOVER ARTIFACT** — the AST layer, emitting.
///
/// Until now the AST layer computed statistics and threw its transformed krate
/// away: `transform_inner` had three call sites and all three discarded it, so
/// nothing anywhere produced a rewritten crate through this layer. The phase-3
/// and phase-4 gates could compare it to the span layer per function; no caller
/// could ASK IT FOR A PROGRAM.
///
/// This is that caller. It runs the same three passes the parity gates measured
/// — `transform_inner`, unchanged — and hands the transformed krate to the same
/// printer `substituted_source` uses, so the emitted text differs from the
/// substrate in exactly the functions the transforms touched.
/// **ONE-SHOT.** Captures, then emits. Correct for a caller that emits once
/// (the string entry, the parity gates). **A verify/revert loop must NOT use
/// it** — see [`ast_emitted_source_from`] for why a second call cannot work.
pub(crate) fn ast_emitted_source(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    reverts: &RevertSet,
) -> Result<(String, super::ast_bridge::SubstStats), String> {
    let capture = capture_ast(tcx)?;
    ast_emitted_source_from(tcx, &capture, reverts)
}

/// **THE LOOP'S ENTRY — emit round N from the round-0 capture.**
///
/// `capture_ast` may succeed **at most once per session**: `expanded_ast`
/// panics once the HIR is built, and the capture itself builds it
/// (`make_ast_to_hir`). So a verify/revert loop cannot re-capture per round —
/// it captures once, before any HIR query, and re-emits from that pristine
/// capture under each round's revert set. `transform_with` already transforms a
/// CLONE, so the capture stays reusable.
///
/// This split is not a convenience: calling [`ast_emitted_source`] twice in one
/// session returns `Err("AST capture panicked")` on the second call, witnessed
/// at `a_second_capture_in_one_session_fails`.
/// **The loop's per-file entry (A1).** Same transform, same const rule, but the
/// emission is keyed by source file rather than collapsed into the root.
///
/// The const is appended to the ROOT file only — it is declared once per crate
/// and named as `crate::SEAM_LEN_PLACEHOLDER`, so a copy per file would be a
/// duplicate-definition error, not redundancy.
///
/// ⚠ **`tcx` IS STILL REQUIRED, and only for one thing: the source map.**
/// `splice_fn_prints_per_file` needs it to resolve spans to files, offsets and
/// original text. It is NOT used to derive anything — `transform_with` takes
/// the capture, the table and the reverts, all as parameters. Narrowing the
/// signature to make re-derivation unrepresentable was considered and is not
/// available here; do not widen `tcx`'s use back beyond the source map without
/// re-reading why this note exists.
pub(crate) fn ast_emitted_files_from(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    capture: &AstCapture,
    reverts: &RevertSet,
    root_key: Option<&super::plan::FileKey>,
    // **THE CALLER'S TABLE, NOT A RE-DERIVATION.** This entry used to call
    // `decide_table_with_ctx` itself — a SECOND derivation of the decision
    // table, and the module's founding defect class in its purest form. It was
    // invisible on every fixture whose table is deterministic, and visible the
    // moment one is INJECTED: `rewrite_core_injected` injects into its own
    // table, the re-derived one never saw the injection, and the AST layer
    // emitted a program without the very edit the test exists to break on.
    table: &super::decision::DecisionTable,
) -> Result<
    (
        std::collections::BTreeMap<super::plan::FileKey, String>,
        super::ast_bridge::SubstStats,
    ),
    String,
> {
    let (_, _, seams, _, _, _, _, krate, edited) = transform_with(capture, table, reverts)?;
    let edited: Vec<rustc_span::Span> = edited.into_iter().map(|(sp, _)| sp).collect();
    let (mut files, stats) =
        super::ast_bridge::splice_fn_prints_per_file(tcx, &krate, Some(&edited));
    if seams.len_fabricated > 0 {
        // Root selection: the caller's key when it has one (the loop's round-0
        // file), else the map's first — deterministic because the map is
        // ordered by `FileKey`.
        let key = root_key.cloned().or_else(|| files.keys().next().cloned());
        if let Some(key) = key
            && let Some(text) = files.get_mut(&key)
            && !text.is_empty()
        {
            text.push('\n');
            text.push_str(&super::decision::seam::fabricated_len_item());
            text.push('\n');
        }
    }
    Ok((files, stats))
}

pub(crate) fn ast_emitted_source_from(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    capture: &AstCapture,
    reverts: &RevertSet,
) -> Result<(String, super::ast_bridge::SubstStats), String> {
    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    let (_, _, seams, _, _, _, _, krate, edited) = transform_with(capture, &table, reverts)?;
    let edited: Vec<rustc_span::Span> = edited.into_iter().map(|(sp, _)| sp).collect();
    let (mut source, stats) = super::ast_bridge::splice_fn_prints(tcx, &krate, Some(&edited));
    // **The fabricated-extent const** (marker ruling, 2026-08-15): emitted when
    // this layer PLACED at least one fabricated adapter.
    //
    // ⚠ **This is NOT the span layer's condition.** The span layer's is
    // *survived*; this one is *placed*.
    //
    // ⚠⚠ **The previous text here was STALE and is corrected (M-2/A task 3,
    // 2026-08-18).** It read: *"`transform_inner` builds its visitors with an
    // explicitly EMPTY revert set."* That was true before M-2/A task 1 threaded
    // `reverts` through; it has been false since. The revert set IS honoured —
    // at `reverted_fns` in the decl arm and at `filtered_inputs` for the use and
    // seam arms — and `a_reverted_fn_keeps_its_raw_declaration` witnesses it.
    //
    // What survives of the old note is only the narrow part: the two conditions
    // still coincide on every current fixture because none reverts a fabricated
    // callee, so `len_fabricated > 0` has not yet been observed to disagree with
    // survival. That is an unexercised case, NOT an established equivalence.
    //
    // Appended, matching `render`'s end-of-file insertion: the spliced output
    // replaces function spans in place, so appending here and inserting at
    // `source.len()` of the original put the item in the same position.
    if seams.len_fabricated > 0 && !source.is_empty() {
        source.push('\n');
        source.push_str(&super::decision::seam::fabricated_len_item());
        source.push('\n');
    }
    Ok((source, stats))
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
    /// **Two table entries sharing one `(fn_did, hir_id)`** in the DECLARATION
    /// join — the counter this file's other two joins had since arm 2 and this
    /// one did not. Registered as a finding at the phase-4 boundary and repaired
    /// here; corpus expectation 0, GATED.
    pub decision_key_collisions: usize,
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
    /// The FABRICATED subset of [`Self::seam_adapter`] — a subset, so the
    /// [`Self::total`] identity is untouched and this cannot drift the ledger.
    pub seam_adapter_fabricated: usize,
    /// The crate-level const declaration.
    ///
    /// ⚠ **A PIN, not a measurement.** Production never fills it: the const edit
    /// is created inside `render` from the surviving edits and never enters
    /// `plan.by_file`, which is what this census walks. Unit-witnessed,
    /// production-unreachable — retained so a `FabricatedLenConst` that DID
    /// reach `count()` could not be silently dropped from the total, and
    /// labelled so nobody reads its zero as evidence about the const.
    pub fabricated_len_const: usize,
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
        // `seam_adapter_fabricated` is deliberately absent: it is a SUBSET of
        // `seam_adapter`, and adding it would double-count every fabricated
        // placement against `edits_in`.
        //
        // ⚠ **`fabricated_len_const` is a bucket that PRODUCTION NEVER FILLS**,
        // and the comment here previously claimed the opposite ("a real edit in
        // `by_file`"). It is not: the const edit is created inside `render`
        // from the surviving edits and never enters `by_file`, which is the only
        // thing this census walks. Corrected 2026-08-15 (ADV-FAB-08) — the claim
        // was contradicted by another comment in the same slice.
        //
        // The term stays in the sum because a `FabricatedLenConst` reaching
        // `count()` *would* be a real edit and must not be dropped; but its zero
        // is a **PIN**, unit-witnessed and production-unreachable, in the same
        // class as `arm4_reroute`/`drop_form`/`store_form` and NOT in
        // `seam_adapter`'s. The real claim about the const's delivery is gated
        // on the EMITTED TEXT (`fab_const_decl` / `fab_const_ref`).
        self.kind_decision
            + self.seam_adapter
            + self.fabricated_len_const
            + self.reroute
            + self.drop_form
            + self.store_form
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
            J::SeamAdapter { fabricated, .. } => {
                self.seam_adapter += 1;
                if *fabricated {
                    self.seam_adapter_fabricated += 1;
                }
            }
            J::FabricatedLenConst => self.fabricated_len_const += 1,
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
#[derive(Default)]
pub(crate) struct RevertSet {
    pub fns: FxHashSet<LocalDefId>,
    pub names: FxHashSet<String>,
    pub subjects: usize,
}

impl RevertSet {
    /// Does an edit owned by `owner_fn` survive? **The single place either side
    /// asks**, so they cannot diverge on population again.
    ///
    /// **PRODUCTION LAW from 2026-08-16 (M-2).** The type graduated out of
    /// `#[cfg(test)]` when the verify/revert loop was wired to the AST layer:
    /// production needs a revert vocabulary spanning BOTH keys, because
    /// `emit_files` filters SUBJECTS by `LocalDefId` while `render` filters
    /// EDITS by `owner_fn`, and a seam edit is only ever caught by the second.
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

/// **THE FILTERED-INPUT BUILDER — production's ONE answer to "which edits
/// survive"** (M-2, ruled 2026-08-16).
///
/// # Why this exists, and why the GATE must not call it
///
/// Arms 2 and 3 revert by **input filtering**, by design: their visitors carry
/// no site check, so *"handing the walk a reverted subject's uses WOULD change
/// the emitted AST"*. Only arm 1 has a per-site check. So the revert semantics
/// for two of three arms live in **how their maps are built**, and building
/// them twice in production would be a second derivation of the survivor set —
/// the class this milestone has repaired four times.
///
/// **`phase3_fn_parity` deliberately keeps its own verbatim filters and never
/// calls this.** That is not duplication, it is the point: a gate is *supposed*
/// to be an independent derivation, and a gate that consumes what it checks is
/// the render-gap tautology. The two sides cannot diverge on **population** —
/// both read one [`RevertSet`] — and if they diverge on **semantics**, the
/// acceptance gate's byte reproduction is the detector. Such a divergence is a
/// finding, never reconciled silently in either direction.
pub(crate) struct FilteredInputs {
    /// Use-graft targets, keyed by `(lo, hi)`, with reverted subjects' uses
    /// already removed.
    pub uses: FxHashMap<(u32, u32), String>,
    /// Seam targets, keyed by `(lo, hi)`, with reverted owners' seams removed.
    pub seams: FxHashMap<(u32, u32), SeamTarget>,
    /// Collisions observed while building each map — a join without a collision
    /// counter agrees with itself while being short.
    pub use_key_collisions: usize,
    pub seam_key_collisions: usize,
}

/// Build both filtered maps from one decision table and one revert set.
///
/// `subject_of` yields each use edit's owning subject so the arm-2 filter can
/// ask `keeps_subject`; the arm-3 filter asks `keeps` on the seam's own
/// `owner_fn`, which is the CALLEE — the revert key a seam is caught by.
pub(crate) fn filtered_inputs(
    table: &super::decision::DecisionTable,
    reverts: &RevertSet,
) -> FilteredInputs {
    let mut out = FilteredInputs {
        uses: FxHashMap::default(),
        seams: FxHashMap::default(),
        use_key_collisions: 0,
        seam_key_collisions: 0,
    };
    for (subject, decision) in &table.entries {
        let use_edits = match decision {
            super::decision::Decision::Ref { .. } => None,
            super::decision::Decision::Slice { uses, .. } => Some(uses),
            super::decision::Decision::Opt { uses, .. } => Some(uses),
            super::decision::Decision::Degraded(_) => continue,
        };
        // ARM 2's filter: no site check downstream, so a reverted subject's
        // uses must never enter the map.
        if !reverts.keeps_subject(subject.fn_did) {
            continue;
        }
        for u in use_edits.into_iter().flatten() {
            insert_counting(
                &mut out.uses,
                (u.span.lo().0, u.span.hi().0),
                u.replacement.clone(),
                &mut out.use_key_collisions,
            );
        }
    }
    for edit in &table.seams.edits {
        // ARM 3's filter, on the CALLEE's path: reverting a callee reverts its
        // seams with it, because `owner_fn` is the revert key.
        if !reverts.keeps(&edit.owner_fn) {
            continue;
        }
        insert_counting(
            &mut out.seams,
            (edit.span.lo().0, edit.span.hi().0),
            SeamTarget::of(edit),
            &mut out.seam_key_collisions,
        );
    }
    out
}

/// **IS THE REVERT RESOLUTION A FUNCTION? (round-3 item 7.)**
///
/// `def_path_str` is **not injective on this corpus** — the project's own record
/// measures **295 duplicate `fn` names in brotli alone** — so a revert line
/// naming a homonym matched EVERY function of that name and over-reverted them
/// all, **silently**: the old `seen.len() == wanted.len()` check passed because
/// `seen` is keyed by NAME while the resolved set collects `LocalDefId`s.
///
/// Over-reverting is invisible to the differential for the usual reason — both
/// sides consume this one set — and was caught only downstream by
/// `decided == emitted + reverted`, which compares a `DefId`-keyed set against
/// the oracle's LINE COUNT. That is a coincidence of two representations, not a
/// check, and it stops holding the moment that ledger line is relaxed.
///
/// **Minimal form, per the charter**: assert the relation is a function and a
/// total one, and name the offenders. A `DefId`-carrying revert format is the
/// real fix and is **registered, not built** in this round.
///
/// Pure over the counts so it has a witness — `oracle_reverts` itself needs a
/// `TyCtxt` and is corpus-only.
pub(crate) fn revert_resolution_failure(
    by_name: &[(String, usize)],
    wanted: usize,
    resolved: usize,
    origin: &str,
) -> Option<String> {
    let mut homonyms: Vec<&(String, usize)> = by_name.iter().filter(|(_, n)| *n > 1).collect();
    if !homonyms.is_empty() {
        homonyms.sort();
        return Some(format!(
            "{} reverted owner name(s) in {origin:?} resolve to MORE THAN ONE \
             local function — `def_path_str` is not injective on this corpus \
             (295 duplicate fn names in brotli alone), so each over-reverts \
             every homonym silently: {:?}",
            homonyms.len(),
            homonyms.iter().take(5).collect::<Vec<_>>()
        ));
    }
    if resolved != wanted {
        return Some(format!(
            "resolved {resolved} LocalDefId(s) for {wanted} reverted owner \
             name(s) in {origin:?} — the revert resolution must be one-to-one"
        ));
    }
    None
}

/// **TAKES THE VERIFIED BYTES, NOT A PATH — the check-to-use closure.**
///
/// This read the file itself, from a path the parent had hashed *earlier*. The
/// parent's preflight therefore certified one set of bytes and the worker
/// consumed whatever was at that path when it got there: a replacement or a
/// symlink retarget in between is consumed unverified, and because BOTH
/// derivations use that same set, parity and the ledger stay green over a
/// substituted revert set. Codex's round-2 [high] finding.
///
/// Taking the content as a parameter makes the window unrepresentable rather
/// than merely small: the caller hashes the buffer it read and hands over that
/// exact buffer.
#[cfg(test)]
pub(crate) fn oracle_reverts(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    body: &str,
    origin: &str,
) -> Result<RevertSet, String> {
    let path = origin;
    // **EVERY NON-EMPTY LINE MUST PARSE.** This was a `filter_map`, which
    // dropped a malformed line while `subjects` still counted it — so a
    // corrupted oracle could under-revert BOTH sides identically, keep the
    // 1,058 pin green, and leave the differential structurally blind to it.
    // Shared held-fixed inputs are guarded AT THE INPUT, because a differential
    // cannot see its own premise being wrong.
    let mut wanted: FxHashSet<&str> = FxHashSet::default();
    let mut subjects = 0usize;
    for line in body.lines().map(str::trim).filter(|l| !l.is_empty()) {
        subjects += 1;
        let Some((owner, tail)) = line.rsplit_once("::") else {
            return Err(format!(
                "malformed revert line {line:?} in {path:?}: expected \
                 `{{fn_path}}::{{param}}#{{mir_local}}`"
            ));
        };
        if owner.is_empty() || !tail.contains('#') {
            return Err(format!("malformed revert line {line:?} in {path:?}"));
        }
        wanted.insert(owner);
    }

    // **INJECTIVITY, ASSERTED (item 7).** `def_path_str` is NOT unique in this
    // corpus — this project's own record measures **295 duplicate `fn` names in
    // brotli alone** — so a revert line naming a homonym matched EVERY function
    // of that name and over-reverted them all, silently: `seen.len() ==
    // wanted.len()` still passed, because `seen` is keyed by NAME while `out`
    // collected several `LocalDefId`s.
    //
    // Over-reverting is invisible to the differential for the usual reason —
    // both sides consume this one set — and was caught only downstream, by
    // `decided == emitted + reverted` comparing a `DefId`-keyed set against the
    // oracle's LINE COUNT. That is a coincidence of two representations, not a
    // check, and it stops holding the moment that ledger line is relaxed.
    //
    // Minimal form, per the round-3 charter: assert the relation is a function,
    // and report the offenders. **No id-format redesign here** — a
    // `DefId`-carrying revert format is the real fix and is registered, not
    // built.
    resolve_reverts(tcx, &wanted, subjects, path)
}

/// **THE ONE NAME→`LocalDefId` RESOLUTION.** Both revert producers go through
/// here: the oracle's text format ([`oracle_reverts`]) and the verify loop's own
/// `BTreeSet<String>` of reverted owners ([`revert_set_from_names`]).
///
/// It is extracted rather than copied for the reason this module keeps
/// re-learning: *which functions are reverted* is exactly the kind of fact that
/// grows a second derivation and then diverges from the first. The stale-edit
/// attribution defect (S3.6-1 task 2, P3(a)) was that shape, and it was in code
/// one commit old at the time.
fn resolve_reverts(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    wanted: &FxHashSet<&str>,
    subjects: usize,
    path: &str,
) -> Result<RevertSet, String> {
    let mut out = FxHashSet::default();
    let mut seen: FxHashSet<String> = FxHashSet::default();
    let mut by_name: FxHashMap<String, usize> = FxHashMap::default();
    for did in tcx.hir_body_owners() {
        let p = tcx.def_path_str(did.to_def_id());
        if wanted.contains(p.as_str()) {
            out.insert(did);
            *by_name.entry(p.clone()).or_default() += 1;
            seen.insert(p);
        }
    }
    let counts: Vec<(String, usize)> = by_name.into_iter().collect();
    if let Some(why) = revert_resolution_failure(&counts, wanted.len(), out.len(), path) {
        return Err(why);
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

/// **THE LOOP'S REVERT ADAPTER.** The verify loop reverts by owner NAME — the
/// vocabulary `render` filters edits with. The AST layer needs both
/// vocabularies, because `emit_files` filters SUBJECTS by `LocalDefId` while the
/// use and seam arms filter EDITS by `owner_fn`.
///
/// ⚠ **An empty name set is not an error and must not resolve to "revert
/// everything" or fail the injectivity check** — round 0 always has one.
pub(crate) fn revert_set_from_names(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    names: &std::collections::BTreeSet<String>,
) -> Result<RevertSet, String> {
    let wanted: FxHashSet<&str> = names.iter().map(String::as_str).collect();
    resolve_reverts(tcx, &wanted, names.len(), "verify-loop")
}

/// **THE EDIT DUMP** — both layers' SURVIVING edits under ONE held revert set.
///
/// Diagnostic only. Nothing gates on it and nothing in the emission path reads
/// it; it exists to answer a question no corpus counter can, because `emitted`
/// and `reverted` count **DECISIONS** and nothing at corpus scale compares
/// **TEXT** (M-2 handoff §2).
///
/// # The revert set is HELD, never re-derived
///
/// Both sides consume the one `RevertSet` parsed from the caller's oracle text,
/// for the reason `phase3_fn_parity` records: a run that re-derived reverts
/// would make any difference ambiguous between the transform layer and the
/// revert layer. The set is also reported back in the dump, so a reader can see
/// which population the two sides were actually asked about.
///
/// # Ordering is load-bearing
///
/// `capture_ast` **first**, before any HIR query — `expanded_ast` panics once
/// the HIR is built, and revert resolution is a HIR query. This is the module's
/// ONE ENTRY rule; getting it wrong panicked all 20 programs once already.
///
/// # Both keys are reported on purpose
///
/// [`RevertSet`] carries `fns` (`LocalDefId`) and `names` (`owner_fn` paths)
/// because `emit_files` filters SUBJECTS by the first while `render` filters
/// EDITS by the second. A dump that showed only one key could not distinguish
/// "not reverted" from "reverted under the other key".
///
/// `#[cfg(test)]` like its sibling [`phase3_fn_parity`], and for the same
/// reason: it consumes `oracle_reverts`, and its only caller is the
/// `#[cfg(test)]` corpus worker. Production emits without it.
#[cfg(test)]
pub(crate) fn edit_dump(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    reverts_text: &str,
    reverts_origin: &str,
    // **WHERE TO WRITE THE TWO EMITTED PROGRAMS.** `None` reports byte counts
    // only. Byte counts say THAT the layers differ; a promote-failure specimen
    // needs to show WHERE, and the emitted text is the only thing that can.
    texts_out: Option<&std::path::Path>,
) -> Result<String, String> {
    use std::fmt::Write as _;

    let capture = capture_ast(tcx)?;
    let reverts = oracle_reverts(tcx, reverts_text, reverts_origin)?;
    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    let sm = tcx.sess.source_map();
    let mut o = String::new();

    let mut names: Vec<&str> = reverts.names.iter().map(String::as_str).collect();
    names.sort_unstable();
    let _ = writeln!(o, "== HELD REVERT SET (one set, both layers) ==");
    let _ = writeln!(
        o,
        "origin={reverts_origin}\nsubjects={} fns={} names={names:?}",
        reverts.subjects,
        reverts.fns.len()
    );

    // Function extents, from the SAME walk the splice uses, so "containing
    // function" here means what it means there.
    let mut fn_spans = Vec::new();
    super::ast_bridge::collect_fn_spans(&capture.krate.items, &mut fn_spans);
    // Body owners, for the resolved `LocalDefId` of whatever contains an edit.
    let owners: Vec<(rustc_span::Span, rustc_hir::def_id::LocalDefId)> = tcx
        .hir_body_owners()
        .map(|did| (tcx.def_span(did), did))
        .collect();
    let locate = |sp: rustc_span::Span| -> String {
        let Some(extent) = fn_spans.iter().find(|f| f.contains(sp)) else {
            return "fn=<none: edit is outside every function extent>".to_owned();
        };
        match owners.iter().find(|(dsp, _)| extent.contains(*dsp)) {
            Some((_, did)) => format!(
                "fn={} local_def_id={did:?} reverted_by_defid={} reverted_by_name={}",
                tcx.def_path_str(*did),
                reverts.fns.contains(did),
                reverts.names.contains(&tcx.def_path_str(*did)),
            ),
            None => format!(
                "fn=<unresolved> extent={}",
                sm.span_to_string(*extent, rustc_span::FileNameDisplayPreference::Local)
            ),
        }
    };

    // ---- AST layer -------------------------------------------------------
    let (_, _, _, _, _, _, _, krate, edited) = transform_with(&capture, &table, &reverts)?;
    let spans: Vec<rustc_span::Span> = edited.iter().map(|(sp, _)| *sp).collect();
    let (files, stats) = super::ast_bridge::splice_fn_prints_per_file(tcx, &krate, Some(&spans));
    let _ = writeln!(
        o,
        "\n== AST LAYER ==\nclaimed_edits={} files_with_edits={} files_emitted={}",
        edited.len(),
        stats.files_with_edits,
        files.len()
    );
    for (i, (sp, claimant)) in edited.iter().enumerate() {
        let _ = writeln!(o, "-- ast edit #{i} kind={claimant}");
        let _ = writeln!(
            o,
            "   at     = {} bytes=[{}, {})",
            sm.span_to_string(*sp, rustc_span::FileNameDisplayPreference::Local),
            sp.lo().0,
            sp.hi().0
        );
        let _ = writeln!(o, "   {}", locate(*sp));
        let _ = writeln!(
            o,
            "   text   = {:?}",
            sm.span_to_snippet(*sp)
                .unwrap_or_else(|_| "<unrenderable>".to_owned())
        );
    }

    // ---- span layer ------------------------------------------------------
    // ⚠ PLANNED vs SURVIVING are reported separately: "0 surviving" and "0
    // planned" are different facts, and collapsing them is absence-as-
    // observation (standard §1a).
    let emission = super::emit_files(tcx, &table, &reverts.fns)?;
    let reverted_names: std::collections::BTreeSet<String> =
        reverts.names.iter().cloned().collect();
    let (span_files, rollbacks) = super::render(&emission.plan, &emission.texts, &reverted_names);
    let planned: usize = emission.plan.by_file.values().map(Vec::len).sum();
    let _ = writeln!(
        o,
        "\n== SPAN LAYER ==\nplanned_edits={planned} files_emitted={} rollbacks={} unplaceable={}",
        span_files.len(),
        rollbacks.len(),
        emission.plan.unplaceable.len()
    );
    for (key, edits) in &emission.plan.by_file {
        for (i, e) in edits.iter().enumerate() {
            let _ = writeln!(
                o,
                "-- span edit #{i} file={key:?} bytes=[{}, {}) owner_fn={} survives={} just={:?}",
                e.lo,
                e.hi,
                e.owner_fn,
                !reverted_names.contains(&e.owner_fn),
                e.justification
            );
            let _ = writeln!(o, "   text   = {:?}", e.replacement);
        }
    }

    // **THE TEXT COMPARISON.** The reason this dump exists: `emitted` and
    // `reverted` count DECISIONS, and nothing at corpus scale compares TEXT, so
    // an emission difference under a converged revert set is invisible to the
    // very ledger that reports the divergence. Here the emitted bytes are
    // compared against the substrate directly, on BOTH layers.
    //
    // A file the layer did not emit at all is reported as `<not emitted>`,
    // which is a different fact from emitting identical bytes — the seeded map
    // makes the AST layer emit where the span layer emits nothing.
    let substrate_of = |key: &super::plan::FileKey| -> Option<String> {
        let super::plan::FileKey::Real(path) = key else {
            return None;
        };
        std::fs::read_to_string(path).ok()
    };
    let mut keys: std::collections::BTreeSet<&super::plan::FileKey> = files.keys().collect();
    keys.extend(span_files.keys());
    let _ = writeln!(o, "\n== EMITTED TEXT vs SUBSTRATE ==");
    for key in keys {
        let base = substrate_of(key);
        let verdict = |emitted: Option<&String>| match (emitted, base.as_ref()) {
            (None, _) => "<not emitted>".to_owned(),
            (Some(_), None) => "<substrate unreadable>".to_owned(),
            (Some(t), Some(b)) if t == b => format!("IDENTICAL ({} bytes)", t.len()),
            (Some(t), Some(b)) => format!(
                "DIFFERS (emitted {} vs substrate {} bytes)",
                t.len(),
                b.len()
            ),
        };
        let _ = writeln!(o, "-- {key:?}");
        let _ = writeln!(o, "   ast  = {}", verdict(files.get(key)));
        let _ = writeln!(o, "   span = {}", verdict(span_files.get(key)));
        if let Some(dir) = texts_out {
            let stem = match key {
                super::plan::FileKey::Real(path) => path
                    .file_name()
                    .map(|n| n.to_string_lossy().into_owned())
                    .unwrap_or_else(|| "unnamed".to_owned()),
                _ => "virtual".to_owned(),
            };
            for (label, text) in [("ast", files.get(key)), ("span", span_files.get(key))] {
                // A layer that emitted nothing writes NO file, rather than an
                // empty one: "did not emit" and "emitted nothing" are different
                // facts, and a zero-byte file conflates them.
                if let Some(text) = text {
                    let at = dir.join(format!("{stem}.{label}"));
                    let _ = std::fs::write(&at, text);
                    let _ = writeln!(o, "   {label} text -> {}", at.display());
                }
            }
        }
    }
    Ok(o)
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
    reverts_text: &str,
    reverts_origin: &str,
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
    let reverts = oracle_reverts(tcx, reverts_text, reverts_origin)?;

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

    // **THE IDENTITY SETS — F2's remedy, built here and not from the walk's own
    // lookup map.** `survivors` and `reverted_ids` partition the non-degraded
    // table by the held-fixed revert set; `labels` renders one for a human and
    // is never used for matching, so two subjects sharing a label cannot merge.
    //
    // What this DOES establish: the walk placed exactly the survivor set,
    // subject by subject. What it does NOT, and the distinction is the whole
    // content of the boundary review: the revert set is a HELD-FIXED population
    // specification (ruled 2026-08-14), shared by both sides on purpose, so no
    // check here re-derives it. `decided == emitted + reverted` remains the one
    // line with a genuinely external second source.
    let mut survivors: FxHashSet<(LocalDefId, HirId)> = FxHashSet::default();
    let mut reverted_ids: FxHashSet<(LocalDefId, HirId)> = FxHashSet::default();
    let mut labels: FxHashMap<(LocalDefId, HirId), String> = FxHashMap::default();
    for (subject, decision) in &table.entries {
        if matches!(decision, super::decision::Decision::Degraded(_)) {
            continue;
        }
        let key = (subject.fn_did, subject.hir_id);
        labels.insert(key, subject.label.clone());
        if reverts.keeps_subject(subject.fn_did) {
            survivors.insert(key);
        } else {
            reverted_ids.insert(key);
        }
    }
    p.survivor_ids = survivors.len();
    let subject_hirs: FxHashSet<HirId> = survivors.iter().map(|(_, h)| *h).collect();

    // ---- the AST side: the same three passes, with the SAME subjects held back ----
    let mut decisions: FxHashMap<(LocalDefId, HirId), (DeclForm, bool)> = FxHashMap::default();
    let mut uses: FxHashMap<(u32, u32), String> = FxHashMap::default();
    for (subject, decision) in &table.entries {
        // **THE PRE-FILTER IS GONE — this is the F2 repair.**
        //
        // The revert set used to be applied HERE, which made `placed ⊆
        // survivors` true by construction and `reverted_placed` empty for a
        // reason no bug could disturb. It now applies at the transform site
        // (see [`RefDeclVisitor::reverted_fns`]), so the declaration walk sees
        // every decided subject and DECLINES the reverted ones — a checked
        // behaviour a mutation can break.
        //
        // The emitted AST is unchanged: a reverted subject previously missed
        // the lookup and returned, and now is found and declined. Neither path
        // rewrites, claims, or renders.
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
        // **THE JOINS GET THEIR COLLISION COUNTERS**, which `transform_inner`
        // has had since arm 2 and this gate did not: a map that silently
        // overwrites holds fewer edits than the table does, and every
        // downstream count then agrees with itself while being short.
        //
        // ⚠ This now runs over the FULL decided population rather than the
        // surviving 62, because the revert filter moved to the transform site.
        // The previous 0 was measured over 62; this is a first measurement over
        // 1,120, and a nonzero is a genuine FINDING (two subjects sharing one
        // `(fn_did, hir_id)` — plausible where MIR splits one HIR binding into
        // several locals), not a regression of this change.
        insert_counting(
            &mut decisions,
            (subject.fn_did, subject.hir_id),
            (form, mutable),
            &mut p.decision_key_collisions,
        );
        // The use edits stay filtered: arm 2's use grafts have no site check,
        // so handing the walk a reverted subject's uses WOULD change the
        // emitted AST. Only the declaration pass gained a site check, and only
        // its population is widened.
        if !reverts.keeps_subject(subject.fn_did) {
            continue;
        }
        for u in use_edits.into_iter().flatten() {
            insert_counting(
                &mut uses,
                (u.span.lo().0, u.span.hi().0),
                u.replacement.clone(),
                &mut p.use_key_collisions,
            );
        }
    }
    p.use_targets = uses.len();

    let mut guard = Composition::default();
    let mut v = RefDeclVisitor {
        local_map: &map.local_map,
        decisions: &decisions,
        global_map: &map.global_map,
        reverted_fns: &reverts.fns,
        subject_hirs: &subject_hirs,
        current_fn: None,
        guard: &mut guard,
        stats: RefDeclStats::default(),
    };
    v.visit_crate(&mut krate);
    let decls_stats = v.stats;
    let mut g = UseGraftVisitor::new(&uses, &mut guard);
    g.visit_crate(&mut krate);
    let grafts_stats = g.finish();

    // **F2 — seams obey the revert set too.** These were unfiltered on the
    // first run, on BOTH sides, so the two agreed about seams a revert should
    // have taken: lodepng reported 21 compared functions with every one of its
    // 179 subjects reverted and nothing emitted.
    let mut seam_targets: FxHashMap<(u32, u32), SeamTarget> = FxHashMap::default();
    for edit in &table.seams.edits {
        if !reverts.keeps(&edit.owner_fn) {
            continue;
        }
        insert_counting(
            &mut seam_targets,
            (edit.span.lo().0, edit.span.hi().0),
            SeamTarget::of(edit),
            &mut p.seam_key_collisions,
        );
    }
    p.seam_targets = seam_targets.len();

    // **ITEM 1 — THE SECOND DERIVATION OF SEAM OWNERSHIP.**
    //
    // Over the FULL seam population, deliberately: the revert filter three lines
    // above READS `owner_fn`, so corroborating only the edits that survive it
    // would exclude exactly the ones a mis-attribution wrongly saved.
    let owner_index = call_arg_owners(tcx);
    let sowner = reconcile_seam_owners(
        table
            .seams
            .edits
            .iter()
            .map(|e| ((e.span.lo().0, e.span.hi().0), e.owner_fn.as_str())),
        &owner_index,
    );
    p.seam_edits = table.seams.edits.len();
    p.seam_owner_agree = sowner.agree;
    p.seam_owner_mismatch = sowner.mismatch;
    p.seam_owner_unlocated = sowner.unlocated;
    p.seam_owner_ambiguous = sowner.ambiguous;
    p.seam_owner_examples = sowner.examples;

    let mut s = SeamGraftVisitor::new(&seam_targets, &mut guard);
    s.visit_crate(&mut krate);
    // **THE STATS ARE READ.** `let _ = s.finish();` discarded every one of them
    // — F1's finding, and the one place in this gate where the seam layer's
    // behaviour under a real revert set could be observed at all.
    // **And the read is EXHAUSTIVE.** Destructured field-by-field rather than
    // accessed, because that is the structural fix for F1's *class* rather than
    // its instance: **a new counter added to [`SeamGraftStats`] breaks this
    // line's compilation** until someone decides whether the gate reads it. A
    // `.field` access would ignore it in silence, which is exactly how eight
    // typed counters came to be written and never consumed.
    //
    // ⚠ Corrects my own first instinct, recorded because it was wrong: an
    // exhaustive destructure of `FnParity` would NOT have caught F1. F1's shape
    // is upstream — the stats were dropped before anything reached `FnParity`.
    // The consumption site is where the mechanism belongs.
    let SeamGraftStats {
        grafted,
        unmatched,
        multi_matched,
        unsupported,
        arg_not_found,
        len_absent,
        len_parse_failed,
        // ---- deliberately NOT gated here, each with its reason ----
        // A family split, not a failure: these partition the placed adapters
        // and are reported by the recon sweep.
        safe: _,
        reborrow: _,
        // Length bookkeeping whose exhaustive identity is gated in the RECON
        // sweep, over the full population the revert set does not shrink.
        len_grafted: _,
        len_shapes: _,
        // The fabricated SUBSET of `len_grafted`. Reported by the seam census
        // and by the recon sweep, which is where the fabricated population's
        // separate count is gated; this phase-4 gate reads the placed/refused
        // partition, and fabrication does not change what that partition means.
        len_fabricated: _,
        // The offending texts behind `len_parse_failed`, capped for artifacts —
        // the count is what gates.
        len_parse_failures: _,
        // **NOW CARRIED.** Still gated jointly as `p4_refused`, but the seam
        // pass's own share is a TERM IN THE CONSERVATION IDENTITY: a refusal is
        // a terminal outcome for a matched target, so an identity without it
        // misattributes the first real refusal as an evaporation.
        refused: seam_refused,
        // This gate builds its OWN seam map and counts its own collisions into
        // `p.seam_key_collisions`; the visitor's copy is never populated here.
        key_collisions: _,
        // A cast peel is a SHAPE the corpus either has or has not — measured,
        // not gated, per the arm-3 ruling.
        arg_peeled: _,
        // The rendered text is the differential's input, not a failure class.
        rendered: _,
    } = s.finish();
    p.seam_grafted = grafted;
    p.seam_unmatched = unmatched;
    p.seam_multi_matched = multi_matched;
    p.seam_unsupported = unsupported;
    p.seam_arg_not_found = arg_not_found;
    p.seam_len_absent = len_absent;
    p.seam_len_parse_failed = len_parse_failed;
    p.seam_refused = seam_refused;
    p.use_parse_failed = grafts_stats.parse_failed;
    p.use_multi_matched = grafts_stats.multi_matched;
    p.unplaceable = emission.unplaceable.len();

    // ---- RENDER-GAP CALIBRATION (round-3 item 8): bounded, one comparison ----
    //
    // **The registered hazard:** this gate verifies the revert property on the
    // AST replica, while the span half **re-implements the revert filter beside
    // `render`** — the production applier, and the only code that actually
    // reverts a seam adapter into a file. `render` is therefore on no path the
    // gate measures, so a production revert defect ships green.
    //
    // Calibrated, not wired: `render` is invoked ONCE with the real revert set,
    // and its output is compared against a reconstruction built the way this
    // gate builds one.
    //
    // **THE TWO SIDES DERIVE THE REVERT DECISION BY DIFFERENT ROUTES — and the
    // honest label for the relation is STRICT REFINEMENT, not independence.**
    //
    // Round 3's version was a tautology: this side asked
    // `reverts.keeps(&e.owner_fn)` and `render` asked
    // `!reverted.contains(&edit.owner_fn)` — one set, one key, one string
    // vocabulary — so 0-differing was FORCED before the sweep ran. `render` now
    // keeps `reverts.names`, the oracle file's parsed strings, while this side
    // asks the **declaration walk's realized verdict** (`withheld_fns`, what the
    // walk actually DECLINED at its site) through a name→`LocalDefId` index
    // built here from `tcx.hir_body_owners()`.
    //
    // ⚠ **WHAT THAT DOES AND DOES NOT BUY (round-4 review, adopted).**
    // `recon-drop = (render-drop ∧ reached) ∨ unresolved` — the `unresolved`
    // term is round 5's fail-closed arm, and the round-5 review caught this
    // formula still missing it. It is a PIN (unreachable, and zero-gated), so
    // the equality below is unaffected in practice; the term is stated because
    // a formula that omits a live disjunct is how the last three overclaims
    // started. With it, and the gated
    // `withheld_missing`/`_surplus == 0` plus the ledger GAP line force
    // `withheld_fns == reverts.fns` — so **on a green gate the two predicates
    // are EQUAL and the corpus zeros below are ENTAILED, not independent
    // evidence.** What is genuinely measured here is (a) a mutation of
    // `render`'s own filter line, and (b) splice-mechanics divergence between
    // [`splice_kept`] and `apply::apply`. The falsifiability that matters is the
    // unit negative control, which injects a one-sided divergence directly.
    //
    // **Compared at FILE level** — §27 offered "calibrate the per-function
    // splice OR say plainly it is a different derivation", and the second branch
    // is taken. ⚠ The round-4 justification for it was WRONG and is corrected
    // here: it claimed phase 3 keeps a cross-vocabulary split because "its span
    // side filters by NAME while its AST side consults `reverts.fns` by
    // `DefId`". **That holds for DECLARATIONS ONLY.** For seams both of phase
    // 3's sides call `reverts.keeps(name)` — the AST seam-target filter above
    // and the span-side per-function filter below — so no such split exists
    // there. The seam path's corroboration is now ATTRIBUTION-side (item 1),
    // which is where a seam's revert decision actually lives.
    //
    // **What stays uncalibrated is the per-function path's OFFSET REBASING**
    // (`base + e.lo`, then `lo - flo`) — named rather than covered by an
    // inference; the predicate and [`splice_kept`] are shared with it.
    //
    // ⚠ `emit_files` calls `render` with an EMPTY revert set — it has already
    // dropped reverted SUBJECTS at plan-build time — so `emission.files` still
    // carries seam edits owned by reverted callees. Comparing against that
    // would measure an expected difference and prove nothing, so this
    // re-renders with `reverts.names`, which is what production passes.
    let reverted_names: std::collections::BTreeSet<String> =
        reverts.names.iter().cloned().collect();
    // **THE ROLLBACKS ARE NOT DISCARDED.** `let (files, _) = render(..)` is
    // `let _ = s.finish()` wearing different clothes — the third appearance of
    // that shape in this milestone, and I wrote it inside the item repairing a
    // hazard. A rollback is the ONE production-coherence signal this gate
    // uniquely has: `apply` emits one when an edit could not be placed
    // coherently, and nothing else in either gate reads them.
    let (rendered_files, rollbacks) =
        super::render(&emission.plan, &emission.texts, &reverted_names);
    p.render_rollbacks = rollbacks.len();
    for rb in rollbacks.iter().take(4) {
        p.render_examples.push(format!("ROLLBACK {rb:?}"));
    }
    // **THE WALK'S OWN VERDICT, projected to the owner half of its key.** A
    // function lands here only by having been reached and declined at
    // `rewrite_decl`'s site check — behaviour, not a set membership copied from
    // the input.
    let withheld_fns: FxHashSet<LocalDefId> =
        decls_stats.withheld_ids.iter().map(|(d, _)| *d).collect();
    // The name→`DefId` bridge, built from the COMPILER rather than from the
    // oracle parse. A `Vec` per name because `def_path_str` is not injective on
    // this corpus (295 duplicate `fn` names in brotli alone) and collapsing that
    // silently is the registered hazard itself.
    let mut owners_by_name: FxHashMap<String, Vec<LocalDefId>> = FxHashMap::default();
    for did in tcx.hir_body_owners() {
        owners_by_name
            .entry(tcx.def_path_str(did.to_def_id()))
            .or_default()
            .push(did);
    }
    let recon = reconstruct_kept_files(
        &emission.plan,
        &emission.texts,
        &owners_by_name,
        &withheld_fns,
    );
    p.render_plan_files = emission.plan.by_file.len();
    p.render_expected_empty = recon.expected_empty;
    p.render_owner_unresolved = recon.owner_unresolved;
    p.render_owner_split = recon.owner_split;
    let calib = compare_rendered(&recon.files, &rendered_files);
    p.render_compared = calib.compared;
    p.render_differing = calib.differing;
    p.render_absent = calib.absent;
    p.render_surplus = calib.surplus;
    p.render_examples.extend(calib.examples);

    // ---- PHASE 4's ledger, on the new layer ----
    p.decided_subjects = table
        .entries
        .iter()
        .filter(|(_, d)| !matches!(d, super::decision::Decision::Degraded(_)))
        .count();
    p.ast_decl_placed =
        decls_stats.rewritten + decls_stats.slice_rewritten + decls_stats.opt_rewritten;
    p.ast_decl_unplaced = decls_stats.not_a_pointer_decl;
    p.ast_use_unmatched = grafts_stats.unmatched;
    p.orphan_subject = decls_stats.orphan_subject;
    p.decl_refused = decls_stats.refused;
    p.reverted_withheld = decls_stats.reverted_withheld;

    // **THE RECONCILIATION — identities, not cardinalities.**
    let placed: FxHashSet<(LocalDefId, HirId)> = decls_stats.placed_ids.iter().copied().collect();
    p.placed_ids = placed.len();
    p.placed_dup = decls_stats.placed_ids.len() - placed.len();
    let recon = reconcile_identities(&survivors, &placed, &reverted_ids, |k| {
        labels.get(k).cloned().unwrap_or_else(|| format!("{k:?}"))
    });
    p.recon_missing = recon.missing;
    p.recon_surplus = recon.surplus;
    p.recon_reverted_placed = recon.reverted_placed;
    // The classes a site-level counter CAN name, subtracted. What is left is
    // the `local_map` miss and the never-visited node, which have no possible
    // site counter — so the residue is reported rather than argued away.
    p.recon_missing_unattributed = recon.missing as i64
        - decls_stats.orphan_subject as i64
        - decls_stats.not_a_pointer_decl as i64
        - decls_stats.refused as i64;
    // **ITS OWN CHANNEL, not `examples`.** Two faults found reviewing this
    // before the sweep landed. The span loop below appends its token-difference
    // examples under an `examples.len() < 6` cap, so a reconciliation failure
    // would have SUPPRESSED every phase-3 diagnostic — two instruments sharing
    // one channel, newest wins. And `report::sanitize` truncates a row value at
    // 120 chars, so a `" | "`-joined list of up to twelve rows would have cut
    // away the very names the reconciliation exists to produce. The charter
    // asks for mismatches as typed rows NAMING the function; a truncated join
    // does not satisfy it.
    p.recon_examples = recon.examples;

    // **THE WITHHELD SIDE, AT IDENTITY LEVEL — round 4's item 2.**
    //
    // Codex's round-3 [high], and it is F2's own defect class one round after
    // repairing F2: `reverted_withheld` is a SCALAR. If two AST declarations
    // resolve to reverted subject `A` while subject `B` is never reached, the
    // count still equals the two oracle lines, survivor reconciliation stays
    // empty and `reverted_placed` stays zero — so *"every reverted subject's
    // declaration was reached"* was asserted by a check that cannot see it.
    //
    // Compared against `reverted_ids` — the TABLE-derived half — while the
    // retained scalar is compared against the oracle's LINE COUNT. Two sources,
    // so both lines are kept.
    let withheld: FxHashSet<(LocalDefId, HirId)> =
        decls_stats.withheld_ids.iter().copied().collect();
    p.withheld_ids = withheld.len();
    p.withheld_dup = decls_stats.withheld_ids.len() - withheld.len();
    // The third argument is deliberately EMPTY and its output deliberately
    // unread: `reverted_placed` asks "did the walk place something reverted",
    // which is the survivor reconciliation's question, not this one. Passing the
    // reverted set here would make it fire on every row and mean nothing.
    let wrecon = reconcile_identities(&reverted_ids, &withheld, &FxHashSet::default(), |k| {
        labels.get(k).cloned().unwrap_or_else(|| format!("{k:?}"))
    });
    p.withheld_missing = wrecon.missing;
    p.withheld_surplus = wrecon.surplus;
    p.withheld_examples = wrecon.examples;

    // **A composition-guard refusal is STOP-class here.** Carried into the
    // result rather than swallowed: this gate is the first place three
    // transforms meet inside one function body.
    //
    // **NO LONGER ADDED TO `differing`** (boundary review): the double-count
    // meant `p4_refused` could never be a *sole* failure, so phase 4 had four
    // independent checks while claiming five. A refusal is still fail-closed —
    // `p4_refused` gates it directly — and a refused declaration still makes
    // its function's text differ, so nothing is lost by removing the second
    // path to the same stop.
    if !guard.refused.is_empty() {
        p.examples.push(format!(
            "COMPOSITION REFUSAL x{}: {:?}",
            guard.refused.len(),
            &guard.refused[..guard.refused.len().min(3)]
        ));
    }
    p.ast_refused = guard.refused.len();

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
                            if kind.starts_with("Ref") =>
                        {
                            "arm1"
                        }
                        super::plan::Justification::KindDecision { .. } => "arm2",
                        super::plan::Justification::SeamAdapter { .. } => "arm3",
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
        // **THE SAME SPLICE HELPER THE CALIBRATION USES** (round-4 item 1b's
        // shared-mechanics half). This loop was a second hand-written copy of
        // `splice_kept`'s body — back-to-front, same bounds guard — so the
        // calibration was measuring a splice discipline this path only
        // resembled. One function now, and what remains genuinely uncalibrated
        // is this path's OFFSET REBASING above (`base + e.lo`, then `lo - flo`),
        // which is named in the calibration's own comment rather than covered by
        // an inference from file equality.
        //
        // The predicate is deliberately NOT shared — see that comment for why
        // sharing it would damage phase 3.
        let mut ranges: Vec<(usize, usize, &str)> = mine
            .iter()
            .map(|(lo, hi, rep, _)| (*lo, *hi, *rep))
            .collect();
        let span_text = splice_kept(&orig, &mut ranges);

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

/// **APPLY SURVIVING EDITS THE WAY THIS GATE APPLIES THEM — back to front.**
///
/// Extracted from the render calibration so the reconstruction has a witness
/// that needs no `TyCtxt`: the round-3 testing review's point was that a broken
/// reconstruction could not fail anything, since the calibration is REPORTED
/// rather than gated (deliberately — the charter asked for one comparison, not
/// permanent wiring). A number nothing can falsify is the shape this whole
/// milestone keeps repairing.
///
/// Back-to-front because the offsets address the ORIGINAL text, which is the
/// same discipline `apply` uses and the same one the per-function splice uses.
pub(crate) fn splice_kept(source: &str, kept: &mut [(usize, usize, &str)]) -> String {
    kept.sort_by_key(|(lo, ..)| std::cmp::Reverse(*lo));
    let mut out = source.to_owned();
    for (lo, hi, rep) in kept.iter() {
        if *lo <= *hi && *hi <= out.len() {
            out.replace_range(*lo..*hi, rep);
        }
    }
    out
}

/// **THE RECONSTRUCTION'S VERDICT ON ONE EDIT — derived the WALK's way.**
///
/// Round 4's item 1. The round-3 calibration asked `reverts.keeps(&e.owner_fn)`
/// while `render` asked `!reverted.contains(&edit.owner_fn)` — the same set, the
/// same key, the same strings — so **0-differing was forced before the sweep
/// ran** and the comparison measured splice mechanics, not the revert decision.
///
/// This side asks a different question of a different object: *did the
/// declaration walk DECLINE this owner at its site?* `withheld` is the walk's
/// realized behaviour projected onto `LocalDefId`, and `candidates` comes from an
/// index built off `tcx.hir_body_owners()`. Neither reads `reverts`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg(test)]
pub(crate) enum OwnerVerdict {
    Kept,
    Withheld,
    /// The name resolved to no local body owner.
    Unresolved,
    /// Several body owners share the name and **disagree** about withheld-ness
    /// — the homonym hazard at the one place it can change a verdict.
    Split,
}

#[cfg(test)]
impl OwnerVerdict {
    /// **THE TWO UNDECIDABLE ARMS FAIL IN OPPOSITE DIRECTIONS, AND EACH
    /// DIRECTION IS THE LOUD ONE FOR ITS ARM.** Round 4 claimed both were
    /// "fail-open and loud"; that was true of `Split` and **false of
    /// `Unresolved`**, which is the correction round 5 lands (C2).
    ///
    /// - `Unresolved` **DROPS** (fail-closed). It cannot be kept: `reverts.names`
    ///   is a *subset* of the same `def_path_str`-over-`hir_body_owners` strings
    ///   `owners_by_name` is keyed by, so a name absent from the index is
    ///   necessarily absent from the revert set — `render` keeps it, and a
    ///   reconstruction that also kept it would agree **because both failed
    ///   identically**, with no text difference to surface. Dropping makes
    ///   `render_differing` fire.
    /// - `Split` **KEEPS**. A split needs at least one reverted candidate, whose
    ///   name is therefore in `reverts.names`, so `render` drops it — keeping
    ///   makes `render_differing` fire here too.
    ///
    /// Neither arm relies on that reasoning alone: both counters are zero-gated
    /// in [`P4_IDENTITY_ZERO_KEYS`] as of round 5, so the text divergence is
    /// defense in depth rather than the only signal.
    pub(crate) fn keeps_edit(self) -> bool {
        match self {
            OwnerVerdict::Kept | OwnerVerdict::Split => true,
            OwnerVerdict::Withheld | OwnerVerdict::Unresolved => false,
        }
    }
}

#[cfg(test)]
pub(crate) fn owner_verdict<D: Eq + std::hash::Hash>(
    candidates: Option<&[D]>,
    withheld: &FxHashSet<D>,
) -> OwnerVerdict {
    let Some(cands) = candidates.filter(|c| !c.is_empty()) else {
        return OwnerVerdict::Unresolved;
    };
    match cands.iter().filter(|d| withheld.contains(*d)).count() {
        0 => OwnerVerdict::Kept,
        n if n == cands.len() => OwnerVerdict::Withheld,
        _ => OwnerVerdict::Split,
    }
}

/// **SEAM OWNER ATTRIBUTION, DERIVED A SECOND TIME — round 5's item 1.**
///
/// Round 4's finding, and the one that kept phase 4 shut: the revert decision has
/// two halves — *which owner an edit belongs to*, and *whether that owner is
/// reverted* — and round 4 duplicated only the second. For a SEAM edit the first
/// half **is** the revert decision, because `plan` filters subjects but pushes
/// every seam unconditionally, so `owner_fn` is the only thing standing between a
/// reverted callee and a transformed call site.
///
/// That string is produced once, at `decision::seam`'s `plan.edits.push`, from
/// the callee that keys `facts.call_args` — and `render`, this gate's
/// reconstruction, the AST seam map and the span splice all consume it without
/// any of them able to disagree with it.
///
/// This derives it again as a **SECOND COPY** of the same computation, keyed by
/// the argument span instead of by the callee.
///
/// ⚠ **WHAT THAT IS AND IS NOT — corrected after the round-5 adversarial review,
/// which falsified the first version of this paragraph.** That version said the
/// owner is "looked up by *where the edit lands* rather than by the map key it
/// was filed under". **That is false.** `emitability` files the map key
/// `local_did` and the `Arg { span: arg.span }` inside the *same*
/// `if let ExprKind::Call(callee, args)`, in the *same* `args` loop — so the two
/// are one derivation indexed two ways, not two derivations.
///
/// This function is [`super::decision::emitability::collect`]'s arm 5 with one
/// predicate removed (`locals.contains`). The consequences are exact and are
/// labelled rather than argued:
///
/// - **`unlocated` is a PIN, not a measurement.** A strictly weaker predicate
///   chain inserts an entry wherever `emitability` produced one, so a seam key
///   is always present. It fires only if the two copies diverge structurally.
/// - **`agree == seam_edits` is ENTAILED given `ambiguous == 0`** whenever both
///   copies are correct — which is the normal state of any differential between
///   two correct implementations, and is why the number is corroboration rather
///   than independent evidence.
/// - **`ambiguous` is the only unconditionally measured content**: a census of
///   argument spans resolving to several distinct callees.
///
/// **What it is nonetheless LIVE against** — the reason it is not vacuous: a
/// defect in either copy. Principally `seam::synthesize`'s ~25-line transport
/// (`owner_fn: def_path_str(site.caller)` fires `mismatch`; a wrong `span` fires
/// `unlocated`), and also `emitability`'s own keying, since this walk re-resolves
/// the callee rather than reading that map. Nothing in the gate forces
/// `mismatch == 0`; only the code under test being correct does.
///
/// **Shared steps, stated in full** (the first version conceded only
/// `Res::Def`): the body enumeration, the `ExprKind::Call` match, the
/// `QPath::Resolved`/`Res::Def`/`as_local` chain, `def_path_str` — which this
/// file measures as NON-INJECTIVE — and the `for arg in args` pairing. A
/// cross-homonym mis-attribution is invisible here by construction; that bound
/// rests on `revert_resolution_failure`, not on this corroboration.
///
/// Body enumeration matches `collect` exactly so a body one walk sees and the
/// other does not cannot present as a mismatch. The index is deliberately NOT
/// filtered by the functions-under-consideration list: a superset can only make
/// lookups succeed, never invent a disagreement.
#[cfg(test)]
pub(crate) fn call_arg_owners(
    tcx: rustc_middle::ty::TyCtxt<'_>,
) -> FxHashMap<(u32, u32), Vec<String>> {
    use rustc_hir::intravisit::{self, Visitor};

    struct ArgOwners<'a, 'tcx> {
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        out: &'a mut FxHashMap<(u32, u32), Vec<String>>,
    }
    impl<'tcx> Visitor<'tcx> for ArgOwners<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            // **DIRECT CALLS ONLY**, which is exactly the shape `call_args`
            // records — a method call produces no seam, so widening here would
            // add index entries no seam edit can ever key into.
            if let rustc_hir::ExprKind::Call(callee, args) = &expr.kind
                && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = &callee.kind
                && let rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Fn, def_id) = path.res
                && let Some(local_did) = def_id.as_local()
            {
                let owner = self.tcx.def_path_str(local_did.to_def_id());
                for arg in args.iter() {
                    self.out
                        .entry((arg.span.lo().0, arg.span.hi().0))
                        .or_default()
                        .push(owner.clone());
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut out: FxHashMap<(u32, u32), Vec<String>> = FxHashMap::default();
    for owner in tcx.hir_body_owners() {
        let body = tcx.hir_body_owned_by(owner);
        let mut v = ArgOwners { tcx, out: &mut out };
        v.visit_body(body);
    }
    out
}

/// The per-seam verdict of the second derivation.
#[derive(Default, Debug)]
#[cfg(test)]
pub(crate) struct SeamOwnerRecon {
    /// The independent derivation names the same owner the edit carries.
    pub agree: usize,
    /// **THE CLASS ROUND 5 EXISTS FOR.** The edit's `owner_fn` is not the callee
    /// of the call its argument sits in — so the revert filter is asking about
    /// the wrong function, and every downstream counter agrees with it.
    pub mismatch: usize,
    /// A seam edit whose argument span matches no direct-call argument.
    ///
    /// ⚠ **A PIN.** `call_arg_owners`' predicate chain is strictly weaker than
    /// the one that produced these spans, so its index is a SUPERSET of the seam
    /// keys and this cannot fire while both copies walk the same construct. It
    /// is gated so that a structural divergence between them cannot land
    /// silently.
    pub unlocated: usize,
    /// One argument span naming several DISTINCT callees — a span collision, and
    /// undecidable rather than wrong. Counted apart so it can never be read as
    /// agreement.
    pub ambiguous: usize,
    pub examples: Vec<String>,
}

/// Reconcile carried seam owners against the independent span-keyed derivation.
///
/// Pure and rustc-free in its signature so the injection witness the charter asks
/// for — *a mis-attributed `owner_fn` MUST fire it* — needs no compiler session.
#[cfg(test)]
pub(crate) fn reconcile_seam_owners<'a>(
    edits: impl Iterator<Item = ((u32, u32), &'a str)>,
    index: &FxHashMap<(u32, u32), Vec<String>>,
) -> SeamOwnerRecon {
    let mut r = SeamOwnerRecon::default();
    for (key, carried) in edits {
        let mut push = |r: &mut SeamOwnerRecon, row: String| {
            if r.examples.len() < 4 {
                r.examples.push(row);
            }
        };
        match index.get(&key) {
            None => {
                r.unlocated += 1;
                push(
                    &mut r,
                    format!("SEAM-OWNER UNLOCATED @{key:?} carried={carried}"),
                );
            }
            Some(found) => {
                let distinct: std::collections::BTreeSet<&str> =
                    found.iter().map(String::as_str).collect();
                if distinct.len() > 1 {
                    r.ambiguous += 1;
                    push(
                        &mut r,
                        format!(
                            "SEAM-OWNER AMBIGUOUS @{key:?} carried={carried} found={distinct:?}"
                        ),
                    );
                } else if distinct.contains(carried) {
                    r.agree += 1;
                } else {
                    r.mismatch += 1;
                    push(
                        &mut r,
                        format!(
                            "SEAM-OWNER MISMATCH @{key:?} carried={carried} derived={distinct:?}"
                        ),
                    );
                }
            }
        }
    }
    r
}

/// The reconstruction's output, and the classes it could not decide.
#[derive(Default, Debug)]
#[cfg(test)]
pub(crate) struct Reconstruction {
    pub files: std::collections::BTreeMap<super::plan::FileKey, String>,
    pub expected_empty: usize,
    pub owner_unresolved: usize,
    pub owner_split: usize,
}

/// **THE RECONSTRUCTION — its signature guards ONE of the two ways back.**
///
/// Round 4 de-tautologized the calibration, and the natural way to undo that is
/// a one-token edit: swap the verdict for `reverts.keeps(&e.owner_fn)` and the
/// two sides consume one predicate again. **No corpus number can catch that** —
/// a tautology's whole property is that it still reads 0 — and a unit test that
/// reassembles the loop from its pieces would not catch it either.
///
/// So the loop lives here, where **there is no `RevertSet` to reach for**: it
/// takes the plan, the texts, a name→owner index and the walk's withheld set,
/// and nothing else. Restoring the tautology *inside this function* therefore
/// requires threading a new parameter through the signature.
///
/// ⚠ **AND THAT IS THE LIMIT OF IT** (round-4 review; round 4's own doc claimed
/// the signature was "the guard", full stop). The CALL SITE is the other way
/// back: `phase3_fn_parity` builds `withheld_fns` from
/// `decls_stats.withheld_ids`, and rewriting that one line to derive it from
/// `reverts.fns` restores the tautology with **no signature change** — and the
/// negative control would not notice, because it drives this function directly
/// with a `withheld` set of its own. The call site is guarded by review, not by
/// construction.
#[cfg(test)]
pub(crate) fn reconstruct_kept_files<D: Eq + std::hash::Hash>(
    planned: &super::plan::Plan,
    texts: &std::collections::BTreeMap<super::plan::FileKey, String>,
    owners_by_name: &FxHashMap<String, Vec<D>>,
    withheld: &FxHashSet<D>,
) -> Reconstruction {
    let mut r = Reconstruction::default();
    // **THE FABRICATED-EXTENT CONST, RE-DERIVED** (repaired 2026-08-15,
    // adversarial finding ADV-FAB-05).
    //
    // `render` adds a crate-level const when a fabricated adapter survives. This
    // reconstruction walked `by_file` and nothing else, so it had **no
    // representation of the const at all** — and the calibration compares the
    // two at file-text level. It is green today only because the frozen oracle's
    // revert set reverted every function fabrication unblocks, so no fabricated
    // adapter survives in this frame: an ENTAILED zero, exactly the shape the
    // REARM pin was labelled for, one gate over. At the first oracle refresh in
    // which one survives, the gate would have fired **on correct behaviour** and
    // read as a render defect.
    //
    // Re-derived rather than shared: this stays a second implementation of the
    // same rule, which is what the calibration is for.
    let const_survives = planned.by_file.values().flatten().any(|e| {
        matches!(
            e.justification,
            super::plan::Justification::SeamAdapter {
                fabricated: true,
                ..
            }
        ) && owner_verdict(owners_by_name.get(&e.owner_fn).map(|v| &v[..]), withheld).keeps_edit()
    });
    let const_target = const_survives
        .then(|| {
            planned
                .root_file
                .clone()
                .zip(planned.len_const_item.clone())
        })
        .flatten();
    for (key, edits) in &planned.by_file {
        let mut kept: Vec<(usize, usize, &str)> = Vec::new();
        for e in edits {
            let verdict = owner_verdict(owners_by_name.get(&e.owner_fn).map(|v| &v[..]), withheld);
            match verdict {
                OwnerVerdict::Unresolved => r.owner_unresolved += 1,
                OwnerVerdict::Split => r.owner_split += 1,
                OwnerVerdict::Kept | OwnerVerdict::Withheld => {}
            }
            if verdict.keeps_edit() {
                kept.push((e.lo, e.hi, e.replacement.as_str()));
            }
        }
        let const_here = const_target.as_ref().filter(|(root, _)| root == key);
        let const_text;
        if let Some((_, item)) = const_here
            && let Some(source) = texts.get(key)
        {
            const_text = format!("\n{item}\n");
            kept.push((source.len(), source.len(), const_text.as_str()));
        }
        if kept.is_empty() {
            // **REPORTED, not `continue`d in silence.** `render` skips such a
            // file too, so the two agree by both emitting nothing — and the
            // agreement is only meaningful because `surplus` checks that
            // `render` really did skip it.
            r.expected_empty += 1;
            continue;
        }
        // `emit_files` errors out if any planned file lacks text, so a miss here
        // is unrepresentable rather than merely unlikely — and if it ever became
        // representable, the file would land in NO population and the gated
        // conservation identity would fail rather than absorb it. That is
        // deliberate: a silent `continue` into no bucket is the exact shape
        // round 3's comparison used to exclude the fully-reverted programs.
        let Some(source) = texts.get(key) else {
            continue;
        };
        r.files.insert(key.clone(), splice_kept(source, &mut kept));
    }
    r
}

/// The symmetric file comparison — **over the UNION of keys**.
///
/// Round-3's loop iterated the reconstruction's keys and `continue`d on an empty
/// surviving set, so a `render` that emitted a file it should not have
/// incremented nothing, and the fully-reverted programs — the population where a
/// revert defect actually shows — were excluded from the denominator by
/// construction. Codex's [high], and it is the half that makes the number mean
/// something.
#[derive(Default, Debug)]
#[cfg(test)]
pub(crate) struct RenderCalibration {
    pub compared: usize,
    pub differing: usize,
    /// Reconstructed, not emitted by `render`.
    pub absent: usize,
    /// Emitted by `render`, and the reconstruction says fully reverted.
    pub surplus: usize,
    pub examples: Vec<String>,
}

#[cfg(test)]
pub(crate) fn compare_rendered<K: Ord + std::fmt::Debug>(
    recon: &std::collections::BTreeMap<K, String>,
    rendered: &std::collections::BTreeMap<K, String>,
) -> RenderCalibration {
    let mut c = RenderCalibration::default();
    let mut push = |c: &mut RenderCalibration, row: String| {
        if c.examples.len() < 4 {
            c.examples.push(row);
        }
    };
    for (key, mine) in recon {
        match rendered.get(key) {
            Some(theirs) if theirs == mine => c.compared += 1,
            Some(_) => {
                c.compared += 1;
                c.differing += 1;
                push(
                    &mut c,
                    format!("RENDER-GAP {key:?}: reconstruction != render"),
                );
            }
            None => {
                c.absent += 1;
                push(
                    &mut c,
                    format!("RENDER-GAP {key:?}: render emitted no file"),
                );
            }
        }
    }
    for key in rendered.keys() {
        if !recon.contains_key(key) {
            c.surplus += 1;
            push(
                &mut c,
                format!("RENDER-GAP {key:?}: render emitted a FULLY REVERTED file"),
            );
        }
    }
    c
}

/// **A MAP INSERT THAT COUNTS ITS OWN COLLISIONS — one mechanism, one witness.**
///
/// Three joins in this file build a lookup map from a table that may contain two
/// entries for one key, and a silent overwrite makes the map hold fewer edits
/// than the table does — every downstream count then agrees with itself while
/// being short. Each join had grown its own hand-written
/// `if map.insert(..).is_some() { n += 1 }`, and the testing review's finding was
/// exact: the *gate* was witnessed at the row level and the **producer branch was
/// not**, in the same change whose own doc says a counter nothing exercises and a
/// gate over a counter that cannot move are the same failure wearing two hats.
///
/// One helper, so the branch has one witness instead of three that never got
/// written.
pub(crate) fn insert_counting<K: Eq + std::hash::Hash, V>(
    map: &mut FxHashMap<K, V>,
    key: K,
    value: V,
    collisions: &mut usize,
) {
    if map.insert(key, value).is_some() {
        *collisions += 1;
    }
}

/// **IDENTITY-SET RECONCILIATION — what a count-based ledger cannot do.**
///
/// The phase-4 boundary review's F2, in one sentence: `p4_placed == emitted`
/// compares two *cardinalities* over one filtered population, so a
/// same-cardinality identity error selects the wrong subjects on both sides
/// together and every line still closes. The honest label for the equality was
/// a **surjectivity check on the walk** — it showed the walk reached every
/// decided declaration once, never that the *set* was right.
///
/// This is the remedy, and it is deliberately **pure and generic**: no
/// `TyCtxt`, no rustc identifier types in the signature, so its own failure
/// modes are exercisable by unit tests. Logic only a corpus sweep can run is
/// logic with no witness — R8, and the reason `p3_row_failures` was extracted
/// from the corpus loop before it.
#[derive(Default, Debug)]
pub(crate) struct IdentityRecon {
    /// A survivor the walk never placed. Every `local_map` miss, unvisited
    /// node, orphaned `impl`-method subject and guard refusal lands here **by
    /// identity**, whether or not a site-level counter could name it.
    pub missing: usize,
    /// Something the walk placed that is not a survivor.
    pub surplus: usize,
    /// **PHASE 4's OWN PROPERTY, named**: a subject the revert set took back
    /// and the walk transformed anyway. A strict sub-class of
    /// [`Self::surplus`] — survivors and reverted are disjoint by construction
    /// — reported apart because it is the semantic violation the phase exists
    /// to exclude, and a sub-class that says what it means beats a total that
    /// does not.
    pub reverted_placed: usize,
    /// Class-tagged, **sorted**, capped rows. Sorted because a set's iteration
    /// order is not an artifact's business.
    pub examples: Vec<String>,
}

/// Reconcile the identities a walk placed against the identities it owed.
///
/// `label` renders one identity for a human; it is never used for matching, so
/// two subjects sharing a label cannot merge.
pub(crate) fn reconcile_identities<T, F>(
    survivors: &FxHashSet<T>,
    placed: &FxHashSet<T>,
    reverted: &FxHashSet<T>,
    label: F,
) -> IdentityRecon
where
    T: Eq + std::hash::Hash,
    F: Fn(&T) -> String,
{
    let collect = |class: &'static str, rows: Vec<&T>| -> (usize, Vec<String>) {
        let mut named: Vec<String> = rows
            .into_iter()
            .map(|t| format!("{class}:{}", label(t)))
            .collect();
        named.sort();
        (named.len(), named)
    };
    let (missing, m_rows) = collect(
        "MISSING",
        survivors.iter().filter(|s| !placed.contains(s)).collect(),
    );
    let (surplus, s_rows) = collect(
        "SURPLUS",
        placed.iter().filter(|p| !survivors.contains(p)).collect(),
    );
    let (reverted_placed, r_rows) = collect(
        "REVERTED-PLACED",
        placed.iter().filter(|p| reverted.contains(p)).collect(),
    );
    let mut examples: Vec<String> = Vec::new();
    for rows in [m_rows, s_rows, r_rows] {
        examples.extend(rows.into_iter().take(4));
    }
    IdentityRecon {
        missing,
        surplus,
        reverted_placed,
        examples,
    }
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

    // ---- PHASE 4: the revert layer, re-derived ON THE NEW LAYER ----
    //
    // Phase 3 held the revert set fixed and tested the transform layer. Phase 4
    // asks the complementary question: does the AST layer PLACE an edit for
    // every surviving subject and for no reverted one? A transform layer known
    // good plus a revert layer checked here is what makes any later difference
    // attributable to one of the two.
    /// Every subject the decision table settled to an emitting form.
    pub decided_subjects: usize,
    /// Declarations the AST layer actually rewrote — arm 1 + arm 2's
    /// declaration half. Must equal [`Self::emitted_subjects`].
    pub ast_decl_placed: usize,
    /// A surviving subject whose declaration the walk could not reach. **Not a
    /// skip**: a decided subject the transform cannot place is a ledger
    /// movement, which is the whole content of the GAP-0 claim.
    pub ast_decl_unplaced: usize,
    /// Use edits whose span matched no AST node — a converted declaration left
    /// with a raw use under it, i.e. an ill-typed crate rather than a partial
    /// rewrite.
    pub ast_use_unmatched: usize,
    /// Composition-guard refusals across all three passes.
    ///
    /// **No longer folded into [`Self::differing`]** (boundary review): it was
    /// double-counted there, so it could never be a *sole* failure and phase 4
    /// had four checks wearing the label of five.
    pub ast_refused: usize,

    // ---- IDENTITY-SET RECONCILIATION — F2's remedy ----
    /// Distinct survivor identities. **Not a second spelling of
    /// [`Self::emitted_subjects`]**: that one counts table ENTRIES, this counts
    /// distinct `(fn_did, hir_id)` keys, so their difference is exactly the
    /// decision-map key collision that would otherwise drop a subject in
    /// silence.
    pub survivor_ids: usize,
    /// Distinct identities the declaration walk placed.
    pub placed_ids: usize,
    /// One identity placed more than once — invisible to a set, which is why
    /// the walk hands over a `Vec`.
    pub placed_dup: usize,
    pub recon_missing: usize,
    pub recon_surplus: usize,
    pub recon_reverted_placed: usize,
    /// [`Self::recon_missing`] minus the classes a site-level counter could
    /// name (`orphan_subject`, `ast_decl_unplaced`, `decl_refused`). The
    /// residue is the `local_map` miss and the never-visited node — the two
    /// paths with no possible site counter. **Signed**: a negative value means
    /// a subject was counted in two classes, which is an instrument fault of
    /// its own.
    pub recon_missing_unattributed: i64,
    /// An `impl`-method subject the walk reached with no owning function.
    pub orphan_subject: usize,
    /// **The site revert check's own denominator.** Decided subjects the walk
    /// reached and DECLINED because their owner is reverted. Non-zero is the
    /// evidence that `recon_reverted_placed`'s zero is a measurement rather
    /// than a construction — a zero here would mean the check never ran.
    ///
    /// Retained against `p3_reverted_subjects`, the oracle's **line count** —
    /// a different source from the table-derived `reverted_ids` the identity
    /// reconciliation below uses. The COVERAGE CLAIM lives there, not here.
    pub reverted_withheld: usize,
    /// Distinct identities the site check declined.
    pub withheld_ids: usize,
    /// One identity declined more than once. Half of the compensating pair a
    /// scalar cannot see; [`Self::withheld_missing`] is the other half.
    pub withheld_dup: usize,
    /// A reverted subject the walk NEVER REACHED. This is the number
    /// *"every reverted subject's declaration was reached"* actually needs.
    pub withheld_missing: usize,
    /// Something declined that the revert set did not take back.
    pub withheld_surplus: usize,
    /// The withheld reconciliation's rows, on their **own** channel — the
    /// two-instruments-one-channel defect this file has now repaired twice.
    pub withheld_examples: Vec<String>,
    /// The reconciliation's class-tagged rows, on their OWN channel — see the
    /// note at the assignment site for the two faults that kept them out of
    /// [`Self::examples`].
    pub recon_examples: Vec<String>,
    /// Declaration-pass refusals alone, for the attribution above.
    pub decl_refused: usize,

    // ---- THE TYPED FAILURE CLASSES, READ (F1) ----
    //
    // `let _ = s.finish();` threw the seam visitor's entire stats away, and
    // none of these was read anywhere in this gate. The false pass was
    // concrete: a seam rejected by BOTH the span locator and the AST walker
    // touches no caller function, appears in neither population, and leaves
    // parity green while a converted callee keeps an unadapted call site.
    //
    // The sibling gate that DOES read them (`arms_full`) runs with an empty
    // revert set, so seam placement under a REAL revert set was measured by
    // nothing anywhere — with 7 of the 68 compared functions seam-only.
    /// Seam targets surviving the revert filter — **the denominator**. A zero
    /// failure count over a zero population is not evidence, so the population
    /// travels with the counters.
    pub seam_targets: usize,
    pub seam_grafted: usize,
    pub seam_unmatched: usize,
    pub seam_multi_matched: usize,
    pub seam_unsupported: usize,
    pub seam_arg_not_found: usize,
    pub seam_len_absent: usize,
    pub seam_len_parse_failed: usize,
    pub seam_key_collisions: usize,
    /// The seam pass's own refusals — a term in the conservation identity, not
    /// a second gate (`p4_refused` gates the joint count across all passes).
    pub seam_refused: usize,

    // ---- SEAM OWNER ATTRIBUTION, SECOND DERIVATION (round 5, item 1) ----
    /// `table.seams.edits.len()` — the corroboration's DENOMINATOR, carried
    /// beside its counters because a zero-mismatch over a zero population is the
    /// shape this milestone keeps having to repair.
    pub seam_edits: usize,
    /// Seam edits whose carried `owner_fn` matches the span-keyed HIR
    /// derivation.
    pub seam_owner_agree: usize,
    /// **The class round 5 exists for**: the carried owner is not the callee of
    /// the call whose argument this edit replaces.
    pub seam_owner_mismatch: usize,
    /// A seam edit whose argument span is no direct-call argument.
    pub seam_owner_unlocated: usize,
    /// One argument span naming several distinct callees — undecidable, never
    /// counted as agreement.
    pub seam_owner_ambiguous: usize,
    /// Its OWN channel. The two-instruments-one-channel defect has been written
    /// into this file four times; this counter arrives with its own key.
    pub seam_owner_examples: Vec<String>,

    // ---- RENDER-GAP CALIBRATION (round-3 item 8) ----
    /// Files compared between this gate's own reconstruction and
    /// `bo_rewriter::render`'s output under the REAL revert set — the
    /// production applier, which no other check in this gate exercises.
    pub render_compared: usize,
    /// Files where the two disagree. **The whole point of the calibration**:
    /// nonzero is a finding about the gate's span-side reconstruction, not
    /// about the code under test.
    pub render_differing: usize,
    /// Files this gate reconstructed that `render` did not emit at all.
    pub render_absent: usize,
    /// **Files `render` emitted that the reconstruction says are FULLY
    /// REVERTED** — the direction round 3's comparison could not see at all,
    /// since it iterated the reconstruction's keys and skipped the empty ones.
    ///
    /// ⚠ **A PIN ONLY WHILE `render_owner_unresolved == 0` — and the round-5
    /// commit that wrote the unconditional proof below is the same one that
    /// broke it.** Round 4 called this "the first measurement of the
    /// fully-reverted population"; round 5 corrected that to a PIN with the
    /// proof *recon-Withheld(e) ⟹ owner ∈ `withheld_fns` ⊆ `reverts.fns` ⟹
    /// `owner_fn` ∈ `reverts.names` ⟹ `render` drops too*, contrapositively
    /// render-keeps ⟹ recon-keeps.
    ///
    /// **That proof covers only `Withheld`.** Since round 5 the reconstruction
    /// also drops on `Unresolved`, and an unresolvable name is by construction
    /// absent from `reverts.names`, so `render` KEEPS it: a file whose every
    /// otherwise-kept edit is unresolved is omitted by the reconstruction and
    /// emitted by `render`, firing this counter **from the reconstruction
    /// side**. "Fires only on a mutation of `render`'s own filter" is false.
    ///
    /// Both directions fail RED, so no green is laundered — `render_owner_
    /// unresolved` is itself zero-gated and fires first. The consequence is
    /// misdiagnosis, not a false pass.
    pub render_surplus: usize,
    /// Planned files whose surviving-edit set is empty on the reconstruction's
    /// derivation. The fully-reverted population, as a reported number rather
    /// than a silent `continue`.
    pub render_expected_empty: usize,
    /// `|plan.by_file|` — the conservation denominator, so every planned file
    /// accounts for itself as compared, absent or expected-empty.
    pub render_plan_files: usize,
    /// An edit whose `owner_fn` resolved to NO local body owner.
    ///
    /// ⚠ **A PIN, and FAIL-CLOSED as of round 5** — this doc said "fail-open
    /// (the edit is kept)" and the same commit made it drop. Unreachable:
    /// `collect_program` gathers only `ItemKind::Fn` body owners and
    /// `owners_by_name` is keyed over all of them, so every `owner_fn` resolves.
    /// **GATED** as of round 5, so its zero cannot be read as a measurement.
    pub render_owner_unresolved: usize,
    /// An edit whose `owner_fn` resolved to several body owners that DISAGREE
    /// about withheld-ness — the registered homonym hazard, at the one place it
    /// could change a verdict.
    ///
    /// ⚠ **A PIN**, unreachable while `revert_resolution_failure` errors on any
    /// reverted homonym. **FAIL-OPEN** (kept) — the opposite arm from
    /// `Unresolved` above, and the asymmetry is deliberate: see
    /// [`OwnerVerdict::keeps_edit`]. **GATED** as of round 5.
    pub render_owner_split: usize,
    /// **`render`'s own rollbacks** — an edit it could not place coherently.
    /// The one production-coherence signal this gate has, and it was being
    /// dropped on the floor.
    pub render_rollbacks: usize,
    /// The calibration's rows, on their OWN channel. Sharing `examples` with
    /// the phase-3 differential is the two-instruments-one-channel defect this
    /// file already repaired once, for `recon_examples`, in round 2 — and I
    /// reintroduced it here in round 3.
    pub render_examples: Vec<String>,
    /// Use targets surviving the revert filter — the other denominator.
    pub use_targets: usize,
    pub use_parse_failed: usize,
    pub use_multi_matched: usize,
    pub use_key_collisions: usize,
    /// Two table entries sharing one `(fn_did, hir_id)`, one overwriting the
    /// other in the walk's lookup map.
    pub decision_key_collisions: usize,
    /// The SPAN layer's own placement loss, pinned at 0 since S2b.3 and never
    /// read by this gate. `emitted` here is decisions-kept; the span layer's
    /// `emitted` subtracts this, and the two coincide only while it is zero.
    pub unplaceable: usize,
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
    let printed = rustc_ast_pretty::pprust::item_to_string(&parsed);
    // **FULL CONSUMPTION.** `parse_item` answers "the FIRST item in this text"
    // and never requires EOF, so `fn f() {} trailing` canonicalises to the
    // prefix and silently discards real output — the same prefix-acceptance
    // defect `graft_expr` was hardened against at the arm-2 boundary, applied
    // here at its new site.
    //
    // Whitespace-insensitive for the reason the corpus differential is:
    // reformatting is licensed, dropping tokens is not.
    let strip = |s: &str| -> String { s.chars().filter(|c| !c.is_whitespace()).collect() };
    if strip(&printed) != strip(text) {
        return None;
    }
    Some(printed)
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
    let (
        decls,
        grafts,
        seams,
        decl_inside_use,
        use_key_collisions,
        decision_key_collisions,
        surface,
        // The transformed krate — `arms_full` measures, it does not emit.
        // `ast_emitted_source` is the caller that wants it.
        _krate,
        _edited,
    ) = transform_inner(tcx, &RevertSet::default())?;
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
    d.decision_key_collisions = decision_key_collisions;
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

            let subject_hirs: FxHashSet<HirId> = decisions.keys().map(|(_, h)| *h).collect();
            // No revert set in these fixtures: the site check is a no-op, so
            // each test isolates the behaviour it names.
            let no_reverts: FxHashSet<LocalDefId> = FxHashSet::default();
            let mut guard = Composition::default();
            let mut v = RefDeclVisitor {
                local_map: &local_map,
                decisions: &decisions,
                global_map: &global_map,
                reverted_fns: &no_reverts,
                subject_hirs: &subject_hirs,
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
            assert!(
                stats.placed_ids.is_empty(),
                "and must contribute NO identity — the list is recorded at the \
                 realized rewrite, so every early return is a non-placement"
            );
            assert_eq!(stats.rewritten, 0, "and must not be transformed");
            assert!(
                guard.claim(ty_id, rustc_span::DUMMY_SP, "someone-else"),
                "THE POINT: the node must still be UNCLAIMED. Claiming before \
                 the shape check meant a declaration this pass cannot transform \
                 still owned its node, so a later transform that legitimately \
                 wanted it would be refused on behalf of work that never happened"
            );
        });
    }

    /// **THE ORPHAN CLASS, INJECTED — an `impl`-method subject is COUNTED, not
    /// skipped.**
    ///
    /// [`RefDeclVisitor::visit_item`] sets `current_fn` only on a top-level
    /// `ItemKind::Fn`, and `visit_assoc_item` is not overridden, so an `impl`
    /// method's params arrive with `current_fn` unset. Before this repair they
    /// returned with **no trace at all** — one of three loss classes the review
    /// found with no counter, and the one the AST layer can produce today.
    ///
    /// Corpus-zero for this class would be **structural, not evidential**, which
    /// is exactly why it ships with an injection rather than an argument: the
    /// two-zeros discipline says a counter whose zero no input can move is a
    /// counter with no witness.
    ///
    /// *Mutation-tested:* deleting the `subject_hirs.contains` branch drops
    /// `orphan_subject` to 0 and this fails; reverting the lookup order so
    /// `current_fn` is checked first makes the branch unreachable and it fails
    /// the same way.
    #[test]
    fn an_impl_method_subject_is_counted_not_skipped() {
        rustc_span::create_default_session_globals_then(|| {
            // The param is a genuine `*mut u32`, so nothing but the missing
            // owner can stop it — the shape check would otherwise take the
            // credit and the test would pass for the wrong reason.
            let mut krate =
                ::utils::ast::parse_crate("struct S; impl S { fn m(p: *mut u32) {} }".to_owned());
            let pat_id = {
                let rustc_ast::ItemKind::Impl(im) = &krate.items[1].kind else {
                    panic!("fixture's second item is an impl")
                };
                let rustc_ast::AssocItemKind::Fn(f) = &im.items[0].kind else {
                    panic!("fixture's impl holds one fn")
                };
                f.sig.decl.inputs[0].pat.id
            };

            let mut local_map = rustc_ast::node_id::NodeMap::default();
            local_map.insert(pat_id, rustc_hir::CRATE_HIR_ID);
            // DELIBERATELY EMPTY: no `impl` item maps to a `LocalDefId`, which
            // is the condition being modelled. The decision map is keyed on a
            // `fn_did` the walk will never learn.
            let global_map = rustc_ast::node_id::NodeMap::default();
            let mut decisions = FxHashMap::default();
            decisions.insert(
                (rustc_hir::def_id::CRATE_DEF_ID, rustc_hir::CRATE_HIR_ID),
                (DeclForm::Ref, true),
            );
            let subject_hirs: FxHashSet<HirId> = decisions.keys().map(|(_, h)| *h).collect();

            // No revert set in these fixtures: the site check is a no-op, so
            // each test isolates the behaviour it names.
            let no_reverts: FxHashSet<LocalDefId> = FxHashSet::default();
            let mut guard = Composition::default();
            let mut v = RefDeclVisitor {
                local_map: &local_map,
                decisions: &decisions,
                global_map: &global_map,
                reverted_fns: &no_reverts,
                subject_hirs: &subject_hirs,
                current_fn: None,
                guard: &mut guard,
                stats: RefDeclStats::default(),
            };
            v.visit_crate(&mut krate);
            let stats = v.stats;

            assert_eq!(
                stats.orphan_subject, 1,
                "a SURVIVOR reached with no owning function must be counted — \
                 this is the class that returned silently"
            );
            assert_eq!(stats.rewritten, 0, "and must not be transformed");
            assert!(stats.placed_ids.is_empty(), "and places no identity");
        });
    }

    /// **THE HOMONYM GATE — the registered hazard, fail-closed and witnessed.**
    ///
    /// `def_path_str` is not injective on this corpus (295 duplicate `fn` names
    /// in brotli alone), and the old check compared a NAME-keyed set against the
    /// wanted names, so one line naming a homonym over-reverted every match
    /// while every count still agreed.
    ///
    /// *Mutation-tested (M15):* widening the `n > 1` filter leaves the homonym
    /// undetected and fails the first assertion.
    #[test]
    fn revert_resolution_must_be_one_to_one() {
        // The conforming shape: every name resolves to exactly one function.
        let ok = [("a::f".to_owned(), 1usize), ("a::g".to_owned(), 1)];
        assert!(
            revert_resolution_failure(&ok, 2, 2, "x.reverts.txt").is_none(),
            "an injective resolution passes"
        );

        // **THE HOMONYM.** One name, two functions — and note the counts the
        // OLD check looked at still agree: 2 names wanted, 2 names seen. Only
        // the resolved-id count betrays it, which is why this takes both.
        let dup = [("a::f".to_owned(), 2usize), ("a::g".to_owned(), 1)];
        let why =
            revert_resolution_failure(&dup, 2, 3, "x.reverts.txt").expect("a homonym must fail");
        assert!(
            why.contains("MORE THAN ONE") && why.contains("a::f"),
            "and must NAME the offender: {why}"
        );

        // Under-resolution is the other direction and must not be silent.
        let short = [("a::f".to_owned(), 1usize)];
        assert!(
            revert_resolution_failure(&short, 2, 1, "x.reverts.txt")
                .expect("under-resolution must fail")
                .contains("one-to-one"),
        );
    }

    /// **THE COLLISION-COUNTING INSERT, witnessed at the PRODUCER.**
    ///
    /// Three joins used to carry a hand-written `insert(..).is_some()` and the
    /// testing review's finding was exact: the *gate* was witnessed at the row
    /// level and **the producer branch was not** — in the change whose own doc
    /// says a counter nothing exercises and a gate over a counter that cannot
    /// move are the same failure wearing two hats. One helper now, so the branch
    /// has one witness instead of three that never got written.
    ///
    /// *Mutation-tested (M12):* dropping the `.is_some()` guard so the counter
    /// never increments fails this test.
    #[test]
    fn a_colliding_insert_is_counted() {
        let mut map: FxHashMap<u32, &str> = FxHashMap::default();
        let mut n = 0usize;
        insert_counting(&mut map, 1, "a", &mut n);
        insert_counting(&mut map, 2, "b", &mut n);
        assert_eq!((map.len(), n), (2, 0), "distinct keys do not collide");

        // The collision: a second entry for a key the map already holds. The
        // map still reads 2, which is the whole hazard — every downstream count
        // agrees with itself while being one short.
        insert_counting(&mut map, 1, "c", &mut n);
        assert_eq!(
            (map.len(), n),
            (2, 1),
            "an overwrite must be COUNTED — the map's own length cannot show it"
        );
        assert_eq!(
            map.get(&1),
            Some(&"c"),
            "and the value is the later one, which is why the earlier edit is \
             the one that goes missing"
        );
    }

    /// **`placed_dup` with a GENUINE duplicate identity.**
    ///
    /// The row-level arithmetic was tested; the real subtraction
    /// (`placed_ids.len() − set.len()`) was not.
    ///
    /// ⚠ **I RECORDED THIS AS UNWITNESSABLE, AND THAT WAS WRONG.**
    ///
    /// Two attempts failed because `parse_crate` yields an **unresolved** crate
    /// in which every node carries `DUMMY_NODE_ID` (`NodeId(4294967040)`): the
    /// two params shared one `Ty` id, the composition guard refused the second
    /// claim, and the walk placed once. I measured that much correctly — and
    /// then drew the wrong conclusion from it, banking "not synthesizable at
    /// unit level" into the record.
    ///
    /// **The round-2 testing review declined to accept the limit**, pointing
    /// out that `NodeId::from_u32` is public and `Pat::id` / `Ty::id` are public
    /// fields. They are: the fixture below assigns its own ids and the walk
    /// places **twice under one identity with no refusal**, which is exactly the
    /// shape `placed_dup` exists to count. A measured premise (`DUMMY_NODE_ID`
    /// everywhere) does not license an unmeasured conclusion (*therefore
    /// nothing can be done*), and the distance between those two is where this
    /// went wrong.
    ///
    /// What survives from that episode is a real fixture rule for the file:
    /// **a witness needing two DISTINCT nodes must supply its own ids**, since
    /// the parser supplies none.
    #[test]
    fn one_identity_placed_twice_is_a_duplicate_not_a_second_subject() {
        rustc_span::create_default_session_globals_then(|| {
            let mut krate =
                ::utils::ast::parse_crate("fn f(p: *mut u32, q: *mut u32) {}".to_owned());
            // **THE FIXTURE ASSIGNS THE IDS.** `parse_crate` leaves every node
            // at `DUMMY_NODE_ID`, which is what made a first attempt collapse
            // into one placement plus one guard refusal — and what I then
            // recorded, wrongly, as "not synthesizable at unit level".
            // `NodeId::from_u32` and the `Pat`/`Ty` `id` fields are public, so
            // the fixture supplies the distinctness the parser does not. Found
            // by the round-2 testing review, which declined to accept the limit
            // as stated.
            let (item_id, pat_a, pat_b) = {
                let item = &mut krate.items[0];
                item.id = rustc_ast::node_id::NodeId::from_u32(900);
                let rustc_ast::ItemKind::Fn(f) = &mut item.kind else { panic!("fixture is a fn") };
                f.sig.decl.inputs[0].pat.id = rustc_ast::node_id::NodeId::from_u32(901);
                f.sig.decl.inputs[0].ty.id = rustc_ast::node_id::NodeId::from_u32(902);
                f.sig.decl.inputs[1].pat.id = rustc_ast::node_id::NodeId::from_u32(903);
                f.sig.decl.inputs[1].ty.id = rustc_ast::node_id::NodeId::from_u32(904);
                (
                    item.id,
                    f.sig.decl.inputs[0].pat.id,
                    f.sig.decl.inputs[1].pat.id,
                )
            };
            assert_ne!(pat_a, pat_b, "the fixture must supply DISTINCT ids");
            let mut local_map = rustc_ast::node_id::NodeMap::default();
            // **BOTH bindings resolve to ONE `HirId`** — the duplicate's source.
            // Their `Ty` nodes are distinct, so the composition guard admits
            // both claims and the walk places twice under one identity.
            local_map.insert(pat_a, rustc_hir::CRATE_HIR_ID);
            local_map.insert(pat_b, rustc_hir::CRATE_HIR_ID);
            let mut global_map = rustc_ast::node_id::NodeMap::default();
            global_map.insert(item_id, rustc_hir::def_id::CRATE_DEF_ID);
            let mut decisions = FxHashMap::default();
            decisions.insert(
                (rustc_hir::def_id::CRATE_DEF_ID, rustc_hir::CRATE_HIR_ID),
                (DeclForm::Ref, true),
            );
            let subject_hirs: FxHashSet<HirId> = FxHashSet::default();
            let no_reverts: FxHashSet<LocalDefId> = FxHashSet::default();
            let mut guard = Composition::default();
            let mut v = RefDeclVisitor {
                local_map: &local_map,
                decisions: &decisions,
                global_map: &global_map,
                reverted_fns: &no_reverts,
                subject_hirs: &subject_hirs,
                current_fn: None,
                guard: &mut guard,
                stats: RefDeclStats::default(),
            };
            // ONE pass. Both params are subjects under the same key.
            v.visit_crate(&mut krate);
            let stats = v.stats;

            let distinct: FxHashSet<(LocalDefId, HirId)> =
                stats.placed_ids.iter().copied().collect();
            assert_eq!(
                (stats.placed_ids.len(), distinct.len(), stats.refused),
                (2, 1, 0),
                "TWO placements under ONE identity and NO refusal — the real \
                 duplicate, produced by the mechanism `placed_dup` exists for"
            );
            assert_eq!(
                stats.placed_ids.len() - distinct.len(),
                1,
                "`placed_dup` is exactly this difference, and a set absorbs the \
                 second placement in silence — which is why the walk hands over \
                 a Vec and not a set"
            );
        });
    }

    /// **THE CALIBRATION'S NEGATIVE CONTROL — an injected ONE-SIDED revert
    /// divergence must FAIL. Round 4's acceptance.**
    ///
    /// This test is unconstructible against the round-3 calibration, and that is
    /// the whole distance the item travels: there was only ONE side to inject
    /// into. The reconstruction asked `reverts.keeps(&e.owner_fn)` while
    /// `render` asked `!reverted.contains(&edit.owner_fn)` — one set, one key,
    /// one vocabulary — so 0-differing was forced before the sweep ran.
    ///
    /// The two sides here derive the revert decision by different routes:
    /// `render` from a set of NAMES, the reconstruction from the set of
    /// `LocalDefId`s the declaration walk DECLINED. Point them at different
    /// functions and the texts must disagree.
    ///
    /// Pure: `render` needs no `TyCtxt`, only a plan, its texts, and a name set.
    ///
    /// *Mutation-tested:* M18 (reconstruction filters by the name set instead —
    /// the round-3 tautology restored) makes the NEGATIVE half report 0
    /// differing, i.e. green when it must be red.
    #[test]
    fn a_one_sided_revert_divergence_fails_the_calibration() {
        use super::super::plan;
        // Two edits in one file, owned by two different functions. The
        // replacement texts differ so a wrongly-kept edit cannot coincide with
        // a rightly-kept one.
        let key = plan::FileKey::Virtual("main.rs".to_owned());
        let source = "AA BB".to_owned();
        let edit = |lo: usize, hi: usize, rep: &str, owner: &str| plan::Edit {
            lo,
            hi,
            replacement: rep.to_owned(),
            justification: plan::Justification::KindDecision { kind: "Ref" },
            owner_fn: owner.to_owned(),
        };
        let mut planned = plan::Plan::default();
        planned.by_file.insert(
            key.clone(),
            vec![edit(0, 2, "aa", "a"), edit(3, 5, "bb", "b")],
        );
        let mut texts = std::collections::BTreeMap::new();
        texts.insert(key.clone(), source.clone());

        // The reconstruction's vocabulary: two distinct owner ids behind the
        // two names. `u32` stands in for `LocalDefId` — `owner_verdict` is
        // generic precisely so its failure modes need no compiler session.
        let by_name: FxHashMap<String, Vec<u32>> =
            [("a".to_owned(), vec![1u32]), ("b".to_owned(), vec![2u32])]
                .into_iter()
                .collect();
        // **THE PRODUCTION FUNCTION, not a copy of it.** A control that
        // reassembles the loop from its pieces witnesses the pieces and leaves
        // the assembly — which is where round 3's defect actually lived —
        // untested.
        let reconstruct = |withheld: &FxHashSet<u32>| {
            reconstruct_kept_files(&planned, &texts, &by_name, withheld).files
        };

        // ---- POSITIVE: the two sides name the SAME function ----
        let reverted: std::collections::BTreeSet<String> = ["b".to_owned()].into_iter().collect();
        let (rendered, rollbacks) = super::super::render(&planned, &texts, &reverted);
        assert!(rollbacks.is_empty(), "the fixture places cleanly");
        let agree = compare_rendered(&reconstruct(&[2u32].into_iter().collect()), &rendered);
        assert_eq!(
            (agree.compared, agree.differing, agree.absent, agree.surplus),
            (1, 0, 0, 0),
            "agreement about the revert decision must compare EQUAL — without \
             this half a calibration that always differed would pass"
        );

        // ---- NEGATIVE: one side withholds `a`, the other reverts `b` ----
        let split = compare_rendered(&reconstruct(&[1u32].into_iter().collect()), &rendered);
        assert_eq!(
            (split.compared, split.differing),
            (1, 1),
            "a ONE-SIDED revert divergence must FAIL the calibration — this is \
             the assertion the round-3 derivation could not host"
        );

        // ---- SURPLUS: `render` emits a file the reconstruction calls fully
        // reverted. Round 3 counted this as nothing, and the 5 programs it
        // excluded from the denominator were exactly the fully-reverted ones.
        let none_reverted: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        let (all_rendered, _) = super::super::render(&planned, &texts, &none_reverted);
        let both_withheld = reconstruct_kept_files(
            &planned,
            &texts,
            &by_name,
            &[1u32, 2u32].into_iter().collect(),
        );
        assert_eq!(
            (
                both_withheld.expected_empty,
                both_withheld.owner_unresolved,
                both_withheld.owner_split
            ),
            (1, 0, 0),
            "a file whose every edit is withheld must be COUNTED expected-empty, \
             not dropped out of every population — the conservation identity's \
             left-hand term"
        );
        let surplus = compare_rendered(&both_withheld.files, &all_rendered);
        assert_eq!(
            (surplus.compared, surplus.absent, surplus.surplus),
            (0, 0, 1),
            "a fully-reverted file that `render` emitted anyway must be COUNTED"
        );
        assert!(
            surplus
                .examples
                .iter()
                .any(|e| e.contains("FULLY REVERTED")),
            "and named: {:?}",
            surplus.examples
        );

        // ---- ABSENT: the reconstruction keeps edits, `render` emits nothing ----
        let absent = compare_rendered(
            &reconstruct(&FxHashSet::default()),
            &std::collections::BTreeMap::new(),
        );
        assert_eq!(
            (absent.compared, absent.absent, absent.surplus),
            (0, 1, 0),
            "the other direction is its own class, not folded into `differing`"
        );
    }

    /// **SEAM OWNER ATTRIBUTION — THE INJECTION WITNESS THE CHARTER ASKS FOR:
    /// a mis-attributed `owner_fn` MUST fire it.** Round 5's item 1.
    ///
    /// Round 4's blocking finding was that the seam owner string is produced
    /// once and consumed identically everywhere, so for seams — where the owner
    /// IS the revert decision — nothing could disagree with it. This drives the
    /// production [`reconcile_seam_owners`] against a hand-built span index.
    ///
    /// *Mutation-tested:* M22 (treat a mismatch as agreement) and M23 (count a
    /// missing index entry as agreement) each fail their own assertion.
    #[test]
    fn a_misattributed_seam_owner_fires_the_corroboration() {
        let mut index: FxHashMap<(u32, u32), Vec<String>> = FxHashMap::default();
        index.insert((10, 20), vec!["crate::callee_a".to_owned()]);
        index.insert((30, 40), vec!["crate::callee_b".to_owned()]);
        // A span whose call was resolved to two different callees — undecidable,
        // and it must not be laundered into either agreement or mismatch.
        index.insert(
            (50, 60),
            vec!["crate::callee_a".to_owned(), "crate::callee_b".to_owned()],
        );
        // The same callee recorded twice for one span is NOT ambiguity — a
        // repeated identical resolution is still one answer.
        index.insert(
            (70, 80),
            vec!["crate::callee_a".to_owned(), "crate::callee_a".to_owned()],
        );

        // ---- the control: every carried owner is the derived one ----
        let ok = reconcile_seam_owners(
            [((10, 20), "crate::callee_a"), ((30, 40), "crate::callee_b")].into_iter(),
            &index,
        );
        assert_eq!(
            (ok.agree, ok.mismatch, ok.unlocated, ok.ambiguous),
            (2, 0, 0, 0),
            "correct attribution must corroborate CLEAN — without this half a \
             check that flagged everything would pass as vigilance"
        );

        // ---- THE INJECTION: the edit at (10,20) claims callee_b ----
        //
        // This is exactly C1's scenario: a seam adapting a call to one function
        // carries another function's name, so the revert filter asks about the
        // wrong function and every downstream counter agrees with it.
        let bad = reconcile_seam_owners([((10, 20), "crate::callee_b")].into_iter(), &index);
        assert_eq!(
            (bad.agree, bad.mismatch),
            (0, 1),
            "a MIS-ATTRIBUTED owner_fn must fire the corroboration — this is the \
             assertion round 4 had no way to host"
        );
        assert!(
            bad.examples.iter().any(|e| e.contains("MISMATCH")
                && e.contains("callee_b")
                && e.contains("callee_a")),
            "and the row must name BOTH the carried and the derived owner: {:?}",
            bad.examples
        );

        // ---- the two undecidable classes, each its own ----
        let amb = reconcile_seam_owners([((50, 60), "crate::callee_a")].into_iter(), &index);
        assert_eq!(
            (amb.agree, amb.mismatch, amb.ambiguous),
            (0, 0, 1),
            "one span naming two callees is UNDECIDABLE — counting it as \
             agreement would let a span collision read as corroboration"
        );
        let dup = reconcile_seam_owners([((70, 80), "crate::callee_a")].into_iter(), &index);
        assert_eq!(
            (dup.agree, dup.ambiguous),
            (1, 0),
            "...but a repeated IDENTICAL resolution is one answer, not a split"
        );
        let miss = reconcile_seam_owners([((90, 99), "crate::callee_a")].into_iter(), &index);
        assert_eq!(
            (miss.agree, miss.unlocated),
            (0, 1),
            "a seam whose argument span is no call argument is its own class — \
             seams come only from call arguments, so this cannot be a nothing"
        );
    }

    /// **THE TWO UNDECIDABLE ARMS FAIL IN OPPOSITE DIRECTIONS — round 5's C2.**
    ///
    /// Round 4 shipped both as fail-open and claimed both were loud. `Split` was;
    /// `Unresolved` was not, because `reverts.names` is a subset of the index's
    /// own keys, so an unresolvable owner is one `render` keeps too — both sides
    /// agreed BECAUSE both failed, and no text difference existed to surface.
    ///
    /// *Mutation-tested:* M20 (fold `Split` into the dropped arm) and M24
    /// (restore `Unresolved` to fail-open) each flip their own assertion.
    #[test]
    fn the_two_undecidable_owner_arms_fail_in_opposite_directions() {
        let withheld: FxHashSet<u32> = [1u32].into_iter().collect();
        assert_eq!(
            owner_verdict(None, &withheld),
            OwnerVerdict::Unresolved,
            "a name resolving to nothing is its own class, not `Kept`"
        );
        assert_eq!(
            owner_verdict(Some(&[][..]), &withheld),
            OwnerVerdict::Unresolved,
            "an EMPTY candidate list is the same absence — a `Some(&[])` that \
             read as `Kept` would be an unresolved owner wearing a verdict"
        );
        assert_eq!(
            owner_verdict(Some(&[1u32][..]), &withheld),
            OwnerVerdict::Withheld
        );
        assert_eq!(
            owner_verdict(Some(&[2u32][..]), &withheld),
            OwnerVerdict::Kept
        );
        assert_eq!(
            owner_verdict(Some(&[1u32, 2u32][..]), &withheld),
            OwnerVerdict::Split,
            "homonyms that DISAGREE are the hazard; homonyms that agree are not"
        );
        assert_eq!(
            owner_verdict(Some(&[1u32, 1u32][..]), &withheld),
            OwnerVerdict::Withheld,
            "...and agreeing homonyms must NOT read as a split"
        );
        // **THE TWO DIRECTIONS, EACH ASSERTED SEPARATELY** — round 5's C2. A
        // single loop over "all undecidable arms keep" is what shipped in round
        // 4, and it encoded the very claim the review refuted.
        assert!(
            OwnerVerdict::Kept.keeps_edit(),
            "a resolved, unreverted owner keeps its edit"
        );
        assert!(
            !OwnerVerdict::Withheld.keeps_edit(),
            "a withheld owner drops its edit — the whole point of the filter"
        );
        assert!(
            !OwnerVerdict::Unresolved.keeps_edit(),
            "UNRESOLVED FAILS CLOSED. `reverts.names` is a subset of the index's \
             own keys, so `render` keeps an unresolvable owner too — keeping it \
             here would make both sides agree BECAUSE both failed, with no text \
             difference to surface. Dropping is what makes it loud."
        );
        assert!(
            OwnerVerdict::Split.keeps_edit(),
            "SPLIT FAILS OPEN, and the asymmetry is deliberate: a split needs a \
             reverted candidate, whose name IS in `reverts.names`, so `render` \
             drops it — keeping here is what produces the divergence"
        );
    }

    /// **WITHHELD AT IDENTITY LEVEL — round 4's item 2, and its ruled negative
    /// control: `A` withheld twice, `B` absent.**
    ///
    /// Codex's round-3 [high], which is F2's own defect class one round after
    /// F2 was repaired: `reverted_withheld` is a SCALAR, so two declarations
    /// resolving to reverted subject `A` while `B` is never reached leaves the
    /// count equal to the two oracle lines and every downstream line green. The
    /// coverage claim needs the SET.
    ///
    /// Both halves are exercised on ONE fixture, because they are one scenario:
    /// the walk produces the duplicate, and the reconciliation produces the
    /// absence.
    ///
    /// *Mutation-tested:* M16 (drop the `withheld_ids` push) collapses the
    /// walk half to `(0, 0)`; M17 (reconcile against `survivors` rather than
    /// `reverted_ids`) inverts missing and surplus.
    #[test]
    fn withheld_identities_are_reconciled_not_counted() {
        rustc_span::create_default_session_globals_then(|| {
            let mut krate =
                ::utils::ast::parse_crate("fn f(p: *mut u32, q: *mut u32) {}".to_owned());
            // The file's fixture rule: a witness needing two DISTINCT nodes
            // supplies its own ids, because `parse_crate` leaves every node at
            // `DUMMY_NODE_ID`.
            let (item_id, pat_a, pat_b) = {
                let item = &mut krate.items[0];
                item.id = rustc_ast::node_id::NodeId::from_u32(910);
                let rustc_ast::ItemKind::Fn(f) = &mut item.kind else { panic!("fixture is a fn") };
                f.sig.decl.inputs[0].pat.id = rustc_ast::node_id::NodeId::from_u32(911);
                f.sig.decl.inputs[0].ty.id = rustc_ast::node_id::NodeId::from_u32(912);
                f.sig.decl.inputs[1].pat.id = rustc_ast::node_id::NodeId::from_u32(913);
                f.sig.decl.inputs[1].ty.id = rustc_ast::node_id::NodeId::from_u32(914);
                (
                    item.id,
                    f.sig.decl.inputs[0].pat.id,
                    f.sig.decl.inputs[1].pat.id,
                )
            };
            assert_ne!(pat_a, pat_b, "the fixture must supply DISTINCT ids");
            let mut local_map = rustc_ast::node_id::NodeMap::default();
            // BOTH bindings resolve to ONE `HirId` — subject `A`, declined
            // twice. This is the compensating half the scalar cannot see.
            local_map.insert(pat_a, rustc_hir::CRATE_HIR_ID);
            local_map.insert(pat_b, rustc_hir::CRATE_HIR_ID);
            let mut global_map = rustc_ast::node_id::NodeMap::default();
            global_map.insert(item_id, rustc_hir::def_id::CRATE_DEF_ID);
            let a = (rustc_hir::def_id::CRATE_DEF_ID, rustc_hir::CRATE_HIR_ID);
            let mut decisions = FxHashMap::default();
            decisions.insert(a, (DeclForm::Ref, true));
            let subject_hirs: FxHashSet<HirId> = FxHashSet::default();
            let reverted: FxHashSet<LocalDefId> =
                [rustc_hir::def_id::CRATE_DEF_ID].into_iter().collect();
            let mut guard = Composition::default();
            let mut v = RefDeclVisitor {
                local_map: &local_map,
                decisions: &decisions,
                global_map: &global_map,
                reverted_fns: &reverted,
                subject_hirs: &subject_hirs,
                current_fn: None,
                guard: &mut guard,
                stats: RefDeclStats::default(),
            };
            v.visit_crate(&mut krate);
            let stats = v.stats;

            let distinct: FxHashSet<(LocalDefId, HirId)> =
                stats.withheld_ids.iter().copied().collect();
            assert_eq!(
                (
                    stats.reverted_withheld,
                    stats.withheld_ids.len(),
                    distinct.len()
                ),
                (2, 2, 1),
                "TWO declines under ONE identity: the scalar reads 2 and the SET \
                 reads 1, which is the whole gap this item closes"
            );

            // ---- the reconciliation half: `B` was owed and never reached ----
            //
            // `B` is a second reverted subject in the same function. The scalar
            // 2 matches the two oracle lines exactly, so nothing count-based
            // can tell this apart from full coverage.
            let b = (
                rustc_hir::def_id::CRATE_DEF_ID,
                rustc_hir::HirId {
                    owner: rustc_hir::CRATE_HIR_ID.owner,
                    local_id: rustc_hir::hir_id::ItemLocalId::from_u32(7),
                },
            );
            assert_ne!(a, b, "the two owed subjects must be distinct identities");
            let reverted_ids: FxHashSet<(LocalDefId, HirId)> = [a, b].into_iter().collect();
            let r = reconcile_identities(&reverted_ids, &distinct, &FxHashSet::default(), |k| {
                format!("{k:?}")
            });
            assert_eq!(
                (r.missing, r.surplus),
                (1, 0),
                "`B` is MISSING — reached by nothing, owed by the revert set — \
                 while the scalar 2 == 2 says the coverage is complete"
            );
            assert!(
                r.examples.iter().any(|e| e.starts_with("MISSING:")),
                "and the row must NAME it: {:?}",
                r.examples
            );

            // The positive half, so a reconciliation that reported MISSING for
            // everything would fail here rather than pass as vigilance.
            let only_a: FxHashSet<(LocalDefId, HirId)> = [a].into_iter().collect();
            let ok = reconcile_identities(&only_a, &distinct, &FxHashSet::default(), |k| {
                format!("{k:?}")
            });
            assert_eq!(
                (ok.missing, ok.surplus),
                (0, 0),
                "full coverage must reconcile CLEAN"
            );
        });
    }

    /// **THE F2 REPAIR, WITNESSED — a reverted subject is DECLINED, and the
    /// decline is a check that can fail.**
    ///
    /// The first repair's `reverted_placed` was empty *by construction*:
    /// `decisions` was pre-filtered, so no input could put a reverted subject
    /// in front of the walk and the counter's zero meant nothing. The filter
    /// now lives at the transform site, so this fixture can do what no input
    /// could do before — hand the walk a decided subject whose owner is
    /// reverted — and observe that it is withheld.
    ///
    /// **This is the test the acceptance criterion asks for**: delete the
    /// `reverted_fns.contains` branch and `placed_ids` gains the reverted
    /// subject, which is `reverted_placed` firing at the gate.
    ///
    /// *Mutation-tested (M9):* removing that branch makes `rewritten` 1 and
    /// `reverted_withheld` 0, failing both assertions.
    #[test]
    fn a_reverted_subject_is_declined_at_the_site() {
        rustc_span::create_default_session_globals_then(|| {
            let mut krate = ::utils::ast::parse_crate("fn f(p: *mut u32) {}".to_owned());
            let (item_id, pat_id) = {
                let item = &krate.items[0];
                let rustc_ast::ItemKind::Fn(f) = &item.kind else { panic!("fixture is a fn") };
                (item.id, f.sig.decl.inputs[0].pat.id)
            };
            let mut local_map = rustc_ast::node_id::NodeMap::default();
            local_map.insert(pat_id, rustc_hir::CRATE_HIR_ID);
            let mut global_map = rustc_ast::node_id::NodeMap::default();
            global_map.insert(item_id, rustc_hir::def_id::CRATE_DEF_ID);
            // A genuine `*mut u32` with a real decision, so nothing but the
            // revert check can stop it — the shape check would otherwise take
            // the credit and the test would pass for the wrong reason.
            let mut decisions = FxHashMap::default();
            decisions.insert(
                (rustc_hir::def_id::CRATE_DEF_ID, rustc_hir::CRATE_HIR_ID),
                (DeclForm::Ref, true),
            );
            let subject_hirs: FxHashSet<HirId> = FxHashSet::default();

            // ---- the control: NOT reverted, so it must be placed ----
            let no_reverts: FxHashSet<LocalDefId> = FxHashSet::default();
            let mut guard = Composition::default();
            let mut v = RefDeclVisitor {
                local_map: &local_map,
                decisions: &decisions,
                global_map: &global_map,
                reverted_fns: &no_reverts,
                subject_hirs: &subject_hirs,
                current_fn: None,
                guard: &mut guard,
                stats: RefDeclStats::default(),
            };
            v.visit_crate(&mut krate);
            assert_eq!(
                (v.stats.rewritten, v.stats.reverted_withheld),
                (1, 0),
                "the same subject with an empty revert set MUST be placed — \
                 without this half, a check that declined EVERYTHING would pass"
            );

            // ---- the injection: owner reverted, everything else identical ----
            let mut krate2 = ::utils::ast::parse_crate("fn f(p: *mut u32) {}".to_owned());
            let reverted: FxHashSet<LocalDefId> =
                [rustc_hir::def_id::CRATE_DEF_ID].into_iter().collect();
            let mut guard2 = Composition::default();
            let mut v2 = RefDeclVisitor {
                local_map: &local_map,
                decisions: &decisions,
                global_map: &global_map,
                reverted_fns: &reverted,
                subject_hirs: &subject_hirs,
                current_fn: None,
                guard: &mut guard2,
                stats: RefDeclStats::default(),
            };
            v2.visit_crate(&mut krate2);
            assert_eq!(
                v2.stats.reverted_withheld, 1,
                "a decided subject whose owner is REVERTED must be declined at \
                 the site and counted"
            );
            assert_eq!(
                v2.stats.rewritten, 0,
                "and must not be transformed — this is phase 4's whole property"
            );
            assert!(
                v2.stats.placed_ids.is_empty(),
                "and must place NO identity: a non-empty `placed_ids` here is \
                 exactly what `reverted_placed` reports at the gate"
            );
        });
    }

    /// **The orphan counter counts SUBJECTS, not every declaration it cannot
    /// key.**
    ///
    /// The negative half, and the reason the hir-only index exists at all: an
    /// ordinary pointer param of an `impl` method that is NOT a subject must
    /// leave the counter alone. Without this the counter would read the whole
    /// `impl` population and its zero would mean nothing.
    #[test]
    fn a_non_subject_in_an_impl_does_not_read_as_an_orphan() {
        rustc_span::create_default_session_globals_then(|| {
            let mut krate =
                ::utils::ast::parse_crate("struct S; impl S { fn m(p: *mut u32) {} }".to_owned());
            let pat_id = {
                let rustc_ast::ItemKind::Impl(im) = &krate.items[1].kind else {
                    panic!("fixture's second item is an impl")
                };
                let rustc_ast::AssocItemKind::Fn(f) = &im.items[0].kind else {
                    panic!("fixture's impl holds one fn")
                };
                f.sig.decl.inputs[0].pat.id
            };
            let mut local_map = rustc_ast::node_id::NodeMap::default();
            local_map.insert(pat_id, rustc_hir::CRATE_HIR_ID);
            let global_map = rustc_ast::node_id::NodeMap::default();
            // No decisions at all — the same walk over a population of zero.
            let decisions = FxHashMap::default();
            let subject_hirs: FxHashSet<HirId> = FxHashSet::default();

            // No revert set in these fixtures: the site check is a no-op, so
            // each test isolates the behaviour it names.
            let no_reverts: FxHashSet<LocalDefId> = FxHashSet::default();
            let mut guard = Composition::default();
            let mut v = RefDeclVisitor {
                local_map: &local_map,
                decisions: &decisions,
                global_map: &global_map,
                reverted_fns: &no_reverts,
                subject_hirs: &subject_hirs,
                current_fn: None,
                guard: &mut guard,
                stats: RefDeclStats::default(),
            };
            v.visit_crate(&mut krate);
            assert_eq!(
                v.stats.orphan_subject, 0,
                "a non-subject declaration must NOT read as a lost subject"
            );
        });
    }

    /// **IDENTITY-SET RECONCILIATION — every class, and the counterweight.**
    ///
    /// Pure and generic on purpose, so its failure modes are exercisable
    /// without a corpus sweep. `(u32, u32)` stands in for `(fn_did, hir_id)`:
    /// the function never inspects the identity, only its equality.
    #[test]
    fn reconciliation_names_every_class() {
        let set = |xs: &[(u32, u32)]| -> FxHashSet<(u32, u32)> { xs.iter().copied().collect() };
        let label = |k: &(u32, u32)| format!("f{}::p{}", k.0, k.1);

        // The conforming shape: placed exactly the survivors.
        let r = reconcile_identities(
            &set(&[(1, 1), (1, 2)]),
            &set(&[(1, 1), (1, 2)]),
            &set(&[(2, 1)]),
            label,
        );
        assert_eq!((r.missing, r.surplus, r.reverted_placed), (0, 0, 0));
        assert!(r.examples.is_empty(), "a clean reconciliation has no rows");

        // **THE SAME-CARDINALITY IDENTITY ERROR** — the exact shape the
        // count-based ledger could not see: two placed, two owed, wrong two.
        let r = reconcile_identities(
            &set(&[(1, 1), (1, 2)]),
            &set(&[(1, 1), (1, 3)]),
            &set(&[]),
            label,
        );
        assert_eq!(
            (r.missing, r.surplus),
            (1, 1),
            "counts agree at 2 == 2 and the SETS do not — this is what \
             `p4_placed == emitted` was blind to"
        );
        assert!(
            r.examples.iter().any(|e| e == "MISSING:f1::p2")
                && r.examples.iter().any(|e| e == "SURPLUS:f1::p3"),
            "and each side must be NAMED: {:?}",
            r.examples
        );

        // A reverted subtree transformed anyway — phase 4's own property.
        let r = reconcile_identities(
            &set(&[(1, 1)]),
            &set(&[(1, 1), (2, 1)]),
            &set(&[(2, 1)]),
            label,
        );
        assert_eq!(
            (r.reverted_placed, r.surplus),
            (1, 1),
            "a reverted subject that was placed is BOTH surplus and the named \
             violation — a sub-class, and it says so"
        );

        // **THE COUNTERWEIGHT.** "Deleting all three AST visitors would leave
        // the GAP check passing unchanged." An empty `placed` is that mutation.
        let r = reconcile_identities(&set(&[(1, 1), (1, 2), (1, 3)]), &set(&[]), &set(&[]), label);
        assert_eq!(
            r.missing, 3,
            "with no walk at all EVERY survivor is missing — the check that \
             makes the counterweight false"
        );

        // Rows are sorted, because a set's iteration order is not an artifact's
        // business and a flapping example column is not evidence.
        let r = reconcile_identities(&set(&[(1, 3), (1, 1), (1, 2)]), &set(&[]), &set(&[]), label);
        let mut sorted = r.examples.clone();
        sorted.sort();
        assert_eq!(r.examples, sorted, "example rows must be deterministic");
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
            assert!(guard.claim(node, rustc_span::DUMMY_SP, "decl:slice"));

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

    /// **THE SEAM THE WALK NEVER REACHED — F1's counter, witnessed.**
    ///
    /// The gate discarded these stats entirely (`let _ = s.finish();`), and the
    /// concrete false pass was a seam rejected by *both* the span locator and
    /// the AST walker: it touches no caller function, appears in neither
    /// compared population, and leaves parity green while a converted callee
    /// keeps an unadapted call site — the `E0308` the seam machinery exists to
    /// remove.
    ///
    /// This is the producer half of that repair; the gate half is
    /// `a_seam_dropped_by_both_layers_cannot_vanish`. Both are needed: a counter
    /// nothing reads, and a gate over a counter that cannot move, are the same
    /// failure wearing two hats.
    ///
    /// The span is a real coordinate that no node in this crate occupies —
    /// deliberately not `DUMMY_SP`, which the walk skips by design, so the
    /// witness tests *not reached* rather than *not eligible*.
    ///
    /// *Mutation-tested (M8):* replacing `finish`'s subtraction-over-identities
    /// with `unmatched = 0` fails this test.
    #[test]
    fn a_seam_no_node_matches_is_counted_unmatched() {
        rustc_span::create_default_session_globals_then(|| {
            let src = "fn f(s: *mut S) { g((*s).ptr) }";
            let krate = ::utils::ast::parse_crate(src.to_owned());
            let arg = call_arg_span(&krate);
            // One byte narrower than any real node's range.
            let phantom = arg.with_hi(rustc_span::BytePos(arg.hi().0 - 1));
            assert!(!phantom.is_dummy(), "the miss must be a real coordinate");

            let (_, stats) = seam_over(
                src,
                &[(
                    phantom,
                    phantom,
                    GlueSpec::core(GlueCore::Reborrow, true),
                    false,
                )],
            );
            assert_eq!(
                stats.grafted, 0,
                "nothing may be placed for a target no node carries"
            );
            assert_eq!(
                stats.unmatched, 1,
                "a seam the walk never reached MUST be counted — this is the \
                 only place a seam dropped by both layers is visible at all"
            );

            // ...and the same visitor over a REAL target reads zero, or the
            // counter would be firing on something other than the miss.
            let (_, ok) = seam_over(
                src,
                &[(arg, arg, GlueSpec::core(GlueCore::Reborrow, true), false)],
            );
            assert_eq!(ok.unmatched, 0, "a reached target is not unmatched");
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
            J::SeamAdapter {
                family: "safe",
                fabricated: false,
            },
            // The fabricated adapter is a SUBSET of `seam_adapter`, so it must
            // increment BOTH — a fabricated placement that stopped counting as
            // a seam would shrink the placed population while the crate still
            // carried the adapter.
            J::SeamAdapter {
                family: "reborrow",
                fabricated: true,
            },
            J::FabricatedLenConst,
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
                seam_adapter: 2,
                seam_adapter_fabricated: 1,
                fabricated_len_const: 1,
                reroute: 1,
                drop_form: 1,
                store_form: 1,
            },
            "each variant must land in its OWN bucket — an arm-4 edit counted \
             as a `KindDecision` would report the market as zero while the \
             population was not"
        );
        assert_eq!(
            c.total(),
            8,
            "the denominator is the sum of the parts — and `fabricated` is a \
             SUBSET flag, not a bucket, so it must not appear in it"
        );

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
                edit(J::SeamAdapter {
                    family: "safe",
                    fabricated: false,
                }),
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
                seam_adapter_fabricated: 0,
                fabricated_len_const: 0,
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
            let licensed = SeamLen::Licensed("n".to_owned());
            let len = finish_len(
                &licensed,
                graft_expr(licensed.text()).expect("the length parses"),
            );
            let built = expr(
                glue_expr(GlueShape::FromRawParts, true, P(arg), Some(len))
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

            // ---- THE FABRICATED ARM (ruling 2026-08-12) ----
            //
            // A fabricated extent is text that **never existed in the input**,
            // so it is the purest case of the aliasing hazard this witness
            // exists for: its spans come from a fresh `ParseSess` whose
            // `BytePos` values start at zero. Witnessed here rather than
            // assumed to inherit the licensed arm's protection — the licensed
            // companion at least corresponds to real source, and it was exactly
            // that kind of "surely it's the same" reasoning that let the parsed
            // `usize` through until the adversarial review.
            let arg2 = ::utils::ast::parse_expr("(*s).ptr".to_owned());
            let kept2: FxHashSet<rustc_span::Span> = spans_of(&arg2).exprs.into_iter().collect();
            let fab = finish_len(
                &SeamLen::Fabricated,
                graft_expr(SeamLen::Fabricated.text()).expect("the const path parses"),
            );
            let built2 = expr(
                glue_expr(GlueShape::FromRawParts, false, P(arg2), Some(fab))
                    .expect("the fabricated shape builds"),
            );
            let got2 = spans_of(&built2);
            let leaked2: Vec<_> = got2
                .exprs
                .iter()
                .filter(|s| !s.is_dummy() && !kept2.contains(s))
                .collect();
            assert!(
                leaked2.is_empty(),
                "the fabricated extent's own nodes must carry DUMMY_SP: {leaked2:?}"
            );
            // And it manufactures NO type — the structural difference from the
            // licensed arm, asserted rather than left to the rendered string.
            assert!(
                got2.tys.is_empty(),
                "a fabricated extent is already `usize` and builds no cast: {:?}",
                got2.tys
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
                guard.claim(node_id, rustc_span::DUMMY_SP, "arm4"),
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
    fn rendered(shape: GlueShape, mutable: bool, len: Option<SeamLen>) -> String {
        let arg = ::utils::ast::parse_expr("(*s).ptr".to_owned());
        // **Through the production helper, not around it.** `finish_len` is what
        // the visitor calls; a harness that applied the cast itself would be a
        // second implementation of the rule under test, and would have gone on
        // passing after the fabricated arm made the rule conditional.
        let len = len.map(|sl| finish_len(&sl, ::utils::ast::parse_expr(sl.text().to_owned())));
        let kind =
            glue_expr(shape, mutable, rustc_ast::ptr::P(arg), len).expect("the shapes all build");
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
            let licensed = || Some(SeamLen::Licensed("n".to_owned()));
            assert_eq!(
                rendered(GlueShape::FromRawParts, true, licensed()),
                "core::slice::from_raw_parts_mut((*s).ptr, (n) as usize)"
            );
            assert_eq!(
                rendered(GlueShape::FromRawParts, false, licensed()),
                "core::slice::from_raw_parts((*s).ptr, (n) as usize)"
            );
            // **The SIXTH realized shape** (ruling 2026-08-12): the fabricated
            // extent, whose text differs from the licensed arm in exactly the
            // two ways the audit depends on — a NAMED const, and no cast.
            //
            // The differential's whole job is that a corpus parity diff is
            // attributable to the decision layer rather than the renderer; the
            // fabricated arm without a row here would be the one placement
            // shape the AST layer renders unwitnessed.
            assert_eq!(
                rendered(GlueShape::FromRawParts, true, Some(SeamLen::Fabricated)),
                "core::slice::from_raw_parts_mut((*s).ptr, crate::SEAM_LEN_PLACEHOLDER)"
            );
            assert_eq!(
                rendered(GlueShape::FromRawParts, false, Some(SeamLen::Fabricated)),
                "core::slice::from_raw_parts((*s).ptr, crate::SEAM_LEN_PLACEHOLDER)"
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
