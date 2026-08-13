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
#[derive(Default)]
pub(crate) struct Composition {
    claimed: FxHashSet<NodeId>,
    /// Refusals, with the node that was claimed twice.
    pub refused: Vec<NodeId>,
}

impl Composition {
    /// `true` when this transform may proceed. `false` means another transform
    /// already owns the node, and THIS one is refused — see the struct doc for
    /// why that is not the same as refusing both.
    pub(crate) fn claim(&mut self, node: NodeId) -> bool {
        if self.claimed.insert(node) {
            true
        } else {
            self.refused.push(node);
            false
        }
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
        if !self.guard.claim(ty.id) {
            self.stats.refused += 1;
            return;
        }
        // The POINTEE MOVES ACROSS. No text is copied and none is re-rendered:
        // `mut_ty.ty` is the same subtree, reattached under a reference — and
        // under a `[…]` and an `Option<…>` too, for the forms that need them.
        let TyKind::Ptr(mut_ty) = &mut ty.kind else {
            self.stats.not_a_pointer_decl += 1;
            return;
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
        if let Some(text) = self.uses.get(&key) {
            self.consumed.insert(key);
            if !self.guard.claim(e.id) {
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
        assert!(g.claim(node), "the first claim must be admitted");
        assert!(
            !g.claim(node),
            "the SECOND claim on one node must be refused — this is the \
             structural half of the barrier the site-overlap gate provides, \
             and it does not lapse in parity mode"
        );
        assert_eq!(
            g.refused,
            vec![node],
            "the refusal must be COUNTED, not \
             merely returned: an unreviewed composition that is refused and \
             not recorded is indistinguishable from one that never arose"
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
        assert!(g.claim(NodeId::from_u32(1)));
        assert!(g.claim(NodeId::from_u32(2)));
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
    transform_inner(tcx).map(|(decls, _)| decls)
}

/// Both passes over ONE capture, sharing ONE composition guard.
///
/// # Why two passes and not one visitor
///
/// The use pass must **not** descend into a subtree it has just replaced — the
/// children are the parsed fragment's, and walking them would be walking the
/// wrong tree. A single visitor doing both jobs would therefore skip any
/// *declaration* inside a rewritten expression as well, silently. Two passes
/// keep the skip local to the pass that needs it.
///
/// The guard is shared precisely because the passes are separate: same-node
/// claims must be refused **across** them, not within each.
#[cfg(test)]
fn transform_inner(
    tcx: rustc_middle::ty::TyCtxt<'_>,
) -> Result<(RefDeclStats, UseGraftStats), String> {
    let captured = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut krate = ::utils::ast::expanded_ast(tcx);
        let map = ::utils::ast::make_ast_to_hir(&mut krate, tcx);
        (krate, map)
    }));
    let (mut krate, map) = captured.map_err(|_| "AST capture panicked".to_owned())?;

    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    let mut decisions: FxHashMap<(LocalDefId, HirId), (DeclForm, bool)> = FxHashMap::default();
    let mut uses: FxHashMap<(u32, u32), String> = FxHashMap::default();
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
    let mut decls = v.stats;

    let mut g = UseGraftVisitor::new(&uses, &mut guard);
    g.visit_crate(&mut krate);
    let grafts = g.finish();

    // The guard's total is split between the passes by their own tallies, so a
    // refusal is attributable to the position it arose at rather than to a
    // corpus-level sum.
    decls.refused = guard.refused.len() - grafts.refused;
    Ok((decls, grafts))
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

/// Join one arm's renders against the plan. Returns
/// `(compared, equal, differing, unmatched_ast)`.
#[cfg(test)]
fn compare_renders(
    renders: &[(u32, String)],
    by_offset: &FxHashMap<u32, String>,
    examples: &mut Vec<String>,
) -> (usize, usize, usize, usize) {
    let (mut compared, mut equal, mut differing, mut unmatched) = (0, 0, 0, 0);
    for (off, rendered) in renders {
        match by_offset.get(off) {
            Some(span_text) => {
                compared += 1;
                if span_text == rendered {
                    equal += 1;
                } else {
                    differing += 1;
                    if examples.len() < 10 {
                        examples.push(format!("@{off} ast={rendered:?} span={span_text:?}"));
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
    let (decls, grafts) = transform_inner(tcx)?;
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

    let (c, eq, diff, un) = compare_renders(&decls.rendered, &by_offset, &mut d.examples);
    d.compared = c;
    d.equal = eq;
    d.differing = diff;
    d.unmatched_ast = un;

    // Arm 2 is one population in two syntactic positions — a declaration and
    // its uses travel together or not at all (`plan`'s `use_failure` enforces
    // exactly that on the span side), so splitting them here would report two
    // half-populations neither of which is the thing that has to agree.
    let arm2: Vec<(u32, String)> = decls
        .rendered_arm2
        .iter()
        .chain(grafts.rendered.iter())
        .cloned()
        .collect();
    let (c2, eq2, diff2, un2) = compare_renders(&arm2, &by_offset, &mut d.examples);
    d.arm2_compared = c2;
    d.arm2_equal = eq2;
    d.arm2_differing = diff2;
    d.arm2_unmatched_ast = un2;

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
pub(crate) fn graft_expr(text: &str) -> Result<rustc_ast::Expr, String> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ::utils::ast::parse_expr(text.to_owned())
    }))
    .map_err(|_| text.to_owned())
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
