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

use rustc_ast::{MutTy, Mutability, NodeId, Ty, TyKind, mut_visit::MutVisitor};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::HirId;
use rustc_span::def_id::LocalDefId;

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
#[derive(Default)]
pub(crate) struct Composition {
    claimed: FxHashSet<NodeId>,
    /// Refusals, with the node that was claimed twice.
    pub refused: Vec<NodeId>,
}

impl Composition {
    /// `true` when this transform may proceed. `false` means another transform
    /// already owns the node and **both** are refused — see the struct doc.
    pub(crate) fn claim(&mut self, node: NodeId) -> bool {
        if self.claimed.insert(node) {
            true
        } else {
            self.refused.push(node);
            false
        }
    }
}

/// What arm 1 rewrote, so the differential has a population to compare.
#[derive(Default)]
pub(crate) struct RefDeclStats {
    /// Declarations rewritten `*mut T`/`*const T` → `&mut T`/`&T`.
    pub rewritten: usize,
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
}

/// Arm 1's visitor: rewrite the declared type of every `Decision::Ref` subject.
pub(crate) struct RefDeclVisitor<'a> {
    /// AST `NodeId` → HIR `HirId`, the forward direction a tree walk wants.
    ///
    /// The `UnordMap` is used DIRECTLY rather than copied into an `FxHashMap`:
    /// a lookup is order-free, `get` is all a tree walk needs, and converting
    /// would mean iterating a container that hides iteration on purpose.
    pub local_map: &'a rustc_ast::node_id::NodeMap<HirId>,
    /// `(fn_did, hir_id)` → is this subject `Ref`, and is it mutable?
    pub decisions: &'a FxHashMap<(LocalDefId, HirId), bool>,
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
        let Some(&mutable) = self.decisions.get(&(fn_did, *hir_id)) else {
            return;
        };
        if !self.guard.claim(ty.id) {
            self.stats.refused += 1;
            return;
        }
        // The POINTEE MOVES ACROSS. No text is copied and none is re-rendered:
        // `mut_ty.ty` is the same subtree, reattached under a reference.
        let TyKind::Ptr(mut_ty) = &mut ty.kind else {
            self.stats.not_a_pointer_decl += 1;
            return;
        };
        let pointee = mut_ty.ty.clone();
        ty.kind = TyKind::Ref(
            None,
            MutTy {
                ty: pointee,
                mutbl: if mutable {
                    Mutability::Mut
                } else {
                    Mutability::Not
                },
            },
        );
        self.stats.rewritten += 1;
        self.stats
            .rendered
            .push((ty.span.lo().0, rustc_ast_pretty::pprust::ty_to_string(ty)));
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
    arm1_population_inner(tcx)
}

#[cfg(test)]
fn arm1_population_inner(tcx: rustc_middle::ty::TyCtxt<'_>) -> Result<RefDeclStats, String> {
    let captured = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut krate = ::utils::ast::expanded_ast(tcx);
        let map = ::utils::ast::make_ast_to_hir(&mut krate, tcx);
        (krate, map)
    }));
    let (mut krate, map) = captured.map_err(|_| "AST capture panicked".to_owned())?;

    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    let mut decisions: FxHashMap<(LocalDefId, HirId), bool> = FxHashMap::default();
    for (subject, decision) in &table.entries {
        // EXHAUSTIVE — the denylist rejects the bypass shape, and arm 1's
        // population is defined by which disposition was reached.
        match decision {
            super::decision::Decision::Ref { mutable } => {
                decisions.insert((subject.fn_did, subject.hir_id), *mutable);
            }
            super::decision::Decision::Slice { .. }
            | super::decision::Decision::Opt { .. }
            | super::decision::Decision::Degraded(_) => {}
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
    let mut stats = v.stats;
    stats.refused = guard.refused.len();
    Ok(stats)
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
    pub unmatched_span: usize,
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
pub(crate) fn arm1_full(
    tcx: rustc_middle::ty::TyCtxt<'_>,
) -> Result<(RefDeclStats, TextDiff), String> {
    let stats = arm1_population_inner(tcx)?;
    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default())?;

    // The span layer's declaration edits, keyed by absolute offset. `Edit::lo`
    // is FILE-relative, so the file's own base is added back before joining —
    // the AST side carries absolute `Span` offsets.
    let sm = tcx.sess.source_map();
    let mut by_offset: FxHashMap<u32, String> = FxHashMap::default();
    for (key, edits) in &emission.plan.by_file {
        let base = sm
            .files()
            .iter()
            .find(|sf| super::file_key(&sf.name).as_ref() == Some(key))
            .map(|sf| sf.start_pos.0)
            .unwrap_or(0);
        for e in edits {
            if matches!(
                e.justification,
                super::plan::Justification::KindDecision { .. }
            ) {
                by_offset.insert(base + e.lo as u32, e.replacement.clone());
            }
        }
    }

    let mut d = TextDiff::default();
    for (off, rendered) in &stats.rendered {
        match by_offset.get(off) {
            Some(span_text) => {
                d.compared += 1;
                if span_text == rendered {
                    d.equal += 1;
                } else {
                    d.differing += 1;
                    if d.examples.len() < 10 {
                        d.examples
                            .push(format!("@{off} ast={rendered:?} span={span_text:?}"));
                    }
                }
            }
            None => d.unmatched_ast += 1,
        }
    }
    let ast_offsets: FxHashSet<u32> = stats.rendered.iter().map(|(o, _)| *o).collect();
    d.unmatched_span = by_offset
        .keys()
        .filter(|o| !ast_offsets.contains(o))
        .count();
    Ok((stats, d))
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
#[cfg(test)]
pub(crate) fn graft_expr(text: &str) -> Result<rustc_ast::Expr, String> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ::utils::ast::parse_expr(text.to_owned())
    }))
    .map_err(|_| text.to_owned())
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
