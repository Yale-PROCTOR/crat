//! **Phase 1 — decision.** Analysis in, decision table out. No AST mutation.
//!
//! Everything that reads BO output or an auxiliary analysis happens here and
//! nowhere else. The table this phase produces is **immutable and complete
//! before any edit is planned**: A1 emitability, A2 degradation closure, and
//! the owning-reachable fixpoint all live here, so no later phase ever has to
//! ask an analysis a question.
//!
//! # E1 state visibility
//!
//! This phase may read `crate::analyses::*` (read-only, §2 precedence rule) and
//! the `BoExport`. It hands [`super::plan`] a finished table by value. It holds
//! no back-pointer to a later phase, and no later phase holds one to it.
//!
//! # Status
//!
//! S1 lands the **G01 arm only**: depth-0 pointer *parameters* whose BO kind is
//! `Ref`. Every other subject degrades with a named reason — the channel S2's
//! envelope-demotion counters aggregate. A2's degradation closure and the
//! owning-reachable fixpoint arrive with S2's breadth.

use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::Span;

use crate::analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef};

pub(crate) mod emitability;
pub(crate) mod universe;

use emitability::EmitabilityFacts;

/// How the parameter's **declaration** is written in source, for a subject
/// whose **resolved** type is a pointer.
///
/// The two can disagree, and that disagreement is the whole reason subject
/// collection moved to resolved types: a C2Rust alias
/// (`pub type lil_value_t = *mut _lil_value_t`) is a pointer parameter that
/// *reads* as a path. Under R-A such parameters are collected — they are real C
/// pointer parameters and excluding them would shrink the universe artificially
/// — and the shape is carried so that an emission obstacle specific to the
/// shape can be attributed with its own reason instead of vanishing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DeclShape {
    /// `*mut T` / `*const T`, written literally. The only emittable shape at M1.
    RawPtr,
    /// A path that resolves to a pointer — the C2Rust type-alias class.
    Alias,
    /// Already a reference in source.
    Reference,
    /// Resolved as a pointer through some other declaration form.
    Other,
}

impl DeclShape {
    fn key(self) -> &'static str {
        match self {
            DeclShape::RawPtr => "raw-ptr",
            DeclShape::Alias => "alias",
            DeclShape::Reference => "reference",
            DeclShape::Other => "other",
        }
    }
}

/// One thing M1 must decide about. **Depth-0 pointer parameters only at S1.**
///
/// Subjects and decisions are counted against each other by the structural gate
/// (`|decisions| == |subjects|`), so a subject that is silently skipped rather
/// than explicitly degraded fails the gate instead of vanishing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Subject {
    pub fn_did: LocalDefId,
    /// MIR local of the parameter: params are `_1 ..= arg_count`.
    pub local: Local,
    /// HIR binding of the same parameter, used to attribute uses to it without
    /// relying on a name that could be shadowed.
    pub hir_id: rustc_hir::HirId,
    /// **Pairing term 1** in the reconciliation artifact: the parameter's
    /// source name. `None` when the pattern is not a plain binding.
    pub param_name: Option<String>,
    /// **Pairing term 2**: the parameter's position in the HIR declaration,
    /// **0-based**, recorded as collected.
    ///
    /// Kept separately from [`Self::local`] deliberately. The two coincide
    /// today (`local == hir_index + 1`), but deriving the artifact's
    /// `arg_index` *from* the local would make it a restatement of the
    /// alignment key — and a pairing field that restates the key can never
    /// disagree with it. F1 is precisely what such a field looks like.
    pub hir_index: usize,
    /// Pointer-chain depth of the RESOLVED parameter type.
    pub ptr_depth: u8,
    /// Human-readable identity for attribution: `fn_name::param_name`.
    pub label: String,
    /// Source span of the parameter's declared **type**.
    pub ty_span: Span,
    /// Source span of the pointee type, kept so the plan can preserve the
    /// pointee's text verbatim rather than re-render it.
    ///
    /// `None` when the declaration is not a syntactic raw pointer: an alias
    /// carries its pointer-ness inside the alias, so there is no pointee text
    /// to copy. Such subjects are degraded in [`decide_one`], so a `Ref`
    /// decision always has a pointee span.
    pub pointee_span: Option<Span>,
    /// How the declaration is written — see [`DeclShape`].
    pub decl_shape: DeclShape,
    pub mutable: bool,
}

/// Why a subject was not emitted.
///
/// A typed reason rather than a string: the counters S2b aggregates need to
/// group by cause, and `CallSiteNotAdapted` in particular is **temporary** —
/// S3's call-site adaptation retires it, and a free-text reason would make that
/// transition invisible in the data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DegradeReason {
    /// BO decided the slot is a raw pointer; leaving the source alone is the
    /// decision, not a failure.
    KindRaw,
    /// BO decided owning; Box forms and the drop policy arrive in S3.
    KindOwning,
    /// The parameter is used in an operation that exists only on raw pointers.
    RawPointerOperation { op: String },
    /// The function is referenced in-crate — called, address-taken, or cast to
    /// a fn pointer — and use sites are not yet adapted. **Retired by S3.**
    CallSiteNotAdapted,
    /// The parameter is compared with `<`, `==`, … (F5).
    ///
    /// Blocking in both directions. The dangerous one is silent: the same
    /// expression compares ADDRESSES on raw pointers and POINTEES on
    /// references, so a rewritten bounds check type-checks, passes the gate,
    /// and inverts. Refusing here is the only place that catches it before a
    /// behavioral gate exists.
    PtrComparison,
    /// Structural: the subject has no depth-0 slot, or none in the model.
    NoSlot,
    /// The resolved parameter type is a pointer but the **declaration** is not
    /// a syntactic `*mut`/`*const` — the C2Rust alias class, or a parameter
    /// that is already a reference.
    ///
    /// R-A: collect these, do not exclude them. They are real C pointer
    /// parameters, so excluding them would shrink the universe artificially;
    /// what they get instead is a decision and an attributed reason. Emitting
    /// *through* an alias is a separate design question — the alias already
    /// contains the `*mut`, so `&mut lil_value_t` would be wrong — and
    /// conflating it with the collection fix would repeat this milestone's
    /// pattern of bundling.
    NonPointerDecl { shape: &'static str },
}

impl DegradeReason {
    /// Stable key for counter aggregation (S2b).
    #[allow(
        dead_code,
        reason = "the aggregation that consumes this is S2b, the next slice. \
                  Targeted rather than module-wide so the lint keeps working \
                  everywhere else."
    )]
    pub(crate) fn key(&self) -> &'static str {
        match self {
            DegradeReason::KindRaw => "kind-raw",
            DegradeReason::KindOwning => "kind-owning",
            DegradeReason::RawPointerOperation { .. } => "raw-pointer-operation",
            DegradeReason::CallSiteNotAdapted => "call-site-not-adapted",
            DegradeReason::PtrComparison => "ptr-comparison",
            DegradeReason::NoSlot => "no-slot",
            DegradeReason::NonPointerDecl { .. } => "non-pointer-decl",
        }
    }
}

/// A degradation, **attributed**: subject, site and reason.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Degradation {
    pub subject: String,
    pub site: String,
    pub reason: DegradeReason,
}

/// What M1 decided for one subject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Decision {
    /// Emit a reference form: `&T` or `&mut T`.
    Ref { mutable: bool },
    /// Not emitted, with the reason ATTRIBUTED. **A first-class outcome.**
    ///
    /// §1.6 admits only conflict-non-increasing rewrites; everything outside
    /// that envelope degrades *here*, with a subject and a site — never
    /// silently, and never by an emitter discovering downstream that it cannot
    /// proceed and reporting it as a property of the whole crate.
    Degraded(Degradation),
}

/// The finished, immutable table handed to [`super::plan`].
#[derive(Clone, Debug, Default)]
pub(crate) struct DecisionTable {
    pub entries: Vec<(Subject, Decision)>,
}

impl DecisionTable {
    /// Structural self-consistency: the table covers exactly the subjects it
    /// was given, once each.
    ///
    /// **This is not the coverage gate**, and the distinction is the lesson of
    /// three failed rounds. Every check here compares the table against the
    /// collector's own output, so none of them can detect a subject the
    /// collector never produced. They catch two real but narrower defects: a
    /// **duplicate subject** (which would otherwise plan two edits for one span
    /// and surface only as an `apply` overlap rollback) and a **dropped
    /// decision**.
    ///
    /// Detecting a subject that was never collected requires an instrument with
    /// a different derivation — see [`coverage::reconcile`], which owns that
    /// job and is the only thing in this module entitled to be called a
    /// coverage gate.
    pub(crate) fn is_self_consistent_over(&self, subjects: &[Subject]) -> Result<(), String> {
        let mut seen = rustc_hash::FxHashSet::default();
        for (subject, _) in &self.entries {
            let key = (subject.fn_did.local_def_index.as_u32(), subject.local);
            if !seen.insert(key) {
                return Err(format!("duplicate decision for subject {}", subject.label));
            }
        }
        for subject in subjects {
            if !seen.contains(&(subject.fn_did.local_def_index.as_u32(), subject.local)) {
                return Err(format!("no decision for subject {}", subject.label));
            }
        }
        if self.entries.len() != subjects.len() {
            return Err(format!(
                "table has {} entries for {} subjects",
                self.entries.len(),
                subjects.len()
            ));
        }
        Ok(())
    }

    /// The envelope-demotion records. S2b aggregates these into the counters.
    ///
    /// C.2: coverage gaps no longer live here. A parameter no subject was
    /// built for is now detected by the harness reconciliation as a
    /// producer-B-only row, which is a property of the ARTIFACTS rather than of
    /// this table — and S2b's coverage-class counters consume those artifacts.
    pub(crate) fn degradations(&self) -> impl Iterator<Item = &Degradation> {
        self.entries.iter().filter_map(|(_, d)| match d {
            Decision::Degraded(record) => Some(record),
            Decision::Ref { .. } => None,
        })
    }

    /// Subjects the table decided to emit.
    pub(crate) fn emitted_count(&self) -> usize {
        self.entries
            .iter()
            .filter(|(_, d)| matches!(d, Decision::Ref { .. }))
            .count()
    }
}

/// Build the decision table from BO's accepted model **and the A1 facts**.
///
/// The accepted model is the only BO input S1/S2a consume. `BoExport`
/// (E-R2..E-R4) is opened by the driver but deliberately not read here: the
/// reference arm needs no move point, no loan identity and no certificate, and
/// consuming facts the arm does not use would make this phase's dependencies a
/// lie.
pub(crate) fn decide(
    tcx: TyCtxt<'_>,
    subjects: &[Subject],
    model: &FxHashMap<SlotRef, SlotKind>,
    slots: &CrateSlots,
    facts: &EmitabilityFacts,
) -> DecisionTable {
    let entries = subjects
        .iter()
        .map(|subject| {
            let decision = decide_one(tcx, subject, model, slots, facts);
            (subject.clone(), decision)
        })
        .collect();
    DecisionTable { entries }
}

fn degrade(subject: &Subject, site: String, reason: DegradeReason) -> Decision {
    Decision::Degraded(Degradation {
        subject: subject.label.clone(),
        site,
        reason,
    })
}

fn decide_one(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    model: &FxHashMap<SlotRef, SlotKind>,
    slots: &CrateSlots,
    facts: &EmitabilityFacts,
) -> Decision {
    let decl_site = EmitabilityFacts::site(tcx, subject.ty_span);

    // The declaration's SHAPE comes FIRST, before any analysis is consulted.
    //
    // R-A collects alias-typed parameters so they are decided rather than
    // dropped; this is where that collection turns into an attributed reason.
    // It is checked ahead of BO's kind because it is knowable without any
    // analysis at all — the plan copies the pointee's source text and an alias
    // has none to copy, whatever BO concluded. Ordering it first also keeps the
    // witness for this class independent of the solver's verdict, which is the
    // §5.3 rule: test the layer you name, not a composition that routes through
    // it.
    //
    // The cost, stated: an alias-typed parameter's BO kind does not reach the
    // counters. That is S2b's question to reopen with a reason if it wants the
    // "how many alias params would have been Ref" breakdown.
    if subject.decl_shape != DeclShape::RawPtr {
        return degrade(
            subject,
            decl_site,
            DegradeReason::NonPointerDecl {
                shape: subject.decl_shape.key(),
            },
        );
    }

    let Some(universe) = slots.fn_local_slots.get(&subject.fn_did) else {
        return degrade(subject, decl_site, DegradeReason::NoSlot);
    };
    let Some(slot_id) = universe.slot_for_local_depth(subject.local, 0) else {
        return degrade(subject, decl_site, DegradeReason::NoSlot);
    };

    // BO's kind first: it is the authority on WHETHER a reference is sound.
    match model.get(&SlotRef::Local(subject.fn_did, slot_id)) {
        Some(SlotKind::Ref) => {}
        Some(SlotKind::Raw) => return degrade(subject, decl_site, DegradeReason::KindRaw),
        Some(SlotKind::Owning) => return degrade(subject, decl_site, DegradeReason::KindOwning),
        None => return degrade(subject, decl_site, DegradeReason::NoSlot),
    }

    // A1 emitability: BO says a reference is SOUND; these say whether one can
    // actually be EMITTED. Both are decision-phase questions, which is the
    // whole point — S1 let them fall through to an anonymous gate failure.
    if let Some((op, span)) = facts.raw_only_uses.get(&(subject.fn_did, subject.hir_id)) {
        return degrade(
            subject,
            EmitabilityFacts::site(tcx, *span),
            DegradeReason::RawPointerOperation { op: op.clone() },
        );
    }
    if let Some(span) = facts.ptr_comparisons.get(&(subject.fn_did, subject.hir_id)) {
        return degrade(
            subject,
            EmitabilityFacts::site(tcx, *span),
            DegradeReason::PtrComparison,
        );
    }
    if let Some(spans) = facts.referenced.get(&subject.fn_did)
        && let Some(span) = spans.first()
    {
        return degrade(
            subject,
            EmitabilityFacts::site(tcx, *span),
            DegradeReason::CallSiteNotAdapted,
        );
    }

    Decision::Ref {
        mutable: subject.mutable,
    }
}

#[cfg(test)]
mod self_consistency_tests {
    //! Witnesses for [`DecisionTable::is_self_consistent_over`] — and for what
    //! it deliberately does **not** do.
    //!
    //! The dropped-subject arm that used to live here has moved to
    //! [`super::coverage`], where it belongs: detecting a subject the collector
    //! never produced needs an instrument with a different derivation, and this
    //! check has none — every comparison in it is against the collector's own
    //! output. Keeping a "coverage" test next to a self-comparison is how three
    //! rounds of unfailable gates read as covered.

    use super::*;

    fn subject(local: u32, label: &str) -> Subject {
        Subject {
            fn_did: rustc_hir::def_id::CRATE_DEF_ID,
            local: Local::from_u32(local),
            hir_id: rustc_hir::CRATE_HIR_ID,
            param_name: Some(label.rsplit("::").next().unwrap_or(label).to_owned()),
            hir_index: local as usize - 1,
            ptr_depth: 1,
            label: label.to_owned(),
            ty_span: rustc_span::DUMMY_SP,
            pointee_span: Some(rustc_span::DUMMY_SP),
            decl_shape: DeclShape::RawPtr,
            mutable: true,
        }
    }

    fn table(entries: Vec<Subject>) -> DecisionTable {
        DecisionTable {
            entries: entries
                .into_iter()
                .map(|s| (s, Decision::Ref { mutable: true }))
                .collect(),
        }
    }

    /// A table that covers its subjects, once each, is self-consistent.
    ///
    /// **Positive control, and no deletion mutation fails it** — recorded
    /// rather than dressed up. A test asserting that a checker *accepts* valid
    /// input cannot be broken by deleting one of that checker's rejection arms;
    /// only making the function unconditionally reject would fail it. Its job is
    /// to prove the three negatives below are not passing because
    /// `is_self_consistent_over` errors on everything.
    #[test]
    fn matching_entries_are_self_consistent() {
        let subjects = vec![subject(1, "f::a"), subject(2, "f::b")];
        assert!(
            table(subjects.clone())
                .is_self_consistent_over(&subjects)
                .is_ok()
        );
    }

    /// A duplicate subject is caught before it can plan two edits for one span
    /// — which `apply` would otherwise surface only as an overlap rollback.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* deleting the `seen.insert`
    /// arm makes this pass.
    #[test]
    fn a_duplicate_subject_is_rejected() {
        let subjects = vec![subject(1, "f::a")];
        let dup = table(vec![subject(1, "f::a"), subject(1, "f::a")]);
        let err = dup
            .is_self_consistent_over(&subjects)
            .expect_err("a duplicate decision must be rejected");
        assert!(err.contains("duplicate"), "wrong failure arm: {err}");
    }

    /// A subject with no decision is caught.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* deleting the
    /// `for subject in subjects` arm makes this pass — the length check alone
    /// does not catch it, because the perturbation changes membership without
    /// changing the count.
    #[test]
    fn a_subject_with_no_decision_is_rejected() {
        let subjects = vec![subject(1, "f::a"), subject(2, "f::b")];
        // Same cardinality, different membership: `f::b` has no decision and
        // `f::c` has one for a subject that was never handed in.
        let skewed = table(vec![subject(1, "f::a"), subject(3, "f::c")]);
        let err = skewed
            .is_self_consistent_over(&subjects)
            .expect_err("a subject with no decision must be rejected");
        assert!(err.contains("no decision for"), "wrong failure arm: {err}");
    }

}
