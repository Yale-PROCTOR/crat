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

use emitability::EmitabilityFacts;

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
    /// Human-readable identity for attribution: `fn_name::param_name`.
    pub label: String,
    /// Source span of the parameter's declared **type**.
    pub ty_span: Span,
    /// Source span of the pointee type, kept so the plan can preserve the
    /// pointee's text verbatim rather than re-render it.
    pub pointee_span: Span,
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
}

impl DegradeReason {
    /// Stable key for counter aggregation (S2b).
    pub(crate) fn key(&self) -> &'static str {
        match self {
            DegradeReason::KindRaw => "kind-raw",
            DegradeReason::KindOwning => "kind-owning",
            DegradeReason::RawPointerOperation { .. } => "raw-pointer-operation",
            DegradeReason::CallSiteNotAdapted => "call-site-not-adapted",
            DegradeReason::PtrComparison => "ptr-comparison",
            DegradeReason::NoSlot => "no-slot",
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
    /// Structural gate: the table covers exactly the subjects it was given,
    /// once each, **and as many subjects as the crate independently has**.
    ///
    /// The previous form compared `entries.len()` against a count captured from
    /// the same `Vec` one line earlier, over a total `map` with no filter — it
    /// could not fail in any execution. This checks the two properties that
    /// *can*: **no duplicate subject** (a collector emitting one parameter
    /// twice would otherwise plan two edits for one span, which `apply` would
    /// only catch as an overlap rollback), and **every input subject present**.
    pub(crate) fn coverage_over(
        &self,
        subjects: &[Subject],
        independent_ptr_params: usize,
    ) -> Result<(), String> {
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
        // F3: the load-bearing comparison. The three checks above compare the
        // table against the collector's OWN OUTPUT, which is unfailable by
        // construction — `decide` is a total map over `subjects` and the same
        // slice is passed here. A coverage gate that compares a pipeline
        // against itself cannot fail; it needs an outside reference.
        //
        // `independent_ptr_params` is counted in a separate walk that does not
        // consult `collect_subjects`, so a subject dropped anywhere in the
        // collector — including the `body.params.get(index)` path, which used
        // to drop it from BOTH sides at once and stay invisible — shows up
        // here as a mismatch.
        if self.entries.len() != independent_ptr_params {
            return Err(format!(
                "table covers {} subjects but the crate has {independent_ptr_params} \
                 pointer parameters — {} were dropped before a decision was made",
                self.entries.len(),
                independent_ptr_params.saturating_sub(self.entries.len())
            ));
        }
        Ok(())
    }

    /// The envelope-demotion records. S2b aggregates these into the counters.
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
mod coverage_tests {
    use super::*;

    fn subject(local: u32, label: &str) -> Subject {
        Subject {
            fn_did: rustc_hir::def_id::CRATE_DEF_ID,
            local: Local::from_u32(local),
            hir_id: rustc_hir::CRATE_HIR_ID,
            label: label.to_owned(),
            ty_span: rustc_span::DUMMY_SP,
            pointee_span: rustc_span::DUMMY_SP,
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

    /// The gate accepts a table that covers its subjects and matches the
    /// independent count.
    #[test]
    fn matching_coverage_is_ok() {
        let subjects = vec![subject(1, "f::a"), subject(2, "f::b")];
        assert!(table(subjects.clone()).coverage_over(&subjects, 2).is_ok());
    }

    /// **F3's load-bearing arm.** A subject dropped by the collector shrinks
    /// BOTH the table and the slice it is compared against, so only the
    /// independent count can see it.
    ///
    /// This is the arm the previous `is_total_over` — and its first replacement
    /// — could not have: both compared the pipeline against its own output.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* removing the
    /// `entries.len() != independent_ptr_params` arm makes this pass.
    #[test]
    fn a_dropped_subject_is_caught_only_by_the_independent_count() {
        let subjects = vec![subject(1, "f::a")];
        // Table and slice agree with each other; the CRATE has two pointer
        // params. Every self-referential check passes; this must not.
        let err = table(subjects.clone())
            .coverage_over(&subjects, 2)
            .expect_err("a dropped subject must fail the coverage gate");
        assert!(
            err.contains("dropped before a decision"),
            "wrong failure arm: {err}"
        );
    }

    /// A duplicate subject is caught before it can plan two edits for one span.
    #[test]
    fn a_duplicate_subject_is_rejected() {
        let subjects = vec![subject(1, "f::a")];
        let dup = table(vec![subject(1, "f::a"), subject(1, "f::a")]);
        let err = dup
            .coverage_over(&subjects, 1)
            .expect_err("a duplicate decision must fail the gate");
        assert!(err.contains("duplicate"), "wrong failure arm: {err}");
    }
}
