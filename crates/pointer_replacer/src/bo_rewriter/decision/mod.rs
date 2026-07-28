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
use rustc_middle::mir::Local;
use rustc_span::Span;

use crate::analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef};

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
    /// Source span of the parameter's declared **type**.
    pub ty_span: Span,
    /// Source span of the pointee type, kept so the plan can preserve the
    /// pointee's text verbatim rather than re-render it.
    pub pointee_span: Span,
    pub mutable: bool,
}

/// What M1 decided for one subject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Decision {
    /// Emit a reference form: `&T` or `&mut T`.
    Ref { mutable: bool },
    /// Not emitted, with the reason recorded. **A first-class outcome.**
    ///
    /// §1.6 admits only conflict-non-increasing rewrites; everything outside
    /// that envelope degrades *here*, with a reason — never silently, and never
    /// by an emitter discovering downstream that it cannot proceed.
    Degraded { reason: &'static str },
}

/// The finished, immutable table handed to [`super::plan`].
#[derive(Clone, Debug, Default)]
pub(crate) struct DecisionTable {
    pub entries: Vec<(Subject, Decision)>,
}

impl DecisionTable {
    /// Structural gate input: every subject has exactly one decision.
    pub(crate) fn is_total_over(&self, subjects: usize) -> bool {
        self.entries.len() == subjects
    }

    /// S2 aggregates these into the envelope-demotion counters.
    pub(crate) fn degraded(&self) -> impl Iterator<Item = (&Subject, &'static str)> {
        self.entries.iter().filter_map(|(s, d)| match d {
            Decision::Degraded { reason } => Some((s, *reason)),
            Decision::Ref { .. } => None,
        })
    }
}

/// Build the decision table from BO's accepted model.
///
/// The accepted model is the **only** BO input S1 consumes. `BoExport`
/// (E-R2..E-R4) is opened by the driver but deliberately not read here: G01
/// needs no move point, no loan identity and no certificate, and consuming
/// facts the arm does not use would make this phase's dependencies a lie.
pub(crate) fn decide(
    subjects: Vec<Subject>,
    model: &FxHashMap<SlotRef, SlotKind>,
    slots: &CrateSlots,
) -> DecisionTable {
    let entries = subjects
        .into_iter()
        .map(|subject| {
            let decision = decide_one(&subject, model, slots);
            (subject, decision)
        })
        .collect();
    DecisionTable { entries }
}

fn decide_one(
    subject: &Subject,
    model: &FxHashMap<SlotRef, SlotKind>,
    slots: &CrateSlots,
) -> Decision {
    let Some(universe) = slots.fn_local_slots.get(&subject.fn_did) else {
        return Decision::Degraded {
            reason: "function has no slot universe",
        };
    };
    let Some(slot_id) = universe.slot_for_local_depth(subject.local, 0) else {
        return Decision::Degraded {
            reason: "parameter has no depth-0 slot",
        };
    };
    match model.get(&SlotRef::Local(subject.fn_did, slot_id)) {
        Some(SlotKind::Ref) => Decision::Ref {
            mutable: subject.mutable,
        },
        // A1 emitability, S1 scope: the reference form and nothing else. `Raw`
        // is a decision to leave the source alone; `Owning` needs the Box forms
        // and the drop policy, which arrive in S3.
        Some(SlotKind::Raw) => Decision::Degraded {
            reason: "BO kind Raw — no rewrite at M1",
        },
        Some(SlotKind::Owning) => Decision::Degraded {
            reason: "BO kind Owning — Box forms arrive in S3",
        },
        None => Decision::Degraded {
            reason: "slot absent from the accepted model",
        },
    }
}
