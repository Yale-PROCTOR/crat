//! **Producer A.** The rewriter's own decision table, serialized as rows.
//!
//! This is `bo_rewriter`'s only addition for S2a-H: it *emits* an artifact and
//! compares nothing. The comparison lives in [`crate::coverage_recon`], outside
//! this module, because four rounds of evidence say a gate written beside the
//! collector it checks encodes the collector's blind spots.
//!
//! # Not a pipeline phase, but regulated like one
//!
//! `decision → plan → apply → verify` is the pipeline; this is a consumer of
//! the finished table sitting *beside* it, not a stage within it. It is
//! nevertheless a directory with its own `PhaseRule`, because the alternative
//! was a special case in the denylist machinery — and an unregulated corner of
//! `bo_rewriter` is precisely what the mechanized rules exist to prevent. One
//! mechanism covering everything beats two mechanisms with a gap between them.
//!
//! # Totality is the point
//!
//! [`rows`] matches [`Decision`] **exhaustively, with no `_` arm**. That is the
//! mechanization of the ruling that the outcome enumeration be total over
//! subject dispositions: a kept-`Raw` subject emits a row exactly as an emitted
//! `Ref` does, so *covered-but-unchanged* stays distinguishable from *dropped*
//! — which is row-absence, and is what a producer-B-only row detects.
//!
//! When S3 adds a `Box` disposition to `Decision`, this match **fails to
//! compile** rather than silently mapping the new variant onto a default. That
//! is the difference between a rule and a wish.

use rustc_middle::ty::TyCtxt;

use super::decision::{DeclShape, Decision, DecisionTable, emitability::EmitabilityFacts};
use crate::coverage_recon::schema::{
    DeclShape as WireShape, Outcome, PairingConfidence, Row,
};

fn wire_shape(shape: DeclShape) -> WireShape {
    // Exhaustive by construction: no `_` arm here either.
    match shape {
        DeclShape::RawPtr => WireShape::RawPtr,
        DeclShape::Alias => WireShape::Alias,
        DeclShape::Reference => WireShape::Reference,
        DeclShape::Other => WireShape::Other,
    }
}

/// Serialize the decision table as producer-A rows.
#[allow(
    dead_code,
    reason = "no non-test consumer until the rewriter is wired into \
              the pipeline. EXPIRY-CORRECTED 2026-07-30: this reason used to \
              say 'consumers land at C.1/C.4'. Both landed and the allow is \
              still required, because both consumers are `cfg(test)` — a dated \
              promise that came due and did not settle. Targeted on the entry \
              point rather than module-wide: allowing an item makes it a live \
              root, so the lint stays active over everything reachable from it."
)]
pub(crate) fn rows(tcx: TyCtxt<'_>, table: &DecisionTable) -> Vec<Row> {
    let source_map = tcx.sess.source_map();
    table
        .entries
        .iter()
        .map(|(subject, decision)| {
            // EXHAUSTIVE. Adding a `Decision` variant must break this build.
            let (outcome, degrade_reason) = match decision {
                Decision::Ref { mutable } => (
                    if *mutable {
                        Outcome::RefMut
                    } else {
                        Outcome::RefShared
                    },
                    None,
                ),
                Decision::Degraded(record) => {
                    (Outcome::Degraded, Some(record.reason.key().to_owned()))
                }
            };
            Row {
                fn_path: tcx.def_path_str(subject.fn_did.to_def_id()),
                mir_local: subject.local.as_u32(),
                param_name: subject.param_name.clone(),
                // 1-based on the wire, matching `VarDebugInfo::argument_index`
                // and MIR's parameter locals. Derived from the HIR position the
                // collector recorded, NOT from `mir_local`.
                arg_index: Some(subject.hir_index as u32 + 1),
                ptr_depth: subject.ptr_depth,
                // Producer A's own doubt, which is narrower than producer B's:
                // A knows only whether the pattern gave it a name.
                pairing_confidence: if subject.param_name.is_some() {
                    PairingConfidence::High
                } else {
                    PairingConfidence::Low
                },
                decl_span: Some(EmitabilityFacts::site(tcx, subject.ty_span)),
                // Through the SAME `lookup_byte_offset` the plan splices with,
                // so the audited number IS the edit target rather than a
                // parallel derivation that could drift from it.
                decl_span_lo: Some(source_map.lookup_byte_offset(subject.ty_span.lo()).pos.0),
                decl_span_hi: Some(source_map.lookup_byte_offset(subject.ty_span.hi()).pos.0),
                binding_span_lo: None,
                binding_span_hi: None,
                decl_shape: Some(wire_shape(subject.decl_shape)),
                outcome: Some(outcome),
                degrade_reason,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use rustc_middle::mir::Local;

    use super::*;
    use crate::bo_rewriter::decision::{DegradeReason, Degradation, Subject};

    fn subject(local: u32, name: Option<&str>) -> Subject {
        Subject {
            fn_did: rustc_hir::def_id::CRATE_DEF_ID,
            local: Local::from_u32(local),
            hir_id: rustc_hir::CRATE_HIR_ID,
            param_name: name.map(str::to_owned),
            hir_index: local as usize - 1,
            ptr_depth: 1,
            label: format!("f::{}", name.unwrap_or("<pattern>")),
            ty_span: rustc_span::DUMMY_SP,
            pointee_span: Some(rustc_span::DUMMY_SP),
            decl_shape: DeclShape::RawPtr,
            mutable: true,
        }
    }

    fn table(entries: Vec<(Subject, Decision)>) -> DecisionTable {
        DecisionTable { entries }
    }

    /// **A.10 — a kept-`Raw` subject EMITS A ROW.**
    ///
    /// This is the totality requirement, and it is about row *presence*. If a
    /// subject BO declined to convert produced no row, then
    /// *covered-but-unchanged* and *dropped* would both be an absent row, and
    /// producer B could not tell them apart — the same conflation A1 exists to
    /// retire, reintroduced at the artifact layer.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* adding a
    /// `.filter(|(_, d)| matches!(d, Decision::Ref { .. }))` before the `map`
    /// in [`rows`] — i.e. emitting only converted subjects — fails this.
    #[test]
    fn a_kept_raw_subject_emits_a_distinguishable_row() {
        ::utils::compilation::run_compiler_on_str("pub fn nothing() {}", |tcx| {
            let t = table(vec![
                (
                    subject(1, Some("kept")),
                    Decision::Degraded(Degradation {
                        subject: "f::kept".to_owned(),
                        site: "<main.rs>:1:1".to_owned(),
                        reason: DegradeReason::KindRaw,
                    }),
                ),
                (subject(2, Some("conv")), Decision::Ref { mutable: true }),
            ]);
            let emitted = rows(tcx, &t);
            assert_eq!(emitted.len(), 2, "a kept-Raw subject must emit a row");

            let kept = &emitted[0];
            assert_eq!(kept.outcome, Some(Outcome::Degraded));
            assert_eq!(
                kept.degrade_reason.as_deref(),
                Some("kind-raw"),
                "the row must say WHY it was unchanged, or it is \
                 indistinguishable from any other degradation"
            );
            assert_eq!(emitted[1].outcome, Some(Outcome::RefMut));
        })
        .expect("fixture compiles");
    }

    /// `arg_index` is derived from the HIR position, **not** from `mir_local`.
    ///
    /// A pairing term that restates the alignment key can never disagree with
    /// it, which is what F1 looked like. This pins the two apart: the subject
    /// below has `hir_index = 0` and `local = _7`, so a `mir_local`-derived
    /// `arg_index` would read 7 rather than 1.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* replacing
    /// `subject.hir_index as u32 + 1` with `subject.local.as_u32()` fails this.
    #[test]
    fn arg_index_comes_from_the_hir_position_not_the_mir_local() {
        ::utils::compilation::run_compiler_on_str("pub fn nothing() {}", |tcx| {
            let mut s = subject(7, Some("p"));
            s.hir_index = 0;
            let emitted = rows(tcx, &table(vec![(s, Decision::Ref { mutable: false })]));
            assert_eq!(emitted[0].mir_local, 7);
            assert_eq!(
                emitted[0].arg_index,
                Some(1),
                "arg_index restated the alignment key instead of recording the \
                 HIR position"
            );
        })
        .expect("fixture compiles");
    }

    /// An unnamed parameter is `null` + low confidence, never a placeholder.
    ///
    /// A `"<pattern>"` placeholder would compare EQUAL between two different
    /// pattern parameters — a pairing term that silently agrees is F1 in
    /// miniature.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* deleting the
    /// `if subject.param_name.is_some()` branch (pinning confidence to `High`)
    /// fails this.
    #[test]
    fn an_unnamed_parameter_is_null_and_low_confidence() {
        ::utils::compilation::run_compiler_on_str("pub fn nothing() {}", |tcx| {
            let emitted = rows(
                tcx,
                &table(vec![(subject(1, None), Decision::Ref { mutable: false })]),
            );
            assert_eq!(emitted[0].param_name, None);
            assert_eq!(emitted[0].pairing_confidence, PairingConfidence::Low);
        })
        .expect("fixture compiles");
    }
}
