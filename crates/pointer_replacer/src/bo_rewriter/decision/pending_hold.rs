//! **R829-1 / R855-1 (USER; main 184) — the caller-side hold of the pending
//! sibling-overlap sites, decided on the settled table.**
//!
//! The temporary pair waiver of 2026-09-08 ended (R829-1): a source delivered as a
//! borrowed form and handed to a raw formal beside a risky raw sibling the pair
//! proof did not show disjoint keeps its raw form. The round driver could not hold
//! a formal after planning (main 182b: its callers stay planned for the delivered
//! form), so the hold is read here, on the table the ladder settled, before
//! anything is planned from it: a held source is DECIDED raw, and the seams then
//! plan every call into it with the ordinary bridge.
//!
//! The predicate is `sibling_overlap::select_pending`, the one the terminal
//! receipts ask (with the frame-binding premise in both places, R857-1), with
//! its `TerminalSiteState` read from the table: the source's
//! decided form and delivery, and the callee formal's decided form (a foreign
//! callee's formal is raw where the raw boundary tracks the argument, as
//! `pending_sibling::pending_sibling_sources` reads it).

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{
    Decision, DecisionTable, DegradeReason, SubjectKind,
    raw_boundary::{RawBoundaryDispositionIndex, site_atom_id},
    seam::{self, Form},
    sibling_overlap::{self, SourceBridgeCoverage, SourceBridgeEvidence, TerminalSiteState},
};

/// The switch `CRAT_RAW_BOUNDARY_PENDING_HOLD`, read strictly: unset or `on` holds,
/// `off` keeps the ended waiver (the price census reads both), anything else is a
/// mistake, never "on".
pub(crate) fn parse(value: Option<&str>) -> Result<bool, String> {
    match value {
        None | Some("on") => Ok(true),
        Some("off") => Ok(false),
        Some(other) => Err(format!(
            "CRAT_RAW_BOUNDARY_PENDING_HOLD must be `on` or `off`, got `{other}`"
        )),
    }
}

/// The switch, from the environment.
pub(crate) fn enabled() -> bool {
    let value = std::env::var("CRAT_RAW_BOUNDARY_PENDING_HOLD").ok();
    parse(value.as_deref()).unwrap_or_else(|why| panic!("{why}"))
}

/// The sources the pending sites name on this table, each with the hold's reason.
/// Only the coverage rows the terminal receipts read (the plan's filter on the
/// source's bridge evidence), so the hold names exactly the sites the pending table
/// would: an address-of local sibling's row (`BindingStorage`, a raw field value)
/// is not a pending site there and is not held here.
pub(crate) fn holds(
    table: &DecisionTable,
    coverage: &[SourceBridgeCoverage],
    raw_boundary: &RawBoundaryDispositionIndex,
) -> FxHashMap<(LocalDefId, HirId), DegradeReason> {
    let by_node: FxHashMap<(LocalDefId, HirId), &Decision> = table
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect();
    let by_formal: FxHashMap<(LocalDefId, usize), &Decision> = table
        .entries
        .iter()
        .filter_map(|(subject, decision)| match subject.kind {
            SubjectKind::Param { hir_index } => Some(((subject.fn_did, hir_index), decision)),
            _ => None,
        })
        .collect();
    let mut out = FxHashMap::default();
    for row in coverage.iter().filter(|row| {
        matches!(
            row.evidence,
            SourceBridgeEvidence::WholeSubject
                | SourceBridgeEvidence::ProjectedReferent { .. }
                | SourceBridgeEvidence::TypedView { .. }
                | SourceBridgeEvidence::NativeReturnExpression { .. }
        )
    }) {
        let potential = &row.potential;
        let Some(source) = potential.source.declared() else {
            continue;
        };
        let node = (source.fn_did, source.hir_id);
        let Some(decision) = by_node.get(&node) else {
            continue;
        };
        let target_form = match potential.callee.as_local() {
            Some(callee) => by_formal
                .get(&(callee, potential.site.argument_index))
                .map_or(Form::Raw, |decision| seam::form_of(decision)),
            None => {
                if raw_boundary.tracks_call_argument(
                    potential.caller,
                    &potential.site.callee.path,
                    potential.argument_span,
                    potential.site.argument_index,
                ) {
                    Form::Raw
                } else {
                    Form::Ref { mutable: false }
                }
            }
        };
        // Exhaustive by rule (`import_denylist`): a new disposition is classified
        // here, never dropped by a bypass shape.
        let source_delivered = match decision {
            Decision::Degraded(_) => false,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Opt { .. }
            | Decision::Box(_) => true,
        };
        let state = TerminalSiteState {
            source_form: seam::form_of(decision),
            target_form,
            source_delivered,
        };
        for receipt in sibling_overlap::select_pending(std::slice::from_ref(potential), |_| state) {
            out.entry(node)
                .or_insert_with(|| DegradeReason::PairNotShownDisjoint {
                    detail: format!(
                        "pair-not-shown-disjoint:{};risky-siblings={}",
                        site_atom_id(&potential.site),
                        receipt
                            .risky_siblings
                            .iter()
                            .map(|sibling| format!("arg{}", sibling.argument_index))
                            .collect::<Vec<_>>()
                            .join(",")
                    ),
                });
        }
    }
    out
}
