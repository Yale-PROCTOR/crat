//! R419-3 / R304-2: a pending sibling-overlap site is a STATED HOLD, read at
//! decision time.
//!
//! The sibling-overlap instrument (`sibling_overlap.rs`) marks a T1 foreign
//! site `t1-sibling-overlap:pending` when its SOURCE is delivered as a borrowed
//! form while another argument of the same call — a sibling — may alias it and
//! writes (`risky_sibling`: an A5 verdict that is not `Clear`, and a contract
//! access `Write` / `Lifecycle` or an unmodeled position). The custody
//! comparator then protects the source binding's declaration. A family that
//! delivers such a source has delivered a held subject (main 039 §2, §5); it
//! consults this inventory BEFORE deciding and refuses with the typed reason.
//!
//! This is the instrument's premise read from the call facts alone, without
//! the verdict term: at decision time a caller LOCAL that is a literal or a
//! null-initialized binding has no frozen-graph array a proof could separate
//! from its sibling, so its verdict is never `Clear`. The read is therefore
//! exactly `risky_sibling` for the population it is consulted for, and
//! conservative for any other.

use rustc_hash::FxHashSet;
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;

use super::{
    Subject, SubjectKind,
    emitability::EmitabilityFacts,
    outbound_expression::OutboundExpressionPlans,
    raw_boundary::RawBoundaryDispositionIndex,
    raw_boundary_contracts::{PointeeAccess, classify_contract},
    seam::Form,
    sibling_overlap,
};

/// Is this sibling argument the address of a place rooted in a binding of the
/// CALLER's own frame (`&mut statBuf`), rather than a pointer value or a borrow
/// through a dereference (`&mut (*p).field`)?
///
/// Such storage did not exist when the frame began, so nothing the frame
/// RECEIVED — a parameter's referent, a string literal's static — can point
/// into it: under the UB-free-input scope the two cannot alias, which is the
/// separation the A5 proof reports as `Clear` and the sibling-overlap
/// instrument reads before holding a site pending. Measured at the batch-9
/// re-census: without this term the three bzip2 `lstat` / `stat` rows
/// (`countHardLinks::name#1`, `notAStandardFile::name#1`,
/// `saveInputFileMetaInfo::srcName#1`) lost the deliveries R407-14 gave them.
fn addresses_a_frame_binding(fact: &super::raw_boundary::ForeignCallArgFact) -> bool {
    matches!(fact.shape, "addr-of" | "addr-of-mut")
        && !fact.root_through_deref
        && fact.root.is_some()
}

/// The first foreign site at which `node` is the source and a sibling argument
/// is risky: `(callee path, node's argument index, the sibling's index)`.
///
/// `frame_external_referent` states that the subject's referent lives outside
/// the caller's frame (a parameter's referent, a string literal's static) — the
/// premise [`addresses_a_frame_binding`] needs.
pub(crate) fn pending_site(
    facts: &EmitabilityFacts,
    node: (LocalDefId, HirId),
    frame_external_referent: bool,
) -> Option<(String, usize, usize)> {
    facts
        .foreign_call_args
        .iter()
        .filter(|fact| fact.caller == node.0 && fact.direct_subject_root() == Some(node.1))
        .find_map(|fact| {
            facts
                .foreign_call_args
                .iter()
                .filter(|sibling| {
                    sibling.caller == fact.caller
                        && sibling.call_span == fact.call_span
                        && sibling.argument_index != fact.argument_index
                })
                .find(|sibling| {
                    if frame_external_referent && addresses_a_frame_binding(sibling) {
                        return false;
                    }
                    match classify_contract(
                        &sibling.callee,
                        sibling.argument_index,
                        &sibling.target,
                    ) {
                        Ok(contract) => matches!(
                            contract.access,
                            PointeeAccess::Write | PointeeAccess::Lifecycle
                        ),
                        Err(_) => true,
                    }
                })
                .map(|sibling| {
                    (
                        fact.callee.path.clone(),
                        fact.argument_index,
                        sibling.argument_index,
                    )
                })
        })
}

/// **Relay 018 §1.** The null-init-family locals whose boundary site would be
/// a PENDING sibling-overlap row once delivered — the same predicate the
/// terminal receipt applies (`select_pending`: a borrowed source at a RAW
/// target, a risky sibling, the local not dead-unprotected after the call),
/// asked before the final decision pass with the optional form as the source
/// and the boundary index's open T1/T2 site as "the target is raw". Computed
/// once, carried on the index the final pass already consults.
pub(crate) fn pending_sibling_sources(
    tcx: TyCtxt<'_>,
    inputs: &sibling_overlap::SiblingInputs<'_>,
    raw_boundary: &RawBoundaryDispositionIndex,
) -> FxHashSet<(LocalDefId, HirId)> {
    let mut out = FxHashSet::default();
    // Nothing to consult where the family has no candidate: the inventory walks
    // every boundary site's MIR body, so it is not derived for its own sake.
    if !inputs.subjects.iter().any(|subject| {
        subject.ty_span.is_none() && matches!(subject.kind, SubjectKind::Local) && subject.null_init
    }) {
        return out;
    }
    let potentials =
        sibling_overlap::collect_inventory_from(tcx, inputs, &OutboundExpressionPlans::default())
            .potentials;
    for potential in &potentials {
        let Some(source) = potential.source.declared() else { continue };
        if source.ty_span.is_some()
            || !matches!(source.kind, SubjectKind::Local)
            || !source.null_init
        {
            continue;
        }
        let raw_target = raw_boundary.tracks_call_argument(
            potential.caller,
            &potential.site.callee.path,
            potential.argument_span,
            potential.site.argument_index,
        );
        let state = sibling_overlap::TerminalSiteState {
            // The predicate asks only whether the source is a borrowed form.
            source_form: Form::Opt {
                mutable: true,
                slice: false,
            },
            target_form: if raw_target {
                Form::Raw
            } else {
                Form::Ref { mutable: false }
            },
            source_delivered: true,
        };
        if !sibling_overlap::select_pending(std::slice::from_ref(potential), |_| state).is_empty() {
            out.insert((source.fn_did, source.hir_id));
        }
    }
    out
}
