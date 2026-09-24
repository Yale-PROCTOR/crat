//! **W6S-13 (R526-4 / R528-4) — the pass-on rule.**
//!
//! [`super::licensed_lift`] lifts a caller held at a local callee to the slice
//! form, and refuses first when the caller has a use with no slice image
//! (`slice-use-unsupported`). At batch 28 that refusal is 79 of the waiver's
//! declines, and 277 of the 300 refused occurrences behind it are a BARE
//! argument at a local callee (wave-6s 068). The collector cannot answer those
//! uses: it runs before any decision exists, and where the owner's SliceUse
//! family is withdrawn (brotli's `StitchToPreviousBlockH2`,
//! `new-family-dependency`) it reads the before-family walk, in which a
//! local-callee argument has no image at all.
//!
//! At promote time the answer exists. A refused use that is an argument at a
//! callee parameter which DELIVERS the slice form in this plan has an image:
//! the caller's slice, handed on. Both ends are safe slices, so no raw pointer
//! crosses the call and the retention/permission holds — which are about raw
//! bridges — are not in play; the pass is the borrow checker's to check. The
//! caller's own extent is the lift's (a licensed width, a root, or the §77
//! fallback, receipted by the lift as before): this rule supplies no extent.
//!
//! What it does NOT admit:
//! - a caller with any refused use that is not such an argument;
//! - a callee parameter decided anything but `Slice` (a thin `Ref` would be a
//!   one-element claim; `Degraded` has no safe form to receive a slice);
//! - a MUTABLE callee slice from a SHARED caller (`&[T]` → `&mut [T]`);
//! - a callee parameter lifted in the same pass (the fixpoint's two rows are
//!   named in 068 and left for a second round).

use rustc_hir::{HirId, def_id::LocalDefId};

use super::{Ctx, Decision, Subject, SubjectKind};

/// One admitted pass-on pair, for the receipt: the caller subject, and the
/// callee parameter it hands its slice to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Receipt {
    pub(crate) caller: String,
    pub(crate) callee: String,
    pub(crate) parameter_index: usize,
}

/// Does every refused use of `node` hand the slice on to a callee parameter
/// that delivers the slice form in `entries`? The pairs when it does.
pub(crate) fn supported(
    ctx: &Ctx<'_, '_>,
    entries: &[(Subject, Decision)],
    node: (LocalDefId, HirId),
) -> Option<Vec<(LocalDefId, usize)>> {
    let uses = ctx.slice_uses.get(&node)?;
    if uses.unsupported.is_none() || uses.other_unsupported != 0 || uses.pass_on.is_empty() {
        return None;
    }
    let caller_mutable = entries
        .iter()
        .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)?
        .0
        .mutable;
    uses.pass_on
        .iter()
        .all(|&(callee, index)| {
            entries.iter().any(|(subject, decision)| {
                subject.fn_did == callee
                    && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == index)
                    && receives(decision, caller_mutable)
            })
        })
        .then(|| uses.pass_on.clone())
}

/// Can this callee-parameter decision receive the caller's slice?
///
/// Exhaustive for the reason `licensed_lift::delivers_slice` is: a new
/// disposition must be answered here, not admitted by a wildcard.
fn receives(decision: &Decision, caller_mutable: bool) -> bool {
    match decision {
        Decision::Slice { mutable, .. } => !*mutable || caller_mutable,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => false,
    }
}

/// The receipts, one per `(caller, callee parameter)` pair, for the lifts this
/// rule admitted: a subject the lift took to `Slice` whose refused uses were
/// all pass-on. Marks those lifts' `use_shape` as `pass-on` so the census row
/// says which door the subject came through.
pub(crate) fn receipts(
    ctx: &Ctx<'_, '_>,
    entries: &[(Subject, Decision)],
    lifts: &mut [super::licensed_lift::LiftReceipt],
) -> Vec<Receipt> {
    let mut out = Vec::new();
    for (subject, decision) in entries {
        if !super::licensed_lift::delivers_slice(decision) {
            continue;
        }
        let Some(pairs) = supported(ctx, entries, (subject.fn_did, subject.hir_id)) else {
            continue;
        };
        let mut lifted = false;
        for lift in lifts
            .iter_mut()
            .filter(|lift| lift.declined.is_none() && lift.subject == subject.label)
        {
            lift.use_shape = Some("pass-on");
            lifted = true;
        }
        if !lifted {
            continue;
        }
        let mut pairs = pairs
            .into_iter()
            .map(|(callee, parameter_index)| {
                (ctx.tcx.def_path_str(callee.to_def_id()), parameter_index)
            })
            .collect::<Vec<_>>();
        pairs.sort();
        pairs.dedup();
        out.extend(pairs.into_iter().map(|(callee, parameter_index)| Receipt {
            caller: subject.label.clone(),
            callee,
            parameter_index,
        }));
    }
    out
}
