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
//! - a callee parameter decided anything but `Slice` or a thin `Ref` (an
//!   `Opt`, `Box`, `Cursor` or `Degraded` formal has no image of a slice here);
//! - a MUTABLE formal from a SHARED caller (`&[T]` → `&mut [T]` / `&mut T`):
//!   refused, and the decline row says so (`use_shape =
//!   pass-on-refused:shared-into-mut`).
//!
//! **W6S-13b (R531-5(a)) — a thin `Ref` formal.** The slice hands on its first
//! element. The call-site seam already renders exactly that for a `Slice`
//! caller at a `Ref` formal (`seam.rs`'s `(Ref, Slice)` glue, `&s[0]` /
//! `&mut s[0]`, bounds-checked), so the rule adds no argument edit of its own.
//!
//! **The chain round (R531-5(b)).** Every lift arm reads a pre-pass view, so a
//! callee lifted by the same pass is invisible to its caller. [`close`] runs the
//! three arms again until a round lifts nothing: monotone (a lifted row is never
//! a candidate again and the set of receiving formals only grows), bounded by
//! the held rows, and measured cycle-free (068).

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
        .all(|&(callee, index)| formal(entries, callee, index, caller_mutable) == Receive::Yes)
        .then(|| uses.pass_on.clone())
}

/// Would `node` be a pass-on but for mutability — every refused use a pass-on
/// into a formal that has an image of the slice, and at least one of those
/// formals MUTABLE under a SHARED caller?
pub(crate) fn refused_by_mutability(
    ctx: &Ctx<'_, '_>,
    entries: &[(Subject, Decision)],
    node: (LocalDefId, HirId),
) -> bool {
    let Some(uses) = ctx.slice_uses.get(&node) else {
        return false;
    };
    if uses.unsupported.is_none() || uses.other_unsupported != 0 || uses.pass_on.is_empty() {
        return false;
    }
    let Some((caller, _)) = entries
        .iter()
        .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)
    else {
        return false;
    };
    let answers = uses
        .pass_on
        .iter()
        .map(|&(callee, index)| formal(entries, callee, index, caller.mutable))
        .collect::<Vec<_>>();
    answers.iter().all(|answer| *answer != Receive::No) && answers.contains(&Receive::Mutability)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Receive {
    Yes,
    /// The formal has an image of the slice, but writes through it and the
    /// caller is shared.
    Mutability,
    No,
}

/// The callee parameter at `index`, asked whether it receives the caller's
/// slice.
fn formal(
    entries: &[(Subject, Decision)],
    callee: LocalDefId,
    index: usize,
    caller_mutable: bool,
) -> Receive {
    entries
        .iter()
        .find(|(subject, _)| {
            subject.fn_did == callee
                && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == index)
        })
        .map_or(Receive::No, |(_, decision)| {
            receives(decision, caller_mutable)
        })
}

/// Can this callee-parameter decision receive the caller's slice?
///
/// Exhaustive for the reason `licensed_lift::delivers_slice` is: a new
/// disposition must be answered here, not admitted by a wildcard.
fn receives(decision: &Decision, caller_mutable: bool) -> Receive {
    let permitted = |mutable: bool| {
        if !mutable || caller_mutable {
            Receive::Yes
        } else {
            Receive::Mutability
        }
    };
    match decision {
        Decision::Slice { mutable, .. } => permitted(*mutable),
        // W6S-13b: a thin formal takes the first element (the seam's glue).
        Decision::Ref { mutable } | Decision::InferredRef { mutable, .. } => permitted(*mutable),
        Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => Receive::No,
    }
}

/// **The chain round (R531-5(b)).** Re-run the three lift arms until a round
/// lifts nothing, keeping every lift and dropping a refusal row whose subject a
/// later round lifted. A later round's refusals for rows still held repeat the
/// first round's and are discarded.
pub(crate) fn close(
    ctx: &Ctx<'_, '_>,
    entries: &mut [(Subject, Decision)],
    lifts: &mut Vec<super::licensed_lift::LiftReceipt>,
    roots: &mut Vec<super::root_extent::RootExtentRow>,
) {
    let held = |entries: &[(Subject, Decision)]| {
        entries
            .iter()
            .filter(|(_, decision)| {
                super::licensed_lift::held_at_a_local_callee(decision).is_some()
            })
            .count()
    };
    for _ in 0..entries.len() {
        // Only a held row some pass-on now reaches can move; otherwise stop.
        let movable = entries.iter().any(|(subject, decision)| {
            super::licensed_lift::held_at_a_local_callee(decision).is_some()
                && supported(ctx, entries, (subject.fn_did, subject.hir_id)).is_some()
        });
        if !movable {
            return;
        }
        let before = held(entries);
        let mut round = super::licensed_lift::promote(ctx, entries);
        let round_roots = super::root_extent::promote(ctx, entries);
        round.extend(super::licensed_lift::promote_fallback(ctx, entries));
        if held(entries) == before {
            return;
        }
        let lifted = round
            .iter()
            .filter(|lift| lift.declined.is_none())
            .map(|lift| lift.subject.clone())
            .chain(
                round_roots
                    .iter()
                    .filter(|row| row.outcome == "lifted")
                    .map(|row| row.subject.clone()),
            )
            .collect::<rustc_hash::FxHashSet<_>>();
        lifts.retain(|lift| lift.declined.is_none() || !lifted.contains(&lift.subject));
        lifts.extend(round.into_iter().filter(|lift| lift.declined.is_none()));
        roots.retain(|row| row.outcome == "lifted" || !lifted.contains(&row.subject));
        roots.extend(
            round_roots
                .into_iter()
                .filter(|row| row.outcome == "lifted"),
        );
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
    for (subject, _) in entries {
        if !refused_by_mutability(ctx, entries, (subject.fn_did, subject.hir_id)) {
            continue;
        }
        for lift in lifts
            .iter_mut()
            .filter(|lift| lift.declined.is_some() && lift.subject == subject.label)
        {
            lift.use_shape = Some("pass-on-refused:shared-into-mut");
        }
    }
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
