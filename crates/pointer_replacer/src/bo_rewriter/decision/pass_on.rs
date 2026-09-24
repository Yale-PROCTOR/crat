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

use rustc_hash::FxHashMap;
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
/// that receives it in `entries`? The pairs when it does.
///
/// **`lift_mutable` is the mutability the ASKING arm will give the lifted
/// slice** (R533-4, wave-4 061 C7) — not the subject's: the exact arm lifts
/// `subject.mutable && region.mutable`, the waiver and B1 `subject.mutable`. A
/// lift that will be `&[T]` must not be admitted into a formal that writes.
pub(crate) fn supported(
    ctx: &Ctx<'_, '_>,
    entries: &[(Subject, Decision)],
    node: (LocalDefId, HirId),
    lift_mutable: bool,
) -> Option<Vec<(LocalDefId, usize)>> {
    let uses = ctx.slice_uses.get(&node)?;
    if uses.unsupported.is_none() || uses.other_unsupported != 0 || uses.pass_on.is_empty() {
        return None;
    }
    let caller_mutable = lift_mutable;
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
/// lifts nothing.
///
/// **The receipts (R536-6, wave-4 062 R1/R2).** Every round re-emits a full set
/// of receipts for each row still held when it starts, so the record needs no
/// cross-round matching at all:
///
/// - a lift is kept from the round that made it, with the refusals that same
///   round wrote for that subject before lifting it (the exact arm's, ahead of
///   the waiver or B1);
/// - a row still held keeps **the LAST round's** refusal — the reason that is
///   true at the fixpoint, not the use gate a callee's lift has since cleared
///   (R2);
/// - B1 writes one row per held subject per round, so its held rows are the
///   last round's and its lifted rows every round's.
///
/// Within one round a refusal is paired with its lift by the identity the
/// census row itself carries — subject label, licensing callee path,
/// parameter index. C2Rust's per-module duplicates share a LABEL (R1) but
/// license from their own module's callee, so that identity separates them;
/// where even it collides, the two rows are indistinguishable in the census
/// schema too, and wave-4's `subject_key` (relay 078) makes it exact.
pub(crate) fn close(
    ctx: &Ctx<'_, '_>,
    entries: &mut [(Subject, Decision)],
    lifts: &mut Vec<super::licensed_lift::LiftReceipt>,
    roots: &mut Vec<super::root_extent::RootExtentRow>,
) {
    use super::{
        licensed_lift::{LiftReceipt, held_at_a_local_callee},
        root_extent::RootExtentRow,
    };
    let held_count = |entries: &[(Subject, Decision)]| {
        entries
            .iter()
            .filter(|(_, decision)| held_at_a_local_callee(decision).is_some())
            .count()
    };
    let identity = |lift: &LiftReceipt| {
        (
            lift.subject.clone(),
            lift.callee.clone(),
            lift.parameter_index,
        )
    };
    // Split one round's receipts into what is final now (its lifts, and the
    // refusals it wrote for subjects it lifted) and what only the LAST round
    // may keep (refusals of rows still held).
    let settle = |entries: &[(Subject, Decision)],
                  round: Vec<LiftReceipt>,
                  round_roots: &[RootExtentRow]|
     -> (Vec<LiftReceipt>, Vec<LiftReceipt>) {
        let lifted = round
            .iter()
            .filter(|lift| lift.declined.is_none())
            .map(identity)
            .collect::<rustc_hash::FxHashSet<_>>();
        let still_held = entries
            .iter()
            .filter(|(_, decision)| held_at_a_local_callee(decision).is_some())
            .map(|(subject, _)| subject.label.clone())
            .collect::<rustc_hash::FxHashSet<_>>();
        let lifted_by_b1 = round_roots
            .iter()
            .filter(|row| row.outcome == "lifted" && !still_held.contains(&row.subject))
            .map(|row| row.subject.clone())
            .collect::<rustc_hash::FxHashSet<_>>();
        round.into_iter().partition(|lift| {
            lift.declined.is_none()
                || lifted.contains(&identity(lift))
                || lifted_by_b1.contains(&lift.subject)
        })
    };
    let movable = |entries: &[(Subject, Decision)]| {
        entries.iter().any(|(subject, decision)| {
            held_at_a_local_callee(decision).is_some()
                && supported(
                    ctx,
                    entries,
                    (subject.fn_did, subject.hir_id),
                    subject.mutable,
                )
                .is_some()
        })
    };
    // No chain to follow: the first round's receipts stand exactly as written.
    if !movable(entries) {
        return;
    }
    let (mut kept, mut pending) = settle(entries, std::mem::take(lifts), roots);
    let mut kept_roots = roots
        .iter()
        .filter(|row| row.outcome == "lifted")
        .cloned()
        .collect::<Vec<_>>();
    let mut pending_roots = roots
        .iter()
        .filter(|row| row.outcome != "lifted")
        .cloned()
        .collect::<Vec<_>>();
    for _ in 0..entries.len() {
        // Only a held row some pass-on now reaches can move; otherwise stop.
        if !movable(entries) {
            break;
        }
        let before = held_count(entries);
        let mut round = super::licensed_lift::promote(ctx, entries);
        let round_roots = super::root_extent::promote(ctx, entries);
        round.extend(super::licensed_lift::promote_fallback(ctx, entries));
        let progressed = held_count(entries) != before;
        // This round is now the latest view of every row still held.
        let (final_now, still_held) = settle(entries, round, &round_roots);
        kept.extend(final_now);
        pending = still_held;
        kept_roots.extend(
            round_roots
                .iter()
                .filter(|row| row.outcome == "lifted")
                .cloned(),
        );
        pending_roots = round_roots
            .into_iter()
            .filter(|row| row.outcome != "lifted")
            .collect();
        if !progressed {
            break;
        }
    }
    // Where even the census identity collides (twins licensed by ONE callee),
    // a paired refusal that a still-held row also carries is that row's.
    let held_identities = pending
        .iter()
        .map(identity)
        .collect::<rustc_hash::FxHashSet<_>>();
    kept.retain(|lift| lift.declined.is_none() || !held_identities.contains(&identity(lift)));
    kept.extend(pending);
    kept_roots.extend(pending_roots);
    *lifts = kept;
    *roots = kept_roots;
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
    // **R536-6 R1 — the marks are keyed on a LABEL, so they are set only when
    // every candidate carrying that label agrees.** The lift rows name their
    // subject by label, and C2Rust's per-module duplicates share one. A
    // candidate here is a subject whose own uses the collector refused
    // (`unsupported` is set): only a lift can have taken such a subject to
    // `Slice`, and only such a subject can be declined at the use gate. A twin
    // the ladder delivered directly has no refused use and takes no part. Where
    // two candidates with one label disagree, no mark is written — the row is
    // left unmarked rather than marked for its twin.
    let refused_use = |subject: &Subject| {
        ctx.slice_uses
            .get(&(subject.fn_did, subject.hir_id))
            .is_some_and(|uses| uses.unsupported.is_some())
    };
    let lifted_mutable = |decision: &Decision| match decision {
        Decision::Slice { mutable, .. } => Some(*mutable),
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => None,
    };
    let mut refused_votes: FxHashMap<&str, Vec<bool>> = FxHashMap::default();
    let mut pass_on_votes: FxHashMap<&str, Vec<bool>> = FxHashMap::default();
    for (subject, decision) in entries {
        if !refused_use(subject) {
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        match lifted_mutable(decision) {
            Some(mutable) => pass_on_votes
                .entry(subject.label.as_str())
                .or_default()
                .push(supported(ctx, entries, node, mutable).is_some()),
            None => refused_votes
                .entry(subject.label.as_str())
                .or_default()
                .push(refused_by_mutability(ctx, entries, node)),
        }
    }
    let unanimous = |votes: &FxHashMap<&str, Vec<bool>>, label: &str| {
        votes.get(label).is_some_and(|v| v.iter().all(|&yes| yes))
    };
    for lift in lifts.iter_mut() {
        if lift.declined.is_some() && unanimous(&refused_votes, &lift.subject) {
            lift.use_shape = Some("pass-on-refused:shared-into-mut");
        }
        if lift.declined.is_none() && unanimous(&pass_on_votes, &lift.subject) {
            lift.use_shape = Some("pass-on");
        }
    }
    let mut out = Vec::new();
    for (subject, decision) in entries {
        let Some(mutable) = lifted_mutable(decision) else {
            continue;
        };
        if !refused_use(subject) {
            continue;
        }
        let Some(pairs) = supported(ctx, entries, (subject.fn_did, subject.hir_id), mutable) else {
            continue;
        };
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
