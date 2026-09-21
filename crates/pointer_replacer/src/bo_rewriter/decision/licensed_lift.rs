//! **W4-LIFT (seat addendum 475, R475-2) — the licensed-width caller lift.**
//!
//! [`super::local_callee_extent`] holds a caller whose THIN subject is handed
//! to a local callee parameter that accesses past one element. The hold names
//! the access and asks for an extent; it does not say where one could come
//! from, and for the `void-pointee-cast-to` half of the class the caller has no
//! evidence of its own — the callee casts an opaque address to a real type, and
//! how many bytes that is, is the CALLEE's fact.
//!
//! wave-6b's region family proves exactly that fact and exports it:
//! [`super::void_region::licensed_width`] answers with the callee parameter's
//! EXACT byte width where that family typed it (`BrotliUnalignedRead32::p` →
//! `Some(4)`, `Read64` → `Some(8)`) and with `None` for the addendum-77
//! fallback arm, for another index, or for a parameter it never typed. A width
//! so proven is a count position of the callee parameter's own pinned contract
//! and a stronger one (R408-1): the value is the callee's own type rather than
//! a position whose value must be read.
//!
//! So the lift: at a held site whose callee parameter carries an exact licensed
//! width `w`, the caller's thin subject takes the SLICE form. Its extent is its
//! own root's — an evidence-backed length where the root supplies one, else the
//! §77 fallback, receipted per site with `FALLBACK_SLICE_EXTENT = 1024 ≥ w` —
//! and the argument is then bridged from a delivered slice rather than
//! fabricated from a one-element claim. R416-5's refusal is untouched: it
//! refuses widening a caller that STAYS thin, and after the lift this one does
//! not.
//!
//! What is deliberately NOT lifted:
//!
//! - **A callee width that is the fallback** (`licensed_width` = `None`). A
//!   fabricated extent licenses no companion (R408-1) and cannot license a
//!   form either.
//! - **A width at another index.** The export is keyed by parameter position
//!   and so is the hold; they must be the same position.
//! - **A caller that is already fat.** It carries its own extent; the hold is
//!   about the thin claim and there is nothing to lift.
//! - **A caller whose slice uses are unsupported.** `&[T]` changes the type at
//!   every occurrence, so a subject with a use that has no slice image would
//!   yield an ill-typed crate — the same rule the slice ladder applies.
//! - **Shapes the seam cannot render from a delivered slice.** wave-6b's
//!   region bridge reads a delivered slice for a [`Shape::WidthRead`] position
//!   only (`&s[..N]`, `seam.rs`'s `region_from_slice`); at a width WRITE the
//!   seam still wants the raw form, so lifting the caller there would trade a
//!   held subject for a blocked seam. The write mirror is named here rather
//!   than attempted.

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{
    Ctx, Decision, DegradeReason, Subject, SubjectKind, local_callee_extent,
    void_region::{Region, Shape},
};

/// One lift, for the receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LiftReceipt {
    pub(crate) subject: String,
    pub(crate) callee: String,
    pub(crate) parameter_index: Option<usize>,
    /// The exact licensed width in bytes, from wave-6b's export. `None` is the
    /// waiver arm: no width was licensed and none was recovered from a root.
    pub(crate) width_bytes: Option<u64>,
    pub(crate) mutable: bool,
    /// **The extent-lift waiver (R481-1).** `true` means this subject took the
    /// slice form with `FALLBACK_SLICE_EXTENT`, not with an extent anything
    /// proved.
    pub(crate) fallback: bool,
}

impl LiftReceipt {
    /// The receipt key the seat reads at the census.
    pub(crate) fn key(&self) -> String {
        let index = self
            .parameter_index
            .map_or_else(|| "-".to_owned(), |index| index.to_string());
        match self.width_bytes {
            Some(width) => format!("evidence(licensed-width:{}:{index}:{width})", self.callee),
            None => format!("fallback(extent-lift@addendum-77:{}:{index})", self.callee),
        }
    }
}

/// The callee parameter's region, looked up over `entries` rather than over a
/// finished [`super::DecisionTable`].
///
/// This is the entries-shaped twin of [`super::void_region::parameter`] and
/// asks its three questions in the same order — same callee, same parameter
/// index, decided as the slice form — because the lift runs INSIDE `decide`,
/// where the table does not exist yet. `licensed_lift_tests` pins the twin
/// against `void_region::licensed_width` on a shared fixture so the two cannot
/// drift.
fn callee_region<'a>(
    ctx: &'a Ctx<'_, '_>,
    entries: &[(Subject, Decision)],
    callee: LocalDefId,
    index: usize,
) -> Option<&'a Region> {
    entries.iter().find_map(|(subject, decision)| {
        (subject.fn_did == callee
            && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == index)
            && delivers_slice(decision))
        .then(|| ctx.void_region.get(&(subject.fn_did, subject.hir_id)))
        .flatten()
    })
}

/// Did the callee parameter deliver as the slice form this family emits under?
///
/// Exhaustive on purpose, and for the reason the import denylist enforces: a
/// `matches!` would compile clean against a new disposition and lift a caller
/// into a callee whose form nobody checked. The twin of
/// [`super::void_region::decided_slice`], which asks the same question of the
/// finished table.
pub(crate) fn delivers_slice(decision: &Decision) -> bool {
    match decision {
        Decision::Slice { .. } => true,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => false,
    }
}

/// The hold this lift answers, if this is that hold.
///
/// Exhaustive for the same reason as [`delivers_slice`].
pub(crate) fn held_at_a_local_callee(
    decision: &Decision,
) -> Option<&local_callee_extent::LocalCalleeAccess> {
    match decision {
        Decision::Degraded(record) => match &record.reason {
            DegradeReason::LocalCalleeAccessExtent { access, .. } => Some(access),
            _ => None,
        },
        Decision::Slice { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. } => None,
    }
}

/// Would this subject's slice form be well typed at every one of its uses?
///
/// An ABSENT entry means the subject has no use the slice form must rewrite,
/// which is the thin case this class is about — so absence is supported, the
/// same default the ladder itself takes (`slice_uses.get(..).unwrap_or_default()`
/// immediately before its own `unsupported` check).
pub(crate) fn slice_uses_supported(ctx: &Ctx<'_, '_>, node: (LocalDefId, HirId)) -> bool {
    ctx.slice_uses
        .get(&node)
        .is_none_or(|uses| uses.unsupported.is_none())
}

/// The subject's own slice-use rewrites, empty when it has none of its own (the
/// thin case this class is about: the subject is handed over and not indexed).
pub(crate) fn slice_rewrites(
    ctx: &Ctx<'_, '_>,
    node: (LocalDefId, HirId),
) -> Vec<super::emitability::UseEdit> {
    ctx.slice_uses
        .get(&node)
        .map(|uses| uses.rewrites.clone())
        .unwrap_or_default()
}

/// **The lift.** Runs over the first pass's entries, after the other promotes,
/// and re-types held callers whose callee parameter carries an exact licensed
/// width.
pub(crate) fn promote(ctx: &Ctx<'_, '_>, entries: &mut [(Subject, Decision)]) -> Vec<LiftReceipt> {
    let widths: FxHashMap<(LocalDefId, HirId), (u64, bool, String, usize)> = entries
        .iter()
        .filter_map(|(subject, decision)| {
            let access = held_at_a_local_callee(decision)?;
            // Already fat: the hold is about a one-element claim, and this
            // subject does not make one.
            if ctx.fat.is_array(subject.fn_did, subject.local) {
                return None;
            }
            let node = (subject.fn_did, subject.hir_id);
            if !slice_uses_supported(ctx, node) {
                return None;
            }
            let region = callee_region(ctx, entries, access.callee_id, access.parameter_index)?;
            // The seam reads a delivered slice at a width READ only.
            if region.shape != Shape::WidthRead {
                return None;
            }
            // EXACT, never the fallback: this is `void_region::licensed_width`.
            let width = region.len_bytes?;
            Some((
                node,
                (
                    width,
                    region.mutable,
                    access.callee.clone(),
                    access.parameter_index,
                ),
            ))
        })
        .collect();
    let mut receipts = Vec::new();
    for (subject, decision) in entries.iter_mut() {
        let Some((width, region_mutable, callee, parameter_index)) =
            widths.get(&(subject.fn_did, subject.hir_id))
        else {
            continue;
        };
        let mutable = subject.mutable && *region_mutable;
        *decision = Decision::Slice {
            mutable,
            uses: slice_rewrites(ctx, (subject.fn_did, subject.hir_id)),
        };
        receipts.push(LiftReceipt {
            subject: subject.label.clone(),
            callee: callee.clone(),
            parameter_index: Some(*parameter_index),
            width_bytes: Some(*width),
            mutable,
            fallback: false,
        });
    }
    receipts.sort_by(|a, b| a.subject.cmp(&b.subject));
    receipts
}

/// **The census receipt** (relay 052: the lifts are counted at the census, not
/// only in the table). One row per lift, in the same shape as this lane's
/// decline receipt: the owner path, the subject, the callee whose width
/// licensed it, the parameter position, the exact width in bytes, and the form
/// the caller took.
pub(crate) fn receipts_tsv(receipts: &[LiftReceipt]) -> String {
    let mut rows = receipts
        .iter()
        .map(|lift| {
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                lift.subject.split("::").next().unwrap_or(&lift.subject),
                lift.subject,
                lift.callee,
                lift.parameter_index
                    .map_or_else(|| "-".to_owned(), |index| index.to_string()),
                lift.width_bytes
                    .map_or_else(|| "-".to_owned(), |width| width.to_string()),
                if lift.mutable { "mut-slice" } else { "slice" },
                if lift.fallback {
                    "fallback"
                } else {
                    "evidence"
                },
                lift.key(),
            )
        })
        .collect::<Vec<_>>();
    rows.sort();
    let mut out = String::from(
        "owner_path\tsubject\tlicensing_callee\tparameter_index\twidth_bytes\tform\textent_class\treceipt\n",
    );
    out.extend(rows);
    out
}

/// **The extent-lift waiver — USER ruling R481-1 ("바로 1024로 fat 처리"),
/// addendum 481.**
///
/// The arms above answer a held row with EVIDENCE: wave-6b's exact licensed
/// width here, wave-5c's mask companion and [`super::root_extent`]'s root walk
/// after it. What is left is the population the seat sized for Decision A —
/// rows whose access nothing bounds — and the user's answer is to lift them
/// anyway, with `FALLBACK_SLICE_EXTENT`.
///
/// **What is waived is BEHAVIOUR, and it is stated rather than hidden.** A
/// checked index past 1024 PANICS where the C program read on. That is not a
/// soundness waiver — no UB is introduced, the slice is a real 1024-byte view
/// of a live allocation — it is a behavioural one, accepted by the user on the
/// record and owed a line in every claims-facing document, beside the
/// slice-extent waiver it extends (2026-08-30).
///
/// The discipline that rides it is ORDER: this pass runs LAST, after the exact
/// width, after the mask companion, and after the root walk, so a fabricated
/// extent is never taken where a proven one exists. Two things stay refused:
/// a caller already fat (it carries its own extent), and the one-element
/// `from_ref` form R416-5 names, whose panic is certain rather than possible.
pub(crate) fn promote_fallback(
    ctx: &Ctx<'_, '_>,
    entries: &mut [(Subject, Decision)],
) -> Vec<LiftReceipt> {
    let candidates: FxHashMap<(LocalDefId, HirId), (String, Option<usize>)> = entries
        .iter()
        .filter_map(|(subject, decision)| {
            let named = match decision {
                Decision::Degraded(record) => match &record.reason {
                    DegradeReason::LocalCalleeAccessExtent { access, .. } => {
                        (access.callee.clone(), Some(access.parameter_index))
                    }
                    DegradeReason::ThinExtent => ("thin-extent".to_owned(), None),
                    _ => return None,
                },
                Decision::Slice { .. }
                | Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::NestedSlice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_)
                | Decision::Cursor { .. } => return None,
            };
            // **No `is_array` refusal here, deliberately.** Fatness says the
            // subject is USED like an array, which is true of most of this
            // population — it is why the callee walks off the one-element claim
            // in the first place. What "already fat" has to mean is "already
            // delivered in a form carrying an extent", and the `Degraded` filter
            // above is exactly that test.
            let node = (subject.fn_did, subject.hir_id);
            if !slice_uses_supported(ctx, node) {
                return None;
            }
            // **R416-5 stays in force, and it is the ONE exclusion the ruling
            // names.** A subject whose root is a borrow of a single place —
            // `&x`, `&arr[i]`, a place read — carries exactly one element, and
            // a fabricated 1024 over it does not risk a panic, it GUARANTEES
            // one at index 1. The waiver is for extents nothing bounds, not for
            // extents something bounds AT ONE.
            if matches!(
                ctx.constructions.by_binding.get(&node),
                Some(super::construction::Construction::AddrOf)
                    | Some(super::construction::Construction::IndexAddr)
            ) {
                return None;
            }
            Some((node, named))
        })
        .collect();
    let mut receipts = Vec::new();
    for (subject, decision) in entries.iter_mut() {
        let Some((callee, parameter_index)) = candidates.get(&(subject.fn_did, subject.hir_id))
        else {
            continue;
        };
        *decision = Decision::Slice {
            mutable: subject.mutable,
            uses: slice_rewrites(ctx, (subject.fn_did, subject.hir_id)),
        };
        receipts.push(LiftReceipt {
            subject: subject.label.clone(),
            callee: callee.clone(),
            parameter_index: *parameter_index,
            width_bytes: None,
            mutable: subject.mutable,
            fallback: true,
        });
    }
    receipts.sort_by(|a, b| a.subject.cmp(&b.subject));
    receipts
}
