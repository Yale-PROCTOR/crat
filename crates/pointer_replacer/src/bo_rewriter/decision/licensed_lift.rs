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
    /// **Why this row was NOT lifted**, and by WHICH arm (wave-4 reports 047
    /// and 048). Until this column existed the family receipted only its lifts,
    /// so a census could say how many rows were fabricated but never why a held
    /// row was passed over — which is exactly the question C5 asked and the
    /// artifacts could not answer. A refusal is a decision and carries its
    /// reason, as B1's two-column table already does.
    pub(crate) declined: Option<Refusal>,
    /// **What the blocking use IS**, when the refusal is a slice-use one
    /// (report 058). `slice-use-unsupported` is the corpus's widest refusal —
    /// 85 of 172 at batch 28 — and "an assignment target" and "an argument at a
    /// local callee" are answered by completely different builds. The reason
    /// alone cannot choose between them.
    pub(crate) use_shape: Option<&'static str>,
}

/// **Which arm refused, and why.**
///
/// The two are separate classes and a census must not add them up: an
/// `Unlicensed` row was passed over by the EXACT arm and may still have been
/// lifted by the waiver below it (with a fabricated extent), while a `Declined`
/// row reached the bottom of the ladder and is held. C5 is the reason the first
/// variant exists: the row's waiver reason was recoverable from `295cf8b6a` and
/// the reason no WIDTH licensed it was not, so "why is this twin held while its
/// identical twin delivers?" stopped one question short of an answer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Refusal {
    /// The exact-width arm found no licensed width here.
    Unlicensed(&'static str),
    /// The waiver refused the row outright.
    Declined(&'static str),
}

impl Refusal {
    fn reason(self) -> &'static str {
        match self {
            Refusal::Unlicensed(reason) | Refusal::Declined(reason) => reason,
        }
    }

    /// The census's `extent_class` for this refusal.
    fn class(self) -> &'static str {
        match self {
            Refusal::Unlicensed(_) => "unlicensed",
            Refusal::Declined(_) => "declined",
        }
    }
}

impl LiftReceipt {
    /// The receipt key the seat reads at the census.
    pub(crate) fn key(&self) -> String {
        let index = self
            .parameter_index
            .map_or_else(|| "-".to_owned(), |index| index.to_string());
        if let Some(refusal) = self.declined {
            let reason = match self.use_shape {
                Some(shape) => format!("{}:{shape}", refusal.reason()),
                None => refusal.reason().to_owned(),
            };
            return match refusal {
                Refusal::Unlicensed(_) => {
                    format!(
                        "unlicensed(licensed-width:{}:{index}:{reason})",
                        self.callee
                    )
                }
                Refusal::Declined(_) => {
                    format!("declined(extent-lift:{}:{index}:{reason})", self.callee)
                }
            };
        }
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
) -> Result<&'a Region, &'static str> {
    let mut parameter_in_frame = false;
    for (subject, decision) in entries.iter() {
        if subject.fn_did != callee
            || !matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == index)
        {
            continue;
        }
        parameter_in_frame = true;
        if !delivers_slice(decision) {
            continue;
        }
        let Some(region) = ctx.void_region.get(&(subject.fn_did, subject.hir_id)) else {
            return Err("callee-carries-no-region");
        };
        // The seam reads a delivered slice at a width READ only.
        if region.shape != Shape::WidthRead {
            return Err("region-is-not-a-width-read");
        }
        if region.len_bytes.is_none() {
            return Err("region-width-is-not-exact");
        }
        return Ok(region);
    }
    // **The two `None`s a census must not confuse** (report 048). "Not in the
    // frame" is a callee this pass never saw; "not YET a slice" is one it saw
    // undecided, which is a statement about pass ORDER and not about the
    // callee — `void_region::licensed_width` asks the finished table and would
    // answer where this twin does not.
    Err(if parameter_in_frame {
        "callee-parameter-not-yet-a-slice"
    } else {
        "callee-parameter-not-in-frame"
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

/// The shape of the use that has no slice image, when there is one — the
/// column that separates "an assignment target" from "an argument at a local
/// callee", which are answered by different builds entirely.
fn unsupported_use_shape(ctx: &Ctx<'_, '_>, node: (LocalDefId, HirId)) -> Option<&'static str> {
    ctx.slice_uses.get(&node)?.unsupported_shape
}

/// **The lift.** Runs over the first pass's entries, after the other promotes,
/// and re-types held callers whose callee parameter carries an exact licensed
/// width.
pub(crate) fn promote(ctx: &Ctx<'_, '_>, entries: &mut [(Subject, Decision)]) -> Vec<LiftReceipt> {
    let mut widths: FxHashMap<(LocalDefId, HirId), (u64, bool, String, usize)> =
        FxHashMap::default();
    // **Every row this arm passes over says why** (report 048, relay 064). The
    // arm used to answer a held row silently, so a census could see that a
    // twin was not lifted and never learn whether the callee stated no width,
    // stated one this seam cannot read, or was simply not decided yet when this
    // pass ran. C5 — one brotli twin delivered, its identical twin held —
    // could not be answered from the artifacts for exactly that reason.
    let mut unlicensed: Vec<LiftReceipt> = Vec::new();
    for (subject, decision) in entries.iter() {
        let access = match held_at_a_local_callee(decision) {
            Some(access) => access,
            None => continue,
        };
        let mut refuse = |why: &'static str| {
            unlicensed.push(LiftReceipt {
                subject: subject.label.clone(),
                callee: access.callee.clone(),
                parameter_index: Some(access.parameter_index),
                width_bytes: None,
                mutable: subject.mutable,
                fallback: false,
                declined: Some(Refusal::Unlicensed(why)),
                use_shape: unsupported_use_shape(ctx, (subject.fn_did, subject.hir_id)),
            });
        };
        // **The width question is asked FIRST, whatever happens next** (report
        // 056). The ladder still refuses in its own order, but the census needs
        // to know whether a refusal is hiding a licensable width behind it: at
        // batch 27 ten of thirteen refusals were `caller-is-already-fat`, and
        // nothing in the tables could say whether those ten had a width waiting
        // or would have failed one question deeper. A reason that reports only
        // the first failing gate is an aim nobody can act on.
        let width = callee_region(ctx, entries, access.callee_id, access.parameter_index);
        let licensed = width
            .as_ref()
            .is_ok_and(|region| region.shape == Shape::WidthRead && region.len_bytes.is_some());
        // Already fat: the hold is about a one-element claim, and this
        // subject does not make one.
        if ctx.fat.is_array(subject.fn_did, subject.local) {
            refuse(if licensed {
                "caller-is-already-fat-with-a-licensed-width"
            } else {
                "caller-is-already-fat"
            });
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        if !slice_uses_supported(ctx, node) {
            refuse(if licensed {
                "slice-use-unsupported-with-a-licensed-width"
            } else {
                "slice-use-unsupported"
            });
            continue;
        }
        // EXACT, never the fallback: this is `void_region::licensed_width`.
        let region = match width {
            Ok(region) => region,
            Err(why) => {
                refuse(why);
                continue;
            }
        };
        let Some(width) = region.len_bytes else {
            refuse("region-width-is-not-exact");
            continue;
        };
        widths.insert(
            node,
            (
                width,
                region.mutable,
                access.callee.clone(),
                access.parameter_index,
            ),
        );
    }
    let mut receipts = unlicensed;
    for (subject, decision) in entries.iter_mut() {
        let Some((width, _region_mutable, callee, parameter_index)) =
            widths.get(&(subject.fn_did, subject.hir_id))
        else {
            continue;
        };
        // **R533-4 (wave-4 061 C7) — the SUBJECT's mutability.** A width-read
        // region is `mutable: false` (`void_region.rs`), so the old
        // `subject.mutable && region.mutable` lifted every exact-arm caller
        // SHARED — including one that writes through another of its uses,
        // which then hands `&[T]` to a writing formal and degrades the whole
        // program. A width read is rendered from a mutable slice as well
        // (`&s[..N]` auto-reborrows), so the lifted form keeps the subject's
        // own permission; the region's is the callee's, not the caller's.
        let mutable = subject.mutable;
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
            declined: None,
            use_shape: None,
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
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                lift.subject.split("::").next().unwrap_or(&lift.subject),
                lift.subject,
                lift.callee,
                lift.parameter_index
                    .map_or_else(|| "-".to_owned(), |index| index.to_string()),
                lift.width_bytes
                    .map_or_else(|| "-".to_owned(), |width| width.to_string()),
                if lift.mutable { "mut-slice" } else { "slice" },
                match (lift.declined, lift.fallback) {
                    (Some(refusal), _) => refusal.class(),
                    (None, true) => "fallback",
                    (None, false) => "evidence",
                },
                lift.use_shape.unwrap_or("-"),
                lift.key(),
            )
        })
        .collect::<Vec<_>>();
    rows.sort();
    let mut out = String::from(
        "owner_path\tsubject\tlicensing_callee\tparameter_index\twidth_bytes\tform\textent_class\tuse_shape\treceipt\n",
    );
    out.extend(rows);
    out
}

/// **R416-5, the exclusion the ruling names, at the place it actually bites.**
///
/// Lifting a PARAMETER makes every caller hand it a slice. A caller that is
/// itself thin has only one element to give, and the seam bridges it with
/// `core::slice::from_ref(..)` — a ONE-element slice into a callee that indexes
/// past one. That panic is certain, not possible, which is exactly what R416-5
/// refuses and what the ruling kept refusing. So the waiver may not lift a
/// parameter any of whose callers would arrive thin.
///
/// A caller counts as thin when its own decision is a reference form that
/// carries one element. A caller still `Degraded` at this point is NOT thin for
/// this test: it is raw, and a raw argument bridges with its own pointer, not
/// with `from_ref`.
fn a_caller_would_arrive_thin(
    ctx: &Ctx<'_, '_>,
    entries: &[(Subject, Decision)],
    owner: LocalDefId,
    index: usize,
) -> bool {
    let thin = |decision: &Decision| match decision {
        Decision::Ref { .. } | Decision::InferredRef { .. } => true,
        Decision::Opt { slice, .. } => !slice,
        Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Cursor { .. }
        | Decision::Box(_)
        | Decision::Degraded(_) => false,
    };
    ctx.facts
        .call_args
        .iter()
        .filter(|(callee, _)| **callee == owner)
        .flat_map(|(_, sites)| sites.iter())
        .filter_map(|site| {
            let argument = site.args.iter().find(|arg| arg.index == index)?;
            let root = match argument.shape {
                super::emitability::ArgShape::BareLocal(id)
                | super::emitability::ArgShape::CastOfLocal { binding: id, .. } => id,
                _ => return None,
            };
            entries
                .iter()
                .find(|(subject, _)| subject.fn_did == site.caller && subject.hir_id == root)
                .map(|(_, decision)| decision)
        })
        .any(thin)
}

/// **The mutability half of the same discipline, for `held:thin-extent` rows**
/// (relay 057, R483-3(b)).
///
/// A local-callee row records its access direction, so C2 (ii) of report 043
/// can refuse a SHARED subject at a WRITE. A thin-extent row records none: its
/// hold comes from the pinned contract table, not from a body walk. The
/// equivalent question is asked of the position itself — does any foreign
/// position this subject reaches take `*mut T`? If it does and the subject is
/// shared, lifting it makes the seam bridge `shared.as_ptr().cast_mut()`, and
/// writing through a pointer derived from a shared reference is UB that §77
/// does not waive: it waives the slice's LENGTH, never its mutability.
///
/// `rb_x3`'s `%s` printf subject is the witness — `printf(FMT, p.as_ptr().cast_mut())`
/// on a `*mut i8` position — and it is why this refusal exists rather than a
/// re-premised assertion.
fn reaches_a_mut_foreign_position(ctx: &Ctx<'_, '_>, node: (LocalDefId, HirId)) -> bool {
    ctx.facts.foreign_call_args.iter().any(|fact| {
        fact.caller == node.0
            && fact.direct_subject_root() == Some(node.1)
            && fact.target.mutability == super::raw_boundary::RawMutability::Mut
    })
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
/// **What is waived, stated precisely rather than softened.** Two things, and
/// the second is the one a reader must not miss:
///
/// 1. **Behaviour.** A checked index past 1024 PANICS where the C program read
///    on. The user accepted that trade on the record (addendum 481).
/// 2. **Slice-length UB, which was ALREADY out of scope.** The fabricated view
///    is `FALLBACK_SLICE_EXTENT` elements of an object whose real size nothing
///    here proved, so constructing it can exceed the allocation — and Rust's
///    contract for `from_raw_parts` is violated by the construction, not only
///    by a later access. That is exactly the slice-length UB the 2026-08-30
///    user+advisor ruling put out of scope under the named fallback extent, and
///    this arm extends that same waiver to a new population rather than opening
///    a new hole. It would be wrong to write "no UB is introduced" here; what
///    is true is that the UB in question is one the project has already
///    declared out of scope, receipted per site so the count is auditable.
///
/// Both belong in every claims-facing document beside the 2026-08-30 waiver.
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
    // The caller-side test below reads other subjects' decisions, so it needs
    // the frame as it stands BEFORE this pass rewrites any of them.
    let entries_snapshot: Vec<(Subject, Decision)> = entries.to_vec();
    let entries_snapshot = entries_snapshot.as_slice();
    let mut declines: Vec<LiftReceipt> = Vec::new();
    let mut decline =
        |subject: &Subject, callee: String, index: Option<usize>, why: &'static str| {
            declines.push(LiftReceipt {
                subject: subject.label.clone(),
                callee,
                parameter_index: index,
                width_bytes: None,
                mutable: subject.mutable,
                fallback: false,
                declined: Some(Refusal::Declined(why)),
                use_shape: unsupported_use_shape(ctx, (subject.fn_did, subject.hir_id)),
            });
        };
    let candidates: FxHashMap<(LocalDefId, HirId), (String, Option<usize>)> = entries
        .iter()
        .filter_map(|(subject, decision)| {
            let named = match decision {
                Decision::Degraded(record) => match &record.reason {
                    DegradeReason::LocalCalleeAccessExtent { access, .. } => {
                        // **A shared subject at a WRITE access is refused.**
                        // Lifting it yields `&[T]`, and the position wants
                        // `*mut T`, so the seam bridges `.cast_mut()` — writing
                        // through a pointer derived from a SHARED reference is
                        // UB of a kind no waiver here covers (§77 waives the
                        // slice's LENGTH, not its mutability). The subject stays
                        // held; its extent is not the problem.
                        if access.access == "write" && !subject.mutable {
                            decline(
                                subject,
                                access.callee.clone(),
                                Some(access.parameter_index),
                                "shared-subject-at-a-write",
                            );
                            return None;
                        }
                        (access.callee.clone(), Some(access.parameter_index))
                    }
                    DegradeReason::ThinExtent => {
                        // R483-3(b): the mutability half, asked of the position
                        // because a thin-extent row carries no direction.
                        if !subject.mutable
                            && reaches_a_mut_foreign_position(ctx, (subject.fn_did, subject.hir_id))
                        {
                            return None;
                        }
                        ("thin-extent".to_owned(), None)
                    }
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
                decline(subject, named.0.clone(), named.1, "slice-use-unsupported");
                return None;
            }
            // R416-5 at the caller side: a parameter whose caller arrives thin
            // would be fed `from_ref(..)`, a one-element slice into a callee
            // that indexes past one — a CERTAIN panic, which the ruling keeps
            // refusing.
            if let SubjectKind::Param { hir_index } = subject.kind
                && a_caller_would_arrive_thin(ctx, entries_snapshot, subject.fn_did, hir_index)
            {
                decline(subject, named.0.clone(), named.1, "a-caller-arrives-thin");
                return None;
            }
            // **R416-5 at the subject's own root.** A subject whose root is a borrow of a single place —
            // `&x`, `&arr[i]`, a place read — carries exactly one element, and
            // a fabricated 1024 over it does not risk a panic, it GUARANTEES
            // one at index 1. The waiver is for extents nothing bounds, not for
            // extents something bounds AT ONE.
            if matches!(
                ctx.constructions.by_binding.get(&node),
                Some(super::construction::Construction::AddrOf)
                    | Some(super::construction::Construction::IndexAddr)
            ) {
                decline(subject, named.0.clone(), named.1, "one-place-root");
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
            declined: None,
            use_shape: None,
        });
    }
    drop(decline);
    receipts.extend(declines);
    receipts.sort_by(|a, b| (a.subject.clone(), a.declined).cmp(&(b.subject.clone(), b.declined)));
    receipts
}
