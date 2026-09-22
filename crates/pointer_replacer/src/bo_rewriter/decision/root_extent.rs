//! **W4-B1 (seat addendum 480, R480-2) — root-extent propagation.**
//!
//! [`super::licensed_lift`] answers the `held:local-callee-access-extent` rows
//! whose CALLEE states an exact width. The rest — `BrotliWriteBits::array` and
//! its 56 callers among them — have accesses no evidence bounds, and the seat's
//! rule for those is the other direction: not the callee's width, the caller's
//! ROOT.
//!
//! A thin subject whose root is an allocation of a known size, an array, a
//! NUL-terminated literal or a buffer with a companion length HAS an extent —
//! it is simply one the ladder never asked for, because the subject's own uses
//! are thin and the access is a callee's. B1 asks for it: at a held row, walk
//! to the subject's root, and where the root states an extent, the subject
//! takes the slice form carrying THAT extent.
//!
//! **No fabrication, and that is the point of the rule.** A row whose root
//! states no extent stays held and is COUNTED. The §77 fallback is not
//! available here: a `&[T]` built on a fabricated 1024 turns every index past
//! the real end into a PANIC where the C program read on — a fabricated extent
//! is sound at a foreign boundary that reads a prefix, and unsound as a
//! program's own bound. The counted residue is the seat's Decision A input.
//!
//! The two positions:
//!
//! - **A LOCAL** carries its own construction, and
//!   [`super::construction::root_extent`] is exactly the evidence half of the
//!   length planner (allocation size, array decay, literal bytes, companion
//!   length) with its fallback arm removed.
//! - **A PARAMETER** has no construction of its own: its extent is its
//!   callers'. It lifts only when EVERY call site hands it something that
//!   itself states an extent — a caller subject already delivered as a slice
//!   (its length is the caller's own), or a local with a root extent. One call
//!   site that cannot, and the parameter is held: a slice parameter whose
//!   caller has no length to pass has only the fallback left, which is the
//!   thing this rule refuses.
//!
//! The forwarding the hold already records (`reason_detail`, up to three hops)
//! is the callee side of the same chain and is unchanged: B1 decides the
//! CALLER's form, and the hold's own walk decides which callers are in the
//! class.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{
    Ctx, Decision, Subject, SubjectKind, construction::SliceLengthSource, emitability::ArgShape,
    licensed_lift::held_at_a_local_callee,
};

/// One decided row, for the receipt: lifted with its evidence, or held with the
/// reason no extent was found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RootExtentRow {
    pub(crate) subject: String,
    pub(crate) position: &'static str,
    /// `lifted` or `held`.
    pub(crate) outcome: &'static str,
    /// The ROOT's own answer, independent of whether the form can be rendered:
    /// the evidence key, or why no extent was found. **This column is the
    /// seat's Decision A input** — how many rows have an extent to propagate —
    /// and it is deliberately not collapsed into the outcome, because a row can
    /// state an extent and still be held by the emission gate below.
    pub(crate) extent: String,
    /// Why the row was not lifted, when it was not.
    pub(crate) evidence: String,
}

/// Why a row could not be lifted. Each is a counted residue class, and the
/// count is what the seat's Decision A is about.
fn held(subject: &Subject, position: &'static str, extent: String, reason: &str) -> RootExtentRow {
    RootExtentRow {
        subject: subject.label.clone(),
        position,
        outcome: "held",
        extent,
        evidence: reason.to_owned(),
    }
}

/// **The element type, when the declaration does not spell one** (R501, dry27).
///
/// `Subject::pointee_span` is the pointee's SOURCE TEXT, kept so a plan can copy
/// it verbatim — and an unannotated declaration has none. That is not a rare
/// shape: C2Rust writes `let mut storage = 0 as *mut uint8_t;` for every C
/// declaration-then-assignment, brotli's whole `storage` tree among them, so
/// without a fallback link (1) would follow the assignment and then fail for
/// want of a type name.
///
/// The fallback is rustc's own rendering of the pointee, and it is taken **only
/// for a primitive**. A printed struct or alias path is not guaranteed to name
/// the same type in the emitted crate, and an extent expression that does not
/// compile is worse than no extent; a primitive prints as itself (`uint8_t` →
/// `u8`), which is both valid there and correct here.
fn printed_element_type(ctx: &Ctx<'_, '_>, subject: &Subject) -> Option<String> {
    let ty = ctx
        .tcx
        .typeck(subject.fn_did)
        .node_type_opt(subject.hir_id)?;
    let rustc_middle::ty::TyKind::RawPtr(pointee, _) = ty.kind() else {
        return None;
    };
    matches!(
        pointee.kind(),
        rustc_middle::ty::TyKind::Int(_)
            | rustc_middle::ty::TyKind::Uint(_)
            | rustc_middle::ty::TyKind::Float(_)
            | rustc_middle::ty::TyKind::Bool
            | rustc_middle::ty::TyKind::Char
    )
    .then(|| pointee.to_string())
}

/// The subject's own root extent, if its construction states one.
fn local_root_extent(ctx: &Ctx<'_, '_>, subject: &Subject) -> Option<SliceLengthSource> {
    let node = (subject.fn_did, subject.hir_id);
    let init_hir = *ctx.constructions.init_hirs.get(&node)?;
    let element_type = subject
        .pointee_span
        .and_then(|span| ctx.tcx.sess.source_map().span_to_snippet(span).ok())
        .or_else(|| printed_element_type(ctx, subject))?;
    super::construction::root_extent(
        ctx.tcx,
        ctx.constructions,
        subject,
        &element_type,
        init_hir,
        &FxHashMap::default(),
    )
    .map(|plan| plan.source)
}

/// **Why a root states nothing — the shape it has instead** (wave-4 report 047).
///
/// `none` alone tells the seat that 43 rows have no extent; it does not say
/// whether those roots are FIELDS whose size is recorded in a sibling (brotli's
/// `(*s).storage_` beside `(*s).storage_size_`, a shape a later build could
/// read) or opaque call results nothing could recover. The receipt therefore
/// carries the root's own construction key, so the next build is chosen on the
/// distribution rather than on a guess.
fn root_shape(ctx: &Ctx<'_, '_>, subject: &Subject) -> String {
    match super::construction::walked_construction(
        ctx.constructions,
        (subject.fn_did, subject.hir_id),
    ) {
        // R501 link (1): the SHAPE follows the walk, so a null-declared local
        // whose assignment the walk now reads reports the assignment's shape.
        // Reporting `null-lit` here would say the walk stopped at the
        // declaration when it did not.
        Some((construction, _)) => format!("none:{}", construction.key()),
        None => "none:no-construction".to_owned(),
    }
}

/// Does this subject state an extent a caller could pass on — either because it
/// is already delivered as a slice, or because its own root states one?
fn states_an_extent(
    ctx: &Ctx<'_, '_>,
    entries: &FxHashMap<(LocalDefId, HirId), &Decision>,
    subject: &Subject,
) -> bool {
    if entries
        .get(&(subject.fn_did, subject.hir_id))
        .is_some_and(|decision| super::licensed_lift::delivers_slice(decision))
    {
        return true;
    }
    local_root_extent(ctx, subject).is_some()
}

/// Every call site of this parameter's owner, and what it is handed there.
///
/// `None` means "a site this rule cannot read" — an argument shape that does
/// not denote a subject — which is a HOLD, never an assumption.
fn every_caller_states_an_extent(
    ctx: &Ctx<'_, '_>,
    entries: &FxHashMap<(LocalDefId, HirId), &Decision>,
    subjects: &FxHashMap<(LocalDefId, HirId), &Subject>,
    owner: LocalDefId,
    index: usize,
) -> Result<(), &'static str> {
    let mut seen = false;
    for (callee, sites) in &ctx.facts.call_args {
        if *callee != owner {
            continue;
        }
        for site in sites {
            let Some(argument) = site.args.iter().find(|arg| arg.index == index) else {
                continue;
            };
            seen = true;
            let root = match argument.shape {
                ArgShape::BareLocal(id) | ArgShape::CastOfLocal { binding: id, .. } => id,
                _ => return Err("caller-argument-not-a-binding"),
            };
            let Some(caller_subject) = subjects.get(&(site.caller, root)) else {
                return Err("caller-argument-not-a-subject");
            };
            if !states_an_extent(ctx, entries, caller_subject) {
                return Err("caller-root-states-no-extent");
            }
        }
    }
    if seen {
        Ok(())
    } else {
        Err("no-call-site-read")
    }
}

/// **The rule.** Runs after [`super::licensed_lift::promote`], so a row that
/// family already answered is never reconsidered here.
pub(crate) fn promote(
    ctx: &Ctx<'_, '_>,
    entries: &mut [(Subject, Decision)],
) -> Vec<RootExtentRow> {
    let decisions: FxHashMap<(LocalDefId, HirId), &Decision> = entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect();
    let subjects: FxHashMap<(LocalDefId, HirId), &Subject> = entries
        .iter()
        .map(|(subject, _)| ((subject.fn_did, subject.hir_id), subject))
        .collect();
    let mut rows = Vec::new();
    let mut lift: FxHashSet<(LocalDefId, HirId)> = FxHashSet::default();
    for (subject, decision) in entries.iter() {
        if held_at_a_local_callee(decision).is_none() {
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        // **Column one: does the ROOT state an extent?** Answered first and
        // recorded whatever happens next, because this is the question the
        // seat's Decision A asks and it is independent of whether this build
        // can render the form.
        let (position, extent) = match subject.kind {
            SubjectKind::Local => (
                "local",
                local_root_extent(ctx, subject).map_or_else(
                    || Err("root-states-no-extent"),
                    |source| Ok(source.receipt_key()),
                ),
            ),
            SubjectKind::Param { hir_index } => (
                "param",
                every_caller_states_an_extent(
                    ctx,
                    &decisions,
                    &subjects,
                    subject.fn_did,
                    hir_index,
                )
                .map(|()| "every-caller-states-an-extent".to_owned()),
            ),
        };
        let extent = match extent {
            Ok(evidence) => evidence,
            Err(reason) => {
                // **R489-3(b): `no-call-site-read` is UNMEASURED, not
                // evidence-absent.** A parameter whose function has no call
                // site the fact table records cannot have its extent proven
                // from callers — and that is a gap in what was observed, not a
                // root that states nothing. It carries its own outcome so a
                // residue count (`outcome == "held"`) leaves it out; the seat's
                // Decision A is about roots that state nothing.
                let outcome = if reason == "no-call-site-read" {
                    "unmeasured"
                } else {
                    "held"
                };
                rows.push(RootExtentRow {
                    subject: subject.label.clone(),
                    position,
                    outcome,
                    extent: root_shape(ctx, subject),
                    evidence: reason.to_owned(),
                });
                continue;
            }
        };
        // **Column two: can the slice form be rendered here?** A use with no
        // slice image would yield an ill-typed crate, so the row is held — but
        // its extent is recorded above, which is what separates "no extent to
        // propagate" from "an extent this build cannot yet carry".
        if !super::licensed_lift::slice_uses_supported(ctx, node) {
            rows.push(held(subject, position, extent, "slice-use-unsupported"));
            continue;
        }
        lift.insert(node);
        rows.push(RootExtentRow {
            subject: subject.label.clone(),
            position,
            outcome: "lifted",
            extent,
            evidence: "-".to_owned(),
        });
    }
    for (subject, decision) in entries.iter_mut() {
        if !lift.contains(&(subject.fn_did, subject.hir_id)) {
            continue;
        }
        *decision = Decision::Slice {
            mutable: subject.mutable,
            uses: super::licensed_lift::slice_rewrites(ctx, (subject.fn_did, subject.hir_id)),
        };
    }
    rows.sort_by(|a, b| (a.subject.clone(), a.outcome).cmp(&(b.subject.clone(), b.outcome)));
    rows
}

/// **The census receipt.** One row per decided subject — the lifts with their
/// evidence key and, the point of the rule, the HELD rows with the reason no
/// extent was found. The held count is the seat's Decision A input.
pub(crate) fn receipts_tsv(rows: &[RootExtentRow]) -> String {
    let mut out =
        String::from("owner_path\tsubject\tposition\toutcome\troot_extent\theld_reason\n");
    let mut lines = rows
        .iter()
        .map(|row| {
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\n",
                row.subject.split("::").next().unwrap_or(&row.subject),
                row.subject,
                row.position,
                row.outcome,
                row.extent,
                row.evidence,
            )
        })
        .collect::<Vec<_>>();
    lines.sort();
    out.extend(lines);
    out
}
