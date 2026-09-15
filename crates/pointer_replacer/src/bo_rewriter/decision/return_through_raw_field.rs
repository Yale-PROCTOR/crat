//! wave-6l rule W6L-1 — a returned reference whose origin is reached THROUGH
//! RAW STORAGE of one input parameter.
//!
//! The NB5-O origin summary of a callee such as heman's
//! `heman_image_texel(img, x, y) -> (*img).data.offset(..)` names the return's
//! only source as `Arg(img)/deref1/field(data)`: a pointer read out of a raw
//! field of the parameter's pointee. E2's planner refuses every field-mediated
//! slot (`lifetime-field-held`), because a PROMOTED field would need a struct
//! lifetime. Here the field stays raw; only the returned value becomes a
//! reference, and the tightest lifetime Rust can name for it without a struct
//! parameter is the parameter's own borrow. This module derives that collapse
//! as a typed permit, never by touching the frozen model: the summary overlay
//! it hands the planner is a rewriter-side derived view (E2 §3, derive-on-load).
//!
//! Soundness (conditional on a UB-free input, §28): every dereference of the
//! returned reference in the emitted program is a dereference the input
//! performs at the same point, so the memory is valid at every use; tying the
//! reference to the parameter's borrow only narrows where Rust lets it be used
//! (the compile gate reverts, it never widens). The reference is manufactured
//! from a raw pointer with a receipted T2 reborrow: raw aliases the C program
//! retains to the same memory are the retention-unknown class every argument
//! bridge already rides under the named T2 waiver (R130). What NO existing
//! gate examines is a second live SAFE view of the same memory in the caller,
//! so a mutable view is admitted only when the caller has no other safe
//! pointer subject over the same pointee type (strict aliasing makes a
//! type-distinct live view disjoint in a UB-free input; `c_void` / byte
//! pointees are treated as wildcards). Shared views may alias each other.
//!
//! Multiple parameters feeding one return are a typed hold
//! (`lifetime-origin-ambiguous`), per the charter: no guessed lifetime.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::RETURN_PLACE, ty::TyKind};

use super::{
    Decision, Subject, SubjectKind,
    co_conversion::NodeKey,
    lifetime::{FnSignatureSlot, LifetimeFailure},
};
use crate::{
    analyses::borrow_ownership::{
        SlotKind,
        crate_slots::CrateSlots,
        origin_summary::{OriginSlot, OriginSummaries, OriginSummary, SignatureRoot},
        solver::SlotRef,
    },
    utils::rustc::RustProgram,
};

/// The collapse one callee earned: its return borrows `parameter`'s own
/// lifetime, and `traversal` names the raw slots the origin actually passed
/// through — the receipt of what was collapsed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ThroughRawFieldReuse {
    pub(crate) parameter: FnSignatureSlot,
    pub(crate) traversal: Vec<String>,
}

impl ThroughRawFieldReuse {
    pub(crate) fn receipt_key(&self) -> String {
        format!(
            "through_raw_field={}\tparameter={}",
            self.traversal.join(","),
            self.parameter.receipt_key()
        )
    }
}

/// A derived permit for one callee: the parameter node the permit is keyed
/// by, the origin slots the planner needs, and the overlay summary carrying
/// the collapsed edge.
#[derive(Clone, Debug)]
pub(crate) struct CalleePermit {
    pub(crate) parameter_node: NodeKey,
    pub(crate) parameter_origin: OriginSlot,
    pub(crate) return_origin: OriginSlot,
    pub(crate) reuse: ThroughRawFieldReuse,
    pub(crate) overlay: OriginSummary,
}

fn traversal_key(root_index: u32, deref_depth: u8, depth: u8, field: bool) -> String {
    if field {
        format!("arg{root_index}/deref{deref_depth}/field")
    } else {
        format!("arg{root_index}/deref{deref_depth}/depth{depth}")
    }
}

/// Derive the permit for one direct local callee, or the typed failure its
/// callers carry.
pub(crate) fn derive_callee(
    program: &RustProgram<'_>,
    callee: LocalDefId,
    origins: Option<&OriginSummaries>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    decisions: &FxHashMap<NodeKey, &Decision>,
    subjects: &[Subject],
) -> Result<CalleePermit, LifetimeFailure> {
    let summary = origins
        .and_then(|origins| origins.get(&callee))
        .ok_or(LifetimeFailure::OriginAbsent)?;
    let returns = summary
        .slots
        .iter_enumerated()
        .filter(|(_, slot)| {
            slot.place.root == SignatureRoot::Return
                && slot.place.field.is_none()
                && slot.place.deref_depth == 0
                && slot.depth == 0
        })
        .map(|(origin, _)| origin)
        .collect::<Vec<_>>();
    let [return_origin] = returns.as_slice() else {
        return Err(LifetimeFailure::OriginConflict);
    };
    let return_origin = *return_origin;
    if summary.unknown.contains(return_origin) {
        return Err(LifetimeFailure::OriginUnknown);
    }
    let model_kind = |local: rustc_middle::mir::Local, depth: u8| {
        slots
            .fn_local_slots
            .get(&callee)
            .and_then(|universe| universe.slot_for_local_depth(local, depth))
            .and_then(|slot| model.get(&SlotRef::Local(callee, slot)))
            .copied()
    };
    if model_kind(RETURN_PLACE, 0) != Some(SlotKind::Ref) {
        return Err(LifetimeFailure::OriginConflict);
    }
    // Every source of the return, whatever its depth: the raw traversal is
    // the whole point, so nothing is filtered by shape here.
    let sources = summary
        .slots
        .iter_enumerated()
        .filter(|(origin, _)| {
            *origin != return_origin && summary.subset.contains(*origin, return_origin)
        })
        .collect::<Vec<_>>();
    if sources.is_empty() {
        return Err(LifetimeFailure::OriginAbsent);
    }
    let mut roots = sources
        .iter()
        .filter_map(|(_, slot)| match slot.place.root {
            SignatureRoot::Arg(local) => Some(local),
            SignatureRoot::Return => None,
        })
        .collect::<Vec<_>>();
    roots.sort_unstable();
    roots.dedup();
    let [root] = roots.as_slice() else {
        return Err(if roots.is_empty() {
            LifetimeFailure::OriginAbsent
        } else {
            LifetimeFailure::OriginAmbiguous
        });
    };
    let root = *root;
    // A bare parameter source belongs to the existing E2 return permit; this
    // rule owns only origins that pass through raw storage.
    if sources
        .iter()
        .any(|(_, slot)| slot.place.deref_depth == 0 && slot.place.field.is_none())
    {
        return Err(LifetimeFailure::OriginConflict);
    }
    let parameter_origin = summary
        .slots
        .iter_enumerated()
        .find(|(_, slot)| {
            slot.place.root == SignatureRoot::Arg(root)
                && slot.place.field.is_none()
                && slot.place.deref_depth == 0
                && slot.depth == 0
        })
        .map(|(origin, _)| origin)
        .ok_or(LifetimeFailure::OriginAbsent)?;
    if model_kind(root, 0) != Some(SlotKind::Ref) {
        return Err(LifetimeFailure::OriginConflict);
    }
    let parameter = subjects
        .iter()
        .find(|subject| {
            subject.fn_did == callee
                && subject.ptr_depth == 1
                && matches!(subject.kind, SubjectKind::Param { hir_index }
                    if hir_index.checked_add(1).and_then(|index| u32::try_from(index).ok())
                        == Some(root.as_u32()))
        })
        .ok_or(LifetimeFailure::OriginConflict)?;
    let parameter_node = (parameter.fn_did, parameter.hir_id);
    // EXHAUSTIVE: the parameter must be a plain reference in the safe
    // variant; every other disposition has no borrow to lend the return.
    match decisions.get(&parameter_node) {
        Some(Decision::Ref { .. }) => {}
        Some(
            Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Degraded(_),
        )
        | None => return Err(LifetimeFailure::OriginConflict),
    }
    let mut traversal = sources
        .iter()
        .map(|(_, slot)| {
            traversal_key(
                root.as_u32(),
                slot.place.deref_depth,
                slot.depth,
                slot.place.field.is_some(),
            )
        })
        .collect::<Vec<_>>();
    traversal.sort_unstable();
    traversal.dedup();
    let mut overlay = summary.clone();
    overlay.subset.insert(parameter_origin, return_origin);
    let _ = program;
    Ok(CalleePermit {
        parameter_node,
        parameter_origin,
        return_origin,
        reuse: ThroughRawFieldReuse {
            parameter: FnSignatureSlot::arg(root.as_u32() as usize, 0, 0),
            traversal,
        },
        overlay,
    })
}

fn pointee_key(program: &RustProgram<'_>, subject: &Subject) -> Option<String> {
    let ty = program.tcx.typeck(subject.fn_did).node_type(subject.hir_id);
    let TyKind::RawPtr(pointee, _) = *ty.kind() else {
        return None;
    };
    Some(pointee.to_string())
}

fn wildcard_pointee(key: &str) -> bool {
    matches!(
        key,
        "u8" | "i8" | "core::ffi::c_void" | "libc::c_void" | "std::ffi::c_void" | "c_void"
    ) || key.ends_with("::c_void")
        || key.ends_with("::c_char")
        || key.ends_with("::c_uchar")
}

/// The caller-side gate for a MUTABLE returned view: no other safe pointer
/// subject of the caller may cover the same pointee type. `admitted_safe`
/// answers whether a sibling subject is (or would be) a safe view.
pub(crate) fn mutable_view_pair_held(
    program: &RustProgram<'_>,
    subject: &Subject,
    subjects: &[Subject],
    admitted_safe: &dyn Fn(&Subject) -> bool,
) -> bool {
    let Some(pointee) = pointee_key(program, subject) else {
        return true;
    };
    subjects.iter().any(|sibling| {
        sibling.fn_did == subject.fn_did
            && (sibling.fn_did, sibling.hir_id) != (subject.fn_did, subject.hir_id)
            && admitted_safe(sibling)
            && pointee_key(program, sibling).is_some_and(|other| {
                other == pointee || wildcard_pointee(&other) || wildcard_pointee(&pointee)
            })
    })
}

/// EXHAUSTIVE: only the residue this rule exists to serve.
pub(crate) fn is_return_residual(decision: Option<&&Decision>) -> bool {
    match decision {
        Some(Decision::Degraded(record)) => record.reason == super::DegradeReason::ReturnNotAdapted,
        Some(
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. },
        )
        | None => false,
    }
}

/// EXHAUSTIVE: whether a hypothetical decision is (or will be) a safe view.
pub(crate) fn is_safe_view(decision: Option<&&Decision>) -> bool {
    match decision {
        Some(
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. },
        ) => true,
        Some(Decision::Box(_) | Decision::Degraded(_)) | None => false,
    }
}

/// Direct local callees named by the caller locals this rule may serve.
pub(crate) fn candidate_callees(
    subjects: &[Subject],
    decisions: &FxHashMap<NodeKey, &Decision>,
    constructions: &super::construction::ConstructionFacts,
) -> FxHashSet<LocalDefId> {
    use super::construction::{CallResultTarget, Construction};
    subjects
        .iter()
        .filter(|subject| {
            matches!(subject.ctor, Some(Construction::CallResult))
                && is_return_residual(decisions.get(&(subject.fn_did, subject.hir_id)))
        })
        .filter_map(|subject| {
            match constructions
                .call_result_targets
                .get(&(subject.fn_did, subject.hir_id))?
            {
                CallResultTarget::DirectLocal(callee) => Some(*callee),
                CallResultTarget::Indirect
                | CallResultTarget::Foreign
                | CallResultTarget::Unresolved => None,
            }
        })
        .collect()
}
