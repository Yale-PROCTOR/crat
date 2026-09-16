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
//!
//! Wave 3 (R401-8): when the parameter is an exclusive reference the view is
//! UNTIED — `-> &'static mut T` / `&'static mut [T]` — the honest declaration
//! that Rust tracks no borrow behind a raw field (an exclusive tie would be
//! E0503 in every caller that reads the parameter while walking the view);
//! it rides the same T2 waiver with the per-site receipt `untied-return-view`,
//! the view-pair gate is active, and an untied view that the caller stores
//! into a field or returns further is a typed hold.
//!
//! Wave 4 (addendum 403, family-to-zero): the **dead return** — a callee whose
//! MIR never reaches an assignment to its return place (heman `kmAABB3Scale`:
//! `__assert_fail(..)` then `return pOut`) has no origin edge in NB5-O because
//! the return never executes. When the source returns a bare parameter, the
//! parameter tie is granted on a derived overlay: it is vacuously sound (no
//! value is ever returned) and it is the tie the live code would carry.
//!
//! Wave 2 adds two things. (1) The **pointee** class: a return derived from
//! the parameter's OWN pointee through a non-bare expression (brotli
//! `StartPosQueueAt`: `&*(*self_0).q_.as_ptr().offset(k) as *const PosData`,
//! an inline array field). NB5-O records `Arg/deref0 → Return` directly, so
//! no collapse is needed and the bridge is the existing T1 reborrow; the
//! existing rule only missed it because no SUBJECT escapes via the return.
//! (2) The **slice form**: when a caller walks or indexes the result, the
//! callee returns `&'a mut [T]` built with `core::slice::from_raw_parts_mut`
//! and the addendum-77 fallback extent receipt; thin callers of such a callee
//! are held `lifetime-seam-incompatible` rather than mis-typed.

use rustc_hash::FxHashMap;
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
    /// The return is a slice (`&'a mut [T]` over the fallback extent) because
    /// at least one caller walks or indexes the result.
    pub(crate) slice: bool,
    /// R401-8: the parameter is an exclusive reference, so the view is
    /// UNTIED (`&'static`) — the honest declaration that Rust tracks no
    /// borrow behind the raw field; receipted `untied-return-view`.
    pub(crate) untied: bool,
}

impl ThroughRawFieldReuse {
    pub(crate) fn receipt_key(&self) -> String {
        format!(
            "through_raw_field={}\tparameter={}\tform={}\ttie={}",
            self.traversal.join(","),
            self.parameter.receipt_key(),
            if self.slice { "slice" } else { "thin" },
            if self.untied {
                "untied-return-view"
            } else {
                "parameter"
            }
        )
    }
}

/// A derived permit for one callee: the parameter node the permit is keyed
/// by, the origin slots the planner needs, and the overlay summary carrying
/// the collapsed edge.
#[derive(Clone, Debug)]
pub(crate) struct CalleePermit {
    pub(crate) parameter_node: NodeKey,
    pub(crate) parameter: FnSignatureSlot,
    pub(crate) parameter_origin: OriginSlot,
    pub(crate) return_origin: OriginSlot,
    /// `None` is the pointee class: the summary already carries the edge and
    /// the existing T1 reborrow applies.
    pub(crate) reuse: Option<ThroughRawFieldReuse>,
    pub(crate) overlay: Option<OriginSummary>,
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
    slice: bool,
    dead_return_parameter: Option<rustc_middle::mir::Local>,
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
        // The dead return: no reachable assignment to the return place, and
        // the source's return expression is the bare parameter `root`. The
        // derived overlay carries the tie NB5-O could not observe.
        let Some(root) = dead_return_parameter else {
            return Err(LifetimeFailure::OriginAbsent);
        };
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
        // EXHAUSTIVE: the dead-return parameter is decided as it stands.
        match decisions.get(&parameter_node) {
            Some(Decision::Ref { .. }) => {}
            Some(
                Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_)
                | Decision::NestedSlice { .. }
                | Decision::Cursor { .. },
            ) => {}
            Some(Decision::Degraded(_)) | None => {
                // The escaping parameter is itself degraded in the hypothetical
                // (`escapes-via-return` blocks it); the permit is what lifts
                // that, exactly as the bare-parameter permit does.
            }
        }
        let mut overlay = summary.clone();
        overlay.subset.insert(parameter_origin, return_origin);
        return Ok(CalleePermit {
            parameter_node,
            parameter: FnSignatureSlot::arg(root.as_u32() as usize, 0, 0),
            parameter_origin,
            return_origin,
            reuse: None,
            overlay: Some(overlay),
        });
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
    // Every source is either the parameter's own pointee (the pointee class:
    // `deref0`, no field) or reached through raw storage. A mix has no single
    // honest bridge tier and is held.
    let pointee_sources = sources
        .iter()
        .filter(|(_, slot)| slot.place.deref_depth == 0 && slot.place.field.is_none())
        .count();
    let pointee_class = match pointee_sources {
        0 => false,
        n if n == sources.len() => true,
        _ => return Err(LifetimeFailure::OriginConflict),
    };
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
    let parameter_mutable = match decisions.get(&parameter_node) {
        Some(Decision::Ref { mutable }) => *mutable,
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
    };
    let parameter = FnSignatureSlot::arg(root.as_u32() as usize, 0, 0);
    let _ = program;
    // A return through raw storage does not point into `*p`, so tying it to
    // an EXCLUSIVE borrow of `*p` would forbid the caller every read of `*p`
    // while the view lives (heman's callers read `(*img).nbands` in the loop
    // that walks the view: E0503, a revert that takes the owner's other
    // deliveries down). A shared parameter lends its lifetime; an exclusive
    // one yields an UNTIED view (R401-8) — the pointee class is exactly the
    // case where the exclusive tie is right, so it is exempt.
    let untied = !pointee_class && parameter_mutable;

    if pointee_class {
        return Ok(CalleePermit {
            parameter_node,
            parameter,
            parameter_origin,
            return_origin,
            reuse: None,
            overlay: None,
        });
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
    Ok(CalleePermit {
        parameter_node,
        parameter,
        parameter_origin,
        return_origin,
        reuse: Some(ThroughRawFieldReuse {
            parameter,
            traversal,
            slice,
            untied,
        }),
        overlay: Some(overlay),
    })
}

/// Whether the caller local walks or indexes the value it receives — the
/// uses a thin reference cannot serve, so the callee must return a slice.
pub(crate) fn arithmetic_use(
    raw_only_uses: &FxHashMap<NodeKey, Vec<(String, rustc_span::Span)>>,
    node: NodeKey,
) -> bool {
    raw_only_uses.get(&node).is_some_and(|uses| {
        uses.iter().any(|(op, _)| {
            matches!(
                op.as_str(),
                "offset" | "wrapping_offset" | "add" | "sub" | "wrapping_add" | "wrapping_sub"
            )
        })
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

/// EXHAUSTIVE: a call-result local delivered by a construction OVER the raw
/// call (a sealed slice constructor, an optional or cursor form) — a
/// delivery the initializer-channel composition renders over this lane's
/// view, so it names the callee exactly as a residual caller does.
pub(crate) fn is_raw_call_construction(decision: Option<&&Decision>) -> bool {
    match decision {
        Some(
            Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. },
        ) => true,
        Some(
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Box(_)
            | Decision::Degraded(_),
        )
        | None => false,
    }
}

/// Direct local callees named by at least one `return-not-adapted` caller
/// local, with EVERY call-result local of that callee — the return form is
/// decided from all of them so it never moves between family stages (a
/// walking caller degraded at an early stage still fixes the form).
pub(crate) fn candidate_callees(
    subjects: &[Subject],
    decisions: &FxHashMap<NodeKey, &Decision>,
    constructions: &super::construction::ConstructionFacts,
) -> FxHashMap<LocalDefId, Vec<NodeKey>> {
    use super::construction::{CallResultTarget, Construction};
    let mut callers = FxHashMap::<LocalDefId, Vec<NodeKey>>::default();
    let mut named = FxHashMap::<LocalDefId, bool>::default();
    for subject in subjects
        .iter()
        .filter(|subject| matches!(subject.ctor, Some(Construction::CallResult)))
    {
        let node = (subject.fn_did, subject.hir_id);
        let Some(target) = constructions.call_result_targets.get(&node) else {
            continue;
        };
        match target {
            CallResultTarget::DirectLocal(callee) => {
                callers.entry(*callee).or_default().push(node);
                let decision = decisions.get(&node);
                *named.entry(*callee).or_default() |= is_return_residual(decision);
                // A call-result local another family delivers from the raw
                // call (a sealed slice constructor over the result) keeps
                // that delivery: the constructor is composed over this lane's
                // view of the adapted call (the initializer-channel
                // composition, wave 6), so the callee stays this rule's.
                *named.entry(*callee).or_default() |= is_raw_call_construction(decision);
            }
            CallResultTarget::Indirect
            | CallResultTarget::Foreign
            | CallResultTarget::Unresolved => {}
        }
    }
    callers.retain(|callee, _| named.get(callee).copied().unwrap_or(false));
    callers
}

/// The local's initializer CASTS the call (`let n = callee(..) as *mut U`):
/// the binding's type is the cast's target, never the callee's borrowed
/// return, so no inferred reference may type it (the cast position is the
/// native-result expression carrier's, with a typed hold on the local).
pub(crate) fn initializer_is_cast(program: &RustProgram<'_>, subject: &Subject) -> bool {
    let tcx = program.tcx;
    let mut node = subject.hir_id;
    loop {
        match tcx.parent_hir_node(node) {
            rustc_hir::Node::Pat(pat) => node = pat.hir_id,
            rustc_hir::Node::LetStmt(local) => {
                return local
                    .init
                    .is_some_and(|init| matches!(init.kind, rustc_hir::ExprKind::Cast(..)));
            }
            _ => return false,
        }
    }
}

/// The cast initializer's target is a raw pointer (`*mut U` / `*const U`),
/// so the local can hold `&U` / `&mut U` through a typed reborrow.
pub(crate) fn initializer_casts_to_raw_pointer(
    program: &RustProgram<'_>,
    subject: &Subject,
) -> bool {
    let tcx = program.tcx;
    let mut node = subject.hir_id;
    loop {
        match tcx.parent_hir_node(node) {
            rustc_hir::Node::Pat(pat) => node = pat.hir_id,
            rustc_hir::Node::LetStmt(local) => {
                return local.init.is_some_and(|init| {
                    matches!(init.kind, rustc_hir::ExprKind::Cast(..))
                        && matches!(
                            tcx.typeck(subject.fn_did).expr_ty(init).kind(),
                            TyKind::RawPtr(..)
                        )
                });
            }
            _ => return false,
        }
    }
}

/// The dead-return parameter of a callee: the bare parameter its `return`
/// hands back when no reachable MIR block assigns the return place (a
/// diverging call precedes every return). `None` when the return place is
/// reachable or the returned value is not a bare parameter.
pub(crate) fn dead_return_parameter(
    program: &RustProgram<'_>,
    callee: LocalDefId,
    escapes: &[super::co_conversion::Escape],
    subjects: &[Subject],
) -> Option<rustc_middle::mir::Local> {
    use rustc_middle::mir::{RETURN_PLACE, StatementKind, TerminatorKind};
    let body_ref = program
        .tcx
        .mir_drops_elaborated_and_const_checked(callee)
        .borrow();
    let reachable = rustc_middle::mir::traversal::reachable_as_bitset(&body_ref);
    let assigns_return = body_ref
        .basic_blocks
        .iter_enumerated()
        .filter(|(block, _)| reachable.contains(*block))
        .any(|(_, data)| {
            data.statements.iter().any(|statement| {
                matches!(&statement.kind, StatementKind::Assign(assign) if assign.0.local == RETURN_PLACE)
            }) || matches!(
                &data.terminator().kind,
                TerminatorKind::Call { destination, .. } if destination.local == RETURN_PLACE
            )
        });
    if assigns_return {
        return None;
    }
    let mut returned = escapes
        .iter()
        .filter(|escape| escape.subject.0 == callee)
        .filter(|escape| matches!(escape.kind, super::co_conversion::EscapeKind::Return))
        .filter_map(|escape| {
            subjects.iter().find(|subject| {
                (subject.fn_did, subject.hir_id) == escape.subject
                    && subject.ptr_depth == 1
                    && matches!(subject.kind, SubjectKind::Param { .. })
            })
        })
        .map(|subject| subject.local)
        .collect::<Vec<_>>();
    returned.sort_unstable();
    returned.dedup();
    match returned.as_slice() {
        [local] => Some(*local),
        _ => None,
    }
}
