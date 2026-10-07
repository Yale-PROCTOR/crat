//! **R864-3 (relay 299; era-5c 154 / 154a / 157c) — the retained-access check of record
//! as the joint fixpoint's fourth predicate.** era-5c's check (`retained_access`, (E)
//! with (ii)'s readings, computed once per program) names the subjects whose referent an
//! evident shape reaches: a value derived from the subject stored into memory (E1), a
//! self-reference (E2), a cycle (E3). On the settled table the predicate holds such a
//! subject raw (`held:retained-alias`, detail `evident:<rule>:<place> | <witness>`), under
//! the three filters of era-5c 154 as 154a §2 completes them:
//!
//! 1. only a subject the settled table decides in a reference family: a `Box` is a move,
//!    not an alias, and a raw or degraded subject is raw already;
//! 2. where the raw-boundary retention tier wrote a disposition other than T1 at a site
//!    the subject is the argument of (a tier-2 waiver, a blocked site, a site another arm
//!    owns), the tier's disposition stands and the check adds nothing;
//! 3. an E1 derived store into a place the rewriter delivers — a field the model decides
//!    `Ref` / `Owning`, a field or array field a field transaction applies, an array local
//!    wave-6f delivers — is not a retained raw pointer. The delivered places are read from
//!    the stage's table before any retained hold (154a §2.1: the transaction the table
//!    would apply with the subject not held). E2 and E3 are never exempt.
//!
//! The holds join the joint fixpoint as the planned holds do: the stage is decided again
//! with them forced raw, before anything is planned (154a class C: a lend planned for the
//! reference the hold forces raw).

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;

use super::{
    Decision, DecisionTable, DegradeReason, SubjectKind,
    raw_boundary::{RawBoundaryDisposition, RawBoundaryDispositionIndex},
    retained_access::{Hold, HoldKind, RetainedAccessCheck, StoreDest, Verdict},
};
use crate::analyses::borrow_ownership::{
    SlotKind, crate_slots::CrateSlots, slots::StructFieldSlot, solver::SlotRef,
};

/// The places the rewriter delivers on the stage's not-held table (filter 3).
#[derive(Clone, Debug, Default)]
pub(crate) struct Delivered {
    /// `(struct def index, field index)` of an applied field transaction (an array field's
    /// too).
    fields: FxHashSet<(u32, usize)>,
    /// `(function def index, MIR local)` of an array local wave-6f delivers.
    array_locals: FxHashSet<(u32, u32)>,
}

impl Delivered {
    pub(crate) fn of(tcx: TyCtxt<'_>, table: &DecisionTable) -> Self {
        let mut out = Self::default();
        for transaction in &table.field_transactions.applied {
            match &transaction.array {
                None => {
                    out.fields.insert((
                        transaction.key.struct_did.local_def_index.as_u32(),
                        transaction.key.field_index,
                    ));
                }
                Some(array) => {
                    if let Some(local) = mir_local_of(tcx, array.owner, array.binding) {
                        out.array_locals
                            .insert((array.owner.local_def_index.as_u32(), local.as_u32()));
                    }
                }
            }
        }
        out
    }
}

/// The MIR local of a HIR binding, by the debug info's place at the binding's span.
fn mir_local_of(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    binding: HirId,
) -> Option<rustc_middle::mir::Local> {
    let span = tcx.hir_span(binding);
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    body.var_debug_info
        .iter()
        .find_map(|info| match &info.value {
            rustc_middle::mir::VarDebugInfoContents::Place(place)
                if place.projection.is_empty() && info.source_info.span == span =>
            {
                Some(place.local)
            }
            _ => None,
        })
}

/// A derived store through a reference to a place (`*p = v` with `p = &mut
/// (*h).f`, wave-6f's `&mut` store idiom), which the check names `Other`: the
/// field `(struct def index, field index)` the one definition of `p` borrows, read
/// at the store's site in the body the check read.
fn store_through_borrow(
    tcx: TyCtxt<'_>,
    (function, block, statement): (u32, u32, usize),
) -> Option<(u32, usize)> {
    use rustc_middle::mir::{BasicBlock, ProjectionElem, Rvalue, StatementKind};
    let function = LocalDefId {
        local_def_index: rustc_hir::def_id::DefIndex::from_u32(function),
    };
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let StatementKind::Assign(assign) = &body
        .basic_blocks
        .get(BasicBlock::from_u32(block))?
        .statements
        .get(statement)?
        .kind
    else {
        return None;
    };
    let dst = assign.0;
    // `*p` or `(*p)[i]`: a store through `p`.
    if !matches!(
        dst.projection.as_slice(),
        [ProjectionElem::Deref] | [ProjectionElem::Deref, ProjectionElem::Index(_)]
    ) {
        return None;
    }
    let mut definitions = body
        .basic_blocks
        .iter()
        .flat_map(|data| &data.statements)
        .filter_map(|statement| match &statement.kind {
            StatementKind::Assign(assign)
                if assign.0.local == dst.local && assign.0.projection.is_empty() =>
            {
                Some(&assign.1)
            }
            _ => None,
        });
    let (Some(Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed)), None) =
        (definitions.next(), definitions.next())
    else {
        return None;
    };
    let projection = borrowed.projection.as_slice();
    let end = match projection.last()? {
        ProjectionElem::Field(..) => projection.len(),
        // An element of an array field.
        ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => projection.len() - 1,
        _ => return None,
    };
    let ProjectionElem::Field(field, _) = projection.get(end.checked_sub(1)?)? else {
        return None;
    };
    let parent = rustc_middle::mir::Place {
        local: borrowed.local,
        projection: tcx.mk_place_elems(&projection[..end - 1]),
    };
    match parent.ty(&*body, tcx).ty.kind() {
        rustc_middle::ty::TyKind::Adt(adt, _) => adt
            .did()
            .as_local()
            .map(|did| (did.local_def_index.as_u32(), field.index())),
        _ => None,
    }
}

/// A derived store through a pointer local whose pointee slot the model decides a
/// reference or an owner (`*out = p` with `out: &mut &'a T`, E2's output storage): the
/// place it stores into is delivered as a reference, as a field the model decides `Ref`
/// is (filter 3's reading for a field, at a pointer's depth-1 slot).
fn store_into_delivered_slot(
    tcx: TyCtxt<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    (function, block, statement): (u32, u32, usize),
) -> bool {
    use rustc_middle::mir::{BasicBlock, ProjectionElem, StatementKind};
    let function = LocalDefId {
        local_def_index: rustc_hir::def_id::DefIndex::from_u32(function),
    };
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let Some(StatementKind::Assign(assign)) = body
        .basic_blocks
        .get(BasicBlock::from_u32(block))
        .and_then(|data| data.statements.get(statement))
        .map(|statement| &statement.kind)
    else {
        return false;
    };
    let dst = assign.0;
    matches!(dst.projection.as_slice(), [ProjectionElem::Deref])
        && slots
            .fn_local_slots
            .get(&function)
            .and_then(|universe| universe.slot_for_local_depth(dst.local, 1))
            .and_then(|slot| model.get(&SlotRef::Local(function, slot)).copied())
            .is_some_and(|kind| matches!(kind, SlotKind::Ref | SlotKind::Owning))
}

/// Filter 1: the reference families, the only decisions the check acts on. Exhaustive by
/// rule (`import_denylist`).
fn reference_family(decision: &Decision) -> bool {
    match decision {
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Cursor { .. } => true,
        Decision::Box(_) | Decision::Degraded(_) => false,
    }
}

/// Filter 2: the retention tier decides a site the subject is the argument of, or,
/// for a formal, a site that passes into it (154a §2.2: wave-6s's positive-retention
/// pin sits on the caller's argument, not on the retaining formal). A T1 row alone
/// (no-retention evidence) is not a disposition of its own.
fn tier_decides(
    raw_boundary: &RawBoundaryDispositionIndex,
    node: (LocalDefId, HirId),
    formal: Option<usize>,
) -> bool {
    let decides = |disposition: &RawBoundaryDisposition| match disposition {
        RawBoundaryDisposition::T1 { .. } => false,
        RawBoundaryDisposition::T2 { .. }
        | RawBoundaryDisposition::Blocked { .. }
        | RawBoundaryDisposition::OwnedByOtherArm { .. } => true,
    };
    raw_boundary
        .node_dispositions(node)
        .iter()
        .any(|(_, disposition)| decides(disposition))
        || formal.is_some_and(|index| {
            raw_boundary
                .inventoried_sites()
                .any(|(key, disposition, site)| {
                    site.callee_local == Some(node.0)
                        && key.argument_index == index
                        && decides(disposition)
                })
        })
}

/// The subjects to hold on this table, each with its receipt.
pub(crate) fn holds(
    tcx: TyCtxt<'_>,
    facts: &super::emitability::EmitabilityFacts,
    table: &DecisionTable,
    raw_boundary: &RawBoundaryDispositionIndex,
    check: &RetainedAccessCheck,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    delivered: &Delivered,
) -> Vec<((LocalDefId, HirId), DegradeReason)> {
    // Filter 3: a field the model decides a reference or an owner, or a transaction
    // applies.
    let field_delivered = |struct_index: u32, field_index: usize| {
        delivered.fields.contains(&(struct_index, field_index)) || {
            let struct_did = LocalDefId {
                local_def_index: rustc_hir::def_id::DefIndex::from_u32(struct_index),
            };
            slots
                .field_slots
                .slot_for_field_depth(
                    StructFieldSlot {
                        struct_did,
                        field_index,
                    },
                    0,
                )
                .map(SlotRef::Field)
                .and_then(|slot| model.get(&slot).copied())
                .is_some_and(|kind| matches!(kind, SlotKind::Ref | SlotKind::Owning))
        }
    };
    // Each candidate's holds left after filter 3's place readings.
    let mut candidates: Vec<((LocalDefId, HirId), Vec<Hold>)> = Vec::new();
    for (subject, decision) in &table.entries {
        if !reference_family(decision) {
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        let formal = match subject.kind {
            SubjectKind::Param { hir_index } => Some(hir_index),
            SubjectKind::Local => None,
        };
        if tier_decides(raw_boundary, node, formal) {
            continue;
        }
        let verdict = match subject.kind {
            SubjectKind::Param { .. } => check.formal(subject.fn_did, subject.local.as_usize()),
            SubjectKind::Local => check.local(subject.fn_did, subject.local),
        };
        let Some(Verdict::Held(holds)) = verdict else {
            continue;
        };
        let kept: Vec<_> = holds
            .iter()
            .filter(|hold| {
                !(hold.kind == HoldKind::DerivedStore
                    && match hold.dest {
                        StoreDest::Field(struct_index, field_index)
                        | StoreDest::ArrayInField(struct_index, field_index) => {
                            field_delivered(struct_index, field_index)
                        }
                        StoreDest::ArrayLocal(local) => {
                            hold.site.is_some_and(|(function, _, _)| {
                                delivered.array_locals.contains(&(function, local))
                            })
                        }
                        StoreDest::Other => hold.site.is_some_and(|site| {
                            store_through_borrow(tcx, site).is_some_and(
                                |(struct_index, field_index)| {
                                    field_delivered(struct_index, field_index)
                                },
                            ) || store_into_delivered_slot(tcx, slots, model, site)
                        }),
                        // Read below, against the callee formals' own outcome.
                        StoreDest::None | StoreDest::Callee => false,
                    })
            })
            .cloned()
            .collect();
        if !kept.is_empty() {
            candidates.push((node, kept));
        }
    }
    // **A callee that keeps what it is passed** (154a §2.1: the callee formal's own
    // decision): the store is the callee's, so it is exempt where every in-program formal
    // the subject is handed to is delivered as a reference and not held itself — its
    // own stores are then into delivered places. Read to a fixpoint from all held, so an
    // exemption rests only on formals shown not held; a subject handed to no formal of
    // the program (a foreign callee) stays held.
    let decision_of: FxHashMap<(LocalDefId, HirId), &Decision> = table
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect();
    let formal_of: FxHashMap<(LocalDefId, usize), (LocalDefId, HirId)> = table
        .entries
        .iter()
        .filter_map(|(subject, _)| match subject.kind {
            SubjectKind::Param { hir_index } => Some((
                (subject.fn_did, hir_index),
                (subject.fn_did, subject.hir_id),
            )),
            SubjectKind::Local => None,
        })
        .collect();
    let receivers = |node: (LocalDefId, HirId)| -> Option<Vec<(LocalDefId, HirId)>> {
        let mut found = Vec::new();
        for (callee, calls) in &facts.call_args {
            for call in calls.iter().filter(|call| call.caller == node.0) {
                for arg in call
                    .args
                    .iter()
                    .filter(|arg| arg.shape.place_root() == Some(node.1))
                {
                    found.push(*formal_of.get(&(*callee, arg.index))?);
                }
            }
        }
        (!found.is_empty()).then_some(found)
    };
    let mut held: FxHashSet<(LocalDefId, HirId)> =
        candidates.iter().map(|(node, _)| *node).collect();
    loop {
        let released: Vec<_> = candidates
            .iter()
            .filter(|(node, kept)| {
                held.contains(node)
                    && kept.iter().all(|hold| {
                        hold.kind == HoldKind::DerivedStore && hold.dest == StoreDest::Callee
                    })
                    && receivers(*node).is_some_and(|formals| {
                        formals.iter().all(|formal| {
                            !held.contains(formal)
                                && decision_of.get(formal).is_some_and(|d| reference_family(d))
                        })
                    })
            })
            .map(|(node, _)| *node)
            .collect();
        if released.is_empty() {
            break;
        }
        for node in released {
            held.remove(&node);
        }
    }
    let mut out = Vec::new();
    for (node, kept) in candidates {
        if !held.contains(&node) {
            continue;
        }
        if let Some(detail) = Verdict::Held(kept).evident_receipt() {
            out.push((node, DegradeReason::RetainedAlias { detail }));
        }
    }
    out.sort_by_key(|((function, binding), _)| {
        (function.local_def_index.as_u32(), binding.local_id.as_u32())
    });
    out
}
