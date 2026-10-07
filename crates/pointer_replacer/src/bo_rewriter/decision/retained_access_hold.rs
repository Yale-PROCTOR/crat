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
//! 2. where the raw-boundary retention tier wrote a retention disposition (the tier-2
//!    waiver, positive retention, an unconfirmed waiver) at a site passing the subject's
//!    own value, the tier's disposition stands and the check adds nothing;
//! 3. an E1 derived store into a place the rewriter delivers is not a retained raw
//!    pointer: a field or an array a field transaction applies on the current table,
//!    also through a reborrow of the field (wave-6f's `&mut` store idiom); an output slot
//!    E2's output-storage permit admits for the subject, of a delivered formal; a callee
//!    whose receiving formals are delivered and not held. E2 and E3 are never exempt.
//!
//! The current table's transactions (not a snapshot of the stage's first pass, the
//! stand-in review's HIGH-1): the map only grows within a stage, so a subject exempt on a
//! table where its field applies is never held for its own store, and a field another
//! hold withdraws holds its stores on the next pass. A field the model decides `Ref` but
//! the rewriter holds raw (wave-6f's `field-mutable-held`) is no delivered place.
//!
//! The holds join the joint fixpoint as the planned holds do: the stage is decided again
//! with them forced raw, before anything is planned (154a class C).

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
    },
    ty::TyCtxt,
};

use super::{
    Decision, DecisionTable, DegradeReason, SubjectKind,
    lifetime::LifetimeEligibility,
    raw_boundary::{RawBoundaryBlockReason, RawBoundaryDisposition, RawBoundaryDispositionIndex},
    retained_access::{Hold, HoldKind, RetainedAccessCheck, StoreDest, Verdict},
};

/// The places the current table delivers (filter 3).
#[derive(Clone, Debug, Default)]
struct Delivered {
    /// `(struct def index, field index)` of an applied field transaction (an array
    /// field's too).
    fields: FxHashSet<(u32, usize)>,
    /// `(function def index, MIR local)` of an array local wave-6f delivers.
    array_locals: FxHashSet<(u32, u32)>,
}

impl Delivered {
    fn of(tcx: TyCtxt<'_>, table: &DecisionTable) -> Self {
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
fn mir_local_of(tcx: TyCtxt<'_>, function: LocalDefId, binding: HirId) -> Option<Local> {
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

fn local_def(index: u32) -> LocalDefId {
    LocalDefId {
        local_def_index: rustc_hir::def_id::DefIndex::from_u32(index),
    }
}

/// The store `*p = v` / `(*p)[i] = v` at a site: the function, the body and `p`.
fn store_through<'b>(
    body: &'b Body<'_>,
    (block, statement): (u32, usize),
) -> Option<(Local, bool)> {
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
    match dst.projection.as_slice() {
        [ProjectionElem::Deref] => Some((dst.local, false)),
        [ProjectionElem::Deref, ProjectionElem::Index(_)] => Some((dst.local, true)),
        _ => None,
    }
}

/// The one definition of a MIR local: assigned whole exactly once by a statement, never
/// a formal, never a call's destination, its address never taken (the stand-in review's
/// MED-2).
fn single_definition<'b, 'tcx>(body: &'b Body<'tcx>, local: Local) -> Option<&'b Rvalue<'tcx>> {
    if local.as_usize() <= body.arg_count {
        return None;
    }
    let mut definition = None;
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            if assign.0.local == local && assign.0.projection.is_empty() {
                if definition.is_some() {
                    return None;
                }
                definition = Some(&assign.1);
            }
            if let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = &assign.1
                && place.local == local
                && place.projection.is_empty()
            {
                return None;
            }
        }
        if let Some(terminator) = &data.terminator
            && let TerminatorKind::Call { destination, .. } = &terminator.kind
            && destination.local == local
        {
            return None;
        }
    }
    definition
}

/// A derived store through a reference to a place (`*p = v` with `p = &mut (*h).f`,
/// wave-6f's `&mut` store idiom), which the check names `Other`: the field `(struct def
/// index, field index)` the one definition of `p` borrows.
fn store_through_borrow(
    tcx: TyCtxt<'_>,
    (function, block, statement): (u32, u32, usize),
) -> Option<(u32, usize)> {
    let body = tcx
        .mir_drops_elaborated_and_const_checked(local_def(function))
        .borrow();
    let (pointer, _) = store_through(&body, (block, statement))?;
    let (Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed)) =
        single_definition(&body, pointer)?
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

/// A derived store `*out = v` into the output slot of a formal `out` the table delivers,
/// where E2's output-storage permit admits the subject's value there (`out: &mut &'a T`):
/// the slot is a reference the rewriter emits (the stand-in review's HIGH-2: the model's
/// depth-1 kind alone is not).
fn store_into_output_slot(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    lifetime: &LifetimeEligibility,
    subject: (LocalDefId, HirId),
    (function, block, statement): (u32, u32, usize),
) -> bool {
    let function = local_def(function);
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let Some((pointer, false)) = store_through(&body, (block, statement)) else {
        return false;
    };
    table.entries.iter().any(|(target, decision)| {
        target.fn_did == function
            && target.local == pointer
            && reference_family(decision)
            && lifetime.permits_output_storage(subject, (target.fn_did, target.hir_id))
    })
}

/// The in-program formals a subject's value reaches at calls of its own function, read
/// from MIR (the stand-in review's MED-1: copies, casts, borrows, aggregates and call
/// results carry it): `None` where a carrier reaches a call no program formal receives
/// (a foreign callee, an aggregate argument, a position that is no subject).
fn receiving_formals(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    local: Local,
    formal_of: &FxHashMap<(LocalDefId, usize), (LocalDefId, HirId)>,
) -> Option<Vec<(LocalDefId, HirId)>> {
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let mut carriers: FxHashSet<Local> = FxHashSet::default();
    carriers.insert(local);
    let reads = |operand: &Operand<'_>, carriers: &FxHashSet<Local>| {
        operand
            .place()
            .is_some_and(|place| carriers.contains(&place.local))
    };
    loop {
        let before = carriers.len();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let carries = match &assign.1 {
                    Rvalue::Use(operand)
                    | Rvalue::Cast(_, operand, _)
                    | Rvalue::Repeat(operand, _) => reads(operand, &carriers),
                    Rvalue::Ref(_, _, place)
                    | Rvalue::RawPtr(_, place)
                    | Rvalue::CopyForDeref(place) => carriers.contains(&place.local),
                    Rvalue::Aggregate(_, operands) => {
                        operands.iter().any(|operand| reads(operand, &carriers))
                    }
                    Rvalue::BinaryOp(_, operands) => {
                        reads(&operands.0, &carriers) || reads(&operands.1, &carriers)
                    }
                    _ => false,
                };
                if carries {
                    carriers.insert(assign.0.local);
                }
            }
            if let Some(terminator) = &data.terminator
                && let TerminatorKind::Call {
                    args, destination, ..
                } = &terminator.kind
                && args.iter().any(|argument| reads(&argument.node, &carriers))
            {
                carriers.insert(destination.local);
            }
        }
        if carriers.len() == before {
            break;
        }
    }
    let mut found = Vec::new();
    for data in body.basic_blocks.iter() {
        let Some(terminator) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            continue;
        };
        for (index, argument) in args.iter().enumerate() {
            if !reads(&argument.node, &carriers) {
                continue;
            }
            let callee = func
                .const_fn_def()
                .and_then(|(callee, _)| callee.as_local())?;
            found.push(*formal_of.get(&(callee, index))?);
        }
    }
    (!found.is_empty()).then_some(found)
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

/// Filter 2: the retention tier wrote a retention disposition (the tier-2 waiver,
/// positive retention, an unconfirmed waiver) at a site passing the subject's own value
/// (`bare-local`, `cast-of-local`; a pointer loaded through the subject is another value:
/// the stand-in review's HIGH-3). A bridge's feasibility block is no retention reading.
fn tier_decides(raw_boundary: &RawBoundaryDispositionIndex, node: (LocalDefId, HirId)) -> bool {
    raw_boundary
        .inventoried_sites()
        .filter(|(_, _, site)| {
            site.node == Some(node) && matches!(site.source_shape, "bare-local" | "cast-of-local")
        })
        .any(|(_, disposition, _)| match disposition {
            RawBoundaryDisposition::T2 { .. } => true,
            RawBoundaryDisposition::Blocked { reason, .. } => match reason {
                RawBoundaryBlockReason::PositiveRetention
                | RawBoundaryBlockReason::WaiverUnconfirmed => true,
                RawBoundaryBlockReason::SiteUnresolved
                | RawBoundaryBlockReason::SubjectUnrooted
                | RawBoundaryBlockReason::SubjectNotSafe
                | RawBoundaryBlockReason::SharedToMut
                | RawBoundaryBlockReason::OwnershipTransfer
                | RawBoundaryBlockReason::Depth2FatLayout
                | RawBoundaryBlockReason::Depth2StorageShape
                | RawBoundaryBlockReason::ContractInvalid
                | RawBoundaryBlockReason::TemplateUnavailable
                | RawBoundaryBlockReason::ReturnedChildPermission => false,
            },
            RawBoundaryDisposition::T1 { .. } | RawBoundaryDisposition::OwnedByOtherArm { .. } => {
                false
            }
        })
}

/// The subjects to hold on this table, each with its receipt.
pub(crate) fn holds(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    raw_boundary: &RawBoundaryDispositionIndex,
    check: &RetainedAccessCheck,
    lifetime: &LifetimeEligibility,
) -> Vec<((LocalDefId, HirId), DegradeReason)> {
    let delivered = Delivered::of(tcx, table);
    // Each candidate's holds left after filter 3's place readings.
    let mut candidates: Vec<((LocalDefId, HirId), Local, Vec<Hold>)> = Vec::new();
    for (subject, decision) in &table.entries {
        if !reference_family(decision) {
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        if tier_decides(raw_boundary, node) {
            continue;
        }
        let verdict = match subject.kind {
            SubjectKind::Param { .. } => check.formal(subject.fn_did, subject.local.as_usize()),
            SubjectKind::Local => check.local(subject.fn_did, subject.local),
        };
        // The mode of record holds by the evident shapes; an `Unknown` verdict (an
        // unmodelled kind) has no evident receipt and stands under P9, as the hook of
        // record read it.
        let holds = match verdict {
            Some(Verdict::Held(holds)) => holds,
            Some(Verdict::Clear | Verdict::Unknown) | None => continue,
        };
        let kept: Vec<_> = holds
            .iter()
            .filter(|hold| {
                !(hold.kind == HoldKind::DerivedStore
                    && match hold.dest {
                        StoreDest::Field(struct_index, field_index)
                        | StoreDest::ArrayInField(struct_index, field_index) => {
                            delivered.fields.contains(&(struct_index, field_index))
                        }
                        StoreDest::ArrayLocal(local) => {
                            hold.site.is_some_and(|(function, _, _)| {
                                delivered.array_locals.contains(&(function, local))
                            })
                        }
                        StoreDest::Other => hold.site.is_some_and(|site| {
                            store_through_borrow(tcx, site)
                                .is_some_and(|field| delivered.fields.contains(&field))
                                || store_into_output_slot(tcx, table, lifetime, node, site)
                        }),
                        // Read below, against the receiving formals' own outcome.
                        StoreDest::None | StoreDest::Callee => false,
                    })
            })
            .cloned()
            .collect();
        if !kept.is_empty() {
            candidates.push((node, subject.local, kept));
        }
    }
    // **A callee that keeps what it is passed** (154a §2.1: the callee formal's own
    // decision): the store is the callee's, so it is exempt where every in-program formal
    // the subject's value reaches is delivered and not held itself — its own stores are
    // then into delivered places. Read to a fixpoint from all held, so an exemption rests
    // only on formals shown not held; a value reaching a call no program formal receives
    // stays held.
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
    let receivers: FxHashMap<(LocalDefId, HirId), Option<Vec<(LocalDefId, HirId)>>> = candidates
        .iter()
        .filter(|(_, _, kept)| {
            kept.iter()
                .all(|hold| hold.kind == HoldKind::DerivedStore && hold.dest == StoreDest::Callee)
        })
        .map(|(node, local, _)| (*node, receiving_formals(tcx, node.0, *local, &formal_of)))
        .collect();
    let mut held: FxHashSet<(LocalDefId, HirId)> =
        candidates.iter().map(|(node, _, _)| *node).collect();
    loop {
        let released: Vec<_> = receivers
            .iter()
            .filter(|(node, formals)| {
                held.contains(*node)
                    && formals.as_ref().is_some_and(|formals| {
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
    for (node, _, kept) in candidates {
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
