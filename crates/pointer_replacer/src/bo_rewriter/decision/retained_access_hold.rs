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
//!    waiver where a bridge renders, positive retention, an unconfirmed waiver) at a site
//!    passing the subject's own value, the tier's disposition stands for the retention
//!    that site reads, and only for it: a store the check derives at that foreign call,
//!    and a callee's store where every in-program callee the subject is handed to reads
//!    so. Never a self-reference, a cycle or the subject's own store into memory (R878-1;
//!    the stand-in review's round 2, R2-1);
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
use rustc_span::Span;

use super::{
    Decision, DecisionTable, DegradeReason, SubjectKind,
    lifetime::LifetimeEligibility,
    raw_boundary::{
        RAW_BOUNDARY_WAIVER_ID, RawBoundaryBlockReason, RawBoundaryDisposition,
        RawBoundaryDispositionIndex, RawBoundaryRenderSite,
    },
    retained_access::{AccessKind, Hold, HoldKind, RetainedAccessCheck, Shape, StoreDest, Verdict},
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

/// A raw pointer's own arithmetic and queries (`core::ptr`'s inherent methods that
/// neither store their arguments nor write through them): no program formal receives
/// the value there and nothing keeps it; the result is carried (the stand-in review's
/// round 2, R2-4).
fn pointer_arithmetic(tcx: TyCtxt<'_>, callee: rustc_hir::def_id::DefId) -> bool {
    // An inherent method of a raw pointer (only `core` defines those, by coherence).
    tcx.impl_of_method(callee).is_some_and(|parent| {
        tcx.trait_id_of_impl(parent).is_none()
            && tcx.type_of(parent).instantiate_identity().is_raw_ptr()
    }) && matches!(
        tcx.item_name(callee).as_str(),
        "is_null"
            | "offset"
            | "wrapping_offset"
            | "add"
            | "sub"
            | "wrapping_add"
            | "wrapping_sub"
            | "byte_offset"
            | "byte_add"
            | "byte_sub"
            | "offset_from"
            | "cast"
            | "cast_mut"
            | "cast_const"
            | "addr"
            | "is_aligned"
    )
}

/// A local that may hold the subject's value: a pointer, an integer (an address made an
/// integer, and what arithmetic makes of it: the check's family carries it, the stand-in
/// review's round 3, R3-4), or anything but a scalar; not a comparison's `bool`. A call's
/// result carries it only as a pointer or an aggregate (R2-4).
fn may_carry(ty: rustc_middle::ty::Ty<'_>, at_call: bool) -> bool {
    ty.is_any_ptr() || !ty.is_scalar() || (!at_call && ty.is_integral())
}

/// Whether an operand reads a carrier's own value (a value loaded through a carrier is
/// another value, R2-4).
fn reads(operand: &Operand<'_>, carriers: &FxHashSet<Local>) -> bool {
    operand.place().is_some_and(|place| {
        carriers.contains(&place.local)
            && !place
                .projection
                .iter()
                .any(|elem| matches!(elem, ProjectionElem::Deref))
    })
}

/// The locals of `body` that carry the value of `local`, read from MIR (the stand-in
/// review's MED-1: copies, casts, borrows, aggregates and call results).
fn carriers(body: &Body<'_>, local: Local) -> FxHashSet<Local> {
    let mut carriers: FxHashSet<Local> = FxHashSet::default();
    carriers.insert(local);
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
                    | Rvalue::Repeat(operand, _)
                    | Rvalue::UnaryOp(_, operand) => reads(operand, &carriers),
                    // A borrow into a carrier's referent points into the subject's object.
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        carriers.contains(&place.local)
                    }
                    Rvalue::CopyForDeref(place) => reads(&Operand::Copy(*place), &carriers),
                    Rvalue::Aggregate(_, operands) => {
                        operands.iter().any(|operand| reads(operand, &carriers))
                    }
                    Rvalue::BinaryOp(_, operands) => {
                        reads(&operands.0, &carriers) || reads(&operands.1, &carriers)
                    }
                    _ => false,
                };
                if carries && may_carry(body.local_decls[assign.0.local].ty, false) {
                    carriers.insert(assign.0.local);
                }
            }
            if let Some(terminator) = &data.terminator
                && let TerminatorKind::Call {
                    args, destination, ..
                } = &terminator.kind
                && args.iter().any(|argument| reads(&argument.node, &carriers))
                && may_carry(body.local_decls[destination.local].ty, true)
            {
                carriers.insert(destination.local);
            }
        }
        if carriers.len() == before {
            break;
        }
    }
    carriers
}

/// One call a carrier reaches: its span, its callee (`None` through a pointer), whether
/// it may enter a program function (a direct call to one, or any call through a
/// pointer), and the argument positions carrying the value; a raw pointer's own
/// arithmetic is no such call.
struct CarriedCall {
    span: Span,
    callee: Option<rustc_hir::def_id::DefId>,
    in_program: bool,
    arguments: Vec<usize>,
}

fn carried_calls(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    carriers: &FxHashSet<Local>,
) -> Vec<CarriedCall> {
    let mut calls = Vec::new();
    for data in body.basic_blocks.iter() {
        let Some(terminator) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            continue;
        };
        let callee = func.const_fn_def().map(|(callee, _)| callee);
        if callee
            .is_some_and(|callee| callee.as_local().is_none() && pointer_arithmetic(tcx, callee))
        {
            continue;
        }
        let arguments: Vec<usize> = args
            .iter()
            .enumerate()
            .filter(|(_, argument)| reads(&argument.node, carriers))
            .map(|(index, _)| index)
            .collect();
        if !arguments.is_empty() {
            calls.push(CarriedCall {
                span: terminator.source_info.span,
                callee,
                in_program: callee.is_none_or(|callee| {
                    callee.as_local().is_some() && !tcx.is_foreign_item(callee)
                }),
                arguments,
            });
        }
    }
    calls
}

/// The in-program formals a subject's value reaches at calls of its own function:
/// `None` where a carrier reaches a call no program formal receives (a foreign callee, an
/// aggregate argument, a position that is no subject), but a raw pointer's own
/// arithmetic.
fn receiving_formals(
    calls: &[CarriedCall],
    formal_of: &FxHashMap<(LocalDefId, usize), (LocalDefId, HirId)>,
) -> Option<Vec<(LocalDefId, HirId)>> {
    let mut found = Vec::new();
    for call in calls {
        let callee = call.callee?.as_local()?;
        for index in &call.arguments {
            found.push(*formal_of.get(&(callee, *index))?);
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

/// Filter 2's reading of one site: a retention disposition (the tier-2 waiver, positive
/// retention, an unconfirmed waiver) where a bridge renders (R878-1 (B): "at sites passing
/// the subject's bridge"; the stand-in review's R2-2, R3-2: a block at a converting target
/// renders nothing and degrades nothing), at a site passing the subject's own value
/// (`bare-local`, `cast-of-local`; a pointer loaded through the subject is another value:
/// HIGH-3). A bridge's feasibility block is no retention reading.
fn reads_retention(disposition: &RawBoundaryDisposition, site: &RawBoundaryRenderSite) -> bool {
    site.target_stays_raw
        && matches!(site.source_shape, "bare-local" | "cast-of-local")
        && match disposition {
            // R889-1 (relay 307; the review's round 4, R4-2): only the c-aliasing waiver
            // excludes an execution that "retains and later uses" the alias; the tier-2
            // retention waiver (R481-2) excludes a use while the reference is live only,
            // and reads no retention here.
            RawBoundaryDisposition::T2 { waiver_id, .. } => *waiver_id == RAW_BOUNDARY_WAIVER_ID,
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
        }
}

/// Filter 2: the (call, argument) positions at which the tier read the subject's
/// retention at its own sites.
fn tier_reading(
    raw_boundary: &RawBoundaryDispositionIndex,
    node: (LocalDefId, HirId),
) -> FxHashSet<(Span, usize)> {
    raw_boundary
        .inventoried_sites()
        .filter(|(_, disposition, site)| {
            site.node == Some(node) && reads_retention(disposition, site)
        })
        .map(|(key, _, site)| (site.call_span, key.argument_index))
        .collect()
}

/// The span of the call a hold is sited at (the check derives a foreign call's keeping
/// as a store at the call).
fn call_at(tcx: TyCtxt<'_>, (function, block, statement): (u32, u32, usize)) -> Option<Span> {
    let body = tcx
        .mir_drops_elaborated_and_const_checked(local_def(function))
        .borrow();
    let data = body.basic_blocks.get(BasicBlock::from_u32(block))?;
    if statement < data.statements.len() {
        return None;
    }
    let terminator = data.terminator.as_ref()?;
    matches!(terminator.kind, TerminatorKind::Call { .. }).then_some(terminator.source_info.span)
}

/// Filter 2, per hold (the stand-in review's round 2, R2-1; round 3, R3-1): the tier's
/// reading stands for the retention it reads, at the call and the argument it reads it —
/// a store the check derives at a call, where every argument carrying the subject there is
/// such a reading; a callee's store, at its call when the check sites it, else at every
/// call the subject's value reaches that may enter a program function (the check's
/// callee store reads program formals only; a foreign callee's keeping is its own hold at
/// that call). Never a self-reference or a cycle (an access hold), never the subject's own
/// store into memory.
fn tier_stands(
    tcx: TyCtxt<'_>,
    reading: &FxHashSet<(Span, usize)>,
    calls: &[CarriedCall],
    hold: &Hold,
) -> bool {
    let covered = |span: Span| {
        let mut at = calls.iter().filter(|call| call.span == span).peekable();
        at.peek().is_some()
            && at.all(|call| {
                call.arguments
                    .iter()
                    .all(|index| reading.contains(&(span, *index)))
            })
    };
    hold.kind == HoldKind::DerivedStore
        && match (hold.dest, hold.site) {
            (StoreDest::Callee, None) => {
                let mut program = calls.iter().filter(|call| call.in_program).peekable();
                program.peek().is_some() && program.all(|call| covered(call.span))
            }
            (_, Some(site)) => call_at(tcx, site).is_some_and(covered),
            (
                StoreDest::None
                | StoreDest::Field(..)
                | StoreDest::ArrayInField(..)
                | StoreDest::ArrayLocal(_)
                | StoreDest::Other,
                None,
            ) => false,
        }
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
    // Each candidate's holds left after filter 3's place readings, whether it is a
    // formal, and the calls its value reaches.
    let mut candidates: Vec<((LocalDefId, HirId), bool, Vec<CarriedCall>, Vec<Hold>)> = Vec::new();
    // The subjects a hold of which the tier's reading stands for (at their own bridged
    // sites).
    let mut waived: FxHashSet<(LocalDefId, HirId)> = FxHashSet::default();
    for (subject, decision) in &table.entries {
        if !reference_family(decision) {
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        let verdict = match subject.kind {
            SubjectKind::Param { .. } => check.formal(subject.fn_did, subject.local.as_usize()),
            SubjectKind::Local => check.local(subject.fn_did, subject.local),
        };
        // era-5c 158a (relay 305): the check's own guard on the applied field transactions
        // first — a hold through a field this table delivers goes — then the three filters.
        // The mode of record holds by the evident shapes; an `Unknown` verdict (an
        // unmodelled kind) has no evident receipt and stands under P9, as the hook of
        // record read it.
        let Some(verdict) = verdict else {
            continue;
        };
        let holds = match check.after_deliveries(verdict, &|struct_index, field_index| {
            delivered.fields.contains(&(struct_index, field_index))
        }) {
            Verdict::Held(holds) => holds,
            Verdict::Clear | Verdict::Unknown => continue,
        };
        let reading = tier_reading(raw_boundary, node);
        let calls = {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(subject.fn_did)
                .borrow();
            carried_calls(tcx, &body, &carriers(&body, subject.local))
        };
        // The stand-in review's round 4, R4-1: the check emits a formal's callee store (its
        // H6 (c)) only where the formal stores nothing itself. Where it does, and its value
        // reaches a call that may enter a program function, the callee store is read here
        // as the check would emit it, unsited; the coverage below and the release judge it.
        let mut holds = holds;
        if matches!(subject.kind, SubjectKind::Param { .. })
            && holds
                .iter()
                .any(|hold| hold.kind == HoldKind::DerivedStore && hold.dest != StoreDest::Callee)
            && !holds
                .iter()
                .any(|hold| hold.dest == StoreDest::Callee && hold.site.is_none())
            && calls.iter().any(|call| call.in_program)
        {
            holds.push(Hold {
                kind: HoldKind::DerivedStore,
                access: AccessKind::Write,
                shape: Shape::Other,
                retaining_place: "callee-store".to_owned(),
                witness: format!(
                    "{} | callee-store | beside its own store",
                    tcx.def_path_str(subject.fn_did.to_def_id())
                ),
                dest: StoreDest::Callee,
                site: None,
                via: None,
            });
        }
        if holds
            .iter()
            .any(|hold| tier_stands(tcx, &reading, &calls, hold))
        {
            waived.insert(node);
        }
        let kept: Vec<_> = holds
            .iter()
            .filter(|hold| !tier_stands(tcx, &reading, &calls, hold))
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
            let formal = matches!(subject.kind, SubjectKind::Param { .. });
            candidates.push((node, formal, calls, kept));
        }
    }
    // **A callee that keeps what it is passed** (154a §2.1: the callee formal's own
    // decision): the store is the callee's, so it is exempt where every in-program formal
    // the subject's value reaches is delivered and not held itself — its own stores are
    // then into delivered places. Read to a fixpoint from all held, so an exemption rests
    // only on formals shown not held; a value reaching a call no program formal receives
    // stays held. A receiver whose holds the tier reads at its own bridged site is not held
    // for a local's release (the kept pointer is derived from the receiver's own
    // reference, and that site's receipt names it), but it is for a formal's: a formal is
    // protected for its call, and what the receiver's callee keeps may be freed before the
    // formal's call returns (the stand-in review's round 3, R3-2).
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
    let receivers: FxHashMap<(LocalDefId, HirId), (bool, Option<Vec<(LocalDefId, HirId)>>)> =
        candidates
            .iter()
            .filter(|(_, _, _, kept)| {
                kept.iter().all(|hold| {
                    hold.kind == HoldKind::DerivedStore && hold.dest == StoreDest::Callee
                })
            })
            .map(|(node, formal, calls, _)| {
                (*node, (*formal, receiving_formals(calls, &formal_of)))
            })
            .collect();
    let mut held: FxHashSet<(LocalDefId, HirId)> =
        candidates.iter().map(|(node, _, _, _)| *node).collect();
    loop {
        let released: Vec<_> = receivers
            .iter()
            .filter(|(node, (is_formal, formals))| {
                held.contains(*node)
                    && formals.as_ref().is_some_and(|formals| {
                        formals.iter().all(|formal| {
                            !held.contains(formal)
                                && !(*is_formal && waived.contains(formal))
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
    for (node, _, _, kept) in candidates {
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
