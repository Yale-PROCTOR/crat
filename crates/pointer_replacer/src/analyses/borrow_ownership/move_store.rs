//! L01⁹ wall 4 (`CRAT_ERA5C_MOVE_STORE`): the model's half of the store-as-move
//! protocol. Design record `agents/plan/2026-09-25-avl-rotation-move-protocol.md`
//! §3, as era-5c 060a filed it.
//!
//! A store `(*C).f = move _t` **qualifies** in a round when (3.1) the field is
//! `Owning` in the round's model, its transfer is a move (2′'s `moved_transfer`),
//! and the store's destination post-store token owns in the round's model. A
//! qualifying store issues **no loan on a local that is not `Raw`** in the round's
//! model (3.2): its operand-pointee loan and its group loans on `Owning` / `Ref`
//! members are cleared from the invalidation matrix. A loan on a `Raw` member stays.
//! The model exports every use of the operand's copy closure after the store as a
//! [`MoveStoreObligation`] (3.3). A store whose row cannot be built does not qualify.

use std::{cell::RefCell, rc::Rc};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::SparseBitMatrix;
use rustc_middle::mir::{
    BasicBlock, Body, Local, Location, Mutability, Operand, Place, RETURN_PLACE, Rvalue,
    StatementKind, TerminatorKind,
};
use rustc_mir_dataflow::points::PointIndex;
use rustc_span::{Span, def_id::LocalDefId};

use super::{
    SlotKind,
    crate_slots::CrateSlots,
    licensing::{
        facts::Facts,
        field_support::{Site, StoredValue, moved_transfer},
        model_selection::Selection,
    },
    ownership_occurrence::{Availability, PathStep},
    slots::SlotOwner,
    solver::SlotRef,
};
use crate::{
    analyses::borrow::{BorrowSet, Borrower, Loan, ProvenanceOwner, StructFieldSlot},
    utils::rustc::RustProgram,
};

/// A field store whose transfer is a move (3.1 (ii)), with its destination's
/// post-store token. Construction 0 only, as 2′'s `MovedInput` requires.
#[derive(Clone, Debug)]
pub(crate) struct Candidate {
    pub(crate) site: Site,
    pub(crate) destination_def: u32,
}

/// Pair each field store with its one `linear` / `equal` transfer, as
/// `field_support`'s owned path does, and keep the moves.
pub(crate) fn candidates(facts: &Facts) -> Vec<Candidate> {
    if facts.constructions != 1 {
        return Vec::new();
    }
    let mut out = Vec::new();
    for store in &facts.field_support_inputs.stores {
        if !store.direct_projection {
            continue;
        }
        let StoredValue::Value(source) = &store.value else { continue };
        let site = &store.site;
        let scoped = |point: &super::ownership_evidence::Point| {
            point.construction == 0 && point.function.as_deref() == Some(site.function.as_str())
        };
        let transfers: Vec<_> = facts
            .equations
            .iter()
            .filter(|equation| scoped(&equation.point))
            .filter(|equation| {
                equation.point.block == Some(site.block)
                    && equation.point.statement == Some(site.statement)
                    && matches!(equation.operation.as_str(), "linear" | "equal")
                    && equation.validate().is_ok()
            })
            .filter_map(|equation| {
                let transfer = equation.transfer.as_ref()?;
                let (Availability::Present(destination), Availability::Present(rhs)) =
                    (&transfer.destination, &transfer.source)
                else {
                    return None;
                };
                if destination.local != site.place.local
                    || destination.projection != site.place.projection
                    || rhs.local != source.local
                    || rhs.projection != source.projection
                {
                    return None;
                }
                if !matches!(destination.path.last(), Some(PathStep::Field { structure, index, .. })
                    if format!("{structure}::field{index}@d0") == site.field_key)
                {
                    return None;
                }
                let head = |id, use_var, def_var| {
                    facts.consumes.iter().any(|consume| {
                        scoped(&consume.point)
                            && consume.ordinal == id
                            && matches!(&consume.projected, Availability::Present(window)
                                if window.use_start == use_var && window.def_start == def_var)
                    })
                };
                (head(
                    destination.consume,
                    transfer.destination_use,
                    transfer.destination_def,
                ) && head(rhs.consume, transfer.source_use, transfer.source_def))
                .then_some((equation, transfer))
            })
            .collect();
        let [(equation, transfer)] = transfers.as_slice() else { continue };
        if moved_transfer(&equation.operation, transfer.by_move) {
            out.push(Candidate {
                site: site.clone(),
                destination_def: transfer.destination_def,
            });
        }
    }
    out
}

/// `CRAT_E5C_W61_FAULT`: `no-export` records no obligation (M5); `raw-too`
/// removes the loans the carve-out keeps (`Raw` members and non-`Ref` derived
/// pointers) too (M7).
fn fault(name: &str) -> bool {
    std::env::var("CRAT_E5C_W61_FAULT").ok().as_deref() == Some(name)
}

/// One function's qualifying stores in the round, and its locals' depth-0 kinds.
#[derive(Clone, Debug, Default)]
pub(crate) struct FnRule {
    pub(crate) stores: FxHashMap<Location, StructFieldSlot>,
    /// Non-`Ref` pointers derived from a qualifying store's alias set: loans kept.
    pub(crate) kept: FxHashSet<Local>,
    pub(crate) kinds: FxHashMap<Local, SlotKind>,
}

impl FnRule {
    /// 3.2: a loan on a local that is not `Raw` in the round's model goes, unless
    /// the local is a non-`Ref` pointer derived from the stored value. A local
    /// without a depth-0 slot keeps its loan (conservative).
    fn removable(&self, local: Local) -> bool {
        if fault("raw-too") {
            return self.kinds.contains_key(&local);
        }
        !self.kept.contains(&local)
            && matches!(
                self.kinds.get(&local),
                Some(SlotKind::Owning | SlotKind::Ref)
            )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum UseKind {
    ReadDeref,
    WriteDeref,
    LoadField,
    BorrowArg,
    RawArg,
    OwnArg,
    Return,
    Store,
    Copy,
}

impl UseKind {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            UseKind::ReadDeref => "read-deref",
            UseKind::WriteDeref => "write-deref",
            UseKind::LoadField => "load-field",
            UseKind::BorrowArg => "borrow-arg",
            UseKind::RawArg => "raw-arg",
            UseKind::OwnArg => "own-arg",
            UseKind::Return => "return",
            UseKind::Store => "store",
            UseKind::Copy => "copy",
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct ObligationUse {
    pub(crate) location: Location,
    pub(crate) span: Span,
    pub(crate) local: Local,
    pub(crate) kind: UseKind,
    pub(crate) dominated: bool,
}

/// 3.3: one row per qualifying store.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct MoveStoreObligation {
    pub(crate) function: LocalDefId,
    pub(crate) store: Location,
    pub(crate) span: Span,
    pub(crate) container: Local,
    pub(crate) field: StructFieldSlot,
    pub(crate) alias: Vec<Local>,
    pub(crate) uses: Vec<ObligationUse>,
    /// Non-`Ref` pointers derived from the alias set: their loans stay (3.2).
    pub(crate) kept: Vec<Local>,
    /// Their uses after S (`loan=kept`); none is an obligation.
    pub(crate) kept_uses: Vec<ObligationUse>,
    /// R577-5: the members whose loans this store cleared, with their round
    /// kinds, as the replay's last pass removed them (`clear_removed`), so the
    /// rewriter can check each one's emitted form.
    pub(crate) cleared: Vec<(Local, SlotKind)>,
}

/// A loan the arm cleared, for the witnesses and `CRAT_ERA5C_DEBUG`.
#[derive(Clone, Debug)]
pub(crate) struct Removed {
    pub(crate) location: Location,
    pub(crate) borrowed: Local,
    pub(crate) kind: Option<SlotKind>,
    pub(crate) was_invalid: bool,
}

#[derive(Default)]
struct Record {
    removed: FxHashMap<LocalDefId, Vec<Removed>>,
    obligations: Vec<MoveStoreObligation>,
}

thread_local! {
    static CURRENT: RefCell<Option<Rc<FxHashMap<LocalDefId, FnRule>>>> = const { RefCell::new(None) };
    static RECORD: RefCell<Record> = RefCell::new(Record::default());
}

pub(crate) struct Scope(Option<Rc<FxHashMap<LocalDefId, FnRule>>>);
impl Drop for Scope {
    fn drop(&mut self) {
        CURRENT.with(|current| *current.borrow_mut() = self.0.take());
    }
}

/// The last round's cleared loans and obligations (the accepted round's, on an accept).
pub(crate) fn last_round() -> (
    FxHashMap<LocalDefId, Vec<Removed>>,
    Vec<MoveStoreObligation>,
) {
    RECORD.with(|record| {
        let record = record.borrow();
        (record.removed.clone(), record.obligations.clone())
    })
}

/// Compute this round's qualifying stores from the round's model and its own
/// values, record their obligations, and install the rule for the replay.
pub(crate) fn enter_round(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    facts: Option<Rc<Facts>>,
    selection: Option<Rc<Selection>>,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> Scope {
    RECORD.with(|record| *record.borrow_mut() = Record::default());
    let rule = match (facts, selection) {
        (Some(facts), Some(selection)) => build(program, slots, &facts, &selection, model),
        _ => FxHashMap::default(),
    };
    Scope(CURRENT.with(|current| current.replace(Some(Rc::new(rule)))))
}

fn build(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    facts: &Rc<Facts>,
    selection: &Selection,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> FxHashMap<LocalDefId, FnRule> {
    let tcx = program.tcx;
    let debug = std::env::var_os("CRAT_ERA5C_DEBUG").is_some();
    let names: FxHashMap<String, LocalDefId> = program
        .functions
        .iter()
        .map(|&f| (tcx.def_path_str(f), f))
        .collect();
    let kind_of = |function: LocalDefId, local: Local| {
        slots
            .fn_local_slots
            .get(&function)
            .and_then(|u| u.slot_for_local_depth(local, 0))
            .and_then(|id| model.get(&SlotRef::Local(function, id)).copied())
    };
    let mut rule: FxHashMap<LocalDefId, FnRule> = FxHashMap::default();
    let mut obligations = Vec::new();
    for candidate in candidates(facts) {
        let Some(&function) = names.get(&candidate.site.function) else { continue };
        let Some(&SlotRef::Field(sid)) = facts.slot_refs.get(&candidate.site.field_key) else {
            continue;
        };
        if model.get(&SlotRef::Field(sid)) != Some(&SlotKind::Owning) {
            continue;
        }
        if selection.move_store_own(facts, candidate.destination_def) != Some(true) {
            continue;
        }
        let SlotOwner::Field(owner) = slots.field_slots.slot(sid).owner else { continue };
        let field = StructFieldSlot {
            struct_did: owner.struct_did,
            field_index: owner.field_index,
        };
        let store = Location {
            block: BasicBlock::from_u32(candidate.site.block),
            statement_index: candidate.site.statement,
        };
        let body = &*tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let Some((row, kept)) = obligation(program, slots, model, function, body, store, field)
        else {
            continue;
        };
        if debug {
            eprintln!(
                "E5C move-store qualify fn={} at={store:?} field={field:?} alias={:?} kept={kept:?} uses={}",
                candidate.site.function,
                row.alias,
                row.uses.len()
            );
            for u in &row.uses {
                eprintln!(
                    "E5C move-store obligation fn={} store={store:?} use={:?} local={:?} kind={} dominated={}",
                    candidate.site.function,
                    u.location,
                    u.local,
                    u.kind.as_str(),
                    u.dominated
                );
            }
        }
        let entry = rule.entry(function).or_insert_with(|| FnRule {
            stores: FxHashMap::default(),
            kept: FxHashSet::default(),
            kinds: body
                .local_decls
                .indices()
                .filter_map(|local| kind_of(function, local).map(|kind| (local, kind)))
                .collect(),
        });
        entry.stores.insert(store, field);
        entry.kept.extend(kept);
        if !fault("no-export") {
            obligations.push(row);
        }
    }
    super::export::record_move_store_obligations(&obligations);
    RECORD.with(|record| record.borrow_mut().obligations = obligations);
    rule
}

/// 3.3's row: the operand's copy closure (plus the `Ref` pointers derived from a
/// member), and every use of a member on a path from the store before that member
/// is redefined; with it, the non-`Ref` derived pointers whose loans stay (3.2).
/// `None` when the store is not `C.f = move/copy _t`.
fn obligation<'tcx>(
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    function: LocalDefId,
    body: &Body<'tcx>,
    store: Location,
    field: StructFieldSlot,
) -> Option<(MoveStoreObligation, FxHashSet<Local>)> {
    let data = body.basic_blocks.get(store.block)?;
    let statement = data.statements.get(store.statement_index)?;
    let StatementKind::Assign(box (destination, Rvalue::Use(operand))) = &statement.kind else {
        return None;
    };
    let (Operand::Move(operand) | Operand::Copy(operand)) = operand else { return None };
    if !operand.projection.is_empty() || destination.projection.is_empty() {
        return None;
    }
    let bare = |place: &Place<'_>| place.projection.is_empty().then_some(place.local);
    // The copy graph: `a = copy/move b` and casts of a bare local.
    let mut edges: FxHashMap<Local, Vec<Local>> = FxHashMap::default();
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else { continue };
            let Some(lhs) = bare(lhs) else { continue };
            let (Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs))
            | Rvalue::Cast(_, Operand::Copy(rhs) | Operand::Move(rhs), _)) = rvalue
            else {
                continue;
            };
            let Some(rhs) = bare(rhs) else { continue };
            edges.entry(lhs).or_default().push(rhs);
            edges.entry(rhs).or_default().push(lhs);
        }
    }
    let mut alias: FxHashSet<Local> = FxHashSet::default();
    let mut stack = vec![operand.local];
    while let Some(local) = stack.pop() {
        if alias.insert(local) {
            stack.extend(edges.get(&local).into_iter().flatten().copied());
        }
    }
    // Pointers derived from a member by anything but a plain copy (a field address
    // `&raw mut (*a).g`, a pointer-returning call on a member) may point into A's
    // object. A `Ref` one is exported (3.3); any other keeps its loan (3.2), whatever
    // its kind: the rewriter cannot deliver an `Owning` field address as a `Box`.
    let kind_of = |f: LocalDefId, local: Local| {
        slots
            .fn_local_slots
            .get(&f)
            .and_then(|u| u.slot_for_local_depth(local, 0))
            .and_then(|id| model.get(&SlotRef::Local(f, id)).copied())
    };
    let mut derived: FxHashSet<Local> = FxHashSet::default();
    loop {
        let source = |local: Local| alias.contains(&local) || derived.contains(&local);
        let mut hits = Vec::new();
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else { continue };
                let Some(lhs) = bare(lhs) else { continue };
                let hit = match rvalue {
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        source(place.local) && place.is_indirect()
                    }
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                    | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
                        place.projection.is_empty() && derived.contains(&place.local)
                    }
                    _ => false,
                };
                if hit {
                    hits.push(lhs);
                }
            }
            if let TerminatorKind::Call {
                args, destination, ..
            } = &block.terminator().kind
                && let Some(lhs) = bare(destination)
                && body.local_decls[lhs].ty.is_any_ptr()
                && args.iter().any(|arg| {
                    arg.node
                        .place()
                        .is_some_and(|p| p.projection.is_empty() && source(p.local))
                })
            {
                hits.push(lhs);
            }
        }
        let before = derived.len();
        derived.extend(hits.into_iter().filter(|local| !alias.contains(local)));
        if derived.len() == before {
            break;
        }
    }
    let mut kept = FxHashSet::default();
    for local in derived {
        if kind_of(function, local) == Some(SlotKind::Ref) {
            alias.insert(local);
        } else {
            kept.insert(local);
        }
    }
    let dominators = body.basic_blocks.dominators();
    let dominated = |location: Location| {
        if location.block == store.block {
            location.statement_index > store.statement_index
        } else {
            dominators.dominates(store.block, location.block)
        }
    };
    let successors = |location: Location| -> Vec<Location> {
        let block = &body.basic_blocks[location.block];
        if location.statement_index < block.statements.len() {
            vec![location.successor_within_block()]
        } else {
            block
                .terminator()
                .successors()
                .map(|b| Location {
                    block: b,
                    statement_index: 0,
                })
                .collect()
        }
    };
    let walk = |set: &FxHashSet<Local>| -> (Vec<Local>, Vec<ObligationUse>) {
        let mut members: Vec<Local> = set.iter().copied().collect();
        members.sort();
        let mut uses = Vec::new();
        for &member in &members {
            let mut seen: FxHashSet<Location> = FxHashSet::default();
            let mut work = successors(store);
            while let Some(location) = work.pop() {
                if !seen.insert(location) {
                    continue;
                }
                let (kinds, redefines) = uses_at(program, slots, model, body, location, member);
                for kind in kinds {
                    uses.push(ObligationUse {
                        location,
                        span: body.source_info(location).span,
                        local: member,
                        kind,
                        dominated: dominated(location),
                    });
                }
                if !redefines {
                    work.extend(successors(location));
                }
            }
        }
        uses.sort_by_key(|u| (u.location, u.local));
        (members, uses)
    };
    let (members, uses) = walk(&alias);
    // ownership-fields 069 (4.2a): the kept members' uses after S, marked
    // `loan=kept`, for the rewriter's consistency guard.
    let (kept_members, kept_uses) = walk(&kept);
    Some((
        MoveStoreObligation {
            function,
            store,
            span: statement.source_info.span,
            container: destination.local,
            field,
            alias: members,
            uses,
            kept: kept_members,
            kept_uses,
            cleared: Vec::new(),
        },
        kept,
    ))
}

/// The uses of `member` at `location`, and whether it redefines `member` whole.
fn uses_at<'tcx>(
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    body: &Body<'tcx>,
    location: Location,
    member: Local,
) -> (Vec<UseKind>, bool) {
    let through = |place: &Place<'_>| place.local == member && place.is_indirect();
    let is_member = |place: &Place<'_>| place.local == member && place.projection.is_empty();
    let block = &body.basic_blocks[location.block];
    let mut kinds = Vec::new();
    if let Some(statement) = block.statements.get(location.statement_index) {
        let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
            return (kinds, false);
        };
        if through(lhs) {
            kinds.push(UseKind::WriteDeref);
        }
        let read = |place: &Place<'tcx>, kinds: &mut Vec<UseKind>| {
            if is_member(place) {
                kinds.push(if lhs.local == RETURN_PLACE && lhs.projection.is_empty() {
                    UseKind::Return
                } else if !lhs.projection.is_empty() {
                    UseKind::Store
                } else {
                    UseKind::Copy
                });
            } else if through(place) {
                kinds.push(if place.ty(body, program.tcx).ty.is_raw_ptr() {
                    UseKind::LoadField
                } else {
                    UseKind::ReadDeref
                });
            }
        };
        match rvalue {
            Rvalue::Use(operand)
            | Rvalue::Repeat(operand, _)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::UnaryOp(_, operand) => {
                if let Some(place) = operand.place() {
                    read(&place, &mut kinds);
                }
            }
            Rvalue::BinaryOp(_, box (a, b)) => {
                for operand in [a, b] {
                    if let Some(place) = operand.place() {
                        read(&place, &mut kinds);
                    }
                }
            }
            Rvalue::Aggregate(_, operands) => {
                for operand in operands {
                    if let Some(place) = operand.place() {
                        read(&place, &mut kinds);
                    }
                }
            }
            Rvalue::CopyForDeref(place) => read(place, &mut kinds),
            Rvalue::Ref(_, kind, place) if through(place) => {
                kinds.push(if kind.to_mutbl_lossy() == Mutability::Mut {
                    UseKind::WriteDeref
                } else {
                    UseKind::ReadDeref
                })
            }
            Rvalue::RawPtr(kind, place) if through(place) => {
                kinds.push(if kind.to_mutbl_lossy() == Mutability::Mut {
                    UseKind::WriteDeref
                } else {
                    UseKind::ReadDeref
                })
            }
            _ => {}
        }
        let redefines = lhs.local == member && lhs.projection.is_empty();
        return (kinds, redefines);
    }
    match &block.terminator().kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            let callee = func
                .const_fn_def()
                .and_then(|(def, _)| def.as_local())
                .filter(|def| slots.fn_local_slots.contains_key(def));
            for (index, arg) in args.iter().enumerate() {
                let Some(place) = arg.node.place() else { continue };
                if is_member(&place) {
                    let formal = callee.and_then(|callee| {
                        slots
                            .fn_local_slots
                            .get(&callee)
                            .and_then(|u| u.slot_for_local_depth(Local::from_usize(index + 1), 0))
                            .and_then(|id| model.get(&SlotRef::Local(callee, id)).copied())
                    });
                    kinds.push(match formal {
                        Some(SlotKind::Ref) => UseKind::BorrowArg,
                        Some(SlotKind::Owning) => UseKind::OwnArg,
                        _ => UseKind::RawArg,
                    });
                } else if through(&place) {
                    kinds.push(UseKind::LoadField);
                }
            }
            if through(destination) {
                kinds.push(UseKind::WriteDeref);
            }
            let redefines = destination.local == member && destination.projection.is_empty();
            (kinds, redefines)
        }
        TerminatorKind::Return if member == RETURN_PLACE => (vec![UseKind::Return], false),
        TerminatorKind::SwitchInt { discr, .. } => {
            if discr.place().is_some_and(|p| is_member(&p)) {
                kinds.push(UseKind::Copy);
            }
            (kinds, false)
        }
        _ => (kinds, false),
    }
}

/// 3.2 at the replay: clear the round's removable loans from `invalidates` for
/// `function`, so they are never invalid (no demotion, no edge).
pub(crate) fn clear_removed(
    function: LocalDefId,
    borrow_set: &BorrowSet<'_>,
    loan_liveness: &SparseBitMatrix<PointIndex, Loan>,
    invalidates: &mut SparseBitMatrix<PointIndex, Loan>,
) {
    let Some(rule) = CURRENT.with(|current| {
        current
            .borrow()
            .as_ref()
            .and_then(|rule| rule.get(&function).cloned())
    }) else {
        return;
    };
    let rows: Vec<PointIndex> = invalidates.rows().collect();
    let mut removed = Vec::new();
    for (loan, data) in borrow_set.loans.iter_enumerated() {
        let Borrower::Assign(ProvenanceOwner::Field(field)) = data.assigned else { continue };
        if rule.stores.get(&data.location()) != Some(&field) {
            continue;
        }
        let borrowed = data.borrowed.local;
        if !rule.removable(borrowed) {
            continue;
        }
        let mut was_invalid = false;
        for &row in &rows {
            if invalidates.contains(row, loan) {
                was_invalid |= loan_liveness.contains(row, loan);
                invalidates.remove(row, loan);
            }
        }
        removed.push(Removed {
            location: data.location(),
            borrowed,
            kind: rule.kinds.get(&borrowed).copied(),
            was_invalid,
        });
    }
    if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
        for r in &removed {
            eprintln!(
                "E5C move-store removed fn={function:?} at={:?} borrowed={:?} kind={:?} was_invalid={}",
                r.location, r.borrowed, r.kind, r.was_invalid
            );
        }
    }
    RECORD.with(|record| {
        let mut record = record.borrow_mut();
        // R577-5: each of this function's rows carries the members its store
        // cleared in this (latest) replay pass.
        let mut changed = false;
        for row in record
            .obligations
            .iter_mut()
            .filter(|row| row.function == function)
        {
            let mut cleared: Vec<(Local, SlotKind)> = removed
                .iter()
                .filter(|r| r.location == row.store)
                .filter_map(|r| r.kind.map(|kind| (r.borrowed, kind)))
                .collect();
            cleared.sort_by_key(|(local, _)| local.as_u32());
            cleared.dedup_by_key(|(local, _)| *local);
            if row.cleared != cleared {
                row.cleared = cleared;
                changed = true;
            }
        }
        record.removed.insert(function, removed);
        if changed {
            super::export::record_move_store_obligations(&record.obligations);
        }
    });
}

/// The round's store candidates' destination tokens, for `Selection::from_model`.
pub(crate) fn destination_vars(facts: &Facts) -> Vec<u32> {
    candidates(facts)
        .into_iter()
        .map(|candidate| candidate.destination_def)
        .collect()
}
