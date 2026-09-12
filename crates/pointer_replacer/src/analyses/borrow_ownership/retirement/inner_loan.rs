//! R343-1 P1S-INNER-LOAN-REPRESENTATION: a BO-owned loan for a holder at depth >= 1.
//!
//! A native loan can never name an inner holder. The native arm consumes three
//! things -- `loan_liveness.row(point)`, the borrowed object resolved AT
//! RESERVATION, and `owners_at(loan, point)` -- and owner resolution runs through
//! maps that are populated only at depth 0, while `ProvenanceOwner` carries no
//! depth at all. So for a non-parameter Ref at depth >= 1 the analysis cannot ask
//! "is this holder's loan live here?", and answers "possibly" by demoting the
//! holder together with its whole copy closure.
//!
//! `protected_entry` already solves the same problem for parameters by supplying
//! the absent loan as a BO-owned obligation. This module is its sibling for the
//! non-parameter inner holders, with one fact the entry machinery does not need:
//! an actual liveness, because an entry is live at every event in its frame and
//! an inner holder is not.
//!
//! Field-owned inner holders get NO obligation here. That is deliberate: the
//! field object identity is row (b)'s material, it is out of this build by
//! R342-4, and a holder without an obligation keeps today's demotion.

use rustc_hash::FxHashSet;
use rustc_index::IndexVec;
use rustc_middle::mir::{
    BasicBlock, Body, Local, Location, Operand, ProjectionElem, RETURN_PLACE, Rvalue,
    StatementKind, TerminatorKind,
};
use rustc_span::def_id::LocalDefId;

use super::{
    super::{crate_slots::CrateSlots, slots::SlotOwner, solver::SlotRef},
    call_reach::EscapeFacts,
};
use crate::utils::rustc::RustProgram;

/// One inner holder, named by its frame, its slot and its depth.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct InnerLoanKey {
    pub(crate) function: LocalDefId,
    pub(crate) local: Local,
    pub(crate) depth: u8,
    pub(crate) holder: SlotRef,
}

/// The BO-owned obligation. This is not a fabricated legacy loan, an empty-loan
/// certificate or a CallArg revival, exactly as `EntryRepresentation` says of the
/// entry obligation it is modelled on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct InnerLoan {
    pub(crate) key: InnerLoanKey,
    /// Every statement that defines this holder's value: an assignment to the
    /// owner local, or a store through a dereference of it. The object is
    /// resolved at these points, never through a later rebinding.
    pub(crate) reservations: Vec<Location>,
}

/// R343-1(i), sizing 2.6: the locals whose VALUE leaves this frame.
///
/// The liveness of an inner holder is computed over its copy closure, and the
/// copy graph is built from five ASSIGNMENT forms. Every way a value can leave
/// the frame goes through a terminator or a projected destination instead, so it
/// creates no copy-graph edge at all: an escaped value has an incomplete closure,
/// and "no closure member uses this loan after the event" would then be a
/// statement about the edges we built rather than about the program. A holder
/// that escapes is therefore `facts missing`, and `facts missing` keeps today's
/// demotion. Flow-insensitive and in the safe direction, exactly as
/// `EscapeFacts::of_body` is.
#[derive(Clone, Debug, Default)]
pub(crate) struct ValueEscapes {
    escaping: FxHashSet<Local>,
}

impl ValueEscapes {
    pub(crate) fn of_body(body: &Body<'_>) -> Self {
        let mut escaping = FxHashSet::default();
        // Form 5, already computed: the local's own storage address escaped, so a
        // callee can reach the cell itself.
        let address = EscapeFacts::of_body(body);
        for local in body.local_decls.indices() {
            if address.escapes(local) {
                escaping.insert(local);
            }
        }
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (destination, value)) = &statement.kind else {
                    continue;
                };
                // Form 2, and form 4 with it: a store through a dereference. A
                // store into a static has the same shape in MIR -- the static is a
                // constant pointer and the write goes through a Deref -- so the
                // one test covers both, rather than a second test that could drift
                // from it.
                let through_pointer = destination
                    .projection
                    .iter()
                    .any(|element| matches!(element, ProjectionElem::Deref));
                // Form 3: the value reaches the return place.
                let returned = destination.local == RETURN_PLACE;
                if through_pointer || returned {
                    read_locals(value, &mut escaping);
                }
            }
            let terminator = data.terminator();
            match &terminator.kind {
                // Form 1: a call argument, and the callee operand itself.
                TerminatorKind::Call { func, args, .. }
                | TerminatorKind::TailCall { func, args, .. } => {
                    for operand in args.iter().map(|argument| &argument.node).chain([func]) {
                        if let Some(place) = operand.place() {
                            escaping.insert(place.local);
                        }
                    }
                }
                // Drop glue is a call the frame does not write: the dropped place
                // reaches code this analysis does not see.
                TerminatorKind::Drop { place, .. } => {
                    escaping.insert(place.local);
                }
                _ => {}
            }
        }
        // MIR copies a value into a temporary before it leaves the frame:
        // `opaque(argument)` is `_5 = copy _3; opaque(move _5)`. A relation that
        // only named `_5` would say `argument` stays home, which is the opposite
        // of the truth, so the escape is propagated BACK along the copy edges the
        // frame actually has. These are the same five assignment forms the copy
        // graph follows, which is why this closure is exactly as wide as the
        // closure the liveness will be computed over -- no wider, no narrower.
        let edges = copy_edges(body);
        let mut moved = true;
        while moved {
            moved = false;
            for &(source, destination) in &edges {
                if escaping.contains(&destination) && escaping.insert(source) {
                    moved = true;
                }
            }
        }
        Self { escaping }
    }

    /// True when this local's value leaves the frame anywhere in it.
    pub(crate) fn escapes(&self, local: Local) -> bool {
        self.escaping.contains(&local)
    }
}

/// `(source, destination)` for every plain copy between two locals: the same five
/// assignment forms `local_outcome::copy_graph` follows, restricted to this body.
fn copy_edges(body: &Body<'_>) -> Vec<(Local, Local)> {
    let mut rows = Vec::new();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(box (destination, value)) = &statement.kind else {
                continue;
            };
            let Some(destination) = destination.as_local() else {
                continue;
            };
            let source = match value {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand.place(),
                Rvalue::CopyForDeref(place)
                | Rvalue::Ref(_, _, place)
                | Rvalue::RawPtr(_, place) => Some(*place),
                _ => None,
            };
            if let Some(place) = source {
                rows.push((place.local, destination));
            }
        }
    }
    rows
}

fn read_locals(value: &Rvalue<'_>, into: &mut FxHashSet<Local>) {
    let mut operand = |operand: &Operand<'_>| {
        if let Some(place) = operand.place() {
            into.insert(place.local);
        }
    };
    match value {
        Rvalue::Use(row) | Rvalue::Repeat(row, _) | Rvalue::Cast(_, row, _) => operand(row),
        Rvalue::BinaryOp(_, rows) => {
            operand(&rows.0);
            operand(&rows.1);
        }
        Rvalue::UnaryOp(_, row) => operand(row),
        Rvalue::Aggregate(_, rows) => {
            for row in rows {
                operand(row);
            }
        }
        Rvalue::CopyForDeref(place)
        | Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::Len(place)
        | Rvalue::Discriminant(place) => {
            into.insert(place.local);
        }
        _ => {}
    }
}

/// R343-1: is this holder's loan still demanded after a point?
///
/// The fact `protected_entry` does not need and this module does. An entry
/// obligation is live at every event in its frame by construction; an inner
/// holder is not, and that difference is the entire recovery.
///
/// Liveness is taken over the holder's COPY CLOSURE, not over its own local. The
/// comment this build exists to answer says why: "a deeper non-entry Ref can keep
/// an inner target live through Raw copies, even after its source local's last
/// use". A closure member's use is the holder's use.
///
/// It is a MAY-live: a reassignment of a member does not kill the closure. That
/// is the safe direction -- over-approximating liveness over-approximates "still
/// demanded", which keeps today's demotion -- and it is stated rather than
/// hidden, because it costs recall wherever a holder is rebound before the event.
#[derive(Clone, Debug)]
pub(crate) struct ClosureLiveness {
    members: FxHashSet<Local>,
    /// Some member is used at or after this block's entry, on some path.
    live_in: IndexVec<BasicBlock, bool>,
}

impl ClosureLiveness {
    pub(crate) fn of_body(body: &Body<'_>, local: Local) -> Self {
        let members = closure_of(body, local);
        let mut live_in: IndexVec<BasicBlock, bool> =
            IndexVec::from_elem_n(false, body.basic_blocks.len());
        let mut moved = true;
        while moved {
            moved = false;
            for (block, data) in body.basic_blocks.iter_enumerated() {
                let here = block_uses(data, &members)
                    || data
                        .terminator()
                        .successors()
                        .any(|successor| live_in[successor]);
                if here && !live_in[block] {
                    live_in[block] = true;
                    moved = true;
                }
            }
        }
        Self { members, live_in }
    }

    /// Every local this holder's value can be in.
    pub(crate) fn members(&self) -> &FxHashSet<Local> {
        &self.members
    }

    /// Is the loan still demanded strictly AFTER this location?
    ///
    /// At a terminator -- which is what a `free` call is -- "after" is the
    /// successors, because the terminator's own operands are the event itself and
    /// not a later use. R321-1's lesson is taken here: the union over successors
    /// answers "somewhere later", and a caller that needs one edge asks for it.
    pub(crate) fn live_after(&self, body: &Body<'_>, location: Location) -> bool {
        let data = &body.basic_blocks[location.block];
        let rest = data
            .statements
            .iter()
            .skip(location.statement_index + 1)
            .any(|statement| statement_uses(statement, &self.members));
        let terminator = location.statement_index < data.statements.len()
            && terminator_uses(data.terminator(), &self.members);
        rest || terminator
            || data
                .terminator()
                .successors()
                .any(|successor| self.live_in[successor])
    }

    /// Is it demanded on THIS edge only? An event on a cleanup path is discharged
    /// by the cleanup successor's liveness, never by the normal path's.
    pub(crate) fn live_on(&self, block: BasicBlock) -> bool {
        self.live_in[block]
    }
}

/// Every local the holder's value can reach through the frame's copy edges.
fn closure_of(body: &Body<'_>, local: Local) -> FxHashSet<Local> {
    let edges = copy_edges(body);
    let mut members = FxHashSet::default();
    members.insert(local);
    let mut moved = true;
    while moved {
        moved = false;
        for &(source, destination) in &edges {
            if members.contains(&source) && members.insert(destination) {
                moved = true;
            }
        }
    }
    members
}

fn block_uses(data: &rustc_middle::mir::BasicBlockData<'_>, members: &FxHashSet<Local>) -> bool {
    data.statements
        .iter()
        .any(|statement| statement_uses(statement, members))
        || terminator_uses(data.terminator(), members)
}

fn statement_uses(
    statement: &rustc_middle::mir::Statement<'_>,
    members: &FxHashSet<Local>,
) -> bool {
    let StatementKind::Assign(box (destination, value)) = &statement.kind else {
        return false;
    };
    let mut read = FxHashSet::default();
    read_locals(value, &mut read);
    // A write THROUGH a member is a use of the member; a write INTO it is not.
    read.iter().any(|local| members.contains(local))
        || (destination.as_local().is_none() && members.contains(&destination.local))
}

fn terminator_uses(
    terminator: &rustc_middle::mir::Terminator<'_>,
    members: &FxHashSet<Local>,
) -> bool {
    let mut operands: Vec<&Operand<'_>> = Vec::new();
    let mut places: Vec<Local> = Vec::new();
    match &terminator.kind {
        TerminatorKind::Call { func, args, .. } | TerminatorKind::TailCall { func, args, .. } => {
            operands.push(func);
            operands.extend(args.iter().map(|argument| &argument.node));
        }
        TerminatorKind::SwitchInt { discr, .. } => operands.push(discr),
        TerminatorKind::Assert { cond, .. } => operands.push(cond),
        TerminatorKind::Drop { place, .. } => places.push(place.local),
        TerminatorKind::Yield { value, .. } => operands.push(value),
        _ => {}
    }
    places.extend(
        operands
            .into_iter()
            .filter_map(|operand| operand.place())
            .map(|place| place.local),
    );
    places.into_iter().any(|local| members.contains(&local))
}

/// The obligations of one program: one per non-parameter Ref local at depth >= 1.
pub(crate) fn obligations(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    is_ref: impl Fn(SlotRef) -> bool,
) -> Vec<InnerLoan> {
    let mut rows = Vec::new();
    for &function in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let Some(universe) = slots.fn_local_slots.get(&function) else {
            continue;
        };
        for index in 0..universe.len() {
            let id = crate::analyses::borrow_ownership::slots::SlotId::from_usize(index);
            let slot = universe.slot(id);
            let SlotOwner::Local(local) = slot.owner else {
                continue;
            };
            // A parameter is `protected_entry`'s, not ours, and depth 0 is the
            // holder's own pointer value, which the native loans already own.
            if slot.depth == 0 || (local.as_usize() > 0 && local.as_usize() <= body.arg_count) {
                continue;
            }
            let holder = SlotRef::Local(function, id);
            if !is_ref(holder) {
                continue;
            }
            rows.push(InnerLoan {
                key: InnerLoanKey {
                    function,
                    local,
                    depth: slot.depth,
                    holder,
                },
                reservations: definitions(&body, local),
            });
        }
    }
    rows
}

/// Where this local's value is defined, and where a store writes through it.
fn definitions(body: &rustc_middle::mir::Body<'_>, local: Local) -> Vec<Location> {
    let mut rows = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let StatementKind::Assign(box (destination, value)) = &statement.kind else {
                continue;
            };
            let defines = destination.local == local
                || matches!(value, Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)
                    if place.local == local);
            if defines {
                rows.push(Location {
                    block,
                    statement_index,
                });
            }
        }
    }
    rows
}
