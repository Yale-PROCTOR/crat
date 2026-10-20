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

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Location, Operand, ProjectionElem, RETURN_PLACE, Rvalue,
        StatementKind, TerminatorKind,
    },
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use super::super::{crate_slots::CrateSlots, slots::SlotOwner, solver::SlotRef};
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

/// R343-1(i), sizing 2.6: the locals whose value leaves this frame DIRECTLY.
///
/// MIR copies a value into a temporary before it leaves -- `opaque(argument)` is
/// `_5 = copy _3; opaque(move _5)` -- so a holder escapes when any member of its
/// copy closure escapes directly. The closure is the production copy graph's
/// component, which is depth-aware; propagating escape along a depth-AGNOSTIC
/// local relation here instead would have been wrong in both directions, and was
/// measured wrong on `_b = copy (*_a)` before this was split.
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
/// Sizing 2.6 named `EscapeFacts::escapes` -- the local's own storage address
/// escaping -- as a fifth form. It is NOT one, and the witness found it: an inner
/// holder is built by taking an address (`inner = &raw mut base`), so `base` is
/// address-taken in every such frame and is a member of the holder's closure. The
/// rule would then mark every stack-constructed inner holder escaped and disable
/// the whole recovery. That relation answers a different question -- can a callee
/// WRITE this cell -- and the object state already answers it, in
/// `clobber_callee_reachable`. Four value-escape forms, then.
#[derive(Clone, Debug, Default)]
pub(crate) struct ValueEscapes {
    escaping: FxHashSet<Local>,
}

impl ValueEscapes {
    pub(crate) fn of_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Self {
        let mut escaping = FxHashSet::default();
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
                    escaping_reads(tcx, body, value, &mut escaping);
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
        Self { escaping }
    }

    /// True when this local's value leaves the frame anywhere in it.
    pub(crate) fn escapes(&self, local: Local) -> bool {
        self.escaping.contains(&local)
    }
}

/// The locals whose OWN VALUE this rvalue produces.
///
/// `_b = copy _a` produces `_a`'s value; `_b = copy (*_a)` produces the pointee,
/// a different value at a different depth. The distinction is the whole
/// difference between an escape and an ordinary read, and it was measured: with
/// the loose rule, `_0 = copy (*_8)` marked `_8` -- the inner cell's own value --
/// as escaped, so every holder read through before a free was demoted.
fn escaping_reads<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    value: &Rvalue<'tcx>,
    into: &mut FxHashSet<Local>,
) {
    let mut operand = |operand: &Operand<'tcx>| {
        let Some(place) = operand.place() else { return };
        // An unprojected read leaves this local's own value. A PROJECTED read
        // leaves what is behind it, which is this local's value at some deeper
        // slot exactly when the thing read is itself a pointer: `_0 = copy (*_qq)`
        // with `*qq: *mut i32` returns the inner cell's value, while the same
        // shape with `*_8: u8` returns a byte and lets no pointer out. The
        // relation is depth-agnostic, so marking the local is the safe direction.
        if place.projection.is_empty() || place.ty(&body.local_decls, tcx).ty.is_any_ptr() {
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
        // `&raw mut (*p)` is a reborrow: the same value as `p`. `&raw mut x` is
        // the ADDRESS of `x`, which is a different value and one the object state
        // owns, not this rule.
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
            if place.projection.len() == 1 && matches!(place.projection[0], ProjectionElem::Deref) {
                into.insert(place.local);
            }
        }
        _ => {}
    }
}

/// Every local this rvalue mentions at all. Liveness wants the loose rule: a read
/// THROUGH a member is still a use of that member.
fn mentioned_locals(value: &Rvalue<'_>, into: &mut FxHashSet<Local>) {
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
    /// Per block, everything a query needs, so the retirement loop can ask
    /// without carrying a `Body` it does not have in that scope.
    blocks: IndexVec<BasicBlock, BlockFacts>,
}

#[derive(Clone, Debug)]
struct BlockFacts {
    /// One entry per statement: does it use a closure member?
    statements: Vec<bool>,
    terminator: bool,
    successor_live: bool,
}

impl ClosureLiveness {
    pub(crate) fn of_body(body: &Body<'_>, members: FxHashSet<Local>) -> Self {
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
        let blocks = body
            .basic_blocks
            .iter_enumerated()
            .map(|(block, data)| BlockFacts {
                statements: data
                    .statements
                    .iter()
                    .map(|statement| statement_uses(statement, &members))
                    .collect(),
                terminator: terminator_uses(data.terminator(), &members),
                successor_live: data
                    .terminator()
                    .successors()
                    .any(|successor| live_in[successor]),
            })
            .collect::<IndexVec<BasicBlock, _>>();
        Self {
            members,
            live_in,
            blocks,
        }
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
    pub(crate) fn live_after(&self, location: Location) -> bool {
        let facts = &self.blocks[location.block];
        let rest = facts
            .statements
            .iter()
            .skip(location.statement_index + 1)
            .any(|&uses| uses);
        // At a terminator -- which is what a `free` call is -- the terminator's
        // own operands are the EVENT, not a later use.
        let terminator = location.statement_index < facts.statements.len() && facts.terminator;
        rest || terminator || facts.successor_live
    }

    /// Is it demanded on THIS edge only? An event on a cleanup path is discharged
    /// by the cleanup successor's liveness, never by the normal path's.
    pub(crate) fn live_on(&self, block: BasicBlock) -> bool {
        self.live_in[block]
    }
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
    mentioned_locals(value, &mut read);
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

/// What the retirement loop should do with one inner holder at one event.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Disposition {
    /// The loan is provably dead here: no conflict and no demotion. The recovery.
    Dead,
    /// Live and demanded: the caller tests object overlap and, if it overlaps,
    /// raises a conflict naming THIS holder rather than demoting its closure.
    Live,
    /// Facts missing. Sizing 2.2 row 3: today's demotion, unchanged.
    Unrepresented(Missing),
}

/// Why a holder has no usable fact. Both keep the current verdict; they are kept
/// apart so the escaped population is counted rather than inferred (sizing 2.6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Missing {
    /// No obligation: a field-owned holder, a parameter, or a Raw carrier.
    NoObligation,
    /// The value leaves the frame, so its copy closure is incomplete.
    Escaped,
}

/// Every inner-holder obligation of a program, with the facts to decide it.
#[derive(Debug, Default)]
pub(crate) struct InnerLoans {
    rows: FxHashMap<(LocalDefId, Local, u8), Row>,
}

#[derive(Debug)]
struct Row {
    loan: InnerLoan,
    escaped: bool,
    liveness: ClosureLiveness,
}

/// Build the obligations and their facts once per model.
///
/// The closure is `local_outcome::copy_graph`'s component -- the same relation
/// the demotion chain already walks, so a holder's closure here is exactly the
/// set that would have been demoted with it -- mapped to the owner locals the
/// MIR-level liveness and escape questions are asked about.
pub(crate) fn analyze(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    is_ref: impl Fn(SlotRef) -> bool,
) -> InnerLoans {
    let graph = super::local_outcome::copy_graph(program, slots);
    let mut rows = FxHashMap::default();
    let mut escapes: FxHashMap<LocalDefId, ValueEscapes> = FxHashMap::default();
    for loan in obligations(program, slots, is_ref) {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(loan.key.function)
            .borrow();
        let members = member_locals(slots, &graph, loan.key.holder, loan.key.local);
        let escaped = {
            let direct = escapes
                .entry(loan.key.function)
                .or_insert_with(|| ValueEscapes::of_body(program.tcx, &body));
            members.iter().any(|&local| direct.escapes(local))
        };
        let liveness = ClosureLiveness::of_body(&body, members);
        rows.insert(
            (loan.key.function, loan.key.local, loan.key.depth),
            Row {
                loan,
                escaped,
                liveness,
            },
        );
    }
    InnerLoans { rows }
}

/// The owner locals of the holder's copy-graph component, in its own frame.
fn member_locals(
    slots: &CrateSlots,
    graph: &FxHashMap<SlotRef, Vec<SlotRef>>,
    holder: SlotRef,
    local: Local,
) -> FxHashSet<Local> {
    let mut seen = FxHashSet::default();
    let mut pending = vec![holder];
    while let Some(slot) = pending.pop() {
        if seen.insert(slot) {
            pending.extend(graph.get(&slot).into_iter().flatten().copied());
        }
    }
    let mut locals = FxHashSet::default();
    locals.insert(local);
    for slot in seen {
        let SlotRef::Local(function, id) = slot else {
            continue;
        };
        let Some(universe) = slots.fn_local_slots.get(&function) else {
            continue;
        };
        if let SlotOwner::Local(member) = universe.slot(id).owner {
            locals.insert(member);
        }
    }
    locals
}

impl InnerLoans {
    /// The locals this holder's value can be in: its copy-graph component.
    pub(crate) fn members(
        &self,
        function: LocalDefId,
        local: Local,
        depth: u8,
    ) -> Option<&FxHashSet<Local>> {
        self.rows
            .get(&(function, local, depth))
            .map(|row| row.liveness.members())
    }

    /// The obligation for one holder, if it has one.
    pub(crate) fn reservations(
        &self,
        function: LocalDefId,
        local: Local,
        depth: u8,
    ) -> &[Location] {
        self.rows
            .get(&(function, local, depth))
            .map_or(&[], |row| row.loan.reservations.as_slice())
    }

    /// R343-1: the three-way disposition of sizing 2.2, in one place.
    ///
    /// The order is the whole soundness argument. Escape is asked BEFORE
    /// liveness, because an escaped value's closure is incomplete and its
    /// liveness answer would be a statement about the edges we built rather than
    /// about the program. Absence of an obligation is asked first of all.
    pub(crate) fn disposition(
        &self,
        function: LocalDefId,
        local: Local,
        depth: u8,
        location: Location,
    ) -> Disposition {
        let Some(row) = self.rows.get(&(function, local, depth)) else {
            return Disposition::Unrepresented(Missing::NoObligation);
        };
        if row.escaped {
            return Disposition::Unrepresented(Missing::Escaped);
        }
        if row.liveness.live_after(location) {
            Disposition::Live
        } else {
            Disposition::Dead
        }
    }

    /// The same question on one edge: an event on a cleanup path is discharged by
    /// the cleanup successor's liveness, never by the normal path's.
    pub(crate) fn disposition_on(
        &self,
        function: LocalDefId,
        local: Local,
        depth: u8,
        block: BasicBlock,
    ) -> Disposition {
        let Some(row) = self.rows.get(&(function, local, depth)) else {
            return Disposition::Unrepresented(Missing::NoObligation);
        };
        if row.escaped {
            return Disposition::Unrepresented(Missing::Escaped);
        }
        if row.liveness.live_on(block) {
            Disposition::Live
        } else {
            Disposition::Dead
        }
    }
}
