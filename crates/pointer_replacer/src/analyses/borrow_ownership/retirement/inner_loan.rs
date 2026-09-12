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

use rustc_middle::mir::{Local, Location, Rvalue, StatementKind};
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
