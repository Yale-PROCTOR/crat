//! L01⁵ (ii) — the field↔field strong-update move.
//!
//! bst needed none of this: its deletion never permutes two live fields. avl's
//! rotations do — `x = (*y).left; T2 = (*x).right; (*x).right = y; (*y).left = T2;`
//! permutes three field slots between two nodes — and W19/W20 measure what that
//! costs: 25 raw / 8 ref / 0 owning with a `free` and without one, while the same
//! shape with no rotation (W18) is 0 raw. The relax core names the mechanism:
//! `coherence::kind-equate(Local(rightRotate, BO_S(2)), Field(BO_S(0)), own)` —
//! a field load kind-equates the local with the CRATE-WIDE field slot, so the
//! field can never hand its token to the local and the whole web settles raw.
//!
//! The fact this module computes is the guard that releases that equality, and
//! only where releasing it is sound: the load is a MOVE when the loaded place is
//! overwritten on EVERY path out of the load before any later read of it — so no
//! reader can observe the field still holding the moved value. It is E5C-1's
//! must-null discharge keyed on an overwrite instead of a NULL, and it asserts
//! nothing about ownership: it only stops forcing local and field to share a kind.
//! The soundness lines of R395-2 are untouched — drops stay at C free sites.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::{
    BasicBlock, Body, Location, Operand, Place, Rvalue, StatementKind, TerminatorKind,
    visit::{PlaceContext, Visitor},
};

use super::null_paths::{NullPlace, Proj};

/// The locations whose field load is a strong-update MOVE.
#[derive(Debug, Default)]
pub(crate) struct FieldMoves {
    moves: FxHashSet<Location>,
    /// Diagnosis only: why a candidate was refused.
    refusals: FxHashMap<Location, &'static str>,
}

impl FieldMoves {
    pub(crate) fn is_move(&self, location: Location) -> bool {
        self.moves.contains(&location)
    }

    pub(crate) fn refusal(&self, location: Location) -> Option<&'static str> {
        self.refusals.get(&location).copied()
    }

    pub(crate) fn len(&self) -> usize {
        self.moves.len()
    }
}

/// A candidate load: `lhs = (*base).field` (a copy out of a field behind a
/// pointer). Only depth-0 pointer-typed loads are candidates.
fn loaded_place<'a, 'tcx>(rvalue: &'a Rvalue<'tcx>) -> Option<&'a Place<'tcx>> {
    match rvalue {
        Rvalue::Use(Operand::Copy(place)) | Rvalue::Use(Operand::Move(place)) => Some(place),
        Rvalue::CopyForDeref(place) => Some(place),
        _ => None,
    }
}

/// Collects every place a statement or terminator mentions.
struct Places<'tcx> {
    seen: Vec<Place<'tcx>>,
}

impl<'tcx> Visitor<'tcx> for Places<'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, _: PlaceContext, _: Location) {
        self.seen.push(*place);
    }
}

fn places_of_statement<'tcx>(
    body: &Body<'tcx>,
    location: Location,
    include_lhs: bool,
) -> Vec<Place<'tcx>> {
    let data = &body.basic_blocks[location.block];
    let mut collector = Places { seen: Vec::new() };
    if location.statement_index < data.statements.len() {
        let statement = &data.statements[location.statement_index];
        if let (false, StatementKind::Assign(boxed)) = (include_lhs, &statement.kind) {
            collector.visit_rvalue(&boxed.1, location);
        } else {
            collector.visit_statement(statement, location);
        }
    } else {
        collector.visit_terminator(data.terminator(), location);
    }
    collector.seen
}

/// Does `statement` at `location` write exactly `place`?
fn writes_place(body: &Body<'_>, location: Location, place: &NullPlace) -> bool {
    let data = &body.basic_blocks[location.block];
    if location.statement_index >= data.statements.len() {
        return false;
    }
    match &data.statements[location.statement_index].kind {
        StatementKind::Assign(boxed) => NullPlace::of(&boxed.0).as_ref() == Some(place),
        _ => false,
    }
}

/// Does anything at `location` READ `place` (or a prefix of it), or take its
/// address, or call through it? Conservative: any mention that is not the exact
/// overwrite counts as a read.
fn mentions_place(body: &Body<'_>, location: Location, place: &NullPlace) -> bool {
    let data = &body.basic_blocks[location.block];
    // A mention that can OBSERVE the moved value is a read of exactly the place
    // or of something deeper through it (`(*p).f`, `(*(*p).f).g`, …). A bare copy
    // of the BASE pointer (`q = p`, or `(*other).g = p`) cannot: the stale field
    // is only reachable through a later deref, and `overwritten_on_every_path`
    // refuses any call in the window, so no callee can perform one either.
    let mentions_in = |p: &Place<'_>| {
        NullPlace::of(p)
            .map(|q| q.local == place.local && q.proj.starts_with(&place.proj))
            .unwrap_or(false)
    };
    // An exact overwrite is not a read: exclude the assignment's own destination.
    let exact_overwrite = location.statement_index < data.statements.len()
        && matches!(&data.statements[location.statement_index].kind,
            StatementKind::Assign(boxed) if NullPlace::of(&boxed.0).as_ref() == Some(place));
    places_of_statement(body, location, !exact_overwrite)
        .iter()
        .any(mentions_in)
}

/// Compute the strong-update field moves of `body`.
pub(crate) fn compute<'tcx>(body: &Body<'tcx>) -> FieldMoves {
    let mut out = FieldMoves::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            let StatementKind::Assign(boxed) = &statement.kind else { continue };
            let (lhs, rvalue) = (&boxed.0, &boxed.1);
            let Some(rhs) = loaded_place(rvalue) else { continue };
            // The loaded place must be a field behind a deref: `(*base).f`.
            let Some(source) = NullPlace::of(rhs) else { continue };
            if !matches!(source.proj.as_slice(), [Proj::Deref, Proj::Field(_)]) {
                out.refusals.insert(location, "not-a-deref-field-load");
                continue;
            }
            // The destination must be a plain local (no projection): a move into
            // a temporary, not a store through another pointer.
            if !lhs.projection.is_empty() {
                out.refusals.insert(location, "destination-is-projected");
                continue;
            }
            // `lhs` has no projection (checked above), so its type is the local's.
            if !matches!(
                body.local_decls[lhs.local].ty.kind(),
                rustc_middle::ty::TyKind::RawPtr(..)
            ) {
                out.refusals
                    .insert(location, "destination-not-a-raw-pointer");
                continue;
            }
            match overwritten_on_every_path(body, location, &source) {
                Ok(()) => {
                    out.moves.insert(location);
                }
                Err(reason) => {
                    out.refusals.insert(location, reason);
                }
            }
        }
    }
    out
}

/// The must-overwrite walk: from the statement AFTER `location`, every path must
/// reach an exact write of `source` before any read of it, and before leaving the
/// function. A loop back-edge that neither writes nor reads is refused (the walk
/// does not assume progress).
fn overwritten_on_every_path(
    body: &Body<'_>,
    location: Location,
    source: &NullPlace,
) -> Result<(), &'static str> {
    let mut seen: FxHashSet<Location> = FxHashSet::default();
    let mut frontier = vec![Location {
        block: location.block,
        statement_index: location.statement_index + 1,
    }];
    while let Some(here) = frontier.pop() {
        if !seen.insert(here) {
            // A cycle with no overwrite on it: the value can be read again.
            return Err("cycle-without-overwrite");
        }
        let data = &body.basic_blocks[here.block];
        if here.statement_index < data.statements.len() {
            if mentions_place(body, here, source) {
                return Err("read-before-overwrite");
            }
            if writes_place(body, here, source) {
                continue; // this path is discharged
            }
            frontier.push(Location {
                block: here.block,
                statement_index: here.statement_index + 1,
            });
            continue;
        }
        // The terminator.
        if mentions_place(body, here, source) {
            return Err("terminator-reads-the-place");
        }
        match &data.terminator().kind {
            TerminatorKind::Return | TerminatorKind::UnwindResume | TerminatorKind::Unreachable => {
                return Err("leaves-the-function-without-overwrite");
            }
            // A callee could deref a copy of the base and observe the moved value.
            TerminatorKind::Call { .. } | TerminatorKind::TailCall { .. } => {
                return Err("call-in-the-window");
            }
            terminator => {
                let mut successors: Vec<BasicBlock> = Vec::new();
                terminator.successors().for_each(|s| successors.push(s));
                if successors.is_empty() {
                    return Err("no-successor");
                }
                for successor in successors {
                    frontier.push(Location {
                        block: successor,
                        statement_index: 0,
                    });
                }
            }
        }
    }
    Ok(())
}
