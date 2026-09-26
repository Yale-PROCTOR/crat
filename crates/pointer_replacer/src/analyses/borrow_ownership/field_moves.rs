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

/// `CRAT_ERA5C_FIELD_MOVE=on|off` (fail-loud, absent = off): L01⁵ (ii)'s pin.
/// Separate from `CRAT_ERA5C_MOVE_TRACKING` because L01⁗ is sealed and landing.
pub(crate) fn field_move() -> bool {
    match std::env::var("CRAT_ERA5C_FIELD_MOVE").ok().as_deref() {
        None | Some("off") => false,
        Some("on") => true,
        Some(other) => panic!("CRAT_ERA5C_FIELD_MOVE must be `on` or `off`, got {other:?}"),
    }
}

/// `CRAT_ERA5C_LEAK_PARITY=on|off` (fail-loud, absent = off): L01^5 (i)'s pin —
/// prefer `Owning` for the field slots of a program that has no sink at all.
pub(crate) fn leak_parity_admission() -> bool {
    match std::env::var("CRAT_ERA5C_LEAK_PARITY").ok().as_deref() {
        None | Some("off") => false,
        Some("on") => true,
        Some(other) => panic!("CRAT_ERA5C_LEAK_PARITY must be `on` or `off`, got {other:?}"),
    }
}

/// `CRAT_ERA5C_RESEAT_A1=on|off` (fail-loud, absent = off): **L01⁶-A1**.
/// A call-result re-seat `x = f(x)` transfers the previous version's ownership
/// to the new version instead of finalizing it `false`, when the callee's
/// summary returns its parameter or a fresh allocation and the re-seat is the
/// last use of the previous version on every path. Era-5c report 034 §1:
/// `own-assume[temporary-finalization]` is in all nine of bst's driver cores,
/// and it is LOAD-BEARING elsewhere (`0/13/31 → 28/8/8` without it), so this
/// displaces it at re-seat sites only.
pub(crate) fn reseat_a1() -> bool {
    match std::env::var("CRAT_ERA5C_RESEAT_A1").ok().as_deref() {
        None | Some("off") => false,
        Some("on") => true,
        Some(other) => panic!("CRAT_ERA5C_RESEAT_A1 must be `on` or `off`, got {other:?}"),
    }
}

/// `CRAT_ERA5C_MUT_MODEL=on|off` (fail-loud, absent = off): **L01⁸, R545-1**.
/// A table's reborrow is unique only when a Ref level below it is written. The
/// verification replay recomputes the mutability facts per round with Foster's
/// load guard dropped where the loaded level is Raw in the round's model (era-5c
/// report 045: tulip's `outputs@d0` is lost to the per-local bit its written
/// element sets, through the closing `offset_from(*outputs.offset(0))` re-read).
pub(crate) fn mut_model() -> bool {
    match std::env::var("CRAT_ERA5C_MUT_MODEL").ok().as_deref() {
        None | Some("off") => false,
        Some("on") => true,
        Some(other) => panic!("CRAT_ERA5C_MUT_MODEL must be `on` or `off`, got {other:?}"),
    }
}

/// `CRAT_ERA5C_LEND_FORMAL=on|off` (fail-loud, absent = off): **L01⁸, R545-2**.
/// A formal whose every closed-world actual is the address of a stack place or
/// an interior place is a lend and never `Owning` (era-5c report 041's
/// `init65::_2`: settled Owning with every arm off).
pub(crate) fn lend_formal() -> bool {
    match std::env::var("CRAT_ERA5C_LEND_FORMAL").ok().as_deref() {
        None | Some("off") => false,
        Some("on") => true,
        Some(other) => panic!("CRAT_ERA5C_LEND_FORMAL must be `on` or `off`, got {other:?}"),
    }
}

/// `CRAT_ERA5C_TRAVERSAL_REF=on|off` (fail-loud, absent = off): **L01⁶-A2**.
/// A field-load re-seat in a loop (`node = (*node).left`) types its result as a
/// BORROW of the container rather than transferring ownership to it. Era-5c
/// report 034b §5: `minValueNode`'s own-probe core is internal and carries
/// `own-linear` + `own-null-join`, so two owners of one allocation is what the
/// transfer reading would need, and linearity forbids it.
pub(crate) fn traversal_ref() -> bool {
    match std::env::var("CRAT_ERA5C_TRAVERSAL_REF").ok().as_deref() {
        None | Some("off") => false,
        Some("on") => true,
        Some(other) => panic!("CRAT_ERA5C_TRAVERSAL_REF must be `on` or `off`, got {other:?}"),
    }
}

/// `CRAT_ERA5C_OWN_PREFER_LOCAL=on|off` (fail-loud, absent = off): **L01⁶ (b)**.
/// The local-slot Owning preference. A slot the licensing layer has already
/// refused a reference (`no_ref_carriers`: its origin atoms are all `Fresh`/
/// `Null`) has only `raw ∨ own` left, and `own` carries no objective weight, so
/// it settles `Raw`. This adds a soft `own` ABOVE `raw`'s 1 and below `ref_`'s
/// `big`, so it can never displace a reference and never makes an illegal model
/// legal. Era-5c report 034b §3 priced the market: 77 of 462 subjects, 7 of the
/// 55 measured CROWN Box units.
pub(crate) fn own_prefer_local() -> bool {
    match std::env::var("CRAT_ERA5C_OWN_PREFER_LOCAL").ok().as_deref() {
        None | Some("off") => false,
        Some("on") => true,
        Some(other) => panic!("CRAT_ERA5C_OWN_PREFER_LOCAL must be `on` or `off`, got {other:?}"),
    }
}

/// `CRAT_ERA5C_FINALIZE_SOFT=on|off` (fail-loud, absent = off): **L01⁶ arm 3**
/// (R518-2). `temporary-finalization` stops being a blanket hard assumption and
/// becomes an objective question, under the R101 leak-parity waiver.
///
/// Two halves, and the second is what makes the first work. Report 034 §1
/// measured that dropping the blanket alone *degrades* bst's corpus form
/// (`0/13/31 → 28/8/8`) — with no finalization the optimum had no reason to
/// seat the ownership token on the NAMED local rather than on a temporary, so
/// ownership smeared. R518-2 reads that correctly as an objective gap, not a
/// reason to keep the blanket. So this arm:
///
///   1. drops the hard `own = false` finalization of temporaries, and
///   2. adds a soft `own` preference on every slot that is a NAMED local
///      (one with `var_debug_info`), at a weight above L01⁶ (b)'s, so the
///      optimum seats the token on the name the source gave it.
///
/// Soundness lines untouched: fresh ≠ Ref, one owner (`own-linear` stays hard),
/// frees at C free sites. Every admitted implicit close is the R101 waiver's
/// `waiver-drop(scope-exit)` site, which the emission side already counts.
pub(crate) fn finalize_soft() -> bool {
    match std::env::var("CRAT_ERA5C_FINALIZE_SOFT").ok().as_deref() {
        None | Some("off") => false,
        Some("on") => true,
        Some(other) => panic!("CRAT_ERA5C_FINALIZE_SOFT must be `on` or `off`, got {other:?}"),
    }
}

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
    if !field_move() {
        return out;
    }
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
                    if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
                        eprintln!(
                            "E5C field-move MOVE {:?} at {location:?} ({:?})",
                            body.source.def_id(),
                            source
                        );
                    }
                }
                Err(reason) => {
                    out.refusals.insert(location, reason);
                    if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
                        eprintln!(
                            "E5C field-move REFUSED {:?} at {location:?}: {reason} ({:?})",
                            body.source.def_id(),
                            source
                        );
                    }
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
