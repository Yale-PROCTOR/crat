// FORKED STAGE from production `crates/pointer_replacer/src/analyses/borrow/invalidates.rs` @ fc3bd4cf.
// Byte-identical to production at 3a (the equivalence baseline) — EXPECTED TO DIVERGE at NB3-3b:
// write-aware invalidation restores the read/write access distinction the port dropped, so the
// immutable-loan skip (`continue; // loan of immutable provenance does not invalidate`) fires for
// READS only, not writes. NO sync tripwire (divergence is the deliverable). NB6's validator uses the
// UNFORKED production engine (D5).
use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::{DenseBitSet, SparseBitMatrix};
use rustc_middle::{
    mir::{
        Body, CopyNonOverlapping, InlineAsmOperand, Local, Location, NonDivergingIntrinsic,
        Operand, Place, PlaceElem, PlaceRef, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind, visit::Visitor,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};

use super::{
    BorrowSet, Loan,
    a5_places_conflict::{ParameterOverlap, places_conflict_with_parameter_overlap},
    places_conflict::{AccessDepth, PlaceConflictBias},
};
use crate::analyses::{
    borrow::{Borrower, ProvenanceOwner, ProvenanceSet},
    borrow_ownership::boundary_table::{self, Matcher, Role},
};

pub(crate) type Invalidates = SparseBitMatrix<PointIndex, Loan>;

/// L2-only side witness for one invalidation insertion attempt.
///
/// The ordinary `Invalidates` matrix remains the sole input to the borrow
/// fixpoint. This parallel record is populated only by
/// `compute_invalidates_capturing` from the exact access being checked; it is
/// never read back into invalidation generation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct InvalidationAccess {
    pub(crate) point: PointIndex,
    pub(crate) loan: Loan,
    pub(crate) accessor: Local,
}

#[derive(Clone, Copy, Debug)]
struct ParameterAccess<'tcx> {
    place: Place<'tcx>,
    kind: AccessKind,
}

pub fn compute_invalidates<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    provenance_set: &ProvenanceSet,
    location_map: &DenseLocationMap,
) -> Invalidates {
    let copy_lends = DenseBitSet::new_empty(borrow_set.loans.len());
    compute_invalidates_inner(
        tcx,
        body,
        borrow_set,
        provenance_set,
        location_map,
        &copy_lends,
        None,
        None,
        None,
    )
}

pub(crate) fn compute_invalidates_with_copy_lends<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    provenance_set: &ProvenanceSet,
    location_map: &DenseLocationMap,
    copy_lends: &DenseBitSet<Loan>,
) -> Invalidates {
    compute_invalidates_inner(
        tcx,
        body,
        borrow_set,
        provenance_set,
        location_map,
        copy_lends,
        None,
        None,
        None,
    )
}

/// Compute the unchanged invalidation facts while also retaining the access
/// local responsible for each conflicting insertion attempt.
///
/// Only the L2 feature-on replay calls this entry point. Feature-off callers
/// continue through `compute_invalidates`, which supplies `None` and therefore
/// performs no side allocation or collection.
pub(crate) fn compute_invalidates_capturing<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    provenance_set: &ProvenanceSet,
    location_map: &DenseLocationMap,
) -> (Invalidates, Vec<InvalidationAccess>) {
    let copy_lends = DenseBitSet::new_empty(borrow_set.loans.len());
    compute_invalidates_capturing_with_copy_lends(
        tcx,
        body,
        borrow_set,
        provenance_set,
        location_map,
        &copy_lends,
    )
}

pub(crate) fn compute_invalidates_capturing_with_copy_lends<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    provenance_set: &ProvenanceSet,
    location_map: &DenseLocationMap,
    copy_lends: &DenseBitSet<Loan>,
) -> (Invalidates, Vec<InvalidationAccess>) {
    let mut accesses = Vec::new();
    let invalidates = compute_invalidates_inner(
        tcx,
        body,
        borrow_set,
        provenance_set,
        location_map,
        copy_lends,
        None,
        Some(&mut accesses),
        None,
    );
    (invalidates, accesses)
}

pub(crate) fn compute_invalidates_with_copy_lends_and_parameter_overlap<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    provenance_set: &ProvenanceSet,
    location_map: &DenseLocationMap,
    copy_lends: &DenseBitSet<Loan>,
    parameter_overlap: &ParameterOverlap,
) -> (Invalidates, Vec<(Local, Local)>) {
    let mut parameter_accesses = Vec::new();
    let invalidates = compute_invalidates_inner(
        tcx,
        body,
        borrow_set,
        provenance_set,
        location_map,
        copy_lends,
        Some(parameter_overlap),
        None,
        Some(&mut parameter_accesses),
    );
    let mut conflicts = BTreeSet::new();
    for (offset, left) in parameter_accesses.iter().enumerate() {
        for right in &parameter_accesses[offset + 1..] {
            if left.place.local == right.place.local
                || !parameter_overlap.contains(left.place.local, right.place.local)
                || (left.kind == AccessKind::Read && right.kind == AccessKind::Read)
                || !places_conflict_with_parameter_overlap(
                    tcx,
                    body,
                    left.place,
                    right.place,
                    AccessDepth::Deep,
                    PlaceConflictBias::Overlap,
                    Some(parameter_overlap),
                )
            {
                continue;
            }
            conflicts.insert((
                left.place.local.min(right.place.local),
                left.place.local.max(right.place.local),
            ));
        }
    }
    (invalidates, conflicts.into_iter().collect())
}

fn compute_invalidates_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    provenance_set: &ProvenanceSet,
    location_map: &DenseLocationMap,
    copy_lends: &DenseBitSet<Loan>,
    parameter_overlap: Option<&ParameterOverlap>,
    accesses: Option<&mut Vec<InvalidationAccess>>,
    parameter_accesses: Option<&mut Vec<ParameterAccess<'tcx>>>,
) -> Invalidates {
    let mut invalidates = SparseBitMatrix::new(borrow_set.loans.len());

    // §NB4-R routing toggle (default ON). `CRAT_NB4R_ROUTING=off|0` disables the cross-alias-write
    // walk, restoring pre-NB4-R invalidation — the sweep's gross-demotion attribution runs both.
    let routing_setting = std::env::var("CRAT_NB4R_ROUTING").ok();
    let routing_enabled = routing_enabled_for(routing_setting.as_deref(), !copy_lends.is_empty());

    LoanInvalidatesGenerator {
        facts: &mut invalidates,
        accesses,
        tcx,
        body,
        borrow_set,
        provenance_set,
        location_map,
        copy_lends,
        parameter_overlap,
        parameter_accesses,
        issued_loans: if routing_enabled {
            build_issued_loans(tcx, body, borrow_set)
        } else {
            FxHashMap::default()
        },
        routing_enabled,
    }
    .visit_body(body);

    invalidates
}

fn routing_enabled_for(setting: Option<&str>, has_copy_lends: bool) -> bool {
    // CopyLend's mandatory free(source)-through-cast rule depends on the issued-loan alias route.
    // The historical NB4-R ablation may disable that route only when no selected CopyLend exists.
    has_copy_lends || !matches!(setting, Some("off" | "0"))
}

#[cfg(test)]
mod copy_lend_routing_tests {
    use super::routing_enabled_for;

    #[test]
    fn copy_lend_keeps_mandatory_alias_routing_under_nb4r_off() {
        assert!(routing_enabled_for(Some("off"), true));
        assert!(routing_enabled_for(Some("0"), true));
        assert!(!routing_enabled_for(Some("off"), false));
    }
}

/// §NB4-R — an `offset`-call destination signature `(dest_local, borrowed=(*arg0))`. The fork
/// CANNOT tell an `offset` loan from a copy loan by `BorrowData` alone (both build `borrowed=(*arg0)`,
/// and `BorrowData::location` is private to the `borrow` module), so the offset destinations are
/// re-derived here by re-walking the MIR. **COUPLING GUARD (spec §4.1 / Amendment 4):** production's
/// `is_borrowing_method` = `{offset, as_ptr, as_mut_ptr}` (`borrow/mod.rs:783`, FROZEN); only `offset`
/// is address-CHANGING — `as_ptr`/`as_mut_ptr` are address-preserving and STAY as routing edges
/// (array-cell collapse). This matches ONLY `offset`; if the frozen set ever gains an address-changing
/// method, extend this filter (`address-changing(is_borrowing_method) ⊆ {offset}`).
fn build_offset_sigs<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> FxHashSet<(Local, Place<'tcx>)> {
    let mut sigs = FxHashSet::default();
    for data in body.basic_blocks.iter() {
        let Some(term) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        else {
            continue;
        };
        let TyKind::FnDef(def_id, _) = func.ty(body, tcx).kind() else {
            continue;
        };
        if def_id.is_local()
            || tcx.def_kind(*def_id) != rustc_hir::def::DefKind::AssocFn
            || tcx.item_name(*def_id).as_str() != "offset"
        {
            continue;
        }
        let Some(arg0) = args.first().and_then(|a| a.node.place()) else {
            continue;
        };
        sigs.insert((
            destination.local,
            arg0.project_deeper(&[PlaceElem::Deref], tcx),
        ));
    }
    sigs
}

/// §NB4-R — the copy/reborrow chain a routed write follows: maps each local to the loans it ISSUES
/// (`assigned == Assign(Local(l))`). A chain edge is a COPY/REBORROW, whose `borrowed` place is
/// `source.project_deeper([Deref])` and therefore ENDS in `Deref` (`b=p`→`[Deref]`; `b=h.q`→
/// `[Field, Deref]`; `b=*pp`→`[Deref, Deref]`; `&mut *p`→`[Deref]`). A DIRECT sub-borrow (`&mut a`→
/// `[]`; `&mut a.f`→`[Field]`; `&mut (*p).f`→`[Deref, Field]`) does NOT end in `Deref` and is excluded
/// (spec §11-B: the discriminator is the LAST element, not the first). Address-changing `offset` edges
/// are excluded via `build_offset_sigs`. `CallArg` loans are not edges (the issuer is a callee, not a
/// copy) but remain invalidation TARGETS in `local_map`. Built once per `compute_invalidates`.
fn build_issued_loans<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
) -> FxHashMap<Local, Vec<Loan>> {
    let offset_sigs = build_offset_sigs(tcx, body);
    let mut m: FxHashMap<Local, Vec<Loan>> = FxHashMap::default();
    for loan in borrow_set.loans.indices() {
        let bd = &borrow_set.loans[loan];
        let Borrower::Assign(ProvenanceOwner::Local(issuer)) = bd.assigned else {
            continue;
        };
        if bd.borrowed.projection.last() != Some(&PlaceElem::Deref) {
            continue; // a direct sub-borrow, not a pointer copy/reborrow
        }
        if bd.borrowed.local == issuer {
            continue; // degenerate self-alias
        }
        if offset_sigs.contains(&(issuer, bd.borrowed)) {
            continue; // address-changing offset (would over-demote; §4.1)
        }
        m.entry(issuer).or_default().push(loan);
    }
    m
}

/// §NB4-R — the routed place a cross-alias access composes to (extracted so the type-check/fallback
/// is testable in isolation, independent of the grouping that masks the end-to-end outcome).
pub(crate) enum RoutedCompose<'tcx> {
    /// `L.borrowed ++ rest` is well-typed (or `rest` is empty) — check it at the access's own depth.
    Composed(Place<'tcx>),
    /// `rest` is NOT applicable to `ty(L.borrowed)` (a type-changing cast) — composing would feed
    /// `places_conflict` an ill-typed place (`unreachable!`) or silently miss (`Disjoint`→UAF). Fall
    /// back to the whole borrowed cell, forced Deep (sound over-approximation; §4 ruling).
    WholeCell(Place<'tcx>),
}

/// Decide how a WRITE access `(*x)[rest]` composes onto an issued loan's `borrowed` place. Pure over
/// `(edge_borrowed, rest, deref_ty)`: `Composed` iff `rest` is empty or `ty(edge_borrowed) == deref_ty`
/// (the original access's deref type); otherwise `WholeCell`. The equality is exactly what guarantees
/// `places_conflict` only ever sees well-typed places rooted at the same base.
pub(crate) fn route_compose<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    edge_borrowed: Place<'tcx>,
    rest: &[PlaceElem<'tcx>],
    deref_ty: Ty<'tcx>,
) -> RoutedCompose<'tcx> {
    if rest.is_empty() {
        RoutedCompose::Composed(edge_borrowed)
    } else if edge_borrowed.ty(body, tcx).ty == deref_ty {
        RoutedCompose::Composed(edge_borrowed.project_deeper(rest, tcx))
    } else {
        RoutedCompose::WholeCell(edge_borrowed)
    }
}

struct LoanInvalidatesGenerator<'g, 'tcx> {
    facts: &'g mut Invalidates,
    /// L2-only write-side capture. `None` on every feature-off path.
    accesses: Option<&'g mut Vec<InvalidationAccess>>,
    tcx: TyCtxt<'tcx>,
    body: &'g Body<'tcx>,
    borrow_set: &'g BorrowSet<'tcx>,
    provenance_set: &'g ProvenanceSet,
    location_map: &'g DenseLocationMap,
    copy_lends: &'g DenseBitSet<Loan>,
    /// A5 effective may-overlap among this function's depth-zero parameters.
    parameter_overlap: Option<&'g ParameterOverlap>,
    /// A5-only access stream used to derive conflicts without synthesizing CallArg loans.
    parameter_accesses: Option<&'g mut Vec<ParameterAccess<'tcx>>>,
    /// §NB4-R routing chain (see `build_issued_loans`). Empty when routing is disabled.
    issued_loans: FxHashMap<Local, Vec<Loan>>,
    /// §NB4-R toggle (`CRAT_NB4R_ROUTING`); gates the cross-alias-write walk for sweep attribution.
    routing_enabled: bool,
}

/// §NB4-4a-ii **kind-labeling hoist** — the read/write kind of an access.
///
/// **Baseline/A12 loan invalidation remains inert by construction**: the immutable-loan skip
/// fires for both kinds, and a mutable loan conflicts with both. A5 precise replay separately
/// consumes the label when pairing accesses across effectively-overlapping parameters; that path
/// is absent when `parameter_overlap=None`. The label was originally threaded so 4b's
/// write-aware invalidation was a one-line skip change rather than a site refactor.
///
/// The site→kind table below is the 3b Task-0 table. Inertness is verified by the suite +
/// a spot sweep being byte-identical across this commit; if it were NOT inert, that would mean
/// access kinds already matter somewhere unknown, and it is a STOP.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AccessKind {
    Read,
    Write,
}

impl<'g, 'tcx> LoanInvalidatesGenerator<'g, 'tcx> {
    fn insert_invalidation(&mut self, point: PointIndex, loan: Loan, accessor: Local) {
        self.facts.insert(point, loan);
        if let Some(accesses) = self.accesses.as_mut() {
            accesses.push(InvalidationAccess {
                point,
                loan,
                accessor,
            });
        }
    }

    fn deeply_access_place(&mut self, location: Location, place: Place<'tcx>, kind: AccessKind) {
        self.check_access_for_conflict(location, place, AccessDepth::Deep, kind, false);
    }

    /// A12's targeted temporal rule. Only typed CopyLend loans are considered; the ordinary call
    /// operand remains a Read below, so existing loans retain pre-A12 deallocator behavior (A1).
    fn invalidate_copy_lends_at_deallocation(&mut self, location: Location, pointer: Place<'tcx>) {
        let pointee = pointer.project_deeper(&[PlaceElem::Deref], self.tcx);
        self.check_access_for_conflict(
            location,
            pointee,
            AccessDepth::Deep,
            AccessKind::Write,
            true,
        );
    }

    fn shallowly_access_place(&mut self, location: Location, place: Place<'tcx>, kind: AccessKind) {
        self.check_access_for_conflict(location, place, AccessDepth::Shallow, kind, false);
    }

    fn check_access_for_conflict(
        &mut self,
        location: Location,
        place: Place<'tcx>,
        access_depth: AccessDepth,
        // §NB4-4a-ii labeled the kind but left it unconsumed. §NB4-R consumes it: only a WRITE
        // access ROUTES (below). The DIRECT check still fires for both kinds (production parity).
        kind: AccessKind,
        copy_lends_only: bool,
    ) {
        if place.projection.first() == Some(&PlaceElem::Deref)
            && self
                .parameter_overlap
                .is_some_and(|overlap| overlap.has_local(place.local))
            && let Some(parameter_accesses) = self.parameter_accesses.as_mut()
        {
            parameter_accesses.push(ParameterAccess { place, kind });
        }
        let point_index = self.location_map.point_from_location(location);

        // DIRECT check: ordinary loans are keyed under the accessed local. A5 effective parameter
        // overlap additionally opens the paired parameter rows for pointee accesses; otherwise the
        // distinct-base `places_conflict` seam would never receive the pair in the first place.
        let mut candidate_bases = vec![place.local];
        if place.projection.first() == Some(&PlaceElem::Deref)
            && let Some(parameter_overlap) = self.parameter_overlap
        {
            candidate_bases.extend(parameter_overlap.partners(place.local));
        }
        for candidate_base in candidate_bases {
            let Some(borrows_for_place_base) = self.borrow_set.local_map.row(candidate_base) else {
                continue;
            };
            for loan in borrows_for_place_base.iter() {
                if copy_lends_only && !self.copy_lends.contains(loan) {
                    continue;
                }
                let borrow_data = &self.borrow_set.loans[loan];
                let copy_lend_write = kind == AccessKind::Write && self.copy_lends.contains(loan);
                if !copy_lend_write
                    && let Some(p) = self.provenance_set.local_data[borrow_data.borrowed.local]
                    && !self.provenance_set.provenance_data[p].is_mutable()
                {
                    continue; // loan of immutable provenance does not invalidate
                }
                if places_conflict_with_parameter_overlap(
                    self.tcx,
                    self.body,
                    borrow_data.borrowed,
                    place,
                    access_depth,
                    PlaceConflictBias::Overlap,
                    self.parameter_overlap,
                ) {
                    self.insert_invalidation(point_index, loan, place.local);
                }
            }
        }

        // §NB4-R CROSS-ALIAS-WRITE ROUTING. Writing `(*x)[rest]` where `x` is a copy/reborrow of some
        // base cell is a WRITE to THAT cell, but `local_map` keys loans by their borrowed base and
        // `places_conflict` bails on differing locals, so `row(x)` is BLIND to loans on the aliased
        // cell (the S2-6 hole). Walk `x`'s issued-loan chain to each aliased base, COMPOSE the access
        // onto the loan's own (type-valid) BORROWED place, and re-check `row(base)`. Runs even when
        // `row(x)` was empty above — that is exactly the witness case.
        //
        // Gated to WRITE + DEREF only: a bare-value read/move touches the pointer VALUE, not the
        // pointee (would route `store_global`-style over-invalidation); and a READ never NEEDS to
        // route — the cross-alias WRITE that makes the cell hazardous already routes to (and demotes)
        // every read view live across it, so routing reads is redundant (and would spuriously demote
        // shared reads of a mutable cell in forced-mut mode). This is the "cross-alias-WRITE routing"
        // divergence class (spec §8).
        if !self.routing_enabled
            || kind != AccessKind::Write
            || place.projection.first() != Some(&PlaceElem::Deref)
        {
            return;
        }
        let rest = &place.projection[1..];
        // ty of `(*x)`: the original access's deref type, computed ONCE. The composition
        // `L.borrowed ++ rest` is well-typed iff `ty(L.borrowed) == deref_ty` (same-type copies
        // preserve it; a type-changing cast breaks it → whole-cell fallback). This equality is what
        // keeps `places_conflict` from hitting its `unreachable!` (both operands well-typed at base).
        let deref_ty = PlaceRef {
            local: place.local,
            projection: &place.projection[..1],
        }
        .ty(self.body, self.tcx)
        .ty;

        // PRE-order bounded walk. Visited keyed on the LOAN (edge), NOT the base Local: distinct edges
        // can share a base local while naming different cells (a writer branch-joined from `h.q`/`h.r`
        // issues loans `(*(h.q))` and `(*(h.r))`, both base `h`); keying on the local would drop one
        // route and miss the cell aliased on the relevant path (Codex F2). Keying on the loan checks
        // every reachable edge exactly once, so the bound is `≤ loans.len()` and reconvergence still
        // cannot re-expand.
        let cap = self.borrow_set.loans.len();
        let mut visited: FxHashSet<Loan> = FxHashSet::default();
        let mut expansions = 0usize;
        let mut worklist: Vec<Loan> = self
            .issued_loans
            .get(&place.local)
            .cloned()
            .unwrap_or_default();
        while let Some(edge) = worklist.pop() {
            if !visited.insert(edge) {
                continue;
            }
            let edge_borrowed = self.borrow_set.loans[edge].borrowed;
            let base = edge_borrowed.local;
            expansions += 1;
            assert!(
                expansions <= cap,
                "NB4-R routing walk exceeded the per-site cap ({cap}); visited discipline regressed"
            );
            // Compose onto the edge's borrowed place, or fall back to whole-cell on a type mismatch.
            let (routed, routed_depth) =
                match route_compose(self.tcx, self.body, edge_borrowed, rest, deref_ty) {
                    RoutedCompose::Composed(p) => (p, access_depth),
                    // type-changing cast: `L.borrowed ++ rest` would be ill-typed ⇒ whole cell, Deep
                    // (sound over-approximation; §4 ruling — whole-cell, never a silent Disjoint).
                    RoutedCompose::WholeCell(p) => (p, AccessDepth::Deep),
                };
            if let Some(borrows_for_base) = self.borrow_set.local_map.row(base) {
                for loan in borrows_for_base.iter() {
                    if copy_lends_only && !self.copy_lends.contains(loan) {
                        continue;
                    }
                    let borrow_data = &self.borrow_set.loans[loan];
                    // self-loan skip: the access IS through `place.local`; its OWN loan (keyed under
                    // `base`) is not a conflict with itself, or every `let b=&mut *p; *b=…` reborrow
                    // would self-demote.
                    if matches!(
                        borrow_data.assigned,
                        Borrower::Assign(ProvenanceOwner::Local(l)) if l == place.local
                    ) {
                        continue;
                    }
                    let copy_lend_write =
                        kind == AccessKind::Write && self.copy_lends.contains(loan);
                    if !copy_lend_write
                        && let Some(p) = self.provenance_set.local_data[borrow_data.borrowed.local]
                        && !self.provenance_set.provenance_data[p].is_mutable()
                    {
                        continue; // loan of immutable provenance does not invalidate (read-only cell)
                    }
                    if places_conflict_with_parameter_overlap(
                        self.tcx,
                        self.body,
                        borrow_data.borrowed,
                        routed,
                        routed_depth,
                        PlaceConflictBias::Overlap,
                        self.parameter_overlap,
                    ) {
                        let accessor = if copy_lends_only { base } else { place.local };
                        self.insert_invalidation(point_index, loan, accessor);
                    }
                }
            }
            // continue the walk from `base`
            if let Some(next) = self.issued_loans.get(&base) {
                worklist.extend(next.iter().copied());
            }
        }
    }

    /// Simulates consumption of an operand. Reading an operand's VALUE is a `Read` at every
    /// site except `copy_nonoverlapping`'s destination, which passes `Write` explicitly.
    fn consume_operand(&mut self, location: Location, operand: &Operand<'tcx>, kind: AccessKind) {
        match *operand {
            Operand::Copy(place) => {
                self.deeply_access_place(location, place, kind);
            }
            Operand::Move(place) => {
                self.deeply_access_place(location, place, kind);
            }
            Operand::Constant(_) => {}
        }
    }

    // Simulates consumption of an rvalue
    fn consume_rvalue(&mut self, location: Location, rvalue: &Rvalue<'tcx>) {
        use rustc_middle::mir::{BorrowKind, RawPtrKind};
        match rvalue {
            // A borrow's kind IS its access kind: `&mut`/`&raw mut` write, shared borrows read.
            &Rvalue::Ref(_ /* rgn */, borrow_kind, place) => {
                let kind = if matches!(borrow_kind, BorrowKind::Mut { .. }) {
                    AccessKind::Write
                } else {
                    AccessKind::Read
                };
                self.deeply_access_place(location, place, kind);
            }

            &Rvalue::RawPtr(ptr_kind, place) => {
                let kind = if matches!(ptr_kind, RawPtrKind::Mut) {
                    AccessKind::Write
                } else {
                    AccessKind::Read
                };
                self.deeply_access_place(location, place, kind);
            }

            Rvalue::ThreadLocalRef(_) => {}

            Rvalue::Use(operand)
            | Rvalue::Repeat(operand, _)
            | Rvalue::UnaryOp(_ /* un_op */, operand)
            | Rvalue::Cast(_ /* cast_kind */, operand, _ /* ty */)
            | Rvalue::ShallowInitBox(operand, _ /* ty */) => {
                self.consume_operand(location, operand, AccessKind::Read)
            }

            &Rvalue::CopyForDeref(place) => {
                let op = &Operand::Copy(place);
                self.consume_operand(location, op, AccessKind::Read);
            }

            &(Rvalue::Len(place) | Rvalue::Discriminant(place)) => {
                self.deeply_access_place(location, place, AccessKind::Read);
            }

            Rvalue::BinaryOp(_bin_op, box (operand1, operand2)) => {
                self.consume_operand(location, operand1, AccessKind::Read);
                self.consume_operand(location, operand2, AccessKind::Read);
            }

            Rvalue::NullaryOp(_op, _ty) => {}

            Rvalue::Aggregate(_, operands) => {
                for operand in operands {
                    self.consume_operand(location, operand, AccessKind::Read);
                }
            }

            Rvalue::WrapUnsafeBinder(op, _) => {
                self.consume_operand(location, op, AccessKind::Read);
            }
        }
    }
}

/// Visits the whole MIR and generates `invalidates()` facts.
/// Most of the code implementing this was stolen from `borrow_check/mod.rs`.
impl<'g, 'tcx> Visitor<'tcx> for LoanInvalidatesGenerator<'g, 'tcx> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        match &statement.kind {
            StatementKind::Assign(box (lhs, rhs)) => {
                self.consume_rvalue(location, rhs);

                // The assignment's destination is WRITTEN.
                self.shallowly_access_place(location, *lhs, AccessKind::Write);
            }
            StatementKind::FakeRead(box (_, _)) => {
                // Only relevant for initialized/liveness/safety checks.
            }
            StatementKind::Intrinsic(box NonDivergingIntrinsic::Assume(op)) => {
                self.consume_operand(location, op, AccessKind::Read);
            }
            StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(CopyNonOverlapping {
                src,
                dst,
                count,
            })) => {
                self.consume_operand(location, src, AccessKind::Read);
                // `copy_nonoverlapping` WRITES through the destination pointer.
                self.consume_operand(location, dst, AccessKind::Write);
                self.consume_operand(location, count, AccessKind::Read);
            }
            // Only relevant for mir typeck
            StatementKind::AscribeUserType(..)
            // Only relevant for liveness and unsafeck
            | StatementKind::PlaceMention(..)
            // Doesn't have any language semantics
            | StatementKind::Coverage(..)
            // Does not actually affect borrowck
            | StatementKind::StorageLive(..) => {}
            StatementKind::StorageDead(local) => {
                // Storage is deallocated — a write in the strongest sense.
                self.shallowly_access_place(location, Place::from(*local), AccessKind::Write);
            }
            StatementKind::ConstEvalCounter
            | StatementKind::Nop
            | StatementKind::Retag { .. }
            | StatementKind::Deinit(..)
            | StatementKind::BackwardIncompatibleDropHint { .. }
            | StatementKind::SetDiscriminant { .. } => {
                unreachable!("Statement not allowed in this MIR phase")
            }
        }

        self.super_statement(statement, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            TerminatorKind::SwitchInt { discr, targets: _ } => {
                self.consume_operand(location, discr, AccessKind::Read);
            }
            TerminatorKind::Drop {
                place: drop_place,
                target: _,
                unwind: _,
                replace: _,
                drop: _,
                async_fut: _,
            } => {
                // Dropping runs the destructor through the place — a write.
                self.deeply_access_place(location, *drop_place, AccessKind::Write);
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target: _,
                unwind: _,
                call_source: _,
                fn_span: _,
            } => {
                self.consume_operand(location, func, AccessKind::Read);
                let copy_lend_deallocator = exact_foreign_sink(func, self.body, self.tcx);
                for arg in args {
                    // §NB4-4a-ii: labeled `Read` here; 4a-ii's GATING commit refines the arg
                    // access by the callee's effect class (a `no-access` callee gets a SHALLOW
                    // access instead of this blanket `Deep` one).
                    self.consume_operand(location, &arg.node, AccessKind::Read);
                }
                if copy_lend_deallocator
                    && let Some(arg0) = args.first()
                    && let Operand::Copy(place) | Operand::Move(place) = &arg0.node
                {
                    self.invalidate_copy_lends_at_deallocation(location, *place);
                }
                // The call's return value is WRITTEN into the destination.
                self.deeply_access_place(location, *destination, AccessKind::Write);
            }
            TerminatorKind::TailCall { func, args, .. } => {
                self.consume_operand(location, func, AccessKind::Read);
                for arg in args {
                    self.consume_operand(location, &arg.node, AccessKind::Read);
                }
            }
            TerminatorKind::Assert {
                cond,
                expected: _,
                msg,
                target: _,
                unwind: _,
            } => {
                self.consume_operand(location, cond, AccessKind::Read);
                use rustc_middle::mir::AssertKind;
                if let AssertKind::BoundsCheck { len, index } = &**msg {
                    self.consume_operand(location, len, AccessKind::Read);
                    self.consume_operand(location, index, AccessKind::Read);
                }
            }
            TerminatorKind::Yield { .. } => {
                unimplemented!()
            }
            TerminatorKind::UnwindResume
            | TerminatorKind::Return
            | TerminatorKind::CoroutineDrop => {
                // Invalidate all borrows of local places
                let borrow_set = self.borrow_set;
                let point_index = self.location_map.point_from_location(location);
                for (i, data) in borrow_set.loans.iter_enumerated() {
                    if !data.borrowed.is_indirect() {
                        self.facts.insert(point_index, i);
                    }
                }
            }
            TerminatorKind::InlineAsm {
                asm_macro: _,
                template: _,
                operands,
                options: _,
                line_spans: _,
                targets: _,
                unwind: _,
            } => {
                for op in operands {
                    match op {
                        InlineAsmOperand::In { reg: _, value } => {
                            self.consume_operand(location, value, AccessKind::Read);
                        }
                        InlineAsmOperand::Out {
                            reg: _,
                            late: _,
                            place,
                            ..
                        } => {
                            if let &Some(place) = place {
                                self.deeply_access_place(location, place, AccessKind::Write);
                            }
                        }
                        InlineAsmOperand::InOut {
                            reg: _,
                            late: _,
                            in_value,
                            out_place,
                        } => {
                            self.consume_operand(location, in_value, AccessKind::Read);
                            if let &Some(out_place) = out_place {
                                self.deeply_access_place(location, out_place, AccessKind::Write);
                            }
                        }
                        InlineAsmOperand::Const { value: _ }
                        | InlineAsmOperand::SymFn { value: _ }
                        | InlineAsmOperand::SymStatic { def_id: _ }
                        | InlineAsmOperand::Label { target_index: _ } => {}
                    }
                }
            }
            TerminatorKind::Goto { target: _ }
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Unreachable
            | TerminatorKind::FalseEdge {
                real_target: _,
                imaginary_target: _,
            }
            | TerminatorKind::FalseUnwind {
                real_target: _,
                unwind: _,
            } => {
                // no data used, thus irrelevant to borrowck
            }
        }

        self.super_terminator(terminator, location);
    }
}

fn exact_foreign_sink<'tcx>(func: &Operand<'tcx>, body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let TyKind::FnDef(def_id, _) = func.ty(body, tcx).kind() else {
        return false;
    };
    let Some(local_did) = def_id.as_local() else {
        return false;
    };
    if !matches!(
        tcx.hir_node_by_def_id(local_did),
        rustc_hir::Node::ForeignItem(_)
    ) {
        return false;
    }
    let name = tcx.item_name(*def_id);
    boundary_table::lookup(name.as_str(), Matcher::ForeignC)
        .is_some_and(|entry| entry.roles == [Role::Sink])
}
