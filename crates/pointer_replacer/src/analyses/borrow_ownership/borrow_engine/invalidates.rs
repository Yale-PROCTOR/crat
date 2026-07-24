// FORKED STAGE from production `crates/pointer_replacer/src/analyses/borrow/invalidates.rs` @ fc3bd4cf.
// Byte-identical to production at 3a (the equivalence baseline) — EXPECTED TO DIVERGE at NB3-3b:
// write-aware invalidation restores the read/write access distinction the port dropped, so the
// immutable-loan skip (`continue; // loan of immutable provenance does not invalidate`) fires for
// READS only, not writes. NO sync tripwire (divergence is the deliverable). NB6's validator uses the
// UNFORKED production engine (D5).
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::SparseBitMatrix;
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
    places_conflict::{AccessDepth, PlaceConflictBias, places_conflict},
};
use crate::analyses::borrow::{Borrower, ProvenanceOwner, ProvenanceSet};

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

pub fn compute_invalidates<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    provenance_set: &ProvenanceSet,
    location_map: &DenseLocationMap,
) -> Invalidates {
    compute_invalidates_inner(tcx, body, borrow_set, provenance_set, location_map, None)
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
    let mut accesses = Vec::new();
    let invalidates = compute_invalidates_inner(
        tcx,
        body,
        borrow_set,
        provenance_set,
        location_map,
        Some(&mut accesses),
    );
    (invalidates, accesses)
}

fn compute_invalidates_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    provenance_set: &ProvenanceSet,
    location_map: &DenseLocationMap,
    accesses: Option<&mut Vec<InvalidationAccess>>,
) -> Invalidates {
    let mut invalidates = SparseBitMatrix::new(borrow_set.loans.len());

    // §NB4-R routing toggle (default ON). `CRAT_NB4R_ROUTING=off|0` disables the cross-alias-write
    // walk, restoring pre-NB4-R invalidation — the sweep's gross-demotion attribution runs both.
    let routing_enabled = !matches!(
        std::env::var("CRAT_NB4R_ROUTING").as_deref(),
        Ok("off") | Ok("0")
    );

    LoanInvalidatesGenerator {
        facts: &mut invalidates,
        accesses,
        tcx,
        body,
        borrow_set,
        provenance_set,
        location_map,
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
    /// §NB4-R routing chain (see `build_issued_loans`). Empty when routing is disabled.
    issued_loans: FxHashMap<Local, Vec<Loan>>,
    /// §NB4-R toggle (`CRAT_NB4R_ROUTING`); gates the cross-alias-write walk for sweep attribution.
    routing_enabled: bool,
}

/// §NB4-4a-ii **kind-labeling hoist** — the read/write kind of an access.
///
/// **INERT TODAY, BY CONSTRUCTION**: `check_access_for_conflict` does not consult it. The
/// immutable-loan skip fires for both kinds, and a mutable loan conflicts with both, so no
/// decision depends on it. It is threaded now so that **4b's write-aware invalidation is a
/// one-line change to the SKIP condition**, not a refactor of every access site — which keeps
/// 4b's sweep row **WA-ALONE** instead of conflating write-awareness with a site→kind
/// re-labeling. (Same hoisting logic as BB3-a and the effect axis landing in 4a.)
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
        self.check_access_for_conflict(location, place, AccessDepth::Deep, kind);
    }

    fn shallowly_access_place(&mut self, location: Location, place: Place<'tcx>, kind: AccessKind) {
        self.check_access_for_conflict(location, place, AccessDepth::Shallow, kind);
    }

    fn check_access_for_conflict(
        &mut self,
        location: Location,
        place: Place<'tcx>,
        access_depth: AccessDepth,
        // §NB4-4a-ii labeled the kind but left it unconsumed. §NB4-R consumes it: only a WRITE
        // access ROUTES (below). The DIRECT check still fires for both kinds (production parity).
        kind: AccessKind,
    ) {
        let point_index = self.location_map.point_from_location(location);

        // DIRECT check: loans keyed under the accessed local.
        if let Some(borrows_for_place_base) = self.borrow_set.local_map.row(place.local) {
            for loan in borrows_for_place_base.iter() {
                let borrow_data = &self.borrow_set.loans[loan];
                if let Some(p) = self.provenance_set.local_data[borrow_data.borrowed.local]
                    && !self.provenance_set.provenance_data[p].is_mutable()
                {
                    continue; // loan of immutable provenance does not invalidate
                }
                if places_conflict(
                    self.tcx,
                    self.body,
                    borrow_data.borrowed,
                    place,
                    access_depth,
                    PlaceConflictBias::Overlap,
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
                    if let Some(p) = self.provenance_set.local_data[borrow_data.borrowed.local]
                        && !self.provenance_set.provenance_data[p].is_mutable()
                    {
                        continue; // loan of immutable provenance does not invalidate (read-only cell)
                    }
                    if places_conflict(
                        self.tcx,
                        self.body,
                        borrow_data.borrowed,
                        routed,
                        routed_depth,
                        PlaceConflictBias::Overlap,
                    ) {
                        self.insert_invalidation(point_index, loan, place.local);
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
                for arg in args {
                    // §NB4-4a-ii: labeled `Read` here; 4a-ii's GATING commit refines the arg
                    // access by the callee's effect class (a `no-access` callee gets a SHALLOW
                    // access instead of this blanket `Deep` one).
                    self.consume_operand(location, &arg.node, AccessKind::Read);
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
