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
        Body, CopyNonOverlapping, InlineAsmOperand, Local, Location, NonDivergingIntrinsic, Operand,
        Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, visit::Visitor,
    },
    ty::TyCtxt,
};
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};

use super::{
    BorrowSet, Loan,
    places_conflict::{AccessDepth, PlaceConflictBias, places_conflict},
};
use crate::analyses::borrow::{Borrower, ProvenanceOwner, ProvenanceSet};

pub(crate) type Invalidates = SparseBitMatrix<PointIndex, Loan>;

pub fn compute_invalidates<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    provenance_set: &ProvenanceSet,
    location_map: &DenseLocationMap,
) -> Invalidates {
    let mut invalidates = SparseBitMatrix::new(borrow_set.loans.len());

    LoanInvalidatesGenerator {
        facts: &mut invalidates,
        tcx,
        body,
        borrow_set,
        provenance_set,
        location_map,
        issued_bases: build_issued_bases(borrow_set),
    }
    .visit_body(body);

    invalidates
}

/// §NB4-4b-i — the copy/reborrow chain a routed write follows. Maps each local to the base
/// locals of the loans it ISSUES (`assigned == Assign(Local(l))`): `let b = p` issues
/// `L borrowed=(*p) assigned=b`, so `b → [p]`. Following this chain sends a write through `b`
/// to the cell `b` actually points into. `CallArg` loans are NOT chain edges (their issuer is a
/// callee, not a copy of a local). Built once per `compute_invalidates`.
fn build_issued_bases(borrow_set: &BorrowSet<'_>) -> FxHashMap<Local, Vec<Local>> {
    use rustc_middle::mir::PlaceElem;
    let mut m: FxHashMap<Local, Vec<Local>> = FxHashMap::default();
    for loan in borrow_set.loans.indices() {
        let bd = &borrow_set.loans[loan];
        // Only a COPY/REBORROW is a chain edge — its borrowed place is `(*base)` (a leading
        // `Deref`), so the issuer holds the SAME address as `base` and a write through the
        // issuer is a write through `base`. A DIRECT borrow (`let x = &mut a`) has `borrowed = a`
        // (no `Deref`): `a` is the POINTEE, not a pointer the issuer copies — following it would
        // re-base `(*x)` onto `(*a)` and spuriously connect independent borrows (the
        // `bbparity_independent_*` failure). Requires `borrowed = (*base)[…]`, base a pointer.
        if let Borrower::Assign(ProvenanceOwner::Local(issuer)) = bd.assigned
            && bd.borrowed.projection.first() == Some(&PlaceElem::Deref)
        {
            let base = bd.borrowed.local;
            if base != issuer {
                m.entry(issuer).or_default().push(base);
            }
        }
    }
    m
}

struct LoanInvalidatesGenerator<'g, 'tcx> {
    facts: &'g mut Invalidates,
    tcx: TyCtxt<'tcx>,
    body: &'g Body<'tcx>,
    borrow_set: &'g BorrowSet<'tcx>,
    provenance_set: &'g ProvenanceSet,
    location_map: &'g DenseLocationMap,
    /// §NB4-4b-i routing chain (see `build_issued_bases`).
    issued_bases: FxHashMap<Local, Vec<Local>>,
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
        // §NB4-4a-ii: labeled, DELIBERATELY UNCONSUMED (see `AccessKind`). WA retired at 4b-i
        // (vacuous under Foster-unified mutability); the label stays as a dormant hook.
        _kind: AccessKind,
    ) {
        let point_index = self.location_map.point_from_location(location);

        // §NB4-4b-i CROSS-ALIAS ROUTING. Accessing `(*b)` where `b` is a copy/reborrow of `p`
        // is an access to the cell `b` points into, `(*p)` — but `local_map` keys loans by their
        // borrowed base, and `b` is a different `Local` than `p`, so the direct `row(b)` lookup
        // (and `places_conflict`, which bails on differing locals) is BLIND to loans on `(*p)`.
        // Route the access along `b`'s issued-loan chain (`b → p`, iterated to a FIXPOINT so
        // `b2 = b = p` reaches `p` through two hops — a depth-1 walk would leave the blindness one
        // copy deeper), and re-base the accessed place onto each reachable local. This is the
        // issues→borrowed chain, NOT `tree_borrow_local` (which is singleton at round 0). Closes
        // the loan-ISSUING alias class (the S2-6 witness); raw-from-round-0 aliases issue no loans
        // and remain out of scope (S2-5's family, §8-guarded).
        let mut seen: FxHashSet<Local> = FxHashSet::default();
        seen.insert(place.local);
        // Route ONLY a DEREF access `(*b)[…]` — an access THROUGH the pointer, which reaches the
        // pointee `b` shares with its base. A bare-local access `b` (reading/moving the pointer
        // VALUE, e.g. `(*out) = move _2`) does NOT touch the pointee, so it must NOT follow the
        // chain — otherwise re-basing `_2` onto its base invalidates `_2`'s own loan
        // (`store_global` over-invalidation). The original local is always checked (below), so a
        // bare-local access keeps its exact pre-routing semantics.
        if place.projection.first() == Some(&rustc_middle::mir::PlaceElem::Deref) {
            let mut worklist = vec![place.local];
            while let Some(l) = worklist.pop() {
                if let Some(bases) = self.issued_bases.get(&l) {
                    for &base in bases {
                        if seen.insert(base) {
                            worklist.push(base);
                        }
                    }
                }
            }
        }

        for local in seen {
            let Some(borrows_for_base) = self.borrow_set.local_map.row(local) else {
                continue;
            };
            // Re-base the accessed place onto this reachable local: `(*b)[proj]` ⇒ `(*p)[proj]`
            // (b and p hold the same address, so the same projection names the same cell). For
            // `local == place.local` this is `place` itself, so the original access is subsumed.
            let routed = Place {
                local,
                projection: place.projection,
            };
            for loan in borrows_for_base.iter() {
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
                    routed,
                    access_depth,
                    PlaceConflictBias::Overlap,
                ) {
                    self.facts.insert(point_index, loan);
                }
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
