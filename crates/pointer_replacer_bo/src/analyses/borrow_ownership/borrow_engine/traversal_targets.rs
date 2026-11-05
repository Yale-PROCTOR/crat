//! Selected returned-borrow targets; loan identity and reservation stay unchanged.

use rustc_abi::FieldIdx;
use rustc_index::bit_set::SparseBitMatrix;
use rustc_middle::{
    mir::{
        Body, Local, Location, Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind, visit::Visitor,
    },
    ty::{TyCtxt, TyKind},
};

use super::{AccessDepth, Loan, PlaceConflictBias, places_conflict};
use crate::analyses::{
    borrow::{BorrowInferenceResults, Borrower},
    borrow_ownership::{export::ProjKey, ownership_access::PlaceSyntax},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Unsupported {
    DuplicateLoan,
    MissingLoan,
    NotCallArgument,
    ProjectedArgument,
    TargetProjection,
    TargetType,
}

/// The caller authenticates the selected call's proxy-to-owner correspondence.
/// Syntax names the pointer value; one final dereference names its borrowed target.
/// Validate the whole batch before changing any inference facts.
pub(super) fn retarget<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    inference: &mut BorrowInferenceResults<'tcx>,
    targets: &[(Loan, PlaceSyntax)],
) -> Result<(), Unsupported> {
    let mut normalized = Vec::with_capacity(targets.len());
    for (index, (loan, syntax)) in targets.iter().enumerate() {
        if targets[..index].iter().any(|(other, _)| other == loan) {
            return Err(Unsupported::DuplicateLoan);
        }
        let data = inference
            .borrow_set
            .loans
            .get(*loan)
            .ok_or(Unsupported::MissingLoan)?;
        if !matches!(data.assigned, Borrower::CallArg(..)) {
            return Err(Unsupported::NotCallArgument);
        }
        if data.borrowed.projection.len() != 1
            || data.borrowed.projection.first() != Some(&PlaceElem::Deref)
        {
            return Err(Unsupported::ProjectedArgument);
        }
        let original = body
            .local_decls
            .get(data.borrowed.local)
            .ok_or(Unsupported::TargetType)?;
        if !matches!(
            syntax.projection.as_slice(),
            [] | [ProjKey::Field(_)] | [ProjKey::Deref, ProjKey::Field(_)]
        ) {
            return Err(Unsupported::TargetProjection);
        }
        let owner = Local::from_u32(syntax.local);
        let mut ty = body
            .local_decls
            .get(owner)
            .ok_or(Unsupported::TargetType)?
            .ty;
        let mut target = Place::from(owner);
        for projection in &syntax.projection {
            let element = match projection {
                ProjKey::Deref => {
                    ty = match ty.kind() {
                        TyKind::RawPtr(pointee, _) | TyKind::Ref(_, pointee, _) => *pointee,
                        _ => return Err(Unsupported::TargetType),
                    };
                    PlaceElem::Deref
                }
                ProjKey::Field(index) => {
                    let TyKind::Adt(adt, args) = ty.kind() else {
                        return Err(Unsupported::TargetType);
                    };
                    if !adt.is_struct() {
                        return Err(Unsupported::TargetType);
                    }
                    let index = FieldIdx::from_u32(*index);
                    let field = adt
                        .non_enum_variant()
                        .fields
                        .get(index)
                        .ok_or(Unsupported::TargetType)?;
                    ty = field.ty(tcx, args);
                    PlaceElem::Field(index, ty)
                }
                _ => return Err(Unsupported::TargetProjection),
            };
            target = target.project_deeper(&[element], tcx);
        }
        if !matches!(original.ty.kind(), TyKind::RawPtr(..)) || original.ty != ty {
            return Err(Unsupported::TargetType);
        }
        normalized.push((*loan, target.project_deeper(&[PlaceElem::Deref], tcx)));
    }
    if targets.is_empty() {
        return Ok(());
    }
    for &(loan, target) in &normalized {
        inference.borrow_set.loans[loan].borrowed = target;
        for killed in inference.killed.iter_mut() {
            killed.remove(loan);
        }
    }
    let mut local_map = SparseBitMatrix::new(inference.borrow_set.loans.len());
    for (loan, data) in inference.borrow_set.loans.iter_enumerated() {
        local_map.insert(data.borrowed.local, loan);
    }
    inference.borrow_set.local_map = local_map;
    // Adapted from analyses/borrow/killed.rs::KillsCollector: preserve its exact
    // StorageDead/assignment/call-destination law, recomputing selected columns only.
    let target_locals: Vec<_> = normalized
        .iter()
        .map(|(loan, target)| (*loan, target.local))
        .collect();
    TargetKills {
        tcx,
        body,
        inference,
        targets: &target_locals,
    }
    .visit_body(body);
    Ok(())
}

struct TargetKills<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    inference: &'a mut BorrowInferenceResults<'tcx>,
    targets: &'a [(Loan, Local)],
}

impl<'tcx> TargetKills<'_, 'tcx> {
    fn record(&mut self, place: Place<'tcx>, location: Location) {
        let point = self.inference.location_map.point_from_location(location);
        for &(loan, owner) in self.targets {
            if place.local != owner {
                continue;
            }
            if place.projection.is_empty()
                || places_conflict(
                    self.tcx,
                    self.body,
                    self.inference.borrow_set.loans[loan].borrowed,
                    place,
                    AccessDepth::Deep,
                    PlaceConflictBias::NoOverlap,
                )
            {
                self.inference.killed[point].insert(loan);
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for TargetKills<'_, 'tcx> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        if let StatementKind::StorageDead(local) = statement.kind {
            self.record(Place::from(local), location);
        }
        self.super_statement(statement, location);
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        self.record(*place, location);
        self.super_assign(place, rvalue, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { destination, .. } = terminator.kind {
            self.record(destination, location);
        }
        self.super_terminator(terminator, location);
    }
}
