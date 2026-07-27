use rustc_hash::FxHashMap;
use rustc_index::{
    IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};
use rustc_middle::{
    mir::{Body, Location, Statement, Terminator, TerminatorEdges},
    ty::TyCtxt,
};
use rustc_mir_dataflow::{
    Analysis,
    points::{DenseLocationMap, PointIndex},
};

use crate::analyses::borrow::{BorrowSet, Loan, Provenance};

pub(super) fn compute_loan_liveness<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    location_map: &DenseLocationMap,
    provenance_liveness: &SparseBitMatrix<PointIndex, Provenance>,
    requires: &SparseBitMatrix<Provenance, Loan>,
    killed: &IndexVec<PointIndex, DenseBitSet<Loan>>,
) -> SparseBitMatrix<PointIndex, Loan> {
    let mut loans_at_location: FxHashMap<Location, Vec<Loan>> = FxHashMap::default();
    for (loan, data) in borrow_set.loans.iter_enumerated() {
        loans_at_location
            .entry(data.location())
            .or_default()
            .push(loan);
    }

    let mut loan_liveness = SparseBitMatrix::new(borrow_set.loans.len());
    let mut loan_live_at = LoanLiveAt {
        loans_at_location: &loans_at_location,
        loan_count: borrow_set.loans.len(),
        location_map,
        provenance_liveness,
        requires,
        killed,
    }
    .iterate_to_fixpoint(tcx, body, None)
    .into_results_cursor(body);

    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        loan_live_at.seek_to_block_start(bb);
        let bb_len = bb_data.statements.len() + bb_data.terminator.is_some() as usize;
        for statement_index in 0..bb_len {
            let location = Location {
                block: bb,
                statement_index,
            };
            loan_live_at.seek_before_primary_effect(location);
            let liveness = loan_live_at.get();
            if !liveness.is_empty() {
                loan_liveness.union_row(location_map.point_from_location(location), liveness);
            }
        }
    }

    loan_liveness
}

struct LoanLiveAt<'a> {
    loans_at_location: &'a FxHashMap<Location, Vec<Loan>>,
    loan_count: usize,
    location_map: &'a DenseLocationMap,
    provenance_liveness: &'a SparseBitMatrix<PointIndex, Provenance>,
    requires: &'a SparseBitMatrix<Provenance, Loan>,
    killed: &'a IndexVec<PointIndex, DenseBitSet<Loan>>,
}

impl LoanLiveAt<'_> {
    fn apply_location_effect(&mut self, state: &mut DenseBitSet<Loan>, location: Location) {
        let point = self.location_map.point_from_location(location);
        let killed = &self.killed[point];
        let mut required = DenseBitSet::new_empty(killed.domain_size());

        for provenance in self
            .provenance_liveness
            .row(point)
            .into_iter()
            .flat_map(|row| row.iter())
        {
            if let Some(loans) = self.requires.row(provenance) {
                required.union(loans);
            }
        }

        state.intersect(&required);
        state.subtract(killed);
        if let Some(loans) = self.loans_at_location.get(&location) {
            for &loan in loans {
                state.insert(loan);
            }
        }
    }
}

impl<'tcx> Analysis<'tcx> for LoanLiveAt<'_> {
    type Direction = rustc_mir_dataflow::Forward;
    type Domain = DenseBitSet<Loan>;

    const NAME: &'static str = "bo_native_loan_live_at";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        DenseBitSet::new_empty(self.loan_count)
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, _state: &mut Self::Domain) {}

    fn apply_primary_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        _statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.apply_location_effect(state, location);
    }

    fn apply_primary_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.apply_location_effect(state, location);
        terminator.edges()
    }
}
