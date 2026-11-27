use rustc_middle::{
    mir::{Body, Location, Statement, Terminator, TerminatorEdges},
    ty::TyCtxt,
};
use rustc_mir_dataflow::{
    Analysis,
    points::{DenseLocationMap, PointIndex},
};

use super::{
    BorrowSet,
    killed::Killed,
    loan_sets::{LoanRows, LoanSet},
    provenance_liveness::ProvenanceLiveness,
    requires::ProvenanceRequiresLoan,
};

/// Loans live on entry at each program point.
pub type LoanLiveness = LoanRows<PointIndex>;

pub fn compute_loan_liveness<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    location_map: &DenseLocationMap,
    provenance_liveness: &ProvenanceLiveness,
    requires: &ProvenanceRequiresLoan,
    killed: &Killed,
) -> LoanLiveness {
    let mut loan_liveness = LoanLiveness::default();

    let mut loan_live_at = LoanLiveAt {
        borrow_set,
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
        for position in 0..bb_len {
            let location = Location {
                block: bb,
                statement_index: position,
            };

            loan_live_at.seek_before_primary_effect(location);
            let liveness = loan_live_at.get();
            if !liveness.is_empty() {
                let point_index = location_map.point_from_location(location);
                loan_liveness.set_row(point_index, liveness.clone());
            }
        }
    }

    loan_liveness
}

pub struct LoanLiveAt<'analysis, 'tcx> {
    borrow_set: &'analysis BorrowSet<'tcx>,
    location_map: &'analysis DenseLocationMap,
    provenance_liveness: &'analysis ProvenanceLiveness,
    requires: &'analysis ProvenanceRequiresLoan,
    killed: &'analysis Killed,
}

impl<'analysis, 'tcx> LoanLiveAt<'analysis, 'tcx> {
    fn apply_location_effect(&mut self, state: &mut LoanSet, location: Location) {
        let point_index = self.location_map.point_from_location(location);

        let killed = &self.killed[point_index];

        if !state.is_empty() {
            let mut requires = LoanSet::default();
            if let Some(live) = self.provenance_liveness.row(point_index) {
                for loans in live
                    .iter()
                    .filter_map(|provenance| self.requires.row(provenance))
                {
                    requires.union(loans);
                }
            }
            state.intersect(&requires);
            state.subtract(killed);
        }

        if let Some(loans) = self.borrow_set.location_map.get(&location) {
            for &loan in loans {
                state.insert(loan);
            }
        }
    }
}

impl<'analysis, 'tcx> Analysis<'tcx> for LoanLiveAt<'analysis, 'tcx> {
    type Direction = rustc_mir_dataflow::Forward;
    type Domain = LoanSet;

    const NAME: &'static str = "loan_live_at";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        LoanSet::default()
    }

    fn initialize_start_block(&self, _: &Body<'tcx>, _: &mut Self::Domain) {}

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
