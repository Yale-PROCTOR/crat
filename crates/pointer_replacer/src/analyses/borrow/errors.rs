use rustc_mir_dataflow::points::PointIndex;

use super::{invalidates::Invalidates, loan_liveness::LoanLiveness, loan_sets::LoanRows};

pub type Errors = LoanRows<PointIndex>;

pub fn compute_errors(loan_liveness: &LoanLiveness, invalidates: &Invalidates) -> Errors {
    let mut answer = Errors::default();

    for row in invalidates.rows() {
        if let (Some(invalidates_at), Some(loan_live_at)) =
            (invalidates.row(row), loan_liveness.row(row))
        {
            let mut errors = invalidates_at.clone();
            errors.intersect(loan_live_at);
            answer.set_row(row, errors);
        }
    }

    answer
}
