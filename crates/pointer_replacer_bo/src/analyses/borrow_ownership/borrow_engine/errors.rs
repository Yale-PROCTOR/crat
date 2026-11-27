// MIRRORED from production `borrow/errors.rs` @ fc3bd4cf (`compute_errors` = loan_liveness ∩
// invalidates). Comment-sync only (NO `include_str!` tripwire): its drift changes conflict edges on
// the fixture suite, so it CANNOT hide from the equivalence differential — tripwires are for leaves
// whose drift can hide (e.g. `places_conflict`), differentials for the rest.
use crate::analyses::borrow::{
    errors::Errors, invalidates::Invalidates, loan_liveness::LoanLiveness,
};

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
