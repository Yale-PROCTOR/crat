// MIRRORED from production `borrow/errors.rs` @ fc3bd4cf (`compute_errors` = loan_liveness ∩
// invalidates). Comment-sync only (NO `include_str!` tripwire): its drift changes conflict edges on
// the fixture suite, so it CANNOT hide from the equivalence differential — tripwires are for leaves
// whose drift can hide (e.g. `places_conflict`), differentials for the rest. Only the
// `loan_liveness::LoanLiveness` import is rewired to a local alias (the engine reuses production's
// `loan_liveness` fact BY VALUE and does not fork the loan-liveness stage); the body is verbatim.
use rustc_index::bit_set::SparseBitMatrix;
use rustc_mir_dataflow::points::PointIndex;

use super::{BorrowSet, Loan, invalidates::Invalidates};

// production alias `borrow::loan_liveness::LoanLiveness` (private module) is the same concrete type,
// so `borrow_inference(...).loan_liveness` passes here unchanged.
pub(crate) type LoanLiveness = SparseBitMatrix<PointIndex, Loan>;
pub(crate) type Errors = SparseBitMatrix<PointIndex, Loan>;

pub fn compute_errors(
    borrow_set: &BorrowSet,
    loan_liveness: &LoanLiveness,
    invalidates: &Invalidates,
) -> Errors {
    let mut answer = SparseBitMatrix::new(borrow_set.loans.len());

    for row in loan_liveness.rows() {
        if let (Some(invalidates_at), Some(loan_live_at)) =
            (invalidates.row(row), loan_liveness.row(row))
        {
            answer.union_row(row, loan_live_at);
            answer.intersect_row(row, invalidates_at);
        }
    }

    answer
}
