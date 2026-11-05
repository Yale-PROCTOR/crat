//! Relay main/388 finish-set (R1403-1): `finish`'s per-source dispositions are read from membership
//! sets built once over the review's rows. For a review whose rows exercise every branch, every
//! source's disposition is the old scan's (`terminal_dispositions_by_scan`, the oracle) and the one
//! the branch names.

use std::collections::BTreeMap;

use rustc_middle::mir::Location;
use rustc_span::def_id::CRATE_DEF_ID;

use super::{
    ContextCoverage, CoverageDisposition, EventDisposition, OverlapReason, RetirementConflict,
    RetirementReview, RetirementUnresolved, UnresolvedReason,
    local_outcome::{Demotion, Reason},
    terminal_dispositions, terminal_dispositions_by_scan,
};
use crate::analyses::borrow_ownership::{
    slots::SlotId,
    solver::SlotRef,
    source_events::{SourceCondition, SourceEventKey, SourcePhase, SourceRole},
};

fn key(function: &str) -> SourceEventKey {
    SourceEventKey {
        function: function.to_string(),
        block: 0,
        statement: 0,
        phase: SourcePhase::Statement,
        role: SourceRole::Free,
        storage_local: None,
        condition: SourceCondition::Unconditional,
    }
}

fn unresolved(source: Option<SourceEventKey>) -> RetirementUnresolved {
    RetirementUnresolved {
        source,
        function: None,
        location: None,
        phase: None,
        route: Vec::new(),
        reason: UnresolvedReason::MissingSourceEvent,
    }
}

fn conflict(source: SourceEventKey) -> RetirementConflict {
    RetirementConflict {
        function: CRATE_DEF_ID,
        target: SlotRef::Field(SlotId::from_u32(0)),
        target_key: "target".to_string(),
        source,
        phase: SourcePhase::Statement,
        location: Location::START,
        route: Vec::new(),
        loan: None,
        entry: None,
        overlap: OverlapReason::UnknownObjects,
    }
}

fn demotion(source: SourceEventKey) -> Demotion {
    Demotion {
        source,
        function: CRATE_DEF_ID,
        location: Location::START,
        phase: SourcePhase::Statement,
        route: Vec::new(),
        holder: SlotRef::Field(SlotId::from_u32(0)),
        reason: Reason::InnerLoanMissing { depth: 1 },
        chain: Vec::new(),
    }
}

fn coverage(source: SourceEventKey, disposition: CoverageDisposition) -> ContextCoverage {
    ContextCoverage {
        source,
        function: CRATE_DEF_ID,
        location: Location::START,
        phase: SourcePhase::Statement,
        route: Vec::new(),
        disposition,
    }
}

/// One source per branch, plus the precedences: an unresolved source with a conflict and a
/// Checked row stays Unresolved; a conflicted or demoted source with a Checked row stays Conflict.
fn fixture() -> (RetirementReview, Vec<(SourceEventKey, EventDisposition)>) {
    let mut review = RetirementReview::default();
    review.unresolved.push(unresolved(Some(key("unresolved"))));
    review.conflicts.push(conflict(key("unresolved")));
    review
        .coverage
        .push(coverage(key("unresolved"), CoverageDisposition::Checked));
    review.conflicts.push(conflict(key("conflict")));
    review
        .coverage
        .push(coverage(key("conflict"), CoverageDisposition::Checked));
    review.demotions.push(demotion(key("demotion")));
    review
        .coverage
        .push(coverage(key("demotion"), CoverageDisposition::Checked));
    review
        .coverage
        .push(coverage(key("checked"), CoverageDisposition::Checked));
    review
        .coverage
        .push(coverage(key("not-checked"), CoverageDisposition::Null));
    review.coverage.push(coverage(
        key("not-checked"),
        CoverageDisposition::IrrelevantNoSafeHolder,
    ));
    let expected = vec![
        (key("unresolved"), EventDisposition::Unresolved),
        (key("conflict"), EventDisposition::Conflict),
        (key("demotion"), EventDisposition::Conflict),
        (key("checked"), EventDisposition::CheckedWithoutConflict),
        (key("not-checked"), EventDisposition::Irrelevant),
        (key("no-row"), EventDisposition::Irrelevant),
    ];
    (review, expected)
}

fn check(review: &RetirementReview, expected: &[(SourceEventKey, EventDisposition)]) {
    let sources = expected.iter().map(|(source, _)| source);
    let by_sets = terminal_dispositions(review, sources.clone());
    let by_scan = terminal_dispositions_by_scan(review, sources);
    assert_eq!(by_sets, by_scan, "the sets answer as the scan");
    let expected: BTreeMap<_, _> = expected.iter().cloned().collect();
    assert_eq!(by_sets, expected, "each branch's disposition");
}

#[test]
fn r1403_the_finish_sets_answer_as_the_per_source_scan_on_every_branch() {
    let (review, expected) = fixture();
    check(&review, &expected);

    // A row without a source makes every source Unresolved, a source with no row included.
    let (mut review, expected) = fixture();
    review.unresolved.push(unresolved(None));
    let expected: Vec<_> = expected
        .into_iter()
        .map(|(source, _)| (source, EventDisposition::Unresolved))
        .collect();
    check(&review, &expected);
}
