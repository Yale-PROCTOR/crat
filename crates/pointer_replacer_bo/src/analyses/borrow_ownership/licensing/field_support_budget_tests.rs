//! Relay main/387 (R1343-1) §1.5 (c): one fixture per reader class, on the readers themselves -- a
//! guard-summary marker never adds a grant. An absence check counts it as present, a count-based
//! grant as more than one, exact support as nothing.
use std::collections::BTreeMap;

use super::{
    super::{
        fold_member_laws::single_free,
        matched::{CallKey, GuardSet, SourceInstance, TerminalInstance},
        transport::Guard,
    },
    *,
};

fn literal(ordinal: usize) -> EquationId {
    EquationId {
        construction: 0,
        ordinal,
    }
}

fn node(var: u32) -> Node {
    Node {
        construction: 0,
        var,
    }
}

fn call() -> CallKey {
    CallKey {
        construction: 0,
        caller: "caller".to_owned(),
        block: 0,
        statement: 0,
        callee: "callee".to_owned(),
    }
}

fn source(endpoint: usize) -> SourceInstance {
    SourceInstance {
        endpoint: literal(endpoint),
        lineage: SourceLineage::Exact(Vec::new()),
    }
}

fn through_call(target: TerminalTarget) -> TerminalInstance {
    TerminalInstance {
        target,
        lineage: SourceLineage::Exact(vec![call()]),
    }
}

fn exact(pairs: &[(usize, bool)]) -> GuardSet {
    GuardSet::Exact(pairs.iter().map(|&(g, v)| (literal(g), v)).collect())
}

fn free_meet(guards: GuardSet) -> Meet {
    Meet::for_test(
        source(1),
        through_call(TerminalTarget::Free(literal(2))),
        guards,
    )
}

fn output_meet(guards: GuardSet) -> Meet {
    Meet::for_test(
        source(1),
        through_call(TerminalTarget::Output {
            node: node(7),
            ordinal: 3,
        }),
        guards,
    )
}

/// A consumed-output certificate for `output_meet` against `free_meet`, its required free bound to
/// literal 5.
fn certificate() -> super::super::ref_effects::ConsumedOutput {
    super::super::ref_effects::ConsumedOutput {
        call: call(),
        field_key: "field".to_owned(),
        free: free_meet(GuardSet::Summarized).terminal,
        output: output_meet(GuardSet::Summarized).terminal,
        output_path: Vec::new(),
        input: node(10),
        free_operand: node(11),
        retained_output: node(12),
        formal_output: node(13),
        actual_output: node(14),
        split: literal(20),
        entry: literal(21),
        exit: literal(22),
        call_input: literal(23),
        call_output: literal(24),
        required_free: Guard {
            binding: literal(5),
            required: true,
        },
    }
}

/// Absence check (`select_terminal`, "is there a competing meet?"): a competing meet that is a
/// marker counts as present -- another source, or a second free -- and the selection refuses.
#[test]
fn r387_c_absence_a_marker_competitor_is_present() {
    let facts = Facts::default();
    let aliases = BTreeMap::new();
    let chosen = free_meet(exact(&[(5, true)]));
    let other_source = Meet::for_test(
        source(9),
        through_call(TerminalTarget::Free(literal(2))),
        GuardSet::Summarized,
    );
    assert_eq!(
        select_terminal(&facts, &aliases, &[chosen.clone(), other_source], &[]).err(),
        Some(Pending::CompetingTerminal),
        "a marker from another source competes"
    );
    let second_free = Meet::for_test(
        source(1),
        through_call(TerminalTarget::Free(literal(8))),
        GuardSet::Summarized,
    );
    assert_eq!(
        select_terminal(&facts, &aliases, &[chosen.clone(), second_free], &[]).err(),
        Some(Pending::CompetingTerminal),
        "a marker to a second free competes"
    );
    assert!(
        select_terminal(&facts, &aliases, &[chosen], &[]).is_ok(),
        "control: the exact meet alone selects"
    );
}

/// Count-based grant (`single_free`, "exactly one free meet"): a marker counts as two or more,
/// never as one -- a marker standing for many guard sets is not a single responsibility.
#[test]
fn r387_c_count_a_lone_marker_is_not_one_meet() {
    assert!(
        single_free(&[free_meet(GuardSet::Summarized)]).is_err(),
        "a lone marker is not one meet"
    );
    assert!(
        single_free(&[free_meet(exact(&[(5, true)]))]).is_ok(),
        "control: one exact meet is one"
    );
}

/// Exact support (`OutputDischarge::certify`, the output's guards against the free's): a marker on
/// either side yields nothing -- no receipt, so the output stays a competitor.
#[test]
fn r387_c_exact_support_a_marker_certifies_nothing() {
    let free = free_meet(exact(&[(5, true)]));
    let certificate = certificate();
    assert!(
        OutputDischarge::certify(&output_meet(exact(&[(5, true)])), &free, &certificate).is_some(),
        "control: the exact output certifies"
    );
    assert!(
        OutputDischarge::certify(&output_meet(GuardSet::Summarized), &free, &certificate).is_none(),
        "a marker output certifies nothing"
    );
    assert!(
        OutputDischarge::certify(
            &output_meet(exact(&[(5, true)])),
            &free_meet(GuardSet::Summarized),
            &certificate
        )
        .is_none(),
        "a marker free certifies nothing"
    );
}
