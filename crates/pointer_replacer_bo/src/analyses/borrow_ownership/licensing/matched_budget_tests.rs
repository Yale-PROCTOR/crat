//! Relay main/387 (R1343-1): the guard-summary marker on synthetic functions, through the relation
//! fixpoint itself. A function is its edges between nodes, each edge carrying at most one guard
//! literal; a call maps the callee's input / output ports to the caller's nodes.
use std::collections::BTreeMap;

use super::*;

fn node(var: u32) -> Node {
    Node {
        construction: 0,
        var,
    }
}

fn literal(ordinal: usize) -> EquationId {
    EquationId {
        construction: 0,
        ordinal,
    }
}

fn edge(from: u32, to: u32, guard: Option<usize>) -> Arc {
    Arc {
        from: node(from),
        to: node(to),
        guards: GuardSet::Exact(guard.map(|g| (literal(g), true)).into_iter().collect()),
        step: Step::Local(Evidence::Phi(literal(guard.unwrap_or(0)))),
    }
}

fn function(inputs: &[u32], outputs: &[u32], edges: Vec<Arc>) -> Function {
    Function {
        edges,
        inputs: inputs.iter().map(|&v| node(v)).collect(),
        outputs: outputs.iter().map(|&v| node(v)).collect(),
        ..Default::default()
    }
}

fn part(formal: u32, actual: u32, ordinal: usize) -> BoundaryPart {
    BoundaryPart {
        guards: Guards::new(),
        construction: 0,
        ordinal,
        binding: BoundaryBinding::Native { matched: 0 },
        formal: node(formal),
        actual: node(actual),
    }
}

fn call_key(caller: &str, callee: &str) -> CallKey {
    CallKey {
        construction: 0,
        caller: caller.to_owned(),
        block: 0,
        statement: 0,
        callee: callee.to_owned(),
    }
}

fn scope(name: &str) -> Scope {
    (0, name.to_owned())
}

/// A scope's relation rows: (exact rows, marker rows).
fn rows(relations: &BTreeMap<Relation, Vec<Step>>, name: &str) -> (usize, usize) {
    relations
        .keys()
        .filter(|row| row.scope == scope(name))
        .fold((0, 0), |(exact, markers), row| {
            if row.guards.is_summarized() {
                (exact, markers + 1)
            } else {
                (exact + 1, markers)
            }
        })
}

/// (a): one input reaching one output port by 15 edges, each with its own literal, is one triple
/// with 15 distinct guard sets -- one past the budget: ONE marker row. With 14 it keeps its rows.
#[test]
fn r387_a_fifteen_guard_sets_collapse_to_one_marker_and_fourteen_stay_exact() {
    let fan = |n: usize, first: usize| {
        function(
            &[1],
            &[2],
            (0..n).map(|i| edge(1, 2, Some(first + i))).collect(),
        )
    };
    let base = BTreeMap::from([
        (scope("wide"), fan(15, 100)),
        (scope("narrow"), fan(14, 200)),
    ]);
    let (_, relations) = MatchedTransport::relation_fixpoint(&base, &BTreeMap::new());
    assert_eq!(
        rows(&relations, "wide"),
        (0, 1),
        "15 distinct guard sets: one marker row"
    );
    assert_eq!(rows(&relations, "narrow"), (14, 0), "14: the exact rows");
}

/// (b): a marker absorbs -- no conflict is detectable through it; exact sets still conflict.
#[test]
fn r387_b_a_marker_absorbs_in_join() {
    let exact = GuardSet::Exact(BTreeMap::from([(literal(1), true)]));
    let conflicting = GuardSet::Exact(BTreeMap::from([(literal(1), false)]));
    assert_eq!(
        join(&exact, &conflicting),
        None,
        "exact sets still conflict"
    );
    assert_eq!(
        join(&GuardSet::Summarized, &exact),
        Some(GuardSet::Summarized)
    );
    assert_eq!(
        join(&conflicting, &GuardSet::Summarized),
        Some(GuardSet::Summarized)
    );
    assert_eq!(
        join_exact(
            &GuardSet::Summarized,
            &BTreeMap::from([(literal(2), false)])
        ),
        Some(GuardSet::Summarized)
    );
}

/// (d): the P02 shape in miniature -- level k calls level k - 1 and then routes the result through
/// three arms, each its own literal, so level k's triple carries 3^(k+1) guard sets: 3, 9, 27.
/// The marker appears where the product passes 14 (level 2), and `top`, which only calls level 2,
/// gets one marker row, not 27.
#[test]
fn r387_d_multiplying_arms_collapse_where_the_product_passes_the_budget() {
    let mut base = BTreeMap::new();
    let mut calls = BTreeMap::new();
    base.insert(
        scope("level0"),
        function(&[0], &[2], (0..3).map(|j| edge(0, 2, Some(j))).collect()),
    );
    for k in 1..=2u32 {
        base.insert(
            scope(&format!("level{k}")),
            function(
                &[10 * k],
                &[10 * k + 2],
                (0..3)
                    .map(|j| edge(10 * k + 1, 10 * k + 2, Some(100 * k as usize + j)))
                    .collect(),
            ),
        );
        calls.insert(
            call_key(&format!("level{k}"), &format!("level{}", k - 1)),
            Call {
                inputs: vec![part(10 * (k - 1), 10 * k, 0)],
                outputs: vec![part(10 * (k - 1) + 2, 10 * k + 1, 1)],
            },
        );
    }
    base.insert(
        scope("top"),
        function(&[30], &[32], vec![edge(31, 32, None)]),
    );
    calls.insert(
        call_key("top", "level2"),
        Call {
            inputs: vec![part(20, 30, 0)],
            outputs: vec![part(22, 31, 1)],
        },
    );
    let (_, relations) = MatchedTransport::relation_fixpoint(&base, &calls);
    assert_eq!(rows(&relations, "level0"), (3, 0));
    assert_eq!(rows(&relations, "level1"), (9, 0));
    assert_eq!(
        rows(&relations, "level2"),
        (0, 1),
        "27 > 14: one marker row"
    );
    assert_eq!(
        rows(&relations, "top"),
        (0, 1),
        "the caller above gets a marker, not 27 rows"
    );
}
