use std::collections::{BTreeMap, BTreeSet};

use super::cursor::retention::{Node, Use, Verdict, summarize};

fn node(uses: Vec<Use<u32>>) -> Node<u32> {
    Node {
        complete: true,
        uses,
    }
}

#[test]
fn w12_destination_chain_exposes_retained_sink_despite_nonretaining_source() {
    let graph = BTreeMap::from([
        (1, node(vec![Use::Observe])),
        (2, node(vec![Use::Copy(3)])),
        (3, node(vec![Use::Copy(4)])),
        (4, node(vec![Use::Retain])),
    ]);
    assert_eq!(summarize(1, &graph).verdict(), Verdict::NoRetention);
    let destination = summarize(2, &graph);
    assert_eq!(destination.verdict(), Verdict::Retained);
    assert_eq!(destination.path_to(4), Some(vec![2, 3, 4]));
    assert_eq!(destination.path_to(1), None);
}

#[test]
fn w12_retained_dominates_unknown_branch_independent_of_edge_order() {
    for edges in [
        vec![Use::Copy(3), Use::Copy(4)],
        vec![Use::Copy(4), Use::Copy(3)],
    ] {
        let graph = BTreeMap::from([
            (2, node(edges)),
            (3, node(vec![Use::Unknown])),
            (4, node(vec![Use::Retain])),
        ]);
        let result = summarize(2, &graph);
        assert_eq!(result.verdict(), Verdict::Retained);
        assert_eq!(result.unknown_at, BTreeSet::from([3]));
        assert_eq!(result.retained_at, BTreeSet::from([4]));
    }
}

#[test]
fn w12_missing_or_incomplete_descendant_is_unknown() {
    let mut graph = BTreeMap::from([(2, node(vec![Use::Copy(3)]))]);
    assert_eq!(summarize(2, &graph).unknown_at, BTreeSet::from([3]));
    graph.insert(
        3,
        Node {
            complete: false,
            uses: vec![],
        },
    );
    assert_eq!(summarize(2, &graph).verdict(), Verdict::Unknown);
    graph.insert(3, node(vec![Use::Observe]));
    assert_eq!(summarize(2, &graph).verdict(), Verdict::NoRetention);
    assert_eq!(summarize(99, &graph).verdict(), Verdict::Unknown);
}

#[test]
fn w12_copy_cycle_terminates_and_carries_writes_and_sink_path() {
    let graph = BTreeMap::from([
        (2, node(vec![Use::Copy(3)])),
        (3, node(vec![Use::Copy(2), Use::Write, Use::Copy(4)])),
        (4, node(vec![Use::Retain])),
    ]);
    let result = summarize(2, &graph);
    assert_eq!(result.reached, BTreeSet::from([2, 3, 4]));
    assert_eq!(result.writes_at, BTreeSet::from([3]));
    assert_eq!(result.path_to(4), Some(vec![2, 3, 4]));
    assert_eq!(result.path_to(2), Some(vec![2]));
}

#[test]
fn w12_used_import_alias_return_is_unknown_then_retained_when_child_escapes() {
    let mut graph = BTreeMap::from([
        (2, node(vec![Use::ImportedAliasReturn(3)])),
        (3, node(vec![Use::Observe])),
    ]);
    let result = summarize(2, &graph);
    assert_eq!(result.verdict(), Verdict::Unknown);
    assert_eq!(result.alias_edges, BTreeSet::from([(2, 3)]));
    assert_eq!(result.reached, BTreeSet::from([2, 3]));
    graph.insert(3, node(vec![Use::Retain]));
    assert_eq!(summarize(2, &graph).verdict(), Verdict::Retained);
    graph.insert(2, node(vec![Use::UnusedImportedAliasReturn]));
    assert_eq!(summarize(2, &graph).verdict(), Verdict::NoRetention);
}

#[test]
fn w12_local_alias_return_follows_descendants_without_fabricating_import_uncertainty() {
    let graph = BTreeMap::from([
        (2, node(vec![Use::LocalAliasReturn(3)])),
        (3, node(vec![Use::Observe])),
    ]);
    let result = summarize(2, &graph);
    assert_eq!(result.verdict(), Verdict::NoRetention);
    assert_eq!(result.alias_edges, BTreeSet::from([(2, 3)]));
}
