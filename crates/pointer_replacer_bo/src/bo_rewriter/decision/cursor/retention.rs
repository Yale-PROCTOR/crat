//! Destination retention over a supplied, compiler-keyed raw-use graph.
//! No analysis query or inferred call contract. The integrating collector owns
//! edge completeness and the classification of each use.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Verdict {
    NoRetention,
    Unknown,
    Retained,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Use<K> {
    Observe,
    Write,
    Retain,
    Unknown,
    Copy(K),
    LocalAliasReturn(K),
    ImportedAliasReturn(K),
    UnusedImportedAliasReturn,
}

pub(crate) struct Node<K> {
    pub complete: bool,
    pub uses: Vec<Use<K>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Summary<K> {
    pub root: K,
    pub reached: BTreeSet<K>,
    pub retained_at: BTreeSet<K>,
    pub unknown_at: BTreeSet<K>,
    pub writes_at: BTreeSet<K>,
    pub alias_edges: BTreeSet<(K, K)>,
    parents: BTreeMap<K, K>,
}

impl<K: Copy + Ord> Summary<K> {
    pub(crate) fn verdict(&self) -> Verdict {
        if !self.retained_at.is_empty() {
            Verdict::Retained
        } else if !self.unknown_at.is_empty() {
            Verdict::Unknown
        } else {
            Verdict::NoRetention
        }
    }

    pub(crate) fn path_to(&self, sink: K) -> Option<Vec<K>> {
        if !self.reached.contains(&sink) {
            return None;
        }
        let mut path = vec![sink];
        let mut current = sink;
        while current != self.root {
            current = *self.parents.get(&current)?;
            path.push(current);
        }
        path.reverse();
        Some(path)
    }
}

pub(crate) fn summarize<K: Copy + Ord>(root: K, graph: &BTreeMap<K, Node<K>>) -> Summary<K> {
    let mut result = Summary {
        root,
        reached: BTreeSet::from([root]),
        retained_at: BTreeSet::new(),
        unknown_at: BTreeSet::new(),
        writes_at: BTreeSet::new(),
        alias_edges: BTreeSet::new(),
        parents: BTreeMap::new(),
    };
    let mut pending = VecDeque::from([root]);
    // Each supplied node is visited once. Missing nodes remain explicit unknown
    // descendants; cycles cannot suppress either retained sinks or writes.
    while let Some(key) = pending.pop_front() {
        let Some(node) = graph.get(&key) else {
            result.unknown_at.insert(key);
            continue;
        };
        if !node.complete {
            result.unknown_at.insert(key);
        }
        for &usage in &node.uses {
            let child = match usage {
                Use::Observe | Use::UnusedImportedAliasReturn => None,
                Use::Write => {
                    result.writes_at.insert(key);
                    None
                }
                Use::Retain => {
                    result.retained_at.insert(key);
                    None
                }
                Use::Unknown => {
                    result.unknown_at.insert(key);
                    None
                }
                Use::Copy(child) => Some(child),
                Use::LocalAliasReturn(child) => {
                    result.alias_edges.insert((key, child));
                    Some(child)
                }
                Use::ImportedAliasReturn(child) => {
                    // R198-1: even a used child with complete nonretaining
                    // descendants cannot turn this import boundary into T1.
                    result.unknown_at.insert(key);
                    result.alias_edges.insert((key, child));
                    Some(child)
                }
            };
            if let Some(child) = child
                && result.reached.insert(child)
            {
                result.parents.insert(child, key);
                pending.push_back(child);
            }
        }
    }
    result
}
