use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::{DenseBitSet, SparseBitMatrix};
use rustc_middle::mir::{Body, Location};
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};

use super::{
    BorrowSet, ConstraintLocation, Loan, MembershipConstraint, Provenance,
    ProvenanceConstraintGraph, ProvenanceData, ProvenanceSet, SubsetConstraint, killed::Killed,
    provenance_liveness::ProvenanceLiveness,
};

/// The set of program points where a loan is live on entry.
pub(crate) type LoanLiveness = SparseBitMatrix<PointIndex, Loan>;

/// Point-sensitive `requires(provenance, loan, point)` facts.
pub(crate) struct LocalizedRequires {
    rows: FxHashMap<(PointIndex, Provenance), DenseBitSet<Loan>>,
}

impl LocalizedRequires {
    fn new() -> Self {
        Self {
            rows: FxHashMap::default(),
        }
    }

    fn insert(&mut self, point: PointIndex, provenance: Provenance, loan: Loan, loans: usize) {
        self.rows
            .entry((point, provenance))
            .or_insert_with(|| DenseBitSet::new_empty(loans))
            .insert(loan);
    }

    pub fn contains(&self, point: PointIndex, provenance: Provenance, loan: Loan) -> bool {
        self.rows
            .get(&(point, provenance))
            .is_some_and(|loans| loans.contains(loan))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct LocalizedNode {
    provenance: Provenance,
    point: PointIndex,
}

struct LocalizedConstraintGraph {
    point_edges: FxHashMap<LocalizedNode, Vec<Provenance>>,
    logical_edges: FxHashMap<Provenance, Vec<Provenance>>,
}

impl LocalizedConstraintGraph {
    fn new(location_map: &DenseLocationMap, constraints: &ProvenanceConstraintGraph) -> Self {
        let mut point_edges: FxHashMap<LocalizedNode, Vec<Provenance>> = FxHashMap::default();
        let mut logical_edges: FxHashMap<Provenance, Vec<Provenance>> = FxHashMap::default();

        for SubsetConstraint { sup, sub, location } in constraints.subset.iter().copied() {
            match location {
                ConstraintLocation::Point(location) => {
                    let node = LocalizedNode {
                        provenance: sub,
                        point: location_map.point_from_location(location),
                    };
                    point_edges.entry(node).or_default().push(sup);
                }
                ConstraintLocation::All => {
                    logical_edges.entry(sub).or_default().push(sup);
                }
            }
        }

        Self {
            point_edges,
            logical_edges,
        }
    }

    fn same_point_successors(&self, node: LocalizedNode) -> impl Iterator<Item = Provenance> + '_ {
        self.point_edges
            .get(&node)
            .into_iter()
            .flatten()
            .chain(
                self.logical_edges
                    .get(&node.provenance)
                    .into_iter()
                    .flatten(),
            )
            .copied()
    }
}

pub fn compute_loan_liveness<'tcx>(
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    location_map: &DenseLocationMap,
    provenance_liveness: &ProvenanceLiveness,
    killed: &Killed,
    provenance_set: &ProvenanceSet,
    constraints: &ProvenanceConstraintGraph,
) -> (LoanLiveness, LocalizedRequires) {
    let graph = LocalizedConstraintGraph::new(location_map, constraints);
    let mut loan_liveness = LoanLiveness::new(borrow_set.loans.len());
    let mut requires = LocalizedRequires::new();
    let mut visited = FxHashSet::default();
    let mut stack = vec![];

    for MembershipConstraint { loan, provenance } in constraints.membership.iter().copied() {
        visited.clear();
        stack.clear();

        let reserve_point = location_map.point_from_location(borrow_set.loans[loan].location);
        let initial = same_point_closure(
            &graph,
            LocalizedNode {
                provenance,
                point: reserve_point,
            },
            provenance_set.provenance_data.len(),
        );

        // Loans are issued after their reservation location. Starting at successor
        // points prevents a borrow from conflicting with the access that creates it.
        for provenance in initial.iter() {
            for successor in successor_points(body, location_map, reserve_point) {
                if provenance_live_at(provenance_set, provenance_liveness, provenance, successor) {
                    stack.push(LocalizedNode {
                        provenance,
                        point: successor,
                    });
                }
            }
        }

        while let Some(node) = stack.pop() {
            if !visited.insert(node) {
                continue;
            }

            if provenance_live_at(
                provenance_set,
                provenance_liveness,
                node.provenance,
                node.point,
            ) {
                loan_liveness.insert(node.point, loan);
                requires.insert(node.point, node.provenance, loan, borrow_set.loans.len());
            }

            for successor in graph.same_point_successors(node) {
                stack.push(LocalizedNode {
                    provenance: successor,
                    point: node.point,
                });
            }

            if killed[node.point].contains(loan) {
                continue;
            }

            for successor in successor_points(body, location_map, node.point) {
                if provenance_live_at(
                    provenance_set,
                    provenance_liveness,
                    node.provenance,
                    successor,
                ) {
                    stack.push(LocalizedNode {
                        provenance: node.provenance,
                        point: successor,
                    });
                }
            }
        }
    }

    (loan_liveness, requires)
}

fn same_point_closure(
    graph: &LocalizedConstraintGraph,
    start: LocalizedNode,
    provenance_count: usize,
) -> DenseBitSet<Provenance> {
    let mut result = DenseBitSet::new_empty(provenance_count);
    let mut stack = vec![start.provenance];

    while let Some(provenance) = stack.pop() {
        if !result.insert(provenance) {
            continue;
        }
        stack.extend(graph.same_point_successors(LocalizedNode {
            provenance,
            point: start.point,
        }));
    }

    result
}

fn provenance_live_at(
    provenance_set: &ProvenanceSet,
    provenance_liveness: &ProvenanceLiveness,
    provenance: Provenance,
    point: PointIndex,
) -> bool {
    matches!(
        provenance_set.provenance_data[provenance],
        ProvenanceData::PlaceHolder(..)
    ) || provenance_liveness
        .row(point)
        .is_some_and(|live| live.contains(provenance))
}

fn successor_points(
    body: &Body<'_>,
    location_map: &DenseLocationMap,
    point: PointIndex,
) -> Vec<PointIndex> {
    let location = location_map.to_location(point);
    let block = &body.basic_blocks[location.block];

    if location.statement_index < block.statements.len() {
        let successor = Location {
            block: location.block,
            statement_index: location.statement_index + 1,
        };
        return vec![location_map.point_from_location(successor)];
    }

    block
        .terminator()
        .successors()
        .map(|block| {
            location_map.point_from_location(Location {
                block,
                statement_index: 0,
            })
        })
        .collect()
}
