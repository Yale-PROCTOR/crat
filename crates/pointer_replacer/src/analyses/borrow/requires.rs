use rustc_data_structures::graph::{scc::Sccs, vec_graph::VecGraph};
use rustc_index::IndexVec;
use utils::graph::SccId;

use super::{
    Loan, Provenance, ProvenanceConstraintGraph, ProvenanceSet,
    loan_sets::{LoanRows, LoanSet},
};

pub type ProvenanceRequiresLoan = LoanRows<Provenance>;

pub fn compute_requires(
    provenance_set: &ProvenanceSet,
    constraint_graph: &ProvenanceConstraintGraph,
) -> ProvenanceRequiresLoan {
    propagate_requires(
        provenance_set.provenance_data.len(),
        constraint_graph
            .subset
            .iter()
            .map(|edge| (edge.sub, edge.sup))
            .collect(),
        constraint_graph
            .membership
            .iter()
            .map(|seed| (seed.loan, seed.provenance)),
    )
}

pub fn propagate_requires(
    provenance_count: usize,
    subset_edges: Vec<(Provenance, Provenance)>,
    membership: impl IntoIterator<Item = (Loan, Provenance)>,
) -> ProvenanceRequiresLoan {
    let subset_graph: VecGraph<Provenance> = VecGraph::new(provenance_count, subset_edges);
    let sccs: Sccs<Provenance, SccId> = Sccs::new(&subset_graph);
    let mut required = IndexVec::from_elem_n(LoanSet::default(), sccs.num_sccs());
    for (loan, provenance) in membership {
        required[sccs.scc(provenance)].insert(loan);
    }

    // Every provenance in an SCC requires the same loans. Process sources
    // before their successors so each subset edge needs only one union.
    for scc in required.indices().rev() {
        if required[scc].is_empty() {
            continue;
        }
        for &successor in sccs.successors(scc) {
            let (source, target) = required.pick2_mut(scc, successor);
            target.union(source);
        }
    }

    let mut answer = ProvenanceRequiresLoan::default();
    for index in 0..provenance_count {
        let provenance = Provenance::from_usize(index);
        let loans = &required[sccs.scc(provenance)];
        if !loans.is_empty() {
            answer.set_row(provenance, loans.clone());
        }
    }
    answer
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn membership_propagates_through_cycles_and_successors() {
        let [source, cycle_start, cycle_end, sink, isolated] =
            [0, 1, 2, 3, 4].map(Provenance::from_usize);
        let [first, second, third] = [0, 64, 1_800_000].map(Loan::from_u32);
        let requires = propagate_requires(
            5,
            vec![
                (source, cycle_start),
                (cycle_start, cycle_end),
                (cycle_end, cycle_start),
                (cycle_start, sink),
                (cycle_end, sink),
                (cycle_end, sink),
            ],
            [(first, source), (second, cycle_end), (third, sink)],
        );

        for (provenance, expected) in [
            (source, &[first][..]),
            (cycle_start, &[first, second][..]),
            (cycle_end, &[first, second][..]),
            (sink, &[first, second, third][..]),
        ] {
            assert!(
                requires
                    .row(provenance)
                    .unwrap()
                    .iter()
                    .eq(expected.iter().copied())
            );
        }
        assert!(requires.row(isolated).is_none());
    }
}
