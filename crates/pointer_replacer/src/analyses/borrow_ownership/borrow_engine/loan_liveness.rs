use rustc_hash::FxHashMap;
use rustc_index::{
    IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};
use rustc_middle::{
    mir::{Body, Location, Statement, Terminator, TerminatorEdges},
    ty::TyCtxt,
};
use rustc_mir_dataflow::{
    Analysis,
    points::{DenseLocationMap, PointIndex},
};

use crate::analyses::borrow::{BorrowSet, Loan, Provenance};

pub(super) fn compute_loan_liveness<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    location_map: &DenseLocationMap,
    provenance_liveness: &SparseBitMatrix<PointIndex, Provenance>,
    requires: &SparseBitMatrix<Provenance, Loan>,
    killed: &IndexVec<PointIndex, DenseBitSet<Loan>>,
) -> SparseBitMatrix<PointIndex, Loan> {
    let mut loans_at_location: FxHashMap<Location, Vec<Loan>> = FxHashMap::default();
    for (loan, data) in borrow_set.loans.iter_enumerated() {
        loans_at_location
            .entry(data.location())
            .or_default()
            .push(loan);
    }

    let mut loan_liveness = SparseBitMatrix::new(borrow_set.loans.len());
    let mut loan_live_at = LoanLiveAt {
        loans_at_location: &loans_at_location,
        loan_count: borrow_set.loans.len(),
        location_map,
        provenance_liveness,
        requires,
        killed,
    }
    .iterate_to_fixpoint(tcx, body, None)
    .into_results_cursor(body);

    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        loan_live_at.seek_to_block_start(bb);
        let bb_len = bb_data.statements.len() + bb_data.terminator.is_some() as usize;
        for statement_index in 0..bb_len {
            let location = Location {
                block: bb,
                statement_index,
            };
            loan_live_at.seek_before_primary_effect(location);
            let liveness = loan_live_at.get();
            if !liveness.is_empty() {
                loan_liveness.union_row(location_map.point_from_location(location), liveness);
            }
        }
    }

    loan_liveness
}

struct LoanLiveAt<'a> {
    loans_at_location: &'a FxHashMap<Location, Vec<Loan>>,
    loan_count: usize,
    location_map: &'a DenseLocationMap,
    provenance_liveness: &'a SparseBitMatrix<PointIndex, Provenance>,
    requires: &'a SparseBitMatrix<Provenance, Loan>,
    killed: &'a IndexVec<PointIndex, DenseBitSet<Loan>>,
}

impl LoanLiveAt<'_> {
    fn apply_location_effect(&mut self, state: &mut DenseBitSet<Loan>, location: Location) {
        let point = self.location_map.point_from_location(location);
        let killed = &self.killed[point];
        let mut required = DenseBitSet::new_empty(killed.domain_size());

        for provenance in self
            .provenance_liveness
            .row(point)
            .into_iter()
            .flat_map(|row| row.iter())
        {
            if let Some(loans) = self.requires.row(provenance) {
                required.union(loans);
            }
        }

        state.intersect(&required);
        state.subtract(killed);
        if let Some(loans) = self.loans_at_location.get(&location) {
            for &loan in loans {
                state.insert(loan);
            }
        }
    }
}

impl<'tcx> Analysis<'tcx> for LoanLiveAt<'_> {
    type Direction = rustc_mir_dataflow::Forward;
    type Domain = DenseBitSet<Loan>;

    const NAME: &'static str = "bo_native_loan_live_at";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        DenseBitSet::new_empty(self.loan_count)
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, _state: &mut Self::Domain) {}

    fn apply_primary_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        _statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.apply_location_effect(state, location);
    }

    fn apply_primary_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.apply_location_effect(state, location);
        terminator.edges()
    }
}

// ===========================================================================================
// §HLZ-PORT (A2) — point-keyed `requires` + fused reachability loan-liveness.
//
// PORTED from Hanliang Zhang's `hlz/flow-sensitive-borrow-inference @ 8d3878a2`
// (`analyses/borrow/loan_liveness.rs` there), adapted to the fork in three ways, each
// deliberate:
//
//   1. It lives HERE, in the fork, and writes a `LocalizedRequires` carried on the fork's own
//      `NativeInference` — production `analyses/borrow/` is not edited, so
//      `borrow::borrow_conflicts` (the D5-independent NB6 validator) keeps its behaviour by
//      construction.
//   2. `provenance_live_at` has NO `PlaceHolder`-is-always-live rule. His version pairs with a
//      `provenance_liveness` repair we do not port; adopting the rule alone would be a
//      TIGHTENING (more live provenances ⇒ more requires ⇒ more errors) on exactly the
//      parameter-shaped code that dominates the corpus. Omitting it is what makes the ported
//      facts a provable pointwise SUBSET of the landed ones (the tripwire below).
//   3. Edge locations are `EdgeLocation`, a fork-local type, because production has no
//      `ConstraintLocation`. Under A2 only loan-derived reborrow edges are `Point`; the
//      closure-derived depth-0 value flows are `All`, since a transitive-closure edge has no
//      single location and locating them means touching `origin_flow` (that is A1).
// ===========================================================================================

use rustc_hash::FxHashSet;

/// Where a subset constraint applies. `All` is the escape hatch for a constraint with no
/// meaningful program point; it behaves exactly as the landed flow-insensitive relation did.
#[derive(Clone, Copy, Debug)]
pub(super) enum EdgeLocation {
    Point(Location),
    All,
}

/// Point-sensitive `requires(point, provenance, loan)`.
pub(super) struct LocalizedRequires {
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

    pub(super) fn contains(&self, point: PointIndex, provenance: Provenance, loan: Loan) -> bool {
        self.rows
            .get(&(point, provenance))
            .is_some_and(|loans| loans.contains(loan))
    }

    /// Every `(point, provenance, loan)` triple held, for the subset tripwire.
    fn triples(&self) -> impl Iterator<Item = (PointIndex, Provenance, Loan)> + '_ {
        self.rows.iter().flat_map(|(&(point, provenance), loans)| {
            loans.iter().map(move |loan| (point, provenance, loan))
        })
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
    fn new(
        location_map: &DenseLocationMap,
        subset: &[(Provenance, Provenance, EdgeLocation)],
    ) -> Self {
        let mut point_edges: FxHashMap<LocalizedNode, Vec<Provenance>> = FxHashMap::default();
        let mut logical_edges: FxHashMap<Provenance, Vec<Provenance>> = FxHashMap::default();

        for &(sub, sup, location) in subset {
            match location {
                EdgeLocation::Point(location) => {
                    let node = LocalizedNode {
                        provenance: sub,
                        point: location_map.point_from_location(location),
                    };
                    point_edges.entry(node).or_default().push(sup);
                }
                EdgeLocation::All => {
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

/// One worklist reachability walk over `(provenance, point)` nodes emitting BOTH facts.
///
/// Union at merges is realized structurally, not by a join operator: `visited` only
/// deduplicates, so a merge point is reached once per predecessor edge and its fact set is the
/// union of the sets arriving on each. Nothing is ever intersected across predecessors, which
/// is why this stays a may-analysis.
pub(super) fn compute_loan_liveness_localized<'tcx>(
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    location_map: &DenseLocationMap,
    provenance_liveness: &SparseBitMatrix<PointIndex, Provenance>,
    killed: &IndexVec<PointIndex, DenseBitSet<Loan>>,
    provenance_count: usize,
    subset: &[(Provenance, Provenance, EdgeLocation)],
    membership: &[(Loan, Provenance)],
) -> (SparseBitMatrix<PointIndex, Loan>, LocalizedRequires) {
    let graph = LocalizedConstraintGraph::new(location_map, subset);
    let mut loan_liveness = SparseBitMatrix::new(borrow_set.loans.len());
    let mut requires = LocalizedRequires::new();
    let mut visited = FxHashSet::default();
    // `bool` = reached by a CFG edge step. Such a node's ENTRY liveness is already established by
    // the edge gate (the source was live on exit), so it records unconditionally; a node reached
    // by an unconditional same-point subset hop still has to prove liveness for itself.
    let mut stack: Vec<(LocalizedNode, bool)> = vec![];

    for &(loan, provenance) in membership {
        visited.clear();
        stack.clear();

        let reserve_point = location_map.point_from_location(borrow_set.loans[loan].location());
        let initial = same_point_closure(
            &graph,
            LocalizedNode {
                provenance,
                point: reserve_point,
            },
            provenance_count,
        );

        // Loans are issued after their reservation location. Starting at successor points
        // prevents a borrow from conflicting with the access that creates it.
        //
        // §HLZ-PORT EDGE GATE (see the note at the bottom of this file): the liveness test is
        // taken at the SOURCE point, not the target, because our `provenance_liveness` holds
        // EXIT liveness. `live_on_exit(q, pt)` is exactly "q is live on the edge out of pt",
        // which is what his entry-liveness test at the target expresses.
        for provenance in initial.iter() {
            if !provenance_live_at(provenance_liveness, provenance, reserve_point) {
                continue;
            }
            for successor in successor_points(body, location_map, reserve_point) {
                stack.push((
                    LocalizedNode {
                        provenance,
                        point: successor,
                    },
                    true,
                ));
            }
        }

        while let Some((node, by_edge)) = stack.pop() {
            if !visited.insert(node) {
                continue;
            }

            if by_edge || provenance_live_at(provenance_liveness, node.provenance, node.point) {
                loan_liveness.insert(node.point, loan);
                requires.insert(node.point, node.provenance, loan, borrow_set.loans.len());
            }

            for successor in graph.same_point_successors(node) {
                stack.push((
                    LocalizedNode {
                        provenance: successor,
                        point: node.point,
                    },
                    false,
                ));
            }

            if killed[node.point].contains(loan) {
                continue;
            }

            // §HLZ-PORT EDGE GATE — same reason as the seed above: gate the CFG step on the
            // SOURCE point's (exit) liveness.
            if provenance_live_at(provenance_liveness, node.provenance, node.point) {
                for successor in successor_points(body, location_map, node.point) {
                    stack.push((
                        LocalizedNode {
                            provenance: node.provenance,
                            point: successor,
                        },
                        true,
                    ));
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

/// NO `PlaceHolder` special case — see the module note above. This reads exactly the same
/// `provenance_liveness` fact the landed `LoanLiveAt` transfer reads at `:80-89`.
fn provenance_live_at(
    provenance_liveness: &SparseBitMatrix<PointIndex, Provenance>,
    provenance: Provenance,
    point: PointIndex,
) -> bool {
    provenance_liveness
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

// ===========================================================================================
// §HLZ-PORT EDGE GATE — why the liveness test sits at the source, not the target
//
// hlz's traversal gates the CFG step on the TARGET point's liveness, and pairs that with a
// `provenance_liveness` repair in the same commit: `seek_before_primary_effect` ->
// `seek_after_primary_effect`, doc comment "live on exit" -> "live on entry"
// (`borrow/provenance_liveness.rs:14`, `:41` pre-hlz; `:14`, `:50-52` on 8d3878a2). The repair
// is not decoration — `MaybeLiveLocals` is a BACKWARD analysis, so "before the primary effect"
// in analysis order is AFTER it in program order, i.e. pre-hlz sampling yields liveness on
// EXIT. Gating on the target's liveness while holding an exit-liveness matrix shortens every
// loan's window by one point at the tail.
//
// We cannot take his repair directly: our production `analyses/borrow/` is byte-frozen for this
// port, and a faithful fork of `compute_provenance_liveness` is impossible without editing it —
// the field branch needs `ProvenanceSet::field_data` and `direct_raw_pointer_field_slots_in_ty`,
// BOTH PRIVATE (`borrow/mod.rs:162`, `:288`).
//
// So the same predicate is expressed on the matrix we already have. For liveness,
//     exit(pt) = ⋃ { entry(s) : s ∈ succ(pt) },
// so testing `live_on_exit(q, pt)` before stepping to `pt'` is his `live_on_entry(q, pt')` test
// — exactly equal where `pt` has one successor, and a UNION (hence more permissive, the
// conservative direction) at a branch. That union is also precisely what the landed dataflow
// did: its `required(pt)` was built from this same exit matrix and applied to every successor.
//
// EXCLUDED, deliberately: hlz's second `provenance_liveness` change — placeholder provenances
// live at every point (`provenance_liveness.rs:24-30`, `:46-48`). It is a genuine tightening on
// parameter-shaped code and is a separate decision with its own measurement (seat, §39
// addendum 15).
//
// The record gate at the node is left as it is: a node arrives either by an edge step (whose
// gate is above) or by an unconditional same-point subset hop, and for the latter the exit
// matrix is also what both downstream consumers intersect against
// (`conflicts.rs:226-230`, `borrow/mod.rs:1273-1277`).
// ===========================================================================================

/// §HLZ-PORT monotonicity tripwire — RELEASE-ACTIVE by design.
///
/// The suite runs `--release`, where `debug_assert!` compiles out, and this project's precedent
/// for a soundness-relevant invariant is a release-active `assert!` (§8 BB3-c). It asserts the
/// claim §2.7 of the port-exploration record argues: the ported facts are a pointwise SUBSET of
/// the landed ones, per round and same input. A FIRE IS A STOP, not a fix — it means the port
/// added a fact the landed relation did not hold, which the placeholder-omission argument says
/// is impossible.
///
/// Disable with `CRAT_BO_POINT_REQUIRES_TRIPWIRE=off` (its cost is a second loan-liveness
/// computation per function); any measurement taken with it off must say so.
pub(super) fn assert_localized_subset(
    landed_loan_liveness: &SparseBitMatrix<PointIndex, Loan>,
    landed_requires: &SparseBitMatrix<Provenance, Loan>,
    ported_loan_liveness: &SparseBitMatrix<PointIndex, Loan>,
    ported_requires: &LocalizedRequires,
) {
    if matches!(
        std::env::var("CRAT_BO_POINT_REQUIRES_TRIPWIRE").as_deref(),
        Ok("off") | Ok("0")
    ) {
        return;
    }
    for point in ported_loan_liveness.rows() {
        let Some(ported) = ported_loan_liveness.row(point) else {
            continue;
        };
        for loan in ported.iter() {
            assert!(
                landed_loan_liveness
                    .row(point)
                    .is_some_and(|landed| landed.contains(loan)),
                "§HLZ-PORT subset tripwire: ported loan_liveness holds {loan:?} at {point:?} \
                 where the landed engine does not — the port must only ever REMOVE facts"
            );
        }
    }
    for (point, provenance, loan) in ported_requires.triples() {
        assert!(
            landed_requires
                .row(provenance)
                .is_some_and(|loans| loans.contains(loan)),
            "§HLZ-PORT subset tripwire: ported requires holds ({point:?}, {provenance:?}, \
             {loan:?}) where the landed whole-body relation does not"
        );
    }
}
