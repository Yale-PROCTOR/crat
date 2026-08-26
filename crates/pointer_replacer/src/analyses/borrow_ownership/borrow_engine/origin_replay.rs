use std::ops::{Deref, DerefMut};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{
    IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};
use rustc_middle::{
    mir::{Local, PlaceElem},
    ty::TyCtxt,
};
use rustc_mir_dataflow::points::PointIndex;
use rustc_span::def_id::LocalDefId;
use smallvec::{SmallVec, smallvec};

use super::{
    PointRequiresMode,
    loan_liveness::{self, EdgeLocation, LocalizedRequires},
};
use crate::{
    analyses::{
        bo_adapter,
        borrow::{
            BorrowInferenceResults, Borrower, GBorrowInferCtxt, Loan, Provenance, ProvenanceOwner,
            ProvenanceSet, StructFieldSlot, borrow_inference,
        },
        borrow_ownership::{
            coherence::SelectedCopyLendLoan,
            export,
            origin_flow::{self, OriginFlowResults},
            slots::SlotOwner,
        },
    },
    utils::rustc::RustProgram,
};

pub(super) struct NativeBorrowContext<'a> {
    pub(super) borrow: GBorrowInferCtxt,
    flows: &'a OriginFlowResults,
}

pub(super) struct NativeInference<'tcx> {
    pub(super) facts: BorrowInferenceResults<'tcx>,
    pub(super) copy_lends: DenseBitSet<Loan>,
    /// §HLZ-PORT (A2). `Some` only under `PointRequiresMode::On`. Deliberately carried HERE and
    /// not on `facts`, so production `BorrowInferenceResults` keeps its type and production's own
    /// consumers keep their behaviour by construction (port-exploration §2.1).
    pub(super) localized_requires: Option<LocalizedRequires>,
    /// §6.4 drop attribution (env-gated, `Some` only under `CRAT_BO_REQUIRER_DROP_OUT`).
    /// Per loan, the provenances reachable from its membership provenance using **`All` edges
    /// only** — i.e. ignoring every located reborrow edge. `All` edges apply at EVERY point, so a
    /// provenance in this set can never be dropped by an edge LOCATION; if a dropped requirer is
    /// NOT in it, the drop is attributable to a located reborrow edge, which A2 places at the
    /// reborrow's own `data.location()`.
    pub(super) all_only_closure: Option<FxHashMap<Loan, DenseBitSet<Provenance>>>,
    /// §8.1 census support (same env gate). The raw MIR CFG over points, and each loan's
    /// reservation point — the two things `extract_conflict_edges` needs to re-derive the
    /// liveness-gated propagation INDEPENDENTLY of the walk that produced the facts.
    pub(super) succ_points: Option<FxHashMap<PointIndex, Vec<PointIndex>>>,
    pub(super) loan_reserve: Option<FxHashMap<Loan, PointIndex>>,
}

pub(crate) fn selected_copy_lend_contains(
    selected: &FxHashSet<SelectedCopyLendLoan>,
    identity: &SelectedCopyLendLoan,
) -> bool {
    selected.contains(identity)
}

impl<'tcx> Deref for NativeInference<'tcx> {
    type Target = BorrowInferenceResults<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.facts
    }
}

impl DerefMut for NativeInference<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.facts
    }
}

impl<'a> NativeBorrowContext<'a> {
    pub(super) fn new<I, J, K, L>(
        program: &RustProgram<'_>,
        flows: &'a OriginFlowResults,
        is_candidate: I,
        is_mutable: K,
    ) -> Self
    where
        I: Fn(LocalDefId) -> J,
        J: Fn(Local) -> bool,
        K: Fn(LocalDefId) -> L,
        L: Fn(Local) -> bool,
    {
        let mut provenances = FxHashMap::default();
        let mut field_users: FxHashMap<StructFieldSlot, FxHashSet<LocalDefId>> =
            FxHashMap::default();

        for f in program.functions.iter().copied() {
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(f)
                .borrow();
            let provenance_set = bo_adapter::provenance_set(&body, is_candidate(f), is_mutable(f));
            for data in provenance_set.provenance_data.iter() {
                if let ProvenanceOwner::Field(field) = data.owner() {
                    field_users.entry(field).or_default().insert(f);
                }
            }
            provenances.insert(f, provenance_set);
        }

        Self {
            borrow: GBorrowInferCtxt {
                provenances,
                lifetime_flows: Default::default(),
                field_users,
            },
            flows,
        }
    }

    pub(super) fn infer<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        f: LocalDefId,
        disabled_fields: &[StructFieldSlot],
        selected_copy_lends: &FxHashSet<SelectedCopyLendLoan>,
    ) -> NativeInference<'tcx> {
        let mut inference = borrow_inference(tcx, f, &self.borrow);
        let mut copy_lends = DenseBitSet::new_empty(inference.borrow_set.loans.len());
        for (loan, data) in inference.borrow_set.loans.iter_enumerated() {
            let borrower = match data.assigned {
                Borrower::Assign(owner) => export::BorrowerKind::Assign {
                    owner: export::OwnerKey::from_owner(owner),
                },
                Borrower::CallArg(callee, arg_index) => export::BorrowerKind::CallArg {
                    callee: callee.local_def_index.as_u32(),
                    arg_index,
                },
            };
            if selected_copy_lend_contains(
                selected_copy_lends,
                &SelectedCopyLendLoan {
                    location: export::location_key(data.location()),
                    borrowed: export::PlaceKey::from_place(data.borrowed),
                    borrower,
                },
            ) {
                copy_lends.insert(loan);
            }
        }
        let provenance_set = self.borrow.provenances.get(&f).unwrap();
        let graph = NativeConstraintGraph::new(
            &inference,
            provenance_set,
            self.flows.get(&f),
            disabled_fields,
        );
        let subset_graph = graph.subset_graph(provenance_set);
        inference.subset_closure = graph.subset_closure(provenance_set, &subset_graph);
        // The landed whole-body relation is computed in BOTH modes: `Off` consumes it, and `On`
        // needs it as the tripwire's reference (and leaves it on `facts` so production's own
        // consumers are untouched).
        inference.requires = graph.requires(&inference, provenance_set, &subset_graph);
        let body = &*tcx.mir_drops_elaborated_and_const_checked(f).borrow();
        let landed_loan_liveness = loan_liveness::compute_loan_liveness(
            tcx,
            body,
            &inference.borrow_set,
            &inference.location_map,
            &inference.provenance_liveness,
            &inference.requires,
            &inference.killed,
        );
        let localized_requires = match PointRequiresMode::current() {
            PointRequiresMode::Off => {
                inference.loan_liveness = landed_loan_liveness;
                None
            }
            PointRequiresMode::On => {
                let (ported_loan_liveness, ported_requires) =
                    loan_liveness::compute_loan_liveness_localized(
                        body,
                        &inference.borrow_set,
                        &inference.location_map,
                        &inference.provenance_liveness,
                        &inference.killed,
                        provenance_set.provenance_data.len(),
                        &graph.subset,
                        &graph.membership,
                    );
                loan_liveness::assert_localized_subset(
                    &landed_loan_liveness,
                    &inference.requires,
                    &ported_loan_liveness,
                    &ported_requires,
                );
                inference.loan_liveness = ported_loan_liveness;
                Some(ported_requires)
            }
        };
        let all_only_closure = if std::env::var_os("CRAT_BO_REQUIRER_DROP_OUT").is_some() {
            let mut all_graph: IndexVec<Provenance, SmallVec<[Provenance; 4]>> =
                IndexVec::from_elem(smallvec![], &provenance_set.provenance_data);
            for &(sub, sup, location) in &graph.subset {
                if matches!(location, EdgeLocation::All) {
                    all_graph[sub].push(sup);
                }
            }
            let mut per_loan = FxHashMap::default();
            for &(loan, provenance) in &graph.membership {
                let mut seen = DenseBitSet::new_empty(provenance_set.provenance_data.len());
                let mut stack = vec![provenance];
                while let Some(p) = stack.pop() {
                    if !seen.insert(p) {
                        continue;
                    }
                    stack.extend_from_slice(&all_graph[p]);
                }
                per_loan.insert(loan, seen);
            }
            Some(per_loan)
        } else {
            None
        };
        let (succ_points, loan_reserve) = if all_only_closure.is_some() {
            let mut succ: FxHashMap<PointIndex, Vec<PointIndex>> = FxHashMap::default();
            for (bb, data) in body.basic_blocks.iter_enumerated() {
                let len = data.statements.len() + data.terminator.is_some() as usize;
                for i in 0..len {
                    let loc = rustc_middle::mir::Location {
                        block: bb,
                        statement_index: i,
                    };
                    let pt = inference.location_map.point_from_location(loc);
                    let outs = if i + 1 < len {
                        vec![inference.location_map.point_from_location(
                            rustc_middle::mir::Location {
                                block: bb,
                                statement_index: i + 1,
                            },
                        )]
                    } else {
                        data.terminator()
                            .successors()
                            .map(|b| {
                                inference.location_map.point_from_location(
                                    rustc_middle::mir::Location {
                                        block: b,
                                        statement_index: 0,
                                    },
                                )
                            })
                            .collect()
                    };
                    succ.insert(pt, outs);
                }
            }
            let reserve = inference
                .borrow_set
                .loans
                .iter_enumerated()
                .map(|(loan, data)| {
                    (
                        loan,
                        inference.location_map.point_from_location(data.location()),
                    )
                })
                .collect();
            (Some(succ), Some(reserve))
        } else {
            (None, None)
        };
        NativeInference {
            facts: inference,
            copy_lends,
            localized_requires,
            all_only_closure,
            succ_points,
            loan_reserve,
        }
    }
}

#[cfg(test)]
mod copy_lend_identity_tests {
    use rustc_hash::FxHashSet;
    use rustc_middle::mir::Local;

    use super::selected_copy_lend_contains;
    use crate::analyses::borrow_ownership::{
        coherence::SelectedCopyLendLoan,
        export::{BorrowerKind, OwnerKey, PlaceKey},
        l2::MirLocationKey,
    };

    #[test]
    fn same_location_companion_is_not_copy_lend() {
        let selected = SelectedCopyLendLoan {
            location: MirLocationKey::new(3, 7),
            borrowed: PlaceKey {
                local: Local::from_u32(1),
                proj: Vec::new(),
            },
            borrower: BorrowerKind::Assign {
                owner: OwnerKey::Local(2),
            },
        };
        let companion = SelectedCopyLendLoan {
            location: selected.location,
            borrowed: PlaceKey {
                local: Local::from_u32(9),
                proj: Vec::new(),
            },
            borrower: selected.borrower,
        };
        let selected_set = FxHashSet::from_iter([selected.clone()]);
        assert!(selected_copy_lend_contains(&selected_set, &selected));
        assert!(
            !selected_copy_lend_contains(&selected_set, &companion),
            "same-location companion must retain Existing loan semantics"
        );
    }
}

#[derive(Default)]
struct NativeConstraintGraph {
    /// §HLZ-PORT (A2): the third component is the edge's program point, or `All` for the
    /// closure-derived depth-0 value flows that have none. `Off` ignores it entirely.
    subset: Vec<(Provenance, Provenance, EdgeLocation)>,
    membership: Vec<(Loan, Provenance)>,
}

impl NativeConstraintGraph {
    fn new(
        inference: &BorrowInferenceResults<'_>,
        provenance_set: &ProvenanceSet,
        origin_flow: Option<&origin_flow::OriginFlowResult>,
        disabled_fields: &[StructFieldSlot],
    ) -> Self {
        let mut graph = Self::default();
        let field_provenances: FxHashMap<_, _> = provenance_set
            .provenance_data
            .iter_enumerated()
            .filter_map(|(provenance, data)| match data.owner() {
                ProvenanceOwner::Field(field) => Some((field, provenance)),
                ProvenanceOwner::Local(_) => None,
            })
            .collect();
        let disabled_fields: FxHashSet<_> = disabled_fields.iter().copied().collect();

        for (loan, data) in inference.borrow_set.loans.iter_enumerated() {
            let Borrower::Assign(owner) = data.assigned else {
                continue;
            };
            let Some(lhs) =
                provenance_for_owner(provenance_set, &field_provenances, &disabled_fields, owner)
            else {
                continue;
            };
            graph.membership.push((loan, lhs));

            let rhs = data.borrowed;
            if !rhs.projection.is_empty()
                && rhs
                    .projection
                    .iter()
                    .all(|projection| matches!(projection, PlaceElem::Deref))
                && let Some(source) = provenance_set.local_data[rhs.local]
            {
                // Loan-derived reborrow: the location is in hand, so this edge is located.
                graph
                    .subset
                    .push((source, lhs, EdgeLocation::Point(data.location())));
            }
        }

        if let Some(origin_flow) = origin_flow {
            for (source, target) in origin_flow.body.depth0_value_flows() {
                let source = slot_owner_to_production(source);
                let target = slot_owner_to_production(target);
                let Some(source) = provenance_for_owner(
                    provenance_set,
                    &field_provenances,
                    &disabled_fields,
                    source,
                ) else {
                    continue;
                };
                let Some(target) = provenance_for_owner(
                    provenance_set,
                    &field_provenances,
                    &disabled_fields,
                    target,
                ) else {
                    continue;
                };
                // A2: `depth0_value_flows` reads the CLOSED matrix (`origin_flow.rs:925-931`), so
                // these are transitive-closure edges with no single location. Emitting them `All`
                // reproduces the landed flow-insensitive behaviour exactly; locating them means
                // touching `origin_flow`, which is A1 and is not authorized here.
                graph.subset.push((source, target, EdgeLocation::All));
            }
        }

        graph
    }

    fn subset_graph(
        &self,
        provenance_set: &ProvenanceSet,
    ) -> IndexVec<Provenance, SmallVec<[Provenance; 4]>> {
        let mut graph = IndexVec::from_elem(smallvec![], &provenance_set.provenance_data);
        for &(sub, sup, _) in &self.subset {
            graph[sub].push(sup);
        }
        graph
    }

    fn subset_closure(
        &self,
        provenance_set: &ProvenanceSet,
        subset_graph: &IndexVec<Provenance, SmallVec<[Provenance; 4]>>,
    ) -> SparseBitMatrix<Provenance, Provenance> {
        let mut answer = SparseBitMatrix::new(provenance_set.provenance_data.len());
        let mut stack = vec![];
        let mut visited = DenseBitSet::new_empty(provenance_set.provenance_data.len());

        for provenance in provenance_set.provenance_data.indices() {
            stack.clear();
            visited.clear();
            stack.push(provenance);
            while let Some(other) = stack.pop() {
                if !visited.insert(other) {
                    continue;
                }
                answer.insert(provenance, other);
                // Preserve production's existing one-hop closure behavior exactly.
                stack.extend_from_slice(&subset_graph[provenance]);
            }
        }
        answer
    }

    fn requires(
        &self,
        inference: &BorrowInferenceResults<'_>,
        provenance_set: &ProvenanceSet,
        subset_graph: &IndexVec<Provenance, SmallVec<[Provenance; 4]>>,
    ) -> SparseBitMatrix<Provenance, Loan> {
        let mut answer = SparseBitMatrix::new(inference.borrow_set.loans.len());
        let mut stack = vec![];
        let mut visited = DenseBitSet::new_empty(provenance_set.provenance_data.len());

        for &(loan, provenance) in &self.membership {
            stack.clear();
            visited.clear();
            stack.push(provenance);
            while let Some(provenance) = stack.pop() {
                if !visited.insert(provenance) {
                    continue;
                }
                answer.insert(provenance, loan);
                stack.extend_from_slice(&subset_graph[provenance]);
            }
        }
        answer
    }
}

fn slot_owner_to_production(owner: SlotOwner) -> ProvenanceOwner {
    match owner {
        SlotOwner::Local(local) => ProvenanceOwner::Local(local),
        SlotOwner::Field(field) => ProvenanceOwner::Field(StructFieldSlot {
            struct_did: field.struct_did,
            field_index: field.field_index,
        }),
    }
}

fn provenance_for_owner(
    provenance_set: &ProvenanceSet,
    field_provenances: &FxHashMap<StructFieldSlot, Provenance>,
    disabled_fields: &FxHashSet<StructFieldSlot>,
    owner: ProvenanceOwner,
) -> Option<Provenance> {
    match owner {
        ProvenanceOwner::Local(local) => provenance_set.local_data[local],
        ProvenanceOwner::Field(field) => {
            if disabled_fields.contains(&field) {
                return None;
            }
            field_provenances.get(&field).copied()
        }
    }
}
