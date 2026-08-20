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
use rustc_span::def_id::LocalDefId;
use smallvec::{SmallVec, smallvec};

use super::loan_liveness;
use crate::{
    analyses::{
        bo_adapter,
        borrow::{
            BorrowInferenceResults, Borrower, GBorrowInferCtxt, Loan, Provenance, ProvenanceOwner,
            ProvenanceSet, StructFieldSlot, borrow_inference,
        },
        borrow_ownership::{
            export,
            l2::MirLocationKey,
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
        selected_copy_lends: &FxHashSet<MirLocationKey>,
    ) -> NativeInference<'tcx> {
        let mut inference = borrow_inference(tcx, f, &self.borrow);
        let mut copy_lends = DenseBitSet::new_empty(inference.borrow_set.loans.len());
        for (loan, data) in inference.borrow_set.loans.iter_enumerated() {
            if selected_copy_lends.contains(&export::location_key(data.location())) {
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
        inference.requires = graph.requires(&inference, provenance_set, &subset_graph);
        let body = &*tcx.mir_drops_elaborated_and_const_checked(f).borrow();
        inference.loan_liveness = loan_liveness::compute_loan_liveness(
            tcx,
            body,
            &inference.borrow_set,
            &inference.location_map,
            &inference.provenance_liveness,
            &inference.requires,
            &inference.killed,
        );
        NativeInference {
            facts: inference,
            copy_lends,
        }
    }
}

#[derive(Default)]
struct NativeConstraintGraph {
    subset: Vec<(Provenance, Provenance)>,
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
                graph.subset.push((source, lhs));
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
                graph.subset.push((source, target));
            }
        }

        graph
    }

    fn subset_graph(
        &self,
        provenance_set: &ProvenanceSet,
    ) -> IndexVec<Provenance, SmallVec<[Provenance; 4]>> {
        let mut graph = IndexVec::from_elem(smallvec![], &provenance_set.provenance_data);
        for &(sub, sup) in &self.subset {
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
