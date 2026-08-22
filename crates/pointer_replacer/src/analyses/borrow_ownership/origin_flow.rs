//! BO-native interprocedural origin-flow derivation.
//!
//! This module mirrors the frozen production `borrow::lifetime_flow` semantics over BO-owned slot
//! and summary types. NB5-O's fine-grained rs-crown differential established equality of every
//! function, ordered slot, subset edge, and unknown-membership entry before the wrapped route was
//! removed from the active BO path.

use std::{cell::Cell, collections::VecDeque};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{
    IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, Const, ConstOperand, ConstValue, HasLocalDecls, Local, Location,
        Operand, Place, PlaceElem, RETURN_PLACE, Rvalue, Statement, StatementKind, Terminator,
        visit::Visitor,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::{DefId, LocalDefId};

use super::{
    origin_summary::{OriginSlot, SignaturePlace, SignatureRoot, SignatureSlot},
    slots::{SlotOwner, StructFieldSlot},
};
use crate::{
    analyses::mir::{CallGraphPostOrder, CallKind, MirFunctionCall, TerminatorExt},
    utils::rustc::RustProgram,
};

pub(crate) const MAX_SIGNATURE_SLOT_DEPTH: u8 = 3;

fn is_direct_raw_ptr_ty(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::RawPtr(..))
}

fn is_borrowing_method(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    !def_id.is_local() && tcx.def_kind(def_id) == rustc_hir::def::DefKind::AssocFn && {
        let name = tcx.item_name(def_id);
        matches!(name.as_str(), "offset" | "as_ptr" | "as_mut_ptr")
    }
}

fn direct_raw_pointer_field_slot<'tcx, D: HasLocalDecls<'tcx>>(
    local_decls: &D,
    place: Place<'tcx>,
) -> Option<(StructFieldSlot, u8, bool)> {
    let mut base_ty = local_decls.local_decls()[place.local].ty;
    let mut deref_depth = 0u8;

    for (index, projection_elem) in place.projection.iter().enumerate() {
        match projection_elem {
            PlaceElem::Deref => {
                deref_depth = deref_depth.checked_add(1)?;
                base_ty = base_ty.builtin_deref(true)?;
            }
            PlaceElem::Field(field, field_ty) if index + 1 == place.projection.len() => {
                let TyKind::Adt(adt_def, _) = base_ty.kind() else {
                    return None;
                };
                if !adt_def.did().is_local() || !adt_def.is_struct() || adt_def.is_union() {
                    return None;
                }
                let TyKind::RawPtr(_, mutability) = field_ty.kind() else {
                    return None;
                };
                return Some((
                    StructFieldSlot {
                        struct_did: adt_def.did().expect_local(),
                        field_index: field.index(),
                    },
                    deref_depth,
                    mutability.is_mut(),
                ));
            }
            PlaceElem::OpaqueCast(_) => {}
            _ => return None,
        }
    }

    None
}

#[derive(Clone, Debug)]
pub(crate) struct NativeOriginSummary {
    pub slots: IndexVec<OriginSlot, SignatureSlot>,
    pub value_flows: SparseBitMatrix<OriginSlot, OriginSlot>,
    pub storage_aliases: SparseBitMatrix<OriginSlot, OriginSlot>,
    pub unknown_targets: DenseBitSet<OriginSlot>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct FieldPlace {
    base: Local,
    deref_depth: u8,
    field: StructFieldSlot,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum OriginOwner {
    Local(Local),
    Field(FieldPlace),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct LocalSlot {
    owner: OriginOwner,
    depth: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct A2State {
    may_originless: DenseBitSet<OriginSlot>,
    modeled_sources: IndexVec<OriginSlot, DenseBitSet<OriginSlot>>,
    unstable_bases: DenseBitSet<OriginSlot>,
}

impl A2State {
    fn all_set(domain_size: usize) -> Self {
        Self {
            may_originless: DenseBitSet::new_filled(domain_size),
            modeled_sources: IndexVec::from_raw(
                (0..domain_size)
                    .map(|_| DenseBitSet::new_empty(domain_size))
                    .collect(),
            ),
            unstable_bases: DenseBitSet::new_empty(domain_size),
        }
    }

    fn clear_as_modeled_entry(&mut self, slot: OriginSlot) {
        self.may_originless.remove(slot);
        self.modeled_sources[slot].clear();
        self.modeled_sources[slot].insert(slot);
    }

    fn join_from(&mut self, other: &Self) -> bool {
        let mut changed = self.may_originless.union(&other.may_originless);
        changed |= self.unstable_bases.union(&other.unstable_bases);
        for slot in self.modeled_sources.indices() {
            changed |= self.modeled_sources[slot].union(&other.modeled_sources[slot]);
        }
        changed
    }

    fn set_originless(&mut self, target: OriginSlot) {
        self.may_originless.insert(target);
        self.modeled_sources[target].clear();
    }

    fn strong_copy(&mut self, target: OriginSlot, sources: &[OriginSlot]) -> bool {
        if sources.is_empty()
            || sources
                .iter()
                .any(|source| self.may_originless.contains(*source))
        {
            self.set_originless(target);
            return false;
        }
        let mut modeled = DenseBitSet::new_empty(self.may_originless.domain_size());
        for &source in sources {
            modeled.union(&self.modeled_sources[source]);
            if modeled.is_empty() {
                modeled.insert(source);
            }
        }
        self.may_originless.remove(target);
        self.modeled_sources[target] = modeled;
        true
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct DerivedPlaceKey {
    local: Local,
    projection: Vec<DerivedPlaceElem>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DerivedPlaceElem {
    Field(usize),
}

#[derive(Clone, Debug)]
pub(crate) struct BodyOriginFlow {
    slots: IndexVec<OriginSlot, LocalSlot>,
    slot_map: FxHashMap<(OriginOwner, u8), OriginSlot>,
    value_flows: SparseBitMatrix<OriginSlot, OriginSlot>,
    storage_aliases: SparseBitMatrix<OriginSlot, OriginSlot>,
    unknown_targets: DenseBitSet<OriginSlot>,
}

#[derive(Clone, Debug)]
pub(crate) struct OriginFlowResult {
    pub summary: NativeOriginSummary,
    pub body: BodyOriginFlow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct A2OpaqueResultGuard {
    pub(crate) function: LocalDefId,
    pub(crate) local: Local,
    pub(crate) depth: u8,
    pub(crate) location: crate::analyses::borrow_ownership::l2::MirLocationKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct A2RestoredSelfOrigin {
    pub(crate) function: LocalDefId,
    pub(crate) slot: SignatureSlot,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct A2Plan {
    pub(crate) opaque_result_guards: Vec<A2OpaqueResultGuard>,
    pub(crate) restored_self_origins: Vec<A2RestoredSelfOrigin>,
    pub(crate) killed_memberships: usize,
    pub(crate) iterations: usize,
}

pub(crate) type OriginFlowResults = FxHashMap<LocalDefId, OriginFlowResult>;

thread_local! {
    /// Per-thread count of full-program native origin-flow fixpoints. **THREAD-LOCAL, not a global
    /// atomic:** rustc test sessions use thread-local compiler globals, and the runs-once test
    /// measures a delta around one driver call on one callback thread.
    pub(crate) static ORIGIN_DERIVATION_COUNT: Cell<usize> = const { Cell::new(0) };
}

pub(crate) fn analyze_program_origin_flow(program: &RustProgram<'_>) -> OriginFlowResults {
    ORIGIN_DERIVATION_COUNT.with(|count| count.set(count.get() + 1));
    let tcx = program.tcx;
    let program_functions: FxHashSet<_> = program.functions.iter().copied().collect();

    let mut results = FxHashMap::default();
    results.reserve(program.functions.len());
    let mut summaries = FxHashMap::default();
    summaries.reserve(program.functions.len());

    for &did in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        let result = empty_origin_flow_result(tcx, &body);
        summaries.insert(did, result.summary.clone());
        results.insert(did, result);
    }

    let call_graph = CallGraphPostOrder::new(program);
    for scc in call_graph.sccs() {
        loop {
            let mut changed = false;

            for &did in scc {
                let did = did.expect_local();
                let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                let result =
                    analyze_body_origin_flow_result(tcx, &body, &summaries, &program_functions);

                if results.get(&did) != Some(&result) {
                    summaries.insert(did, result.summary.clone());
                    results.insert(did, result);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }
    }

    results
}

pub(crate) fn analyze_program_origin_flow_a2(
    program: &RustProgram<'_>,
) -> (OriginFlowResults, A2Plan) {
    let mut flows = analyze_program_origin_flow(program);
    let mut plan = A2Plan {
        iterations: 1,
        ..A2Plan::default()
    };
    for &function in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let ordinary_unknown = flows[&function].summary.unknown_targets.count();
        let result = compute_body_a2(program.tcx, &body, &flows[&function].body);
        plan.killed_memberships +=
            ordinary_unknown.saturating_sub(result.summary.unknown_targets.count());
        plan.opaque_result_guards
            .extend(result.guards.into_iter().map(|(local, depth, location)| {
                A2OpaqueResultGuard {
                    function,
                    local,
                    depth,
                    location: crate::analyses::borrow_ownership::l2::MirLocationKey::new(
                        location.block.as_u32(),
                        location.statement_index,
                    ),
                }
            }));
        plan.restored_self_origins.extend(
            result
                .restored
                .into_iter()
                .map(|slot| A2RestoredSelfOrigin { function, slot }),
        );
        flows
            .get_mut(&function)
            .expect("A2 function result")
            .summary = result.summary;
    }
    plan.opaque_result_guards.sort_by_key(|guard| {
        (
            guard.function.local_def_index.as_u32(),
            guard.location,
            guard.local.as_u32(),
            guard.depth,
        )
    });
    plan.opaque_result_guards.dedup();
    plan.restored_self_origins.sort_by_key(|restored| {
        (
            restored.function.local_def_index.as_u32(),
            match restored.slot.place.root {
                SignatureRoot::Return => 0,
                SignatureRoot::Arg(local) => local.as_u32() + 1,
            },
            restored.slot.place.deref_depth,
            restored.slot.depth,
        )
    });
    plan.restored_self_origins.dedup();
    (flows, plan)
}

fn analyze_body_origin_flow_result<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    callee_summaries: &FxHashMap<LocalDefId, NativeOriginSummary>,
    program_functions: &FxHashSet<LocalDefId>,
) -> OriginFlowResult {
    let mut body_flow = BodyOriginFlow::new(tcx, body);
    let derived_place_sources = compute_derived_place_sources(tcx, body, &body_flow);

    FlowVisitor {
        tcx,
        body,
        flow: &mut body_flow,
        callee_summaries,
        program_functions,
        derived_place_sources,
    }
    .visit_body(body);

    let body_flow = body_flow.closed();
    let summary = body_flow.to_summary(body);

    OriginFlowResult {
        summary,
        body: body_flow,
    }
}

fn empty_origin_flow_result<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> OriginFlowResult {
    let body_flow = BodyOriginFlow::new(tcx, body).closed();
    let summary = body_flow.to_summary(body);
    OriginFlowResult {
        summary,
        body: body_flow,
    }
}

impl PartialEq for NativeOriginSummary {
    fn eq(&self, other: &Self) -> bool {
        self.slots == other.slots
            && same_matrix(&self.value_flows, &other.value_flows)
            && same_matrix(&self.storage_aliases, &other.storage_aliases)
            && self.unknown_targets == other.unknown_targets
    }
}

impl Eq for NativeOriginSummary {}

impl PartialEq for BodyOriginFlow {
    fn eq(&self, other: &Self) -> bool {
        self.slots == other.slots
            && self.slot_map == other.slot_map
            && same_matrix(&self.value_flows, &other.value_flows)
            && same_matrix(&self.storage_aliases, &other.storage_aliases)
            && self.unknown_targets == other.unknown_targets
    }
}

impl Eq for BodyOriginFlow {}

impl PartialEq for OriginFlowResult {
    fn eq(&self, other: &Self) -> bool {
        self.summary == other.summary && self.body == other.body
    }
}

impl Eq for OriginFlowResult {}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct DerivedPlaceSourceState {
    sources: FxHashMap<DerivedPlaceKey, FxHashSet<OriginSlot>>,
}

impl DerivedPlaceSourceState {
    fn union_from(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (key, sources) in &other.sources {
            let target = self.sources.entry(key.clone()).or_default();
            let old_len = target.len();
            target.extend(sources.iter().copied());
            changed |= target.len() != old_len;
        }
        changed
    }

    fn kill_place_prefix(&mut self, place: Place<'_>) {
        let Some(prefix) = derived_place_key_prefix(place) else {
            return;
        };
        self.sources.retain(|key, _| !key.starts_with(&prefix));
    }

    fn insert_sources<I>(&mut self, key: DerivedPlaceKey, sources: I)
    where I: IntoIterator<Item = OriginSlot> {
        let sources = sources.into_iter().collect::<FxHashSet<_>>();
        if sources.is_empty() {
            return;
        }
        self.sources.entry(key).or_default().extend(sources);
    }

    fn sources_for_key(&self, key: &DerivedPlaceKey) -> Vec<OriginSlot> {
        self.sources
            .get(key)
            .map(|sources| sources.iter().copied().collect())
            .unwrap_or_default()
    }
}

impl DerivedPlaceKey {
    fn starts_with(&self, prefix: &Self) -> bool {
        self.local == prefix.local && self.projection.starts_with(&prefix.projection)
    }

    fn rebase_from_prefix(
        &self,
        source_prefix: &Self,
        target_prefix: &Self,
    ) -> Option<DerivedPlaceKey> {
        if !self.starts_with(source_prefix) {
            return None;
        }

        let suffix = &self.projection[source_prefix.projection.len()..];
        let mut projection = target_prefix.projection.clone();
        projection.extend_from_slice(suffix);
        Some(DerivedPlaceKey {
            local: target_prefix.local,
            projection,
        })
    }
}

struct DerivedPlaceDataflow<'flow, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'flow Body<'tcx>,
    flow: &'flow BodyOriginFlow,
}

impl<'flow, 'tcx> DerivedPlaceDataflow<'flow, 'tcx> {
    fn compute(&self) -> FxHashMap<Location, DerivedPlaceSourceState> {
        let mut in_states =
            IndexVec::from_elem(DerivedPlaceSourceState::default(), &self.body.basic_blocks);

        loop {
            let mut changed = false;

            for (block, block_data) in self.body.basic_blocks.iter_enumerated() {
                let mut state = in_states[block].clone();

                for statement in &block_data.statements {
                    self.apply_statement_effect(&mut state, statement);
                }

                if let Some(terminator) = &block_data.terminator {
                    self.apply_terminator_effect(&mut state, terminator);
                    for successor in terminator.successors() {
                        changed |= in_states[successor].union_from(&state);
                    }
                }
            }

            if !changed {
                break;
            }
        }

        let mut by_location = FxHashMap::default();
        for (block, block_data) in self.body.basic_blocks.iter_enumerated() {
            let mut state = in_states[block].clone();

            for (statement_index, statement) in block_data.statements.iter().enumerate() {
                by_location.insert(
                    Location {
                        block,
                        statement_index,
                    },
                    state.clone(),
                );
                self.apply_statement_effect(&mut state, statement);
            }

            if let Some(terminator) = &block_data.terminator {
                by_location.insert(
                    Location {
                        block,
                        statement_index: block_data.statements.len(),
                    },
                    state.clone(),
                );
                self.apply_terminator_effect(&mut state, terminator);
            }
        }

        by_location
    }

    fn apply_statement_effect(
        &self,
        state: &mut DerivedPlaceSourceState,
        statement: &Statement<'tcx>,
    ) {
        let StatementKind::Assign(box (place, rvalue)) = &statement.kind else {
            return;
        };
        self.apply_assign_effect(state, *place, rvalue);
    }

    fn apply_assign_effect(
        &self,
        state: &mut DerivedPlaceSourceState,
        target: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) {
        match rvalue {
            Rvalue::Use(operand)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::ShallowInitBox(operand, _)
            | Rvalue::WrapUnsafeBinder(operand, _) => {
                self.apply_operand_assign_effect(state, target, operand);
            }
            Rvalue::CopyForDeref(place) => {
                self.apply_place_assign_effect(state, target, *place);
            }
            Rvalue::BinaryOp(BinOp::Offset, operands) => {
                self.apply_operand_assign_effect(state, target, &operands.0);
            }
            Rvalue::Ref(..)
            | Rvalue::RawPtr(..)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::Repeat(..)
            | Rvalue::Len(..)
            | Rvalue::BinaryOp(..)
            | Rvalue::NullaryOp(..)
            | Rvalue::UnaryOp(..)
            | Rvalue::Discriminant(..)
            | Rvalue::Aggregate(..) => {
                state.kill_place_prefix(target);
            }
        }
    }

    fn apply_operand_assign_effect(
        &self,
        state: &mut DerivedPlaceSourceState,
        target: Place<'tcx>,
        operand: &Operand<'tcx>,
    ) {
        let before = state.clone();
        state.kill_place_prefix(target);

        let Some(source_place) = operand.place() else {
            return;
        };

        self.copy_derived_descendants(&before, state, target, source_place);
        if let Some(target_key) = derived_place_key(target) {
            state.insert_sources(
                target_key,
                self.place_sources_from_state(&before, source_place),
            );
        }
    }

    fn apply_place_assign_effect(
        &self,
        state: &mut DerivedPlaceSourceState,
        target: Place<'tcx>,
        source: Place<'tcx>,
    ) {
        let before = state.clone();
        state.kill_place_prefix(target);

        self.copy_derived_descendants(&before, state, target, source);
        if let Some(target_key) = derived_place_key(target) {
            state.insert_sources(target_key, self.place_sources_from_state(&before, source));
        }
    }

    fn apply_terminator_effect(
        &self,
        state: &mut DerivedPlaceSourceState,
        terminator: &Terminator<'tcx>,
    ) {
        let Some(call) = terminator.as_call(self.tcx) else {
            return;
        };

        let before = state.clone();
        state.kill_place_prefix(call.destination);

        let Some(arg0) = call.args.first() else {
            return;
        };
        if !is_known_slice_split_return_call(&call.func, self.tcx)
            || !self.operand_is_slice_like_ref(&arg0.node)
            || !place_is_slice_pair_ref(self.body, self.tcx, call.destination)
        {
            return;
        }

        let sources = self.operand_sources_from_state(&before, &arg0.node);
        for field_index in [0, 1] {
            if let Some(key) = derived_field_key(call.destination, field_index) {
                state.insert_sources(key, sources.iter().copied());
            }
        }
    }

    fn copy_derived_descendants(
        &self,
        before: &DerivedPlaceSourceState,
        state: &mut DerivedPlaceSourceState,
        target: Place<'tcx>,
        source: Place<'tcx>,
    ) {
        let Some(source_prefix) = derived_place_key_prefix(source) else {
            return;
        };
        let Some(target_prefix) = derived_place_key_prefix(target) else {
            return;
        };

        for (key, sources) in &before.sources {
            let Some(target_key) = key.rebase_from_prefix(&source_prefix, &target_prefix) else {
                continue;
            };
            state.insert_sources(target_key, sources.iter().copied());
        }
    }

    fn operand_sources_from_state(
        &self,
        state: &DerivedPlaceSourceState,
        operand: &Operand<'tcx>,
    ) -> Vec<OriginSlot> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.place_sources_from_state(state, *place)
            }
            Operand::Constant(_) => vec![],
        }
    }

    fn place_sources_from_state(
        &self,
        state: &DerivedPlaceSourceState,
        place: Place<'tcx>,
    ) -> Vec<OriginSlot> {
        if let Some(slot) = self.flow.slot_for_place(self.body, place, 0) {
            return vec![slot];
        }
        let Some(key) = derived_place_key(place) else {
            return vec![];
        };
        state.sources_for_key(&key)
    }

    fn operand_is_slice_like_ref(&self, operand: &Operand<'tcx>) -> bool {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                is_slice_like_ref_ty(place.ty(self.body, self.tcx).ty)
            }
            Operand::Constant(_) => false,
        }
    }
}

fn compute_derived_place_sources<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    flow: &BodyOriginFlow,
) -> FxHashMap<Location, DerivedPlaceSourceState> {
    DerivedPlaceDataflow { tcx, body, flow }.compute()
}

impl BodyOriginFlow {
    fn new<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Self {
        let mut slots = IndexVec::new();
        let mut slot_map = FxHashMap::default();

        for (local, local_decl) in body.local_decls.iter_enumerated() {
            for depth in 0..pointer_slot_count(local_decl.ty) {
                let owner = OriginOwner::Local(local);
                let slot = slots.push(LocalSlot { owner, depth });
                slot_map.insert((owner, depth), slot);
            }
            for field_place in field_places_for_local(tcx, local, local_decl.ty) {
                let owner = OriginOwner::Field(field_place);
                let slot = slots.push(LocalSlot { owner, depth: 0 });
                slot_map.insert((owner, 0), slot);
            }
        }

        let domain_size = slots.len();
        BodyOriginFlow {
            slots,
            slot_map,
            value_flows: SparseBitMatrix::new(domain_size),
            storage_aliases: SparseBitMatrix::new(domain_size),
            unknown_targets: DenseBitSet::new_empty(domain_size),
        }
    }

    fn slot_for_local(&self, local: Local, depth: u8) -> Option<OriginSlot> {
        self.slot_for_owner(OriginOwner::Local(local), depth)
    }

    fn slot_for_owner(&self, owner: OriginOwner, depth: u8) -> Option<OriginSlot> {
        self.slot_map.get(&(owner, depth)).copied()
    }

    pub(crate) fn depth0_value_flows(&self) -> Vec<(SlotOwner, SlotOwner)> {
        let mut flows = vec![];

        for source in self.value_flows.rows() {
            let source_slot = self.slots[source];
            if source_slot.depth != 0 {
                continue;
            }
            let Some(source_owner) = slot_owner(source_slot.owner) else {
                continue;
            };

            let Some(targets) = self.value_flows.row(source) else {
                continue;
            };

            for target in targets.iter() {
                let target_slot = self.slots[target];
                if target_slot.depth == 0 {
                    let Some(target_owner) = slot_owner(target_slot.owner) else {
                        continue;
                    };
                    flows.push((source_owner, target_owner));
                }
            }
        }

        flows
    }

    /// Phase-1b eligibility's read-only view of the existing flow-insensitive unknown fact.
    /// No second unknown analysis is derived: this projects the closed matrix's exact members
    /// onto the owner/depth vocabulary consumed by construction.
    pub(crate) fn unknown_owner_depths(&self) -> FxHashSet<(SlotOwner, u8)> {
        self.unknown_targets
            .iter()
            .filter_map(|slot| {
                let local_slot = self.slots[slot];
                slot_owner(local_slot.owner).map(|owner| (owner, local_slot.depth))
            })
            .collect()
    }

    fn slot_for_place<'tcx, D: HasLocalDecls<'tcx>>(
        &self,
        local_decls: &D,
        place: Place<'tcx>,
        extra_depth: u8,
    ) -> Option<OriginSlot> {
        if let Some((field, deref_depth, _)) = direct_raw_pointer_field_slot(local_decls, place)
            && extra_depth == 0
        {
            return self.slot_for_owner(
                OriginOwner::Field(FieldPlace {
                    base: place.local,
                    deref_depth,
                    field,
                }),
                0,
            );
        }
        let base_depth = place_deref_depth(place)?;
        let depth = base_depth.checked_add(extra_depth)?;
        self.slot_for_local(place.local, depth)
    }

    fn slot_after(&self, slot: OriginSlot, offset: u8) -> Option<OriginSlot> {
        let local_slot = self.slots[slot];
        self.slot_for_owner(local_slot.owner, local_slot.depth.checked_add(offset)?)
    }

    fn add_flow(&mut self, source: OriginSlot, target: OriginSlot) {
        if source != target {
            self.value_flows.insert(source, target);
        }
    }

    fn add_alias(&mut self, a: OriginSlot, b: OriginSlot) {
        if a == b {
            return;
        }
        self.storage_aliases.insert(a, b);
        self.storage_aliases.insert(b, a);
    }

    fn add_descendant_aliases(&mut self, a: OriginSlot, b: OriginSlot) {
        for offset in 1..=MAX_SIGNATURE_SLOT_DEPTH {
            let Some(a_descendant) = self.slot_after(a, offset) else {
                break;
            };
            let Some(b_descendant) = self.slot_after(b, offset) else {
                break;
            };
            self.add_alias(a_descendant, b_descendant);
        }
    }

    fn mark_unknown(&mut self, target: OriginSlot) {
        self.unknown_targets.insert(target);
    }

    fn mark_unknown_place_slots<'tcx, D: HasLocalDecls<'tcx>>(
        &mut self,
        local_decls: &D,
        place: Place<'tcx>,
        start_depth: u8,
    ) {
        for depth in start_depth..MAX_SIGNATURE_SLOT_DEPTH {
            let Some(slot) = self.slot_for_place(local_decls, place, depth) else {
                break;
            };
            self.mark_unknown(slot);
        }
    }

    fn closed(mut self) -> Self {
        self.storage_aliases = transitive_closure(&self.storage_aliases, self.slots.len());

        let mut combined = SparseBitMatrix::new(self.slots.len());
        union_matrix_into(&mut combined, &self.value_flows);
        union_matrix_into(&mut combined, &self.storage_aliases);
        self.value_flows = transitive_closure(&combined, self.slots.len());

        let mut unknown = self.unknown_targets.clone();
        for source in self.unknown_targets.iter() {
            if let Some(targets) = self.value_flows.row(source) {
                unknown.union(targets);
            }
        }
        self.unknown_targets = unknown;

        self
    }

    fn to_summary(&self, body: &Body<'_>) -> NativeOriginSummary {
        self.to_summary_with_unknown(body, &self.unknown_targets)
    }

    fn to_summary_with_unknown(
        &self,
        body: &Body<'_>,
        internal_unknown: &DenseBitSet<OriginSlot>,
    ) -> NativeOriginSummary {
        let mut slots = IndexVec::new();
        let mut internal_to_summary = FxHashMap::default();

        for local in std::iter::once(RETURN_PLACE).chain(body.args_iter()) {
            let root = if local == RETURN_PLACE {
                SignatureRoot::Return
            } else {
                SignatureRoot::Arg(local)
            };

            for depth in 0..pointer_slot_count(body.local_decls[local].ty) {
                let Some(internal) = self.slot_for_local(local, depth) else {
                    continue;
                };
                let summary = slots.push(SignatureSlot {
                    place: SignaturePlace {
                        root,
                        deref_depth: 0,
                        field: None,
                    },
                    depth,
                });
                internal_to_summary.insert(internal, summary);
            }
        }

        for (slot, local_slot) in self.slots.iter_enumerated() {
            let OriginOwner::Field(field_place) = local_slot.owner else {
                continue;
            };
            let root = if field_place.base == RETURN_PLACE {
                SignatureRoot::Return
            } else if field_place.base.index() <= body.arg_count {
                SignatureRoot::Arg(field_place.base)
            } else {
                continue;
            };
            let summary = slots.push(SignatureSlot {
                place: SignaturePlace {
                    root,
                    deref_depth: field_place.deref_depth,
                    field: Some(field_place.field),
                },
                depth: local_slot.depth,
            });
            internal_to_summary.insert(slot, summary);
        }

        let mut value_flows = SparseBitMatrix::new(slots.len());
        let mut storage_aliases = SparseBitMatrix::new(slots.len());
        let mut unknown_targets = DenseBitSet::new_empty(slots.len());

        for source in self.value_flows.rows() {
            let Some(&summary_source) = internal_to_summary.get(&source) else {
                continue;
            };
            let Some(targets) = self.value_flows.row(source) else {
                continue;
            };
            for target in targets.iter() {
                let Some(&summary_target) = internal_to_summary.get(&target) else {
                    continue;
                };
                if observable_value_target(slots[summary_target]) {
                    value_flows.insert(summary_source, summary_target);
                }
            }
        }

        for source in self.storage_aliases.rows() {
            let Some(&summary_source) = internal_to_summary.get(&source) else {
                continue;
            };
            let Some(targets) = self.storage_aliases.row(source) else {
                continue;
            };
            for target in targets.iter() {
                let Some(&summary_target) = internal_to_summary.get(&target) else {
                    continue;
                };
                storage_aliases.insert(summary_source, summary_target);
            }
        }

        for target in internal_unknown.iter() {
            let Some(&summary_target) = internal_to_summary.get(&target) else {
                continue;
            };
            if observable_value_target(slots[summary_target]) {
                unknown_targets.insert(summary_target);
            }
        }

        NativeOriginSummary {
            slots,
            value_flows,
            storage_aliases,
            unknown_targets,
        }
    }

    fn signature_slot_for_internal(
        &self,
        body: &Body<'_>,
        slot: OriginSlot,
    ) -> Option<SignatureSlot> {
        let local_slot = self.slots[slot];
        match local_slot.owner {
            OriginOwner::Local(local)
                if local == RETURN_PLACE || local.index() <= body.arg_count =>
            {
                Some(SignatureSlot {
                    place: SignaturePlace {
                        root: if local == RETURN_PLACE {
                            SignatureRoot::Return
                        } else {
                            SignatureRoot::Arg(local)
                        },
                        deref_depth: 0,
                        field: None,
                    },
                    depth: local_slot.depth,
                })
            }
            OriginOwner::Field(field)
                if field.base == RETURN_PLACE || field.base.index() <= body.arg_count =>
            {
                Some(SignatureSlot {
                    place: SignaturePlace {
                        root: if field.base == RETURN_PLACE {
                            SignatureRoot::Return
                        } else {
                            SignatureRoot::Arg(field.base)
                        },
                        deref_depth: field.deref_depth,
                        field: Some(field.field),
                    },
                    depth: local_slot.depth,
                })
            }
            _ => None,
        }
    }
}

struct BodyA2Result {
    summary: NativeOriginSummary,
    guards: Vec<(Local, u8, Location)>,
    restored: Vec<SignatureSlot>,
}

fn a2_exact_target<'tcx>(
    flow: &BodyOriginFlow,
    body: &Body<'tcx>,
    state: &A2State,
    place: Place<'tcx>,
) -> Option<OriginSlot> {
    let target = flow.slot_for_place(body, place, 0)?;
    let base_depth = if let Some((_, deref_depth, _)) = direct_raw_pointer_field_slot(body, place) {
        deref_depth
    } else {
        place_deref_depth(place)?
    };
    for depth in 0..base_depth {
        let base = flow.slot_for_local(place.local, depth)?;
        if state.unstable_bases.contains(base) {
            return None;
        }
    }
    Some(target)
}

fn a2_operand_sources<'tcx>(
    flow: &BodyOriginFlow,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Vec<OriginSlot> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            flow.slot_for_place(body, *place, 0).into_iter().collect()
        }
        Operand::Constant(_) => Vec::new(),
    }
}

fn a2_rvalue_sources<'tcx>(
    flow: &BodyOriginFlow,
    body: &Body<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Vec<OriginSlot> {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::Cast(_, operand, _)
        | Rvalue::ShallowInitBox(operand, _)
        | Rvalue::WrapUnsafeBinder(operand, _) => a2_operand_sources(flow, body, operand),
        Rvalue::CopyForDeref(place) => flow.slot_for_place(body, *place, 0).into_iter().collect(),
        Rvalue::BinaryOp(BinOp::Offset, operands) => a2_operand_sources(flow, body, &operands.0),
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
            flow.slot_for_place(body, *place, 0).into_iter().collect()
        }
        _ => Vec::new(),
    }
}

fn a2_merge_input(
    inputs: &mut IndexVec<BasicBlock, Option<A2State>>,
    block: BasicBlock,
    incoming: &A2State,
    pending: &mut VecDeque<BasicBlock>,
) {
    match &mut inputs[block] {
        Some(state) => {
            if state.join_from(incoming) {
                pending.push_back(block);
            }
        }
        slot @ None => {
            *slot = Some(incoming.clone());
            pending.push_back(block);
        }
    }
}

fn compute_body_a2<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    flow: &BodyOriginFlow,
) -> BodyA2Result {
    let domain_size = flow.slots.len();
    let mut entry = A2State::all_set(domain_size);
    for local in body.args_iter() {
        for depth in 0..MAX_SIGNATURE_SLOT_DEPTH {
            let Some(slot) = flow.slot_for_local(local, depth) else {
                break;
            };
            entry.clear_as_modeled_entry(slot);
        }
    }

    let mut inputs = IndexVec::from_elem_n(None, body.basic_blocks.len());
    inputs[BasicBlock::from_usize(0)] = Some(entry);
    let mut pending = VecDeque::from([BasicBlock::from_usize(0)]);
    let mut exit: Option<A2State> = None;
    let mut guards = Vec::new();
    let mut restored = Vec::new();

    while let Some(block) = pending.pop_front() {
        let Some(mut state) = inputs[block].clone() else {
            continue;
        };
        let data = &body.basic_blocks[block];
        for statement in &data.statements {
            let StatementKind::Assign(box (place, rvalue)) = &statement.kind else {
                continue;
            };
            if pointer_slot_count(rvalue.ty(body, tcx)) == 0 {
                continue;
            }
            let sources = a2_rvalue_sources(flow, body, rvalue);
            if let Some(target) = a2_exact_target(flow, body, &state, *place) {
                if sources.is_empty() {
                    state.set_originless(target);
                } else if state.strong_copy(target, &sources)
                    && state.modeled_sources[target].contains(target)
                    && let Some(signature) = flow.signature_slot_for_internal(body, target)
                {
                    restored.push(signature);
                }
                state.unstable_bases.insert(target);
            }
        }

        let terminator = data.terminator();
        let location = Location {
            block,
            statement_index: data.statements.len(),
        };
        match &terminator.kind {
            rustc_middle::mir::TerminatorKind::Return => match &mut exit {
                Some(current) => {
                    current.join_from(&state);
                }
                slot @ None => *slot = Some(state),
            },
            rustc_middle::mir::TerminatorKind::Call {
                destination,
                target,
                ..
            } => {
                let mut normal = state.clone();
                if let Some(slot) = a2_exact_target(flow, body, &normal, *destination) {
                    normal.set_originless(slot);
                    if let LocalSlot {
                        owner: OriginOwner::Local(local),
                        depth,
                    } = flow.slots[slot]
                    {
                        guards.push((local, depth, location));
                    }
                    normal.unstable_bases.insert(slot);
                }
                for successor in terminator.successors() {
                    let edge = if Some(successor) == *target {
                        &normal
                    } else {
                        &state
                    };
                    a2_merge_input(&mut inputs, successor, edge, &mut pending);
                }
            }
            rustc_middle::mir::TerminatorKind::TailCall { .. } => match &mut exit {
                Some(current) => {
                    current.join_from(&state);
                }
                slot @ None => *slot = Some(state),
            },
            _ => {
                for successor in terminator.successors() {
                    a2_merge_input(&mut inputs, successor, &state, &mut pending);
                }
            }
        }
    }

    let mut refined = flow.unknown_targets.clone();
    match exit {
        Some(exit) => {
            refined.intersect(&exit.may_originless);
        }
        None => {}
    }
    restored.sort_by_key(|slot| {
        (
            match slot.place.root {
                SignatureRoot::Return => 0,
                SignatureRoot::Arg(local) => local.as_u32() + 1,
            },
            slot.place.deref_depth,
            slot.place
                .field
                .map(|field| (field.struct_did.local_def_index.as_u32(), field.field_index)),
            slot.depth,
        )
    });
    restored.dedup();
    guards.sort_by_key(|(local, depth, location)| {
        (
            location.block.as_u32(),
            location.statement_index,
            local.as_u32(),
            *depth,
        )
    });
    guards.dedup();
    BodyA2Result {
        summary: flow.to_summary_with_unknown(body, &refined),
        guards,
        restored,
    }
}

fn slot_owner(owner: OriginOwner) -> Option<SlotOwner> {
    match owner {
        OriginOwner::Local(local) => Some(SlotOwner::Local(local)),
        OriginOwner::Field(field_place) => Some(SlotOwner::Field(field_place.field)),
    }
}

fn field_places_for_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    local: Local,
    mut ty: Ty<'tcx>,
) -> Vec<FieldPlace> {
    let mut fields = vec![];
    for deref_depth in 0..=MAX_SIGNATURE_SLOT_DEPTH {
        if let TyKind::Adt(adt_def, args) = ty.kind()
            && adt_def.did().is_local()
            && adt_def.is_struct()
            && !adt_def.is_union()
        {
            for (field_index, field_def) in adt_def.all_fields().enumerate() {
                if is_direct_raw_ptr_ty(field_def.ty(tcx, args)) {
                    fields.push(FieldPlace {
                        base: local,
                        deref_depth,
                        field: StructFieldSlot {
                            struct_did: adt_def.did().expect_local(),
                            field_index,
                        },
                    });
                }
            }
        }

        let Some(pointee) = pointer_pointee_ty(ty) else {
            break;
        };
        ty = pointee;
    }
    fields
}

struct FlowVisitor<'flow, 'summary, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'flow Body<'tcx>,
    flow: &'flow mut BodyOriginFlow,
    callee_summaries: &'summary FxHashMap<LocalDefId, NativeOriginSummary>,
    program_functions: &'summary FxHashSet<LocalDefId>,
    derived_place_sources: FxHashMap<Location, DerivedPlaceSourceState>,
}

impl<'flow, 'summary, 'tcx> FlowVisitor<'flow, 'summary, 'tcx> {
    fn assign_from_operand(
        &mut self,
        target: OriginSlot,
        operand: &Operand<'tcx>,
        location: Location,
    ) {
        let sources = self.operand_slots(operand, location);
        if sources.is_empty() {
            if self.operand_without_modeled_sources_is_unknown(operand) {
                self.flow.mark_unknown(target);
            }
            return;
        }

        for source in sources {
            self.flow.add_flow(source, target);
            self.flow.add_descendant_aliases(source, target);
        }
    }

    fn operand_slots(&self, operand: &Operand<'tcx>, location: Location) -> Vec<OriginSlot> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.place_slots_or_derived(*place, location)
            }
            Operand::Constant(_) => vec![],
        }
    }

    fn place_slots_or_derived(&self, place: Place<'tcx>, location: Location) -> Vec<OriginSlot> {
        if let Some(slot) = self.flow.slot_for_place(self.body, place, 0) {
            return vec![slot];
        }
        self.derived_place_sources(place, location)
    }

    fn derived_place_sources(&self, place: Place<'tcx>, location: Location) -> Vec<OriginSlot> {
        let Some(key) = derived_place_key(place) else {
            return vec![];
        };
        self.derived_place_sources
            .get(&location)
            .and_then(|state| state.sources.get(&key))
            .map(|sources| sources.iter().copied().collect())
            .unwrap_or_default()
    }

    fn operand_is_slice_like_ref(&self, operand: &Operand<'tcx>) -> bool {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                is_slice_like_ref_ty(place.ty(self.body, self.tcx).ty)
            }
            Operand::Constant(_) => false,
        }
    }

    fn operand_without_modeled_sources_is_unknown(&self, operand: &Operand<'tcx>) -> bool {
        match operand {
            Operand::Copy(_) | Operand::Move(_) => true,
            Operand::Constant(constant) => {
                self.constant_without_modeled_sources_is_unknown(constant)
            }
        }
    }

    fn constant_without_modeled_sources_is_unknown(&self, constant: &ConstOperand<'tcx>) -> bool {
        match &constant.const_ {
            Const::Unevaluated(unevaluated, ty) => {
                if unevaluated.promoted.is_some() {
                    return false;
                }
                self.tcx
                    .const_eval_poly(unevaluated.def)
                    .map(|value| self.const_value_without_modeled_sources_is_unknown(&value, *ty))
                    .unwrap_or(true)
            }
            Const::Val(value, ty) => {
                self.const_value_without_modeled_sources_is_unknown(value, *ty)
            }
            Const::Ty(_, _) => true,
        }
    }

    fn const_value_without_modeled_sources_is_unknown(
        &self,
        value: &ConstValue<'tcx>,
        ty: Ty<'tcx>,
    ) -> bool {
        match value {
            ConstValue::Scalar(scalar) => match scalar.try_to_scalar_int() {
                Ok(int) => int.to_bits(int.size()) != 0,
                Err(_) => true,
            },
            ConstValue::Indirect { .. } => pointer_slot_count(ty) > 0,
            ConstValue::ZeroSized | ConstValue::Slice { .. } => false,
        }
    }

    fn place_is_slice_like_ref(&self, place: Place<'tcx>) -> bool {
        is_slice_like_ref_ty(place.ty(self.body, self.tcx).ty)
    }

    fn assign_from_place_address(&mut self, target: OriginSlot, place: Place<'tcx>) {
        match place_deref_depth(place) {
            Some(0) => {
                if let Some(place_slot) = self.flow.slot_for_place(self.body, place, 0)
                    && let Some(target_pointee) = self.flow.slot_after(target, 1)
                {
                    self.flow.add_alias(target_pointee, place_slot);
                }
            }
            Some(deref_depth) => {
                if let Some(source) = self
                    .flow
                    .slot_for_local(place.local, deref_depth.saturating_sub(1))
                {
                    self.flow.add_flow(source, target);
                    self.flow.add_descendant_aliases(source, target);
                }
            }
            None => {
                if let Some(deref_depth) = place_deref_interior_depth(place) {
                    if let Some(source) = self.flow.slot_for_local(place.local, deref_depth - 1) {
                        self.flow.add_flow(source, target);
                    } else {
                        self.flow.mark_unknown(target);
                    }
                } else {
                    self.flow.mark_unknown(target);
                }
            }
        }
    }

    fn apply_known_input_return_call(
        &mut self,
        call: &MirFunctionCall<'_, 'tcx>,
        location: Location,
    ) -> bool {
        let Some(arg0) = call.args.first() else {
            return false;
        };

        if self.apply_known_aggregate_input_return_call(call, &arg0.node) {
            return true;
        }

        let Some(destination) = self.flow.slot_for_place(self.body, call.destination, 0) else {
            return false;
        };

        if is_provenance_preserving_pointer_method(&call.func, self.tcx) {
            self.assign_known_return_from_operand(destination, &arg0.node, location);
            return true;
        }

        if is_known_slice_view_return_call(&call.func, self.tcx)
            && self.place_is_slice_like_ref(call.destination)
        {
            self.assign_known_return_from_operand(destination, &arg0.node, location);
            return true;
        }

        if is_known_slice_index_return_call(&call.func, self.tcx)
            && self.operand_is_slice_like_ref(&arg0.node)
        {
            self.assign_known_return_from_operand(destination, &arg0.node, location);
            return true;
        }

        if is_known_c_string_search_return_call(&call.func, self.tcx) {
            self.assign_known_return_from_operand(destination, &arg0.node, location);
            return true;
        }

        if is_known_memchr_return_call(&call.func, self.tcx)
            && self.operand_is_slice_like_ref(&arg0.node)
        {
            self.assign_known_return_from_operand(destination, &arg0.node, location);
            return true;
        }

        false
    }

    fn apply_known_aggregate_input_return_call(
        &mut self,
        call: &MirFunctionCall<'_, 'tcx>,
        arg0: &Operand<'tcx>,
    ) -> bool {
        if !is_known_slice_split_return_call(&call.func, self.tcx)
            || !self.operand_is_slice_like_ref(arg0)
            || !place_is_slice_pair_ref(self.body, self.tcx, call.destination)
        {
            return false;
        }

        true
    }

    fn assign_known_return_from_operand(
        &mut self,
        target: OriginSlot,
        operand: &Operand<'tcx>,
        location: Location,
    ) {
        let sources = self.operand_slots(operand, location);
        if sources.is_empty() {
            self.flow.mark_unknown(target);
        } else {
            for source in sources {
                self.flow.add_flow(source, target);
            }
        }
    }

    fn apply_call_summary(
        &mut self,
        call: &MirFunctionCall<'_, 'tcx>,
        summary: &NativeOriginSummary,
    ) {
        for source in summary.value_flows.rows() {
            let Some(source_slot) = self.instantiate_signature_slot(call, summary.slots[source])
            else {
                continue;
            };
            let Some(targets) = summary.value_flows.row(source) else {
                continue;
            };
            for target in targets.iter() {
                let Some(target_slot) =
                    self.instantiate_signature_slot(call, summary.slots[target])
                else {
                    continue;
                };
                self.flow.add_flow(source_slot, target_slot);
            }
        }

        for source in summary.storage_aliases.rows() {
            let Some(source_slot) = self.instantiate_signature_slot(call, summary.slots[source])
            else {
                continue;
            };
            let Some(targets) = summary.storage_aliases.row(source) else {
                continue;
            };
            for target in targets.iter() {
                let Some(target_slot) =
                    self.instantiate_signature_slot(call, summary.slots[target])
                else {
                    continue;
                };
                self.flow.add_alias(source_slot, target_slot);
            }
        }

        for target in summary.unknown_targets.iter() {
            if let Some(target_slot) = self.instantiate_signature_slot(call, summary.slots[target])
            {
                self.flow.mark_unknown(target_slot);
            }
        }
    }

    fn instantiate_signature_slot(
        &self,
        call: &MirFunctionCall<'_, 'tcx>,
        slot: SignatureSlot,
    ) -> Option<OriginSlot> {
        match slot.place.root {
            SignatureRoot::Return => {
                self.instantiate_signature_place(call.destination, slot.place, slot.depth)
            }
            SignatureRoot::Arg(local) => {
                let arg_index = local.index().checked_sub(1)?;
                let arg = call.args.get(arg_index)?;
                let place = arg.node.place()?;
                self.instantiate_signature_place(place, slot.place, slot.depth)
            }
        }
    }

    fn instantiate_signature_place(
        &self,
        root_place: Place<'tcx>,
        signature_place: SignaturePlace,
        depth: u8,
    ) -> Option<OriginSlot> {
        if let Some(field) = signature_place.field {
            if depth != 0 {
                return None;
            }
            let root_depth = place_deref_depth(root_place)?;
            return self.flow.slot_for_owner(
                OriginOwner::Field(FieldPlace {
                    base: root_place.local,
                    deref_depth: root_depth.checked_add(signature_place.deref_depth)?,
                    field,
                }),
                0,
            );
        }

        self.flow.slot_for_place(
            self.body,
            root_place,
            signature_place.deref_depth.checked_add(depth)?,
        )
    }

    fn mark_unknown_call_effects(&mut self, call: &MirFunctionCall<'_, 'tcx>) {
        self.flow
            .mark_unknown_place_slots(self.body, call.destination, 0);

        for arg in call.args {
            let Some(place) = arg.node.place() else {
                continue;
            };
            self.flow.mark_unknown_place_slots(self.body, place, 1);
        }
    }
}

impl<'tcx> Visitor<'tcx> for FlowVisitor<'_, '_, 'tcx> {
    fn visit_assign(
        &mut self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        let rvalue_ty = rvalue.ty(self.body, self.tcx);
        if pointer_slot_count(rvalue_ty) == 0 {
            return;
        }

        let Some(target) = self.flow.slot_for_place(self.body, *place, 0) else {
            return;
        };

        match rvalue {
            Rvalue::Use(operand)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::ShallowInitBox(operand, _)
            | Rvalue::WrapUnsafeBinder(operand, _) => {
                self.assign_from_operand(target, operand, location)
            }
            Rvalue::CopyForDeref(place) => {
                for source in self.place_slots_or_derived(*place, location) {
                    self.flow.add_flow(source, target);
                    self.flow.add_descendant_aliases(source, target);
                }
            }
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                self.assign_from_place_address(target, *place);
            }
            Rvalue::ThreadLocalRef(_) => self.flow.mark_unknown(target),
            Rvalue::BinaryOp(BinOp::Offset, operands) => {
                self.assign_from_operand(target, &operands.0, location);
            }
            Rvalue::Repeat(..)
            | Rvalue::Len(..)
            | Rvalue::BinaryOp(..)
            | Rvalue::NullaryOp(..)
            | Rvalue::UnaryOp(..)
            | Rvalue::Discriminant(..)
            | Rvalue::Aggregate(..) => self.flow.mark_unknown(target),
        }
    }

    fn visit_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        let Some(call) = terminator.as_call(self.tcx) else {
            return;
        };

        if self.apply_known_input_return_call(&call, location) {
            return;
        }

        if let CallKind::RustLib(def_id) = &call.func
            && is_borrowing_method(*def_id, self.tcx)
            && let Some(arg0) = call.args.first()
        {
            if let Some(destination) = self.flow.slot_for_place(self.body, call.destination, 0) {
                self.assign_from_operand(destination, &arg0.node, location);
            }
            return;
        }

        if let CallKind::RustLib(def_id) = &call.func
            && is_null_pointer_constructor(*def_id, self.tcx)
        {
            return;
        }

        match &call.func {
            CallKind::FreeStanding(callee) if self.program_functions.contains(callee) => {
                if let Some(summary) = self.callee_summaries.get(callee) {
                    self.apply_call_summary(&call, summary);
                } else {
                    self.mark_unknown_call_effects(&call);
                }
            }
            _ => self.mark_unknown_call_effects(&call),
        }
    }
}

fn observable_value_target(slot: SignatureSlot) -> bool {
    match slot.place.root {
        SignatureRoot::Return => true,
        SignatureRoot::Arg(_) => slot.place.field.is_some() || slot.depth > 0,
    }
}

fn pointer_slot_count(mut ty: Ty<'_>) -> u8 {
    let mut depth = 0;
    while depth < MAX_SIGNATURE_SLOT_DEPTH {
        let Some(pointee) = pointer_pointee_ty(ty) else {
            break;
        };
        depth += 1;
        ty = pointee;
    }
    depth
}

fn pointer_pointee_ty(ty: Ty<'_>) -> Option<Ty<'_>> {
    match ty.kind() {
        TyKind::RawPtr(inner, _) => Some(*inner),
        TyKind::Ref(_, inner, _) => Some(*inner),
        _ => None,
    }
}

fn is_slice_like_ref_ty(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Ref(_, inner, _) => matches!(inner.kind(), TyKind::Slice(_) | TyKind::Array(..)),
        _ => false,
    }
}

fn place_is_slice_pair_ref<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>, place: Place<'tcx>) -> bool {
    is_slice_pair_ref_ty(place.ty(body, tcx).ty)
}

fn is_slice_pair_ref_ty(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Tuple(fields) if fields.len() == 2 => {
            fields.iter().all(|field| is_slice_like_ref_ty(field))
        }
        _ => false,
    }
}

fn is_null_pointer_constructor(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    !def_id.is_local() && {
        let name = tcx.item_name(def_id);
        let name = name.as_str();
        name == "null" || name == "null_mut"
    }
}

fn is_provenance_preserving_pointer_method(func: &CallKind, tcx: TyCtxt<'_>) -> bool {
    let CallKind::RustLib(def_id) = func else {
        return false;
    };
    if def_id.is_local() || tcx.def_kind(*def_id) != rustc_hir::def::DefKind::AssocFn {
        return false;
    }

    let name = tcx.item_name(*def_id);
    let name = name.as_str();
    matches!(
        name,
        "wrapping_offset"
            | "byte_offset"
            | "wrapping_byte_offset"
            | "add"
            | "wrapping_add"
            | "sub"
            | "wrapping_sub"
    )
}

fn is_known_slice_view_return_call(func: &CallKind, tcx: TyCtxt<'_>) -> bool {
    let CallKind::RustLib(def_id) = func else {
        return false;
    };
    if def_id.is_local() {
        return false;
    }

    let name = tcx.item_name(*def_id);
    let name = name.as_str();
    name == "cast_slice"
        || name == "cast_slice_mut"
        || name == "from_raw_parts"
        || name == "from_raw_parts_mut"
}

fn is_known_slice_index_return_call(func: &CallKind, tcx: TyCtxt<'_>) -> bool {
    let CallKind::RustLib(def_id) = func else {
        return false;
    };
    if def_id.is_local() || tcx.def_kind(*def_id) != rustc_hir::def::DefKind::AssocFn {
        return false;
    }

    let name = tcx.item_name(*def_id);
    let name = name.as_str();
    matches!(
        name,
        "index" | "index_mut" | "get_unchecked" | "get_unchecked_mut"
    )
}

fn is_known_slice_split_return_call(func: &CallKind, tcx: TyCtxt<'_>) -> bool {
    let CallKind::RustLib(def_id) = func else {
        return false;
    };
    if def_id.is_local() || tcx.def_kind(*def_id) != rustc_hir::def::DefKind::AssocFn {
        return false;
    }

    let name = tcx.item_name(*def_id);
    let name = name.as_str();
    matches!(
        name,
        "split_at" | "split_at_mut" | "split_at_unchecked" | "split_at_mut_unchecked"
    )
}

fn is_known_c_string_search_return_call(func: &CallKind, tcx: TyCtxt<'_>) -> bool {
    match func {
        CallKind::FreeStanding(def_id) | CallKind::Impl(def_id) => {
            is_known_c_string_search_name(tcx.item_name(def_id.to_def_id()).as_str())
        }
        CallKind::RustLib(def_id) => is_known_c_string_search_name(tcx.item_name(*def_id).as_str()),
        CallKind::LibC(name) => is_known_c_string_search_name(name.as_str()),
        CallKind::Closure | CallKind::Dynamic => false,
    }
}

fn is_known_memchr_return_call(func: &CallKind, tcx: TyCtxt<'_>) -> bool {
    match func {
        CallKind::FreeStanding(def_id) | CallKind::Impl(def_id) => {
            tcx.item_name(def_id.to_def_id()).as_str() == "memchr"
        }
        CallKind::RustLib(def_id) => tcx.item_name(*def_id).as_str() == "memchr",
        CallKind::LibC(name) => name.as_str() == "memchr",
        CallKind::Closure | CallKind::Dynamic => false,
    }
}

fn is_known_c_string_search_name(name: impl PartialEq<&'static str>) -> bool {
    name == "strchr" || name == "strrchr" || name == "strstr"
}

fn place_deref_depth(place: Place<'_>) -> Option<u8> {
    let mut depth = 0u8;
    for projection in place.projection {
        match projection {
            PlaceElem::Deref => {
                depth = depth.checked_add(1)?;
            }
            PlaceElem::OpaqueCast(_) => {}
            _ => return None,
        }
    }
    Some(depth)
}

fn derived_place_key(place: Place<'_>) -> Option<DerivedPlaceKey> {
    let key = derived_place_key_prefix(place)?;
    if key.projection.is_empty() {
        return None;
    }
    Some(key)
}

fn derived_field_key(place: Place<'_>, field_index: usize) -> Option<DerivedPlaceKey> {
    let mut key = derived_place_key_prefix(place)?;
    key.projection.push(DerivedPlaceElem::Field(field_index));
    Some(key)
}

fn derived_place_key_prefix(place: Place<'_>) -> Option<DerivedPlaceKey> {
    let mut projection = vec![];
    for elem in place.projection {
        match elem {
            PlaceElem::Field(field, _) => {
                projection.push(DerivedPlaceElem::Field(field.as_usize()));
            }
            PlaceElem::OpaqueCast(_) => {}
            _ => return None,
        }
    }
    Some(DerivedPlaceKey {
        local: place.local,
        projection,
    })
}

fn place_deref_interior_depth(place: Place<'_>) -> Option<u8> {
    let mut depth = 0u8;
    let mut saw_interior = false;
    for projection in place.projection {
        match projection {
            PlaceElem::Deref if !saw_interior => {
                depth = depth.checked_add(1)?;
            }
            PlaceElem::Field(..)
            | PlaceElem::Index(_)
            | PlaceElem::ConstantIndex { .. }
            | PlaceElem::Subslice { .. }
            | PlaceElem::Downcast(..)
                if depth > 0 =>
            {
                saw_interior = true;
            }
            PlaceElem::OpaqueCast(_) => {}
            _ => return None,
        }
    }
    saw_interior.then_some(depth)
}

fn transitive_closure(
    edges: &SparseBitMatrix<OriginSlot, OriginSlot>,
    domain_size: usize,
) -> SparseBitMatrix<OriginSlot, OriginSlot> {
    let mut closure = SparseBitMatrix::new(domain_size);
    let mut stack = vec![];
    let mut visited = DenseBitSet::new_empty(domain_size);

    for source in (0..domain_size).map(OriginSlot::from_usize) {
        stack.clear();
        visited.clear();

        if let Some(targets) = edges.row(source) {
            stack.extend(targets.iter());
        }

        while let Some(target) = stack.pop() {
            if !visited.insert(target) {
                continue;
            }
            if source != target {
                closure.insert(source, target);
            }
            if let Some(next_targets) = edges.row(target) {
                stack.extend(next_targets.iter());
            }
        }
    }

    closure
}

fn union_matrix_into(
    target: &mut SparseBitMatrix<OriginSlot, OriginSlot>,
    source: &SparseBitMatrix<OriginSlot, OriginSlot>,
) {
    for row in source.rows() {
        if let Some(bits) = source.row(row) {
            target.union_row(row, bits);
        }
    }
}

fn same_matrix(
    lhs: &SparseBitMatrix<OriginSlot, OriginSlot>,
    rhs: &SparseBitMatrix<OriginSlot, OriginSlot>,
) -> bool {
    for row in lhs.rows() {
        if lhs.row(row) != rhs.row(row) {
            return false;
        }
    }
    for row in rhs.rows() {
        if lhs.row(row) != rhs.row(row) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod a2_tests {
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::{mir::Local, ty::TyCtxt};

    use super::*;

    fn program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for owner in tcx
            .hir_crate(())
            .owners
            .iter()
            .filter_map(|owner| owner.as_owner())
        {
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    fn function(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .functions
            .iter()
            .copied()
            .find(|did| program.tcx.item_name(did.to_def_id()).as_str() == name)
            .expect("fixture function")
    }

    fn signature_slot(summary: &NativeOriginSummary, root: SignatureRoot, depth: u8) -> OriginSlot {
        summary
            .slots
            .iter_enumerated()
            .find_map(|(slot, value)| {
                (value.place.root == root
                    && value.place.deref_depth == 0
                    && value.place.field.is_none()
                    && value.depth == depth)
                    .then_some(slot)
            })
            .expect("signature slot")
    }

    fn solved_kind(
        program: &RustProgram<'_>,
        function: LocalDefId,
        local: Local,
        depth: u8,
        opaque_guards: bool,
    ) -> crate::analyses::borrow_ownership::SlotKind {
        use crate::analyses::borrow_ownership::{
            construction::{CopyLendMode, construct_bo_into_a2, verify_bo_construction},
            crate_slots::CrateSlots,
            mutability_facts::MutFacts,
            origins::compute_origins_a2,
            solver::{KindSolver, SlotRef},
        };

        let slots = CrateSlots::build(program);
        let (origins, mut a2) = compute_origins_a2(program);
        if !opaque_guards {
            a2.opaque_result_guards.clear();
        }
        let mutability = MutFacts::from_program(program);
        let solver = KindSolver::new(&slots);
        let construction = construct_bo_into_a2(
            program,
            &slots,
            &origins,
            &a2,
            &mutability,
            &solver,
            CopyLendMode::Baseline,
        )
        .expect("A2 construction");
        let model = verify_bo_construction(
            program,
            &slots,
            &origins,
            &solver,
            &construction,
            &mutability,
        )
        .expect("A2 accepted model");
        let slot = slots.fn_local_slots[&function]
            .slot_for_local_depth(local, depth)
            .expect("kind slot");
        model[&SlotRef::Local(function, slot)]
    }

    const OP: &str = "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; }";

    #[test]
    fn a2_copy_chain_kills_stale_opaque_definition() {
        let code = format!(
            "{OP} unsafe fn f(p: *mut i32) -> *mut i32 {{ \
             let mut q = op(p); q = p; q }}"
        );
        ::utils::compilation::run_compiler_on_str(&code, |tcx| {
            let program = program(tcx);
            let f = function(&program, "f");
            let (flows, _plan) = analyze_program_origin_flow_a2(&program);
            let summary = &flows[&f].summary;
            let ret = signature_slot(summary, SignatureRoot::Return, 0);
            assert!(
                !summary.unknown_targets.contains(ret),
                "A2 must kill the overwritten opaque definition reaching return"
            );
            assert_eq!(
                solved_kind(&program, f, Local::from_usize(1), 0, false),
                crate::analyses::borrow_ownership::SlotKind::Ref,
                "diagnostic: deleting the opaque-temp guard recovers the copy-chain Ref"
            );
            assert_eq!(
                solved_kind(&program, f, Local::from_usize(1), 0, true),
                crate::analyses::borrow_ownership::SlotKind::Ref,
                "copy-chain modeled parameter must recover Ref under A2"
            );
        })
        .unwrap();
    }

    #[test]
    fn a2_restore_after_opaque_recovers_signature_origin() {
        let code = format!(
            "{OP} unsafe fn f(out: *mut *mut i32) {{ \
             let old = *out; *out = op(old); *out = old; }}"
        );
        ::utils::compilation::run_compiler_on_str(&code, |tcx| {
            let program = program(tcx);
            let f = function(&program, "f");
            let (flows, plan) = analyze_program_origin_flow_a2(&program);
            let summary = &flows[&f].summary;
            let out1 = signature_slot(summary, SignatureRoot::Arg(Local::from_usize(1)), 1);
            assert!(!summary.unknown_targets.contains(out1));
            assert!(
                plan.restored_self_origins
                    .iter()
                    .any(|restored| restored.function == f && restored.slot == summary.slots[out1]),
                "restore must carry a typed identity-origin witness"
            );
            assert_eq!(
                solved_kind(&program, f, Local::from_usize(1), 1, false),
                crate::analyses::borrow_ownership::SlotKind::Ref,
                "diagnostic: deleting the opaque-temp guard recovers restored out@1"
            );
            assert_eq!(
                solved_kind(&program, f, Local::from_usize(1), 1, true),
                crate::analyses::borrow_ownership::SlotKind::Ref,
                "restored out@1 must recover Ref under A2"
            );
        })
        .unwrap();
    }

    #[test]
    fn a2_branch_join_keeps_unknown() {
        let code = format!(
            "{OP} unsafe fn f(p: *mut i32, c: bool) -> *mut i32 {{ \
             let q = if c {{ op(p) }} else {{ p }}; q }}"
        );
        ::utils::compilation::run_compiler_on_str(&code, |tcx| {
            let program = program(tcx);
            let f = function(&program, "f");
            let (flows, _) = analyze_program_origin_flow_a2(&program);
            let summary = &flows[&f].summary;
            let ret = signature_slot(summary, SignatureRoot::Return, 0);
            assert!(summary.unknown_targets.contains(ret));
        })
        .unwrap();
    }

    #[test]
    fn a2_opaque_result_temp_stays_guarded() {
        let code = format!(
            "{OP} unsafe fn f(p: *mut i32) -> *mut i32 {{ \
             let mut q = op(p); q = p; q }}"
        );
        ::utils::compilation::run_compiler_on_str(&code, |tcx| {
            let program = program(tcx);
            let (_, plan) = analyze_program_origin_flow_a2(&program);
            assert!(
                !plan.opaque_result_guards.is_empty(),
                "opaque-result guard population is the nonvacuity precondition"
            );
        })
        .unwrap();
    }

    #[test]
    fn a2_reassigned_deref_base_cannot_strong_clear() {
        let code = format!(
            "{OP} unsafe fn f(mut out: *mut *mut i32, other: *mut *mut i32) {{ \
             let old = *out; *out = op(old); out = other; *out = old; }}"
        );
        ::utils::compilation::run_compiler_on_str(&code, |tcx| {
            let program = program(tcx);
            let f = function(&program, "f");
            let (flows, _) = analyze_program_origin_flow_a2(&program);
            let summary = &flows[&f].summary;
            let out1 = signature_slot(summary, SignatureRoot::Arg(Local::from_usize(1)), 1);
            assert!(summary.unknown_targets.contains(out1));
        })
        .unwrap();
    }
}
