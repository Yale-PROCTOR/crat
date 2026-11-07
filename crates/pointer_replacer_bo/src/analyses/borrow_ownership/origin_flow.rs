//! BO-native interprocedural origin-flow derivation.
//!
//! Uses BO-owned slots and summaries, with explicit foreign pointer-return contracts and
//! conservative byte-write effects. The legacy lifetime-flow derivation remains a differential
//! oracle for their shared language fragment.

use std::cell::Cell;
#[cfg(test)]
use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{
    IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};
#[cfg(test)]
use rustc_middle::mir::BasicBlock;
use rustc_middle::{
    mir::{
        AggregateKind, BinOp, Body, Const, ConstOperand, ConstValue, HasLocalDecls, Local,
        Location, Operand, Place, PlaceElem, RETURN_PLACE, Rvalue, Statement, StatementKind,
        Terminator, visit::Visitor,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::{DefId, LocalDefId};

use super::{
    boundary_table::pointer_return_contract,
    origin_summary::{
        FieldPath, FieldStep, MAX_FIELD_PATH_DEPTH, OriginSlot, SignaturePlace, SignatureRoot,
        SignatureSlot,
    },
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

fn field_place_for_place<'tcx, D: HasLocalDecls<'tcx>>(
    local_decls: &D,
    place: Place<'tcx>,
) -> Option<(FieldPlace, u8)> {
    let mut base_ty = local_decls.local_decls()[place.local].ty;
    let mut deref_depth = 0u8;
    let mut steps = Vec::new();

    for projection_elem in place.projection {
        match projection_elem {
            PlaceElem::Deref => {
                deref_depth = deref_depth.checked_add(1)?;
                base_ty = base_ty.builtin_deref(true)?;
            }
            PlaceElem::Field(field, field_ty) => {
                let TyKind::Adt(adt_def, _) = base_ty.kind() else {
                    return None;
                };
                if !adt_def.did().is_local() || !adt_def.is_struct() || adt_def.is_union() {
                    return None;
                }
                steps.push(FieldStep {
                    deref_depth,
                    field: StructFieldSlot {
                        struct_did: adt_def.did().expect_local(),
                        field_index: field.index(),
                    },
                });
                base_ty = field_ty;
                deref_depth = 0;
            }
            PlaceElem::OpaqueCast(_) => {}
            _ => return None,
        }
    }

    Some((FieldPlace::from_steps(place.local, steps)?, deref_depth))
}

#[derive(Clone, Debug)]
pub(crate) struct NativeOriginSummary {
    pub slots: IndexVec<OriginSlot, SignatureSlot>,
    pub value_flows: SparseBitMatrix<OriginSlot, OriginSlot>,
    pub storage_aliases: SparseBitMatrix<OriginSlot, OriginSlot>,
    pointee_copies: SparseBitMatrix<OriginSlot, OriginSlot>,
    stores: SparseBitMatrix<OriginSlot, OriginSlot>,
    written_slots: DenseBitSet<OriginSlot>,
    pub unknown_targets: DenseBitSet<OriginSlot>,
    pub cutoff_targets: DenseBitSet<OriginSlot>,
    pub cutoff_writes: DenseBitSet<OriginSlot>,
    written_pointees: DenseBitSet<OriginSlot>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct FieldPlace {
    base: Local,
    parents: FieldPath,
    deref_depth: u8,
    field: StructFieldSlot,
}

impl FieldPlace {
    fn steps(&self) -> impl Iterator<Item = FieldStep> + '_ {
        self.parents.iter().chain(std::iter::once(FieldStep {
            deref_depth: self.deref_depth,
            field: self.field,
        }))
    }

    fn from_steps(base: Local, steps: impl IntoIterator<Item = FieldStep>) -> Option<Self> {
        let mut steps = steps.into_iter();
        let mut last = steps.next()?;
        let mut derefs = u16::from(last.deref_depth);
        let mut parents = FieldPath::default();
        for step in steps {
            parents.push(last)?;
            derefs += u16::from(step.deref_depth);
            last = step;
        }
        if derefs > u16::from(MAX_SIGNATURE_SLOT_DEPTH) {
            return None;
        }
        Some(Self {
            base,
            parents,
            deref_depth: last.deref_depth,
            field: last.field,
        })
    }

    fn under(self, root: LocalSlot) -> Option<Self> {
        let mut steps = self.steps();
        let mut first = steps.next()?;
        first.deref_depth = first.deref_depth.checked_add(root.depth)?;
        let suffix = std::iter::once(first).chain(steps);
        match root.owner {
            OriginOwner::Local(local) => Self::from_steps(local, suffix),
            OriginOwner::Field(field) => Self::from_steps(field.base, field.steps().chain(suffix)),
        }
    }

    fn relative_to(self, root: LocalSlot) -> Option<Self> {
        let mut steps = self.steps();
        match root.owner {
            OriginOwner::Local(local) if local == self.base => {}
            OriginOwner::Field(field) if field.base == self.base => {
                for expected in field.steps() {
                    if steps.next() != Some(expected) {
                        return None;
                    }
                }
            }
            _ => return None,
        }
        let mut first = steps.next()?;
        if first.deref_depth < root.depth {
            return None;
        }
        first.deref_depth -= root.depth;
        Self::from_steps(self.base, std::iter::once(first).chain(steps))
    }
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

fn place_root<'tcx, D: HasLocalDecls<'tcx>>(
    local_decls: &D,
    place: Place<'tcx>,
) -> Option<LocalSlot> {
    if let Some((field, depth)) = field_place_for_place(local_decls, place) {
        Some(LocalSlot {
            owner: OriginOwner::Field(field),
            depth,
        })
    } else {
        Some(LocalSlot {
            owner: OriginOwner::Local(place.local),
            depth: place_deref_depth(place)?,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg(test)]
struct A2State {
    may_originless: DenseBitSet<OriginSlot>,
    modeled_sources: IndexVec<OriginSlot, DenseBitSet<OriginSlot>>,
    unstable_bases: DenseBitSet<OriginSlot>,
}

#[cfg(test)]
impl A2State {
    #[cfg(test)]
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

    #[cfg(test)]
    fn clear_as_modeled_entry(&mut self, slot: OriginSlot) {
        self.may_originless.remove(slot);
        self.modeled_sources[slot].clear();
        self.modeled_sources[slot].insert(slot);
    }

    #[cfg(test)]
    fn join_from(&mut self, other: &Self) -> bool {
        let mut changed = self.may_originless.union(&other.may_originless);
        changed |= self.unstable_bases.union(&other.unstable_bases);
        for slot in self.modeled_sources.indices() {
            changed |= self.modeled_sources[slot].union(&other.modeled_sources[slot]);
        }
        changed
    }

    #[cfg(test)]
    fn set_originless(&mut self, target: OriginSlot) {
        self.may_originless.insert(target);
        self.modeled_sources[target].clear();
    }

    #[cfg(test)]
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
    pointee_copies: SparseBitMatrix<OriginSlot, OriginSlot>,
    // Copies share possible field storage, but only actual stores flow back to other views.
    field_aliases: SparseBitMatrix<OriginSlot, OriginSlot>,
    stores: SparseBitMatrix<OriginSlot, OriginSlot>,
    written_slots: DenseBitSet<OriginSlot>,
    field_descendants: FxHashMap<OriginSlot, Vec<(OriginSlot, FieldPlace)>>,
    erased_pointers: DenseBitSet<OriginSlot>,
    unknown_targets: DenseBitSet<OriginSlot>,
    cutoff_targets: DenseBitSet<OriginSlot>,
    cutoff_writes: DenseBitSet<OriginSlot>,
    written_pointees: DenseBitSet<OriginSlot>,
}

#[derive(Clone, Debug)]
pub(crate) struct OriginFlowResult {
    pub summary: NativeOriginSummary,
    pub body: BodyOriginFlow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(test)]
pub(crate) struct A2OpaqueResultGuard {
    pub(crate) function: LocalDefId,
    pub(crate) local: Local,
    pub(crate) depth: u8,
    pub(crate) location: crate::analyses::borrow_ownership::guarded_repair::MirLocationKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(test)]
pub(crate) struct A2RestoredSelfOrigin {
    pub(crate) function: LocalDefId,
    pub(crate) slot: SignatureSlot,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[cfg(test)]
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
        let recursive = scc.len() > 1
            || scc.first().is_some_and(|&did| {
                tcx.mir_drops_elaborated_and_const_checked(did.expect_local())
                    .borrow()
                    .basic_blocks
                    .iter()
                    .any(|block| {
                        block
                            .terminator()
                            .as_call(tcx)
                            .and_then(|call| call.func.did())
                            == Some(did)
                    })
            });
        // Absence of an argument origin is meaningful only after recursive flows settle.
        for seed_unrooted_fields in [false, true] {
            if !seed_unrooted_fields && !recursive {
                continue;
            }
            loop {
                let mut changed = false;

                for &did in scc {
                    let did = did.expect_local();
                    let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                    let result = analyze_body_origin_flow_result(
                        tcx,
                        &body,
                        &summaries,
                        &program_functions,
                        seed_unrooted_fields,
                    );

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
    }

    results
}

#[cfg(test)]
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
                    location:
                        crate::analyses::borrow_ownership::guarded_repair::MirLocationKey::new(
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
    seed_unrooted_fields: bool,
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

    let body_flow = body_flow.closed(body, seed_unrooted_fields);
    let summary = body_flow.to_summary(body);

    OriginFlowResult {
        summary,
        body: body_flow,
    }
}

fn empty_origin_flow_result<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> OriginFlowResult {
    let body_flow = BodyOriginFlow::new(tcx, body).closed(body, false);
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
            && same_matrix(&self.pointee_copies, &other.pointee_copies)
            && same_matrix(&self.stores, &other.stores)
            && self.written_slots == other.written_slots
            && self.unknown_targets == other.unknown_targets
            && self.cutoff_targets == other.cutoff_targets
            && self.cutoff_writes == other.cutoff_writes
            && self.written_pointees == other.written_pointees
    }
}

impl Eq for NativeOriginSummary {}

impl PartialEq for BodyOriginFlow {
    fn eq(&self, other: &Self) -> bool {
        self.slots == other.slots
            && self.slot_map == other.slot_map
            && same_matrix(&self.value_flows, &other.value_flows)
            && same_matrix(&self.storage_aliases, &other.storage_aliases)
            && same_matrix(&self.pointee_copies, &other.pointee_copies)
            && same_matrix(&self.field_aliases, &other.field_aliases)
            && same_matrix(&self.stores, &other.stores)
            && self.written_slots == other.written_slots
            && self.unknown_targets == other.unknown_targets
            && self.cutoff_targets == other.cutoff_targets
            && self.cutoff_writes == other.cutoff_writes
            && self.written_pointees == other.written_pointees
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
        let mut erased_pointers = Vec::new();
        let erased = |mut ty, depth| {
            for _ in 0..=depth {
                ty = pointer_pointee_ty(ty).unwrap();
            }
            ty.is_c_void(tcx)
        };

        for (local, local_decl) in body.local_decls.iter_enumerated() {
            for depth in 0..pointer_slot_count(local_decl.ty) {
                let owner = OriginOwner::Local(local);
                let slot = slots.push(LocalSlot { owner, depth });
                slot_map.insert((owner, depth), slot);
                if erased(local_decl.ty, depth) {
                    erased_pointers.push(slot);
                }
            }
            for (field_place, ty) in field_places_for_local(tcx, local, local_decl.ty) {
                let owner = OriginOwner::Field(field_place);
                for depth in 0..pointer_slot_count(ty) {
                    let slot = slots.push(LocalSlot { owner, depth });
                    slot_map.insert((owner, depth), slot);
                    if erased(ty, depth) {
                        erased_pointers.push(slot);
                    }
                }
            }
        }

        let domain_size = slots.len();
        let mut erased = DenseBitSet::new_empty(domain_size);
        for slot in erased_pointers {
            erased.insert(slot);
        }
        BodyOriginFlow {
            slots,
            slot_map,
            value_flows: SparseBitMatrix::new(domain_size),
            storage_aliases: SparseBitMatrix::new(domain_size),
            pointee_copies: SparseBitMatrix::new(domain_size),
            field_aliases: SparseBitMatrix::new(domain_size),
            stores: SparseBitMatrix::new(domain_size),
            written_slots: DenseBitSet::new_empty(domain_size),
            field_descendants: FxHashMap::default(),
            erased_pointers: erased,
            unknown_targets: DenseBitSet::new_empty(domain_size),
            cutoff_targets: DenseBitSet::new_empty(domain_size),
            cutoff_writes: DenseBitSet::new_empty(domain_size),
            written_pointees: DenseBitSet::new_empty(domain_size),
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
            .chain(self.cutoff_targets.iter())
            .filter_map(|slot| {
                let local_slot = self.slots[slot];
                slot_owner(local_slot.owner).map(|owner| (owner, local_slot.depth))
            })
            .collect()
    }

    pub(crate) fn depth0_origin_indices(
        &self,
        body: &Body<'_>,
        local: Local,
        caller_reachable_from_unknown: bool,
    ) -> Option<(std::collections::BTreeSet<usize>, bool)> {
        let target = self.slot_for_local(local, 0)?;
        let origins = self
            .slots
            .indices()
            .filter(|&source| source == target || self.value_flows.contains(source, target))
            .map(|source| source.index())
            .collect::<std::collections::BTreeSet<_>>();
        let mut complete =
            !self.unknown_targets.contains(target) && !self.cutoff_targets.contains(target);
        if caller_reachable_from_unknown {
            complete &= !body.args_iter().any(|argument| {
                self.slot_for_local(argument, 0).is_some_and(|source| {
                    source == target || self.value_flows.contains(source, target)
                })
            });
        }
        Some((origins, complete))
    }

    /// Depth-zero caller parameters whose values can flow into `local`.
    ///
    /// The parameter-overlap analysis uses this projection to distinguish a
    /// direct call-site overlap fact from a fact that is conditional on one of
    /// the caller's parameter pairs.
    /// The boolean is false when the ordinary origin analysis has an unknown
    /// source for the local, in which case the producer must also retain a
    /// direct conservative witness.
    pub(crate) fn depth0_argument_origins(
        &self,
        body: &Body<'_>,
        local: Local,
    ) -> Option<(std::collections::BTreeSet<usize>, bool)> {
        let target = self.slot_for_local(local, 0)?;
        let arguments = body
            .args_iter()
            .filter_map(|argument| {
                let source = self.slot_for_local(argument, 0)?;
                (source == target || self.value_flows.contains(source, target))
                    .then_some(argument.index())
            })
            .collect();
        Some((
            arguments,
            !self.unknown_targets.contains(target) && !self.cutoff_targets.contains(target),
        ))
    }

    // Used only after a frozen reader transfer independently certifies its parameter root.
    pub(crate) fn reader_origin_is_known(&self, local: Local) -> bool {
        self.slot_for_local(local, 0)
            .is_some_and(|slot| !self.unknown_targets.contains(slot))
    }

    pub(crate) fn depth0_storage_alias(&self, left: Local, right: Local) -> bool {
        match (self.slot_for_local(left, 0), self.slot_for_local(right, 0)) {
            (Some(left), Some(right)) => {
                left == right || self.storage_aliases.contains(left, right)
            }
            _ => false,
        }
    }

    fn slot_for_place<'tcx, D: HasLocalDecls<'tcx>>(
        &self,
        local_decls: &D,
        place: Place<'tcx>,
        extra_depth: u8,
    ) -> Option<OriginSlot> {
        if let Some((field, deref_depth)) = field_place_for_place(local_decls, place) {
            return self.slot_for_owner(
                OriginOwner::Field(field),
                deref_depth.checked_add(extra_depth)?,
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

    fn add_copy(&mut self, source: OriginSlot, target: OriginSlot) {
        self.add_flow(source, target);
        if source != target {
            self.pointee_copies.insert(source, target);
        }
    }

    fn transfer_fields(&mut self, source: LocalSlot, target: LocalSlot, address: bool) {
        let mut target = target;
        if address {
            target.depth += 1;
        }
        let pairs = self
            .slots
            .iter_enumerated()
            .filter_map(|(from, slot)| {
                let OriginOwner::Field(field) = slot.owner else { return None };
                let field = field.relative_to(source)?.under(target)?;
                Some((
                    from,
                    self.slot_for_owner(OriginOwner::Field(field), slot.depth)?,
                ))
            })
            .collect::<Vec<_>>();
        for (source, target) in pairs {
            if address {
                self.add_alias(source, target);
            } else {
                self.add_copy(source, target);
                self.stores.insert(source, target);
                self.written_slots.insert(target);
            }
        }
        let missing = self
            .slots
            .iter_enumerated()
            .filter_map(|(to, slot)| {
                let OriginOwner::Field(field) = slot.owner else { return None };
                let relative = field.relative_to(target)?;
                match relative.under(source) {
                    None => Some((to, true)),
                    Some(field)
                        if self
                            .slot_for_owner(OriginOwner::Field(field), slot.depth)
                            .is_none() =>
                    {
                        Some((to, false))
                    }
                    _ => None,
                }
            })
            .collect::<Vec<_>>();
        for (target, cutoff) in missing {
            if cutoff {
                self.cutoff_targets.insert(target);
            } else {
                self.mark_unknown(target);
            }
        }
    }

    fn add_descendant_aliases(&mut self, a: OriginSlot, b: OriginSlot) -> bool {
        let mut pairs = Vec::new();
        for offset in 1..=MAX_SIGNATURE_SLOT_DEPTH {
            let Some(a_descendant) = self.slot_after(a, offset) else {
                break;
            };
            let Some(b_descendant) = self.slot_after(b, offset) else {
                break;
            };
            pairs.push((a_descendant, b_descendant));
        }
        for root in [a, b] {
            self.field_descendants.entry(root).or_insert_with(|| {
                self.slots
                    .iter_enumerated()
                    .filter_map(|(source, slot)| {
                        let OriginOwner::Field(field) = slot.owner else { return None };
                        Some((source, field.relative_to(self.slots[root])?))
                    })
                    .collect()
            });
        }
        let descendants = self.field_descendants[&a].clone();
        let mut changed = false;
        for (source, field) in descendants {
            if let Some(field) = field.under(self.slots[b])
                && let Some(target) =
                    self.slot_for_owner(OriginOwner::Field(field), self.slots[source].depth)
            {
                changed |= source != target && !self.pointee_copies.contains(source, target);
                self.add_copy(source, target);
                self.field_aliases.insert(source, target);
                self.field_aliases.insert(target, source);
            }
        }
        for (source, target) in pairs {
            changed |= source != target && !self.storage_aliases.contains(source, target);
            self.add_alias(source, target);
        }
        changed
    }

    fn mark_unknown(&mut self, target: OriginSlot) {
        self.unknown_targets.insert(target);
        let root = self.slots[target];
        for (slot, value) in self.slots.iter_enumerated() {
            if matches!(value.owner, OriginOwner::Field(field) if field.relative_to(root).is_some())
            {
                self.unknown_targets.insert(slot);
            }
        }
    }

    fn invalidate_place_slots<'tcx, D: HasLocalDecls<'tcx>>(
        &mut self,
        local_decls: &D,
        place: Place<'tcx>,
        start_depth: u8,
        cutoff: bool,
    ) {
        for depth in start_depth..MAX_SIGNATURE_SLOT_DEPTH {
            let Some(slot) = self.slot_for_place(local_decls, place, depth) else {
                break;
            };
            self.invalidate_stored_slot(slot, cutoff);
            self.written_slots.insert(slot);
        }
        if let Some(root) = place_root(local_decls, place) {
            let targets = self
                .slots
                .iter_enumerated()
                .filter_map(|(target, slot)| {
                    let OriginOwner::Field(field) = slot.owner else { return None };
                    let relative = field.relative_to(root)?;
                    (start_depth == 0
                        || slot.depth >= start_depth
                        || relative.steps().any(|step| step.deref_depth >= start_depth))
                    .then_some(target)
                })
                .collect::<Vec<_>>();
            for target in targets {
                self.invalidate_stored_slot(target, cutoff);
                self.written_slots.insert(target);
            }
        }
    }

    fn invalidate_stored_slot(&mut self, target: OriginSlot, cutoff: bool) {
        if cutoff {
            self.cutoff_targets.insert(target);
            if matches!(
                self.slots[target],
                LocalSlot {
                    owner: OriginOwner::Field(_),
                    ..
                } | LocalSlot { depth: 1.., .. }
            ) {
                self.cutoff_writes.insert(target);
            }
        } else {
            self.mark_unknown(target);
        }
    }

    fn closed(mut self, body: &Body<'_>, seed_unrooted_fields: bool) -> Self {
        let stores = self.stores.clone();
        loop {
            let mut combined = SparseBitMatrix::new(self.slots.len());
            union_matrix_into(&mut combined, &self.pointee_copies);
            union_matrix_into(&mut combined, &self.storage_aliases);
            self.pointee_copies = transitive_closure(&combined, self.slots.len());
            let edges = self
                .pointee_copies
                .rows()
                .flat_map(|source| {
                    self.pointee_copies
                        .row(source)
                        .into_iter()
                        .flat_map(move |targets| targets.iter().map(move |target| (source, target)))
                })
                .collect::<Vec<_>>();
            let mut changed = false;
            for (source, target) in edges {
                changed |= self.add_descendant_aliases(source, target);
            }
            for source in stores.rows() {
                for target in stores
                    .row(source)
                    .into_iter()
                    .flat_map(|targets| targets.iter())
                {
                    let aliases = self
                        .field_aliases
                        .row(target)
                        .into_iter()
                        .flat_map(|targets| targets.iter())
                        .collect::<Vec<_>>();
                    for alias in aliases {
                        if self.pointee_copies.contains(source, target) {
                            changed |=
                                source != alias && !self.pointee_copies.contains(source, alias);
                            self.add_copy(source, alias);
                        } else {
                            self.add_flow(source, alias);
                        }
                        self.stores.insert(source, alias);
                        self.written_slots.insert(alias);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        self.storage_aliases = transitive_closure(&self.storage_aliases, self.slots.len());
        let mut combined = SparseBitMatrix::new(self.slots.len());
        union_matrix_into(&mut combined, &self.value_flows);
        union_matrix_into(&mut combined, &self.storage_aliases);
        self.value_flows = transitive_closure(&combined, self.slots.len());
        for source in self.pointee_copies.rows() {
            let source_base = match self.slots[source].owner {
                OriginOwner::Local(local) => local,
                OriginOwner::Field(field) => field.base,
            };
            if self.erased_pointers.contains(source)
                && (source_base == RETURN_PLACE || source_base.index() > body.arg_count)
                && !self.unknown_targets.contains(source)
                && self.pointee_copies.rows().any(|ancestor| {
                    !self.erased_pointers.contains(ancestor)
                        && self.pointee_copies.contains(ancestor, source)
                })
            {
                continue;
            }
            for target in self
                .pointee_copies
                .row(source)
                .into_iter()
                .flat_map(|targets| targets.iter())
            {
                if let Some(descendants) = self.field_descendants.get(&target) {
                    for &(slot, relative) in descendants {
                        match relative.under(self.slots[source]) {
                            None => {
                                self.cutoff_targets.insert(slot);
                            }
                            Some(field)
                                if self
                                    .slot_for_owner(
                                        OriginOwner::Field(field),
                                        self.slots[slot].depth,
                                    )
                                    .is_none() =>
                            {
                                self.unknown_targets.insert(slot);
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        let arguments = self
            .slots
            .iter_enumerated()
            .filter_map(|(slot, value)| {
                let local = match value.owner {
                    OriginOwner::Local(local) => local,
                    OriginOwner::Field(field) => field.base,
                };
                (local != RETURN_PLACE && local.index() <= body.arg_count).then_some(slot)
            })
            .collect::<Vec<_>>();
        for (source, value) in self.slots.iter_enumerated() {
            if matches!(value.owner, OriginOwner::Field(field) if field.base.index() > body.arg_count)
                && seed_unrooted_fields
                && !self.cutoff_targets.contains(source)
                && !arguments
                    .iter()
                    .any(|&argument| self.value_flows.contains(argument, source))
            {
                self.unknown_targets.insert(source);
            }
        }

        // Recover typed pointees erased by casts to void pointers before applying byte writes.
        let mut written = self.written_pointees.clone();
        for source in self.slots.indices() {
            if self
                .written_pointees
                .iter()
                .any(|target| self.value_flows.contains(source, target))
            {
                written.insert(source);
            }
        }
        self.written_pointees = written.clone();
        for source in written.iter() {
            if let Some(targets) = self.value_flows.row(source) {
                self.written_pointees.union(targets);
            }
        }
        for source in self.written_pointees.iter() {
            for depth in 1..MAX_SIGNATURE_SLOT_DEPTH {
                if let Some(target) = self.slot_after(source, depth) {
                    self.unknown_targets.insert(target);
                }
            }
            for (target, slot) in self.slots.iter_enumerated() {
                if let OriginOwner::Field(field) = slot.owner
                    && field.relative_to(self.slots[source]).is_some()
                {
                    self.unknown_targets.insert(target);
                }
            }
        }
        // Incomplete view paths are not opaque writes or origin-less pointer values.
        loop {
            let previous_writes = self.cutoff_writes.clone();
            let mut cutoffs = self.cutoff_targets.clone();
            for source in self.cutoff_targets.iter() {
                if let Some(targets) = self.value_flows.row(source) {
                    cutoffs.union(targets);
                }
            }
            for source in previous_writes.iter() {
                if let Some(targets) = self.field_aliases.row(source) {
                    cutoffs.union(targets);
                    self.cutoff_writes.union(targets);
                    self.written_slots.union(targets);
                }
            }
            for source in self.stores.rows() {
                if cutoffs.contains(source) {
                    for target in self
                        .stores
                        .row(source)
                        .into_iter()
                        .flat_map(|targets| targets.iter())
                    {
                        if matches!(
                            self.slots[target],
                            LocalSlot {
                                owner: OriginOwner::Field(_),
                                ..
                            } | LocalSlot { depth: 1.., .. }
                        ) {
                            self.cutoff_writes.insert(target);
                        }
                    }
                }
            }
            if cutoffs == self.cutoff_targets && previous_writes == self.cutoff_writes {
                break;
            }
            self.cutoff_targets = cutoffs;
        }
        loop {
            let mut unknown = self.unknown_targets.clone();
            for source in self.unknown_targets.iter() {
                if let Some(targets) = self.value_flows.row(source) {
                    unknown.union(targets);
                }
                if self.written_slots.contains(source)
                    && let Some(aliases) = self.field_aliases.row(source)
                {
                    unknown.union(aliases);
                    self.written_slots.union(aliases);
                }
            }
            if unknown == self.unknown_targets {
                break;
            }
            self.unknown_targets = unknown;
        }

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
        let mut slots = IndexVec::<OriginSlot, SignatureSlot>::new();
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
                        parents: Default::default(),
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
                    parents: field_place.parents,
                    deref_depth: field_place.deref_depth,
                    field: Some(field_place.field),
                },
                depth: local_slot.depth,
            });
            internal_to_summary.insert(slot, summary);
        }

        let mut value_flows = SparseBitMatrix::new(slots.len());
        let mut storage_aliases = SparseBitMatrix::new(slots.len());
        let mut pointee_copies = SparseBitMatrix::new(slots.len());
        let mut stores = SparseBitMatrix::new(slots.len());
        let mut written_slots = DenseBitSet::new_empty(slots.len());
        let mut unknown_targets = DenseBitSet::new_empty(slots.len());
        let mut cutoff_targets = DenseBitSet::new_empty(slots.len());
        let mut cutoff_writes = DenseBitSet::new_empty(slots.len());
        let mut written_pointees = DenseBitSet::new_empty(slots.len());

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
        for source in self.pointee_copies.rows() {
            let Some(&summary_source) = internal_to_summary.get(&source) else { continue };
            for target in self
                .pointee_copies
                .row(source)
                .into_iter()
                .flat_map(|targets| targets.iter())
            {
                if let Some(&summary_target) = internal_to_summary.get(&target) {
                    pointee_copies.insert(summary_source, summary_target);
                }
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

        for source in self.stores.rows() {
            for target in self
                .stores
                .row(source)
                .into_iter()
                .flat_map(|targets| targets.iter())
            {
                if matches!(
                    self.slots[target],
                    LocalSlot {
                        owner: OriginOwner::Local(_),
                        depth: 0
                    }
                ) {
                    continue;
                }
                let Some(&to) = internal_to_summary.get(&target) else { continue };
                for (&ancestor, &from) in &internal_to_summary {
                    if ancestor == source || self.value_flows.contains(ancestor, source) {
                        stores.insert(from, to);
                    }
                }
            }
        }
        for target in self.written_slots.iter() {
            if matches!(
                self.slots[target],
                LocalSlot {
                    owner: OriginOwner::Local(_),
                    depth: 0
                }
            ) {
                continue;
            }
            if let Some(&target) = internal_to_summary.get(&target) {
                written_slots.insert(target);
            }
        }
        for target in self.cutoff_targets.iter() {
            if let Some(&target) = internal_to_summary.get(&target)
                && observable_value_target(slots[target])
            {
                cutoff_targets.insert(target);
            }
        }
        for target in self.cutoff_writes.iter() {
            if let Some(&target) = internal_to_summary.get(&target) {
                cutoff_writes.insert(target);
            }
        }

        for written in self.written_pointees.iter() {
            if let Some(&target) = internal_to_summary.get(&written)
                && matches!(slots[target].place.root, SignatureRoot::Arg(_))
            {
                written_pointees.insert(target);
            }
        }

        NativeOriginSummary {
            slots,
            value_flows,
            storage_aliases,
            pointee_copies,
            stores,
            written_slots,
            unknown_targets,
            cutoff_targets,
            cutoff_writes,
            written_pointees,
        }
    }

    #[cfg(test)]
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
                        parents: Default::default(),
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
                        parents: field.parents,
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

#[cfg(test)]
struct BodyA2Result {
    summary: NativeOriginSummary,
    guards: Vec<(Local, u8, Location)>,
    restored: Vec<SignatureSlot>,
}

#[cfg(test)]
fn a2_exact_target<'tcx>(
    flow: &BodyOriginFlow,
    body: &Body<'tcx>,
    state: &A2State,
    place: Place<'tcx>,
) -> Option<OriginSlot> {
    let target = flow.slot_for_place(body, place, 0)?;
    let base_depth = if let Some((field, _)) = field_place_for_place(body, place) {
        if !field.parents.is_empty() {
            return None;
        }
        field.deref_depth
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

#[cfg(test)]
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

#[cfg(test)]
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

#[cfg(test)]
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

#[cfg(test)]
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
    if let Some(exit) = exit {
        refined.intersect(&exit.may_originless);
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
    ty: Ty<'tcx>,
) -> Vec<(FieldPlace, Ty<'tcx>)> {
    fn visit<'tcx>(
        tcx: TyCtxt<'tcx>,
        local: Local,
        ty: Ty<'tcx>,
        parents: &mut Vec<FieldStep>,
        deref_depth: u8,
        total_derefs: u8,
        fields: &mut Vec<(FieldPlace, Ty<'tcx>)>,
    ) {
        if let Some(pointee) = pointer_pointee_ty(ty) {
            if total_derefs < MAX_SIGNATURE_SLOT_DEPTH {
                visit(
                    tcx,
                    local,
                    pointee,
                    parents,
                    deref_depth + 1,
                    total_derefs + 1,
                    fields,
                );
            }
        } else if let TyKind::Adt(adt_def, args) = ty.kind()
            && adt_def.did().is_local()
            && adt_def.is_struct()
        {
            for (field_index, field_def) in adt_def.all_fields().enumerate() {
                let ty = field_def.ty(tcx, args);
                parents.push(FieldStep {
                    deref_depth,
                    field: StructFieldSlot {
                        struct_did: adt_def.did().expect_local(),
                        field_index,
                    },
                });
                if is_direct_raw_ptr_ty(ty)
                    && let Some(place) = FieldPlace::from_steps(local, parents.iter().copied())
                {
                    fields.push((place, ty));
                }
                if parents.len() < MAX_FIELD_PATH_DEPTH {
                    visit(tcx, local, ty, parents, 0, total_derefs, fields);
                }
                parents.pop();
            }
        }
    }
    let mut fields = vec![];
    visit(tcx, local, ty, &mut Vec::new(), 0, 0, &mut fields);
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
            self.flow.add_copy(source, target);
            self.flow.stores.insert(source, target);
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
        if let Some(source) = place_root(self.body, place) {
            self.flow
                .transfer_fields(source, self.flow.slots[target], true);
        }
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
                    self.flow.add_copy(source, target);
                    self.flow.stores.insert(source, target);
                    self.flow.add_descendant_aliases(source, target);
                }
            }
            None => {
                if let Some(deref_depth) = place_deref_interior_depth(place) {
                    if let Some(source) = self.flow.slot_for_local(place.local, deref_depth - 1) {
                        self.flow.add_flow(source, target);
                        self.flow.stores.insert(source, target);
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
            self.assign_from_operand(destination, &arg0.node, location);
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

        if let Some(contract) = pointer_return_contract(&call.func)
            && let Some(argument) = call.args.get(contract.argument)
        {
            self.assign_known_return_from_operand(destination, &argument.node, location);
            for &index in contract.writes {
                if let Some(argument) = call.args.get(index) {
                    for target in self.operand_slots(&argument.node, location) {
                        self.flow.written_pointees.insert(target);
                    }
                }
            }
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
                self.flow.stores.insert(source, target);
            }
        }
    }

    fn apply_call_summary(
        &mut self,
        call: &MirFunctionCall<'_, 'tcx>,
        summary: &NativeOriginSummary,
    ) {
        let mut unmapped = false;
        let mut cutoff_effect = false;
        for written in summary.written_slots.iter() {
            if let Some(target) = self.instantiate_signature_slot(call, summary.slots[written]) {
                self.flow.written_slots.insert(target);
            } else if matches!(summary.slots[written].place.root, SignatureRoot::Arg(_)) {
                if self.signature_slot_is_cutoff(call, summary.slots[written]) {
                    cutoff_effect = true;
                } else {
                    unmapped = true;
                }
            }
        }
        for source in summary.stores.rows() {
            for target in summary
                .stores
                .row(source)
                .into_iter()
                .flat_map(|targets| targets.iter())
            {
                match (
                    self.instantiate_signature_slot(call, summary.slots[source]),
                    self.instantiate_signature_slot(call, summary.slots[target]),
                ) {
                    (Some(source), Some(target)) => {
                        self.flow.stores.insert(source, target);
                    }
                    (source_slot, target_slot) => {
                        if (source_slot.is_some()
                            || self.signature_slot_is_cutoff(call, summary.slots[source]))
                            && (target_slot.is_some()
                                || self.signature_slot_is_cutoff(call, summary.slots[target]))
                        {
                            cutoff_effect = true;
                        } else {
                            unmapped = true;
                        }
                    }
                }
            }
        }
        for written in summary.written_pointees.iter() {
            if let Some(target) = self.instantiate_signature_slot(call, summary.slots[written]) {
                self.flow.written_pointees.insert(target);
            } else if self.signature_slot_is_cutoff(call, summary.slots[written]) {
                cutoff_effect = true;
            } else {
                unmapped = true;
            }
        }
        for source in summary.value_flows.rows() {
            let source_slot = self.instantiate_signature_slot(call, summary.slots[source]);
            let Some(targets) = summary.value_flows.row(source) else {
                continue;
            };
            for target in targets.iter() {
                let is_result = matches!(summary.slots[target].place.root, SignatureRoot::Return)
                    && summary.slots[target].place.field.is_none()
                    && summary.slots[target].depth == 0;
                match (
                    source_slot,
                    self.instantiate_signature_slot(call, summary.slots[target]),
                ) {
                    (Some(source), Some(target)) => {
                        self.flow.add_flow(source, target);
                        if is_result {
                            self.flow.stores.insert(source, target);
                        }
                    }
                    (_, Some(target)) => {
                        if self.signature_slot_is_cutoff(call, summary.slots[source]) {
                            self.flow.cutoff_targets.insert(target);
                        } else {
                            self.flow.mark_unknown(target);
                        }
                    }
                    _ => {}
                }
            }
        }

        for source in summary.storage_aliases.rows() {
            let source_slot = self.instantiate_signature_slot(call, summary.slots[source]);
            let Some(targets) = summary.storage_aliases.row(source) else {
                continue;
            };
            for target in targets.iter() {
                match (
                    source_slot,
                    self.instantiate_signature_slot(call, summary.slots[target]),
                ) {
                    (Some(source), Some(target)) => self.flow.add_alias(source, target),
                    (source, target) => {
                        for slot in source.into_iter().chain(target) {
                            self.flow.mark_unknown(slot);
                        }
                        unmapped = true;
                    }
                }
            }
        }

        for target in summary.unknown_targets.iter() {
            if let Some(target_slot) = self.instantiate_signature_slot(call, summary.slots[target])
            {
                self.flow.mark_unknown(target_slot);
            } else {
                unmapped = true;
            }
        }
        for target in summary.cutoff_targets.iter() {
            if let Some(target) = self.instantiate_signature_slot(call, summary.slots[target]) {
                self.flow.cutoff_targets.insert(target);
            }
        }
        for target in summary.cutoff_writes.iter() {
            if let Some(target) = self.instantiate_signature_slot(call, summary.slots[target]) {
                self.flow.cutoff_targets.insert(target);
                self.flow.cutoff_writes.insert(target);
            } else if self.signature_slot_is_cutoff(call, summary.slots[target]) {
                cutoff_effect = true;
            } else {
                unmapped = true;
            }
        }
        for source in summary.pointee_copies.rows() {
            let source_slot = self.instantiate_signature_slot(call, summary.slots[source]);
            for target in summary
                .pointee_copies
                .row(source)
                .into_iter()
                .flat_map(|targets| targets.iter())
            {
                if let (Some(source), Some(target)) = (
                    source_slot,
                    self.instantiate_signature_slot(call, summary.slots[target]),
                ) {
                    self.flow.add_copy(source, target);
                } else {
                    // The corresponding value-flow target carries any observable cutoff.
                }
            }
        }
        if unmapped {
            self.mark_unknown_call_effects(call);
        } else if cutoff_effect {
            self.invalidate_call_effects(call, true);
        }
    }

    fn signature_slot_is_cutoff(
        &self,
        call: &MirFunctionCall<'_, 'tcx>,
        slot: SignatureSlot,
    ) -> bool {
        let Some(field) = slot.place.field else { return false };
        let place = match slot.place.root {
            SignatureRoot::Return => call.destination,
            SignatureRoot::Arg(local) => {
                let Some(place) = local
                    .index()
                    .checked_sub(1)
                    .and_then(|index| call.args.get(index))
                    .and_then(|arg| arg.node.place())
                else {
                    return false;
                };
                place
            }
        };
        let Some(root) = place_root(self.body, place) else { return false };
        FieldPlace {
            base: place.local,
            parents: slot.place.parents,
            deref_depth: slot.place.deref_depth,
            field,
        }
        .under(root)
        .is_none()
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
            let root = place_root(self.body, root_place)?;
            let field = FieldPlace {
                base: root_place.local,
                parents: signature_place.parents,
                deref_depth: signature_place.deref_depth,
                field,
            }
            .under(root)?;
            return self.flow.slot_for_owner(OriginOwner::Field(field), depth);
        }

        self.flow.slot_for_place(
            self.body,
            root_place,
            signature_place.deref_depth.checked_add(depth)?,
        )
    }

    fn mark_unknown_call_effects(&mut self, call: &MirFunctionCall<'_, 'tcx>) {
        self.invalidate_call_effects(call, false);
    }

    fn invalidate_call_effects(&mut self, call: &MirFunctionCall<'_, 'tcx>, cutoff: bool) {
        self.flow
            .invalidate_place_slots(self.body, call.destination, 0, cutoff);

        for arg in call.args {
            let Some(place) = arg.node.place() else {
                continue;
            };
            self.flow
                .invalidate_place_slots(self.body, place, 1, cutoff);
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
            if !matches!(rvalue_ty.kind(), TyKind::Adt(definition, _) if definition.did().is_local() && definition.is_struct())
            {
                return;
            }
            match rvalue {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                    if let Some(source) = operand.place()
                        && let (Some(source), Some(target)) =
                            (place_root(self.body, source), place_root(self.body, *place))
                    {
                        self.flow.transfer_fields(source, target, false);
                    }
                }
                Rvalue::CopyForDeref(source) => {
                    if let (Some(source), Some(target)) = (
                        place_root(self.body, *source),
                        place_root(self.body, *place),
                    ) {
                        self.flow.transfer_fields(source, target, false);
                    }
                }
                Rvalue::Aggregate(kind, operands)
                    if matches!(kind.as_ref(), AggregateKind::Adt(..)) =>
                {
                    for (index, operand) in operands.iter_enumerated() {
                        let target = place.project_deeper(
                            &[PlaceElem::Field(index, operand.ty(self.body, self.tcx))],
                            self.tcx,
                        );
                        if let Some(slot) = self.flow.slot_for_place(self.body, target, 0) {
                            self.flow.written_slots.insert(slot);
                            self.assign_from_operand(slot, operand, location);
                        } else if let Some(source) = operand.place()
                            && let (Some(source), Some(target)) =
                                (place_root(self.body, source), place_root(self.body, target))
                        {
                            self.flow.transfer_fields(source, target, false);
                        }
                    }
                }
                _ => {}
            }
            return;
        }

        let Some(target) = self.flow.slot_for_place(self.body, *place, 0) else {
            return;
        };
        self.flow.written_slots.insert(target);

        match rvalue {
            Rvalue::Use(operand)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::ShallowInitBox(operand, _)
            | Rvalue::WrapUnsafeBinder(operand, _) => {
                self.assign_from_operand(target, operand, location)
            }
            Rvalue::CopyForDeref(place) => {
                for source in self.place_slots_or_derived(*place, location) {
                    self.flow.add_copy(source, target);
                    self.flow.stores.insert(source, target);
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
        if let Some(target) = self.flow.slot_for_place(self.body, call.destination, 0) {
            self.flow.written_slots.insert(target);
        }

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
        if let CallKind::RustLib(def_id) = &call.func
            && !def_id.is_local()
            && self.tcx.def_kind(*def_id) == rustc_hir::def::DefKind::AssocFn
            && self.tcx.crate_name(def_id.krate).as_str() == "core"
            && matches!(
                self.tcx.def_path(*def_id).data.first().map(|part| part.data),
                Some(rustc_hir::definitions::DefPathData::TypeNs(name)) if name.as_str() == "ptr"
            )
            && matches!(self.tcx.item_name(*def_id).as_str(), "is_null" | "addr")
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

    const OP: &str = "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; }";

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
