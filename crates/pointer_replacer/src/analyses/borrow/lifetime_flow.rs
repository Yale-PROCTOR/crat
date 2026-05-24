use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{
    IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};
use rustc_middle::{
    mir::{
        BinOp, Body, Const, ConstOperand, ConstValue, Local, Location, Operand, Place, PlaceElem,
        RETURN_PLACE, Rvalue, Statement, StatementKind, Terminator, visit::Visitor,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::{DefId, LocalDefId};

use super::is_borrowing_method;
use crate::{
    analyses::mir::{CallGraphPostOrder, CallKind, MirFunctionCall, TerminatorExt},
    utils::rustc::RustProgram,
};

pub const MAX_SIGNATURE_SLOT_DEPTH: u8 = 3;

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "S_({})"]
    pub struct LifetimeSlot {}
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SignatureRoot {
    Return,
    Arg(Local),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SignatureSlot {
    pub root: SignatureRoot,
    pub depth: u8,
}

#[derive(Clone, Debug)]
pub struct LifetimeFlowSummary {
    pub slots: IndexVec<LifetimeSlot, SignatureSlot>,
    pub value_flows: SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
    pub storage_aliases: SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
    pub unknown_targets: DenseBitSet<LifetimeSlot>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LocalSlot {
    pub local: Local,
    pub depth: u8,
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
pub struct BodyLifetimeFlow {
    pub slots: IndexVec<LifetimeSlot, LocalSlot>,
    slot_map: FxHashMap<(usize, u8), LifetimeSlot>,
    pub value_flows: SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
    pub storage_aliases: SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
    pub unknown_targets: DenseBitSet<LifetimeSlot>,
}

#[derive(Clone, Debug)]
pub struct LifetimeFlowResult {
    pub summary: LifetimeFlowSummary,
    pub body: BodyLifetimeFlow,
}

pub type LifetimeFlowResults = FxHashMap<LocalDefId, LifetimeFlowResult>;

pub fn analyze_program_lifetime_flow(program: &RustProgram<'_>) -> LifetimeFlowResults {
    let tcx = program.tcx;
    let program_functions: FxHashSet<_> = program.functions.iter().copied().collect();

    let mut results = FxHashMap::default();
    results.reserve(program.functions.len());
    let mut summaries = FxHashMap::default();
    summaries.reserve(program.functions.len());

    for &did in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        let result = empty_lifetime_flow_result(&body);
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
                    analyze_body_lifetime_flow_result(tcx, &body, &summaries, &program_functions);

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

#[allow(dead_code)]
pub fn analyze_body_lifetime_flow<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    callee_summaries: &FxHashMap<LocalDefId, LifetimeFlowSummary>,
    program_functions: &FxHashSet<LocalDefId>,
) -> LifetimeFlowSummary {
    analyze_body_lifetime_flow_result(tcx, body, callee_summaries, program_functions).summary
}

pub fn analyze_body_lifetime_flow_result<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    callee_summaries: &FxHashMap<LocalDefId, LifetimeFlowSummary>,
    program_functions: &FxHashSet<LocalDefId>,
) -> LifetimeFlowResult {
    let mut body_flow = BodyLifetimeFlow::new(body);
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

    LifetimeFlowResult {
        summary,
        body: body_flow,
    }
}

fn empty_lifetime_flow_result(body: &Body<'_>) -> LifetimeFlowResult {
    let body_flow = BodyLifetimeFlow::new(body).closed();
    let summary = body_flow.to_summary(body);
    LifetimeFlowResult {
        summary,
        body: body_flow,
    }
}

impl PartialEq for LifetimeFlowSummary {
    fn eq(&self, other: &Self) -> bool {
        self.slots == other.slots
            && same_matrix(&self.value_flows, &other.value_flows)
            && same_matrix(&self.storage_aliases, &other.storage_aliases)
            && self.unknown_targets == other.unknown_targets
    }
}

impl Eq for LifetimeFlowSummary {}

impl PartialEq for BodyLifetimeFlow {
    fn eq(&self, other: &Self) -> bool {
        self.slots == other.slots
            && self.slot_map == other.slot_map
            && same_matrix(&self.value_flows, &other.value_flows)
            && same_matrix(&self.storage_aliases, &other.storage_aliases)
            && self.unknown_targets == other.unknown_targets
    }
}

impl Eq for BodyLifetimeFlow {}

impl PartialEq for LifetimeFlowResult {
    fn eq(&self, other: &Self) -> bool {
        self.summary == other.summary && self.body == other.body
    }
}

impl Eq for LifetimeFlowResult {}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct DerivedPlaceSourceState {
    sources: FxHashMap<DerivedPlaceKey, FxHashSet<LifetimeSlot>>,
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
    where I: IntoIterator<Item = LifetimeSlot> {
        let sources = sources.into_iter().collect::<FxHashSet<_>>();
        if sources.is_empty() {
            return;
        }
        self.sources.entry(key).or_default().extend(sources);
    }

    fn sources_for_key(&self, key: &DerivedPlaceKey) -> Vec<LifetimeSlot> {
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
    flow: &'flow BodyLifetimeFlow,
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
    ) -> Vec<LifetimeSlot> {
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
    ) -> Vec<LifetimeSlot> {
        if let Some(slot) = self.flow.slot_for_place(place, 0) {
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
    flow: &BodyLifetimeFlow,
) -> FxHashMap<Location, DerivedPlaceSourceState> {
    DerivedPlaceDataflow { tcx, body, flow }.compute()
}

impl BodyLifetimeFlow {
    fn new(body: &Body<'_>) -> Self {
        let mut slots = IndexVec::new();
        let mut slot_map = FxHashMap::default();

        for (local, local_decl) in body.local_decls.iter_enumerated() {
            for depth in 0..pointer_slot_count(local_decl.ty) {
                let slot = slots.push(LocalSlot { local, depth });
                slot_map.insert((local.index(), depth), slot);
            }
        }

        let domain_size = slots.len();
        BodyLifetimeFlow {
            slots,
            slot_map,
            value_flows: SparseBitMatrix::new(domain_size),
            storage_aliases: SparseBitMatrix::new(domain_size),
            unknown_targets: DenseBitSet::new_empty(domain_size),
        }
    }

    pub fn slot_for_local(&self, local: Local, depth: u8) -> Option<LifetimeSlot> {
        self.slot_map.get(&(local.index(), depth)).copied()
    }

    pub fn depth0_value_flows(&self) -> Vec<(Local, Local)> {
        let mut flows = vec![];

        for source in self.value_flows.rows() {
            let source_slot = self.slots[source];
            if source_slot.depth != 0 {
                continue;
            }

            let Some(targets) = self.value_flows.row(source) else {
                continue;
            };

            for target in targets.iter() {
                let target_slot = self.slots[target];
                if target_slot.depth == 0 {
                    flows.push((source_slot.local, target_slot.local));
                }
            }
        }

        flows
    }

    fn slot_for_place(&self, place: Place<'_>, extra_depth: u8) -> Option<LifetimeSlot> {
        let base_depth = place_deref_depth(place)?;
        let depth = base_depth.checked_add(extra_depth)?;
        self.slot_for_local(place.local, depth)
    }

    fn slot_after(&self, slot: LifetimeSlot, offset: u8) -> Option<LifetimeSlot> {
        let local_slot = self.slots[slot];
        self.slot_for_local(local_slot.local, local_slot.depth.checked_add(offset)?)
    }

    fn add_flow(&mut self, source: LifetimeSlot, target: LifetimeSlot) {
        if source != target {
            self.value_flows.insert(source, target);
        }
    }

    fn add_alias(&mut self, a: LifetimeSlot, b: LifetimeSlot) {
        if a == b {
            return;
        }
        self.storage_aliases.insert(a, b);
        self.storage_aliases.insert(b, a);
    }

    fn add_descendant_aliases(&mut self, a: LifetimeSlot, b: LifetimeSlot) {
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

    fn mark_unknown(&mut self, target: LifetimeSlot) {
        self.unknown_targets.insert(target);
    }

    fn mark_unknown_place_slots(&mut self, place: Place<'_>, start_depth: u8) {
        for depth in start_depth..MAX_SIGNATURE_SLOT_DEPTH {
            let Some(slot) = self.slot_for_place(place, depth) else {
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

    fn to_summary(&self, body: &Body<'_>) -> LifetimeFlowSummary {
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
                let summary = slots.push(SignatureSlot { root, depth });
                internal_to_summary.insert(internal, summary);
            }
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

        for target in self.unknown_targets.iter() {
            let Some(&summary_target) = internal_to_summary.get(&target) else {
                continue;
            };
            if observable_value_target(slots[summary_target]) {
                unknown_targets.insert(summary_target);
            }
        }

        LifetimeFlowSummary {
            slots,
            value_flows,
            storage_aliases,
            unknown_targets,
        }
    }
}

struct FlowVisitor<'flow, 'summary, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'flow Body<'tcx>,
    flow: &'flow mut BodyLifetimeFlow,
    callee_summaries: &'summary FxHashMap<LocalDefId, LifetimeFlowSummary>,
    program_functions: &'summary FxHashSet<LocalDefId>,
    derived_place_sources: FxHashMap<Location, DerivedPlaceSourceState>,
}

impl<'flow, 'summary, 'tcx> FlowVisitor<'flow, 'summary, 'tcx> {
    fn assign_from_operand(
        &mut self,
        target: LifetimeSlot,
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

    fn operand_slots(&self, operand: &Operand<'tcx>, location: Location) -> Vec<LifetimeSlot> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.place_slots_or_derived(*place, location)
            }
            Operand::Constant(_) => vec![],
        }
    }

    fn place_slots_or_derived(&self, place: Place<'tcx>, location: Location) -> Vec<LifetimeSlot> {
        if let Some(slot) = self.flow.slot_for_place(place, 0) {
            return vec![slot];
        }
        self.derived_place_sources(place, location)
    }

    fn derived_place_sources(&self, place: Place<'tcx>, location: Location) -> Vec<LifetimeSlot> {
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

    fn assign_from_place_address(&mut self, target: LifetimeSlot, place: Place<'tcx>) {
        match place_deref_depth(place) {
            Some(0) => {
                if let Some(place_slot) = self.flow.slot_for_place(place, 0)
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

        let Some(destination) = self.flow.slot_for_place(call.destination, 0) else {
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
        target: LifetimeSlot,
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
        summary: &LifetimeFlowSummary,
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
    ) -> Option<LifetimeSlot> {
        match slot.root {
            SignatureRoot::Return => self.flow.slot_for_place(call.destination, slot.depth),
            SignatureRoot::Arg(local) => {
                let arg_index = local.index().checked_sub(1)?;
                let arg = call.args.get(arg_index)?;
                let place = arg.node.place()?;
                self.flow.slot_for_place(place, slot.depth)
            }
        }
    }

    fn mark_unknown_call_effects(&mut self, call: &MirFunctionCall<'_, 'tcx>) {
        self.flow.mark_unknown_place_slots(call.destination, 0);

        for arg in call.args {
            let Some(place) = arg.node.place() else {
                continue;
            };
            self.flow.mark_unknown_place_slots(place, 1);
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

        let Some(target) = self.flow.slot_for_place(*place, 0) else {
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
            if let Some(destination) = self.flow.slot_for_place(call.destination, 0) {
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
    match slot.root {
        SignatureRoot::Return => true,
        SignatureRoot::Arg(_) => slot.depth > 0,
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
    edges: &SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
    domain_size: usize,
) -> SparseBitMatrix<LifetimeSlot, LifetimeSlot> {
    let mut closure = SparseBitMatrix::new(domain_size);
    let mut stack = vec![];
    let mut visited = DenseBitSet::new_empty(domain_size);

    for source in (0..domain_size).map(LifetimeSlot::from_usize) {
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
    target: &mut SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
    source: &SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
) {
    for row in source.rows() {
        if let Some(bits) = source.row(row) {
            target.union_row(row, bits);
        }
    }
}

fn same_matrix(
    lhs: &SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
    rhs: &SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
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
