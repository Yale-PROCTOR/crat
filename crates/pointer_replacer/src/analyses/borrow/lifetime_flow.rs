use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{
    IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};
use rustc_middle::{
    mir::{
        Body, Local, Operand, Place, PlaceElem, RETURN_PLACE, Rvalue, Terminator, visit::Visitor,
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

    FlowVisitor {
        tcx,
        body,
        flow: &mut body_flow,
        callee_summaries,
        program_functions,
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
}

impl<'flow, 'summary, 'tcx> FlowVisitor<'flow, 'summary, 'tcx> {
    fn assign_from_operand(&mut self, target: LifetimeSlot, operand: &Operand<'tcx>) {
        let Some(source) = self.operand_slot(operand) else {
            return;
        };
        self.flow.add_flow(source, target);
        self.flow.add_descendant_aliases(source, target);
    }

    fn operand_slot(&self, operand: &Operand<'tcx>) -> Option<LifetimeSlot> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.flow.slot_for_place(*place, 0),
            Operand::Constant(_) => None,
        }
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
                self.flow.mark_unknown(target);
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
        _location: rustc_middle::mir::Location,
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
            | Rvalue::WrapUnsafeBinder(operand, _) => self.assign_from_operand(target, operand),
            Rvalue::CopyForDeref(place) => {
                if let Some(source) = self.flow.slot_for_place(*place, 0) {
                    self.flow.add_flow(source, target);
                    self.flow.add_descendant_aliases(source, target);
                }
            }
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                self.assign_from_place_address(target, *place);
            }
            Rvalue::ThreadLocalRef(_) => self.flow.mark_unknown(target),
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
        _location: rustc_middle::mir::Location,
    ) {
        let Some(call) = terminator.as_call(self.tcx) else {
            return;
        };

        if let CallKind::RustLib(def_id) = &call.func
            && is_borrowing_method(*def_id, self.tcx)
            && let Some(arg0) = call.args.first()
        {
            if let Some(destination) = self.flow.slot_for_place(call.destination, 0) {
                self.assign_from_operand(destination, &arg0.node);
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

fn is_null_pointer_constructor(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    !def_id.is_local() && {
        let name = tcx.item_name(def_id);
        let name = name.as_str();
        name == "null" || name == "null_mut"
    }
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
