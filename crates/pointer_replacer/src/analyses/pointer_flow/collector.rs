//! MIR statement/terminator collector that builds the pointer flow graph for
//! a single function body.

use std::ops::Range;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{
        self, BasicBlock, Body, CastKind, Local, Location, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    ty::{self, Ty, TyCtxt},
};
use rustc_span::source_map::Spanned;

use crate::{
    analyses::{
        mir::CallGraphPostOrder,
        pointer_flow::{
            PointerFlowResult,
            builtin::{
                builtin_summary, call_name, call_no_writes, call_propagates_first_arg,
                constant_pointer_reason, is_as_ptr, is_empty_array_ref_ty, is_heap_alloc_call,
                is_null_ptr_call, is_pointer_arithmetic, is_zero_int_operand,
            },
            field_access::{FieldAccess, FieldAccessReject, FieldEventScanner},
            graph::{BaseId, PfgNode, PointerFlowGraph, UnknownReason, solve_reachable_bases},
            slots::{SlotIdx, SlotPathElem, SlotTable, count_slots},
            summary::{
                CallEffects, FunctionSummary, InstantiatedArgWrite, InstantiatedUnknownArgWrite,
                SummarySource, build_function_summary,
            },
        },
    },
    utils::rustc::RustProgram,
};

// pre-computed assignment right-hand sides used by `array_source_for_local`
pub(crate) enum AssignRhs<'tcx> {
    // rvalue is Ref/RawPtr of this place; if place.local is an array type or
    // has an array projection, the local is a direct array source
    ArrayBorrow(Place<'tcx>),
    // rvalue is Use/Cast/CopyForDeref of this local; follow it recursively
    Follow(Local),
}

pub(crate) fn build_rhs_map<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> FxHashMap<Local, Vec<AssignRhs<'tcx>>> {
    let mut map: FxHashMap<Local, Vec<AssignRhs<'tcx>>> = FxHashMap::default();
    for block_data in body.basic_blocks.iter() {
        for statement in &block_data.statements {
            let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                continue;
            };
            let Some(local) = lhs.as_local() else { continue };
            match rvalue {
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                    map.entry(local)
                        .or_default()
                        .push(AssignRhs::ArrayBorrow(*place));
                }
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                | Rvalue::CopyForDeref(place) => {
                    map.entry(local)
                        .or_default()
                        .push(AssignRhs::Follow(place.local));
                }
                _ => {}
            }
        }

        // for pointer-arithmetic and as_ptr/as_mut_ptr call terminators, record the
        // first argument as a Follow entry so that array_source_for_local can trace
        // back through chains like:  _tmp3 = offset(_tmp2, i)
        //                            _tmp2 = as_mut_ptr(move _tmp1)
        //                            _tmp1 = &mut (*arr).data   ← ArrayBorrow already recorded
        let Some(terminator) = &block_data.terminator else { continue };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        let Some(dest_local) = destination.as_local() else {
            continue;
        };
        if let Some((def_id, name)) = call_name(tcx, func)
            && (is_pointer_arithmetic(tcx, def_id, &name) || is_as_ptr(tcx, def_id, &name))
            && let Some(arg) = args.first()
            && let Some(place) = operand_place(&arg.node)
        {
            map.entry(dest_local)
                .or_default()
                .push(AssignRhs::Follow(place.local));
        }
    }
    map
}

pub(crate) struct Collector<'a, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) body: &'a Body<'tcx>,
    pub(crate) alloc_fns: &'a FxHashSet<LocalDefId>,
    pub(crate) callee_summaries: Option<&'a FxHashMap<LocalDefId, FunctionSummary>>,
    pub(crate) slot_table: &'a SlotTable,
    pub(crate) graph: PointerFlowGraph,
    pub(crate) rhs_map: FxHashMap<Local, Vec<AssignRhs<'tcx>>>,
    pub(crate) direct_param_slots: FxHashSet<SlotIdx>,
    pub(crate) call_effects: FxHashMap<Location, CallEffects>,
    pub(crate) field_accesses: Vec<FieldAccess>,
    pub(crate) field_rejects: Vec<FieldAccessReject>,
}

impl<'tcx> Collector<'_, 'tcx> {
    pub(crate) fn collect(&mut self) {
        for arg in self.body.args_iter() {
            for slot in self.slot_table.local_slots(arg) {
                self.direct_param_slots.insert(slot);
                self.graph
                    .add_base_edge(BaseId::Param { local: arg, slot }, PfgNode::Slot(slot));
            }
        }

        for (block, block_data) in self.body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in block_data.statements.iter().enumerate() {
                let location = Location {
                    block,
                    statement_index,
                };
                self.collect_statement(statement, location);
            }
            let location = Location {
                block,
                statement_index: block_data.statements.len(),
            };
            self.collect_terminator(block, location);
        }
    }

    fn collect_statement(&mut self, statement: &mir::Statement<'tcx>, location: Location) {
        let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
            return;
        };
        // iterate all pointer slots in the destination via place_slots; no longer
        // restricted to destinations whose top-level type is itself a raw pointer
        let Some(dst_slots) = self.slot_table.place_slots(*lhs, self.body, self.tcx) else {
            return;
        };
        if dst_slots.is_empty() {
            return;
        }
        let dst = PfgNode::Slot(dst_slots.start);

        match rvalue {
            Rvalue::Use(operand) => {
                // slot pairing: head slot (i=0) gets a unidirectional add_edge;
                // tail slots (i>0) get add_bidirectional_edge so that pointer
                // fields nested inside the source/destination stay linked in
                // both directions (copy does not establish ownership).
                match operand {
                    Operand::Copy(src_place) | Operand::Move(src_place) => {
                        if let Some(src_slots) =
                            self.slot_table.place_slots(*src_place, self.body, self.tcx)
                        {
                            for (i, (src_slot, dst_slot)) in
                                src_slots.zip(dst_slots.clone()).enumerate()
                            {
                                let src_node = PfgNode::Slot(src_slot);
                                let dst_node = PfgNode::Slot(dst_slot);
                                if i == 0 {
                                    self.graph.add_edge(src_node, dst_node);
                                } else {
                                    // propagate direct-param status across bidirectional copy
                                    // edges so that UML suppression in add_unknown_pointee_slots
                                    // also covers slots of param copies
                                    if self.direct_param_slots.contains(&src_slot) {
                                        self.direct_param_slots.insert(dst_slot);
                                    } else if self.direct_param_slots.contains(&dst_slot) {
                                        self.direct_param_slots.insert(src_slot);
                                    }
                                    self.graph.add_bidirectional_edge(src_node, dst_node);
                                }
                            }
                        } else {
                            self.graph.add_base_edge(
                                BaseId::Unknown {
                                    location,
                                    reason: UnknownReason::UnsupportedProjection,
                                },
                                dst,
                            );
                        }
                    }
                    Operand::Constant(_) => {
                        self.collect_operand_flow(operand, dst, location);
                    }
                }
            }
            Rvalue::CopyForDeref(place) => {
                // when the source can be resolved, collect_place_flow links tail
                // slots via link_tail_slots (bidirectional); only when it cannot be
                // resolved does slot[0] get Unknown and tail slots need it too.
                if self.source_node(*place).is_none() {
                    for slot in dst_slots.clone().skip(1) {
                        self.graph.add_base_edge(
                            BaseId::Unknown {
                                location,
                                reason: UnknownReason::UnsupportedProjection,
                            },
                            PfgNode::Slot(slot),
                        );
                    }
                }
                self.collect_place_flow(*place, dst, true, location);
            }
            Rvalue::Cast(kind, operand, _) => {
                self.collect_cast(*kind, operand, dst, location);
                // collect_cast only models slot[0]; emit Unknown conservatively for
                // any nested pointer slots in the destination (e.g. *mut *mut T)
                for slot in dst_slots.clone().skip(1) {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::UnsupportedProjection,
                        },
                        PfgNode::Slot(slot),
                    );
                }
            }
            Rvalue::RawPtr(_, place) => {
                self.collect_raw_borrow_flow(*lhs, *place, dst.clone(), &dst_slots, location);
            }
            Rvalue::Ref(_, _, place) => {
                self.collect_raw_borrow_flow(*lhs, *place, dst.clone(), &dst_slots, location);
            }
            _ => {
                // only emit a conservative Unknown edge when the rvalue is itself
                // a raw-pointer value we do not specifically handle.  Non-pointer
                // rvalues (e.g. Aggregate/Repeat used to initialise structs or
                // arrays that contain pointer fields) must not pollute those slots.
                if rvalue.ty(self.body, self.tcx).is_raw_ptr() {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::UnsupportedProjection,
                        },
                        dst,
                    );
                }
            }
        }
    }

    fn instantiate_summary_source_node(
        &self,
        source: &SummarySource,
        args: &[Spanned<Operand<'tcx>>],
        location: Location,
    ) -> Option<PfgNode> {
        match source {
            SummarySource::ParamSlot { arg_index, path } => {
                let arg = args.get(*arg_index)?;
                let place = operand_place(&arg.node)?;
                self.place_path_node(place, path)
            }
            SummarySource::Unknown(reason) => {
                let base = BaseId::Unknown {
                    location,
                    reason: reason.clone(),
                };
                Some(PfgNode::Base(base))
            }
            SummarySource::OpaqueReturn => Some(PfgNode::Base(BaseId::OpaqueReturn { location })),
            SummarySource::HeapAlloc => Some(PfgNode::Base(BaseId::HeapAlloc { location })),
        }
    }

    fn place_path_node(&self, place: Place<'tcx>, path: &[SlotPathElem]) -> Option<PfgNode> {
        let slots = self.slot_table.place_slots(place, self.body, self.tcx)?;
        for slot in slots {
            let info = self.slot_table.slot_infos.get(slot)?;
            if info.path.ends_with(path) {
                return Some(PfgNode::Slot(slot));
            }
        }
        None
    }

    fn argument_path_node(
        &self,
        args: &[Spanned<Operand<'tcx>>],
        arg_index: usize,
        path: &[SlotPathElem],
    ) -> Option<PfgNode> {
        let arg = args.get(arg_index)?;
        let place = operand_place(&arg.node)?;
        self.place_path_node(place, path)
    }

    fn destination_path_node(
        &self,
        destination: Place<'tcx>,
        path: &[SlotPathElem],
    ) -> Option<PfgNode> {
        self.place_path_node(destination, path)
    }

    fn should_skip_unknown_memory_load_on_node(&self, dst: &PfgNode) -> bool {
        matches!(dst, PfgNode::Slot(slot) if self.direct_param_slots.contains(slot))
    }

    fn collect_summary_call(
        &mut self,
        callee: LocalDefId,
        args: &[Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        location: Location,
    ) -> bool {
        let Some(summary) = self
            .callee_summaries
            .and_then(|summaries| summaries.get(&callee))
            .cloned()
        else {
            return false;
        };
        if !summary.is_complete() {
            return false;
        }

        self.apply_summary(&summary, args, destination, location)
    }

    fn apply_summary(
        &mut self,
        summary: &FunctionSummary,
        args: &[Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        location: Location,
    ) -> bool {
        let mut return_edges = Vec::new();
        let mut arg_write_edges: FxHashMap<(usize, SlotIdx), Vec<PfgNode>> = FxHashMap::default();
        let mut unknown_returns = Vec::new();
        let mut unknown_arg_writes = Vec::new();

        for flow in &summary.return_flows {
            let Some(src) = self.instantiate_summary_source_node(&flow.src, args, location) else {
                return false;
            };
            let Some(dst) = self.destination_path_node(destination, &flow.dst_return_path) else {
                return false;
            };
            return_edges.push((src, dst));
        }

        for flow in &summary.arg_write_flows {
            let Some(src) = self.instantiate_summary_source_node(&flow.src, args, location) else {
                return false;
            };
            let Some(dst) = self.argument_path_node(args, flow.dst_arg_index, &flow.dst_path)
            else {
                return false;
            };
            let PfgNode::Slot(destination) = dst else {
                return false;
            };
            arg_write_edges
                .entry((flow.dst_arg_index, destination))
                .or_default()
                .push(src);
        }

        for path in &summary.unknown_return_slots {
            let Some(dst) = self.destination_path_node(destination, path) else {
                return false;
            };
            unknown_returns.push(dst);
        }

        for target in &summary.unknown_arg_writes {
            let Some(dst) = self.argument_path_node(args, target.arg_index, &target.path) else {
                return false;
            };
            let PfgNode::Slot(destination) = dst else {
                return false;
            };
            unknown_arg_writes.push(InstantiatedUnknownArgWrite {
                dst_arg_index: target.arg_index,
                destination,
            });
        }

        for (src, dst) in return_edges {
            if let PfgNode::Base(base) = &src {
                self.graph.add_base(base.clone());
            }
            self.graph.add_edge(src, dst);
        }

        let mut writes = Vec::with_capacity(arg_write_edges.len());
        for ((dst_arg_index, destination), sources) in arg_write_edges {
            for src in &sources {
                if let PfgNode::Base(base) = src {
                    self.graph.add_base(base.clone());
                }
                self.graph.add_edge(src.clone(), PfgNode::Slot(destination));
            }
            writes.push(InstantiatedArgWrite {
                dst_arg_index,
                destination,
                sources,
            });
        }
        writes.sort_by_key(|write| (write.dst_arg_index, write.destination));
        unknown_arg_writes.sort_by_key(|write| (write.dst_arg_index, write.destination));

        for dst in unknown_returns {
            self.graph
                .add_base_edge(BaseId::OpaqueReturn { location }, dst);
        }

        for write in &unknown_arg_writes {
            let dst = PfgNode::Slot(write.destination);
            if self.should_skip_unknown_memory_load_on_node(&dst) {
                continue;
            }
            self.graph.add_base_edge(
                BaseId::Unknown {
                    location,
                    reason: UnknownReason::UnsupportedMemoryLoad,
                },
                dst,
            );
        }

        self.call_effects.insert(
            location,
            CallEffects {
                complete: true,
                writes,
                unknown_writes: unknown_arg_writes,
            },
        );

        true
    }

    fn collect_terminator(&mut self, block: BasicBlock, location: Location) {
        let terminator = self.body.basic_blocks[block].terminator();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            return;
        };

        let call = call_name(self.tcx, func);

        if let Some((def_id, _name)) = call.as_ref()
            && let Some(local_def_id) = def_id.as_local()
            && self.collect_summary_call(local_def_id, args, *destination, location)
        {
            return;
        }

        if let Some((def_id, name)) = call.as_ref()
            && let Some(summary) =
                builtin_summary(self.tcx, *def_id, name, args, *destination, self.body)
            && self.apply_summary(&summary, args, *destination, location)
        {
            return;
        }

        if !call
            .as_ref()
            .is_some_and(|(def_id, name)| call_no_writes(self.tcx, *def_id, name))
        {
            // a *mut *mut T argument lets the callee overwrite the pointed-to
            // pointer through the double-pointer, changing its base in the caller
            for arg in args.iter() {
                if let Some(place) = operand_place(&arg.node) {
                    let arg_ty = place.ty(self.body, self.tcx).ty;
                    if let Some(inner) = arg_ty.builtin_deref(true)
                        && count_slots(inner, self.tcx, &mut FxHashSet::default()) > 0
                    {
                        self.add_unknown_pointee_slots(place, location);
                    }
                }
            }
        }

        if let Some((def_id, name)) = call {
            if is_pointer_arithmetic(self.tcx, def_id, &name) {
                let Some(dst) = self.destination_node(*destination, location) else {
                    return;
                };
                if let Some(arg) = args.first() {
                    self.collect_operand_head_flow(&arg.node, dst, location);
                } else {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::UnsupportedCall,
                        },
                        dst,
                    );
                }
                return;
            }

            if call_propagates_first_arg(self.tcx, def_id, &name, args, *destination, self.body) {
                let Some(dst) = self.destination_node(*destination, location) else {
                    return;
                };
                if let Some(arg) = args.first() {
                    self.collect_operand_head_flow(&arg.node, dst, location);
                } else {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::UnsupportedCall,
                        },
                        dst,
                    );
                }
                return;
            }

            if is_as_ptr(self.tcx, def_id, &name)
                && let Some(arg) = args.first()
                && let Some(place) = operand_place(&arg.node)
            {
                if let Some(dst) = self.destination_node(*destination, location) {
                    if let Some(base) = self.local_array_base_from_place(place, location) {
                        self.graph.add_base_edge(base, dst);
                    } else if self.source_node(place).is_some() {
                        self.collect_place_flow(place, dst, false, location);
                    } else {
                        let base = self.base_for_raw_borrow(place, location);
                        self.graph.add_base_edge(base, dst);
                    }
                }
                return;
            }

            if is_heap_alloc_call(self.tcx, def_id, self.alloc_fns) {
                let Some(dst) = self.destination_node(*destination, location) else {
                    return;
                };
                let return_node = PfgNode::CallReturn(location);
                self.graph
                    .add_base_edge(BaseId::HeapAlloc { location }, return_node.clone());
                self.graph.add_edge(return_node, dst.clone());
                self.add_unknown_pointee_slots(*destination, location);
                return;
            }

            if is_null_ptr_call(self.tcx, def_id, &name) {
                if let Some(dst) = self.destination_node(*destination, location) {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::NullLike,
                        },
                        dst,
                    );
                }
                return;
            }
        }

        // generic: one CallReturn node with an add_edge to every slot in the destination range
        let return_node = PfgNode::CallReturn(location);
        self.graph
            .add_base_edge(BaseId::OpaqueReturn { location }, return_node.clone());
        if let Some(slots) = self
            .slot_table
            .place_slots(*destination, self.body, self.tcx)
        {
            for slot in slots {
                self.graph
                    .add_edge(return_node.clone(), PfgNode::Slot(slot));
            }
        }
        self.add_unknown_pointee_slots(*destination, location);
    }

    fn collect_cast(
        &mut self,
        kind: CastKind,
        operand: &Operand<'tcx>,
        dst: PfgNode,
        location: Location,
    ) {
        match kind {
            CastKind::PointerWithExposedProvenance => {
                // `0 as *mut T` is a null pointer sentinel — treat as NullLike so that
                // variables null-initialized via integer cast can participate in groups.
                if is_zero_int_operand(operand, self.tcx) {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::NullLike,
                        },
                        dst,
                    );
                } else {
                    let cast_node = PfgNode::CastResult(location);
                    self.graph
                        .add_base_edge(BaseId::IntToPtr { location }, cast_node.clone());
                    self.graph.add_edge(cast_node, dst);
                }
            }
            CastKind::PointerCoercion(ty::adjustment::PointerCoercion::ArrayToPointer, _) => {
                if let Some(place) = operand_place(operand)
                    && let Some(base) = self.local_array_base_from_place(place, location)
                {
                    let cast_node = PfgNode::CastResult(location);
                    self.graph.add_base_edge(base, cast_node.clone());
                    self.graph.add_edge(cast_node, dst);
                } else {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::UnsupportedProjection,
                        },
                        dst,
                    );
                }
            }
            CastKind::PtrToPtr
            | CastKind::PointerCoercion(ty::adjustment::PointerCoercion::MutToConstPointer, _)
            | CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, _) => {
                self.collect_operand_head_flow(operand, dst, location);
            }
            _ => {
                if operand.constant().is_some() {
                    self.graph.add_base_edge(
                        BaseId::Unknown {
                            location,
                            reason: UnknownReason::ConstantPointer,
                        },
                        dst,
                    );
                } else {
                    self.collect_operand_head_flow(operand, dst, location);
                }
            }
        }
    }

    fn collect_operand_flow(&mut self, operand: &Operand<'tcx>, dst: PfgNode, location: Location) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.collect_place_flow(*place, dst, true, location);
            }
            Operand::Constant(_) => {
                if is_empty_array_ref_ty(operand.ty(self.body, self.tcx), self.tcx) {
                    return;
                }
                self.graph.add_base_edge(
                    BaseId::Unknown {
                        location,
                        reason: constant_pointer_reason(operand, self.tcx),
                    },
                    dst,
                );
            }
        }
    }

    fn collect_operand_head_flow(
        &mut self,
        operand: &Operand<'tcx>,
        dst: PfgNode,
        location: Location,
    ) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.collect_place_flow(*place, dst, false, location);
            }
            Operand::Constant(_) => {
                if is_empty_array_ref_ty(operand.ty(self.body, self.tcx), self.tcx) {
                    return;
                }
                self.graph.add_base_edge(
                    BaseId::Unknown {
                        location,
                        reason: constant_pointer_reason(operand, self.tcx),
                    },
                    dst,
                );
            }
        }
    }

    fn collect_place_flow(
        &mut self,
        place: Place<'tcx>,
        dst: PfgNode,
        link_tail_slots: bool,
        location: Location,
    ) {
        if let Some(src) = self.source_node(place) {
            self.graph.add_edge(src.clone(), dst.clone());
            if link_tail_slots {
                self.link_tail_slots(place, dst);
            }
        } else {
            self.graph.add_base_edge(
                BaseId::Unknown {
                    location,
                    reason: UnknownReason::UnsupportedProjection,
                },
                dst,
            );
        }
    }

    fn source_slots(&self, place: Place<'tcx>) -> Option<Range<SlotIdx>> {
        let slots = self.slot_table.place_slots(place, self.body, self.tcx)?;
        if slots.is_empty() { None } else { Some(slots) }
    }

    fn destination_slots(&self, place: Place<'tcx>) -> Option<Range<SlotIdx>> {
        let slots = self.slot_table.place_slots(place, self.body, self.tcx)?;
        if slots.is_empty() { None } else { Some(slots) }
    }

    fn source_node(&self, place: Place<'tcx>) -> Option<PfgNode> {
        self.source_slots(place)?.next().map(PfgNode::Slot)
    }

    fn destination_node(&mut self, place: Place<'tcx>, location: Location) -> Option<PfgNode> {
        if let Some(mut slots) = self.destination_slots(place) {
            slots.next().map(PfgNode::Slot)
        } else {
            self.graph.add_base(BaseId::Unknown {
                location,
                reason: UnknownReason::UnsupportedProjection,
            });
            None
        }
    }

    fn add_unknown_pointee_slots(&mut self, place: Place<'tcx>, location: Location) {
        let Some(slots) = self.slot_table.place_slots(place, self.body, self.tcx) else {
            return;
        };
        // Only mark true pointee slots (depth > 0) as unknown; sibling field
        // slots in a struct destination (depth = 0) are NOT pointees and must
        // not be polluted here.
        for slot in slots.skip(1) {
            if self.slot_table.slot_infos[slot].depth == 0 {
                continue;
            }
            if self.should_skip_unknown_memory_load_on_node(&PfgNode::Slot(slot)) {
                continue;
            }
            self.graph.add_base_edge(
                BaseId::Unknown {
                    location,
                    reason: UnknownReason::UnsupportedMemoryLoad,
                },
                PfgNode::Slot(slot),
            );
        }
    }

    fn collect_address_links(
        &mut self,
        destination: Place<'tcx>,
        borrowed: Place<'tcx>,
        _location: Location,
    ) {
        let Some(borrowed_slots) = self.slot_table.place_slots(borrowed, self.body, self.tcx)
        else {
            return;
        };
        let Some(pointee_slots) = self
            .slot_table
            .place_slots(destination, self.body, self.tcx)
            .map(|slots| slots.start + 1..slots.end)
        else {
            return;
        };

        for (borrowed_slot, pointee_slot) in borrowed_slots.zip(pointee_slots) {
            self.graph
                .add_bidirectional_edge(PfgNode::Slot(borrowed_slot), PfgNode::Slot(pointee_slot));
        }
    }

    /// Shared implementation for `Rvalue::Ref` and `Rvalue::RawPtr`.
    ///
    /// When the borrowed place is a simple `*local_ptr` (deref of a raw pointer),
    /// propagate provenance from `local_ptr`'s slot rather than minting a fresh
    /// `RawBorrow` base.
    fn collect_raw_borrow_flow(
        &mut self,
        lhs: Place<'tcx>,
        place: Place<'tcx>,
        dst: PfgNode,
        dst_slots: &std::ops::Range<SlotIdx>,
        location: Location,
    ) {
        // The reborrow pattern `&mut *(_5: *mut T)` gives `_4: &mut T`,
        // and `&raw mut *(_4: &mut T)` gives `_3: *mut T`.
        let propagated = if let [ProjectionElem::Deref] = place.projection.as_ref()
            && (self.local_ty(place.local).is_raw_ptr() || self.local_ty(place.local).is_ref())
            && let Some(slot) = self.slot_table.local_head_slot(place.local)
        {
            self.graph.add_edge(PfgNode::Slot(slot), dst.clone());
            true
        } else {
            false
        };

        if !propagated {
            let base = self.base_for_raw_borrow(place, location);
            self.graph.add_base_edge(base, dst.clone());
        }

        self.collect_address_links(lhs, place, location);

        if self
            .slot_table
            .place_slots(place, self.body, self.tcx)
            .is_none()
        {
            for slot in dst_slots.clone().skip(1) {
                self.graph.add_base_edge(
                    BaseId::Unknown {
                        location,
                        reason: UnknownReason::UnsupportedProjection,
                    },
                    PfgNode::Slot(slot),
                );
            }
        }
    }

    fn link_tail_slots(&mut self, src: Place<'tcx>, dst_head: PfgNode) {
        let Some(dst_slot) = dst_head.as_slot() else {
            return;
        };
        let Some(src_slots) = self.slot_table.place_slots(src, self.body, self.tcx) else {
            return;
        };
        let dst_slots = dst_slot..dst_slot + src_slots.len();

        for (src_slot, dst_slot) in src_slots.skip(1).zip(dst_slots.skip(1)) {
            // propagate direct-param status across copy edges so that UML suppression
            // in add_unknown_pointee_slots also covers slots of param copies
            if self.direct_param_slots.contains(&src_slot) {
                self.direct_param_slots.insert(dst_slot);
            } else if self.direct_param_slots.contains(&dst_slot) {
                self.direct_param_slots.insert(src_slot);
            }
            self.graph
                .add_bidirectional_edge(PfgNode::Slot(src_slot), PfgNode::Slot(dst_slot));
        }
    }

    fn base_for_raw_borrow(&self, place: Place<'tcx>, location: Location) -> BaseId {
        if let Some(base) = self.local_array_base_from_place(place, location) {
            return base;
        }

        if place.projection.is_empty() && !self.local_ty(place.local).is_raw_ptr() {
            return BaseId::LocalScalar { local: place.local };
        }

        BaseId::RawBorrow {
            target: self.slot_table.place_head_slot(place, self.body, self.tcx),
            location,
        }
    }

    fn local_array_base_from_place(
        &self,
        place: Place<'tcx>,
        _location: Location,
    ) -> Option<BaseId> {
        if place.projection.iter().any(is_array_projection) {
            return Some(BaseId::LocalArray { local: place.local });
        }

        self.array_source_for_local(place.local, &mut FxHashSet::default())
            .map(|local| BaseId::LocalArray { local })
    }

    fn array_source_for_local(
        &self,
        local: Local,
        visited: &mut FxHashSet<Local>,
    ) -> Option<Local> {
        if !visited.insert(local) {
            return None;
        }

        if matches!(self.local_ty(local).kind(), ty::TyKind::Array(..)) {
            return Some(local);
        }

        for rhs in self.rhs_map.get(&local).into_iter().flatten() {
            match rhs {
                AssignRhs::ArrayBorrow(place) => {
                    if matches!(self.local_ty(place.local).kind(), ty::TyKind::Array(..))
                        || place.projection.iter().any(is_array_projection)
                        || matches!(
                            place.ty(self.body, self.tcx).ty.kind(),
                            ty::TyKind::Array(..)
                        )
                    {
                        return Some(place.local);
                    }
                }
                AssignRhs::Follow(src_local) => {
                    if let Some(array_local) = self.array_source_for_local(*src_local, visited) {
                        return Some(array_local);
                    }
                }
            }
        }

        None
    }

    fn local_ty(&self, local: Local) -> Ty<'tcx> {
        self.body.local_decls[local].ty
    }
}

pub(crate) fn is_array_projection(elem: ProjectionElem<Local, Ty<'_>>) -> bool {
    matches!(
        elem,
        ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
    )
}

pub(crate) fn operand_place<'tcx>(operand: &Operand<'tcx>) -> Option<Place<'tcx>> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(*place),
        Operand::Constant(_) => None,
    }
}

pub fn pointer_flow_analysis(
    input: &RustProgram<'_>,
    alloc_fns: &FxHashSet<LocalDefId>,
) -> FxHashMap<LocalDefId, PointerFlowResult> {
    let call_graph = CallGraphPostOrder::new(input);
    let function_set: FxHashSet<LocalDefId> = input.functions.iter().copied().collect();
    let mut summaries: FxHashMap<LocalDefId, FunctionSummary> = FxHashMap::default();
    let mut results: FxHashMap<LocalDefId, PointerFlowResult> = FxHashMap::default();

    for scc in call_graph.sccs() {
        let local_scc: Vec<LocalDefId> = scc
            .iter()
            .filter_map(|def_id| def_id.as_local())
            .filter(|def_id| function_set.contains(def_id))
            .collect();
        if local_scc.is_empty() {
            continue;
        }

        for &def_id in &local_scc {
            summaries.entry(def_id).or_default();
        }

        let mut stabilized = false;
        for _ in 0..32 {
            let mut changed = false;
            for &def_id in &local_scc {
                let body = input
                    .tcx
                    .mir_drops_elaborated_and_const_checked(def_id)
                    .borrow();
                let result = analyze_body_with_summaries(
                    input.tcx,
                    def_id,
                    &body,
                    alloc_fns,
                    Some(&summaries),
                );
                let mut summary = build_function_summary(input.tcx, def_id, &body, &result);
                summary.normalize();
                changed |= summaries.get(&def_id) != Some(&summary);
                summaries.insert(def_id, summary);
                results.insert(def_id, result);
            }
            if !changed {
                stabilized = true;
                break;
            }
        }

        if !stabilized {
            for &def_id in &local_scc {
                summaries.remove(&def_id);
            }
            for &def_id in &local_scc {
                let body = input
                    .tcx
                    .mir_drops_elaborated_and_const_checked(def_id)
                    .borrow();
                let result = analyze_body_with_summaries(
                    input.tcx,
                    def_id,
                    &body,
                    alloc_fns,
                    Some(&summaries),
                );
                results.insert(def_id, result);
            }
        }
    }

    results
}

pub(crate) fn analyze_body_with_summaries<'tcx>(
    tcx: TyCtxt<'tcx>,
    _def_id: LocalDefId,
    body: &Body<'tcx>,
    alloc_fns: &FxHashSet<LocalDefId>,
    callee_summaries: Option<&FxHashMap<LocalDefId, FunctionSummary>>,
) -> PointerFlowResult {
    let slot_table = SlotTable::new(body, tcx);
    let (field_accesses, field_rejects) = FieldEventScanner::scan(tcx, body, &slot_table);
    let rhs_map = build_rhs_map(body, tcx);
    let mut collector = Collector {
        tcx,
        body,
        alloc_fns,
        callee_summaries,
        slot_table: &slot_table,
        graph: PointerFlowGraph::default(),
        rhs_map,
        direct_param_slots: FxHashSet::default(),
        call_effects: FxHashMap::default(),
        field_accesses,
        field_rejects,
    };
    collector.collect();
    let graph = collector.graph;
    let call_effects = collector.call_effects;
    let field_accesses = collector.field_accesses;
    let field_rejects = collector.field_rejects;
    let provenance = solve_reachable_bases(&graph);

    PointerFlowResult {
        slot_table,
        graph,
        provenance,
        call_effects,
        field_accesses,
        field_rejects,
    }
}
