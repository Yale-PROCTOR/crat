//! Finite may-value graph; no per-index tokens, reference proofs or ownership grants.
use std::collections::BTreeSet;

use rustc_hash::{FxHashMap as Map, FxHashSet as Set};
use rustc_middle::{
    mir::{AggregateKind, Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind},
    ty::{TyCtxt, TyKind},
};
use rustc_span::def_id::LocalDefId;

use super::{ArrayFieldRow, HoldReason};
use crate::{
    analyses::{
        borrow_ownership::{
            crate_slots::CrateSlots,
            nullability::NullabilityFacts,
            slot_key,
            slots::{SlotId, SlotOwner, StructFieldSlot},
            solver::SlotRef,
            source_events,
        },
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

#[derive(Default)]
pub(super) struct Values {
    pub(super) rows: Vec<ArrayFieldRow>,
    pub(super) null_literal_slots: Vec<SlotRef>,
    pub(super) null_use_slots: Vec<SlotRef>,
    pub(super) raw_load_slots: Vec<SlotRef>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Node {
    Local(LocalDefId, Local),
    Field(StructFieldSlot),
}
#[derive(Clone, Default)]
struct Fact {
    sources: BTreeSet<String>,
    fields: Set<StructFieldSlot>,
    null: bool,
    null_use: bool,
    opaque: bool,
    unknown: bool,
}
impl Fact {
    fn join(&mut self, other: &Self) -> bool {
        let before = (
            self.sources.len(),
            self.fields.len(),
            self.null,
            self.null_use,
            self.opaque,
            self.unknown,
        );
        self.sources.extend(other.sources.iter().cloned());
        self.fields.extend(other.fields.iter().copied());
        self.null |= other.null;
        self.null_use |= other.null_use;
        self.opaque |= other.opaque;
        self.unknown |= other.unknown;
        before
            != (
                self.sources.len(),
                self.fields.len(),
                self.null,
                self.null_use,
                self.opaque,
                self.unknown,
            )
    }
}
#[derive(Clone)]
enum Value {
    Node(Node),
    Literal(Fact),
}
#[derive(Default)]
struct Graph {
    facts: Map<Node, Fact>,
    edges: Vec<(Node, Node)>,
    addresses: Map<Node, Set<StructFieldSlot>>,
    alias_edges: Vec<(Node, Node)>,
    loads: Vec<(Node, Node)>,
    stores: Vec<(Node, Value, bool)>,
    calls: Vec<Vec<Node>>,
    checks: Vec<Node>,
    initialized: Set<StructFieldSlot>,
    defined: Set<Node>,
}
impl Graph {
    fn add(&mut self, target: Node, value: Value) {
        self.defined.insert(target);
        match value {
            Value::Node(source) => {
                self.edges.push((source, target));
                self.alias_edges.push((source, target));
            }
            Value::Literal(fact) => {
                self.facts.entry(target).or_default().join(&fact);
            }
        }
    }

    fn close(&mut self) {
        loop {
            let mut changed = false;
            for &(source, target) in &self.alias_edges {
                let aliases = self.addresses.get(&source).cloned().unwrap_or_default();
                let targets = self.addresses.entry(target).or_default();
                let before = targets.len();
                targets.extend(aliases);
                changed |= before != targets.len();
            }
            if !changed {
                break;
            }
        }
        for (alias, target) in self.loads.clone() {
            let fields = self.addresses.get(&alias).cloned().unwrap_or_default();
            if fields.is_empty() {
                self.facts.entry(target).or_default().unknown = true;
            }
            for field in fields {
                self.add(target, Value::Node(Node::Field(field)));
            }
        }
        for (alias, value, whole) in self.stores.clone() {
            for field in self.addresses.get(&alias).cloned().unwrap_or_default() {
                self.add(Node::Field(field), value.clone());
                if whole {
                    self.initialized.insert(field);
                }
            }
        }
        for call in &self.calls {
            for argument in call {
                for field in self.addresses.get(argument).into_iter().flatten() {
                    self.facts.entry(Node::Field(*field)).or_default().unknown = true;
                }
            }
        }
        loop {
            let mut changed = false;
            for &(source, target) in &self.edges {
                let value = self.facts.get(&source).cloned().unwrap_or_else(|| Fact {
                    unknown: true,
                    ..Fact::default()
                });
                changed |= self.facts.entry(target).or_default().join(&value);
            }
            if !changed {
                break;
            }
        }
        for checked in &self.checks {
            let fields = self
                .facts
                .get(checked)
                .map(|fact| fact.fields.clone())
                .unwrap_or_default();
            for field in fields {
                self.facts.entry(Node::Field(field)).or_default().null_use = true;
            }
        }
    }
}

// Whole arrays and indexed elements share this declaration value node. A
// further dereference accesses the pointed-to object, not the array's cell.
fn field_place<'tcx>(
    place: Place<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<(StructFieldSlot, bool)> {
    let mut ty = body.local_decls[place.local].ty;
    let mut field = None;
    let mut indexed = false;
    for projection in place.projection {
        match projection {
            ProjectionElem::Deref if field.is_none() => {
                ty = ty.builtin_deref(true)?;
            }
            ProjectionElem::Field(index, field_ty) if field.is_none() => {
                let TyKind::Adt(adt, _) = ty.kind() else { return None };
                if !adt.is_struct() || !adt.did().is_local() {
                    return None;
                }
                let candidate = StructFieldSlot {
                    struct_did: adt.did().expect_local(),
                    field_index: index.as_usize(),
                };
                ty = field_ty;
                if matches!(ty.kind(), TyKind::Array(..) | TyKind::RawPtr(..)) {
                    field = Some(candidate);
                }
            }
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                if field.is_some() && !indexed && matches!(ty.kind(), TyKind::Array(..)) =>
            {
                ty = ty.builtin_index()?;
                indexed = true;
            }
            ProjectionElem::OpaqueCast(next) | ProjectionElem::Subtype(next) => {
                ty = next;
            }
            _ => return None,
        }
    }
    let _ = tcx;
    field.map(|field| (field, indexed))
}
fn node<'tcx>(
    place: Place<'tcx>,
    function: LocalDefId,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Node> {
    place
        .as_local()
        .map(|local| Node::Local(function, local))
        .or_else(|| field_place(place, body, tcx).map(|(field, _)| Node::Field(field)))
}
fn indirect(place: Place<'_>, function: LocalDefId) -> Option<Node> {
    (matches!(place.projection.first(), Some(ProjectionElem::Deref))
        && place.projection[1..].iter().all(|p| {
            matches!(
                p,
                ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
            )
        }))
    .then_some(Node::Local(function, place.local))
}
fn value<'tcx>(
    operand: &Operand<'tcx>,
    function: LocalDefId,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Value {
    if matches!(operand, Operand::Constant(_)) {
        let null = source_events::operand_is_null(operand, &[], tcx);
        Value::Literal(Fact {
            null,
            opaque: !null,
            ..Fact::default()
        })
    } else if let Some(source) = operand
        .place()
        .and_then(|place| node(place, function, body, tcx))
    {
        Value::Node(source)
    } else {
        Value::Literal(Fact {
            unknown: true,
            ..Fact::default()
        })
    }
}
fn tracked(ty: rustc_middle::ty::Ty<'_>) -> bool {
    ty.is_any_ptr() || matches!(ty.kind(), TyKind::Array(element, _) if element.is_raw_ptr())
}

pub(super) fn collect(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    nullable: &NullabilityFacts,
) -> Values {
    let tcx = program.tcx;
    let mut graph = Graph::default();
    let mut fields = Vec::new();
    for index in 0..slots.field_slots.len() {
        let id = SlotId::from_usize(index);
        let slot = slots.field_slots.slot(id);
        let SlotOwner::Field(field) = slot.owner else { continue };
        if slot.depth != 0 {
            continue;
        }
        let fact = graph.facts.entry(Node::Field(field)).or_default();
        if slots.field_slots.is_array_field(field) {
            fact.fields.insert(field);
            fields.push(field);
        } else {
            fact.sources.insert(slot_key::field_key(
                tcx,
                field.struct_did,
                field.field_index,
                0,
            ));
        }
        fact.null |= nullable.null_literal.contains(&SlotRef::Field(id));
        fact.null_use |= nullable.is_null_use.contains(&SlotRef::Field(id));
    }
    for &function in &program.functions {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        for (local, declaration) in body.local_decls.iter_enumerated() {
            if !tracked(declaration.ty) {
                continue;
            }
            let key = Node::Local(function, local);
            let fact = graph.facts.entry(key).or_default();
            if let Some(id) = slots.fn_local_slots[&function].slot_for_local_depth(local, 0) {
                fact.sources
                    .insert(slot_key::local_key(tcx, function, local.as_usize(), 0));
                fact.null |= nullable
                    .null_literal
                    .contains(&SlotRef::Local(function, id));
                fact.null_use |= nullable.is_null_use.contains(&SlotRef::Local(function, id));
            } else if local.as_usize() <= body.arg_count {
                fact.unknown = true;
            }
            if local.as_usize() > 0 && local.as_usize() <= body.arg_count {
                graph.defined.insert(key);
            }
        }
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (destination, rhs)) = &statement.kind else {
                    continue;
                };
                if let Rvalue::Aggregate(kind, operands) = rhs
                    && let AggregateKind::Adt(definition, _, _, _, _) = kind.as_ref()
                    && let Some(struct_did) = definition.as_local()
                {
                    for (index, operand) in operands.iter().enumerate() {
                        let field = StructFieldSlot {
                            struct_did,
                            field_index: index,
                        };
                        if slots.field_slots.is_array_field(field) {
                            graph.add(Node::Field(field), value(operand, function, &body, tcx));
                            graph.initialized.insert(field);
                        }
                    }
                    continue;
                }
                if !tracked(destination.ty(&*body, tcx).ty) {
                    continue;
                }
                let target = node(*destination, function, &body, tcx);
                let whole = matches!(destination.ty(&*body, tcx).ty.kind(), TyKind::Array(..));
                if let Some(Node::Field(field)) = target
                    && whole
                {
                    graph.initialized.insert(field);
                }
                let operand = match rhs {
                    Rvalue::Use(operand)
                    | Rvalue::Cast(_, operand, _)
                    | Rvalue::Repeat(operand, _) => Some(operand),
                    _ => None,
                };
                if let Some(target) = target {
                    match rhs {
                        Rvalue::Aggregate(kind, operands)
                            if matches!(kind.as_ref(), AggregateKind::Array(_)) =>
                        {
                            graph.defined.insert(target);
                            for operand in operands {
                                graph.add(target, value(operand, function, &body, tcx));
                            }
                        }
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                            graph.defined.insert(target);
                            if let Some((field, _)) = field_place(*place, &body, tcx)
                                && slots.field_slots.is_array_field(field)
                            {
                                graph.addresses.entry(target).or_default().insert(field);
                            } else if let Some(alias) = indirect(*place, function) {
                                // Reborrowing a known storage address preserves
                                // its declaration alias, including element selection.
                                graph.alias_edges.push((alias, target));
                            }
                        }
                        Rvalue::CopyForDeref(place) => {
                            if let Some(source) = node(*place, function, &body, tcx) {
                                graph.add(target, Value::Node(source));
                            } else if let Some(alias) = indirect(*place, function) {
                                graph.loads.push((alias, target));
                                graph.defined.insert(target);
                            } else {
                                graph.add(
                                    target,
                                    Value::Literal(Fact {
                                        unknown: true,
                                        ..Fact::default()
                                    }),
                                );
                            }
                        }
                        _ if operand.is_some() => {
                            let operand = operand.unwrap();
                            if let Some(alias) = operand
                                .place()
                                .filter(|place| node(*place, function, &body, tcx).is_none())
                                .and_then(|place| indirect(place, function))
                            {
                                graph.loads.push((alias, target));
                                graph.defined.insert(target);
                            } else {
                                graph.add(target, value(operand, function, &body, tcx));
                            }
                        }
                        _ => {
                            graph.add(
                                target,
                                Value::Literal(Fact {
                                    unknown: true,
                                    ..Fact::default()
                                }),
                            );
                        }
                    }
                } else if let Some(alias) = indirect(*destination, function) {
                    let rhs = operand
                        .map(|operand| value(operand, function, &body, tcx))
                        .unwrap_or(Value::Literal(Fact {
                            unknown: true,
                            ..Fact::default()
                        }));
                    graph.stores.push((alias, rhs, whole));
                }
            }
            let Some(call) = data.terminator().as_call(tcx) else { continue };
            let arguments: Vec<_> = call
                .args
                .iter()
                .filter_map(|argument| {
                    argument
                        .node
                        .place()
                        .and_then(|place| node(place, function, &body, tcx))
                })
                .collect();
            let null = matches!(&call.func, CallKind::RustLib(did) if tcx.crate_name(did.krate).as_str() == "core"
                && tcx.def_path_str(*did).contains("::ptr::") && matches!(tcx.item_name(*did).as_str(), "null" | "null_mut"));
            let observation = matches!(&call.func, CallKind::RustLib(did) if tcx.crate_name(did.krate).as_str() == "core"
                && tcx.def_path_str(*did).contains("::ptr::") && tcx.item_name(*did).as_str() == "is_null");
            let allocator = matches!(&call.func, CallKind::LibC(name) if matches!(name.as_str(), "malloc" | "calloc" | "realloc" | "strdup"));
            let view = matches!(&call.func, CallKind::RustLib(did) if tcx.crate_name(did.krate).as_str() == "core"
                && matches!(tcx.item_name(*did).as_str(), "as_ptr" | "as_mut_ptr"));
            if observation {
                graph.checks.extend(arguments.iter().copied());
            } else if !null && !view {
                graph.calls.push(arguments.clone());
            }
            if tracked(call.destination.ty(&*body, tcx).ty)
                && let Some(target) = node(call.destination, function, &body, tcx)
            {
                graph.defined.insert(target);
                if view {
                    if let Some(&argument) = arguments.first() {
                        graph.alias_edges.push((argument, target));
                    } else {
                        graph.facts.entry(target).or_default().unknown = true;
                    }
                } else {
                    graph.facts.entry(target).or_default().join(&Fact {
                        null,
                        opaque: !null && !allocator,
                        ..Fact::default()
                    });
                }
            }
        }
    }
    for (&node, fact) in &mut graph.facts {
        if matches!(node, Node::Local(..)) && !graph.defined.contains(&node) {
            fact.unknown = true;
        }
    }
    for &field in &fields {
        if !graph.initialized.contains(&field) {
            graph.facts.entry(Node::Field(field)).or_default().unknown = true;
        }
    }
    graph.close();
    let mut result = Values::default();
    let mut loaded: Map<StructFieldSlot, BTreeSet<String>> = Map::default();
    for (&node, fact) in &graph.facts {
        let Node::Local(function, local) = node else { continue };
        let Some(id) = slots.fn_local_slots[&function].slot_for_local_depth(local, 0) else {
            continue;
        };
        if !fact.fields.is_empty() {
            let slot = SlotRef::Local(function, id);
            if fact.null {
                result.null_literal_slots.push(slot);
            }
            if fact.null_use {
                result.null_use_slots.push(slot);
            }
            // A known array-field alias load carries the complete element
            // chain. The array wrapper itself contributes no pointer level.
            let range = slots.fn_local_slots[&function]
                .slots_for_local(local)
                .unwrap();
            for index in range.start.as_usize()..range.end.as_usize() {
                let id = SlotId::from_usize(index);
                let depth = slots.fn_local_slots[&function].slot(id).depth;
                result.raw_load_slots.push(SlotRef::Local(function, id));
                for field in &fact.fields {
                    loaded
                        .entry(*field)
                        .or_default()
                        .insert(slot_key::local_key(tcx, function, local.as_usize(), depth));
                }
            }
        }
    }
    for field in fields {
        let fact = graph
            .facts
            .get(&Node::Field(field))
            .cloned()
            .unwrap_or_default();
        let range = slots
            .field_slots
            .slots_for_field(field)
            .expect("registered array summary");
        let ids: Vec<_> = (range.start.as_usize()..range.end.as_usize())
            .map(SlotId::from_usize)
            .collect();
        if fact.null {
            result.null_literal_slots.push(SlotRef::Field(ids[0]));
        }
        if fact.null_use {
            result.null_use_slots.push(SlotRef::Field(ids[0]));
        }
        let mut holds = Vec::new();
        if fact.opaque {
            holds.push(HoldReason::OpaqueElement);
        }
        if fact.unknown {
            holds.push(HoldReason::UnknownValue);
        }
        result.rows.push(ArrayFieldRow {
            field: format!(
                "{}::field{}::element",
                tcx.def_path_str(field.struct_did.to_def_id()),
                field.field_index
            ),
            slot_keys: ids
                .iter()
                .map(|&id| {
                    slot_key::field_key(
                        tcx,
                        field.struct_did,
                        field.field_index,
                        slots.field_slots.slot(id).depth,
                    )
                })
                .collect(),
            source_slots: fact.sources.into_iter().collect(),
            loaded_slots: loaded
                .remove(&field)
                .unwrap_or_default()
                .into_iter()
                .collect(),
            null_literal: fact.null,
            opaque: fact.opaque,
            unknown: fact.unknown,
            holds,
        });
    }
    result.rows.sort_by(|a, b| a.field.cmp(&b.field));
    result.raw_load_slots.sort_by_cached_key(|slot| {
        let SlotRef::Local(function, id) = *slot else { unreachable!("local loads") };
        let descriptor = slots.fn_local_slots[&function].slot(id);
        let SlotOwner::Local(local) = descriptor.owner else { unreachable!("local slot") };
        slot_key::local_key(tcx, function, local.as_usize(), descriptor.depth)
    });
    result
}
