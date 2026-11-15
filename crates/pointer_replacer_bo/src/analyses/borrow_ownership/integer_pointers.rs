use std::hash::Hash;

use rustc_abi::{FIRST_VARIANT, FieldIdx};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        AggregateKind, Body, Local, Location, Operand, Place, PlaceElem, RETURN_PLACE, Rvalue,
        StatementKind,
        visit::{PlaceContext, Visitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::{DefId, LocalDefId};

use super::{
    SlotKind,
    crate_slots::{CrateSlots, MAX_SLOT_DEPTH},
    resolve::{ResolvedSlot, resolve_place},
    slots::{SlotId, SlotOwner},
    solver::{KindSolver, SlotRef},
    source_events::operand_is_null,
};
use crate::{analyses::mir::TerminatorExt, utils::rustc::RustProgram};

/// Integer reconstruction has no modeled loan origin. In particular, an integer
/// MIR place must never acquire a synthetic Deref projection in the loan builder.
pub(super) fn is_integer_reconstruction<'tcx>(
    rvalue: &Rvalue<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    matches!(rvalue, Rvalue::Cast(_, operand, target)
        if target.is_raw_ptr() && operand.ty(body, tcx).is_integral())
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Local(LocalDefId, Local),
    Field(DefId),
    Static(DefId),
}

fn reachable<N: Copy + Eq + Hash>(
    edges: &FxHashMap<N, Vec<N>>,
    seeds: impl IntoIterator<Item = N>,
) -> FxHashSet<N> {
    let mut pending: Vec<_> = seeds.into_iter().collect();
    let mut reached = FxHashSet::default();
    while let Some(node) = pending.pop() {
        if reached.insert(node)
            && let Some(next) = edges.get(&node)
        {
            pending.extend(next);
        }
    }
    reached
}

#[derive(Default)]
struct AddressFlow<'tcx> {
    values: FxHashMap<Node, Vec<Node>>,
    connections: FxHashMap<Node, Vec<Node>>,
    places: FxHashMap<LocalDefId, FxHashMap<Place<'tcx>, Node>>,
    calls: FxHashMap<LocalDefId, Vec<LocalDefId>>,
    exposed: Vec<Node>,
    escapes: Vec<(LocalDefId, Node)>,
    reconstructed: Vec<(LocalDefId, Node)>,
    aggregates: FxHashSet<(Node, Ty<'tcx>)>,
}

impl<'tcx> AddressFlow<'tcx> {
    fn connect(&mut self, source: Node, destination: Node) {
        self.connections
            .entry(source)
            .or_default()
            .push(destination);
        self.connections
            .entry(destination)
            .or_default()
            .push(source);
    }

    fn transfer(&mut self, source: Node, destination: Node) {
        self.connect(source, destination);
        self.values.entry(source).or_default().push(destination);
    }

    fn place(
        &mut self,
        function: LocalDefId,
        place: Place<'tcx>,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Node {
        let mut node = Node::Local(function, place.local);
        self.places
            .entry(function)
            .or_default()
            .insert(Place::from(place.local), node);
        for (prefix, element) in place.iter_projections() {
            if let PlaceElem::Field(index, _) = element
                && let TyKind::Adt(adt, _) = prefix.ty(body, tcx).ty.kind()
            {
                let variant = prefix.ty(body, tcx).variant_index.unwrap_or(FIRST_VARIANT);
                let field = Node::Field(adt.variant(variant).fields[index].did);
                self.connect(node, field);
                node = field;
            }
            self.places
                .entry(function)
                .or_default()
                .insert(prefix.project_deeper(&[element], tcx), node);
        }
        self.aggregate(node, place.ty(body, tcx).ty, tcx);
        node
    }

    fn aggregate(&mut self, node: Node, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) {
        if !self.aggregates.insert((node, ty)) {
            return;
        }
        match ty.kind() {
            TyKind::Adt(adt, arguments) => {
                for field in adt.all_fields() {
                    let ty = field.ty(tcx, arguments);
                    if carries_address(ty) {
                        let member = Node::Field(field.did);
                        self.transfer(node, member);
                        self.transfer(member, node);
                        self.aggregate(member, ty, tcx);
                    }
                }
            }
            TyKind::Tuple(elements) => {
                for ty in elements.iter() {
                    self.aggregate(node, ty, tcx);
                }
            }
            TyKind::Array(element, _) | TyKind::Slice(element) => {
                self.aggregate(node, *element, tcx)
            }
            _ => {}
        }
    }

    fn operand(
        &mut self,
        function: LocalDefId,
        operand: &Operand<'tcx>,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<Node> {
        if let Some(place) = operand.place() {
            Some(self.place(function, place, body, tcx))
        } else if let Operand::Constant(constant) = operand {
            constant.check_static_ptr(tcx).map(Node::Static)
        } else {
            None
        }
    }

    fn assignment(
        &mut self,
        function: LocalDefId,
        destination: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) {
        let output = self.place(function, destination, body, tcx);
        if !destination.projection.is_empty() || destination.local == RETURN_PLACE {
            self.escapes.push((function, output));
        }
        if is_integer_reconstruction(rvalue, body, tcx)
            && let Rvalue::Cast(_, operand, _) = rvalue
            && !(matches!(operand, Operand::Constant(_)) && operand_is_null(operand, &[], tcx))
        {
            self.reconstructed.push((function, output));
        }
        if let Rvalue::Cast(_, operand, target) = rvalue
            && target.is_integral()
            && operand.ty(body, tcx).is_any_ptr()
        {
            self.exposed.push(output);
        }
        // Comparisons and length/discriminant observations carry no address value.
        if !carries_address(destination.ty(body, tcx).ty) {
            return;
        }
        let mut transfer = |operand: &Operand<'tcx>, output| {
            if carries_address(operand.ty(body, tcx))
                && let Some(source) = self.operand(function, operand, body, tcx)
            {
                self.transfer(source, output);
            }
        };
        match rvalue {
            Rvalue::Use(operand)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::UnaryOp(_, operand)
            | Rvalue::Repeat(operand, _)
            | Rvalue::ShallowInitBox(operand, _) => transfer(operand, output),
            Rvalue::BinaryOp(_, operands) => {
                transfer(&operands.0, output);
                transfer(&operands.1, output);
            }
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) | Rvalue::CopyForDeref(place) => {
                let source = self.place(function, *place, body, tcx);
                self.transfer(source, output);
            }
            Rvalue::Aggregate(kind, operands) => {
                for (index, operand) in operands.iter().enumerate() {
                    let field = if let AggregateKind::Adt(adt, variant, _, _, active) = **kind {
                        Some(Node::Field(
                            tcx.adt_def(adt).variant(variant).fields
                                [active.unwrap_or_else(|| FieldIdx::from_usize(index))]
                            .did,
                        ))
                    } else {
                        None
                    };
                    if let Some(field) = field {
                        self.transfer(field, output);
                        self.transfer(output, field);
                        self.escapes.push((function, field));
                    }
                    if carries_address(operand.ty(body, tcx))
                        && let Some(source) = self.operand(function, operand, body, tcx)
                    {
                        self.transfer(source, field.unwrap_or(output));
                    }
                }
            }
            Rvalue::ThreadLocalRef(definition) => self.transfer(Node::Static(*definition), output),
            _ => {}
        }
    }
}

fn carries_address(ty: Ty<'_>) -> bool {
    ty.is_integral()
        || ty.is_floating_point()
        || ty.is_any_ptr()
        || matches!(
            ty.kind(),
            TyKind::Adt(..) | TyKind::Tuple(..) | TyKind::Array(..) | TyKind::Slice(..)
        )
}

pub(super) fn constrain_integer_boundaries(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    solver: &KindSolver,
) {
    let tcx = program.tcx;
    if !program.functions.iter().any(|&function| {
        let body = tcx.mir_drops_elaborated_and_const_checked(function).borrow();
        body.basic_blocks.iter().any(|block| block.statements.iter().any(|statement| {
            matches!(&statement.kind, StatementKind::Assign(box (_, Rvalue::Cast(_, operand, target)))
                if (target.is_raw_ptr() && operand.ty(&*body, tcx).is_integral())
                    || (target.is_integral() && operand.ty(&*body, tcx).is_any_ptr()))
        }))
    }) {
        return;
    }
    let arguments: FxHashMap<_, _> = program
        .functions
        .iter()
        .map(|&function| {
            (
                function,
                tcx.mir_drops_elaborated_and_const_checked(function)
                    .borrow()
                    .arg_count,
            )
        })
        .collect();
    let mut flow = AddressFlow::default();
    for &function in &program.functions {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        struct Places<'a, 'tcx> {
            flow: &'a mut AddressFlow<'tcx>,
            function: LocalDefId,
            body: &'a Body<'tcx>,
            tcx: TyCtxt<'tcx>,
        }
        impl<'tcx> Visitor<'tcx> for Places<'_, 'tcx> {
            fn visit_place(&mut self, place: &Place<'tcx>, _: PlaceContext, _: Location) {
                self.flow.place(self.function, *place, self.body, self.tcx);
            }
        }
        Places {
            flow: &mut flow,
            function,
            body: &body,
            tcx,
        }
        .visit_body(&body);
        for local in body.local_decls.indices() {
            flow.place(function, Place::from(local), &body, tcx);
        }
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                if let StatementKind::Assign(box (destination, rvalue)) = &statement.kind {
                    flow.assignment(function, *destination, rvalue, &body, tcx);
                }
            }
            if let Some(call) = block.terminator().as_call(tcx) {
                let destination = flow.place(function, call.destination, &body, tcx);
                let callee = call
                    .func
                    .did()
                    .and_then(DefId::as_local)
                    .filter(|callee| arguments.contains_key(callee));
                if let Some(callee) = callee {
                    flow.calls.entry(callee).or_default().push(function);
                    flow.calls.entry(function).or_default().push(callee);
                    flow.transfer(Node::Local(callee, RETURN_PLACE), destination);
                }
                let mut actuals = Vec::new();
                for (index, argument) in call.args.iter().enumerate() {
                    if carries_address(argument.node.ty(&*body, tcx))
                        && let Some(actual) = flow.operand(function, &argument.node, &body, tcx)
                    {
                        actuals.push(actual);
                        if let Some(callee) = callee.filter(|callee| index < arguments[callee]) {
                            flow.transfer(
                                actual,
                                Node::Local(callee, Local::from_usize(index + 1)),
                            );
                        } else {
                            flow.escapes.push((function, actual));
                            if carries_address(call.destination.ty(&*body, tcx).ty) {
                                flow.transfer(actual, destination);
                            }
                        }
                    }
                }
                // Unknown code can also retain an argument through another one.
                if callee.is_none() {
                    for &actual in &actuals {
                        for &other in &actuals {
                            flow.transfer(actual, other);
                        }
                    }
                }
            }
        }
    }
    let exposed = reachable(&flow.values, flow.exposed.iter().copied());
    let mut seeds: FxHashSet<_> = flow.reconstructed.iter().map(|&(_, node)| node).collect();
    let mut hazardous: FxHashSet<_> = flow
        .reconstructed
        .iter()
        .map(|&(function, _)| function)
        .collect();
    for &(function, node) in &flow.escapes {
        if exposed.contains(&node) {
            seeds.insert(node);
            hazardous.insert(function);
        }
    }
    // Reconstructed addresses may alias memory without an explicit value-flow
    // edge. Retain every raw layer in connected scopes and analyzed call components.
    loop {
        let previous = (seeds.len(), hazardous.len());
        let unknown = reachable(&flow.connections, seeds.iter().copied());
        for (&function, places) in &flow.places {
            if places.values().any(|node| unknown.contains(node)) {
                hazardous.insert(function);
            }
        }
        hazardous = reachable(&flow.calls, hazardous);
        for function in &hazardous {
            seeds.extend(flow.places[function].values().copied());
        }
        if previous == (seeds.len(), hazardous.len()) {
            break;
        }
    }
    let connected = reachable(&flow.connections, seeds);
    let mut pinned = FxHashSet::default();
    for index in 0..slots.field_slots.len() {
        let id = SlotId::from_usize(index);
        let slot = slots.field_slots.slot(id);
        let SlotOwner::Field(field) = slot.owner else { continue };
        let definition = &tcx.adt_def(field.struct_did).non_enum_variant().fields
            [FieldIdx::from_usize(field.field_index)];
        let mut ty = tcx.type_of(definition.did).instantiate_identity();
        if slots.field_slots.is_array_field(field)
            && let TyKind::Array(element, _) = ty.kind()
        {
            ty = *element;
        }
        for _ in 0..slot.depth {
            let Some(pointee) = ty.builtin_deref(true) else { break };
            ty = pointee;
        }
        if connected.contains(&Node::Field(definition.did)) && ty.is_raw_ptr() {
            let reference = SlotRef::Field(id);
            if pinned.insert(reference) {
                solver.assume(reference, SlotKind::Raw);
            }
        }
    }
    for (&function, places) in &flow.places {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        for (&place, node) in places {
            if !connected.contains(node) {
                continue;
            }
            let mut ty = place.ty(&*body, tcx).ty;
            for depth in 0..MAX_SLOT_DEPTH {
                if ty.is_raw_ptr()
                    && let Some(slot) = resolve_place(slots, function, &body, place, depth, None)
                {
                    let slot = match slot {
                        ResolvedSlot::Local(slot) => SlotRef::Local(function, slot),
                        ResolvedSlot::Field(slot) => SlotRef::Field(slot),
                    };
                    if pinned.insert(slot) {
                        solver.assume(slot, SlotKind::Raw);
                    }
                }
                let Some(pointee) = ty.builtin_deref(true) else { break };
                ty = pointee;
            }
        }
    }
}
