use pointer_replacer_bo::{
    AcceptedPointerAnalysis, analyses::borrow_ownership::slots::StructFieldSlot,
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        self, AggregateKind, Local, Place, PlaceElem, PlaceRef, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{TyCtxt, TyKind},
};
use rustc_span::def_id::LocalDefId;

use super::{FieldRegion, TypeLifetimes};

pub(super) type LifetimeKey = (usize, usize, Option<FieldRegion>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Node {
    function: LocalDefId,
    local: Local,
    depth: usize,
    field: Option<FieldRegion>,
}

pub(super) struct LifetimeFlow {
    edges: FxHashMap<Node, Vec<Node>>,
}

impl LifetimeFlow {
    pub fn new(analysis: &AcceptedPointerAnalysis, types: &TypeLifetimes, tcx: TyCtxt<'_>) -> Self {
        let mut result = Self {
            edges: FxHashMap::default(),
        };
        if types.plans.is_empty() {
            return result;
        }
        for &function in analysis.slots.fn_local_slots.keys() {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let nodes = |place| place_nodes(function, place, &body, types, tcx);
            for block in body.basic_blocks.iter() {
                for statement in &block.statements {
                    let StatementKind::Assign(box (target, value)) = &statement.kind else {
                        continue;
                    };
                    let targets = nodes(*target);
                    match value {
                        Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                            if let Some(place) = operand.place() {
                                result.connect(&nodes(place), &targets, 0);
                            }
                        }
                        Rvalue::CopyForDeref(place) => result.connect(&nodes(*place), &targets, 0),
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                            result.connect(&nodes(*place), &targets, 1)
                        }
                        Rvalue::Aggregate(kind, operands) => {
                            for (index, operand) in operands.iter_enumerated() {
                                let Some(place) = operand.place() else { continue };
                                let sources = nodes(place);
                                result.connect(&sources, &targets, 0);
                                if let AggregateKind::Adt(did, ..) = **kind
                                    && tcx.adt_def(did).is_struct()
                                    && let Some(owner) = did.as_local()
                                {
                                    let field = StructFieldSlot {
                                        struct_did: owner,
                                        field_index: index.as_usize(),
                                    };
                                    if analysis.slots.field_slots.slots_for_field(field).is_none() {
                                        continue;
                                    }
                                    for &(key, source) in &sources {
                                        if key.2.is_some() {
                                            continue;
                                        }
                                        let region = FieldRegion {
                                            owner,
                                            field: index.as_usize(),
                                            depth: key.1,
                                        };
                                        let target = Node {
                                            function,
                                            local: target.local,
                                            depth: region.depth,
                                            field: Some(region),
                                        };
                                        result.edges.entry(source).or_default().push(target);
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
                let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } = &block.terminator().kind
                else {
                    continue;
                };
                let TyKind::FnDef(callee, _) = func.ty(&*body, tcx).kind() else { continue };
                let Some(callee) = callee
                    .as_local()
                    .filter(|did| analysis.slots.fn_local_slots.contains_key(did))
                else {
                    continue;
                };
                let callee_body = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
                for (index, argument) in args.iter().take(callee_body.arg_count).enumerate() {
                    if let Some(place) = argument.node.place() {
                        result.connect(
                            &nodes(place),
                            &place_nodes(
                                callee,
                                Place::from(Local::from_usize(index + 1)),
                                &callee_body,
                                types,
                                tcx,
                            ),
                            0,
                        );
                    }
                }
                result.connect(
                    &place_nodes(
                        callee,
                        Place::from(mir::RETURN_PLACE),
                        &callee_body,
                        types,
                        tcx,
                    ),
                    &nodes(*destination),
                    0,
                );
            }
        }
        result
    }

    fn connect(
        &mut self,
        sources: &[(LifetimeKey, Node)],
        targets: &[(LifetimeKey, Node)],
        shift: usize,
    ) {
        for &(source_key, source) in sources {
            for &(target_key, target) in targets {
                if source_key.2 == target_key.2
                    && (source_key.2.is_some() || source_key.1 + shift == target_key.1)
                {
                    self.edges.entry(source).or_default().push(target);
                }
            }
        }
    }

    pub fn flows(
        &self,
        function: LocalDefId,
        keys: &std::collections::BTreeSet<LifetimeKey>,
    ) -> std::collections::BTreeSet<(LifetimeKey, LifetimeKey)> {
        let mut flows = std::collections::BTreeSet::new();
        for &key in keys {
            let start = Node {
                function,
                local: Local::from_usize(key.0),
                depth: key.1,
                field: key.2,
            };
            let mut pending = vec![(start, start.field.is_some())];
            let mut visited = FxHashSet::default();
            while let Some((node, through_field)) = pending.pop() {
                if !visited.insert((node, through_field)) {
                    continue;
                }
                let target = (node.local.index(), node.depth, node.field);
                if through_field
                    && node.function == function
                    && key != target
                    && keys.contains(&target)
                {
                    flows.insert((key, target));
                }
                if let Some(targets) = self.edges.get(&node) {
                    pending.extend(
                        targets
                            .iter()
                            .map(|target| (*target, through_field || target.field.is_some())),
                    );
                }
            }
        }
        flows
    }
}

fn place_nodes<'tcx>(
    function: LocalDefId,
    place: Place<'tcx>,
    body: &mir::Body<'tcx>,
    types: &TypeLifetimes,
    tcx: TyCtxt<'tcx>,
) -> Vec<(LifetimeKey, Node)> {
    let mut field = None;
    let mut derefs = 0;
    for (index, projection) in place.projection.iter().enumerate() {
        match projection {
            PlaceElem::Deref => derefs += 1,
            PlaceElem::Field(index_field, field_ty) if field_ty.is_raw_ptr() => {
                let base = PlaceRef {
                    local: place.local,
                    projection: &place.projection[..index],
                }
                .ty(body, tcx)
                .ty;
                if let TyKind::Adt(definition, _) = base.kind()
                    && definition.is_struct()
                    && let Some(owner) = definition.did().as_local()
                {
                    field = Some((owner, index_field.as_usize()));
                    derefs = 0;
                }
            }
            _ => {}
        }
    }
    let source = place.ty(body, tcx).ty;
    let mut ty = source;
    let mut nodes = Vec::new();
    let mut depth = 0;
    while let TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) = ty.kind() {
        let region = field.map(|(owner, field)| FieldRegion {
            owner,
            field,
            depth: depth + derefs,
        });
        let node = Node {
            function,
            local: place.local,
            depth: depth + derefs,
            field: region,
        };
        nodes.push(((0, depth, None), node));
        depth += 1;
        ty = *inner;
    }
    for region in types.regions_of(source) {
        let node = Node {
            function,
            local: place.local,
            depth: region.depth,
            field: Some(region),
        };
        nodes.push(((0, region.depth, Some(region)), node));
    }
    nodes
}
