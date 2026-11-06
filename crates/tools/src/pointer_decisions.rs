use std::collections::{BTreeMap, BTreeSet};

use pointer_replacer_bo::{
    AcceptedPointerAnalysis, SignatureRoot, SignatureSlot,
    analyses::borrow_ownership::{
        SlotKind,
        crate_slots::MAX_SLOT_DEPTH,
        resolve::{ResolvedSlot, resolve_place},
        slots::StructFieldSlot,
        solver::SlotRef,
    },
    analyze_pointers,
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId,
    intravisit::{self, Visitor},
};
use rustc_middle::{
    mir::{AggregateKind, Local, Operand, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind},
    ty::{self, TyCtxt, TyKind},
};
use rustc_span::{Symbol, def_id::LocalDefId};

mod lifetime_flow;
mod struct_types;
pub(super) use struct_types::{FieldRegion, TypeLifetimes};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PtrKind {
    Raw(bool),
    Ref(bool),
    OptRef(bool),
    Slice(bool),
    OptSlice(bool),
    Box,
    OptBox,
    BoxedSlice,
    OptBoxedSlice,
}

impl PtrKind {
    pub fn is_mut(self) -> bool {
        match self {
            Self::Raw(mutable)
            | Self::Ref(mutable)
            | Self::OptRef(mutable)
            | Self::Slice(mutable)
            | Self::OptSlice(mutable) => mutable,
            Self::Box | Self::OptBox | Self::BoxedSlice | Self::OptBoxedSlice => true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct SigDecision {
    pub input_decs: Vec<Option<PtrKind>>,
    pub input_lifetimes: Vec<Option<Symbol>>,
    pub output_dec: Option<PtrKind>,
    pub output_lifetime: Option<Symbol>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct SigDecisions {
    pub data: FxHashMap<LocalDefId, SigDecision>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum PointerTarget {
    Input(LocalDefId, usize),
    Output(LocalDefId),
    Binding(HirId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct PointerLayer {
    pub kind: PtrKind,
    pub lifetime: Option<Symbol>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct InitialPointerDecisions {
    pub signatures: SigDecisions,
    pub bindings: FxHashMap<HirId, PtrKind>,
    nested: FxHashMap<PointerTarget, Vec<PointerLayer>>,
    pub bounds: FxHashMap<LocalDefId, Vec<(Symbol, Symbol)>>,
    pub fields: FxHashMap<StructFieldSlot, Vec<PointerLayer>>,
    pub foreign_types: FxHashSet<LocalDefId>,
    pub types: TypeLifetimes,
    pub type_arguments: FxHashMap<(LocalDefId, usize), BTreeMap<FieldRegion, Symbol>>,
}

impl InitialPointerDecisions {
    pub fn nested(&self, target: PointerTarget) -> &[PointerLayer] {
        self.nested
            .get(&target)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub fn clear_signature(&mut self, function: LocalDefId) {
        self.nested.retain(|target, _| {
            !matches!(target, PointerTarget::Input(owner, _) | PointerTarget::Output(owner) if *owner == function)
        });
        self.bounds.remove(&function);
        self.type_arguments
            .retain(|(owner, _), _| *owner != function);
    }
}

#[cfg(test)]
pub(super) fn initial_pointer_decisions(
    tcx: TyCtxt<'_>,
) -> Result<InitialPointerDecisions, String> {
    initial_pointer_decisions_for_api(tcx, &FxHashSet::default())
}

pub(super) fn initial_pointer_decisions_for_api(
    tcx: TyCtxt<'_>,
    api: &FxHashSet<String>,
) -> Result<InitialPointerDecisions, String> {
    let analysis = analyze_pointers(tcx)?;
    let representations = representation_facts(&analysis, tcx);
    let mut result = InitialPointerDecisions {
        signatures: SigDecisions {
            data: FxHashMap::default(),
        },
        bindings: FxHashMap::default(),
        nested: FxHashMap::default(),
        bounds: FxHashMap::default(),
        fields: FxHashMap::default(),
        foreign_types: struct_types::foreign_types(tcx),
        types: TypeLifetimes::default(),
        type_arguments: FxHashMap::default(),
    };
    let (exposed, layout_sensitive) = struct_types::api_structs(tcx, api);
    for &slot in analysis.kinds.keys() {
        let SlotRef::Field(slot) = slot else { continue };
        let field = analysis.slots.field_slots.slot(slot);
        let pointer_replacer_bo::analyses::borrow_ownership::slots::SlotOwner::Field(owner) =
            field.owner
        else {
            continue;
        };
        if field.depth != 0
            || analysis.slots.field_slots.is_array_field(owner)
            || result.foreign_types.contains(&owner.struct_did)
        {
            continue;
        }
        let definition = tcx.adt_def(owner.struct_did);
        let original = definition.non_enum_variant().fields
            [rustc_abi::FieldIdx::from_usize(owner.field_index)]
        .ty(
            tcx,
            ty::GenericArgs::identity_for_item(tcx, owner.struct_did),
        );
        let mut current = original;
        let mut layers = Vec::new();
        while let TyKind::RawPtr(inner, mutability) = *current.kind() {
            let depth = layers.len();
            let slot = (depth < usize::from(MAX_SLOT_DEPTH))
                .then(|| {
                    analysis
                        .slots
                        .field_slots
                        .slot_for_field_depth(owner, depth as u8)
                })
                .flatten()
                .map(SlotRef::Field);
            let kind = slot
                .and_then(|slot| analysis.kinds.get(&slot))
                .copied()
                .unwrap_or(SlotKind::Raw);
            let mutable = mutability.is_mut()
                && analysis
                    .mutability
                    .struct_field_fact(owner.struct_did, owner.field_index, depth)
                    .is_none_or(|fact| fact.is_mutable());
            let array = analysis
                .fatness
                .struct_field_fact(owner.struct_did, owner.field_index, depth)
                .is_some_and(|fact| fact.is_arr())
                || (kind == SlotKind::Owning
                    && slot
                        .and_then(|slot| representations.allocations.get(&slot))
                        .is_some_and(|sizes| {
                            let size = tcx
                                .layout_of(
                                    ty::TypingEnv::post_analysis(tcx, owner.struct_did)
                                        .as_query_input(inner),
                                )
                                .ok()
                                .map(|layout| layout.size.bytes());
                            sizes.iter().any(|bytes| bytes.is_none() || *bytes != size)
                        }));
            let optional = slot.is_some_and(|slot| representations.nullable.contains(&slot));
            // A new non-null field can change enum discriminants or Rust field ordering.
            let protected = exposed.contains(&owner.struct_did)
                && (array
                    || (depth == 0 && !optional && layout_sensitive.contains(&owner.struct_did)));
            let kind = if protected || inner.is_c_void(tcx) {
                PtrKind::Raw(mutability.is_mut())
            } else {
                representation(kind, mutable, mutability.is_mut(), array, optional)
            };
            layers.push(PointerLayer {
                kind,
                lifetime: None,
            });
            current = inner;
        }
        struct_types::mutable_ancestors(original, &mut layers);
        result.fields.insert(owner, layers);
    }
    struct_types::retain_union_compatible_fields(&mut result.fields, tcx);
    result.types = TypeLifetimes::new(&mut result.fields, tcx);
    let lifetime_flow = lifetime_flow::LifetimeFlow::new(&analysis, &result.types, tcx);
    for (&function, universe) in &analysis.slots.fn_local_slots {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let arguments = tcx
            .fn_sig(function)
            .instantiate_identity()
            .skip_binder()
            .inputs()
            .len();
        let mut locals = FxHashMap::default();
        for (local, declaration) in body.local_decls.iter_enumerated() {
            let mut original = declaration.ty;
            let mut layers = Vec::new();
            loop {
                let (TyKind::RawPtr(inner, source_mutability)
                | TyKind::Ref(_, inner, source_mutability)) = *original.kind()
                else {
                    break;
                };
                let depth = layers.len();
                if depth >= usize::from(MAX_SLOT_DEPTH) {
                    // Preserve unmodeled kinds, including the lifetimes of existing references.
                    let kind = if original.is_ref() {
                        PtrKind::Ref(source_mutability.is_mut())
                    } else {
                        PtrKind::Raw(source_mutability.is_mut())
                    };
                    layers.push(PointerLayer {
                        kind,
                        lifetime: None,
                    });
                    original = inner;
                    continue;
                }
                let depth = depth as u8;
                let Some(slot) = universe.slot_for_local_depth(local, depth) else { break };
                let slot = SlotRef::Local(function, slot);
                let kind = analysis.kinds.get(&slot).ok_or_else(|| {
                    format!(
                        "BO model has no decision for {}::{local:?} at depth {depth}",
                        tcx.def_path_str(function)
                    )
                })?;
                let mutable = source_mutability.is_mut()
                    && (representations.mutable.contains(&slot)
                        || if depth == 0 {
                            analysis.is_mutable(function, local)
                        } else {
                            analysis
                                .mutability
                                .function_body_fact(function, local.index(), depth.into())
                                .is_none_or(|fact| fact.is_mutable())
                        });
                let array = analysis
                    .fatness
                    .function_body_fact(function, local.index(), depth.into())
                    .is_some_and(|fact| fact.is_arr())
                    || (*kind == SlotKind::Owning
                        && representations.allocations.get(&slot).is_some_and(|sizes| {
                            let element_size = tcx
                                .layout_of(
                                    ty::TypingEnv::post_analysis(tcx, function)
                                        .as_query_input(inner),
                                )
                                .ok()
                                .map(|layout| layout.size.bytes());
                            sizes
                                .iter()
                                .any(|size| size.is_none() || *size != element_size)
                        }));
                let optional = representations.nullable.contains(&slot);
                let kind = if matches!(original.kind(), TyKind::Ref(..)) {
                    PtrKind::Ref(source_mutability.is_mut())
                } else if inner.is_c_void(tcx) {
                    PtrKind::Raw(source_mutability.is_mut())
                } else {
                    representation(*kind, mutable, source_mutability.is_mut(), array, optional)
                };
                layers.push(PointerLayer {
                    kind,
                    lifetime: None,
                });
                original = inner;
            }
            if !layers.is_empty() {
                struct_types::mutable_ancestors(declaration.ty, &mut layers);
                locals.insert(local, layers);
            }
        }
        let bounds = signature_lifetimes(
            function,
            arguments,
            &analysis,
            &lifetime_flow,
            &mut locals,
            &mut result,
            tcx,
        )?;
        result.bounds.insert(function, bounds);
        let mut signature = SigDecision {
            input_decs: vec![None; arguments],
            input_lifetimes: vec![None; arguments],
            output_dec: None,
            output_lifetime: None,
        };
        for index in 0..arguments {
            if let Some(layers) = locals.get(&Local::from_usize(index + 1)) {
                signature.input_decs[index] = Some(layers[0].kind);
                signature.input_lifetimes[index] = layers[0].lifetime;
                result
                    .nested
                    .insert(PointerTarget::Input(function, index), layers[1..].to_vec());
            }
        }
        if let Some(layers) = locals.get(&RETURN_PLACE) {
            signature.output_dec = Some(layers[0].kind);
            signature.output_lifetime = layers[0].lifetime;
            result
                .nested
                .insert(PointerTarget::Output(function), layers[1..].to_vec());
        }
        result.signatures.data.insert(function, signature);
        let mapping = utils::ir::map_thir_to_mir(function, false, tcx);
        for (binding, local) in mapping.binding_to_local {
            if let Some(layers) = locals.get(&local) {
                result.bindings.insert(binding, layers[0].kind);
                let mut inner = layers[1..].to_vec();
                // Local annotations infer their region variables from the body.
                for layer in &mut inner {
                    layer.lifetime = None;
                }
                result.nested.insert(PointerTarget::Binding(binding), inner);
            }
        }
    }
    Ok(result)
}

fn representation(
    kind: SlotKind,
    mutable: bool,
    source_mutable: bool,
    array: bool,
    optional: bool,
) -> PtrKind {
    match (kind, array, optional) {
        (SlotKind::Raw, _, _) => PtrKind::Raw(source_mutable),
        (SlotKind::Ref, false, false) => PtrKind::Ref(mutable),
        (SlotKind::Ref, false, true) => PtrKind::OptRef(mutable),
        (SlotKind::Ref, true, false) => PtrKind::Slice(mutable),
        (SlotKind::Ref, true, true) => PtrKind::OptSlice(mutable),
        (SlotKind::Owning, false, false) => PtrKind::Box,
        (SlotKind::Owning, false, true) => PtrKind::OptBox,
        (SlotKind::Owning, true, false) => PtrKind::BoxedSlice,
        (SlotKind::Owning, true, true) => PtrKind::OptBoxedSlice,
    }
}

fn carries_lifetime(kind: PtrKind) -> bool {
    matches!(
        kind,
        PtrKind::Ref(_) | PtrKind::OptRef(_) | PtrKind::Slice(_) | PtrKind::OptSlice(_)
    )
}

fn signature_lifetimes(
    function: LocalDefId,
    arguments: usize,
    analysis: &AcceptedPointerAnalysis,
    lifetime_flow: &lifetime_flow::LifetimeFlow,
    locals: &mut FxHashMap<Local, Vec<PointerLayer>>,
    decisions: &mut InitialPointerDecisions,
    tcx: TyCtxt<'_>,
) -> Result<Vec<(Symbol, Symbol)>, String> {
    let mut keys = BTreeSet::new();
    for index in 0..=arguments {
        if let Some(layers) = locals.get(&Local::from_usize(index)) {
            for (depth, layer) in layers.iter().enumerate() {
                if carries_lifetime(layer.kind) {
                    keys.insert((index, depth, None));
                }
            }
        }
    }
    let source_signature = tcx.fn_sig(function).instantiate_identity().skip_binder();
    for index in 0..=arguments {
        let source = if index == 0 {
            source_signature.output()
        } else {
            source_signature.inputs()[index - 1]
        };
        for region in decisions.types.regions_of(source) {
            keys.insert((index, region.depth, Some(region)));
        }
    }
    let mut fixed = BTreeMap::new();
    let mut source_regions = FxHashMap::default();
    for index in 0..=arguments {
        let mut source = if index == 0 {
            source_signature.output()
        } else {
            source_signature.inputs()[index - 1]
        };
        let mut depth = 0;
        loop {
            if let TyKind::Ref(region, _, _) = source.kind() {
                source_regions
                    .entry(*region)
                    .or_insert_with(Vec::new)
                    .push((index, depth, None));
                let name = match region.kind() {
                    ty::RegionKind::ReStatic => Some(Symbol::intern("static")),
                    ty::RegionKind::ReEarlyParam(parameter) => Some(parameter.name),
                    ty::RegionKind::ReBound(_, bound) => match bound.kind {
                        ty::BoundRegionKind::Named(_, name) => Some(name),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(name) = name {
                    let name = name.as_str().trim_start_matches('\'').to_owned();
                    if name != "_" && !name.is_empty() {
                        fixed.insert((index, depth, None), Symbol::intern(&name));
                    }
                }
            }
            let (TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _)) = source.kind() else {
                break;
            };
            source = *inner;
            depth += 1;
        }
    }
    let mut groups = keys
        .iter()
        .map(|&key| (key, key))
        .collect::<BTreeMap<_, _>>();
    let mut flows = BTreeSet::new();
    for group in source_regions.values() {
        for &source in group {
            for &target in group {
                if source != target && keys.contains(&source) && keys.contains(&target) {
                    flows.insert((source, target));
                }
            }
        }
    }
    if let Some(summary) = analysis.origins.get(&function) {
        let key_of = |slot: &SignatureSlot| {
            let local = match slot.place.root {
                SignatureRoot::Return => 0,
                SignatureRoot::Arg(local) => local.index(),
            };
            let region = slot.place.field.map(|field| FieldRegion {
                owner: field.struct_did,
                field: field.field_index,
                depth: usize::from(slot.depth),
            });
            let key = (
                local,
                region.map_or(usize::from(slot.place.deref_depth + slot.depth), |region| {
                    region.depth
                }),
                region,
            );
            if keys.contains(&key) {
                Some(key)
            } else if region.is_some_and(|region| {
                decisions
                    .fields
                    .get(&StructFieldSlot {
                        struct_did: region.owner,
                        field_index: region.field,
                    })
                    .and_then(|layers| layers.get(region.depth))
                    .is_some_and(|layer| {
                        matches!(
                            layer.kind,
                            PtrKind::Box
                                | PtrKind::OptBox
                                | PtrKind::BoxedSlice
                                | PtrKind::OptBoxedSlice
                        )
                    })
            }) {
                locals
                    .get(&Local::from_usize(local))
                    .and_then(|layers| {
                        layers
                            .iter()
                            .enumerate()
                            .rev()
                            .find(|(_, layer)| carries_lifetime(layer.kind))
                    })
                    .map(|(depth, _)| (local, depth, None))
            } else {
                None
            }
        };
        for (source, source_slot) in summary.slots.iter_enumerated() {
            let Some(source_key) = key_of(source_slot) else { continue };
            for (target, target_slot) in summary.slots.iter_enumerated() {
                let Some(target_key) = key_of(target_slot) else { continue };
                if source_key != target_key && summary.subset.contains(source, target) {
                    flows.insert((source_key, target_key));
                }
            }
        }
    }
    flows.extend(lifetime_flow.flows(function, &keys));
    flows = flows
        .into_iter()
        .map(|(source, target)| {
            if target.0 == 0
                && target.1 == 0
                && target.2.is_none()
                && let Some(region) = source.2
                && decisions
                    .fields
                    .get(&StructFieldSlot {
                        struct_did: region.owner,
                        field_index: region.field,
                    })
                    .and_then(|layers| layers.get(region.depth))
                    .is_some_and(|layer| {
                        matches!(
                            layer.kind,
                            PtrKind::Ref(true)
                                | PtrKind::OptRef(true)
                                | PtrKind::Slice(true)
                                | PtrKind::OptSlice(true)
                                | PtrKind::Box
                                | PtrKind::OptBox
                                | PtrKind::BoxedSlice
                                | PtrKind::OptBoxedSlice
                        )
                    })
                && let Some((depth, _)) =
                    locals.get(&Local::from_usize(source.0)).and_then(|layers| {
                        layers
                            .iter()
                            .enumerate()
                            .rev()
                            .find(|(_, layer)| carries_lifetime(layer.kind))
                    })
            {
                ((source.0, depth, None), target)
            } else {
                (source, target)
            }
        })
        .collect();
    let ties = flows
        .iter()
        .filter_map(|&(source, target)| {
            (flows.contains(&(target, source)) || (source.0 > 0 && target.0 == 0))
                .then_some((source, target))
        })
        .collect::<Vec<_>>();
    // Match BO's lifetime convention: equivalent origins and returned input borrows share a name.
    for &(source, target) in &ties {
        let from = groups[&source];
        let into = groups[&target];
        let representative = from.min(into);
        for group in groups.values_mut() {
            if *group == from || *group == into {
                *group = representative;
            }
        }
    }
    let no_borrowed_return =
        keys.iter().any(|key| key.0 == 0) && return_has_no_borrowed_value(function, tcx);
    for &key in &keys {
        if key.0 == 0
            && key.2.is_none()
            && !fixed.contains_key(&key)
            && !no_borrowed_return
            && !flows
                .iter()
                .any(|&(source, target)| source.0 > 0 && target == key)
        {
            return Err(format!(
                "cannot determine the lifetime of {} return pointer at depth {} from BO origins",
                tcx.def_path_str(function),
                key.1
            ));
        }
    }
    let mut names = BTreeMap::new();
    for (key, name) in fixed.iter().filter(|(key, _)| key.0 == 0) {
        if let Some(group) = groups.get(key) {
            names.insert(*group, *name);
        }
    }
    for group in groups.values() {
        let input_names = fixed
            .iter()
            .filter_map(|(key, name)| {
                (key.0 > 0 && groups.get(key) == Some(group)).then_some(*name)
            })
            .collect::<BTreeSet<_>>();
        if input_names.len() == 1 {
            names.entry(*group).or_insert(*input_names.first().unwrap());
        }
    }
    let mut used = tcx
        .generics_of(function)
        .own_params
        .iter()
        .map(|parameter| parameter.name.as_str().trim_start_matches('\'').to_owned())
        .chain(fixed.values().map(|name| name.as_str().to_owned()))
        .collect::<BTreeSet<_>>();
    if let hir::Node::Item(item) = tcx.hir_node_by_def_id(function)
        && let Some(generics) = item.kind.generics()
    {
        used.extend(generics.params.iter().map(|parameter| {
            parameter
                .name
                .ident()
                .name
                .as_str()
                .trim_start_matches('\'')
                .to_owned()
        }));
    }
    let mut next = 0;
    for group in groups.values() {
        names.entry(*group).or_insert_with(|| {
            loop {
                let name = if next < 26 {
                    ((b'a' + next as u8) as char).to_string()
                } else {
                    format!("lt{next}")
                };
                next += 1;
                if used.insert(name.clone()) {
                    break Symbol::intern(&name);
                }
            }
        });
    }
    let needed = flows
        .iter()
        .filter(|(source, target)| source.0 != target.0)
        .flat_map(|(source, target)| [source.0, target.0])
        .chain(
            keys.iter()
                .filter_map(|key| key.2.is_some().then_some(key.0)),
        )
        .chain([0])
        .collect::<BTreeSet<_>>();
    for (&(local, depth, region), group) in &groups {
        if let Some(region) = region {
            decisions
                .type_arguments
                .entry((function, local))
                .or_default()
                .insert(region, names[group]);
        } else if needed.contains(&local) {
            locals.get_mut(&Local::from_usize(local)).unwrap()[depth].lifetime = Some(names[group]);
        }
    }
    let mut bounds = BTreeSet::new();
    for (&key, &source_name) in &fixed {
        if source_name.as_str() != "static"
            && let Some(selected) = locals[&Local::from_usize(key.0)][key.1].lifetime
            && source_name != selected
        {
            bounds.insert((
                source_name.as_str().to_owned(),
                selected.as_str().to_owned(),
            ));
        }
    }
    for (source, target) in flows {
        if !needed.contains(&source.0) || !needed.contains(&target.0) {
            continue;
        }
        let (source, target) = (names[&groups[&source]], names[&groups[&target]]);
        if source != target {
            bounds.insert((source.as_str().to_owned(), target.as_str().to_owned()));
        }
    }
    for (local, layers) in locals
        .iter()
        .filter(|(local, _)| local.index() <= arguments)
    {
        for (depth, outer) in layers.iter().enumerate() {
            if let Some(outer) = fixed
                .get(&(local.index(), depth, None))
                .copied()
                .or(outer.lifetime)
            {
                for (index, layer) in layers.iter().enumerate().skip(depth + 1) {
                    let Some(inner) = fixed
                        .get(&(local.index(), index, None))
                        .copied()
                        .or(layer.lifetime)
                    else {
                        continue;
                    };
                    if inner != outer {
                        bounds.insert((inner.as_str().to_owned(), outer.as_str().to_owned()));
                    }
                }
            }
        }
    }
    for (&(local, depth, _), &name) in &fixed {
        if let Some(layer) = locals
            .get_mut(&Local::from_usize(local))
            .and_then(|layers| layers.get_mut(depth))
            && carries_lifetime(layer.kind)
        {
            layer.lifetime = Some(name);
        }
    }
    Ok(bounds
        .into_iter()
        .map(|(longer, shorter)| (Symbol::intern(&longer), Symbol::intern(&shorter)))
        .collect())
}

struct RepresentationFacts {
    nullable: FxHashSet<SlotRef>,
    allocations: FxHashMap<SlotRef, FxHashSet<Option<u64>>>,
    mutable: FxHashSet<SlotRef>,
}

fn representation_facts(
    analysis: &AcceptedPointerAnalysis,
    tcx: TyCtxt<'_>,
) -> RepresentationFacts {
    let mut nullable = analysis.nullable.clone();
    let mut mutable = FxHashSet::default();
    for &slot in analysis.kinds.keys() {
        let SlotRef::Field(id) = slot else { continue };
        let field = analysis.slots.field_slots.slot(id);
        let pointer_replacer_bo::analyses::borrow_ownership::slots::SlotOwner::Field(owner) =
            field.owner
        else {
            unreachable!()
        };
        let definition = tcx.adt_def(owner.struct_did);
        let mut source = definition.non_enum_variant().fields
            [rustc_abi::FieldIdx::from_usize(owner.field_index)]
        .ty(
            tcx,
            ty::GenericArgs::identity_for_item(tcx, owner.struct_did),
        );
        for _ in 0..field.depth {
            let TyKind::RawPtr(inner, _) = source.kind() else { break };
            source = *inner;
        }
        if matches!(source.kind(), TyKind::RawPtr(_, mutability) if mutability.is_mut())
            && analysis
                .mutability
                .struct_field_fact(owner.struct_did, owner.field_index, field.depth.into())
                .is_none_or(|fact| fact.is_mutable())
        {
            mutable.insert(slot);
        }
    }
    let mut null_tests = FxHashSet::default();
    let mut allocations = FxHashMap::<SlotRef, FxHashSet<Option<u64>>>::default();
    let mut edges = Vec::new();
    let mut copies = Vec::new();
    for &function in analysis.slots.fn_local_slots.keys() {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let mapping = utils::ir::map_thir_to_mir(function, false, tcx);
        let source_allocations = {
            let mut source = SourceFacts {
                function,
                analysis,
                bindings: &mapping.binding_to_local,
                tcx,
                nullable: &mut null_tests,
                allocations: FxHashMap::default(),
            };
            source.visit_body(tcx.hir_body_owned_by(function));
            source.allocations
        };
        let resolve = |place, depth| {
            resolve_place(&analysis.slots, function, &body, place, depth, None).map(|slot| {
                match slot {
                    ResolvedSlot::Local(slot) => SlotRef::Local(function, slot),
                    ResolvedSlot::Field(slot) => SlotRef::Field(slot),
                }
            })
        };
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                let StatementKind::Assign(box (target, value)) = &statement.kind else { continue };
                if let Rvalue::Aggregate(kind, operands) = value
                    && let AggregateKind::Adt(definition, ..) = **kind
                    && let Some(struct_did) = definition.as_local()
                {
                    for (index, operand) in operands.iter_enumerated() {
                        let Some(source) = operand.place() else { continue };
                        let field = StructFieldSlot {
                            struct_did,
                            field_index: index.as_usize(),
                        };
                        for depth in 0..MAX_SLOT_DEPTH {
                            if let (Some(source), Some(target)) = (
                                resolve(source, depth),
                                analysis
                                    .slots
                                    .field_slots
                                    .slot_for_field_depth(field, depth),
                            ) {
                                edges.push((source, SlotRef::Field(target)));
                                copies.push((source, SlotRef::Field(target)));
                            }
                        }
                    }
                    continue;
                }
                let (source, shift) = match value {
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                    | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                    | Rvalue::CopyForDeref(place) => (*place, 0),
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => (*place, 1),
                    _ => continue,
                };
                for depth in 0..MAX_SLOT_DEPTH {
                    if let (Some(source), Some(target)) =
                        (resolve(source, depth), resolve(*target, depth + shift))
                    {
                        edges.push((source, target));
                        copies.push((source, target));
                    }
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
            let TyKind::FnDef(callee, _) = *func.ty(&*body, tcx).kind() else { continue };
            let span = block.terminator().source_info.span;
            if let Some(size) = source_allocations.get(&(span.lo().0, span.hi().0))
                && let Some(target) = resolve(*destination, 0)
            {
                allocations.entry(target).or_default().insert(*size);
            }
            let Some(callee) = callee.as_local() else { continue };
            let Some(callee_slots) = analysis.slots.fn_local_slots.get(&callee) else { continue };
            for depth in 0..MAX_SLOT_DEPTH {
                for (index, argument) in args.iter().enumerate() {
                    let Some(target) =
                        callee_slots.slot_for_local_depth(Local::from_usize(index + 1), depth)
                    else {
                        continue;
                    };
                    let target = SlotRef::Local(callee, target);
                    if let Some(source) = argument
                        .node
                        .place()
                        .and_then(|place| resolve(place, depth))
                    {
                        edges.push((source, target));
                    } else if depth == 0
                        && matches!(&argument.node, Operand::Constant(constant) if constant.const_.try_to_scalar().and_then(|scalar| scalar.try_to_scalar_int().ok()).is_some_and(|value| value.to_bits(value.size()) == 0))
                    {
                        nullable.insert(target);
                    }
                }
                if let (Some(source), Some(target)) = (
                    callee_slots.slot_for_local_depth(RETURN_PLACE, depth),
                    resolve(*destination, depth),
                ) {
                    edges.push((SlotRef::Local(callee, source), target));
                }
            }
        }
    }
    loop {
        let mut changed = false;
        // A null test constrains copies of the same value in both directions. Null
        // assignments flow forward only, preserving known nonnull construction sites.
        for &(source, target) in &copies {
            if null_tests.contains(&source) {
                changed |= null_tests.insert(target);
            }
            if null_tests.contains(&target) {
                changed |= null_tests.insert(source);
            }
        }
        for &slot in &null_tests {
            changed |= nullable.insert(slot);
        }
        for &(source, target) in &edges {
            if mutable.contains(&target) {
                changed |= mutable.insert(source);
            }
            if nullable.contains(&source) {
                changed |= nullable.insert(target);
            }
            if let Some(sizes) = allocations.get(&source).cloned() {
                let target = allocations.entry(target).or_default();
                for size in sizes {
                    changed |= target.insert(size);
                }
            }
        }
        if !changed {
            break;
        }
    }
    RepresentationFacts {
        nullable,
        allocations,
        mutable,
    }
}

fn expression_slot(
    expression: &hir::Expr<'_>,
    depth: u8,
    function: LocalDefId,
    analysis: &AcceptedPointerAnalysis,
    bindings: &FxHashMap<HirId, Local>,
    tcx: TyCtxt<'_>,
) -> Option<SlotRef> {
    match expression.kind {
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => {
            let hir::def::Res::Local(binding) = path.res else { return None };
            let slot = analysis.slots.fn_local_slots[&function]
                .slot_for_local_depth(*bindings.get(&binding)?, depth)?;
            Some(SlotRef::Local(function, slot))
        }
        hir::ExprKind::Unary(hir::UnOp::Deref, base) => {
            expression_slot(base, depth + 1, function, analysis, bindings, tcx)
        }
        hir::ExprKind::Cast(base, _) => {
            expression_slot(base, depth, function, analysis, bindings, tcx)
        }
        hir::ExprKind::Field(base, _) => {
            let typeck = tcx.typeck(function);
            let base = typeck.expr_ty(base).peel_refs();
            let TyKind::Adt(definition, _) = base.kind() else { return None };
            let field = StructFieldSlot {
                struct_did: definition.did().as_local()?,
                field_index: typeck.field_index(expression.hir_id).as_usize(),
            };
            analysis
                .slots
                .field_slots
                .slot_for_field_depth(field, depth)
                .map(SlotRef::Field)
        }
        _ => None,
    }
}

struct SourceFacts<'a, 'tcx> {
    function: LocalDefId,
    analysis: &'a AcceptedPointerAnalysis,
    bindings: &'a FxHashMap<HirId, Local>,
    tcx: TyCtxt<'tcx>,
    nullable: &'a mut FxHashSet<SlotRef>,
    allocations: FxHashMap<(u32, u32), Option<u64>>,
}

impl<'tcx> Visitor<'tcx> for SourceFacts<'_, 'tcx> {
    fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
        let typeck = self.tcx.typeck(self.function);
        if let hir::ExprKind::MethodCall(method, receiver, [], _) = expression.kind
            && method.ident.name.as_str() == "is_null"
            && typeck.expr_ty(receiver).is_raw_ptr()
            && let Some(slot) = expression_slot(
                receiver,
                0,
                self.function,
                self.analysis,
                self.bindings,
                self.tcx,
            )
        {
            self.nullable.insert(slot);
        }
        if let hir::ExprKind::Binary(operator, left, right) = expression.kind
            && matches!(operator.node, hir::BinOpKind::Eq | hir::BinOpKind::Ne)
        {
            for (pointer, other) in [(left, right), (right, left)] {
                if typeck.expr_ty(pointer).is_raw_ptr()
                    && null_expression(other, self.function, self.tcx)
                    && let Some(slot) = expression_slot(
                        pointer,
                        0,
                        self.function,
                        self.analysis,
                        self.bindings,
                        self.tcx,
                    )
                {
                    self.nullable.insert(slot);
                }
            }
        }
        if let hir::ExprKind::Call(callee, arguments) = expression.kind
            && let TyKind::FnDef(definition, _) = *typeck.expr_ty(callee).kind()
            && let Some(symbol) =
                crate::observation::local_c_foreign_function_symbol(definition, self.tcx)
        {
            let size = match (symbol.as_str(), arguments) {
                ("malloc" | "xmalloc", [size]) | ("realloc", [_, size]) => {
                    Some(allocation_bytes(size, self.function, self.tcx))
                }
                ("calloc" | "xcalloc", [count, size]) => Some(
                    allocation_bytes(count, self.function, self.tcx)
                        .zip(allocation_bytes(size, self.function, self.tcx))
                        .and_then(|(count, size)| count.checked_mul(size)),
                ),
                _ => None,
            };
            if let Some(size) = size {
                self.allocations
                    .insert((expression.span.lo().0, expression.span.hi().0), size);
            }
        }
        intravisit::walk_expr(self, expression);
    }
}

fn allocation_bytes(
    expression: &hir::Expr<'_>,
    function: LocalDefId,
    tcx: TyCtxt<'_>,
) -> Option<u64> {
    match expression.kind {
        hir::ExprKind::Lit(literal) => match literal.node {
            rustc_ast::LitKind::Int(value, _) => value.get().try_into().ok(),
            _ => None,
        },
        hir::ExprKind::Cast(value, _) => allocation_bytes(value, function, tcx),
        hir::ExprKind::Binary(operator, left, right) if operator.node == hir::BinOpKind::Mul => {
            allocation_bytes(left, function, tcx)?
                .checked_mul(allocation_bytes(right, function, tcx)?)
        }
        hir::ExprKind::Call(callee, []) => {
            let typeck = tcx.typeck(function);
            let TyKind::FnDef(definition, arguments) = *typeck.expr_ty(callee).kind() else {
                return None;
            };
            if !tcx.is_diagnostic_item(Symbol::intern("mem_size_of"), definition) {
                return None;
            }
            let element = arguments.types().next()?;
            tcx.layout_of(ty::TypingEnv::post_analysis(tcx, function).as_query_input(element))
                .ok()
                .map(|layout| layout.size.bytes())
        }
        _ => None,
    }
}

fn null_expression(expression: &hir::Expr<'_>, function: LocalDefId, tcx: TyCtxt<'_>) -> bool {
    match expression.kind {
        hir::ExprKind::Cast(value, _) => null_expression(value, function, tcx),
        hir::ExprKind::Lit(literal) => {
            matches!(literal.node, rustc_ast::LitKind::Int(value, _) if value.get() == 0)
        }
        hir::ExprKind::Call(callee, []) => {
            let TyKind::FnDef(definition, _) = *tcx.typeck(function).expr_ty(callee).kind() else {
                return false;
            };
            tcx.is_diagnostic_item(Symbol::intern("ptr_null"), definition)
                || tcx.is_diagnostic_item(Symbol::intern("ptr_null_mut"), definition)
        }
        _ => false,
    }
}

fn return_has_no_borrowed_value(function: LocalDefId, tcx: TyCtxt<'_>) -> bool {
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let mut blocks = vec![rustc_middle::mir::START_BLOCK];
    let mut reachable = FxHashSet::default();
    while let Some(block) = blocks.pop() {
        if reachable.insert(block) {
            blocks.extend(body.basic_blocks[block].terminator().successors());
        }
    }
    if !reachable.iter().any(|&block| {
        matches!(
            body.basic_blocks[block].terminator().kind,
            TerminatorKind::Return
        )
    }) {
        return true;
    }
    let mut pending = vec![RETURN_PLACE];
    let mut visited = FxHashSet::default();
    let mut found_null = false;
    while let Some(local) = pending.pop() {
        if !visited.insert(local) {
            continue;
        }
        let mut defined = false;
        for &block in &reachable {
            let block = &body.basic_blocks[block];
            for statement in &block.statements {
                let StatementKind::Assign(box (target, value)) = &statement.kind else { continue };
                if target.as_local() != Some(local) {
                    continue;
                }
                defined = true;
                let operand = match value {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand,
                    _ => return false,
                };
                if let Some(source) = operand.place().and_then(|place| place.as_local()) {
                    pending.push(source);
                } else if matches!(operand, Operand::Constant(constant) if constant.const_.try_to_scalar().and_then(|scalar| scalar.try_to_scalar_int().ok()).is_some_and(|value| value.to_bits(value.size()) == 0))
                {
                    found_null = true;
                } else {
                    return false;
                }
            }
            if let TerminatorKind::Call {
                func, destination, ..
            } = &block.terminator().kind
                && destination.as_local() == Some(local)
            {
                defined = true;
                let TyKind::FnDef(definition, _) = *func.ty(&*body, tcx).kind() else {
                    return false;
                };
                if tcx.is_diagnostic_item(Symbol::intern("ptr_null"), definition)
                    || tcx.is_diagnostic_item(Symbol::intern("ptr_null_mut"), definition)
                {
                    found_null = true;
                } else {
                    return false;
                }
            }
        }
        if !defined {
            return false;
        }
    }
    found_null
}
