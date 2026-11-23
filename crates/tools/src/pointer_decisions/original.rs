use pointer_replacer::analyses::borrow::lifetime_flow::{
    LifetimeFlowSummary, SignatureRoot as OriginalRoot, SignatureSlot as OriginalSlot,
};

use super::*;

pub(super) fn initial_pointer_decisions(
    tcx: TyCtxt<'_>,
    api: &FxHashSet<String>,
) -> InitialPointerDecisions {
    let original = pointer_replacer::initial_pointer_decisions(
        &pointer_replacer::Config::default(),
        pointer_replacer::PointerDecisionOptions {
            assume_nonnegative_offsets: true,
        },
        tcx,
    );
    let file_types = struct_types::file_types(tcx);
    let mut result = InitialPointerDecisions {
        signatures: SigDecisions {
            data: FxHashMap::default(),
        },
        preserve_safety: FxHashSet::default(),
        bindings: FxHashMap::default(),
        nested: FxHashMap::default(),
        bounds: FxHashMap::default(),
        fields: FxHashMap::default(),
        foreign_types: struct_types::foreign_types(tcx, &file_types),
        file_types,
        types: TypeLifetimes::default(),
        type_arguments: FxHashMap::default(),
    };
    let (exposed, _) = struct_types::api_structs(tcx, api);
    for (&field, &kind) in &original.fields {
        if result.foreign_types.contains(&field.struct_did) {
            continue;
        }
        let source = tcx.adt_def(field.struct_did).non_enum_variant().fields
            [rustc_abi::FieldIdx::from_usize(field.field_index)]
        .ty(
            tcx,
            ty::GenericArgs::identity_for_item(tcx, field.struct_did),
        );
        let TyKind::RawPtr(inner, mutable) = *source.kind() else { continue };
        let mut kind = convert_kind(kind, false);
        if inner.is_c_void(tcx)
            || result.preserves_file_type(inner, tcx)
            || (exposed.contains(&field.struct_did)
                && matches!(
                    kind,
                    PtrKind::Slice(_)
                        | PtrKind::OptSlice(_)
                        | PtrKind::BoxedSlice
                        | PtrKind::OptBoxedSlice
                ))
        {
            kind = PtrKind::Raw(mutable.is_mut());
        }
        result.fields.insert(
            StructFieldSlot {
                struct_did: field.struct_did,
                field_index: field.field_index,
            },
            vec![PointerLayer {
                kind,
                lifetime: None,
            }],
        );
    }
    struct_types::retain_union_compatible_fields(&mut result.fields, tcx);
    result.types = TypeLifetimes::new(&mut result.fields, tcx);
    let lifetime_flow = lifetime_flow::LifetimeFlow::new(
        original.signatures.data.keys().copied().collect(),
        |field| {
            original
                .fields
                .contains_key(&pointer_replacer::analyses::borrow::StructFieldSlot {
                    struct_did: field.struct_did,
                    field_index: field.field_index,
                })
        },
        &result.types,
        tcx,
    );
    for (&function, signature) in &original.signatures.data {
        let source_signature = tcx.fn_sig(function).instantiate_identity().skip_binder();
        if signature.signature_locked && !source_signature.safety.is_unsafe() {
            result.preserve_safety.insert(function);
        }
        if requires_unstructured_body(function, tcx) {
            continue;
        }
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let arguments = source_signature.inputs().len();
        let mapping = utils::ir::map_thir_to_mir(function, false, tcx);
        let mut kinds = FxHashMap::default();
        for (&binding, &local) in &mapping.binding_to_local {
            if let Some(&kind) = original.bindings.get(&binding) {
                kinds.insert(local, kind);
            }
        }
        for (index, &kind) in signature.input_decs.iter().take(arguments).enumerate() {
            if let Some(kind) = kind {
                kinds.insert(Local::from_usize(index + 1), kind);
            }
        }
        if let Some(kind) = signature.output_dec {
            kinds.insert(RETURN_PLACE, kind);
        }
        let mut locals = FxHashMap::default();
        for (local, declaration) in body.local_decls.iter_enumerated() {
            if signature.signature_locked && local.index() <= arguments {
                continue;
            }
            let non_null = original
                .non_null_locals
                .get(&function)
                .is_some_and(|locals| locals.contains(local));
            let mut source = declaration.ty;
            let mut layers = Vec::new();
            while let TyKind::RawPtr(inner, mutable) | TyKind::Ref(_, inner, mutable) =
                *source.kind()
            {
                let kind = if source.is_ref() {
                    PtrKind::Ref(mutable.is_mut())
                } else if layers.is_empty() {
                    kinds
                        .get(&local)
                        .map_or(PtrKind::Raw(mutable.is_mut()), |&kind| {
                            convert_kind(kind, non_null)
                        })
                } else {
                    PtrKind::Raw(mutable.is_mut())
                };
                layers.push(PointerLayer {
                    kind,
                    lifetime: None,
                });
                source = inner;
            }
            if !layers.is_empty() {
                locals.insert(local, layers);
            }
        }
        if !signature.signature_locked {
            let origins = original
                .lifetime_flows
                .get(&function)
                .map(signature_origins);
            let bounds = signature_lifetimes(
                function,
                arguments,
                origins.as_ref(),
                &lifetime_flow,
                &mut locals,
                &mut result,
                tcx,
            );
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
        }
        for (binding, local) in mapping.binding_to_local {
            if let Some(layers) = locals.get(&local) {
                result.bindings.insert(binding, layers[0].kind);
                let mut inner = layers[1..].to_vec();
                for layer in &mut inner {
                    layer.lifetime = None;
                }
                result.nested.insert(PointerTarget::Binding(binding), inner);
            }
        }
    }
    result
}

fn convert_kind(kind: pointer_replacer::PtrKind, non_null: bool) -> PtrKind {
    use pointer_replacer::PtrKind as Original;
    match kind {
        Original::Raw(mutable) => PtrKind::Raw(mutable),
        Original::Ref(mutable) => PtrKind::Ref(mutable),
        Original::OptRef(mutable) => PtrKind::OptRef(mutable),
        Original::Slice(mutable) if non_null => PtrKind::Slice(mutable),
        Original::Slice(mutable) => PtrKind::OptSlice(mutable),
        Original::Box => PtrKind::Box,
        Original::OptBox => PtrKind::OptBox,
        Original::BoxedSlice => PtrKind::BoxedSlice,
        Original::OptBoxedSlice => PtrKind::OptBoxedSlice,
        Original::SliceCursor(_) => unreachable!("tools assume nonnegative offsets"),
    }
}

fn signature_origins(summary: &LifetimeFlowSummary) -> SignatureOrigins {
    let slot = |slot: OriginalSlot| SignatureSlot {
        place: SignaturePlace {
            root: match slot.place.root {
                OriginalRoot::Return => SignatureRoot::Return,
                OriginalRoot::Arg(local) => SignatureRoot::Arg(local),
            },
            parents: Default::default(),
            deref_depth: slot.place.deref_depth,
            field: slot.place.field.map(|field| StructFieldSlot {
                struct_did: field.struct_did,
                field_index: field.field_index,
            }),
        },
        depth: slot.depth,
    };
    let mut flows = Vec::new();
    for (source, source_slot) in summary.slots.iter_enumerated() {
        let mut pending = vec![source];
        let mut visited = FxHashSet::default();
        while let Some(target) = pending.pop() {
            if !visited.insert(target) {
                continue;
            }
            flows.push((slot(*source_slot), slot(summary.slots[target])));
            for next in summary.slots.indices() {
                if summary.value_flows.contains(target, next)
                    || summary.storage_aliases.contains(target, next)
                {
                    pending.push(next);
                }
            }
        }
    }
    SignatureOrigins {
        flows,
        unknown: summary
            .unknown_targets
            .iter()
            .map(|index| slot(summary.slots[index]))
            .collect(),
    }
}
