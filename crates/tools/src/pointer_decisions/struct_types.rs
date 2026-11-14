use std::collections::{BTreeMap, BTreeSet};

use pointer_replacer_bo::analyses::borrow_ownership::slots::StructFieldSlot;
use rustc_ast::{
    AngleBracketedArg, AngleBracketedArgs, GenericArg, GenericArgs, Ty, TyKind as AstTyKind, ptr::P,
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::{self, TyCtxt, TyKind};
use rustc_span::{
    DUMMY_SP, Symbol,
    def_id::{DefId, LocalDefId},
    sym,
};
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt;

use super::{PointerLayer, PtrKind, carries_lifetime};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct FieldRegion {
    pub owner: LocalDefId,
    pub field: usize,
    pub depth: usize,
}

impl Ord for FieldRegion {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.owner.local_def_index.as_u32(), self.field, self.depth).cmp(&(
            other.owner.local_def_index.as_u32(),
            other.field,
            other.depth,
        ))
    }
}

impl PartialOrd for FieldRegion {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct TypeLifetimes {
    pub plans: FxHashMap<LocalDefId, BTreeMap<FieldRegion, Symbol>>,
    pub invalid_derives: FxHashMap<LocalDefId, FxHashSet<Symbol>>,
}

const FILE_TYPE_NAMES: &[&str] = &["FILE", "_IO_FILE", "__sFILE", "_IO_FILE_plus"];

fn file_type_definition(mut source: ty::Ty<'_>) -> Option<DefId> {
    loop {
        match source.kind() {
            TyKind::RawPtr(inner, _)
            | TyKind::Ref(_, inner, _)
            | TyKind::Array(inner, _)
            | TyKind::Slice(inner) => source = *inner,
            TyKind::Adt(definition, _) => return Some(definition.did()),
            TyKind::Foreign(definition) => return Some(*definition),
            _ => return None,
        }
    }
}

pub(super) fn file_types(tcx: TyCtxt<'_>) -> FxHashSet<DefId> {
    tcx.hir_crate_items(())
        .free_items()
        .filter_map(|id| {
            let item = tcx.hir_item(id);
            if !matches!(
                item.kind,
                hir::ItemKind::Struct(..)
                    | hir::ItemKind::Enum(..)
                    | hir::ItemKind::Union(..)
                    | hir::ItemKind::TyAlias(..)
            ) || !FILE_TYPE_NAMES.contains(&tcx.item_name(item.owner_id.to_def_id()).as_str())
            {
                return None;
            }
            file_type_definition(tcx.type_of(item.owner_id.def_id).instantiate_identity())
        })
        .collect()
}

pub(super) fn contains_file_type(
    source: ty::Ty<'_>,
    definitions: &FxHashSet<DefId>,
    tcx: TyCtxt<'_>,
) -> bool {
    file_type_definition(source).is_some_and(|definition| {
        definitions.contains(&definition)
            || FILE_TYPE_NAMES.contains(&tcx.item_name(definition).as_str())
    })
}

pub(super) fn foreign_types(
    tcx: TyCtxt<'_>,
    file_types: &FxHashSet<DefId>,
) -> FxHashSet<LocalDefId> {
    struct TypeVisitor<'tcx> {
        tcx: TyCtxt<'tcx>,
        roots: FxHashSet<LocalDefId>,
        dependencies: FxHashMap<LocalDefId, FxHashSet<LocalDefId>>,
        fixed_header: bool,
    }

    impl<'tcx> Visitor<'tcx> for TypeVisitor<'tcx> {
        type NestedFilter = rustc_middle::hir::nested_filter::All;

        fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
            self.tcx
        }

        fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
            if let hir::ItemKind::Fn { sig, generics, .. } = item.kind
                && self
                    .tcx
                    .generics_of(item.owner_id)
                    .own_params
                    .iter()
                    .any(|parameter| matches!(parameter.kind, ty::GenericParamDefKind::Type { .. }))
            {
                self.fixed_header = true;
                intravisit::walk_fn_decl(self, sig.decl);
                intravisit::walk_generics(self, generics);
                self.fixed_header = false;
            }
            intravisit::walk_item(self, item);
        }

        fn visit_ty(&mut self, ty: &'tcx hir::Ty<'tcx, hir::AmbigArg>) {
            if let hir::TyKind::Path(hir::QPath::Resolved(_, path)) = ty.kind
                && let Res::Def(_, did) = path.res
                && let Some(did) = did.as_local()
            {
                if self.fixed_header {
                    self.roots.insert(did);
                }
                for parent in self.tcx.hir_parent_id_iter(ty.hir_id) {
                    match self.tcx.hir_node(parent) {
                        hir::Node::ForeignItem(_) => {
                            self.roots.insert(did);
                            break;
                        }
                        hir::Node::Item(item) => {
                            if matches!(
                                item.kind,
                                hir::ItemKind::Struct(..)
                                    | hir::ItemKind::Enum(..)
                                    | hir::ItemKind::Union(..)
                                    | hir::ItemKind::TyAlias(..)
                            ) {
                                self.dependencies
                                    .entry(item.owner_id.def_id)
                                    .or_default()
                                    .insert(did);
                            }
                            break;
                        }
                        _ => {}
                    }
                }
            }
            intravisit::walk_ty(self, ty);
        }
    }

    let mut visitor = TypeVisitor {
        tcx,
        roots: file_types
            .iter()
            .filter_map(|definition| definition.as_local())
            .collect(),
        dependencies: FxHashMap::default(),
        fixed_header: false,
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);
    let mut pending = visitor.roots.into_iter().collect::<Vec<_>>();
    let mut protected = FxHashSet::default();
    while let Some(did) = pending.pop() {
        if protected.insert(did)
            && let Some(dependencies) = visitor.dependencies.get(&did)
        {
            pending.extend(dependencies);
        }
    }
    protected
}

fn children<'tcx>(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>, values: &mut Vec<ty::Ty<'tcx>>) {
    match ty.kind() {
        TyKind::RawPtr(inner, _)
        | TyKind::Ref(_, inner, _)
        | TyKind::Array(inner, _)
        | TyKind::Slice(inner) => values.push(*inner),
        TyKind::Tuple(elements) => values.extend(elements.iter()),
        TyKind::Adt(definition, arguments) => {
            values.extend(arguments.types());
            if definition.did().is_local() {
                values.extend(
                    definition
                        .all_fields()
                        .map(|field| field.ty(tcx, arguments)),
                );
            }
        }
        _ => {}
    }
}

fn reachable_structs<'tcx>(
    roots: impl IntoIterator<Item = ty::Ty<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> FxHashSet<LocalDefId> {
    let mut pending = roots.into_iter().collect::<Vec<_>>();
    let mut visited = FxHashSet::default();
    let mut structs = FxHashSet::default();
    while let Some(ty) = pending.pop() {
        if !visited.insert(ty) {
            continue;
        }
        if let TyKind::Adt(definition, _) = ty.kind()
            && definition.is_struct()
            && let Some(local) = definition.did().as_local()
        {
            structs.insert(local);
        }
        children(ty, tcx, &mut pending);
    }
    structs
}

pub(super) fn api_structs(
    tcx: TyCtxt<'_>,
    api: &FxHashSet<String>,
) -> (FxHashSet<LocalDefId>, FxHashSet<LocalDefId>) {
    let mut roots = Vec::new();
    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        let hir::ItemKind::Fn { ident, .. } = item.kind else { continue };
        let did = item.owner_id.def_id;
        if api.contains(ident.name.as_str())
            || api.contains(&tcx.def_path_str(did))
            || tcx.get_attrs(did, sym::export_name).any(|attr| {
                attr.value_str()
                    .is_some_and(|name| api.contains(name.as_str()))
            })
        {
            roots.extend(
                tcx.fn_sig(did)
                    .instantiate_identity()
                    .skip_binder()
                    .inputs_and_output
                    .iter(),
            );
        }
    }
    let mut pending = roots.clone();
    let mut visited = FxHashSet::default();
    let mut layout_roots = Vec::new();
    while let Some(ty) = pending.pop() {
        if !visited.insert(ty) {
            continue;
        }
        if let TyKind::Adt(definition, _) = ty.kind()
            && (definition.is_enum()
                || (!definition.repr().c() && !definition.repr().transparent()))
        {
            layout_roots.push(ty);
        }
        children(ty, tcx, &mut pending);
    }
    (
        reachable_structs(roots, tcx),
        reachable_structs(layout_roots, tcx),
    )
}

pub(super) fn retain_union_compatible_fields(
    fields: &mut FxHashMap<StructFieldSlot, Vec<PointerLayer>>,
    tcx: TyCtxt<'_>,
) {
    let mut roots = Vec::new();
    let mut value_structs = FxHashSet::default();
    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        if !matches!(item.kind, hir::ItemKind::Union(..)) {
            continue;
        }
        let ty = tcx.type_of(item.owner_id.def_id).instantiate_identity();
        let preserve_copy = tcx.type_is_copy_modulo_regions(
            ty::TypingEnv::post_analysis(tcx, item.owner_id.def_id),
            ty,
        );
        let TyKind::Adt(definition, arguments) = ty.kind() else { continue };
        for field in definition.all_fields() {
            let field_ty = field.ty(tcx, arguments);
            roots.push(field_ty);
            let mut pending = vec![field_ty];
            let mut visited = FxHashSet::default();
            while let Some(ty) = pending.pop() {
                if !visited.insert(ty) {
                    continue;
                }
                match ty.kind() {
                    TyKind::Array(inner, _) => pending.push(*inner),
                    TyKind::Tuple(elements) => pending.extend(elements.iter()),
                    TyKind::Adt(definition, arguments) if definition.did().is_local() => {
                        if definition.is_struct() {
                            value_structs.insert(definition.did().expect_local());
                        }
                        pending.extend(
                            definition
                                .all_fields()
                                .map(|field| field.ty(tcx, arguments)),
                        );
                    }
                    TyKind::Adt(definition, arguments)
                        if preserve_copy
                            || !tcx.is_lang_item(definition.did(), hir::LangItem::ManuallyDrop) =>
                    {
                        pending.extend(arguments.types())
                    }
                    _ => {}
                }
            }
        }
    }
    let mentioned = reachable_structs(roots, tcx);
    for (field, layers) in fields {
        if (mentioned.contains(&field.struct_did)
            && layers.iter().any(|layer| carries_lifetime(layer.kind)))
            || (value_structs.contains(&field.struct_did)
                && layers.first().is_some_and(|layer| !copy_kind(layer.kind)))
        {
            let definition = tcx.adt_def(field.struct_did);
            let mut original = definition.non_enum_variant().fields
                [rustc_abi::FieldIdx::from_usize(field.field_index)]
            .ty(
                tcx,
                ty::GenericArgs::identity_for_item(tcx, field.struct_did),
            );
            for layer in layers {
                let TyKind::RawPtr(inner, mutable) = original.kind() else { break };
                layer.kind = PtrKind::Raw(mutable.is_mut());
                original = *inner;
            }
        }
    }
}

fn copy_kind(kind: PtrKind) -> bool {
    matches!(
        kind,
        PtrKind::Raw(_)
            | PtrKind::Ref(false)
            | PtrKind::OptRef(false)
            | PtrKind::Slice(false)
            | PtrKind::OptSlice(false)
    )
}

pub(super) fn mutable_ancestors(source: ty::Ty<'_>, layers: &mut [PointerLayer]) {
    let mut ty = source;
    let mut mutable = Vec::new();
    for _ in layers.iter() {
        let (TyKind::RawPtr(inner, mutability) | TyKind::Ref(_, inner, mutability)) = ty.kind()
        else {
            break;
        };
        mutable.push(mutability.is_mut());
        ty = *inner;
    }
    let mut child_mutable = false;
    for (index, layer) in layers.iter_mut().enumerate().rev() {
        layer.kind = match layer.kind {
            PtrKind::Ref(value) => PtrKind::Ref(value || (child_mutable && mutable[index])),
            PtrKind::OptRef(value) => PtrKind::OptRef(value || (child_mutable && mutable[index])),
            PtrKind::Slice(value) => PtrKind::Slice(value || (child_mutable && mutable[index])),
            PtrKind::OptSlice(value) => {
                PtrKind::OptSlice(value || (child_mutable && mutable[index]))
            }
            kind => kind,
        };
        child_mutable = !copy_kind(layer.kind);
    }
}

impl TypeLifetimes {
    pub(super) fn new(
        fields: &mut FxHashMap<StructFieldSlot, Vec<PointerLayer>>,
        tcx: TyCtxt<'_>,
    ) -> Self {
        let mut result = Self::default();
        for (field, layers) in fields.iter() {
            for (depth, layer) in layers.iter().enumerate() {
                if carries_lifetime(layer.kind) {
                    result.plans.entry(field.struct_did).or_default().insert(
                        FieldRegion {
                            owner: field.struct_did,
                            field: field.field_index,
                            depth,
                        },
                        Symbol::intern("_"),
                    );
                }
            }
        }
        let mut definitions = Vec::new();
        for item_id in tcx.hir_crate_items(()).free_items() {
            let item = tcx.hir_item(item_id);
            let did = item.owner_id.def_id;
            match item.kind {
                hir::ItemKind::TyAlias(..) => {
                    definitions.push((did, vec![tcx.type_of(did).instantiate_identity()]))
                }
                hir::ItemKind::Struct(..) | hir::ItemKind::Enum(..) => {
                    let arguments = ty::GenericArgs::identity_for_item(tcx, did);
                    definitions.push((
                        did,
                        tcx.adt_def(did)
                            .all_fields()
                            .map(|field| field.ty(tcx, arguments))
                            .collect(),
                    ));
                }
                _ => {}
            }
        }
        loop {
            let mut changed = false;
            for (did, types) in &definitions {
                for ty in types {
                    for region in result.regions_of(*ty) {
                        let plan = result.plans.entry(*did).or_default();
                        if let std::collections::btree_map::Entry::Vacant(entry) =
                            plan.entry(region)
                        {
                            entry.insert(Symbol::intern("_"));
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for (&did, plan) in &mut result.plans {
            let mut used = tcx
                .generics_of(did)
                .own_params
                .iter()
                .map(|parameter| parameter.name.as_str().trim_start_matches('\'').to_owned())
                .collect::<BTreeSet<_>>();
            let mut index: usize = 0;
            for name in plan.values_mut() {
                loop {
                    let candidate = if index < 26 {
                        ((b'a' + index as u8) as char).to_string()
                    } else {
                        format!("lt{index}")
                    };
                    index += 1;
                    if used.insert(candidate.clone()) {
                        *name = Symbol::intern(&candidate);
                        break;
                    }
                }
            }
        }
        for (field, layers) in fields.iter_mut() {
            for (depth, layer) in layers.iter_mut().enumerate() {
                layer.lifetime = result
                    .plans
                    .get(&field.struct_did)
                    .and_then(|plan| {
                        plan.get(&FieldRegion {
                            owner: field.struct_did,
                            field: field.field_index,
                            depth,
                        })
                    })
                    .copied();
            }
        }
        result.find_invalid_derives(fields, tcx);
        result
    }

    fn find_invalid_derives(
        &mut self,
        fields: &FxHashMap<StructFieldSlot, Vec<PointerLayer>>,
        tcx: TyCtxt<'_>,
    ) {
        let changed_structs = fields
            .iter()
            .filter_map(|(field, layers)| {
                layers
                    .iter()
                    .any(|layer| !matches!(layer.kind, PtrKind::Raw(_)))
                    .then_some(field.struct_did)
            })
            .collect::<FxHashSet<_>>();
        if changed_structs.is_empty() {
            return;
        }
        let mut derived = Vec::new();
        for item_id in tcx.hir_crate_items(()).free_items() {
            let item = tcx.hir_item(item_id);
            let hir::ItemKind::Impl(implementation) = item.kind else { continue };
            if !tcx.is_automatically_derived(item.owner_id.def_id.to_def_id())
                && !item.span.in_derive_expansion()
            {
                continue;
            }
            let Some(trait_id) = implementation
                .of_trait
                .and_then(|reference| reference.trait_def_id())
            else {
                continue;
            };
            let name = tcx.item_name(trait_id);
            if !matches!(
                name.as_str(),
                "Copy"
                    | "Clone"
                    | "Debug"
                    | "Default"
                    | "PartialEq"
                    | "Eq"
                    | "PartialOrd"
                    | "Ord"
                    | "Hash"
                    | "Zeroable"
                    | "Pod"
                    | "AnyBitPattern"
                    | "NoUninit"
            ) {
                continue;
            }
            let ty = tcx.type_of(item.owner_id.def_id).instantiate_identity();
            if let TyKind::Adt(definition, _) = ty.kind()
                && let Some(owner) = definition.did().as_local()
                && reachable_structs([ty], tcx)
                    .iter()
                    .any(|did| changed_structs.contains(did))
                && !(definition.is_enum() && name.as_str() == "Default")
            {
                derived.push((owner, trait_id, name));
            }
        }
        loop {
            let mut changed = false;
            for &(owner, trait_id, name) in &derived {
                if self
                    .invalid_derives
                    .get(&owner)
                    .is_some_and(|names| names.contains(&name))
                {
                    continue;
                }
                let definition = tcx.adt_def(owner);
                let arguments = ty::GenericArgs::identity_for_item(tcx, owner);
                let valid = definition.variants().iter().all(|variant| {
                    variant.fields.iter_enumerated().all(|(index, field)| {
                        let layers = if definition.is_struct() {
                            fields
                                .get(&StructFieldSlot {
                                    struct_did: owner,
                                    field_index: index.as_usize(),
                                })
                                .map(Vec::as_slice)
                                .unwrap_or_default()
                        } else {
                            &[]
                        };
                        self.supports_derive(
                            target_semantic_type(field.ty(tcx, arguments), layers, tcx),
                            trait_id,
                            name,
                            owner,
                            tcx,
                            &mut FxHashSet::default(),
                        )
                    })
                });
                if !valid {
                    self.invalid_derives.entry(owner).or_default().insert(name);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn supports_derive<'tcx>(
        &self,
        target: ty::Ty<'tcx>,
        trait_id: rustc_span::def_id::DefId,
        name: Symbol,
        owner: LocalDefId,
        tcx: TyCtxt<'tcx>,
        visited: &mut FxHashSet<(ty::Ty<'tcx>, rustc_span::def_id::DefId)>,
    ) -> bool {
        if !visited.insert((target, trait_id)) {
            return true;
        }
        if let TyKind::Adt(definition, _) = target.kind()
            && definition.did().as_local().is_some_and(|did| {
                self.invalid_derives
                    .get(&did)
                    .is_some_and(|names| names.contains(&name))
            })
        {
            return false;
        }
        if self.plans.get(&owner).is_some_and(|plan| !plan.is_empty())
            && tcx.crate_name(trait_id.krate).as_str() == "bytemuck"
            && matches!(name.as_str(), "Pod" | "AnyBitPattern" | "NoUninit")
        {
            return false;
        }
        let infcx = tcx.infer_ctxt().build(ty::TypingMode::PostAnalysis);
        let arguments = if matches!(name.as_str(), "PartialEq" | "PartialOrd") {
            vec![target, target]
        } else {
            vec![target]
        };
        let reference = ty::TraitRef::new(tcx, trait_id, arguments);
        let obligation = rustc_trait_selection::traits::Obligation {
            cause: rustc_trait_selection::traits::ObligationCause::dummy(),
            param_env: tcx.param_env(owner),
            recursion_depth: 0,
            predicate: ty::TraitPredicate {
                trait_ref: reference,
                polarity: ty::PredicatePolarity::Positive,
            },
        };
        let Ok(Some(selection)) =
            rustc_trait_selection::traits::SelectionContext::new(&infcx).select(&obligation)
        else {
            return false;
        };
        for nested in selection.nested_obligations() {
            if !infcx
                .evaluate_obligation_no_overflow(&nested)
                .must_apply_modulo_regions()
            {
                return false;
            }
            if let ty::PredicateKind::Clause(ty::ClauseKind::Trait(predicate)) =
                nested.predicate.kind().skip_binder()
            {
                let target = infcx.resolve_vars_if_possible(predicate.self_ty());
                let trait_id = predicate.trait_ref.def_id;
                if !self.supports_derive(
                    target,
                    trait_id,
                    tcx.item_name(trait_id),
                    owner,
                    tcx,
                    visited,
                ) {
                    return false;
                }
            }
        }
        true
    }

    pub(crate) fn regions_of(&self, source: ty::Ty<'_>) -> BTreeSet<FieldRegion> {
        let mut result = BTreeSet::new();
        let mut pending = vec![source];
        while let Some(ty) = pending.pop() {
            match ty.kind() {
                TyKind::RawPtr(inner, _)
                | TyKind::Ref(_, inner, _)
                | TyKind::Array(inner, _)
                | TyKind::Slice(inner) => pending.push(*inner),
                TyKind::Tuple(elements) => pending.extend(elements.iter()),
                TyKind::Adt(definition, arguments) => {
                    if let Some(plan) = definition
                        .did()
                        .as_local()
                        .and_then(|did| self.plans.get(&did))
                    {
                        result.extend(plan.keys().copied());
                    }
                    pending.extend(arguments.types());
                }
                _ => {}
            }
        }
        result
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn rewrite_ty(
        &self,
        target: &mut Ty,
        source: ty::Ty<'_>,
        layers: &[PointerLayer],
        names: Option<&BTreeMap<FieldRegion, Symbol>>,
        mapping: &utils::ir::AstToHir,
        source_hint: Option<&Ty>,
        tcx: TyCtxt<'_>,
    ) {
        let hint = source_hint.filter(|hint| match (&target.kind, &hint.kind) {
            (AstTyKind::Path(_, target), AstTyKind::Path(_, source)) => {
                target.segments.last().map(|segment| segment.ident.name)
                    == source.segments.last().map(|segment| segment.ident.name)
            }
            _ => false,
        });
        let resolved = mapping
            .get_ty(target.id, tcx)
            .or_else(|| hint.and_then(|hint| mapping.get_ty(hint.id, tcx)))
            .and_then(|ty| match ty.kind {
                hir::TyKind::Path(hir::QPath::Resolved(_, path)) => match path.res {
                    Res::Def(_, did) => did.as_local(),
                    _ => None,
                },
                _ => None,
            });
        if let Some(did) = resolved
            && matches!(tcx.def_kind(did), hir::def::DefKind::TyAlias)
            && let Some(plan) = self.plans.get(&did)
        {
            add_arguments(
                target,
                plan.keys().map(|region| {
                    names
                        .and_then(|names| names.get(region))
                        .copied()
                        .unwrap_or(Symbol::intern("_"))
                }),
            );
            return;
        }
        if let TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) = source.kind() {
            let kind = layers.first().map(|layer| layer.kind);
            if let Some(pointee) = target_pointee(target, kind) {
                let hint = source_hint.and_then(|hint| match &hint.kind {
                    AstTyKind::Ptr(inner) | AstTyKind::Ref(_, inner) => Some(&*inner.ty),
                    _ => None,
                });
                self.rewrite_ty(
                    pointee,
                    *inner,
                    layers.get(1..).unwrap_or_default(),
                    names,
                    mapping,
                    hint,
                    tcx,
                );
            }
            return;
        }
        match (&mut target.kind, source.kind()) {
            (
                AstTyKind::Array(element, _) | AstTyKind::Slice(element),
                TyKind::Array(inner, _) | TyKind::Slice(inner),
            ) => self.rewrite_ty(
                element,
                *inner,
                &[],
                names,
                mapping,
                source_hint.and_then(|hint| match &hint.kind {
                    AstTyKind::Array(inner, _) | AstTyKind::Slice(inner) => Some(&**inner),
                    _ => None,
                }),
                tcx,
            ),
            (AstTyKind::Tup(elements), TyKind::Tuple(types)) => {
                for (index, (element, ty)) in elements.iter_mut().zip(types.iter()).enumerate() {
                    let hint = source_hint.and_then(|hint| match &hint.kind {
                        AstTyKind::Tup(elements) => elements.get(index).map(|ty| &**ty),
                        _ => None,
                    });
                    self.rewrite_ty(element, ty, &[], names, mapping, hint, tcx);
                }
            }
            (AstTyKind::Path(_, path), TyKind::Adt(definition, arguments)) => {
                if let Some(segment) = path.segments.last_mut()
                    && let Some(args) = &mut segment.args
                    && let GenericArgs::AngleBracketed(args) = &mut **args
                {
                    for (index, (argument, source)) in args
                        .args
                        .iter_mut()
                        .filter_map(|argument| match argument {
                            AngleBracketedArg::Arg(GenericArg::Type(ty)) => Some(ty),
                            _ => None,
                        })
                        .zip(arguments.types())
                        .enumerate()
                    {
                        let hint = source_hint.and_then(|hint| match &hint.kind {
                            AstTyKind::Path(_, path) => path
                                .segments
                                .last()
                                .and_then(|segment| segment.args.as_deref())
                                .and_then(|args| match args {
                                    GenericArgs::AngleBracketed(args) => args
                                        .args
                                        .iter()
                                        .filter_map(|argument| match argument {
                                            AngleBracketedArg::Arg(GenericArg::Type(ty)) => {
                                                Some(&**ty)
                                            }
                                            _ => None,
                                        })
                                        .nth(index),
                                    _ => None,
                                }),
                            _ => None,
                        });
                        self.rewrite_ty(argument, source, &[], names, mapping, hint, tcx);
                    }
                }
                if let Some(plan) = resolved
                    .or_else(|| definition.did().as_local())
                    .and_then(|did| self.plans.get(&did))
                {
                    add_arguments(
                        target,
                        plan.keys().map(|region| {
                            names
                                .and_then(|names| names.get(region))
                                .copied()
                                .unwrap_or(Symbol::intern("_"))
                        }),
                    );
                }
            }
            _ => {}
        }
    }
}

fn target_semantic_type<'tcx>(
    source: ty::Ty<'tcx>,
    layers: &[PointerLayer],
    tcx: TyCtxt<'tcx>,
) -> ty::Ty<'tcx> {
    let Some((layer, rest)) = layers.split_first() else { return source };
    let TyKind::RawPtr(inner, _) = source.kind() else { return source };
    let inner = target_semantic_type(*inner, rest, tcx);
    let mutable = if layer.kind.is_mut() {
        hir::Mutability::Mut
    } else {
        hir::Mutability::Not
    };
    let slice = matches!(
        layer.kind,
        PtrKind::Slice(_) | PtrKind::OptSlice(_) | PtrKind::BoxedSlice | PtrKind::OptBoxedSlice
    );
    let inner = if slice {
        ty::Ty::new_slice(tcx, inner)
    } else {
        inner
    };
    let target = match layer.kind {
        PtrKind::Raw(_) => ty::Ty::new_ptr(tcx, inner, mutable),
        PtrKind::Box | PtrKind::OptBox | PtrKind::BoxedSlice | PtrKind::OptBoxedSlice => {
            ty::Ty::new_box(tcx, inner)
        }
        _ => ty::Ty::new_ref(tcx, tcx.lifetimes.re_erased, inner, mutable),
    };
    if matches!(
        layer.kind,
        PtrKind::OptRef(_) | PtrKind::OptSlice(_) | PtrKind::OptBox | PtrKind::OptBoxedSlice
    ) {
        let option = tcx.adt_def(tcx.require_lang_item(hir::LangItem::Option, DUMMY_SP));
        ty::Ty::new_adt(tcx, option, tcx.mk_args(&[target.into()]))
    } else {
        target
    }
}

fn add_arguments(target: &mut Ty, names: impl Iterator<Item = Symbol>) {
    let AstTyKind::Path(_, path) = &mut target.kind else { return };
    let Some(segment) = path.segments.last_mut() else { return };
    let args = segment.args.get_or_insert_with(|| {
        P(GenericArgs::AngleBracketed(AngleBracketedArgs {
            span: DUMMY_SP,
            args: Default::default(),
        }))
    });
    let GenericArgs::AngleBracketed(args) = &mut **args else { return };
    for (offset, name) in names.enumerate() {
        let parsed = utils::ty!("&'{} i32", name.as_str());
        let AstTyKind::Ref(Some(lifetime), _) = parsed.kind else { unreachable!() };
        args.args.insert(
            offset,
            AngleBracketedArg::Arg(GenericArg::Lifetime(lifetime)),
        );
    }
}

fn first_type(ty: &mut Ty) -> Option<&mut Ty> {
    let AstTyKind::Path(_, path) = &mut ty.kind else { return None };
    let GenericArgs::AngleBracketed(args) = &mut **path.segments.last_mut()?.args.as_mut()? else {
        return None;
    };
    args.args.iter_mut().find_map(|argument| match argument {
        AngleBracketedArg::Arg(GenericArg::Type(ty)) => Some(&mut **ty),
        _ => None,
    })
}

fn target_pointee(ty: &mut Ty, kind: Option<PtrKind>) -> Option<&mut Ty> {
    match kind {
        Some(
            PtrKind::OptRef(_) | PtrKind::OptSlice(_) | PtrKind::OptBox | PtrKind::OptBoxedSlice,
        ) => {
            let payload = first_type(ty)?;
            let inner = match kind.unwrap() {
                PtrKind::OptRef(mutable) => PtrKind::Ref(mutable),
                PtrKind::OptSlice(mutable) => PtrKind::Slice(mutable),
                PtrKind::OptBox => PtrKind::Box,
                PtrKind::OptBoxedSlice => PtrKind::BoxedSlice,
                _ => unreachable!(),
            };
            target_pointee(payload, Some(inner))
        }
        Some(PtrKind::Box) => first_type(ty),
        Some(PtrKind::BoxedSlice) => match &mut first_type(ty)?.kind {
            AstTyKind::Slice(inner) => Some(inner),
            _ => None,
        },
        Some(PtrKind::Slice(_)) => match &mut ty.kind {
            AstTyKind::Ref(_, inner) => match &mut inner.ty.kind {
                AstTyKind::Slice(element) => Some(element),
                _ => None,
            },
            _ => None,
        },
        _ => match &mut ty.kind {
            AstTyKind::Ptr(inner) | AstTyKind::Ref(_, inner) => Some(&mut inner.ty),
            _ => None,
        },
    }
}
