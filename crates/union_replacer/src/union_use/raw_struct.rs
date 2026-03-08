use rustc_ast::mut_visit::MutVisitor;
use rustc_hash::FxHashMap;
use rustc_middle::ty::{Ty, TyCtxt, TypingMode};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_trait_selection::infer::{InferCtxtExt as _, TyCtxtInferExt as _};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldTypeClass {
    AnyBitPattern,
    NoUninit,
    Pod,
    Other,
}

#[derive(Debug, Clone)]
pub struct UnionFieldClassification<'tcx> {
    pub field_name: String,
    pub field_ty: Ty<'tcx>,
    pub class: FieldTypeClass,
}

#[derive(Debug, Clone, Copy, Default)]
struct BytemuckTraitIds {
    any_bit_pattern: Option<DefId>,
    no_uninit: Option<DefId>,
    pod: Option<DefId>,
}

pub fn has_visible_bytemuck_traits(tcx: TyCtxt<'_>) -> bool {
    let trait_ids = resolve_bytemuck_trait_ids(tcx);
    trait_ids.pod.is_some() || trait_ids.any_bit_pattern.is_some() || trait_ids.no_uninit.is_some()
}

/// Classify each local union field type into one of:
/// `AnyBitPattern` / `NoUninit` / `Pod` / `Other`.
pub fn classify_union_field_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_tys: &[LocalDefId],
    verbose: bool,
) -> FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>> {
    let trait_ids = resolve_bytemuck_trait_ids(tcx);
    if verbose {
        println!(
            "\nBytemuck trait ids: Pod={:?}, AnyBitPattern={:?}, NoUninit={:?}",
            trait_ids.pod, trait_ids.any_bit_pattern, trait_ids.no_uninit
        );
    }
    let mut class_cache: FxHashMap<Ty<'tcx>, FieldTypeClass> = FxHashMap::default();
    let mut results: FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>> =
        FxHashMap::default();

    for &union_ty in union_tys {
        let union_adt = tcx.adt_def(union_ty.to_def_id());
        if !union_adt.is_union() {
            continue;
        }

        let union_ty_value = tcx.type_of(union_ty).instantiate_identity();
        let mut fields = Vec::new();
        if let rustc_middle::ty::TyKind::Adt(_, args) = union_ty_value.kind() {
            for field in union_adt.all_fields() {
                let field_ty = field.ty(tcx, args);
                let class = *class_cache
                    .entry(field_ty)
                    .or_insert_with(|| classify_field_type(tcx, union_ty, field_ty, trait_ids));
                fields.push(UnionFieldClassification {
                    field_name: field.ident(tcx).name.to_ident_string(),
                    field_ty,
                    class,
                });
            }
        }
        results.insert(union_ty, fields);
    }

    if verbose {
        println!("\nUnion Field Type Classification:");
        let mut unions = results.keys().copied().collect::<Vec<_>>();
        unions.sort_by_key(|def_id| tcx.def_path_str(*def_id));
        for union_ty in unions {
            println!("\t{}:", tcx.def_path_str(union_ty));
            for field in &results[&union_ty] {
                println!(
                    "\t\t{}: {:?} -> {:?}",
                    field.field_name, field.field_ty, field.class
                );
            }
        }
    }

    results
}

fn classify_field_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    ty: Ty<'tcx>,
    trait_ids: BytemuckTraitIds,
) -> FieldTypeClass {
    if trait_ids
        .pod
        .is_some_and(|did| ty_implements_trait(tcx, owner, ty, did))
    {
        return FieldTypeClass::Pod;
    }
    if trait_ids
        .any_bit_pattern
        .is_some_and(|did| ty_implements_trait(tcx, owner, ty, did))
    {
        return FieldTypeClass::AnyBitPattern;
    }
    if trait_ids
        .no_uninit
        .is_some_and(|did| ty_implements_trait(tcx, owner, ty, did))
    {
        return FieldTypeClass::NoUninit;
    }
    FieldTypeClass::Other
}

fn ty_implements_trait<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    ty: Ty<'tcx>,
    trait_def_id: DefId,
) -> bool {
    let param_env = tcx.param_env(owner);
    let infcx = tcx.infer_ctxt().build(TypingMode::non_body_analysis());
    infcx
        .type_implements_trait(trait_def_id, [ty], param_env)
        .must_apply_modulo_regions()
}

fn resolve_bytemuck_trait_ids(tcx: TyCtxt<'_>) -> BytemuckTraitIds {
    let mut trait_ids = BytemuckTraitIds::default();
    for did in tcx.all_traits() {
        if tcx.crate_name(did.krate).as_str() != "bytemuck" {
            continue;
        }
        match tcx.item_name(did).as_str() {
            "Pod" if trait_ids.pod.is_none() => trait_ids.pod = Some(did),
            "AnyBitPattern" if trait_ids.any_bit_pattern.is_none() => {
                trait_ids.any_bit_pattern = Some(did);
            }
            "NoUninit" if trait_ids.no_uninit.is_none() => {
                trait_ids.no_uninit = Some(did);
            }
            _ => {}
        }
    }
    trait_ids
}

pub struct RawStructVisitor<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub field_classes: FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>>,
}

impl<'tcx> RawStructVisitor<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        field_classes: FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>>,
    ) -> Self {
        Self { tcx, field_classes }
    }
}

impl MutVisitor for RawStructVisitor<'_> {}
