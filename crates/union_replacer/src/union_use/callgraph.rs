use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{
        Body, Location, Place,
        visit::{PlaceContext, Visitor as MirVisitor},
    },
    ty::{self, Ty, TyCtxt},
};
use rustc_span::def_id::LocalDefId;

struct BodyUnionUseCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    union_tys: &'a FxHashSet<LocalDefId>,
    found_unions: FxHashSet<LocalDefId>,
}

impl<'tcx, 'a> BodyUnionUseCollector<'tcx, 'a> {
    fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>, union_tys: &'a FxHashSet<LocalDefId>) -> Self {
        Self {
            tcx,
            body,
            union_tys,
            found_unions: FxHashSet::default(),
        }
    }
}

impl<'tcx> MirVisitor<'tcx> for BodyUnionUseCollector<'tcx, '_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        let ty = place.ty(self.body, self.tcx).ty;
        collect_union_ids_from_ty(ty, self.union_tys, &mut self.found_unions);
        self.super_place(place, context, location);
    }
}

fn collect_union_ids_from_ty<'tcx>(
    mut ty: Ty<'tcx>,
    union_tys: &FxHashSet<LocalDefId>,
    out: &mut FxHashSet<LocalDefId>,
) {
    loop {
        match ty.kind() {
            ty::Adt(adt_def, _) if adt_def.is_union() => {
                if let Some(local_id) = adt_def.did().as_local()
                    && union_tys.contains(&local_id)
                {
                    out.insert(local_id);
                }
                break;
            }
            ty::Ref(_, inner, _) => ty = *inner,
            ty::RawPtr(t, _) => ty = *t,
            _ => break,
        }
    }
}

pub fn collect_union_seed_functions<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_tys: &[LocalDefId],
    verbose: bool,
) -> FxHashMap<LocalDefId, Vec<LocalDefId>> {
    let union_tys: FxHashSet<_> = union_tys.iter().copied().collect();
    let mut map: FxHashMap<LocalDefId, FxHashSet<LocalDefId>> = union_tys
        .iter()
        .copied()
        .map(|union_ty| (union_ty, FxHashSet::default()))
        .collect();

    for def_id in tcx.hir_body_owners() {
        if !is_target_seed_function(tcx, def_id) {
            continue;
        }

        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body: &Body<'_> = &body.borrow();
        let mut found_unions = FxHashSet::default();

        for arg in body.args_iter() {
            let ty = body.local_decls[arg].ty;
            collect_union_ids_from_ty(ty, &union_tys, &mut found_unions);
        }

        let mut collector = BodyUnionUseCollector::new(tcx, body, &union_tys);
        collector.visit_body(body);
        found_unions.extend(collector.found_unions);

        for union_ty in found_unions {
            map.entry(union_ty).or_default().insert(def_id);
        }
    }

    let map: FxHashMap<LocalDefId, Vec<LocalDefId>> = map
        .into_iter()
        .map(|(union_ty, mut fn_ids)| {
            let mut fn_ids = fn_ids.drain().collect::<Vec<_>>();
            fn_ids.sort_by_key(|def_id| tcx.def_path_str(*def_id));
            (union_ty, fn_ids)
        })
        .collect();

    if verbose {
        println!("\nCallgraph Seed Functions:\n\t{}", {
            let mut lines = map
                .iter()
                .map(|(ty, funcs)| {
                    let ty_name = tcx.def_path_str(*ty);
                    let func_names = funcs
                        .iter()
                        .map(|def_id| tcx.def_path_str(*def_id))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{ty_name}\n\t\t-> {func_names}")
                })
                .collect::<Vec<_>>();
            lines.sort();
            lines.join("\n\t")
        });
    }

    map
}

fn is_target_seed_function(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return false;
    }

    // Skip compiler/macro-generated bodies (ex. clone)
    if tcx.def_span(def_id).from_expansion() {
        return false;
    }

    let def_id = def_id.to_def_id();
    if let Some(impl_id) = tcx.impl_of_method(def_id)
        && let Some(trait_id) = tcx.trait_id_of_impl(impl_id)
    {
        let trait_path = tcx.def_path_str(trait_id);
        if trait_path.starts_with("core::") || trait_path.starts_with("std::") {
            return false;
        }
    }

    true
}
