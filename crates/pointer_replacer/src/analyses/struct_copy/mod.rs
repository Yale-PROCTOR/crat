use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir,
    def::{DefKind, Res},
};
use rustc_middle::{
    mir::{Body, Local, Operand, Place, PlaceElem, Rvalue, StatementKind, TerminatorKind},
    ty::{self, TyCtxt},
};
use rustc_span::def_id::LocalDefId;

use crate::{analyses::borrow::StructFieldSlot, utils::rustc::RustProgram};

#[derive(Debug, Default)]
pub struct StructCopyAnalysisResult {
    copy_impl_structs: FxHashSet<LocalDefId>,
    copy_removable_structs: FxHashSet<LocalDefId>,
}

impl StructCopyAnalysisResult {
    pub fn must_preserve_copy(&self, struct_did: LocalDefId) -> bool {
        self.copy_impl_structs.contains(&struct_did)
            && !self.copy_removable_structs.contains(&struct_did)
    }

    pub fn should_remove_generated_impl(&self, struct_did: LocalDefId) -> bool {
        self.copy_removable_structs.contains(&struct_did)
    }
}

pub fn analyze(
    input: &RustProgram<'_>,
    mutable_fields: &FxHashSet<StructFieldSlot>,
) -> StructCopyAnalysisResult {
    let copy_impls = collect_copy_impls(input.tcx);
    let candidate_structs = mutable_fields
        .iter()
        .map(|field| field.struct_did)
        .collect::<FxHashSet<_>>();
    let candidate_generated_copy_structs = candidate_structs
        .iter()
        .copied()
        .filter(|struct_did| copy_impls.generated.contains(struct_did))
        .collect::<FxHashSet<_>>();

    let mut required = collect_hard_copy_requirements(input);
    propagate_copy_field_requirements(
        input.tcx,
        &copy_impls.all,
        &candidate_generated_copy_structs,
        &mut required,
    );

    let copy_removable_structs = candidate_generated_copy_structs
        .difference(&required)
        .copied()
        .collect();

    StructCopyAnalysisResult {
        copy_impl_structs: copy_impls.all,
        copy_removable_structs,
    }
}

#[derive(Default)]
struct CopyImpls {
    all: FxHashSet<LocalDefId>,
    generated: FxHashSet<LocalDefId>,
}

fn collect_copy_impls(tcx: TyCtxt<'_>) -> CopyImpls {
    let mut impls = CopyImpls::default();
    for owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Impl(impl_) = item.kind else {
            continue;
        };
        let Some(of_trait) = impl_.of_trait else {
            continue;
        };
        if !matches!(
            of_trait.path.segments.last(),
            Some(seg) if seg.ident.name.as_str() == "Copy"
        ) {
            continue;
        }
        let Some(struct_did) = hir_local_struct_did_from_ty(impl_.self_ty) else {
            continue;
        };
        impls.all.insert(struct_did);
        if tcx.is_automatically_derived(item.owner_id.def_id.to_def_id()) {
            impls.generated.insert(struct_did);
        }
    }
    impls
}

fn collect_hard_copy_requirements(input: &RustProgram<'_>) -> FxHashSet<LocalDefId> {
    let mut required = FxHashSet::default();
    for &did in &input.functions {
        let body = input
            .tcx
            .mir_drops_elaborated_and_const_checked(did)
            .borrow();
        collect_body_hard_copy_requirements(input.tcx, &body, &mut required);
    }
    required
}

fn collect_body_hard_copy_requirements<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    required: &mut FxHashSet<LocalDefId>,
) {
    let mut moved_into_raw_storage: FxHashSet<(Local, LocalDefId)> = FxHashSet::default();
    let mut copy_aliases: FxHashMap<Local, (Local, LocalDefId)> = FxHashMap::default();

    for block in body.basic_blocks.iter() {
        for stmt in &block.statements {
            if let StatementKind::Assign(box (lhs, rvalue)) = &stmt.kind {
                inspect_rvalue_operands(tcx, body, rvalue, &moved_into_raw_storage, required);

                if let Some(local) = lhs.as_local() {
                    moved_into_raw_storage.retain(|(moved_local, _)| *moved_local != local);
                    copy_aliases.remove(&local);
                }
                if place_has_raw_deref(body, *lhs)
                    && let Some((local, struct_did)) = rvalue_local_struct_source(tcx, body, rvalue)
                {
                    moved_into_raw_storage.insert(resolve_copy_alias(
                        local,
                        struct_did,
                        &copy_aliases,
                    ));
                }
                if let Some(lhs_local) = lhs.as_local()
                    && let Some((rhs_local, rhs_struct)) =
                        rvalue_local_struct_source(tcx, body, rvalue)
                {
                    copy_aliases.insert(
                        lhs_local,
                        resolve_copy_alias(rhs_local, rhs_struct, &copy_aliases),
                    );
                }
            }
        }

        let terminator = block.terminator();
        match &terminator.kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                inspect_operand(tcx, body, func, &moved_into_raw_storage, required);
                for arg in args {
                    inspect_operand(tcx, body, &arg.node, &moved_into_raw_storage, required);
                }
            }
            TerminatorKind::SwitchInt { discr, .. }
            | TerminatorKind::Assert { cond: discr, .. } => {
                inspect_operand(tcx, body, discr, &moved_into_raw_storage, required);
            }
            TerminatorKind::Yield { value, .. } => {
                inspect_operand(tcx, body, value, &moved_into_raw_storage, required);
            }
            _ => {}
        }
    }
}

fn resolve_copy_alias(
    mut local: Local,
    mut struct_did: LocalDefId,
    copy_aliases: &FxHashMap<Local, (Local, LocalDefId)>,
) -> (Local, LocalDefId) {
    let mut seen = FxHashSet::default();
    while seen.insert(local) {
        let Some(&(next_local, next_struct)) = copy_aliases.get(&local) else {
            break;
        };
        local = next_local;
        struct_did = next_struct;
    }
    (local, struct_did)
}

fn inspect_rvalue_operands<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rvalue: &Rvalue<'tcx>,
    moved_into_raw_storage: &FxHashSet<(Local, LocalDefId)>,
    required: &mut FxHashSet<LocalDefId>,
) {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::Repeat(operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(_, operand, _)
        | Rvalue::ShallowInitBox(operand, _)
        | Rvalue::WrapUnsafeBinder(operand, _) => {
            inspect_operand(tcx, body, operand, moved_into_raw_storage, required);
            if matches!(rvalue, Rvalue::Repeat(..))
                && let Some(struct_did) = operand_local_struct(tcx, body, operand)
            {
                required.insert(struct_did);
            }
        }
        Rvalue::BinaryOp(_, box (lhs, rhs)) => {
            inspect_operand(tcx, body, lhs, moved_into_raw_storage, required);
            inspect_operand(tcx, body, rhs, moved_into_raw_storage, required);
        }
        Rvalue::Aggregate(_, operands) => {
            for operand in operands {
                inspect_operand(tcx, body, operand, moved_into_raw_storage, required);
            }
        }
        Rvalue::CopyForDeref(place) => {
            inspect_place(tcx, body, *place, moved_into_raw_storage, required);
        }
        _ => {}
    }
}

fn inspect_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
    moved_into_raw_storage: &FxHashSet<(Local, LocalDefId)>,
    required: &mut FxHashSet<LocalDefId>,
) {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return;
    };
    inspect_place(tcx, body, *place, moved_into_raw_storage, required);
}

fn inspect_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: Place<'tcx>,
    moved_into_raw_storage: &FxHashSet<(Local, LocalDefId)>,
    required: &mut FxHashSet<LocalDefId>,
) {
    for &(local, struct_did) in moved_into_raw_storage {
        if place.local == local {
            required.insert(struct_did);
        }
    }

    if place_has_raw_deref(body, place)
        && let Some(struct_did) = local_struct_ty(place.ty(body, tcx).ty)
    {
        required.insert(struct_did);
    }
}

fn rvalue_local_struct_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<(Local, LocalDefId)> {
    let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = rvalue else {
        return None;
    };
    let local = place.as_local()?;
    let struct_did = local_struct_ty(place.ty(body, tcx).ty)?;
    Some((local, struct_did))
}

fn operand_local_struct<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<LocalDefId> {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return None;
    };
    local_struct_ty(place.ty(body, tcx).ty)
}

fn place_has_raw_deref(body: &Body<'_>, place: Place<'_>) -> bool {
    body.local_decls[place.local].ty.is_raw_ptr()
        && place
            .projection
            .iter()
            .any(|elem| matches!(elem, PlaceElem::Deref))
}

fn propagate_copy_field_requirements(
    tcx: TyCtxt<'_>,
    copy_impl_structs: &FxHashSet<LocalDefId>,
    candidate_removable_structs: &FxHashSet<LocalDefId>,
    required: &mut FxHashSet<LocalDefId>,
) {
    loop {
        let mut changed = false;
        for &container in copy_impl_structs {
            let container_copy_will_be_removed =
                candidate_removable_structs.contains(&container) && !required.contains(&container);
            if container_copy_will_be_removed {
                continue;
            }

            for field_struct in copied_field_structs(tcx, container) {
                if copy_impl_structs.contains(&field_struct) {
                    changed |= required.insert(field_struct);
                }
            }
        }

        if !changed {
            break;
        }
    }
}

fn copied_field_structs(tcx: TyCtxt<'_>, struct_did: LocalDefId) -> FxHashSet<LocalDefId> {
    let mut copied = FxHashSet::default();
    let struct_ty = tcx.type_of(struct_did).skip_binder();
    let ty::TyKind::Adt(adt_def, args) = struct_ty.kind() else {
        return copied;
    };
    for field in adt_def.all_fields() {
        collect_local_structs_requiring_copy(field.ty(tcx, args), &mut copied);
    }
    copied.remove(&struct_did);
    copied
}

fn collect_local_structs_requiring_copy(ty: ty::Ty<'_>, out: &mut FxHashSet<LocalDefId>) {
    match ty.kind() {
        ty::TyKind::Adt(adt_def, args) => {
            if adt_def.did().is_local() && adt_def.is_struct() && !adt_def.is_union() {
                out.insert(adt_def.did().expect_local());
            }
            for arg in args.iter() {
                if let ty::GenericArgKind::Type(ty) = arg.kind() {
                    collect_local_structs_requiring_copy(ty, out);
                }
            }
        }
        ty::TyKind::Array(inner, _) | ty::TyKind::Slice(inner) => {
            collect_local_structs_requiring_copy(*inner, out);
        }
        ty::TyKind::Tuple(fields) => {
            for field in fields.iter() {
                collect_local_structs_requiring_copy(field, out);
            }
        }
        ty::TyKind::RawPtr(..) | ty::TyKind::Ref(..) => {}
        _ => {}
    }
}

fn local_struct_ty(ty: ty::Ty<'_>) -> Option<LocalDefId> {
    let ty::TyKind::Adt(adt_def, _) = ty.kind() else {
        return None;
    };
    (adt_def.did().is_local() && adt_def.is_struct() && !adt_def.is_union())
        .then(|| adt_def.did().expect_local())
}

fn hir_local_struct_did_from_ty(ty: &hir::Ty<'_>) -> Option<LocalDefId> {
    let hir::TyKind::Path(qpath) = ty.kind else {
        return None;
    };
    hir_local_struct_did_from_qpath(&qpath)
}

fn hir_local_struct_did_from_qpath(qpath: &hir::QPath<'_>) -> Option<LocalDefId> {
    let hir::QPath::Resolved(_, path) = qpath else {
        return None;
    };
    match path.res {
        Res::Def(DefKind::Struct, def_id) if def_id.is_local() => Some(def_id.expect_local()),
        _ => None,
    }
}
