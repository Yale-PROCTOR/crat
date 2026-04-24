use rustc_abi::Size;
use rustc_ast::{
    Item, ItemKind,
    mut_visit::{self, MutVisitor},
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, TypeVisitableExt};
use rustc_span::def_id::{DefId, LocalDefId};
use utils::ir::AstToHir;

use super::raw_struct::UnionFieldClassification;

// This module recreates the bytemuck 1.24.x derive rules
// Assume AnyBitPattern + NoUninit = Pod, which is a stricter requirement than bytemuck's actual Pod.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldTypeClass {
    AnyBitPattern,
    NoUninit(bool),
    Pod,
    Other,
}

impl FieldTypeClass {
    pub fn is_other(self) -> bool {
        matches!(self, Self::Other)
    }

    pub fn is_pod(self) -> bool {
        matches!(self, Self::Pod)
    }

    pub fn is_writable(self) -> bool {
        matches!(self, Self::Pod | Self::NoUninit(_))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DerivedMarker {
    NoUninit,
    AnyBitPattern,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BytemuckDerive {
    Zeroable,
    AnyBitPattern,
    NoUninit,
    Pod,
}

#[derive(Debug, Default, Clone)]
pub struct BytemuckDerivePlan {
    pub per_type: FxHashMap<LocalDefId, FxHashSet<BytemuckDerive>>,
}

pub struct BytemuckTypeClassifier<'tcx> {
    tcx: TyCtxt<'tcx>,
    derivable_cache: FxHashMap<(Ty<'tcx>, DerivedMarker), bool>,
    in_progress: FxHashSet<(Ty<'tcx>, DerivedMarker)>,
}

impl<'tcx> BytemuckTypeClassifier<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            derivable_cache: FxHashMap::default(),
            in_progress: FxHashSet::default(),
        }
    }

    pub fn classify_type(&mut self, _owner: LocalDefId, ty: Ty<'tcx>) -> FieldTypeClass {
        if let Some(class) = Self::primitive_class(ty) {
            return class;
        }

        let is_any_bit_pattern = self.is_derivable(ty, DerivedMarker::AnyBitPattern);
        let is_no_uninit = self.is_derivable(ty, DerivedMarker::NoUninit);

        match (is_any_bit_pattern, is_no_uninit) {
            (true, true) => FieldTypeClass::Pod,
            (true, false) => FieldTypeClass::AnyBitPattern,
            (false, true) => FieldTypeClass::NoUninit(matches!(ty.kind(), TyKind::RawPtr(..))),
            (false, false) => FieldTypeClass::Other,
        }
    }

    pub fn derive_markers_for_type(&mut self, ty: Ty<'tcx>) -> FxHashSet<BytemuckDerive> {
        let mut derives = FxHashSet::default();
        let is_any_bit_pattern = self.is_derivable(ty, DerivedMarker::AnyBitPattern);
        let is_no_uninit = self.is_derivable(ty, DerivedMarker::NoUninit);

        match (is_any_bit_pattern, is_no_uninit) {
            (true, true) => {
                derives.insert(BytemuckDerive::Zeroable);
                derives.insert(BytemuckDerive::Pod);
            }
            (true, false) => {
                derives.insert(BytemuckDerive::AnyBitPattern);
            }
            (false, true) => {
                derives.insert(BytemuckDerive::NoUninit);
            }
            (false, false) => {}
        }

        derives
    }

    fn primitive_class(ty: Ty<'tcx>) -> Option<FieldTypeClass> {
        match ty.kind() {
            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => Some(FieldTypeClass::Pod),
            TyKind::RawPtr(..) => Some(FieldTypeClass::NoUninit(true)),
            TyKind::Char | TyKind::Bool => Some(FieldTypeClass::NoUninit(false)),
            TyKind::Array(elem, _) => Self::primitive_class(*elem),
            TyKind::Ref(..) | TyKind::Never | TyKind::FnDef(..) | TyKind::FnPtr(..) => {
                Some(FieldTypeClass::Other)
            }
            _ => None,
        }
    }

    fn is_derivable(&mut self, ty: Ty<'tcx>, marker: DerivedMarker) -> bool {
        if let Some(&cached) = self.derivable_cache.get(&(ty, marker)) {
            return cached;
        }
        if !self.in_progress.insert((ty, marker)) {
            return false;
        }

        let result = self.compute_derivable(ty, marker);
        self.in_progress.remove(&(ty, marker));
        self.derivable_cache.insert((ty, marker), result);
        result
    }

    fn compute_derivable(&mut self, ty: Ty<'tcx>, marker: DerivedMarker) -> bool {
        if ty.has_non_region_param() || ty.has_escaping_bound_vars() {
            return false;
        }
        if !self.is_pod_candidate(ty) {
            return false;
        }

        match ty.kind() {
            TyKind::Array(elem, _) => self.is_derivable(*elem, marker),
            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => true,
            TyKind::Char | TyKind::Bool | TyKind::RawPtr(..) => {
                matches!(marker, DerivedMarker::NoUninit)
            }
            TyKind::Ref(..) | TyKind::Never | TyKind::FnDef(..) | TyKind::FnPtr(..) => false,
            TyKind::Adt(adt, args) if adt.is_struct() => {
                self.is_derivable_struct(adt.did(), args, marker)
            }
            _ => false,
        }
    }

    fn is_derivable_struct(
        &mut self,
        did: DefId,
        args: ty::GenericArgsRef<'tcx>,
        marker: DerivedMarker,
    ) -> bool {
        let Some(local_def_id) = did.as_local() else {
            return false;
        };
        let adt = self.tcx.adt_def(did);
        let repr = adt.repr();

        match marker {
            DerivedMarker::NoUninit => {
                if !(repr.c() || repr.transparent()) {
                    return false;
                }
                if !self.has_no_padding(local_def_id, args) {
                    return false;
                }
            }
            DerivedMarker::AnyBitPattern => {}
        }

        for field in adt.all_fields() {
            let field_ty = field.ty(self.tcx, args);
            if !self.is_derivable(field_ty, marker) {
                return false;
            }
        }

        true
    }

    fn is_pod_candidate(&self, ty: Ty<'tcx>) -> bool {
        ty.is_sized(self.tcx, ty::TypingEnv::fully_monomorphized())
            && self
                .tcx
                .type_is_copy_modulo_regions(ty::TypingEnv::fully_monomorphized(), ty)
    }

    fn has_no_padding(&self, owner: LocalDefId, args: ty::GenericArgsRef<'tcx>) -> bool {
        let ty = Ty::new_adt(self.tcx, self.tcx.adt_def(owner.to_def_id()), args);
        let typing_env = ty::TypingEnv::post_analysis(self.tcx, owner);
        let Ok(layout) = self.tcx.layout_of(typing_env.as_query_input(ty)) else {
            return false;
        };

        let adt = self.tcx.adt_def(owner.to_def_id());
        let mut fields = adt
            .all_fields()
            .enumerate()
            .map(|(index, field)| {
                let field_ty = field.ty(self.tcx, args);
                let field_size = match self.tcx.layout_of(typing_env.as_query_input(field_ty)) {
                    Ok(field_layout) => field_layout.size,
                    Err(_) => return None,
                };
                Some((layout.fields.offset(index), field_size))
            })
            .collect::<Option<Vec<_>>>();

        let Some(fields) = fields.take() else {
            return false;
        };

        let mut fields = fields;
        fields.sort_by_key(|(offset, _)| offset.bytes());

        let mut cursor = Size::ZERO;
        for (offset, size) in fields {
            if size == Size::ZERO {
                continue;
            }
            if offset != cursor {
                return false;
            }
            cursor = offset + size;
        }

        cursor == layout.size
    }
}

/// This function must be called after the analysis
pub fn build_bytemuck_derive_plan<'tcx>(
    tcx: TyCtxt<'tcx>,
    punning_tys: &[LocalDefId],
    field_classes: &FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>>,
) -> BytemuckDerivePlan {
    let mut builder = BytemuckDerivePlanBuilder::new(tcx);

    for &union_ty in punning_tys {
        let Some(fields) = field_classes.get(&union_ty) else {
            continue;
        };
        for field in fields {
            if !field.class.is_other() {
                builder.collect_from_ty(field.field_ty);
            }
        }
    }

    builder.plan
}

struct BytemuckDerivePlanBuilder<'tcx> {
    tcx: TyCtxt<'tcx>,
    classifier: BytemuckTypeClassifier<'tcx>,
    visited_tys: FxHashSet<Ty<'tcx>>,
    plan: BytemuckDerivePlan,
}

impl<'tcx> BytemuckDerivePlanBuilder<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            classifier: BytemuckTypeClassifier::new(tcx),
            visited_tys: FxHashSet::default(),
            plan: BytemuckDerivePlan::default(),
        }
    }

    fn collect_from_ty(&mut self, ty: Ty<'tcx>) {
        if !self.visited_tys.insert(ty) {
            return;
        }

        match ty.kind() {
            TyKind::Array(elem, _) => self.collect_from_ty(*elem),
            TyKind::Adt(adt, args) if adt.is_struct() => {
                let Some(local_def_id) = adt.did().as_local() else {
                    return;
                };
                let derives = self.classifier.derive_markers_for_type(ty);

                // if ty derives some bytemuck traits, record that in the plan
                if !derives.is_empty() {
                    self.plan
                        .per_type
                        .entry(local_def_id)
                        .or_default()
                        .extend(derives);
                }

                // and then recursively check its fields
                for field in adt.all_fields() {
                    self.collect_from_ty(field.ty(self.tcx, args));
                }
            }
            _ => {}
        }
    }
}

/// Visitor for bytemuck derives
pub struct BytemuckDeriveVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a AstToHir,
    derives_by_type: FxHashMap<LocalDefId, Vec<BytemuckDerive>>,
}

impl<'a, 'tcx> BytemuckDeriveVisitor<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, ast_to_hir: &'a AstToHir, plan: BytemuckDerivePlan) -> Self {
        let derives_by_type = plan
            .per_type
            .into_iter()
            .map(|(local_def_id, derives)| {
                let derives = derives.into_iter().collect::<Vec<_>>();
                (local_def_id, derives)
            })
            .collect();
        Self {
            tcx,
            ast_to_hir,
            derives_by_type,
        }
    }
}

impl MutVisitor for BytemuckDeriveVisitor<'_, '_> {
    fn visit_item(&mut self, item: &mut Item) {
        mut_visit::walk_item(self, item);

        if !matches!(&item.kind, ItemKind::Struct(..)) {
            return;
        }
        let Some(hir_item) = self.ast_to_hir.get_item(item.id, self.tcx) else {
            return;
        };
        let local_def_id = hir_item.owner_id.def_id;
        let Some(derives) = self.derives_by_type.get(&local_def_id) else {
            return;
        };

        let derive_list = derives
            .iter()
            .map(|derive| derive.path())
            .collect::<Vec<_>>()
            .join(", ");
        let mut new_attrs = utils::attr!("#[derive({derive_list})]");
        new_attrs.extend(item.attrs.drain(..));
        item.attrs = new_attrs;
    }
}

impl BytemuckDerive {
    fn path(self) -> &'static str {
        match self {
            Self::Zeroable => "bytemuck::Zeroable",
            Self::AnyBitPattern => "bytemuck::AnyBitPattern",
            Self::NoUninit => "bytemuck::NoUninit",
            Self::Pod => "bytemuck::Pod",
        }
    }
}
