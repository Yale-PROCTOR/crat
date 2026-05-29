use std::{fs, path::Path, str::FromStr};

use rustc_abi::Size;
use rustc_ast::{
    Item, ItemKind,
    mut_visit::{self, MutVisitor},
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, TypeVisitableExt};
use rustc_span::def_id::{DefId, LocalDefId};
use toml_edit::{DocumentMut, Item as TomlItem, Table};

use crate::ir::AstToHir;

// This module recreates the bytemuck 1.24.x derive rules.
// It assumes AnyBitPattern + NoUninit = Pod, which is stricter than bytemuck's actual Pod.

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BytemuckRequirement {
    NoUninit,
    AnyBitPattern,
    Pod,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DerivedMarker {
    NoUninit,
    AnyBitPattern,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

impl BytemuckDerivePlan {
    pub fn is_empty(&self) -> bool {
        self.per_type.is_empty()
    }

    pub fn collect_from_ty<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        classifier: &mut BytemuckTypeClassifier<'tcx>,
        ty: Ty<'tcx>,
    ) {
        let mut visited_tys = FxHashSet::default();
        self.collect_from_ty_inner(tcx, classifier, ty, &mut visited_tys);
    }

    pub fn require_type<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        classifier: &mut BytemuckTypeClassifier<'tcx>,
        ty: Ty<'tcx>,
        requirement: BytemuckRequirement,
    ) -> bool {
        if !classifier.satisfies_requirement(ty, requirement) {
            return false;
        }
        let mut visited_tys = FxHashSet::default();
        self.collect_requirement_from_ty(tcx, classifier, ty, requirement, &mut visited_tys);
        true
    }

    fn collect_from_ty_inner<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        classifier: &mut BytemuckTypeClassifier<'tcx>,
        ty: Ty<'tcx>,
        visited_tys: &mut FxHashSet<Ty<'tcx>>,
    ) {
        if !visited_tys.insert(ty) {
            return;
        }

        match ty.kind() {
            TyKind::Array(elem, _) => {
                self.collect_from_ty_inner(tcx, classifier, *elem, visited_tys)
            }
            TyKind::Adt(adt, args) if adt.is_struct() => {
                let Some(local_def_id) = adt.did().as_local() else {
                    return;
                };
                let derives = classifier.derive_markers_for_type(ty);

                if !derives.is_empty() {
                    self.per_type
                        .entry(local_def_id)
                        .or_default()
                        .extend(derives);
                }

                for field in adt.all_fields() {
                    self.collect_from_ty_inner(tcx, classifier, field.ty(tcx, args), visited_tys);
                }
            }
            _ => {}
        }
    }

    fn collect_requirement_from_ty<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        classifier: &mut BytemuckTypeClassifier<'tcx>,
        ty: Ty<'tcx>,
        requirement: BytemuckRequirement,
        visited_tys: &mut FxHashSet<Ty<'tcx>>,
    ) {
        if !visited_tys.insert(ty) {
            return;
        }

        match ty.kind() {
            TyKind::Array(elem, _) => {
                self.collect_requirement_from_ty(tcx, classifier, *elem, requirement, visited_tys)
            }
            TyKind::Adt(adt, args) if adt.is_struct() => {
                let Some(local_def_id) = adt.did().as_local() else {
                    return;
                };
                self.per_type
                    .entry(local_def_id)
                    .or_default()
                    .extend(classifier.derives_for_requirement(ty, requirement));

                for field in adt.all_fields() {
                    self.collect_requirement_from_ty(
                        tcx,
                        classifier,
                        field.ty(tcx, args),
                        requirement,
                        visited_tys,
                    );
                }
            }
            _ => {}
        }
    }
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

    pub fn satisfies_requirement(
        &mut self,
        ty: Ty<'tcx>,
        requirement: BytemuckRequirement,
    ) -> bool {
        match requirement {
            BytemuckRequirement::NoUninit => self.is_derivable(ty, DerivedMarker::NoUninit),
            BytemuckRequirement::AnyBitPattern => {
                self.is_derivable(ty, DerivedMarker::AnyBitPattern)
            }
            BytemuckRequirement::Pod => {
                self.is_derivable(ty, DerivedMarker::AnyBitPattern)
                    && self.is_derivable(ty, DerivedMarker::NoUninit)
            }
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

    fn derives_for_requirement(
        &mut self,
        ty: Ty<'tcx>,
        requirement: BytemuckRequirement,
    ) -> FxHashSet<BytemuckDerive> {
        let mut derives = FxHashSet::default();
        if !self.satisfies_requirement(ty, requirement) {
            return derives;
        }
        match requirement {
            BytemuckRequirement::NoUninit => {
                derives.insert(BytemuckDerive::NoUninit);
            }
            BytemuckRequirement::AnyBitPattern => {
                derives.insert(BytemuckDerive::AnyBitPattern);
            }
            BytemuckRequirement::Pod => {
                derives.insert(BytemuckDerive::Zeroable);
                derives.insert(BytemuckDerive::Pod);
            }
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
                let mut derives = derives.into_iter().collect::<Vec<_>>();
                derives.sort();
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
        let mut new_attrs = crate::attr!("#[derive({derive_list})]");
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

pub fn ensure_bytemuck_with_derive(dir: &Path) {
    let path = dir.join("Cargo.toml");
    let content = fs::read_to_string(&path).unwrap();
    let mut doc = content.parse::<DocumentMut>().unwrap();

    if !doc.as_table().contains_key("dependencies") {
        doc["dependencies"] = TomlItem::Table(Table::new());
    }

    let deps = doc["dependencies"].as_table_mut().unwrap();
    deps["bytemuck"] = TomlItem::from_str(
        r#"{ version = "1.24.0", features = ["derive", "min_const_generics", "must_cast"] }"#,
    )
    .unwrap();

    fs::write(path, doc.to_string()).unwrap();
}
