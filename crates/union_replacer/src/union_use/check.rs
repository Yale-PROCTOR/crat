use rustc_abi::Size;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, TypeVisitableExt};
use rustc_span::def_id::{DefId, LocalDefId};

// This module recreates the bytemuck 1.24.x derive rules
// Assume AnyBitPattern + NoUninit = Pod, which is a stricter requirement than bytemuck's actual Pod.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldTypeClass {
    AnyBitPattern,
    NoUninit,
    Pod,
    Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DerivedMarker {
    NoUninit,
    AnyBitPattern,
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
            (false, true) => FieldTypeClass::NoUninit,
            (false, false) => FieldTypeClass::Other,
        }
    }

    fn primitive_class(ty: Ty<'tcx>) -> Option<FieldTypeClass> {
        match ty.kind() {
            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => Some(FieldTypeClass::Pod),
            TyKind::RawPtr(..) | TyKind::Char | TyKind::Bool => Some(FieldTypeClass::NoUninit),
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
