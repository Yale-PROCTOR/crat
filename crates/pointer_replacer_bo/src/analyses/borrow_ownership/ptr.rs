use rustc_middle::ty::{AdtDef, Ty, TyKind};

use super::Precision;

pub type Measure = u32;

pub trait Measurable<'tcx> {
    #[inline]
    fn contains_ptr(&self, ty: Ty) -> bool {
        // self.measure(ty, 0) > 0
        self.measure(ty, 0) > 0
    }

    #[inline]
    fn measure_ptr(&self, ty: Ty) -> Measure {
        let (ptr_measure, base) = decompose_ty(ty);
        ptr_measure
            + match base.kind() {
                TyKind::Tuple(elements) => elements.iter().map(|ty| self.measure_ptr(ty)).sum(),
                _ => 0,
            }
    }

    fn measure(&self, ty: Ty, ptr_chased: u32) -> Measure;

    fn measure_adt(&self, adt_def: AdtDef, ptr_chased: u32) -> Measure;

    fn field_offset(&self, ty: Ty, field: usize, ptr_chased: u32) -> Measure;

    fn field_measure(&self, ty: Ty, field: usize, ptr_chased: u32) -> Measure {
        self.field_offset(ty, field + 1, ptr_chased) - self.field_offset(ty, field, ptr_chased)
    }

    fn leaf_nodes(&self, adt_def: AdtDef, ptr_chased: u32) -> &[(Ty<'tcx>, u32)];

    fn extension_leaves(&self, ty: Ty<'tcx>, ptr_chased: u32) -> Vec<(Ty<'tcx>, u32)> {
        let available = (self.max_ptr_chased() as u32).saturating_sub(ptr_chased);
        let (depth, base) = decompose_ty(ty);
        if depth >= available {
            return vec![(peel_pointers(ty, available), available)];
        }
        match base.kind() {
            TyKind::Adt(adt, _) => self
                .leaf_nodes(*adt, ptr_chased + depth)
                .iter()
                .map(|&(ty, offset)| (ty, offset + depth))
                .collect(),
            TyKind::Tuple(elements) => {
                let mut leaves = Vec::new();
                let mut offset = depth;
                for ty in elements.iter() {
                    leaves.extend(
                        self.extension_leaves(ty, ptr_chased + depth)
                            .into_iter()
                            .map(|(ty, inner)| (ty, offset + inner)),
                    );
                    offset += self.measure(ty, ptr_chased + depth);
                }
                leaves
            }
            _ => Vec::new(),
        }
    }

    fn max_ptr_chased(&self) -> Precision;

    fn absolute_precision(&self, ty: Ty, measure: Measure) -> Precision;
}

impl<'tcx, M: Measurable<'tcx>> Measurable<'tcx> for &M {
    #[inline]
    fn measure(&self, ty: Ty, ptr_chased: u32) -> Measure {
        (*self).measure(ty, ptr_chased)
    }

    #[inline]
    fn measure_adt(&self, adt_def: AdtDef, ptr_chased: u32) -> Measure {
        (*self).measure_adt(adt_def, ptr_chased)
    }

    #[inline]
    fn field_offset(&self, ty: Ty, field: usize, ptr_chased: u32) -> Measure {
        (*self).field_offset(ty, field, ptr_chased)
    }

    #[inline]
    fn max_ptr_chased(&self) -> Precision {
        (*self).max_ptr_chased()
    }

    fn leaf_nodes(&self, adt_def: AdtDef, ptr_chased: u32) -> &[(Ty<'tcx>, u32)] {
        (*self).leaf_nodes(adt_def, ptr_chased)
    }

    fn absolute_precision(&self, ty: Ty, measure: Measure) -> Precision {
        (*self).absolute_precision(ty, measure)
    }
}

#[inline]
pub fn decompose_ty(ty: Ty) -> (Measure, Ty) {
    let mut ty = ty;

    let mut ptr_measure = 0;
    loop {
        if let Some(inner_ty) = ty.builtin_index() {
            ty = inner_ty;
            continue;
        }

        if let Some(ty_mut) = ty.builtin_deref(true) {
            ty = ty_mut;
            ptr_measure += 1;
            continue;
        }

        break;
    }

    (ptr_measure, ty)
}

pub(super) fn peel_pointers(mut ty: Ty<'_>, depth: u32) -> Ty<'_> {
    for _ in 0..depth {
        while let Some(element) = ty.builtin_index() {
            ty = element;
        }
        ty = ty.builtin_deref(true).unwrap();
    }
    ty
}
