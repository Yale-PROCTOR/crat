use std::ops::ControlFlow;

use rustc_middle::{
    query::IntoQueryParam,
    ty::{Ty, TyCtxt, TyKind, TypeVisitor},
};
use rustc_span::def_id::DefId;
use rustc_type_ir::{TypeSuperVisitable as _, TypeVisitable as _};

#[inline]
pub fn is_file_ty(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> bool {
    crate::ir::def_id_to_symbol(id, tcx).is_some_and(|name| name.as_str() == "_IO_FILE")
}

#[inline]
pub fn is_file_ptr<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let (TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _)) = ty.kind() else { return false };
    let TyKind::Adt(adt_def, _) = ty.kind() else { return false };
    is_file_ty(adt_def.did(), tcx)
}

#[inline]
pub fn is_file_ptr_ptr<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let (TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _)) = ty.kind() else { return false };
    is_file_ptr(*ty, tcx)
}

#[inline]
pub fn contains_file_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let mut visitor = FileTypeVisitor { tcx };
    ty.visit_with(&mut visitor).is_break()
}

struct FileTypeVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for FileTypeVisitor<'tcx> {
    type Result = ControlFlow<()>;

    fn visit_ty(&mut self, t: Ty<'tcx>) -> Self::Result {
        if let TyKind::Adt(adt_def, _) = t.kind()
            && is_file_ty(adt_def.did(), self.tcx)
        {
            return ControlFlow::Break(());
        }
        t.super_visit_with(self)
    }
}

pub fn file_param_index<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<usize> {
    match ty.kind() {
        TyKind::Adt(adt_def, targs) => {
            if crate::ir::is_option(adt_def.did(), tcx) {
                let targs = targs.into_type_list(tcx);
                file_param_index(targs[0], tcx)
            } else {
                None
            }
        }
        TyKind::FnPtr(binder, _) => binder
            .as_ref()
            .skip_binder()
            .inputs()
            .iter()
            .enumerate()
            .find_map(|(i, ty)| if is_file_ptr(*ty, tcx) { Some(i) } else { None }),
        _ => None,
    }
}

pub mod api_list;
