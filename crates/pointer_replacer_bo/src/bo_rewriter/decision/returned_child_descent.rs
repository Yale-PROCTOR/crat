//! W-C5: when no child can descend from an argument.
//!
//! A shared view borrowed into a contract-less local callee that may hand a
//! pointer back is refused `write-through-shared-view` unless the caller's use
//! of what comes back is proven read-only (K18′). Two facts together prove
//! that nothing coming back can descend from THIS argument at all, so the
//! question is moot: the callee's retention summary certifies `NoRetain` for
//! the argument (its value never reaches the return, an out-param or a store —
//! `Return` is a retention event), and the argument's pointee type reaches no
//! pointer (so nothing loaded through it is a pointer either). Then the
//! pointer handed back is another argument's or fresh, and the shared view is
//! never written through it.
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::raw_boundary::RetentionVerdict;

/// Every value reachable from `ty` by value (fields, elements) is a scalar.
pub(crate) fn pointer_free<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    fn walk<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, seen: &mut FxHashSet<Ty<'tcx>>) -> bool {
        if !seen.insert(ty) {
            return true;
        }
        match ty.kind() {
            TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
                true
            }
            TyKind::Array(element, _) => walk(tcx, *element, seen),
            TyKind::Tuple(elements) => elements.iter().all(|element| walk(tcx, element, seen)),
            TyKind::Adt(adt, args) if adt.is_struct() || adt.is_enum() => adt
                .all_fields()
                .all(|field| walk(tcx, field.ty(tcx, args), seen)),
            _ => false,
        }
    }
    walk(tcx, ty, &mut FxHashSet::default())
}

/// The raw-pointer parameters of `function` whose pointee is pointer-free.
pub(crate) fn pointer_free_parameters(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
) -> impl Iterator<Item = usize> {
    let sig = tcx.fn_sig(function).skip_binder().skip_binder();
    sig.inputs()
        .iter()
        .enumerate()
        .filter_map(|(index, ty)| match ty.kind() {
            TyKind::RawPtr(pointee, _) if pointer_free(tcx, *pointee) => Some(index),
            _ => None,
        })
        .collect::<Vec<_>>()
        .into_iter()
}

pub(crate) fn no_child_can_descend(verdict: &RetentionVerdict, pointee_pointer_free: bool) -> bool {
    pointee_pointer_free && matches!(verdict, RetentionVerdict::NoRetain { .. })
}
