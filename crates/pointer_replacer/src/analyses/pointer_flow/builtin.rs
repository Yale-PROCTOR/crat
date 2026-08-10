use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{Body, Operand, Place},
    ty::{self, Ty, TyCtxt},
};
use rustc_span::{def_id::DefId, source_map::Spanned};

use crate::analyses::pointer_flow::{
    collector::operand_place,
    graph::UnknownReason,
    summary::{FunctionSummary, SummaryCompleteness, SummaryFlow, SummarySource},
};

pub(crate) fn call_name(tcx: TyCtxt<'_>, func: &Operand<'_>) -> Option<(DefId, String)> {
    let constant = func.constant()?;
    let ty = constant.ty();
    let ty::TyKind::FnDef(def_id, _) = ty.kind() else {
        return None;
    };
    Some((*def_id, tcx.def_path_str(*def_id)))
}

/// Returns true only for the core/std inherent raw-pointer arithmetic
/// methods. The crate and `::ptr::` path checks keep user-defined functions
/// that merely share these names (common in translated C code, e.g. a free
/// function `add`) from being granted base-preserving semantics.
pub(crate) fn is_pointer_arithmetic(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std")
        && name.contains("::ptr::")
        && matches!(
            name.rsplit("::").next(),
            Some(
                "offset"
                    | "wrapping_offset"
                    | "byte_offset"
                    | "wrapping_byte_offset"
                    | "add"
                    | "wrapping_add"
                    | "sub"
                    | "wrapping_sub"
            )
        )
}

pub(crate) fn is_as_ptr(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std")
        && (name.contains("::slice::") || name.contains("::array::"))
        && matches!(name.rsplit("::").next(), Some("as_ptr" | "as_mut_ptr"))
}

pub(crate) fn call_no_writes(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std")
        && name.contains("::ptr::")
        && matches!(name.rsplit("::").next(), Some("is_null"))
}

pub(crate) fn is_null_ptr_call(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std")
        && matches!(name.rsplit("::").next(), Some("null" | "null_mut"))
}

/// Returns true when `operand` is the integer constant zero, i.e. `0 as *mut T`.
pub(crate) fn is_zero_int_operand<'tcx>(operand: &Operand<'tcx>, _tcx: TyCtxt<'tcx>) -> bool {
    let Some(const_op) = operand.constant() else {
        return false;
    };
    let Some(scalar) = const_op.const_.try_to_scalar() else {
        return false;
    };
    let Ok(int_val) = scalar.try_to_scalar_int() else {
        return false;
    };
    int_val.to_bits(int_val.size()) == 0
}

pub(crate) fn constant_pointer_reason<'tcx>(
    operand: &Operand<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> UnknownReason {
    if is_zero_int_operand(operand, tcx) {
        UnknownReason::NullLike
    } else {
        UnknownReason::ConstantPointer
    }
}

pub(crate) fn builtin_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
    args: &[Spanned<Operand<'tcx>>],
    destination: Place<'tcx>,
    body: &Body<'tcx>,
) -> Option<FunctionSummary> {
    if !tcx.is_foreign_item(def_id) {
        return None;
    }
    let last = name.rsplit("::").next()?;
    let arg0_is_ptr = args
        .first()
        .is_some_and(|arg| arg.node.ty(body, tcx).is_raw_ptr());
    let dst_is_ptr = destination.ty(body, tcx).ty.is_raw_ptr();
    let base_preserving = || FunctionSummary {
        completeness: SummaryCompleteness::Complete,
        return_flows: vec![
            SummaryFlow {
                dst_return_path: vec![],
                src: SummarySource::ParamSlot {
                    arg_index: 0,
                    path: vec![],
                },
            },
            SummaryFlow {
                dst_return_path: vec![],
                src: SummarySource::Unknown(UnknownReason::NullLike),
            },
        ],
        ..FunctionSummary::default()
    };
    let empty_complete = || FunctionSummary {
        completeness: SummaryCompleteness::Complete,
        ..FunctionSummary::default()
    };
    match last {
        // base-preserving, null-on-miss: returns a cursor into arg0 or null.
        "strstr" | "strchr" | "strrchr" | "strpbrk"
            if args.len() == 2 && arg0_is_ptr && dst_is_ptr =>
        {
            Some(base_preserving())
        }
        "memchr" if args.len() == 3 && arg0_is_ptr && dst_is_ptr => Some(base_preserving()),
        // read-only: no pointer return, no pointer-changing arg writes.
        "strlen" if args.len() == 1 && arg0_is_ptr => Some(empty_complete()),
        "strcmp" if args.len() == 2 && arg0_is_ptr => Some(empty_complete()),
        "strncmp" | "memcmp" if args.len() == 3 && arg0_is_ptr => Some(empty_complete()),
        _ => None,
    }
}

pub(crate) fn call_propagates_first_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
    args: &[Spanned<Operand<'tcx>>],
    destination: Place<'tcx>,
    body: &Body<'tcx>,
) -> bool {
    is_from_raw_parts_mut_call(tcx, def_id, name, args, destination, body)
        || is_slice_index_mut_call(tcx, def_id, name, args, destination, body)
}

pub(crate) fn is_from_raw_parts_mut_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
    args: &[Spanned<Operand<'tcx>>],
    destination: Place<'tcx>,
    body: &Body<'tcx>,
) -> bool {
    matches!(name.rsplit("::").next(), Some("from_raw_parts_mut"))
        && is_core_or_std_from_raw_parts_mut_path(tcx, def_id, name)
        && args
            .first()
            .is_some_and(|arg| arg.node.ty(body, tcx).is_raw_ptr())
        && is_mut_slice_ref_ty(destination.ty(body, tcx).ty)
}

pub(crate) fn is_slice_index_mut_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
    args: &[Spanned<Operand<'tcx>>],
    destination: Place<'tcx>,
    body: &Body<'tcx>,
) -> bool {
    matches!(name.rsplit("::").next(), Some("index_mut"))
        && is_core_or_std_slice_index_mut_path(tcx, def_id, name)
        && args
            .first()
            .and_then(|arg| operand_place(&arg.node))
            .is_some_and(|place| is_mut_slice_ref_ty(place.ty(body, tcx).ty))
        && is_mut_slice_ref_ty(destination.ty(body, tcx).ty)
}

pub(crate) fn is_core_or_std_from_raw_parts_mut_path(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    name: &str,
) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std")
        && name.contains("::slice::")
        && name.ends_with("::from_raw_parts_mut")
}

pub(crate) fn is_core_or_std_slice_index_mut_path(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    name: &str,
) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    matches!(crate_name.as_str(), "core" | "std") && name.ends_with("::ops::IndexMut::index_mut")
}

pub(crate) fn is_mut_slice_ref_ty(ty: Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::Ref(_, inner_ty, mutability)
            if mutability.is_mut() && matches!(inner_ty.kind(), ty::TyKind::Slice(_))
    )
}

pub(crate) fn is_empty_array_ref_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let ty::TyKind::Ref(_, inner_ty, _) = ty.kind() else {
        return false;
    };
    let ty::TyKind::Array(_, len) = inner_ty.kind() else {
        return false;
    };
    len.try_to_target_usize(tcx) == Some(0)
}

/// Returns true for allocator shims found by Andersen pre-analysis and for
/// the foreign libc allocators. A local Rust function that merely shares an
/// allocator name gets no heap-alloc provenance.
pub(crate) fn is_heap_alloc_call(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    alloc_fns: &FxHashSet<LocalDefId>,
) -> bool {
    def_id
        .as_local()
        .is_some_and(|local_def_id| alloc_fns.contains(&local_def_id))
        || tcx.is_foreign_item(def_id)
            && matches!(
                tcx.item_name(def_id).as_str(),
                "malloc" | "calloc" | "realloc"
            )
}
