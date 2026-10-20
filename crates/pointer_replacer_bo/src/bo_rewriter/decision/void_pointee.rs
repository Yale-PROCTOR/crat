//! Void-pointee slots (seat ruling R271-1).
//!
//! `core::ffi::c_void` is `#[repr(u8)]` with two hidden variants, so it is a
//! ONE-BYTE type and a reference to it carries one byte of provenance. A
//! `c_void` pointer in C2Rust output is an opaque byte address: the callee's
//! first act is invariably to cast it to the type it actually wants and access
//! at that width. Miri confirms the emitted `&c_void` form is UB under Stacked
//! Borrows at the second byte read.
//!
//! No reference form of `c_void` can carry the right provenance — the pointee
//! type has no extent to carry — so this is not a bridge or carrier problem and
//! cannot be fixed downstream of the decision. The slot is held.
//!
//! The caller end of each `x as *const c_void` edge is what makes this a repair
//! rather than a pure loss: with the callee's parameter no longer converting,
//! the caller leaves the `CastOfConvertingLocal`/`ArgCastFormUnbuilt` pair and
//! takes the ordinary raw-boundary bridge, whose pointer carries the caller
//! subject's own full extent.

use rustc_hash::FxHashSet;
use rustc_hir::{HirId, Node, def_id::LocalDefId};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::Subject;

/// How many pointer hops are followed before conceding. Depth-2 out-parameters
/// (`*mut *mut c_void`) need two; the budget bounds pathological nesting.
pub(crate) const VOID_POINTEE_DEPTH: u32 = 6;

/// Is this exactly `core::ffi::c_void`? Matched through the lang item, as
/// `declaration::definition_path_is_accessible` does, so an alias spelling
/// (`libc::c_void`, `std::ffi::c_void`) resolves to the same definition.
fn is_c_void(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Adt(definition, _)
        if tcx.lang_items().c_void() == Some(definition.did()))
}

/// Does any pointer or reference layer of this slot point at `c_void`?
///
/// The walk follows the slot's own pointer chain and nothing else: a struct
/// that merely CONTAINS a `*mut c_void` field is not held by this rule, because
/// that field is its own slot and is held on its own account.
pub(crate) fn has_void_pointee<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: u32) -> bool {
    if depth == 0 {
        return false;
    }
    match ty.kind() {
        TyKind::RawPtr(pointee, _) | TyKind::Ref(_, pointee, _) => {
            is_c_void(tcx, *pointee) || has_void_pointee(tcx, *pointee, depth - 1)
        }
        _ => false,
    }
}

/// The element spelling a `c_void` pointee takes in a SAFE emitted form
/// (wave-6b, R447-4): **`u8`**.
///
/// The header's reasoning, carried one step further. `c_void` is a one-byte
/// type with two hidden variants, so `&c_void` / `&[c_void]` carries a byte of
/// provenance and no usable value — and every family that DOES deliver a void
/// buffer safely already spells its element `u8` (this lane's typed regions and
/// byte views, the counted-void copies' `u8` / `MaybeUninit<u8>`). A producer
/// that instead spells the element from the DECLARED pointee emits `[c_void]`
/// against those neighbours' `[u8]`, and the two are different types: the
/// emitted crate stops compiling at the seam even though both sides are the
/// same form. One spelling, chosen once, here.
///
/// Raw forms are untouched: `*mut c_void` is the C interface's own type and
/// every bridge that reaches one casts to it explicitly.
pub(crate) fn byte_element(pointee: &str) -> &str {
    const VOID: [&str; 6] = [
        "c_void",
        "core::ffi::c_void",
        "::core::ffi::c_void",
        "std::ffi::c_void",
        "libc::c_void",
        "::libc::c_void",
    ];
    if VOID.contains(&pointee.trim()) {
        "u8"
    } else {
        pointee
    }
}

/// Every subject whose declared type has a `c_void` pointee at any depth.
pub(crate) fn collect(tcx: TyCtxt<'_>, subjects: &[Subject]) -> FxHashSet<(LocalDefId, HirId)> {
    let mut held = FxHashSet::default();
    for subject in subjects {
        let Node::Pat(pattern) = tcx.hir_node(subject.hir_id) else { continue };
        let ty = tcx.typeck(subject.fn_did).pat_ty(pattern);
        if has_void_pointee(tcx, ty, VOID_POINTEE_DEPTH) {
            held.insert((subject.fn_did, subject.hir_id));
        }
    }
    held
}
