//! **Relay 371 step 3 (main 254 §1 (a), §2) — the identity-cast strip.**
//!
//! A call argument `q as *mut T` / `&mut e as *mut T` whose cast keeps the pointee — the operand's
//! and the target's pointee are equal as `Ty` after typeck, so typedefs are already resolved
//! (`kat_tr_ctx = blakestate256`, `uint8_t = c_uchar`) — is the argument itself. The class gate takes
//! it as it takes the bare argument: a class edge where both ends convert, the existing raw-boundary
//! bridge over the operand where the binding stays raw. The seam renders the operand without the cast.
//!
//! Refused here, and so still held by the cast form: a retyping cast (the pointee changes: A4's
//! one-type `void *` view, or a byte view); a depth-2 cast (`*mut *mut T`, the out-parameter form);
//! and `*const T as *mut T` into a formal its callee writes. The prefix / layout rule (a different
//! `repr(C)` type with the same leading fields) is not built: 0 of the 224 A2 rows needed it.

use rustc_hir::{Expr, ExprKind, def_id::LocalDefId};
use rustc_middle::ty::{TyCtxt, TyKind};

/// The fact, read where the argument is collected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IdentityCast {
    /// `*const T as *mut T` (or `&e as *mut T`): admitted only into a formal its callee never writes.
    pub(crate) strengthens: bool,
    /// The operand's type and the cast's, as rendered, for the receipt.
    pub(crate) from: String,
    pub(crate) to: String,
}

/// `arg` is a cast chain whose every link keeps the operand's pointee, which is not itself a pointer.
pub(crate) fn of<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    arg: &'tcx Expr<'tcx>,
) -> Option<IdentityCast> {
    if !matches!(arg.kind, ExprKind::Cast(..)) {
        return None;
    }
    let typeck = tcx.typeck(owner);
    let TyKind::RawPtr(target, target_mutability) = *typeck.expr_ty(arg).kind() else {
        return None;
    };
    if matches!(target.kind(), TyKind::RawPtr(..) | TyKind::Ref(..)) {
        return None;
    }
    let mut inner = arg;
    while let ExprKind::Cast(operand, _) = inner.kind {
        inner = operand;
        if matches!(inner.kind, ExprKind::Cast(..)) {
            let TyKind::RawPtr(link, _) = *typeck.expr_ty(inner).kind() else {
                return None;
            };
            if link != target {
                return None;
            }
        }
    }
    let operand_ty = typeck.expr_ty(inner);
    let (source, source_mutability) = match *operand_ty.kind() {
        TyKind::RawPtr(source, mutability) | TyKind::Ref(_, source, mutability) => {
            (source, mutability)
        }
        _ => return None,
    };
    (source == target).then(|| IdentityCast {
        strengthens: source_mutability.is_not() && target_mutability.is_mut(),
        from: operand_ty.to_string(),
        to: typeck.expr_ty(arg).to_string(),
    })
}

/// The gate's rule: an identity cast is the argument itself, except a strengthening one into a
/// written formal.
pub(crate) fn admitted(cast: &IdentityCast, formal_written: bool) -> bool {
    !cast.strengthens || !formal_written
}

/// **The strip's receipt** (relay 371 step 3): one row per identity-cast argument whose callee
/// formal the table decides in a safe form — the site the seam rendered without its cast — with the
/// caller, the callee and position, the site, `<from> → <to>`, and both ends' decisions. Whether the
/// two delivered is `subjects.tsv`'s outcome.
pub(crate) fn receipts_tsv(
    tcx: TyCtxt<'_>,
    facts: &super::emitability::EmitabilityFacts,
    table: &super::DecisionTable,
) -> String {
    let decision = |key: (LocalDefId, rustc_hir::HirId)| {
        table
            .entries
            .iter()
            .find(|(subject, _)| (subject.fn_did, subject.hir_id) == key)
            .map(|(_, decision)| decision)
    };
    let form = |decision: Option<&super::Decision>| match decision {
        None => "-",
        Some(super::Decision::Ref { .. }) | Some(super::Decision::InferredRef { .. }) => "ref",
        Some(super::Decision::Slice { .. }) => "slice",
        Some(super::Decision::NestedSlice { .. }) => "nested-slice",
        Some(super::Decision::Opt { .. }) => "opt",
        Some(super::Decision::Box(_)) => "box",
        Some(super::Decision::Cursor { .. }) => "cursor",
        Some(super::Decision::Degraded(_)) => "degraded",
    };
    let formal = |callee: LocalDefId, index: usize| {
        table.entries.iter().find(|(subject, _)| {
            subject.fn_did == callee
                && matches!(subject.kind, super::SubjectKind::Param { hir_index } if hir_index == index)
        })
    };
    let mut rows = Vec::new();
    for (callee, sites) in &facts.call_args {
        for site in sites {
            for arg in &site.args {
                let Some(cast) = &arg.identity_cast else { continue };
                let Some((_, formal_decision)) = formal(*callee, arg.index) else {
                    continue;
                };
                let callee_form = form(Some(formal_decision));
                if matches!(callee_form, "degraded" | "-") {
                    continue;
                }
                let caller_form = match arg.shape {
                    super::emitability::ArgShape::CastOfLocal { binding, .. } => {
                        form(decision((site.caller, binding)))
                    }
                    _ => "-",
                };
                rows.push(format!(
                    "{}\t{}#{}\t{}\t{} -> {}\t{}\t{caller_form}\t{callee_form}\n",
                    tcx.def_path_str(site.caller.to_def_id()),
                    tcx.def_path_str(callee.to_def_id()),
                    arg.index,
                    super::emitability::EmitabilityFacts::site(tcx, arg.span),
                    cast.from,
                    cast.to,
                    if cast.strengthens { "strengthens" } else { "-" },
                ));
            }
        }
    }
    rows.sort();
    let mut out =
        String::from("caller\tcallee_position\tsite\tcast\tmutability\tcaller_form\tcallee_form\n");
    out.extend(rows);
    out
}
