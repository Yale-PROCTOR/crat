//! **A counted `void *` parameter STORED into a local aggregate (R499-1).**
//!
//! json.h's shape: the parameter's only uses are null tests and exactly one
//! cast-store — `state.src = src as *const c_char` — beside a store of the
//! sibling COUNT into a neighbouring field of the same base (`state.size =
//! src_size`). The declaration becomes `Option<&[u8]>` with that sibling as the
//! extent; the store itself keeps its raw form as a bridge, and neither the
//! aggregate nor the count field is converted.
//!
//! **The base must be a LOCAL aggregate.** The bridge hands a raw pointer
//! derived from the borrow to a place, and a place that outlives the call keeps
//! that pointer after the borrow ends — bzip2's `(*bzf).strm.next_out` is
//! exactly that shape, and it is refused here rather than waived: retention
//! past the frame is the seat's ruling to make (R130 tier 2), not this rule's.
use rustc_hir::{
    Expr, ExprKind, Node, PatKind,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{
    Subject, SubjectKind,
    counted_void::{ByteElement, Contract},
    emitability::UseEdit,
};

/// Every mention of `target`, plus the two shapes that disqualify the subject
/// outright: a write to the parameter itself and any closure in the body.
struct Uses<'tcx> {
    target: rustc_hir::HirId,
    found: Vec<&'tcx Expr<'tcx>>,
    stores: Vec<(&'tcx Expr<'tcx>, &'tcx Expr<'tcx>)>,
    writes: bool,
    closures: bool,
}

impl<'tcx> Visitor<'tcx> for Uses<'tcx> {
    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = e.kind
            && path.res == Res::Local(self.target)
        {
            self.found.push(e);
        }
        match e.kind {
            ExprKind::Assign(lhs, rhs, _) => {
                if matches!(lhs.kind, ExprKind::Path(rustc_hir::QPath::Resolved(_, p)) if p.res == Res::Local(self.target))
                {
                    self.writes = true;
                }
                self.stores.push((lhs, rhs));
            }
            ExprKind::AssignOp(_, lhs, _) if matches!(lhs.kind, ExprKind::Path(rustc_hir::QPath::Resolved(_, p)) if p.res == Res::Local(self.target)) =>
            {
                self.writes = true;
            }
            ExprKind::Closure(..) => self.closures = true,
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }
}

/// The local a field place is rooted at, when it is rooted at one: `state.src`
/// yields `state`, `(*bzf).strm.next_out` yields nothing — a deref is where the
/// frame ends.
fn field_base_local(e: &Expr<'_>) -> Option<rustc_hir::HirId> {
    match e.kind {
        ExprKind::Field(base, _) => field_base_local(base),
        ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

/// The local an expression reads, through the casts a count carries
/// (`src_size`, `len as c_uint`).
fn value_local(e: &Expr<'_>) -> Option<rustc_hir::HirId> {
    match e.kind {
        ExprKind::Cast(inner, _) => value_local(inner),
        ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn prove(tcx: TyCtxt<'_>, s: &Subject) -> Option<Contract> {
    if s.ptr_depth != 1 || !matches!(s.kind, SubjectKind::Param { .. }) {
        return None;
    }
    let Node::Pat(pat) = tcx.hir_node(s.hir_id) else { return None };
    if !super::void_pointee::has_void_pointee(tcx, tcx.typeck(s.fn_did).pat_ty(pat), 1) {
        return None;
    }
    let name = s.param_name.as_ref()?;
    let body = tcx.hir_body_owned_by(s.fn_did);
    let mut uses = Uses {
        target: s.hir_id,
        found: Vec::new(),
        stores: Vec::new(),
        writes: false,
        closures: false,
    };
    uses.visit_expr(body.value);
    if uses.writes || uses.closures {
        return None;
    }

    let typeck = tcx.typeck(s.fn_did);
    let sm = tcx.sess.source_map();
    let mut nullable = false;
    let mut edits = Vec::new();
    let mut store: Option<(&Expr<'_>, String)> = None;
    for use_ in &uses.found {
        let Node::Expr(parent) = tcx.parent_hir_node(use_.hir_id) else { return None };
        match parent.kind {
            ExprKind::MethodCall(segment, receiver, [], _)
                if receiver.hir_id == use_.hir_id && segment.ident.name.as_str() == "is_null" =>
            {
                nullable = true;
                edits.push(UseEdit {
                    span: parent.span,
                    replacement: format!("{name}.is_none()"),
                    bridge_kind: "counted-void-null-test",
                });
            }
            ExprKind::Cast(inner, ty) if inner.hir_id == use_.hir_id => {
                // A byte pointee, and SHARED: a `*mut` store hands out a
                // writable alias of the borrow, which is a different rule.
                let TyKind::RawPtr(target, mutability) = typeck.expr_ty(parent).kind() else {
                    return None;
                };
                if !mutability.is_not() {
                    return None;
                }
                match target.kind() {
                    TyKind::Uint(rustc_middle::ty::UintTy::U8)
                    | TyKind::Int(rustc_middle::ty::IntTy::I8) => {}
                    _ => return None,
                }
                let Node::Expr(grand) = tcx.parent_hir_node(parent.hir_id) else { return None };
                let ExprKind::Assign(place, value, _) = grand.kind else { return None };
                if value.hir_id != parent.hir_id || store.is_some() {
                    return None;
                }
                let text = sm.span_to_snippet(ty.span).ok()?;
                store = Some((place, text));
            }
            // Forwarded to a callee: the seam bridges it, and the callee's own
            // contract is what types it.
            ExprKind::Call(_, args) if args.iter().any(|a| a.hir_id == use_.hir_id) => {}
            _ => return None,
        }
    }

    let (place, ptr_text) = store?;
    // The frame test: the store's base is a local aggregate, so the raw pointer
    // the bridge hands over dies with the frame that borrowed it.
    let base = field_base_local(place)?;
    // The count is the sibling parameter stored into a neighbouring field of
    // the SAME base — the pair the C code writes together.
    let mut named: Option<usize> = None;
    let mut ambiguous = false;
    for (lhs, rhs) in &uses.stores {
        if field_base_local(lhs) != Some(base) || lhs.span == place.span {
            continue;
        }
        let Some(local) = value_local(rhs) else { continue };
        if let Some(index) = body
            .params
            .iter()
            .position(|p| matches!(p.pat.kind, PatKind::Binding(_, h, _, _) if h == local))
        {
            match named {
                None => named = Some(index),
                Some(seen) if seen == index => {}
                Some(_) => ambiguous = true,
            }
        }
    }
    let own = body
        .params
        .iter()
        .position(|p| matches!(p.pat.kind, PatKind::Binding(_, h, _, _) if h == s.hir_id))?;
    // **R500-8.** A body that pairs exactly one sibling with the pointer NAMES
    // the count, and that is evidence. Where it names none, or several — json.h
    // stores `src_size` and `flags_bitset` into the same state — the sibling
    // IMMEDIATELY FOLLOWING the pointer is admissible instead, and the receipt
    // calls it what it is: a positional guess, counted with §77's fabricated
    // extents, never as evidence. Only an integer can be a length.
    let (count_index, count_positional) = match named {
        Some(index) if !ambiguous && index != own => (index, None),
        _ => {
            let index = own + 1;
            let param = body.params.get(index)?;
            let PatKind::Binding(_, _, ident, None) = param.pat.kind else { return None };
            match tcx.typeck(s.fn_did).pat_ty(param.pat).kind() {
                TyKind::Uint(_) | TyKind::Int(_) => {}
                _ => return None,
            }
            (index, Some(ident.name.to_string()))
        }
    };

    // The store keeps its raw form: the view lends its pointer and the place
    // takes it exactly as the input wrote it.
    let replacement = if nullable {
        format!(
            "{name}.map_or(0 as {ptr_text}, |__crat_cv_{name}| __crat_cv_{name}.as_ptr() as {ptr_text})"
        )
    } else {
        format!("{name}.as_ptr() as {ptr_text}")
    };
    let Node::Expr(cast) = tcx.parent_hir_node(
        uses.found
            .iter()
            .find(|use_| {
                matches!(tcx.parent_hir_node(use_.hir_id), Node::Expr(p) if matches!(p.kind, ExprKind::Cast(inner, _) if inner.hir_id == use_.hir_id))
            })?
            .hir_id,
    ) else {
        return None;
    };
    edits.push(UseEdit {
        span: cast.span,
        replacement,
        bridge_kind: "counted-void-store-bridge",
    });

    Some(Contract {
        count_index,
        count_positional,
        element: ByteElement::Read,
        nullable,
        width: None,
        alias: None,
        decl: None,
        handle: None,
        uses: edits,
    })
}
