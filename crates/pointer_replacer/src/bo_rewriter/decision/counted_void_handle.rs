//! A `void *` HANDLE to one struct: the parameter is cast to `*mut T` /
//! `*const T` (one `T`, an ADT) and every cast is dereferenced as a single
//! element — never offset, indexed, stored or compared. The declaration becomes
//! `&mut T` / `&T`; the body stays as written, since `&mut T as *mut T` is a
//! legal cast; a raw argument bridges to it at the call, and a raw callee that
//! receives it takes the ordinary safe-to-raw bridge.
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

pub(super) fn prove(tcx: TyCtxt<'_>, s: &Subject) -> Option<Contract> {
    if s.ptr_depth != 1 || !matches!(s.kind, SubjectKind::Param { .. }) {
        return None;
    }
    let Node::Pat(pat) = tcx.hir_node(s.hir_id) else { return None };
    if !super::void_pointee::has_void_pointee(tcx, tcx.typeck(s.fn_did).pat_ty(pat), 1) {
        return None;
    }
    struct Uses<'tcx> {
        target: rustc_hir::HirId,
        found: Vec<&'tcx Expr<'tcx>>,
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
                ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _) if matches!(lhs.kind, ExprKind::Path(rustc_hir::QPath::Resolved(_, p)) if p.res == Res::Local(self.target)) =>
                {
                    self.writes = true;
                }
                ExprKind::Closure(..) => self.closures = true,
                _ => {}
            }
            intravisit::walk_expr(self, e);
        }
    }
    let body = tcx.hir_body_owned_by(s.fn_did);
    let mut uses = Uses {
        target: s.hir_id,
        found: Vec::new(),
        writes: false,
        closures: false,
    };
    uses.visit_expr(body.value);
    if uses.writes || uses.closures {
        return None;
    }
    let name = s.param_name.as_ref()?;
    let typeck = tcx.typeck(s.fn_did);
    let sm = tcx.sess.source_map();
    let mut pointee: Option<(rustc_middle::ty::Ty<'_>, String)> = None;
    let mut casts = 0usize;
    let mut nullable = false;
    let mut edits = Vec::new();
    for use_ in uses.found {
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
                let TyKind::RawPtr(target, _) = typeck.expr_ty(parent).kind() else {
                    return None;
                };
                if !matches!(target.kind(), TyKind::Adt(..)) {
                    return None;
                }
                let rustc_hir::TyKind::Ptr(mut_ty) = ty.kind else { return None };
                let text = sm.span_to_snippet(mut_ty.ty.span).ok()?;
                match &pointee {
                    None => pointee = Some((*target, text)),
                    Some((seen, _)) if *seen == *target => {}
                    Some(_) => return None,
                }
                // The cast is dereferenced directly, as one element.
                let Node::Expr(grand) = tcx.parent_hir_node(parent.hir_id) else { return None };
                if !matches!(grand.kind, ExprKind::Unary(rustc_hir::UnOp::Deref, _)) {
                    return None;
                }
                casts += 1;
            }
            // Forwarded to a callee: the seam bridges it.
            ExprKind::Call(_, args) if args.iter().any(|a| a.hir_id == use_.hir_id) => {}
            _ => return None,
        }
    }
    if casts == 0 {
        return None;
    }
    let (_, text) = pointee?;
    Some(Contract {
        count_index: usize::MAX,
        element: ByteElement::Read,
        nullable,
        // wave-6v2 typed-width table (ec0e694a): not a width-fixed view.
        width: None,
        alias: None,
        decl: None,
        handle: Some(text),
        uses: edits,
    })
}
