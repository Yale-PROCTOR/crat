//! Realize shared permission for original field borrows between shared subjects.

use rustc_ast::mut_visit::MutVisitor;
use rustc_hir::{
    BorrowKind, Expr, ExprKind, HirId, Mutability, QPath, UnOp,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::{
    ast_transform::{Composition, RevertSet},
    decision::{Decision, DecisionTable, SubjectKind},
};

fn shared(decision: &Decision) -> bool {
    match decision {
        Decision::Ref { mutable } => !mutable,
        Decision::InferredRef { .. }
        | Decision::Cursor { .. }
        | Decision::NestedSlice { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Degraded(_) => false,
    }
}

/// Side-effect-free field place under exactly one dereference.
fn root(expr: &Expr<'_>, dereferenced: bool) -> Option<HirId> {
    match expr.kind {
        ExprKind::Field(base, _) => root(base, dereferenced),
        ExprKind::Unary(UnOp::Deref, base) if !dereferenced => root(base, true),
        ExprKind::Path(QPath::Resolved(_, path)) if dereferenced => match path.res {
            Res::Local(binding) => Some(binding),
            _ => None,
        },
        _ => None,
    }
}

/// This is a final-tree syntax repair, not a new seam or permission grant.
/// Reverted subjects and callees retain their original argument expression.
pub(super) fn apply(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    reverts: &RevertSet,
    krate: &mut rustc_ast::Crate,
    guard: &mut Composition,
) -> Result<(), String> {
    struct Calls<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        table: &'a DecisionTable,
        reverts: &'a RevertSet,
        owner: LocalDefId,
        sites: &'a mut rustc_hash::FxHashMap<Span, Span>,
    }
    impl<'tcx> Visitor<'tcx> for Calls<'_, 'tcx> {
        fn visit_expr(&mut self, call: &'tcx Expr<'tcx>) {
            intravisit::walk_expr(self, call);
            let ExprKind::Call(callee, args) = call.kind else { return };
            let ExprKind::Path(ref path) = callee.kind else { return };
            let Res::Def(_, did) = self.tcx.typeck(self.owner).qpath_res(path, callee.hir_id)
            else {
                return;
            };
            let Some(callee) = did.as_local() else { return };
            for (index, arg) in args.iter().enumerate() {
                let ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, place) = arg.kind else {
                    continue;
                };
                if !matches!(place.kind, ExprKind::Field(..)) {
                    continue;
                }
                let Some(binding) = root(place, false) else { continue };
                let source_shared = self.table.entries.iter().any(|(s, d)| {
                    s.fn_did == self.owner
                        && s.hir_id == binding
                        && shared(d)
                        && self.reverts.keeps_subject(s.fn_did, s.hir_id)
                });
                let target_shared = self.table.entries.iter().any(|(s, d)| {
                    s.fn_did == callee
                        && matches!(s.kind, SubjectKind::Param { hir_index } if hir_index == index)
                        && shared(d)
                        && self.reverts.keeps_subject(s.fn_did, s.hir_id)
                });
                if source_shared && target_shared {
                    self.sites.insert(arg.span, place.span);
                }
            }
        }
    }
    let mut sites = rustc_hash::FxHashMap::default();
    let mut owners = rustc_hash::FxHashSet::default();
    for (subject, _) in &table.entries {
        if owners.insert(subject.fn_did)
            && let Some(body) = tcx.hir_node_by_def_id(subject.fn_did).body_id()
        {
            Calls {
                tcx,
                table,
                reverts,
                owner: subject.fn_did,
                sites: &mut sites,
            }
            .visit_body(tcx.hir_body(body));
        }
    }
    struct Apply<'a> {
        sites: &'a rustc_hash::FxHashMap<Span, Span>,
        guard: &'a mut Composition,
        collision: bool,
    }
    impl MutVisitor for Apply<'_> {
        fn visit_expr(&mut self, expr: &mut rustc_ast::Expr) {
            rustc_ast::mut_visit::walk_expr(self, expr);
            let Some(&place_span) = self.sites.get(&expr.span) else { return };
            let rustc_ast::ExprKind::AddrOf(rustc_ast::BorrowKind::Ref, permission, place) =
                &mut expr.kind
            else {
                return;
            };
            if *permission != rustc_ast::Mutability::Mut || place.span != place_span {
                return;
            }
            if !self.guard.claim(expr.id, expr.span, "shared-field-borrow") {
                self.collision = true;
                return;
            }
            *permission = rustc_ast::Mutability::Not;
        }
    }
    let mut apply = Apply {
        sites: &sites,
        guard,
        collision: false,
    };
    apply.visit_crate(krate);
    if apply.collision {
        Err("shared-field-borrow-collision".into())
    } else {
        Ok(())
    }
}
