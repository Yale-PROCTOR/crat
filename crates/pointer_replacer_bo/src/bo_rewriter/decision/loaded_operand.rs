//! **R838 (era-5c 148) — origin evidence over a value loaded from memory.**
//!
//! A5's origin evidence calls the origin of a value loaded from memory (a
//! static's contents, a pointee through any pointer) complete and private, so
//! two such loads always read as disjoint origins, whatever other bodies stored
//! there; `classify_pair` takes origins OR points-to, so that evidence wins
//! even where the points-to sets overlap. The analyses tree does not say which
//! evidence proved a pair, so the pair pass does not take the classifier's
//! proof where an operand is loaded from memory: such a pair is not shown
//! disjoint (R833-1).

use rustc_hir::{
    Expr, ExprKind, HirId, Node, PatKind, QPath, def::Res, def_id::LocalDefId, intravisit::Visitor,
};
use rustc_middle::ty::TyCtxt;

use super::{
    a5_site_proof::{A5PeerProof, A5SiteProofVerdict},
    emitability::CallSite,
};

/// The reason a corrected proof carries.
pub(crate) const REASON: &str = "a5-proof-over-a-loaded-operand";

/// The proof at `site` for `left` / `right`, read with the correction.
pub(crate) fn read_loaded_operands(
    site: &CallSite,
    callee: LocalDefId,
    left: usize,
    right: usize,
    proof: &mut A5PeerProof,
    no_retention: impl Fn(LocalDefId, usize) -> bool,
) {
    if proof.verdict != A5SiteProofVerdict::Clear || proof.reason != "a5-proven-disjoint" {
        return;
    }
    let argument = |index: usize| site.args.iter().find(|argument| argument.index == index);
    let loaded = |index: usize| argument(index).is_some_and(|argument| argument.loaded_from_memory);
    // A pointer loaded from memory cannot hold an address no pointer held
    // before the call: the address of a scalar local taken only by this
    // argument, at a call no loop repeats (the independent review, R820-2:
    // the retention rows do not see every store, so the body alone decides
    // that) - and, as relay 180 item 4 asks, handed to a callee that carries
    // the no-retention certificate for it.
    let unescaped = |index: usize| {
        argument(index).is_some_and(|argument| argument.address_once_here)
            && no_retention(callee, index)
    };
    if (loaded(left) && unescaped(right)) || (loaded(right) && unescaped(left)) {
        return;
    }
    if loaded(left) || loaded(right) {
        proof.verdict = A5SiteProofVerdict::Overlapping;
        proof.reason = REASON;
        proof.family = "not-shown-disjoint";
    }
}

/// Is `borrow` (an `&` / `&mut` / `&raw` of the scalar local `local`) the
/// only place `owner`'s body takes `local`'s address, outside any loop?
/// Then no pointer anywhere holds that address when the call `borrow` is an
/// argument of evaluates its arguments. Any other way of taking a scalar's
/// address counts: another borrow, a `ref` binding (`let`, `if let`, a match
/// arm), an auto-referenced method receiver; a body with a closure, which can
/// capture it by reference, is never read so.
pub(crate) fn address_taken_once_here(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    local: HirId,
    borrow: HirId,
) -> bool {
    let typeck = tcx.typeck(owner);
    if !typeck.node_type(local).is_scalar() {
        return false;
    }
    struct Uses<'a, 'tcx> {
        typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
        local: HirId,
        borrows: Vec<Option<HirId>>,
        closure: bool,
    }
    fn is_local(expr: &Expr<'_>, local: HirId) -> bool {
        matches!(expr.kind, ExprKind::Path(QPath::Resolved(None, path)) if path.res == Res::Local(local))
    }
    fn binds_by_ref(pat: &rustc_hir::Pat<'_>) -> bool {
        let mut by_ref = false;
        pat.walk_always(|pat| {
            if let PatKind::Binding(mode, ..) = pat.kind
                && mode.0 != rustc_hir::ByRef::No
            {
                by_ref = true;
            }
        });
        by_ref
    }
    impl<'tcx> Visitor<'tcx> for Uses<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            match expr.kind {
                ExprKind::Closure(..) => self.closure = true,
                ExprKind::AddrOf(_, _, operand) if is_local(operand, self.local) => {
                    self.borrows.push(Some(expr.hir_id));
                }
                ExprKind::MethodCall(_, receiver, _, _)
                    if is_local(receiver, self.local)
                        && self
                            .typeck
                            .expr_adjustments(receiver)
                            .iter()
                            .any(|adjustment| {
                                matches!(
                                    adjustment.kind,
                                    rustc_middle::ty::adjustment::Adjust::Borrow(_)
                                )
                            }) =>
                {
                    self.borrows.push(None);
                }
                ExprKind::Match(scrutinee, arms, _)
                    if is_local(scrutinee, self.local)
                        && arms.iter().any(|arm| binds_by_ref(arm.pat)) =>
                {
                    self.borrows.push(None);
                }
                ExprKind::Let(let_expr)
                    if is_local(let_expr.init, self.local) && binds_by_ref(let_expr.pat) =>
                {
                    self.borrows.push(None);
                }
                _ => {}
            }
            rustc_hir::intravisit::walk_expr(self, expr);
        }

        fn visit_local(&mut self, let_stmt: &'tcx rustc_hir::LetStmt<'tcx>) {
            if let Some(init) = let_stmt.init
                && is_local(init, self.local)
                && binds_by_ref(let_stmt.pat)
            {
                self.borrows.push(None);
            }
            rustc_hir::intravisit::walk_local(self, let_stmt);
        }
    }
    let body = tcx.hir_body_owned_by(owner);
    let mut uses = Uses {
        typeck,
        local,
        borrows: Vec::new(),
        closure: false,
    };
    uses.visit_body(body);
    if uses.closure || uses.borrows != [Some(borrow)] {
        return false;
    }
    // Not inside a loop: a later iteration's call would see what an earlier
    // one may have stored.
    let mut node = borrow;
    loop {
        node = tcx.parent_hir_id(node);
        match tcx.hir_node(node) {
            Node::Expr(parent) if matches!(parent.kind, ExprKind::Loop(..)) => return false,
            Node::Item(_)
            | Node::ImplItem(_)
            | Node::TraitItem(_)
            | Node::ForeignItem(_)
            | Node::Crate(_) => return true,
            _ => {}
        }
    }
}
