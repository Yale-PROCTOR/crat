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
    Expr, ExprKind, HirId, Node, PatKind, QPath,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::Visitor,
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
    left: usize,
    right: usize,
    proof: &mut A5PeerProof,
    _may_retain: impl Fn(LocalDefId, usize) -> bool,
) {
    if proof.verdict != A5SiteProofVerdict::Clear || proof.reason != "a5-proven-disjoint" {
        return;
    }
    let loaded = |index: usize| {
        site.args
            .iter()
            .find(|argument| argument.index == index)
            .is_some_and(|argument| argument.loaded_from_memory)
    };
    if loaded(left) || loaded(right) {
        proof.verdict = A5SiteProofVerdict::Overlapping;
        proof.reason = REASON;
        proof.family = "not-shown-disjoint";
    }
}

/// Every place `owner`'s body takes the address of the scalar local `local`:
/// `Some((callee, position))` where the address (under casts) is directly an
/// argument of a call to a local function, `None` for any other borrow — an
/// address stored, bound, compared or cast to an integer, a `ref` binding of
/// the local, an auto-referenced method receiver. Absent (`None` overall)
/// when the local is not a scalar or the body has a closure, which could
/// capture it by reference. A scalar's address is taken by `&` / `&raw` or by
/// a `ref` binding, and by nothing else.
pub(crate) fn address_uses(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    local: HirId,
) -> Option<Vec<Option<(LocalDefId, usize)>>> {
    let typeck = tcx.typeck(owner);
    if !typeck.node_type(local).is_scalar() {
        return None;
    }
    struct Uses<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
        local: HirId,
        uses: Vec<Option<(LocalDefId, usize)>>,
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
    impl<'tcx> Uses<'_, 'tcx> {
        /// The call argument this borrow is, through casts.
        fn argument_of(&self, borrow: &Expr<'_>) -> Option<(LocalDefId, usize)> {
            let mut child = borrow.hir_id;
            loop {
                let Node::Expr(parent) = self.tcx.parent_hir_node(child) else {
                    return None;
                };
                match parent.kind {
                    ExprKind::Cast(..) | ExprKind::DropTemps(..) => child = parent.hir_id,
                    ExprKind::Call(callee, arguments) => {
                        let position = arguments.iter().position(|a| a.hir_id == child)?;
                        let ExprKind::Path(QPath::Resolved(None, path)) = callee.kind else {
                            return None;
                        };
                        let Res::Def(DefKind::Fn, function) = path.res else {
                            return None;
                        };
                        return function.as_local().map(|function| (function, position));
                    }
                    _ => return None,
                }
            }
        }
    }
    impl<'tcx> Visitor<'tcx> for Uses<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            match expr.kind {
                ExprKind::Closure(..) => self.closure = true,
                ExprKind::AddrOf(_, _, operand) if is_local(operand, self.local) => {
                    let argument = self.argument_of(expr);
                    self.uses.push(argument);
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
                    self.uses.push(None);
                }
                ExprKind::Match(scrutinee, arms, _)
                    if is_local(scrutinee, self.local)
                        && arms.iter().any(|arm| binds_by_ref(arm.pat)) =>
                {
                    self.uses.push(None);
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
                self.uses.push(None);
            }
            rustc_hir::intravisit::walk_local(self, let_stmt);
        }
    }
    let body = tcx.hir_body_owned_by(owner);
    let mut uses = Uses {
        tcx,
        typeck,
        local,
        uses: Vec::new(),
        closure: false,
    };
    uses.visit_body(body);
    (!uses.closure).then_some(uses.uses)
}
