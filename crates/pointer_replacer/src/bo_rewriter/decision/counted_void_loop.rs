//! Complete-loop schedule proof for the counted byte copy/fill rule.
//!
//! A lexical `i < count` guard alone does not establish that a source has
//! initialized bytes throughout the proposed slice. Accept exactly a complete
//! traversal, with no early exit, index reassignment, or additional operation.

use rustc_hir::{
    BinOpKind, Expr, ExprKind, HirId, LoopSource, PatKind, QPath, Stmt, StmtKind, UnOp, def::Res,
    def_id::LocalDefId,
};
use rustc_middle::ty::{IntTy, TyCtxt, TyKind, UintTy};

#[derive(Clone, Copy, Debug)]
pub(super) struct LoopProof {
    pub(super) index: HirId,
    pub(super) count: HirId,
    pub(super) assignment: HirId,
    pub(super) destination: HirId,
    pub(super) source: Option<HirId>,
}

fn peel<'a, 'tcx>(mut e: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    while let ExprKind::DropTemps(inner) = e.kind {
        e = inner;
    }
    e
}

fn binding(e: &Expr<'_>) -> Option<HirId> {
    match peel(e).kind {
        ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

fn small_integer(e: &Expr<'_>, expected: u128) -> bool {
    match peel(e).kind {
        ExprKind::Lit(lit) => {
            matches!(lit.node, rustc_ast::LitKind::Int(value, _) if value.get() == expected)
        }
        // Zero and one retain their value through valid integral casts.
        ExprKind::Cast(inner, _) => small_integer(inner, expected),
        _ => false,
    }
}

fn statement<'tcx>(s: &Stmt<'tcx>) -> Option<&'tcx Expr<'tcx>> {
    match s.kind {
        StmtKind::Expr(e) | StmtKind::Semi(e) => Some(e),
        _ => None,
    }
}

fn unsigned_word(tcx: TyCtxt<'_>, owner: LocalDefId, e: &Expr<'_>) -> bool {
    matches!(
        tcx.typeck(owner).expr_ty(e).kind(),
        TyKind::Uint(UintTy::Usize)
    ) || (tcx.data_layout.pointer_size.bits() == 64
        && matches!(
            tcx.typeck(owner).expr_ty(e).kind(),
            TyKind::Uint(UintTy::U64)
        ))
}

fn byte_access(tcx: TyCtxt<'_>, owner: LocalDefId, e: &Expr<'_>, index: HirId) -> Option<HirId> {
    let ExprKind::Unary(UnOp::Deref, offset) = peel(e).kind else { return None };
    let ExprKind::MethodCall(method, receiver, [argument], _) = offset.kind else {
        return None;
    };
    if method.ident.name.as_str() != "offset" {
        return None;
    }
    let ExprKind::Cast(base, _) = receiver.kind else { return None };
    let TyKind::RawPtr(pointee, _) = tcx.typeck(owner).expr_ty(receiver).kind() else {
        return None;
    };
    if !matches!(
        pointee.kind(),
        TyKind::Int(IntTy::I8) | TyKind::Uint(UintTy::U8)
    ) {
        return None;
    }
    // Exactly one cast to isize: stripping an arbitrary cast chain would turn
    // `(i as u8) as isize` into `i`, silently changing the accessed byte.
    let ExprKind::Cast(inner, _) = argument.kind else { return None };
    if !matches!(
        tcx.typeck(owner).expr_ty(argument).kind(),
        TyKind::Int(IntTy::Isize)
    ) || binding(inner) != Some(index)
        || !unsigned_word(tcx, owner, inner)
    {
        return None;
    }
    binding(base)
}

fn scalar_parameter(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    mut e: &Expr<'_>,
    params: &[HirId],
    count: HirId,
) -> bool {
    loop {
        if !matches!(
            tcx.typeck(owner).expr_ty(e).kind(),
            TyKind::Int(_) | TyKind::Uint(_)
        ) {
            return false;
        }
        match peel(e).kind {
            ExprKind::Cast(inner, _) => e = inner,
            _ => return binding(e).is_some_and(|id| id != count && params.contains(&id)),
        }
    }
}

pub(super) fn prove(tcx: TyCtxt<'_>, owner: LocalDefId) -> Option<LoopProof> {
    let body = tcx.hir_body_owned_by(owner);
    let params = body
        .params
        .iter()
        .map(|p| match p.pat.kind {
            PatKind::Binding(_, id, _, None) => Some(id),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let ExprKind::Block(block, None) = peel(body.value).kind else { return None };
    let (first, remainder) = block.stmts.split_first()?;
    let StmtKind::Let(decl) = first.kind else { return None };
    let PatKind::Binding(_, index, _, None) = decl.pat.kind else { return None };
    let init = decl.init?;
    if !small_integer(init, 0) || !unsigned_word(tcx, owner, init) {
        return None;
    }
    let mut outer = remainder
        .iter()
        .map(statement)
        .collect::<Option<Vec<_>>>()?;
    outer.extend(block.expr);
    if let Some(reset) = outer.first()
        && matches!(reset.kind, ExprKind::Assign(lhs, rhs, _)
            if binding(lhs) == Some(index) && small_integer(rhs, 0))
    {
        outer.remove(0);
    }
    let [loop_expr] = outer.as_slice() else { return None };
    let ExprKind::Loop(lowered, None, LoopSource::While, _) = loop_expr.kind else {
        return None;
    };
    if !lowered.stmts.is_empty() {
        return None;
    }
    let ExprKind::If(condition, yes, Some(no)) = lowered.expr?.kind else { return None };
    let ExprKind::Binary(op, left, right) = peel(condition).kind else { return None };
    let count = binding(right)?;
    if op.node != BinOpKind::Lt
        || binding(left) != Some(index)
        || !params.contains(&count)
        || !unsigned_word(tcx, owner, left)
        || !unsigned_word(tcx, owner, right)
    {
        return None;
    }
    // rustc's while lowering is `loop { if cond { body } else { break; } }`.
    // Validate even the generated exit, following cursor/delivered.rs.
    let ExprKind::Block(exit, None) = no.kind else { return None };
    let [exit_stmt] = exit.stmts else { return None };
    if exit.expr.is_some()
        || !matches!(statement(exit_stmt).map(|e| &e.kind),
            Some(ExprKind::Break(destination, None))
                if destination.target_id.is_ok_and(|id| id == loop_expr.hir_id))
    {
        return None;
    }
    let ExprKind::Block(loop_body, None) = yes.kind else { return None };
    let mut operations = loop_body
        .stmts
        .iter()
        .map(statement)
        .collect::<Option<Vec<_>>>()?;
    operations.extend(loop_body.expr);
    let [assignment, increment] = operations.as_slice() else { return None };
    let ExprKind::Assign(lhs, rhs, _) = assignment.kind else { return None };
    let destination = byte_access(tcx, owner, lhs, index)?;
    if !params.contains(&destination) {
        return None;
    }
    let source = byte_access(tcx, owner, rhs, index);
    if !source.is_some_and(|id| params.contains(&id))
        && !scalar_parameter(tcx, owner, rhs, &params, count)
    {
        return None;
    }
    let ExprKind::Assign(lhs, rhs, _) = increment.kind else { return None };
    let ExprKind::MethodCall(method, receiver, [one], _) = rhs.kind else { return None };
    if binding(lhs) != Some(index)
        || binding(receiver) != Some(index)
        || method.ident.name.as_str() != "wrapping_add"
        || !small_integer(one, 1)
    {
        return None;
    }
    Some(LoopProof {
        index,
        count,
        assignment: assignment.hir_id,
        destination,
        source,
    })
}
