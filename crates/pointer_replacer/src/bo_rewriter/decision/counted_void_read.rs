//! Counted READ aliases: a `void *` parameter cast once to a byte pointer and
//! read through a cursor inside the loop that counts a sibling parameter down
//! to zero. The reads become checked indexing over the counted view (R394-1);
//! the cursor becomes a re-slice; the cast becomes the view itself.
use rustc_hash::FxHashMap;
use rustc_hir::{
    BinOpKind, Expr, ExprKind, HirId, LoopSource, Node, PatKind, StmtKind,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{
    Subject, SubjectKind,
    counted_void::{ByteElement, Contract},
    emitability::UseEdit,
};

fn local_of(e: &Expr<'_>) -> Option<HirId> {
    match e.kind {
        ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

fn is_zero(e: &Expr<'_>) -> bool {
    matches!(e.kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(v, _) if v.get() == 0))
}

/// `while C != 0` / `while C > 0` / `while 0 != C`: the counted-down parameter.
fn countdown_guard(condition: &Expr<'_>) -> Option<HirId> {
    let ExprKind::Binary(op, left, right) = condition.kind else { return None };
    match op.node {
        BinOpKind::Ne => local_of(left)
            .filter(|_| is_zero(right))
            .or_else(|| local_of(right).filter(|_| is_zero(left))),
        BinOpKind::Gt => local_of(left).filter(|_| is_zero(right)),
        _ => None,
    }
}

/// `x = x.wrapping_sub(1)` / `x = x - 1` / `x -= 1`.
fn is_decrement(e: &Expr<'_>, x: HirId) -> bool {
    match e.kind {
        ExprKind::Assign(lhs, rhs, _) if local_of(lhs) == Some(x) => match rhs.kind {
            ExprKind::MethodCall(segment, receiver, [one], _) => {
                segment.ident.name.as_str() == "wrapping_sub"
                    && local_of(receiver) == Some(x)
                    && matches!(one.kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(v, _) if v.get() == 1))
            }
            ExprKind::Binary(op, l, r) => {
                op.node == BinOpKind::Sub
                    && local_of(l) == Some(x)
                    && matches!(r.kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(v, _) if v.get() == 1))
            }
            _ => false,
        },
        ExprKind::AssignOp(op, lhs, rhs) => {
            op.node == rustc_hir::AssignOpKind::SubAssign
                && local_of(lhs) == Some(x)
                && matches!(rhs.kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(v, _) if v.get() == 1))
        }
        _ => false,
    }
}

/// `a = a.offset(1)`: the cursor advance, one element.
fn is_advance(e: &Expr<'_>, a: HirId) -> bool {
    matches!(e.kind, ExprKind::Assign(lhs, rhs, _)
        if local_of(lhs) == Some(a)
            && matches!(rhs.kind, ExprKind::MethodCall(segment, receiver, [one], _)
                if segment.ident.name.as_str() == "offset"
                    && local_of(receiver) == Some(a)
                    && matches!(one.kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(v, _) if v.get() == 1))))
}

struct Facts<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: rustc_hir::def_id::LocalDefId,
    /// Every use of the parameter or the alias, with its parent.
    uses: FxHashMap<HirId, Vec<&'tcx Expr<'tcx>>>,
    /// Loop stack: (loop hir id, counted-down local of its guard).
    loops: Vec<(HirId, Option<HirId>)>,
    /// (expression, enclosing loop, position in that loop's statement list).
    context: FxHashMap<HirId, (Option<HirId>, usize)>,
    writes: FxHashMap<HirId, Vec<&'tcx Expr<'tcx>>>,
    closures: bool,
}
impl<'tcx> Visitor<'tcx> for Facts<'tcx> {
    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if let Some(id) = local_of(e) {
            self.uses.entry(id).or_default().push(e);
            let (lp, pos) = self
                .loops
                .last()
                .map_or((None, 0), |(id, _)| (Some(*id), 0));
            self.context.insert(e.hir_id, (lp, pos));
        }
        match e.kind {
            ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _) => {
                if let Some(id) = local_of(lhs) {
                    self.writes.entry(id).or_default().push(e);
                }
            }
            ExprKind::Closure(..) => self.closures = true,
            _ => {}
        }
        if let ExprKind::Loop(block, _, LoopSource::While, _) = e.kind
            && let Some(ExprKind::If(condition, _, _)) = block.expr.map(|x| x.kind)
        {
            self.loops
                .push((e.hir_id, countdown_guard(peel(condition))));
            intravisit::walk_expr(self, e);
            self.loops.pop();
            return;
        }
        intravisit::walk_expr(self, e);
    }
}

fn peel<'a>(mut e: &'a Expr<'a>) -> &'a Expr<'a> {
    while let ExprKind::DropTemps(inner) = e.kind {
        e = inner;
    }
    e
}

/// Is `e` read as a value (not assigned, not borrowed)?
fn rvalue(tcx: TyCtxt<'_>, e: &Expr<'_>) -> bool {
    match tcx.parent_hir_node(e.hir_id) {
        Node::Expr(parent) => match parent.kind {
            ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _) => lhs.hir_id != e.hir_id,
            ExprKind::AddrOf(..) => false,
            _ => true,
        },
        _ => true,
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
    let body = tcx.hir_body_owned_by(s.fn_did);
    let params = body
        .params
        .iter()
        .map(|p| match p.pat.kind {
            PatKind::Binding(_, id, _, None) => Some(id),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let mut facts = Facts {
        tcx,
        owner: s.fn_did,
        uses: FxHashMap::default(),
        loops: Vec::new(),
        context: FxHashMap::default(),
        writes: FxHashMap::default(),
        closures: false,
    };
    facts.visit_expr(body.value);
    if facts.closures || facts.writes.contains_key(&s.hir_id) {
        return None;
    }
    let name = s.param_name.as_ref()?;
    let typeck = tcx.typeck(s.fn_did);

    // The parameter: null tests and exactly one `let alias = P as *const B`.
    let mut uses = Vec::new();
    let mut alias: Option<(HirId, &Expr<'_>, &'static str, String)> = None;
    let mut nullable = false;
    for use_ in facts.uses.get(&s.hir_id)?.clone() {
        match tcx.parent_hir_node(use_.hir_id) {
            Node::Expr(parent) => match parent.kind {
                ExprKind::MethodCall(segment, receiver, [], _)
                    if receiver.hir_id == use_.hir_id
                        && segment.ident.name.as_str() == "is_null" =>
                {
                    nullable = true;
                    uses.push(UseEdit {
                        span: parent.span,
                        replacement: format!("{name}.is_none()"),
                        bridge_kind: "counted-void-null-test",
                    });
                }
                ExprKind::Cast(inner, _) if inner.hir_id == use_.hir_id => {
                    let byte = match typeck.expr_ty(parent).kind() {
                        TyKind::RawPtr(pointee, _) => match pointee.kind() {
                            TyKind::Uint(rustc_middle::ty::UintTy::U8) => "u8",
                            TyKind::Int(rustc_middle::ty::IntTy::I8) => "i8",
                            _ => return None,
                        },
                        _ => return None,
                    };
                    let Node::LetStmt(decl) = tcx.parent_hir_node(parent.hir_id) else {
                        return None;
                    };
                    let PatKind::Binding(_, a, ident, None) = decl.pat.kind else { return None };
                    if alias.is_some() || decl.init.map(|i| i.hir_id) != Some(parent.hir_id) {
                        return None;
                    }
                    alias = Some((a, parent, byte, ident.name.to_string()));
                }
                _ => return None,
            },
            _ => return None,
        }
    }
    let (alias, cast, byte, alias_name) = alias?;
    // Every write to the alias is the advance; every read is a cursor read.
    let advances = facts.writes.get(&alias).cloned().unwrap_or_default();
    if advances.is_empty() || !advances.iter().all(|w| is_advance(w, alias)) {
        return None;
    }
    let mut counted_loop: Option<(HirId, HirId)> = None;
    let mut in_loop = |e: &Expr<'_>| -> Option<()> {
        let (Some(lp), _) = facts.context.get(&e.hir_id).copied()? else { return None };
        let count = facts.loops_guard(lp)?;
        match counted_loop {
            None => counted_loop = Some((lp, count)),
            Some((seen, _)) if seen == lp => {}
            Some(_) => return None,
        }
        Some(())
    };
    let mut reads = Vec::new();
    for use_ in facts.uses.get(&alias)?.clone() {
        let Node::Expr(parent) = tcx.parent_hir_node(use_.hir_id) else { return None };
        match parent.kind {
            // `*alias`
            ExprKind::Unary(rustc_hir::UnOp::Deref, _) => {
                if !rvalue(tcx, parent) {
                    return None;
                }
                in_loop(use_)?;
                reads.push(UseEdit {
                    span: parent.span,
                    replacement: format!("({alias_name}[0] as {byte})"),
                    bridge_kind: "counted-void-cursor-read",
                });
            }
            // `alias = alias.offset(1)`: the receiver use inside the advance.
            ExprKind::MethodCall(_, receiver, [_], _) if receiver.hir_id == use_.hir_id => {
                let Node::Expr(assign) = tcx.parent_hir_node(parent.hir_id) else { return None };
                if !is_advance(assign, alias) {
                    return None;
                }
                in_loop(use_)?;
                reads.push(UseEdit {
                    span: parent.span,
                    replacement: format!("&{alias_name}[1..]"),
                    bridge_kind: "counted-void-cursor-advance",
                });
            }
            // The advance's own left-hand side, and the `let` binding.
            ExprKind::Assign(lhs, _, _) if lhs.hir_id == use_.hir_id => {}
            _ => return None,
        }
    }
    let (lp, count) = counted_loop?;
    if !params.contains(&count) || count == s.hir_id {
        return None;
    }
    // The count's only writes are decrements inside the counted loop, and the
    // loop body ends with the decrement and the advance, so every read sits at
    // the cursor while the remaining count is positive.
    let decrements = facts.writes.get(&count).cloned().unwrap_or_default();
    let decrement_lhs = |e: &Expr<'_>| match e.kind {
        ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _) => Some(lhs.hir_id),
        _ => None,
    };
    if decrements.len() != 1
        || !is_decrement(decrements[0], count)
        || decrement_lhs(decrements[0])
            .and_then(|lhs| facts.context.get(&lhs))
            .and_then(|c| c.0)
            != Some(lp)
    {
        return None;
    }
    let Node::Expr(loop_expr) = tcx.hir_node(lp) else { return None };
    let ExprKind::Loop(block, _, _, _) = loop_expr.kind else { return None };
    let Some(ExprKind::If(_, then, _)) = block.expr.map(|x| x.kind) else { return None };
    let ExprKind::Block(body_block, _) = then.kind else { return None };
    let tail: Vec<&Expr<'_>> = body_block
        .stmts
        .iter()
        .rev()
        .take(2)
        .filter_map(|st| match st.kind {
            StmtKind::Semi(e) | StmtKind::Expr(e) => Some(e),
            _ => None,
        })
        .collect();
    if body_block.expr.is_some()
        || tail.len() != 2
        || !(tail.iter().any(|e| is_advance(e, alias))
            && tail.iter().any(|e| is_decrement(e, count)))
        || advances.len() != 1
    {
        return None;
    }
    let count_index = params.iter().position(|p| *p == count)?;
    let _ = cast;
    uses.push(UseEdit {
        span: cast.span,
        replacement: if nullable {
            format!("{name}.unwrap_or(&[])")
        } else {
            name.clone()
        },
        bridge_kind: "counted-void-read-alias",
    });
    uses.extend(reads);
    Some(Contract {
        count_index,
        element: ByteElement::Read,
        nullable,
        uses,
    })
}

impl Facts<'_> {
    fn loops_guard(&self, lp: HirId) -> Option<HirId> {
        // Re-read the guard: the stack is gone after the walk, so derive it
        // from the loop expression itself.
        let Node::Expr(loop_expr) = self.tcx.hir_node(lp) else { return None };
        let ExprKind::Loop(block, _, LoopSource::While, _) = loop_expr.kind else { return None };
        let Some(ExprKind::If(condition, _, _)) = block.expr.map(|x| x.kind) else { return None };
        let _ = self.owner;
        countdown_guard(peel(condition))
    }
}
