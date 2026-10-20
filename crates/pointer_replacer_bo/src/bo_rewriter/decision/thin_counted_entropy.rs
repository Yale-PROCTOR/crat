//! Native access proof for a typed forwarding parameter and a two-state reader.
//!
//! This proves the callee's demand in u32 ELEMENTS, not caller capacity. The
//! caller producer must separately bind that count to a real allocation/slice,
//! including byte-size and isize representability, before creating a slice.

use std::collections::HashSet;

use rustc_hir::{
    BinOpKind, Expr, ExprKind, HirId, PatKind, StmtKind, UnOp,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind, UintTy};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Hold {
    Parameter,
    Forwarding,
    ReaderShape,
    StateTransition,
    PointerUse,
    OpaqueEffects,
}

/// Frozen edits for the same structurally proved reader body. The parent
/// owns admission, complete incoming-source coverage, and edit composition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReaderProof {
    pub count_parameter: usize,
    pub rewrites: Vec<super::emitability::UseEdit>,
    pub comparison: rustc_span::Span,
    pub end_binding: HirId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ForwarderProof {
    pub count_parameter: usize,
    pub callee: LocalDefId,
    pub callee_parameter: usize,
    pub callee_count_parameter: usize,
    pub call_hir: HirId,
    pub call_span: rustc_span::Span,
    pub pointer_argument: HirId,
    pub count_argument: HirId,
}

fn peel<'a>(mut e: &'a Expr<'a>) -> &'a Expr<'a> {
    while let ExprKind::DropTemps(inner) = e.kind {
        e = inner;
    }
    e
}

fn binding(e: &Expr<'_>) -> Option<HirId> {
    match peel(e).kind {
        ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

// Only 0 and 1 are used through casts. Both are preserved by every integral
// cast, unlike arbitrary constants; state labels must be direct literals.
fn small_integer<'a>(mut e: &'a Expr<'a>, want: u128) -> bool {
    loop {
        match peel(e).kind {
            ExprKind::Cast(inner, _) => e = inner,
            ExprKind::Lit(lit) => {
                return matches!(lit.node, rustc_ast::LitKind::Int(n, _) if n.get() == want);
            }
            _ => return false,
        }
    }
}

fn state_literal(e: &Expr<'_>) -> Option<u128> {
    match peel(e).kind {
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(n, _) => Some(n.get()),
            _ => None,
        },
        _ => None,
    }
}

fn usize_like(tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Uint(UintTy::Usize))
        || (tcx.data_layout.pointer_size.bits() == 64
            && matches!(ty.kind(), TyKind::Uint(UintTy::U64)))
}

fn u32_pointer(ty: rustc_middle::ty::Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::RawPtr(pointee, _) if matches!(pointee.kind(), TyKind::Uint(UintTy::U32)))
}

fn block<'a>(e: &'a Expr<'a>) -> Option<&'a rustc_hir::Block<'a>> {
    match peel(e).kind {
        ExprKind::Block(body, _) => Some(body),
        _ => None,
    }
}

fn expressions<'a>(b: &'a rustc_hir::Block<'a>) -> Vec<&'a Expr<'a>> {
    b.stmts
        .iter()
        .filter_map(|s| match s.kind {
            StmtKind::Expr(e) | StmtKind::Semi(e) => Some(e),
            _ => None,
        })
        .chain(b.expr)
        .collect()
}

fn single<'a>(e: &'a Expr<'a>) -> Option<&'a Expr<'a>> {
    let b = block(e)?;
    let es = expressions(b);
    (b.stmts.len() + usize::from(b.expr.is_some()) == 1)
        .then(|| es.first().copied())
        .flatten()
}

fn offset<'a>(
    tcx: TyCtxt<'a>,
    owner: LocalDefId,
    e: &'a Expr<'a>,
) -> Option<(&'a Expr<'a>, &'a Expr<'a>)> {
    let ExprKind::MethodCall(_, receiver, [arg], _) = peel(e).kind else { return None };
    let did = tcx.typeck(owner).type_dependent_def_id(peel(e).hir_id)?;
    (tcx.crate_name(did.krate).as_str() == "core" && tcx.item_name(did).as_str() == "offset")
        .then_some((receiver, arg))
}

fn assign_state<'a>(e: &'a Expr<'a>) -> Option<(&'a Expr<'a>, u128)> {
    let ExprKind::Assign(left, right, _) = peel(e).kind else { return None };
    binding(left)?;
    Some((left, state_literal(right)?))
}

/// Complete use accounting: every occurrence of the tracked bindings must be
/// one of the structurally proved expressions. This catches aliases, writes,
/// address-taking, method autoref, forwarding, and extra reads. Nested bodies
/// are refused rather than being silently skipped by the HIR visitor.
struct Uses<'a> {
    tracked: &'a HashSet<HirId>,
    allowed: &'a HashSet<HirId>,
    seen: HashSet<HirId>,
    error: Option<Hold>,
}
impl<'v> Visitor<'v> for Uses<'_> {
    fn visit_expr(&mut self, e: &'v Expr<'v>) {
        if matches!(e.kind, ExprKind::Closure(..) | ExprKind::InlineAsm(..)) {
            self.error = Some(Hold::OpaqueEffects);
            return;
        }
        if let Some(id) = binding(e)
            && self.tracked.contains(&id)
        {
            if e.span.from_expansion() {
                self.error = Some(Hold::OpaqueEffects);
            } else if !self.allowed.contains(&e.hir_id) {
                self.error = Some(Hold::PointerUse);
            }
            self.seen.insert(e.hir_id);
        }
        intravisit::walk_expr(self, e);
    }
}

fn complete_uses(
    body: &rustc_hir::Body<'_>,
    tracked: HashSet<HirId>,
    allowed: &HashSet<HirId>,
) -> Result<(), Hold> {
    let mut uses = Uses {
        tracked: &tracked,
        allowed,
        seen: HashSet::new(),
        error: None,
    };
    uses.visit_body(body);
    if let Some(error) = uses.error {
        return Err(error);
    }
    if uses.seen != *allowed {
        return Err(Hold::PointerUse);
    }
    Ok(())
}

// Returns the reader's complete access/edit proof. State numbers and binding
// names come from native identities; no library/function names are recognized.
pub(crate) fn reader(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    parameter: usize,
) -> Result<ReaderProof, Hold> {
    if !tcx.hir_body_owners().any(|id| id == owner) {
        return Err(Hold::Parameter);
    }
    let body = tcx.hir_body_owned_by(owner);
    let parameters = body.params.iter().map(|p| p.pat.hir_id).collect::<Vec<_>>();
    let pointer = *parameters.get(parameter).ok_or(Hold::Parameter)?;
    let sig = tcx.fn_sig(owner).skip_binder().skip_binder();
    if !sig
        .inputs()
        .get(parameter)
        .is_some_and(|ty| u32_pointer(*ty))
    {
        return Err(Hold::Parameter);
    }
    let top = block(body.value).ok_or(Hold::ReaderShape)?;
    let mut end_candidates = Vec::new();
    for stmt in top.stmts {
        if let StmtKind::Let(local) = stmt.kind
            && let Some(init) = local.init
            && let Some((receiver, count)) = offset(tcx, owner, init)
            && binding(receiver) == Some(pointer)
            && let ExprKind::Cast(inner, _) = peel(count).kind
            && let Some(count_id) = binding(inner)
            && let Some(index) = parameters.iter().position(|id| *id == count_id)
            && usize_like(tcx, sig.inputs()[index])
        {
            if local.ty.is_some() || local.span.from_expansion() || init.span.from_expansion() {
                return Err(Hold::ReaderShape);
            }
            end_candidates.push((local.pat.hir_id, receiver, inner, index, init.span));
        }
    }
    let [(end, end_receiver, count_expr, count_index, end_init)] = end_candidates.as_slice() else {
        return Err(Hold::ReaderShape);
    };
    let count_id = parameters[*count_index];
    let snippet = |span: rustc_span::Span| {
        if span.from_expansion() {
            return Err(Hold::ReaderShape);
        }
        tcx.sess
            .source_map()
            .span_to_snippet(span)
            .map_err(|_| Hold::ReaderShape)
    };
    let pointer_text = snippet(end_receiver.span)?;
    let count_text = snippet(count_expr.span)?;
    let mut rewrites = vec![super::emitability::UseEdit {
        span: *end_init,
        replacement: format!(
            "{pointer_text}.len().checked_sub({count_text} as usize).expect(\"count exceeds slice\")"
        ),
        bridge_kind: "subject-use",
    }];
    let mut comparison_span = None;
    let mut allowed = HashSet::from([end_receiver.hir_id, count_expr.hir_id]);
    let mut selectors = Vec::new();
    let top_exprs = expressions(top);
    for (position, expr) in top_exprs.iter().enumerate() {
        let ExprKind::If(cond, yes, Some(no)) = peel(expr).kind else { continue };
        let ExprKind::Binary(ne, mask, zero) = peel(cond).kind else { continue };
        let ExprKind::Binary(and, value, one) = peel(mask).kind else { continue };
        if ne.node != BinOpKind::Ne
            || and.node != BinOpKind::BitAnd
            || binding(value) != Some(count_id)
            || !small_integer(one, 1)
            || !small_integer(zero, 0)
        {
            continue;
        }
        let Some((odd_left, odd)) = single(yes).and_then(assign_state) else { continue };
        let Some((even_left, even)) = single(no).and_then(assign_state) else { continue };
        if binding(odd_left) != binding(even_left) || odd == even {
            continue;
        }
        selectors.push((position, value, odd_left, even_left, odd, even));
    }
    let [(selector_position, parity_count, odd_left, even_left, odd, even)] = selectors.as_slice()
    else {
        return Err(Hold::StateTransition);
    };
    let state = binding(odd_left).ok_or(Hold::StateTransition)?;
    allowed.extend([parity_count.hir_id, odd_left.hir_id, even_left.hir_id]);
    let loop_expr = *top_exprs
        .get(selector_position + 1)
        .ok_or(Hold::ReaderShape)?;
    let ExprKind::Loop(loop_body, _, rustc_hir::LoopSource::Loop, _) = peel(loop_expr).kind else {
        return Err(Hold::ReaderShape);
    };
    let loop_nodes = expressions(loop_body);
    let [match_expr] = loop_nodes.as_slice() else { return Err(Hold::ReaderShape) };
    if loop_body.stmts.len() + usize::from(loop_body.expr.is_some()) != 1 {
        return Err(Hold::ReaderShape);
    }
    let ExprKind::Match(discriminant, arms, _) = peel(match_expr).kind else {
        return Err(Hold::ReaderShape);
    };
    if binding(discriminant) != Some(state)
        || arms.len() != 2
        || arms.iter().any(|a| a.guard.is_some())
    {
        return Err(Hold::StateTransition);
    }
    allowed.insert(discriminant.hir_id);
    let mut even_arm = None;
    let mut odd_arm = None;
    for arm in arms {
        if matches!(arm.pat.kind, PatKind::Wild) {
            if odd_arm.replace(arm.body).is_some() {
                return Err(Hold::StateTransition);
            }
        } else {
            // Only a decimal literal pattern is admitted. Native discriminant
            // and assignment identities above bind its meaning to the state.
            let snippet = tcx
                .sess
                .source_map()
                .span_to_snippet(arm.pat.span)
                .map_err(|_| Hold::StateTransition)?;
            if snippet.is_empty()
                || !snippet.chars().all(|c| c.is_ascii_digit() || c == '_')
                || snippet.replace('_', "").parse::<u128>().ok() != Some(*even)
                || even_arm.replace(arm.body).is_some()
            {
                return Err(Hold::StateTransition);
            }
        }
    }
    for (arm, checked, target_state) in [
        (even_arm.ok_or(Hold::StateTransition)?, true, *odd),
        (odd_arm.ok_or(Hold::StateTransition)?, false, *even),
    ] {
        let b = block(arm).ok_or(Hold::ReaderShape)?;
        let mut items = Vec::new();
        for stmt in b.stmts {
            match stmt.kind {
                StmtKind::Let(local) => items.push(local.init.ok_or(Hold::ReaderShape)?),
                StmtKind::Expr(e) | StmtKind::Semi(e) => items.push(e),
                _ => return Err(Hold::ReaderShape),
            }
        }
        items.extend(b.expr);
        let read_index = usize::from(checked);
        if checked {
            let ExprKind::If(condition, yes, None) =
                peel(items.first().ok_or(Hold::ReaderShape)?).kind
            else {
                return Err(Hold::ReaderShape);
            };
            let ExprKind::Unary(UnOp::Not, comparison) = peel(condition).kind else {
                return Err(Hold::ReaderShape);
            };
            let ExprKind::Binary(op, left, right) = peel(comparison).kind else {
                return Err(Hold::ReaderShape);
            };
            if op.node != BinOpKind::Lt
                || binding(left) != Some(pointer)
                || binding(right) != Some(*end)
            {
                return Err(Hold::ReaderShape);
            }
            let exit = single(yes).ok_or(Hold::ReaderShape)?;
            let ExprKind::Break(destination, None) = peel(exit).kind else {
                return Err(Hold::ReaderShape);
            };
            if destination.target_id.ok() != Some(loop_expr.hir_id) {
                return Err(Hold::ReaderShape);
            }
            allowed.extend([left.hir_id, right.hir_id]);
            let end_text = snippet(right.span)?;
            comparison_span = Some(peel(comparison).span);
            rewrites.push(super::emitability::UseEdit {
                span: peel(comparison).span,
                replacement: format!("{pointer_text}.len() > {end_text}"),
                bridge_kind: "subject-use",
            });
        }
        let ExprKind::Unary(UnOp::Deref, read) =
            peel(items.get(read_index).ok_or(Hold::ReaderShape)?).kind
        else {
            return Err(Hold::ReaderShape);
        };
        if binding(read) != Some(pointer) {
            return Err(Hold::ReaderShape);
        }
        allowed.insert(read.hir_id);
        rewrites.push(super::emitability::UseEdit {
            span: peel(items[read_index]).span,
            replacement: format!("{pointer_text}[0]"),
            bridge_kind: "subject-use",
        });
        let advance = *items.get(read_index + 1).ok_or(Hold::ReaderShape)?;
        let ExprKind::Assign(left, right, _) = peel(advance).kind else {
            return Err(Hold::ReaderShape);
        };
        let (receiver, one) = offset(tcx, owner, right).ok_or(Hold::ReaderShape)?;
        if binding(left) != Some(pointer)
            || binding(receiver) != Some(pointer)
            || !small_integer(one, 1)
        {
            return Err(Hold::ReaderShape);
        }
        allowed.extend([left.hir_id, receiver.hir_id]);
        rewrites.push(super::emitability::UseEdit {
            span: right.span,
            replacement: format!("&{pointer_text}[1..]"),
            bridge_kind: "subject-use",
        });
        let (toggle, value) =
            assign_state(items.last().ok_or(Hold::ReaderShape)?).ok_or(Hold::StateTransition)?;
        if binding(toggle) != Some(state) || value != target_state {
            return Err(Hold::StateTransition);
        }
        allowed.insert(toggle.hir_id);
        // No additional control flow may skip the toggle and cause the
        // unguarded odd arm to repeat. The recognized first guard is excluded.
        struct Control {
            invalid: bool,
        }
        impl<'v> Visitor<'v> for Control {
            fn visit_expr(&mut self, e: &'v Expr<'v>) {
                if matches!(
                    e.kind,
                    ExprKind::If(..)
                        | ExprKind::Match(..)
                        | ExprKind::Loop(..)
                        | ExprKind::Break(..)
                        | ExprKind::Continue(..)
                        | ExprKind::Ret(..)
                        | ExprKind::Closure(..)
                        | ExprKind::InlineAsm(..)
                ) {
                    self.invalid = true;
                }
                intravisit::walk_expr(self, e);
            }
        }
        let mut control = Control { invalid: false };
        for item in items.iter().skip(read_index) {
            control.visit_expr(item);
        }
        if control.invalid {
            return Err(Hold::OpaqueEffects);
        }
    }
    complete_uses(
        body,
        HashSet::from([pointer, count_id, *end, state]),
        &allowed,
    )?;
    if rewrites.len() != 6
        || rewrites
            .iter()
            .any(|edit| edit.span.from_expansion() || edit.span.is_dummy())
    {
        return Err(Hold::ReaderShape);
    }
    rewrites.sort_by_key(|edit| (edit.span.lo().0, edit.span.hi().0));
    if rewrites
        .windows(2)
        .any(|pair| pair[0].span.hi() > pair[1].span.lo())
    {
        return Err(Hold::ReaderShape);
    }
    // L >= n is checked before any read. As the shared slice advances, its
    // remaining length is compared with the fixed threshold L - n. Thus the
    // original parity transition graph consumes precisely n elements, even
    // when the incoming slice carries more capacity than the requested count.
    Ok(ReaderProof {
        count_parameter: *count_index,
        rewrites,
        comparison: comparison_span.ok_or(Hold::ReaderShape)?,
        end_binding: *end,
    })
}

/// Bind a wrapper's sole pointer forwarding call to the native parity reader.
/// Returns the wrapper's count-parameter index, with no caller-capacity claim.
pub(crate) fn forwarder(
    tcx: TyCtxt<'_>,
    caller: LocalDefId,
    parameter: usize,
) -> Result<ForwarderProof, Hold> {
    if !tcx.hir_body_owners().any(|id| id == caller) {
        return Err(Hold::Parameter);
    }
    let body = tcx.hir_body_owned_by(caller);
    let params = body.params.iter().map(|p| p.pat.hir_id).collect::<Vec<_>>();
    let pointer = *params.get(parameter).ok_or(Hold::Parameter)?;
    let sig = tcx.fn_sig(caller).skip_binder().skip_binder();
    if !sig
        .inputs()
        .get(parameter)
        .is_some_and(|ty| u32_pointer(*ty))
    {
        return Err(Hold::Parameter);
    }
    struct Calls<'tcx> {
        calls: Vec<&'tcx Expr<'tcx>>,
    }
    impl<'tcx> Visitor<'tcx> for Calls<'tcx> {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if matches!(e.kind, ExprKind::Call(..)) {
                self.calls.push(e);
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut scan = Calls { calls: Vec::new() };
    scan.visit_body(body);
    let mut candidates = Vec::new();
    for call in scan.calls {
        let ExprKind::Call(function, args) = call.kind else { continue };
        let TyKind::FnDef(did, _) = tcx.typeck(caller).expr_ty(function).kind() else { continue };
        let Some(callee) = did.as_local() else { continue };
        if callee == caller {
            continue;
        }
        for (position, arg) in args.iter().enumerate() {
            if binding(arg) != Some(pointer) {
                continue;
            }
            let Ok(reader) = reader(tcx, callee, position) else { continue };
            let count_position = reader.count_parameter;
            let Some(count_arg) = args.get(count_position) else { continue };
            let Some(count_id) = binding(count_arg) else { continue };
            let Some(index) = params.iter().position(|id| *id == count_id) else { continue };
            if !usize_like(tcx, sig.inputs()[index]) {
                continue;
            }
            if call.span.from_expansion()
                || arg.span.from_expansion()
                || count_arg.span.from_expansion()
            {
                continue;
            }
            candidates.push((
                arg.hir_id,
                count_arg.hir_id,
                count_id,
                ForwarderProof {
                    count_parameter: index,
                    callee,
                    callee_parameter: position,
                    callee_count_parameter: count_position,
                    call_hir: call.hir_id,
                    call_span: call.span,
                    pointer_argument: arg.hir_id,
                    count_argument: count_arg.hir_id,
                },
            ));
        }
    }
    let [(pointer_use, count_use, count_id, proof)] = candidates.as_slice() else {
        return Err(Hold::Forwarding);
    };
    complete_uses(
        body,
        HashSet::from([pointer, *count_id]),
        &HashSet::from([*pointer_use, *count_use]),
    )?;
    Ok(proof.clone())
}
