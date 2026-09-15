//! Bounded native cursor emission. An existing reference to a fixed-size array
//! supplies a real window; every generated index is statically within it.
//! Raw entry pointers and pointer-table loads do not invent a prefix or extent.

use std::collections::BTreeSet;

use rustc_hir::{
    self as hir,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;

use super::{CursorHold, CursorPlan};
use crate::bo_rewriter::decision::{Ctx, Decision, Subject, SubjectKind, emitability::UseEdit};

#[derive(Clone, Copy, Debug)]
struct Range {
    lo: i128,
    hi: i128,
}

fn text(tcx: TyCtxt<'_>, span: Span) -> Result<String, CursorHold> {
    tcx.sess
        .source_map()
        .span_to_snippet(span)
        .map_err(|_| CursorHold::SourceUnavailable)
}

fn local(expr: &hir::Expr<'_>) -> Option<hir::HirId> {
    match expr.kind {
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn binding_name(tcx: TyCtxt<'_>, subject: &Subject) -> Result<String, CursorHold> {
    let hir::Node::Pat(pattern) = tcx.hir_node(subject.hir_id) else {
        return Err(CursorHold::DeclarationUnbuilt);
    };
    let hir::PatKind::Binding(_, id, ident, None) = pattern.kind else {
        return Err(CursorHold::DeclarationUnbuilt);
    };
    if id != subject.hir_id {
        return Err(CursorHold::DeclarationUnbuilt);
    }
    // Preserve the compiler-resolved binding token, including raw identifiers.
    // Symbol spelling alone drops `r#` and can turn a use into a keyword.
    text(tcx, ident.span)
}

pub(super) fn method(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    expr: &hir::Expr<'_>,
    expected: &[&str],
) -> bool {
    let Some(did) = tcx.typeck(owner).type_dependent_def_id(expr.hir_id) else { return false };
    !did.is_local()
        && matches!(tcx.crate_name(did.krate).as_str(), "core" | "std")
        && expected.contains(&tcx.item_name(did).as_str())
}

fn condition_is_pure(expr: &hir::Expr<'_>) -> bool {
    match expr.kind {
        hir::ExprKind::DropTemps(inner) => condition_is_pure(inner),
        hir::ExprKind::Path(_) | hir::ExprKind::Lit(_) => true,
        _ => false,
    }
}

fn scalar_range(expr: &hir::Expr<'_>) -> Option<Range> {
    match expr.kind {
        hir::ExprKind::DropTemps(inner) => scalar_range(inner),
        hir::ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(value, _) => i128::try_from(value.get())
                .ok()
                .map(|n| Range { lo: n, hi: n }),
            _ => None,
        },
        hir::ExprKind::Unary(hir::UnOp::Neg, value) => {
            let r = scalar_range(value)?;
            Some(Range {
                lo: r.hi.checked_neg()?,
                hi: r.lo.checked_neg()?,
            })
        }
        hir::ExprKind::Block(block, _) if block.stmts.is_empty() => scalar_range(block.expr?),
        hir::ExprKind::If(condition, yes, Some(no)) if condition_is_pure(condition) => {
            let a = scalar_range(yes)?;
            let b = scalar_range(no)?;
            Some(Range {
                lo: a.lo.min(b.lo),
                hi: a.hi.max(b.hi),
            })
        }
        _ => None,
    }
}

fn step(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    expr: &hir::Expr<'_>,
    index: String,
    range: Range,
) -> Result<(String, Range), CursorHold> {
    let hir::ExprKind::MethodCall(segment, _, [delta], _) = expr.kind else {
        return Err(CursorHold::UseUnbuilt);
    };
    if !method(tcx, owner, expr, &["offset", "add", "sub"]) {
        return Err(CursorHold::UseUnbuilt);
    }
    let d = scalar_range(delta).ok_or(CursorHold::IndexRangeMissing)?;
    let (operation, range) = match segment.ident.name.as_str() {
        "offset" => (
            "checked_add_signed",
            Range {
                lo: range
                    .lo
                    .checked_add(d.lo)
                    .ok_or(CursorHold::IndexRangeMissing)?,
                hi: range
                    .hi
                    .checked_add(d.hi)
                    .ok_or(CursorHold::IndexRangeMissing)?,
            },
        ),
        "add" => (
            "checked_add",
            Range {
                lo: range
                    .lo
                    .checked_add(d.lo)
                    .ok_or(CursorHold::IndexRangeMissing)?,
                hi: range
                    .hi
                    .checked_add(d.hi)
                    .ok_or(CursorHold::IndexRangeMissing)?,
            },
        ),
        "sub" => (
            "checked_sub",
            Range {
                lo: range
                    .lo
                    .checked_sub(d.hi)
                    .ok_or(CursorHold::IndexRangeMissing)?,
                hi: range
                    .hi
                    .checked_sub(d.lo)
                    .ok_or(CursorHold::IndexRangeMissing)?,
            },
        ),
        _ => return Err(CursorHold::UseUnbuilt),
    };
    Ok((
        format!(
            "({index}).{operation}({}).expect(\"cursor index overflow\")",
            text(tcx, delta.span)?
        ),
        range,
    ))
}

fn contains_local(expr: &hir::Expr<'_>, target: hir::HirId) -> bool {
    struct Find {
        target: hir::HirId,
        found: bool,
    }
    impl<'v> Visitor<'v> for Find {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            self.found |= local(e) == Some(self.target);
            intravisit::walk_expr(self, e);
        }
    }
    let mut find = Find {
        target,
        found: false,
    };
    find.visit_expr(expr);
    find.found
}

struct Origin {
    root: hir::HirId,
    name: String,
    count: u64,
    index: String,
    range: Range,
    mutable: bool,
}

fn origin(tcx: TyCtxt<'_>, owner: LocalDefId, expr: &hir::Expr<'_>) -> Result<Origin, CursorHold> {
    if let hir::ExprKind::MethodCall(_, receiver, _, _) = expr.kind {
        if method(tcx, owner, expr, &["offset", "add", "sub"]) {
            let mut base = origin(tcx, owner, receiver)?;
            (base.index, base.range) = step(tcx, owner, expr, base.index, base.range)?;
            if base.range.lo < 0 || base.range.hi > i128::from(base.count) {
                return Err(CursorHold::WindowMissing);
            }
            return Ok(base);
        }
        if method(tcx, owner, expr, &["as_ptr", "as_mut_ptr"]) {
            let root = local(receiver).ok_or(CursorHold::BaseMissing)?;
            let ty::Ref(_, pointee, mutable) = *tcx.typeck(owner).expr_ty(receiver).kind() else {
                return Err(CursorHold::BaseMissing);
            };
            let ty::Array(element, length) = *pointee.kind() else {
                return Err(CursorHold::WindowMissing);
            };
            if !matches!(
                element.kind(),
                ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Bool | ty::Char
            ) {
                return Err(CursorHold::LayoutUnbuilt);
            }
            let count = length
                .try_to_target_usize(tcx)
                .ok_or(CursorHold::WindowMissing)?;
            return Ok(Origin {
                root,
                name: text(tcx, receiver.span)?,
                count,
                index: "0usize".to_owned(),
                range: Range { lo: 0, hi: 0 },
                mutable: mutable.is_mut(),
            });
        }
    }
    Err(CursorHold::BaseMissing)
}

/// A compiler-resolved scalar raw reader. Its entire body is one primitive
/// pointer read, so it cannot store/return a pointer or consume the allocation.
/// This is an independent T1 proof, not a function-name allowlist.
pub(super) fn scalar_reader(tcx: TyCtxt<'_>, callee: &hir::Expr<'_>) -> Option<LocalDefId> {
    let ty::FnDef(did, _) = *tcx
        .typeck(callee.hir_id.owner.def_id)
        .expr_ty(callee)
        .kind()
    else {
        return None;
    };
    let did = did.as_local()?;
    if !matches!(tcx.hir_node_by_def_id(did), hir::Node::Item(item) if matches!(item.kind, hir::ItemKind::Fn { .. }))
    {
        return None;
    }
    let body = tcx.hir_body_owned_by(did);
    if body.params.len() != 1 {
        return None;
    }
    let hir::PatKind::Binding(_, parameter, _, None) = body.params[0].pat.kind else { return None };
    let hir::ExprKind::Block(block, _) = body.value.kind else { return None };
    if !block.stmts.is_empty() {
        return None;
    }
    let value = block.expr?;
    let hir::ExprKind::MethodCall(_, receiver, [], _) = value.kind else { return None };
    if local(receiver) != Some(parameter) || !method(tcx, did, value, &["read"]) {
        return None;
    }
    let ty::RawPtr(element, mutability) = *tcx.typeck(did).expr_ty(receiver).kind() else {
        return None;
    };
    if mutability.is_mut()
        || !matches!(
            element.kind(),
            ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Bool | ty::Char
        )
    {
        return None;
    }
    Some(did)
}

struct Uses<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    subject: &'a Subject,
    origin: &'a Origin,
    init: hir::HirId,
    name: String,
    uses: Vec<UseEdit>,
    use_hirs: Vec<hir::HirId>,
    hold: Option<CursorHold>,
    bridges: Vec<super::CursorBridge>,
}

impl Uses<'_, '_> {
    fn position(&self, expr: &hir::Expr<'_>) -> Result<(String, Range), CursorHold> {
        if local(expr) == Some(self.subject.hir_id) {
            return Ok((format!("({}).1", self.name), self.origin.range));
        }
        if let hir::ExprKind::MethodCall(_, receiver, _, _) = expr.kind {
            let (index, range) = self.position(receiver)?;
            let (index, range) = step(self.tcx, self.subject.fn_did, expr, index, range)?;
            // Every position in the chain needs a representation, including
            // positions that are never dereferenced. One-past is permitted;
            // leaving the carried window and returning is not a usize cursor.
            if range.lo < 0 || range.hi > i128::from(self.origin.count) {
                return Err(CursorHold::WindowMissing);
            }
            return Ok((index, range));
        }
        Err(CursorHold::UseUnbuilt)
    }

    fn push(&mut self, id: hir::HirId, span: Span, replacement: String, kind: &'static str) {
        self.uses.push(UseEdit {
            span,
            replacement,
            bridge_kind: kind,
        });
        self.use_hirs.push(id);
    }
}

impl<'v> Visitor<'v> for Uses<'_, '_> {
    fn visit_expr(&mut self, expr: &'v hir::Expr<'v>) {
        if expr.hir_id == self.init {
            return;
        }
        if matches!(expr.kind, hir::ExprKind::AddrOf(..))
            && contains_local(expr, self.subject.hir_id)
        {
            self.hold.get_or_insert(CursorHold::BorrowedElementUnbuilt);
            return;
        }
        if let hir::ExprKind::Unary(hir::UnOp::Deref, pointer) = expr.kind {
            let position = self.position(pointer);
            if let Err(hold) = position
                && contains_local(pointer, self.subject.hir_id)
            {
                self.hold.get_or_insert(hold);
                return;
            }
            if let Ok((index, range)) = position {
                if range.lo < 0 || range.hi >= i128::from(self.origin.count) {
                    self.hold = Some(CursorHold::WindowMissing);
                    return;
                }
                self.push(
                    expr.hir_id,
                    expr.span,
                    format!("({}).0[{index}]", self.name),
                    "cursor-element",
                );
                return;
            }
        }
        if let hir::ExprKind::Call(callee, [argument]) = expr.kind
            && local(argument) == Some(self.subject.hir_id)
        {
            if let Some(did) = scalar_reader(self.tcx, callee) {
                if self.origin.range.lo < 0 || self.origin.range.hi >= i128::from(self.origin.count)
                {
                    self.hold = Some(CursorHold::WindowMissing);
                    return;
                }
                // The tuple operand is a bare binding, so each projection has
                // no side effects. Its index and full slice have sealed origin.
                let value = if self.subject.mutable {
                    format!(
                        "({}).0.as_mut_ptr().add(({}).1).cast_const()",
                        self.name, self.name
                    )
                } else {
                    format!("({}).0.as_ptr().add(({}).1)", self.name, self.name)
                };
                let value = crate::bo_rewriter::mechanical_receipt::present_unsafe_text(
                    value,
                    self.tcx
                        .fn_sig(self.subject.fn_did)
                        .skip_binder()
                        .skip_binder()
                        .safety
                        .is_unsafe(),
                );
                self.push(argument.hir_id, argument.span, value, "raw-op-cursor-t1");
                self.bridges.push(super::CursorBridge {
                    call_hir: expr.hir_id,
                    callee: did,
                    argument_span: argument.span,
                    argument_index: 0,
                });
                return;
            }
            self.hold = Some(CursorHold::RawBoundaryUnbuilt);
        }
        if local(expr) == Some(self.subject.hir_id) {
            self.hold = Some(CursorHold::UseUnbuilt);
        }
        if local(expr) == Some(self.origin.root) {
            self.hold = Some(CursorHold::ScheduleMissing);
        }
        if matches!(expr.kind, hir::ExprKind::Closure(_)) {
            self.hold = Some(CursorHold::ScheduleMissing);
        }
        intravisit::walk_expr(self, expr);
    }
}

pub(super) fn plan(
    ctx: &Ctx<'_, '_>,
    subject: &Subject,
    entries: &[(Subject, Decision)],
) -> Result<CursorPlan, CursorHold> {
    if !matches!(subject.kind, SubjectKind::Local)
        || subject.ptr_depth != 1
        || subject.ty_span.is_none()
    {
        return Err(CursorHold::DeclarationUnbuilt);
    }
    if subject.null_init {
        return Err(CursorHold::OptionalUnbuilt);
    }
    let key = (subject.fn_did, subject.hir_id);
    let init = *ctx
        .constructions
        .init_hirs
        .get(&key)
        .ok_or(CursorHold::BaseMissing)?;
    let expression = ctx.tcx.hir_node(init).expect_expr();
    let base = origin(ctx.tcx, subject.fn_did, expression)?;
    if subject.mutable && !base.mutable {
        return Err(CursorHold::ScheduleMissing);
    }
    let observed = super::inspect_subject(ctx.tcx, ctx.slots, ctx.model, subject);
    if observed.findings[0].outcome
        == super::admission::Outcome::Missing(super::admission::Need::RefAdmission)
    {
        return Err(CursorHold::RefMissing);
    }
    if observed.shape != super::admission::Shape::BorrowedSlice {
        return Err(CursorHold::BaseMissing);
    }
    // A named alias needs a one-base/many-index plan not built in this slice.
    if entries.iter().any(|(other, _)| {
        other.fn_did == subject.fn_did
            && other.hir_id != subject.hir_id
            && observed.component.contains(&other.local)
            && other.hir_id != base.root
            && matches!(other.kind, SubjectKind::Local)
    }) {
        return Err(CursorHold::ComponentAliasUnbuilt);
    }
    let mut visitor = Uses {
        tcx: ctx.tcx,
        subject,
        origin: &base,
        init,
        name: binding_name(ctx.tcx, subject)?,
        uses: vec![],
        use_hirs: vec![],
        hold: None,
        bridges: vec![],
    };
    visitor.visit_body(ctx.tcx.hir_body_owned_by(subject.fn_did));
    if let Some(hold) = visitor.hold {
        return Err(hold);
    }
    for bridge in &visitor.bridges {
        let target = entries.iter().find(|(s, _)| {
            s.fn_did == bridge.callee && matches!(s.kind, SubjectKind::Param { hir_index: 0 })
        });
        let stays_raw = match target.map(|(_, d)| d) {
            Some(Decision::Degraded(_)) => true,
            Some(
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_)
                | Decision::NestedSlice { .. }
                | Decision::Cursor { .. },
            )
            | None => false,
        };
        if !stays_raw {
            return Err(CursorHold::RawBoundaryUnbuilt);
        }
    }
    let mode = if subject.mutable { "mut " } else { "" };
    visitor.push(
        expression.hir_id,
        expression.span,
        format!("(&{mode}({})[..], {})", base.name, base.index),
        "cursor-constructor",
    );
    let root_index = ctx.tcx.hir_body_owned_by(subject.fn_did).params.iter().position(|param|
        matches!(param.pat.kind, hir::PatKind::Binding(_, id, _, None) if id == base.root)).ok_or(CursorHold::BaseMissing)?;
    let root_local = rustc_middle::mir::Local::from_usize(root_index + 1);
    if !observed.component.contains(&root_local) {
        return Err(CursorHold::BaseMissing);
    }
    let spans: BTreeSet<_> = visitor
        .uses
        .iter()
        .map(|u| (u.span.lo(), u.span.hi()))
        .collect();
    if spans.len() != visitor.uses.len() {
        return Err(CursorHold::UseUnbuilt);
    }
    Ok(CursorPlan {
        parent_cursor: None,
        wrapper: false,
        parameter: false,
        optional: false,
        fallback: false,
        uses: visitor.uses,
        use_hirs: visitor.use_hirs,
        base: root_local,
        component: observed.component,
        extent: base.count,
        delivered_base: None,
        bridges: visitor.bridges,
        local_bridges: vec![],
        composed_edit_spans: vec![],
    })
}
