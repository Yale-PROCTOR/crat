//! R394: signed cursors retain the delivered base and use the legacy wrapper's
//! runtime slice checks. Selection consumes offset-sign facts, not a window proof.
use rustc_hir::{
    self as hir,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_middle::{mir::Local, ty};

use super::{CursorHold, CursorPlan, DeliveredBase, DeliveredBaseProvider, emission};
use crate::bo_rewriter::decision::{Ctx, Decision, Subject, SubjectKind, emitability::UseEdit};

fn local(e: &hir::Expr<'_>) -> Option<hir::HirId> {
    match e.kind {
        hir::ExprKind::Path(hir::QPath::Resolved(_, p)) => match p.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}
fn contains(e: &hir::Expr<'_>, id: hir::HirId) -> bool {
    struct Find {
        id: hir::HirId,
        found: bool,
    }
    impl<'v> Visitor<'v> for Find {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            self.found |= local(e) == Some(self.id);
            intravisit::walk_expr(self, e);
        }
    }
    let mut v = Find { id, found: false };
    v.visit_expr(e);
    v.found
}
fn text(ctx: &Ctx<'_, '_>, e: &hir::Expr<'_>) -> Result<String, CursorHold> {
    ctx.tcx
        .sess
        .source_map()
        .span_to_snippet(e.span)
        .map_err(|_| CursorHold::SourceUnavailable)
}
pub(crate) fn type_text(
    mutable: bool,
    optional: bool,
    pointee: &str,
    lifetime: Option<&str>,
) -> String {
    let lt = lifetime.unwrap_or("_").trim_start_matches('\'');
    let ty = format!(
        "crate::slice_cursor::SliceCursor{}<'{lt}, {pointee}>",
        if mutable { "Mut" } else { "" }
    );
    if optional {
        format!("Option<{ty}>")
    } else {
        ty
    }
}
fn constructor(mutable: bool) -> &'static str {
    if mutable {
        "crate::slice_cursor::SliceCursorMut"
    } else {
        "crate::slice_cursor::SliceCursor"
    }
}
fn model_ref(ctx: &Ctx<'_, '_>, s: &Subject) -> bool {
    use crate::analyses::borrow_ownership::{SlotKind, solver::SlotRef};
    ctx.slots
        .fn_local_slots
        .get(&s.fn_did)
        .and_then(|slots| slots.slot_for_local_depth(s.local, 0))
        .and_then(|slot| ctx.model.get(&SlotRef::Local(s.fn_did, slot)))
        == Some(&SlotKind::Ref)
}
struct Base {
    parent_cursor: Option<hir::HirId>,
    expression: String,
    binding: Option<hir::HirId>,
    local: Local,
    delivered: Option<DeliveredBase>,
    fallback: bool,
    composed: Vec<rustc_span::Span>,
}
/// A shared cursor over an element loaded from a delivered outer table:
/// `let p: *const T = *table.offset(k)` with `table` a delivered slice. The
/// loaded element is a bare raw base and takes the same receipted fallback as
/// a raw path; the constructor composes the outer's own element rewrite so the
/// two edits never collide at the initializer span. A written element takes the
/// exclusive view only when the table is named once in the function (relay 003).
fn table_element_base(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    e: &hir::Expr<'_>,
    entries: &[(Subject, Decision)],
) -> Result<Base, CursorHold> {
    if !model_ref(ctx, s) {
        return Err(CursorHold::RefMissing);
    }
    let hir::ExprKind::Unary(hir::UnOp::Deref, pointer) = e.kind else {
        return Err(CursorHold::BaseMissing);
    };
    let root = source_binding(ctx.tcx, s.fn_did, pointer).ok_or(CursorHold::BaseMissing)?;
    // A written element takes an exclusive view only when it is the function's
    // only view of that buffer: the table is named exactly once (this load),
    // so no other element load and no escape of the table exists (relay 003).
    if s.mutable && !table_named_once(ctx.tcx, s.fn_did, root) {
        return Err(CursorHold::BaseMissing);
    }
    let (_, decision) = entries
        .iter()
        .find(|(source, _)| source.fn_did == s.fn_did && source.hir_id == root)
        .ok_or(CursorHold::BaseMissing)?;
    let uses = match decision {
        Decision::Slice { uses, .. } => uses,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => return Err(CursorHold::BaseMissing),
    };
    let element = uses
        .iter()
        .find(|edit| edit.span.source_callsite() == e.span.source_callsite())
        .ok_or(CursorHold::BaseMissing)?;
    Ok(Base {
        parent_cursor: None,
        expression: format!(
            "unsafe {{ {}::from_raw_parts{}({}, crate::FALLBACK_SLICE_EXTENT) }}",
            constructor(s.mutable),
            if s.mutable { "_mut" } else { "" },
            element.replacement
        ),
        binding: None,
        local: s.local,
        delivered: Some(DeliveredBase {
            binding: root,
            window_binding: root,
            initializer: ctx.constructions.init_hirs.get(&(s.fn_did, root)).copied(),
            provider: DeliveredBaseProvider::TableElement,
        }),
        fallback: true,
        composed: vec![element.span],
    })
}
/// Exactly one path expression in the owner's body resolves to `binding`.
pub(crate) fn table_named_once(
    tcx: ty::TyCtxt<'_>,
    owner: rustc_hir::def_id::LocalDefId,
    binding: hir::HirId,
) -> bool {
    struct Names {
        binding: hir::HirId,
        count: usize,
    }
    impl<'v> Visitor<'v> for Names {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            if local(e) == Some(self.binding) {
                self.count += 1;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut names = Names { binding, count: 0 };
    names.visit_body(tcx.hir_body_owned_by(owner));
    names.count == 1
}
/// c2rust spells pointer arithmetic as `&*p.offset(k) as *const T`; the value
/// is `p.offset(k)`. Only a pointee-preserving cast is peeled (`&T` / `*mut T`
/// to `*const T`); a reinterpreting cast stays a cast base.
fn peel_reborrow_idiom<'h, 'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    owner: rustc_hir::def_id::LocalDefId,
    mut e: &'h hir::Expr<'h>,
) -> &'h hir::Expr<'h> {
    fn pointee<'tcx>(t: ty::Ty<'tcx>) -> Option<ty::Ty<'tcx>> {
        match *t.kind() {
            ty::RawPtr(p, _) | ty::Ref(_, p, _) => Some(p),
            _ => None,
        }
    }
    loop {
        match e.kind {
            hir::ExprKind::Cast(inner, _) => {
                let typeck = tcx.typeck(owner);
                if pointee(typeck.expr_ty(e)).is_some()
                    && pointee(typeck.expr_ty(e)) == pointee(typeck.expr_ty(inner))
                {
                    e = inner;
                } else {
                    return e;
                }
            }
            hir::ExprKind::AddrOf(hir::BorrowKind::Ref, _, inner)
                if matches!(inner.kind, hir::ExprKind::Unary(hir::UnOp::Deref, _)) =>
            {
                let hir::ExprKind::Unary(_, pointer) = inner.kind else { unreachable!() };
                e = pointer;
            }
            _ => return e,
        }
    }
}
fn base(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    e: &hir::Expr<'_>,
    entries: &[(Subject, Decision)],
) -> Result<Base, CursorHold> {
    let e = peel_reborrow_idiom(ctx.tcx, s.fn_did, e);
    if let Some(raw) = table_origin(ctx, s, e, entries, &mut rustc_hash::FxHashSet::default()) {
        if raw {
            return Err(CursorHold::BaseModelRaw);
        }
        return table_element_base(ctx, s, e, entries);
    }
    if let hir::ExprKind::MethodCall(_, receiver, [delta], _) = e.kind
        && emission::method(ctx.tcx, s.fn_did, e, &["offset", "add", "sub"])
    {
        let mut b = base(ctx, s, receiver, entries)?;
        b.expression = format!(
            "({}).offset_by({})",
            b.expression,
            delta_text(ctx, s, e, delta)?
        );
        return Ok(b);
    }
    if let hir::ExprKind::MethodCall(_, receiver, [], _) = e.kind
        && emission::method(ctx.tcx, s.fn_did, e, &["as_ptr", "as_mut_ptr"])
        && let ty::Ref(_, element, mutable) = *ctx.tcx.typeck(s.fn_did).expr_ty(receiver).kind()
        && matches!(element.kind(), ty::Slice(_) | ty::Array(..))
    {
        let binding = local(receiver).ok_or(CursorHold::BaseMissing)?;
        if s.mutable && !mutable.is_mut() {
            return Err(CursorHold::ScheduleMissing);
        }
        let root = ctx
            .tcx
            .hir_body_owned_by(s.fn_did)
            .params
            .iter()
            .position(
                |p| matches!(p.pat.kind, hir::PatKind::Binding(_, id, _, None) if id == binding),
            )
            .map(|i| Local::from_usize(i + 1))
            .or_else(|| {
                entries
                    .iter()
                    .find(|(other, _)| other.fn_did == s.fn_did && other.hir_id == binding)
                    .map(|(other, _)| other.local)
            })
            .unwrap_or(s.local);
        return Ok(Base {
            parent_cursor: None,
            expression: format!(
                "{}::new(&{}({})[..])",
                constructor(s.mutable),
                if s.mutable { "mut " } else { "" },
                text(ctx, receiver)?
            ),
            binding: Some(binding),
            local: root,
            delivered: Some(DeliveredBase {
                binding,
                window_binding: binding,
                initializer: match ctx.tcx.parent_hir_node(binding) {
                    hir::Node::LetStmt(decl) => decl.init.map(|e| e.hir_id),
                    _ => None,
                },
                provider: DeliveredBaseProvider::OriginalSlice,
            }),
            fallback: false,
            composed: vec![],
        });
    }
    // A delivered slice PARAMETER is the base itself at the safe body
    // (`in_0: &[T]`); the window is the binding's runtime length.
    if let Some(binding) = local(e)
        && let Some((source, decision)) = entries
            .iter()
            .find(|(source, _)| source.fn_did == s.fn_did && source.hir_id == binding)
        && matches!(source.kind, SubjectKind::Param { .. })
        && let Some(mutable) = slice_mutability(decision)
    {
        if s.mutable && !mutable {
            return Err(CursorHold::ScheduleMissing);
        }
        return Ok(Base {
            parent_cursor: None,
            expression: format!("{}::new({})", constructor(s.mutable), text(ctx, e)?),
            binding: Some(binding),
            local: source.local,
            delivered: Some(DeliveredBase {
                binding,
                window_binding: binding,
                initializer: None,
                provider: DeliveredBaseProvider::SliceParameter,
            }),
            fallback: false,
            composed: vec![],
        });
    }
    if let Some(binding) = local(e)
        && let Some((source, decision)) = entries
            .iter()
            .find(|(source, _)| source.fn_did == s.fn_did && source.hir_id == binding)
        && let Some(mutable) = slice_mutability(decision)
    {
        if s.mutable && !mutable {
            return Err(CursorHold::ScheduleMissing);
        }
        let table = crate::bo_rewriter::decision::DecisionTable {
            entries: entries.to_vec(),
            input_interfaces: ctx.input_interfaces.clone(),
            ..Default::default()
        };
        let producer = crate::bo_rewriter::decision::construction::plan_slice_constructions(
            ctx.tcx,
            &table,
            ctx.constructions,
            ctx.family_policy,
        )
        .into_iter()
        .find(|p| {
            p.node == (s.fn_did, binding)
                && p.hold_reason.is_none()
                && p.replacement.is_some()
                && !p.nullable
        })
        .ok_or(CursorHold::BaseMissing)?;
        return Ok(Base {
            parent_cursor: None,
            expression: format!(
                "{}::new(&{}({})[..])",
                constructor(s.mutable),
                if s.mutable { "mut " } else { "" },
                text(ctx, e)?
            ),
            binding: Some(binding),
            local: source.local,
            delivered: Some(DeliveredBase {
                binding,
                window_binding: binding,
                initializer: Some(producer.init_hir),
                provider: DeliveredBaseProvider::Slice { producer },
            }),
            fallback: false,
            composed: vec![],
        });
    }
    if let Some(binding) = local(e)
        && let Some((source, source_decision)) = entries
            .iter()
            .find(|(source, _)| source.fn_did == s.fn_did && source.hir_id == binding)
        && candidate_shape_in(ctx, source, source_decision, entries)
    {
        if s.mutable && !source.mutable {
            return Err(CursorHold::ScheduleMissing);
        }
        let name = emission::binding_name(ctx.tcx, source)?;
        // An optional parent lends its view through the checked accessor; a
        // shared cursor copies out of it.
        let parent_optional = source.null_init
            || ctx
                .facts
                .raw_only_uses
                .get(&(source.fn_did, source.hir_id))
                .is_some_and(|uses| uses.iter().any(|(op, _)| op == "is_null"));
        let expression = match (source.mutable, s.mutable, parent_optional) {
            (false, false, false) => name,
            (false, false, true) => format!("(*{name}.as_ref().expect(\"non-null cursor\"))"),
            (true, true, false) => format!("{name}.as_deref_mut()"),
            (true, true, true) => {
                format!("{name}.as_mut().expect(\"non-null cursor\").as_deref_mut()")
            }
            (true, false, false) => format!("{name}.as_deref_mut().as_deref()"),
            (true, false, true) => {
                format!("{name}.as_mut().expect(\"non-null cursor\").as_deref_mut().as_deref()")
            }
            (false, true, _) => return Err(CursorHold::ScheduleMissing),
        };
        return Ok(Base {
            expression,
            parent_cursor: Some(binding),
            binding: None,
            local: source.local,
            delivered: None,
            fallback: false,
            composed: vec![],
        });
    }
    let mut raw_origin = e;
    while let hir::ExprKind::Cast(inner, _) = raw_origin.kind {
        raw_origin = inner;
    }
    if !model_ref(ctx, s) {
        return Err(CursorHold::RefMissing);
    }
    // A raw base gets the same explicitly receipted fallback as a raw-to-slice
    // construction. Calls and opaque expressions need their own producer. A raw
    // pointer FIELD of a struct is a bare raw base for a shared cursor only: an
    // exclusive view over a field the struct may hand out again is not proven.
    let field_base = matches!(raw_origin.kind, hir::ExprKind::Field(..))
        && !s.mutable
        && matches!(
            ctx.tcx.typeck(s.fn_did).expr_ty(raw_origin).kind(),
            ty::RawPtr(..)
        );
    if !matches!(raw_origin.kind, hir::ExprKind::Path(_)) && !field_base {
        return Err(CursorHold::BaseMissing);
    }
    let method = if s.mutable {
        "from_raw_parts_mut"
    } else {
        "from_raw_parts"
    };
    Ok(Base {
        parent_cursor: None,
        expression: format!(
            "unsafe {{ {}::{method}({}, crate::FALLBACK_SLICE_EXTENT) }}",
            constructor(s.mutable),
            text(ctx, e)?
        ),
        binding: local(raw_origin),
        local: s.local,
        delivered: None,
        fallback: true,
        composed: vec![],
    })
}
fn delta_text(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    call: &hir::Expr<'_>,
    delta: &hir::Expr<'_>,
) -> Result<String, CursorHold> {
    let hir::ExprKind::MethodCall(segment, _, _, _) = call.kind else {
        return Err(CursorHold::UseUnbuilt);
    };
    if !emission::method(ctx.tcx, s.fn_did, call, &["offset", "add", "sub"]) {
        return Err(CursorHold::UseUnbuilt);
    }
    let d = text(ctx, delta)?;
    Ok(if segment.ident.name.as_str() == "sub" {
        format!("({d} as isize).wrapping_neg()")
    } else {
        format!("({d}) as isize")
    })
}
struct Uses<'a, 'tcx> {
    ctx: &'a Ctx<'a, 'tcx>,
    subject: &'a Subject,
    entries: &'a [(Subject, Decision)],
    name: String,
    init: Option<hir::HirId>,
    base: Option<hir::HirId>,
    optional: bool,
    exclusive_base: bool,
    tail: Option<hir::HirId>,
    bridges: Vec<super::CursorBridge>,
    edits: Vec<UseEdit>,
    hirs: Vec<hir::HirId>,
    hold: Option<CursorHold>,
}
impl Uses<'_, '_> {
    /// A derived pointer leaving the function through its raw return: the tail
    /// view's address under the raw-boundary T2 receipt (retained by the caller).
    /// The seam planner owns a return that is lifetime-planned; a return permit
    /// on this subject leaves the site to it.
    fn raw_return(&mut self, value: &hir::Expr<'_>) {
        let owner = self.subject.fn_did;
        let output = self
            .ctx
            .tcx
            .fn_sig(owner)
            .skip_binder()
            .skip_binder()
            .output();
        let ty::RawPtr(_, output_mutability) = *output.kind() else {
            self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
            return;
        };
        if self.optional
            || self.ctx.lifetime_eligibility.is_some_and(|eligibility| {
                eligibility
                    .return_permit((owner, self.subject.hir_id))
                    .is_some()
            })
        {
            self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
            return;
        }
        let method = match (self.subject.mutable, output_mutability) {
            (true, _) => "as_mut_ptr",
            (false, ty::Mutability::Not) => "as_ptr",
            (false, ty::Mutability::Mut) => {
                self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
                return;
            }
        };
        match self.index(value) {
            Ok(d) if local(value) == Some(self.subject.hir_id) => {
                self.push(
                    value,
                    format!("{}.{method}()", self.name),
                    "raw-op-cursor-return",
                );
                let _ = d;
            }
            Ok(d) => self.push(
                value,
                format!("{}.offset_by({d}).{method}()", self.name),
                "raw-op-cursor-return",
            ),
            Err(hold) => {
                self.hold.get_or_insert(hold);
            }
        }
    }

    fn view(&self) -> String {
        if self.optional {
            format!(
                "{}.as_{}().expect(\"non-null cursor\")",
                self.name,
                if self.subject.mutable { "mut" } else { "ref" }
            )
        } else {
            self.name.clone()
        }
    }

    fn push(&mut self, e: &hir::Expr<'_>, replacement: String, kind: &'static str) {
        self.edits.push(UseEdit {
            span: e.span,
            replacement,
            bridge_kind: kind,
        });
        self.hirs.push(e.hir_id);
    }

    /// The bare subject, possibly under an offset chain, is the right-hand side
    /// of an assignment into a shared peer cursor of this family; the peer owns
    /// that edit (`data = start`, `end = data.offset(k)`).
    fn assigned_to_shared_peer(&self, e: &hir::Expr<'_>) -> bool {
        let mut node = e.hir_id;
        loop {
            let hir::Node::Expr(parent) = self.ctx.tcx.parent_hir_node(node) else {
                return false;
            };
            match parent.kind {
                hir::ExprKind::MethodCall(_, receiver, [_], _)
                    if receiver.hir_id == node
                        && emission::method(
                            self.ctx.tcx,
                            self.subject.fn_did,
                            parent,
                            &["offset", "add", "sub"],
                        ) =>
                {
                    node = parent.hir_id;
                }
                hir::ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == node => {
                    return local(lhs).is_some_and(|peer| {
                        peer != self.subject.hir_id
                            && self.entries.iter().any(|(other, decision)| {
                                other.fn_did == self.subject.fn_did
                                    && other.hir_id == peer
                                    && !other.mutable
                                    && candidate_shape(self.ctx, other, decision)
                            })
                    });
                }
                _ => return false,
            }
        }
    }

    fn peer_index(&self, e: &hir::Expr<'_>, peer: hir::HirId) -> Result<String, CursorHold> {
        if local(e) == Some(peer) {
            return Ok("0isize".into());
        }
        if let hir::ExprKind::MethodCall(_, receiver, [delta], _) = e.kind {
            let prior = self.peer_index(receiver, peer)?;
            let d = delta_text(self.ctx, self.subject, e, delta)?;
            return Ok(format!("({prior}).wrapping_add({d})"));
        }
        Err(CursorHold::UseUnbuilt)
    }

    fn index(&self, e: &hir::Expr<'_>) -> Result<String, CursorHold> {
        if local(e) == Some(self.subject.hir_id) {
            return Ok("0isize".into());
        }
        if let hir::ExprKind::MethodCall(_, receiver, [delta], _) = e.kind {
            let prior = self.index(receiver)?;
            let d = delta_text(self.ctx, self.subject, e, delta)?;
            return Ok(format!("({prior}).wrapping_add({d})"));
        }
        Err(CursorHold::UseUnbuilt)
    }
}
impl<'v> Visitor<'v> for Uses<'_, '_> {
    fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
        if Some(e.hir_id) == self.init {
            return;
        }
        // Only comparison/difference observations are scalar operations:
        // the resulting pointer is consumed by the comparison/difference, never
        // retained. Each operand owns its own edit and typed cursor receipt.
        if let Some(operand) = self
            .ctx
            .facts
            .address_observations
            .iter()
            .filter(|observation| scalar_address_operation(observation.op))
            .flat_map(|observation| &observation.operands)
            .find(|operand| {
                operand.node == (self.subject.fn_did, self.subject.hir_id) && operand.span == e.span
            })
        {
            let value = if self.optional {
                format!(
                    "{}.as_ref().map_or(core::ptr::null(), |cursor| cursor.addr())",
                    self.name
                )
            } else {
                format!("{}.addr()", self.name)
            };
            let value =
                if operand.target.mutability == super::super::raw_boundary::RawMutability::Mut {
                    format!("({value}).cast_mut()")
                } else {
                    value
                };
            self.push(e, value, "cursor-address");
            return;
        }
        if self
            .ctx
            .facts
            .address_observations
            .iter()
            .any(|observation| {
                scalar_address_operation(observation.op) && observation.span == e.span
            })
        {
            intravisit::walk_expr(self, e);
            return;
        }
        // A comparison with an offset-chain operand has no address observation
        // (the shared collector wants two bare locals): each side rooted at this
        // subject takes the derived cursor's address, `S.offset_by(k).addr()`.
        if let hir::ExprKind::Binary(op, lhs, rhs) = e.kind
            && matches!(
                op.node,
                hir::BinOpKind::Lt
                    | hir::BinOpKind::Le
                    | hir::BinOpKind::Gt
                    | hir::BinOpKind::Ge
                    | hir::BinOpKind::Eq
                    | hir::BinOpKind::Ne
            )
            && [lhs, rhs].iter().any(|side| {
                source_binding(self.ctx.tcx, self.subject.fn_did, side) == Some(self.subject.hir_id)
            })
            && [lhs, rhs].iter().any(|side| {
                matches!(side.kind, hir::ExprKind::MethodCall(..))
                    && source_binding(self.ctx.tcx, self.subject.fn_did, side).is_some_and(|root| {
                        root == self.subject.hir_id
                            || self.entries.iter().any(|(other, decision)| {
                                other.fn_did == self.subject.fn_did
                                    && other.hir_id == root
                                    && candidate_shape_in(self.ctx, other, decision, self.entries)
                            })
                    })
            })
            && !self
                .ctx
                .facts
                .address_observations
                .iter()
                .any(|observation| observation.span == e.span)
        {
            for side in [lhs, rhs] {
                if source_binding(self.ctx.tcx, self.subject.fn_did, side)
                    != Some(self.subject.hir_id)
                {
                    self.visit_expr(side);
                    continue;
                }
                let address = |derived: &str| {
                    if self.optional {
                        format!(
                            "{}.as_ref().map_or(core::ptr::null(), |cursor| cursor{derived}.addr())",
                            self.name
                        )
                    } else {
                        format!("{}{derived}.addr()", self.name)
                    }
                };
                match self.index(side) {
                    Ok(_) if local(side) == Some(self.subject.hir_id) => {
                        let value = address("");
                        self.push(side, value, "cursor-address");
                    }
                    Ok(d) => {
                        let value = address(&format!(".offset_by({d})"));
                        self.push(side, value, "cursor-address");
                    }
                    Err(hold) => {
                        self.hold.get_or_insert(hold);
                    }
                }
            }
            return;
        }
        // A difference whose other operand is not a bare local has no address
        // observation; the receiver chain rooted at this subject takes its
        // address and the other operand is left to its own subject.
        if let hir::ExprKind::MethodCall(_, receiver, [other], _) = e.kind
            && emission::method(self.ctx.tcx, self.subject.fn_did, e, &["offset_from"])
            && source_binding(self.ctx.tcx, self.subject.fn_did, receiver)
                == Some(self.subject.hir_id)
            && !self
                .ctx
                .facts
                .address_observations
                .iter()
                .any(|observation| observation.span == e.span)
        {
            let address = |derived: &str| {
                if self.optional {
                    format!(
                        "{}.as_ref().map_or(core::ptr::null(), |cursor| cursor{derived}.addr())",
                        self.name
                    )
                } else {
                    format!("{}{derived}.addr()", self.name)
                }
            };
            match self.index(receiver) {
                Ok(_) if local(receiver) == Some(self.subject.hir_id) => {
                    let value = address("");
                    self.push(receiver, value, "cursor-address");
                }
                Ok(d) => {
                    let value = address(&format!(".offset_by({d})"));
                    self.push(receiver, value, "cursor-address");
                }
                Err(hold) => {
                    self.hold.get_or_insert(hold);
                }
            }
            self.visit_expr(other);
            return;
        }
        // The c2rust reborrow idiom `&*S.offset(k) as *const T` rooted at this
        // subject: a peer's constructor when it initialises or is assigned into
        // a cursor candidate (that peer owns the edit); otherwise the derived
        // address, where a raw value is compared or differenced.
        if matches!(e.kind, hir::ExprKind::Cast(..) | hir::ExprKind::AddrOf(..))
            && let chain = peel_reborrow_idiom(self.ctx.tcx, self.subject.fn_did, e)
            && !std::ptr::eq(chain, e)
            && !matches!(chain.kind, hir::ExprKind::AddrOf(..))
            && source_binding(self.ctx.tcx, self.subject.fn_did, chain) == Some(self.subject.hir_id)
        {
            let parent = self.ctx.tcx.parent_hir_node(e.hir_id);
            let peer_owned = match parent {
                hir::Node::LetStmt(decl) => {
                    decl.init.is_some_and(|init| init.hir_id == e.hir_id)
                        && self.entries.iter().any(|(other, decision)| {
                            other.fn_did == self.subject.fn_did
                                && other.hir_id == decl.pat.hir_id
                                && candidate_shape(self.ctx, other, decision)
                        })
                }
                hir::Node::Expr(parent) => match parent.kind {
                    hir::ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == e.hir_id => local(lhs)
                        .is_some_and(|peer| {
                            self.entries.iter().any(|(other, decision)| {
                                other.fn_did == self.subject.fn_did
                                    && other.hir_id == peer
                                    && candidate_shape(self.ctx, other, decision)
                            })
                        }),
                    _ => false,
                },
                _ => false,
            };
            if peer_owned {
                return;
            }
            let raw_operand = matches!(parent, hir::Node::Expr(parent) if matches!(parent.kind,
                hir::ExprKind::Binary(..))
                || matches!(parent.kind, hir::ExprKind::MethodCall(_, _, [arg], _)
                    if arg.hir_id == e.hir_id
                        && emission::method(self.ctx.tcx, self.subject.fn_did, parent, &["offset_from"])));
            if raw_operand && !self.optional {
                match self.index(chain) {
                    Ok(d) => self.push(
                        e,
                        format!("{}.offset_by({d}).addr()", self.name),
                        "cursor-address",
                    ),
                    Err(hold) => {
                        self.hold.get_or_insert(hold);
                    }
                }
                return;
            }
            self.hold.get_or_insert(CursorHold::BorrowedElementUnbuilt);
            return;
        }
        if matches!(e.kind, hir::ExprKind::AddrOf(..)) && contains(e, self.subject.hir_id) {
            self.hold.get_or_insert(CursorHold::BorrowedElementUnbuilt);
            return;
        }
        // The derived binding owns its constructor edit; the parent lends its
        // full base only through the wrapper's checked Rust reborrow API.
        if self.index(e).is_ok()
            && self.entries.iter().any(|(child, child_decision)| {
                child.fn_did == self.subject.fn_did
                    && child.hir_id != self.subject.hir_id
                    && candidate_shape(self.ctx, child, child_decision)
                    && self
                        .ctx
                        .constructions
                        .init_hirs
                        .get(&(child.fn_did, child.hir_id))
                        == Some(&e.hir_id)
            })
        {
            return;
        }
        if let hir::ExprKind::Assign(lhs, rhs, _) = e.kind
            && local(lhs) == Some(self.subject.hir_id)
        {
            // A shared cursor re-pointed from a peer cursor of the same base
            // family: `data = start` needs no edit (the wrapper is `Copy`),
            // `end = data.offset(k)` takes the peer's derived cursor. Both
            // peers are cursors of this family or neither is emitted.
            if !self.subject.mutable
                && !self.optional
                && let Some(peer) = source_binding(self.ctx.tcx, self.subject.fn_did, rhs)
                && peer != self.subject.hir_id
                && self.entries.iter().any(|(other, decision)| {
                    other.fn_did == self.subject.fn_did
                        && other.hir_id == peer
                        && !other.mutable
                        && candidate_shape(self.ctx, other, decision)
                })
            {
                if local(rhs) != Some(peer)
                    && let Ok(d) = self.peer_index(rhs, peer)
                {
                    let name = emission::binding_name(
                        self.ctx.tcx,
                        self.entries
                            .iter()
                            .find(|(other, _)| other.hir_id == peer)
                            .map(|(other, _)| other)
                            .expect("peer entry"),
                    );
                    match name {
                        Ok(name) => {
                            self.push(rhs, format!("{name}.offset_by({d})"), "cursor-advance")
                        }
                        Err(hold) => {
                            self.hold.get_or_insert(hold);
                        }
                    }
                } else if local(rhs) != Some(peer) {
                    self.hold.get_or_insert(CursorHold::UseUnbuilt);
                }
                return;
            }
            match self.index(rhs) {
                Ok(d) => {
                    self.push(
                        e,
                        format!(
                            "{}.seek({d})",
                            if self.optional {
                                format!("{}.as_mut().expect(\"non-null cursor\")", self.name)
                            } else {
                                self.name.clone()
                            }
                        ),
                        "cursor-advance",
                    );
                }
                Err(hold) => {
                    if self.optional && !self.subject.mutable {
                        match base(self.ctx, self.subject, rhs, self.entries) {
                            Ok(b)
                                if (b.delivered.is_some() || b.parent_cursor.is_some())
                                    && !b.fallback =>
                            {
                                self.push(
                                    e,
                                    format!("{} = Some({})", self.name, b.expression),
                                    "cursor-constructor",
                                )
                            }
                            _ => {
                                self.hold.get_or_insert(hold);
                            }
                        }
                    } else {
                        self.hold.get_or_insert(hold);
                    }
                }
            }
            return;
        }
        if let hir::ExprKind::Ret(Some(value)) = e.kind
            && source_binding(self.ctx.tcx, self.subject.fn_did, value) == Some(self.subject.hir_id)
        {
            self.raw_return(value);
            return;
        }
        if Some(e.hir_id) == self.tail
            && source_binding(self.ctx.tcx, self.subject.fn_did, e) == Some(self.subject.hir_id)
        {
            self.raw_return(e);
            return;
        }
        // Only a deref whose pointer chain is rooted at this subject is this
        // subject's element; an enclosing deref of another pointer that merely
        // carries the subject inside its offset operand is walked instead.
        if let hir::ExprKind::Unary(hir::UnOp::Deref, pointer) = e.kind
            && source_binding(self.ctx.tcx, self.subject.fn_did, pointer)
                == Some(self.subject.hir_id)
        {
            match self.index(pointer) {
                Ok(i) => self.push(e, format!("{}[{i}]", self.view()), "cursor-element"),
                Err(hold) => {
                    self.hold.get_or_insert(hold);
                }
            }
            return;
        }
        if let hir::ExprKind::MethodCall(_, receiver, [], _) = e.kind
            && local(receiver) == Some(self.subject.hir_id)
            && emission::method(self.ctx.tcx, self.subject.fn_did, e, &["is_null"])
        {
            self.push(e, format!("{}.is_none()", self.name), "cursor-element");
            return;
        }
        if let hir::ExprKind::Call(callee, args) = e.kind {
            for (index, arg) in args.iter().enumerate() {
                if local(arg) == Some(self.subject.hir_id) {
                    let ty::FnDef(did, _) = *self
                        .ctx
                        .tcx
                        .typeck(self.subject.fn_did)
                        .expr_ty(callee)
                        .kind()
                    else {
                        self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
                        return;
                    };
                    let target = did.as_local().and_then(|did| self.entries.iter().find(|(s, _)| s.fn_did == did && matches!(s.kind, SubjectKind::Param { hir_index } if hir_index == index)));
                    let raw = target.is_none_or(|(_, d)| raw_decision(d));
                    if raw
                        && !self.optional
                        && index == 0
                        && args.len() == 1
                        && let Some(callee) = emission::scalar_reader(self.ctx.tcx, callee)
                    {
                        self.push(arg, format!("{}.as_ptr()", self.name), "raw-op-cursor-t1");
                        self.bridges.push(super::CursorBridge {
                            call_hir: e.hir_id,
                            callee,
                            argument_span: arg.span,
                            argument_index: index,
                        });
                    } else if raw {
                        // Hypothetical decisions expose the candidate. The final
                        // table must have the existing R130 site permit; that
                        // producer alone owns the argument edit and receipt.
                        if self.ctx.raw_boundary.is_some_and(|rb| {
                            !rb.opens_argument(
                                (self.subject.fn_did, self.subject.hir_id),
                                arg.span,
                                index,
                            )
                        }) {
                            self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
                        }
                    } else if target
                        .and_then(|(_, d)| {
                            slice_mutability(d).or_else(|| cursor_parameter_mutability(d))
                        })
                        .is_some()
                    {
                        // An optional cursor handed to a non-optional slice
                        // position: the C callee dereferences it, so `None` is
                        // the C program's own null path (§28).
                        self.push(
                            arg,
                            format!(
                                "{}.{}()",
                                self.view(),
                                if self.subject.mutable {
                                    "as_slice_mut"
                                } else {
                                    "as_slice"
                                }
                            ),
                            "cursor-element",
                        );
                    } else {
                        self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
                    }
                } else {
                    self.visit_expr(arg);
                }
            }
            self.visit_expr(callee);
            return;
        }
        if local(e) == Some(self.subject.hir_id) {
            // The bare subject as the right-hand side of an assignment into a
            // shared peer cursor (`data = start`) is the peer's edit or no edit.
            let assigned_to_peer = !self.subject.mutable && self.assigned_to_shared_peer(e);
            if !assigned_to_peer {
                self.hold.get_or_insert(CursorHold::UseUnbuilt);
            }
        }
        if self.exclusive_base && self.base == local(e) && self.base.is_some() {
            self.hold.get_or_insert(CursorHold::ScheduleMissing);
        }
        intravisit::walk_expr(self, e);
    }
}
/// The subject is an operand of a pointer ordering / difference observation:
/// the cursor form carries those as address views, so a forward-only walk
/// that is ordered against another pointer is this family's too (relay 008).
pub(crate) fn ordering_participant(ctx: &Ctx<'_, '_>, s: &Subject) -> bool {
    ctx.facts
        .address_observations
        .iter()
        .filter(|observation| scalar_address_operation(observation.op))
        .flat_map(|observation| &observation.operands)
        .any(|operand| operand.node == (s.fn_did, s.hir_id))
}
/// Ordering participation selects a subject only where the other families
/// DEGRADE it (`ptr-comparison` or a cursor reason): a subject they deliver —
/// a thin reference compared, a slice differenced — keeps its delivered form.
fn ordering_degraded(decision: &Decision) -> bool {
    match decision {
        Decision::Degraded(record) => {
            matches!(record.reason, super::super::DegradeReason::PtrComparison)
                || super::is_cursor_reason(&record.reason)
        }
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. } => false,
    }
}
/// The option family degraded this null-initialised subject at a use.
fn optional_degraded(decision: &Decision) -> bool {
    match decision {
        Decision::Degraded(record) => {
            matches!(
                record.reason,
                super::super::DegradeReason::OptUseUnsupported
            )
        }
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. } => false,
    }
}
fn selected(ctx: &Ctx<'_, '_>, s: &Subject, decision: &Decision) -> bool {
    ctx.sign.may_be_negative(s.fn_did, s.local)
        || (ordering_participant(ctx, s) && ordering_degraded(decision))
}
/// A null-initialised local the option family degrades (`opt-use-unsupported`)
/// whose every assignment is an offset chain (or the reborrow idiom) rooted at
/// a cursor root of this family: the optional cursor form covers it.
fn derived_from_cursor_root(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    decision: &Decision,
    entries: &[(Subject, Decision)],
) -> bool {
    if !s.null_init || s.ptr_depth != 1 || !optional_degraded(decision) {
        return false;
    }
    struct Assigns<'a, 'tcx> {
        ctx: &'a Ctx<'a, 'tcx>,
        owner: rustc_hir::def_id::LocalDefId,
        subject: hir::HirId,
        entries: &'a [(Subject, Decision)],
        rooted: usize,
        other: usize,
    }
    impl<'v> Visitor<'v> for Assigns<'_, '_> {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            if let hir::ExprKind::Assign(lhs, rhs, _) = e.kind
                && local(lhs) == Some(self.subject)
            {
                let rhs = peel_reborrow_idiom(self.ctx.tcx, self.owner, rhs);
                let root = source_binding(self.ctx.tcx, self.owner, rhs);
                if root == Some(self.subject) {
                    // a self-advance; not a root
                } else if root.is_some_and(|root| {
                    self.entries.iter().any(|(other, decision)| {
                        other.fn_did == self.owner
                            && other.hir_id == root
                            && (selected(self.ctx, other, decision)
                                || derives_cursor(self.ctx, other, decision, self.entries))
                    })
                }) {
                    self.rooted += 1;
                } else {
                    self.other += 1;
                }
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut assigns = Assigns {
        ctx,
        owner: s.fn_did,
        subject: s.hir_id,
        entries,
        rooted: 0,
        other: 0,
    };
    assigns.visit_body(ctx.tcx.hir_body_owned_by(s.fn_did));
    assigns.rooted > 0 && assigns.other == 0
}
/// The subject is the root of another subject's cursor candidate — its
/// initializer or an assignment into it is an offset chain (or the c2rust
/// reborrow idiom) rooted here — and the other families degrade it: the
/// derived cursors need their parent in this family.
fn derives_cursor(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    decision: &Decision,
    entries: &[(Subject, Decision)],
) -> bool {
    if !ordering_degraded(decision) || s.ptr_depth != 1 {
        return false;
    }
    struct Roots<'a, 'tcx> {
        ctx: &'a Ctx<'a, 'tcx>,
        owner: rustc_hir::def_id::LocalDefId,
        subject: hir::HirId,
        entries: &'a [(Subject, Decision)],
        found: bool,
    }
    impl<'v> Visitor<'v> for Roots<'_, '_> {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            if let hir::ExprKind::Assign(lhs, rhs, _) = e.kind
                && let Some(target) = local(lhs)
                && source_binding(
                    self.ctx.tcx,
                    self.owner,
                    peel_reborrow_idiom(self.ctx.tcx, self.owner, rhs),
                ) == Some(self.subject)
                && self.entries.iter().any(|(other, decision)| {
                    other.fn_did == self.owner
                        && other.hir_id == target
                        && other.hir_id != self.subject
                        && selected(self.ctx, other, decision)
                })
            {
                self.found = true;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let inits = entries.iter().any(|(other, other_decision)| {
        other.fn_did == s.fn_did
            && other.hir_id != s.hir_id
            && selected(ctx, other, other_decision)
            && ctx
                .constructions
                .init_hirs
                .get(&(other.fn_did, other.hir_id))
                .is_some_and(|init| {
                    source_binding(
                        ctx.tcx,
                        s.fn_did,
                        peel_reborrow_idiom(
                            ctx.tcx,
                            s.fn_did,
                            ctx.tcx.hir_node(*init).expect_expr(),
                        ),
                    ) == Some(s.hir_id)
                })
    });
    if inits {
        return true;
    }
    let mut roots = Roots {
        ctx,
        owner: s.fn_did,
        subject: s.hir_id,
        entries,
        found: false,
    };
    roots.visit_body(ctx.tcx.hir_body_owned_by(s.fn_did));
    roots.found
}
pub(super) fn plan(
    ctx: &Ctx<'_, '_>,
    subject: &Subject,
    decision: &Decision,
    entries: &[(Subject, Decision)],
) -> Option<Result<CursorPlan, CursorHold>> {
    if (!selected(ctx, subject, decision)
        && !derives_cursor(ctx, subject, decision, entries)
        && !derived_from_cursor_root(ctx, subject, decision, entries))
        || subject.ptr_depth != 1
    {
        return None;
    }
    match decision {
        Decision::Box(_) | Decision::NestedSlice { .. } | Decision::Cursor { .. } => return None,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Degraded(_) => {}
    }
    // Keep ordinary non-arithmetic references out of this family even when
    // their sign slot is absent. An actual pointer offset must be present.
    struct Offsets {
        binding: hir::HirId,
        found: bool,
    }
    impl<'v> Visitor<'v> for Offsets {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            if let hir::ExprKind::MethodCall(segment, receiver, _, _) = e.kind
                && ["offset", "add", "sub"].contains(&segment.ident.name.as_str())
                && contains(receiver, self.binding)
            {
                self.found = true;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut offsets = Offsets {
        binding: subject.hir_id,
        found: false,
    };
    offsets.visit_body(ctx.tcx.hir_body_owned_by(subject.fn_did));
    // An end marker (`p < end`) may carry no arithmetic of its own; ordering
    // participation admits it beside the walked cursor.
    if !offsets.found
        && !ordering_participant(ctx, subject)
        && !derives_cursor(ctx, subject, decision, entries)
        && !derived_from_cursor_root(ctx, subject, decision, entries)
    {
        return None;
    }
    Some(build(ctx, subject, entries))
}
fn build(
    ctx: &Ctx<'_, '_>,
    subject: &Subject,
    entries: &[(Subject, Decision)],
) -> Result<CursorPlan, CursorHold> {
    let parameter = matches!(subject.kind, SubjectKind::Param { .. });
    let name = emission::binding_name(ctx.tcx, subject)?;
    let init = ctx
        .constructions
        .init_hirs
        .get(&(subject.fn_did, subject.hir_id))
        .copied();
    let null_init = subject.null_init
        || init.is_some_and(|id| is_null_value(ctx, subject, ctx.tcx.hir_node(id).expect_expr()));
    let optional = null_init
        || ctx
            .facts
            .raw_only_uses
            .get(&(subject.fn_did, subject.hir_id))
            .is_some_and(|uses| uses.iter().any(|(op, _)| op == "is_null"));
    let b = if null_init {
        if subject.mutable {
            return Err(CursorHold::OptionalUnbuilt);
        }
        Base {
            parent_cursor: None,
            expression: "None".into(),
            binding: None,
            local: subject.local,
            delivered: None,
            fallback: false,
            composed: vec![],
        }
    } else if parameter {
        if !model_ref(ctx, subject) {
            return Err(CursorHold::RefMissing);
        }
        Base {
            parent_cursor: None,
            expression: String::new(),
            binding: None,
            local: subject.local,
            delivered: None,
            fallback: false,
            composed: vec![],
        }
    } else {
        base(
            ctx,
            subject,
            ctx.tcx
                .hir_node(init.ok_or(CursorHold::BaseMissing)?)
                .expect_expr(),
            entries,
        )?
    };
    // An untyped local (`let mut q = p.offset(k)`) gets its cursor type as an
    // explicit declaration (the custody instrument rejects inferred types); the
    // pointee is the compiler's, rendered.
    let explicit_declaration = if !parameter && subject.ty_span.is_none() {
        let ty::RawPtr(pointee, _) = *ctx
            .tcx
            .typeck(subject.fn_did)
            .node_type(subject.hir_id)
            .kind()
        else {
            return Err(CursorHold::DeclarationUnbuilt);
        };
        Some(type_text(
            subject.mutable,
            optional,
            &pointee.to_string(),
            None,
        ))
    } else {
        None
    };
    let mut v = Uses {
        ctx,
        subject,
        entries,
        name,
        init,
        base: b.binding,
        optional,
        exclusive_base: subject.mutable || b.fallback,
        tail: {
            let body = ctx.tcx.hir_body_owned_by(subject.fn_did);
            match body.value.kind {
                hir::ExprKind::Block(block, _) => block.expr.map(|e| e.hir_id),
                _ => Some(body.value.hir_id),
            }
        },
        bridges: vec![],
        edits: vec![],
        hirs: vec![],
        hold: None,
    };
    v.visit_body(ctx.tcx.hir_body_owned_by(subject.fn_did));
    if let Some(hold) = v.hold {
        return Err(hold);
    }
    if let Some(init) = init {
        v.push(
            ctx.tcx.hir_node(init).expect_expr(),
            if optional && !null_init {
                format!("Some({})", b.expression)
            } else {
                b.expression
            },
            "cursor-constructor",
        );
    }
    Ok(CursorPlan {
        parent_cursor: b.parent_cursor,
        wrapper: true,
        parameter,
        optional,
        fallback: b.fallback,
        uses: v.edits,
        use_hirs: v.hirs,
        base: b.local,
        component: vec![subject.local],
        extent: 0,
        delivered_base: b.delivered,
        bridges: v.bridges,
        local_bridges: vec![],
        composed_edit_spans: b.composed,
        explicit_declaration,
    })
}

/// Recover the compiler-resolved delivered base through a chain of offsets.
pub(crate) fn source_binding(
    tcx: ty::TyCtxt<'_>,
    owner: rustc_hir::def_id::LocalDefId,
    mut e: &hir::Expr<'_>,
) -> Option<hir::HirId> {
    while let hir::ExprKind::MethodCall(_, receiver, _, _) = e.kind {
        if !emission::method(
            tcx,
            owner,
            e,
            &["offset", "add", "sub", "as_ptr", "as_mut_ptr"],
        ) {
            return None;
        }
        e = receiver;
    }
    local(e)
}

pub(crate) fn parameter_form(decision: &Decision) -> super::super::seam::Form {
    use super::super::seam::{Form, form_of};
    match decision {
        Decision::Cursor { mutable, plan } if plan.wrapper && plan.parameter => {
            if plan.optional {
                Form::Opt {
                    mutable: *mutable,
                    slice: true,
                }
            } else {
                Form::Slice { mutable: *mutable }
            }
        }
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::NestedSlice { .. }
        | Decision::Degraded(_) => form_of(decision),
    }
}

fn slice_mutability(decision: &Decision) -> Option<bool> {
    match decision {
        Decision::Slice { mutable, .. } => Some(*mutable),
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::NestedSlice { .. }
        | Decision::Degraded(_) => None,
    }
}
/// A local callee's parameter that is itself a wrapper cursor is a slice at
/// its safe body (`parameter_form`); the caller hands it the tail view.
fn cursor_parameter_mutability(decision: &Decision) -> Option<bool> {
    match decision {
        Decision::Cursor { mutable, plan } if plan.wrapper && plan.parameter && !plan.optional => {
            Some(*mutable)
        }
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::NestedSlice { .. }
        | Decision::Degraded(_) => None,
    }
}
fn raw_decision(decision: &Decision) -> bool {
    match decision {
        Decision::Degraded(_) => true,
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::NestedSlice { .. } => false,
    }
}

fn is_null_value(ctx: &Ctx<'_, '_>, s: &Subject, e: &hir::Expr<'_>) -> bool {
    if crate::bo_rewriter::decision::emitability::is_zero_literal(e) {
        return true;
    }
    let hir::ExprKind::Call(callee, []) = e.kind else {
        return false;
    };
    let ty::FnDef(did, _) = *ctx.tcx.typeck(s.fn_did).expr_ty(callee).kind() else {
        return false;
    };
    !did.is_local()
        && ctx.tcx.crate_name(did.krate).as_str() == "core"
        && ["null", "null_mut"].contains(&ctx.tcx.item_name(did).as_str())
}

fn table_origin(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    mut e: &hir::Expr<'_>,
    entries: &[(Subject, Decision)],
    seen: &mut rustc_hash::FxHashSet<hir::HirId>,
) -> Option<bool> {
    while let hir::ExprKind::Cast(inner, _) = e.kind {
        e = inner;
    }
    if let hir::ExprKind::Unary(hir::UnOp::Deref, pointer) = e.kind {
        let root = source_binding(ctx.tcx, s.fn_did, pointer)?;
        let source = entries
            .iter()
            .find(|(source, _)| source.fn_did == s.fn_did && source.hir_id == root)?
            .0
            .clone();
        use crate::analyses::borrow_ownership::{SlotKind, solver::SlotRef};
        let raw = ctx
            .slots
            .fn_local_slots
            .get(&source.fn_did)
            .and_then(|slots| slots.slot_for_local_depth(source.local, 0))
            .and_then(|slot| ctx.model.get(&SlotRef::Local(source.fn_did, slot)))
            == Some(&SlotKind::Raw);
        return Some(raw);
    }
    if let Some(root) = local(e)
        && seen.insert(root)
        && let Some(init) = ctx.constructions.init_hirs.get(&(s.fn_did, root))
    {
        return table_origin(ctx, s, ctx.tcx.hir_node(*init).expect_expr(), entries, seen);
    }
    None
}

fn candidate_shape(ctx: &Ctx<'_, '_>, s: &Subject, decision: &Decision) -> bool {
    candidate_shape_in(ctx, s, decision, &[])
}
/// `entries` lets a root selected only through its derived cursors count.
fn candidate_shape_in(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    decision: &Decision,
    entries: &[(Subject, Decision)],
) -> bool {
    let uses = ctx.facts.raw_only_uses.get(&(s.fn_did, s.hir_id));
    s.ptr_depth == 1
        && (selected(ctx, s, decision)
            || derives_cursor(ctx, s, decision, entries)
            || (s.null_init && optional_degraded(decision)))
        && (uses.is_some_and(|uses| {
            uses.iter()
                .any(|(op, _)| ["offset", "add", "sub"].contains(&op.as_str()))
        }) || ordering_participant(ctx, s))
        && uses.is_none_or(|uses| uses.iter().all(|(op, _)| op != "is_null"))
}

pub(crate) fn parent_available(
    table: &crate::bo_rewriter::decision::DecisionTable,
    s: &Subject,
    cursor: &CursorPlan,
) -> bool {
    cursor.parent_cursor.is_none_or(|parent| {
        parent.owner.def_id == s.fn_did
            && parent != s.hir_id
            && table.entries.iter().any(|(source, d)| {
                if source.fn_did != s.fn_did || source.hir_id != parent {
                    return false;
                }
                match d {
                    Decision::Cursor { plan, .. } => plan.wrapper,
                    Decision::Ref { .. }
                    | Decision::InferredRef { .. }
                    | Decision::Slice { .. }
                    | Decision::Opt { .. }
                    | Decision::Box(_)
                    | Decision::NestedSlice { .. }
                    | Decision::Degraded(_) => false,
                }
            })
    })
}

fn scalar_address_operation(op: &str) -> bool {
    matches!(
        op,
        "lt" | "le" | "gt" | "ge" | "eq" | "ne" | "ptr-eq" | "difference"
    )
}
