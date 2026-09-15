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
fn base(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    e: &hir::Expr<'_>,
    entries: &[(Subject, Decision)],
) -> Result<Base, CursorHold> {
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
        && let Some((source, _)) = entries
            .iter()
            .find(|(source, _)| source.fn_did == s.fn_did && source.hir_id == binding)
        && candidate_shape(ctx, source)
    {
        if s.mutable && !source.mutable {
            return Err(CursorHold::ScheduleMissing);
        }
        let name = emission::binding_name(ctx.tcx, source)?;
        let expression = match (source.mutable, s.mutable) {
            (false, false) => name,
            (true, true) => format!("{name}.as_deref_mut()"),
            (true, false) => format!("{name}.as_deref_mut().as_deref()"),
            (false, true) => return Err(CursorHold::ScheduleMissing),
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
    // construction. Calls and opaque expressions need their own producer.
    if !matches!(raw_origin.kind, hir::ExprKind::Path(_)) {
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
    bridges: Vec<super::CursorBridge>,
    edits: Vec<UseEdit>,
    hirs: Vec<hir::HirId>,
    hold: Option<CursorHold>,
}
impl Uses<'_, '_> {
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
                    "{}.as_ref().map_or(core::ptr::null(), |cursor| cursor.as_ptr())",
                    self.name
                )
            } else {
                format!("{}.as_ptr()", self.name)
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
        if matches!(e.kind, hir::ExprKind::AddrOf(..)) && contains(e, self.subject.hir_id) {
            self.hold.get_or_insert(CursorHold::BorrowedElementUnbuilt);
            return;
        }
        // The derived binding owns its constructor edit; the parent lends its
        // full base only through the wrapper's checked Rust reborrow API.
        if self.index(e).is_ok()
            && self.entries.iter().any(|(child, _)| {
                child.fn_did == self.subject.fn_did
                    && child.hir_id != self.subject.hir_id
                    && candidate_shape(self.ctx, child)
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
                            Ok(b) if b.delivered.is_some() && !b.fallback => self.push(
                                e,
                                format!("{} = Some({})", self.name, b.expression),
                                "cursor-constructor",
                            ),
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
        if let hir::ExprKind::Unary(hir::UnOp::Deref, pointer) = e.kind
            && contains(pointer, self.subject.hir_id)
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
                    } else if target.and_then(|(_, d)| slice_mutability(d)).is_some() {
                        self.push(
                            arg,
                            format!(
                                "{}.{}()",
                                self.name,
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
            self.hold.get_or_insert(CursorHold::UseUnbuilt);
        }
        if self.exclusive_base && self.base == local(e) && self.base.is_some() {
            self.hold.get_or_insert(CursorHold::ScheduleMissing);
        }
        intravisit::walk_expr(self, e);
    }
}
pub(super) fn plan(
    ctx: &Ctx<'_, '_>,
    subject: &Subject,
    decision: &Decision,
    entries: &[(Subject, Decision)],
) -> Option<Result<CursorPlan, CursorHold>> {
    if !ctx.sign.may_be_negative(subject.fn_did, subject.local) || subject.ptr_depth != 1 {
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
    if !offsets.found {
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
        if subject.ty_span.is_none() {
            return Err(CursorHold::DeclarationUnbuilt);
        }
        base(
            ctx,
            subject,
            ctx.tcx
                .hir_node(init.ok_or(CursorHold::BaseMissing)?)
                .expect_expr(),
            entries,
        )?
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

fn candidate_shape(ctx: &Ctx<'_, '_>, s: &Subject) -> bool {
    s.ptr_depth == 1
        && s.ty_span.is_some()
        && !s.null_init
        && ctx.sign.may_be_negative(s.fn_did, s.local)
        && ctx
            .facts
            .raw_only_uses
            .get(&(s.fn_did, s.hir_id))
            .is_some_and(|uses| {
                uses.iter()
                    .any(|(op, _)| ["offset", "add", "sub"].contains(&op.as_str()))
                    && uses.iter().all(|(op, _)| op != "is_null")
            })
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
