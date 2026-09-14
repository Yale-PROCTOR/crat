//! Cursor walks over an existing slice binding. The first loop license keeps
//! index == counter at the header, with counter < the very same base length.
//! Bounds checks defend that invariant; they do not replace the compiler proof.

use rustc_hash::FxHashMap;
use rustc_hir::{
    self as hir,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_middle::ty;

use super::{
    CursorBridge, CursorHold, CursorLocalBridge, CursorPlan, DeliveredBase, DeliveredBaseProvider,
    emission,
};
use crate::bo_rewriter::decision::{Ctx, Decision, Subject, SubjectKind, emitability::UseEdit};

fn local(expr: &hir::Expr<'_>) -> Option<hir::HirId> {
    match expr.kind {
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

fn peel<'a, 'tcx>(mut expr: &'a hir::Expr<'tcx>) -> &'a hir::Expr<'tcx> {
    while let hir::ExprKind::DropTemps(inner) = expr.kind {
        expr = inner;
    }
    expr
}

fn integer(expr: &hir::Expr<'_>, expected: u128) -> bool {
    match peel(expr).kind {
        hir::ExprKind::Lit(lit) => {
            matches!(lit.node, rustc_ast::LitKind::Int(n, _) if n.get() == expected)
        }
        // Only zero and one are used: these casts cannot wrap or change sign.
        hir::ExprKind::Cast(inner, _) => integer(inner, expected),
        _ => false,
    }
}

fn contains(expr: &hir::Expr<'_>, binding: hir::HirId) -> bool {
    struct Find {
        binding: hir::HirId,
        found: bool,
    }
    impl<'v> Visitor<'v> for Find {
        fn visit_expr(&mut self, expr: &'v hir::Expr<'v>) {
            self.found |= local(expr) == Some(self.binding);
            intravisit::walk_expr(self, expr);
        }
    }
    let mut find = Find {
        binding,
        found: false,
    };
    find.visit_expr(expr);
    find.found
}

#[derive(Default)]
struct Inventory<'tcx> {
    block: Option<hir::HirId>,
    initializers: FxHashMap<hir::HirId, (&'tcx hir::Expr<'tcx>, Option<hir::HirId>)>,
    loops: Vec<(&'tcx hir::Expr<'tcx>, Option<hir::HirId>)>,
}

impl<'tcx> Visitor<'tcx> for Inventory<'tcx> {
    fn visit_block(&mut self, block: &'tcx hir::Block<'tcx>) {
        let old = self.block.replace(block.hir_id);
        intravisit::walk_block(self, block);
        self.block = old;
    }

    fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) {
        if let hir::StmtKind::Let(decl) = stmt.kind
            && let hir::PatKind::Binding(_, binding, _, None) = decl.pat.kind
            && let Some(init) = decl.init
        {
            self.initializers.insert(binding, (init, self.block));
        }
        intravisit::walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if matches!(expr.kind, hir::ExprKind::Loop(..)) {
            self.loops.push((expr, self.block));
        }
        intravisit::walk_expr(self, expr);
    }
}

fn statement<'a, 'tcx>(stmt: &'a hir::Stmt<'tcx>) -> Option<&'a hir::Expr<'tcx>> {
    match stmt.kind {
        hir::StmtKind::Semi(expr) | hir::StmtKind::Expr(expr) => Some(expr),
        _ => None,
    }
}

struct Uses<'a, 'tcx> {
    ctx: &'a Ctx<'a, 'tcx>,
    subject: &'a Subject,
    base: hir::HirId,
    counter: hir::HirId,
    length_binding: Option<hir::HirId>,
    init: hir::HirId,
    loop_id: hir::HirId,
    loop_span: rustc_span::Span,
    active_from: rustc_span::BytePos,
    inside: bool,
    name: String,
    hold: Option<CursorHold>,
    edits: Vec<UseEdit>,
    hirs: Vec<hir::HirId>,
    bridges: Vec<CursorBridge>,
}

impl Uses<'_, '_> {
    fn push(&mut self, expr: &hir::Expr<'_>, replacement: String, kind: &'static str) {
        self.edits.push(UseEdit {
            span: expr.span,
            replacement,
            bridge_kind: kind,
        });
        self.hirs.push(expr.hir_id);
    }

    fn length(&self, expr: &hir::Expr<'_>) -> bool {
        matches!(expr.kind, hir::ExprKind::MethodCall(_, receiver, [], _)
            if local(receiver) == Some(self.base)
            && emission::method(self.ctx.tcx, self.subject.fn_did, expr, &["len"]))
    }
}

impl<'v> Visitor<'v> for Uses<'_, 'v> {
    fn visit_pat(&mut self, pat: &'v hir::Pat<'v>) {
        if matches!(pat.kind, hir::PatKind::Binding(mode, _, _, _) if mode.0 != rustc_ast::ByRef::No)
        {
            self.hold = Some(CursorHold::ScheduleMissing);
            return;
        }
        intravisit::walk_pat(self, pat);
    }

    fn visit_stmt(&mut self, stmt: &'v hir::Stmt<'v>) {
        if self.inside
            && let hir::StmtKind::Let(decl) = stmt.kind
        {
            // A body-scoped destructor could act after the final pointer step.
            // The first induction license permits only scalar, drop-free locals.
            let ty = self
                .ctx
                .tcx
                .typeck(self.subject.fn_did)
                .node_type(decl.pat.hir_id);
            if !matches!(
                ty.kind(),
                ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Bool | ty::Char
            ) {
                self.hold = Some(CursorHold::ScheduleMissing);
                return;
            }
        }
        intravisit::walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &'v hir::Expr<'v>) {
        if !self.inside && (expr.hir_id == self.init || expr.hir_id == self.loop_id) {
            return;
        }
        if matches!(
            expr.kind,
            hir::ExprKind::Closure(_) | hir::ExprKind::InlineAsm(..)
        ) {
            self.hold = Some(CursorHold::ScheduleMissing);
            return;
        }
        if matches!(expr.kind, hir::ExprKind::AddrOf(..))
            && (contains(expr, self.subject.hir_id)
                || contains(expr, self.base)
                || contains(expr, self.counter)
                || self
                    .length_binding
                    .is_some_and(|binding| contains(expr, binding)))
        {
            self.hold = Some(CursorHold::BorrowedElementUnbuilt);
            return;
        }
        if matches!(expr.kind, hir::ExprKind::Assign(lhs, _, _) | hir::ExprKind::AssignOp(_, lhs, _)
            if local(lhs) == Some(self.counter) || local(lhs) == Some(self.base)
                || self.length_binding.is_some_and(|binding| local(lhs) == Some(binding)))
        {
            self.hold = Some(CursorHold::ScheduleMissing);
            return;
        }
        if let hir::ExprKind::MethodCall(_, receiver, _, _) = expr.kind
            && (contains(receiver, self.subject.hir_id)
                || (contains(receiver, self.base) && !self.length(expr))
                || contains(receiver, self.counter)
                || self
                    .length_binding
                    .is_some_and(|binding| contains(receiver, binding)))
        {
            // Includes implicit &mut receiver borrows such as clone_from.
            self.hold = Some(CursorHold::ScheduleMissing);
            return;
        }
        if let hir::ExprKind::Call(_, arguments) = expr.kind
            && arguments
                .iter()
                .any(|argument| contains(argument, self.base))
        {
            // A retained alias established before the cursor's borrow needs
            // a separate schedule license, even if the base itself is safe.
            self.hold = Some(CursorHold::ScheduleMissing);
            return;
        }
        if self.inside {
            if matches!(
                expr.kind,
                hir::ExprKind::Loop(..)
                    | hir::ExprKind::Break(..)
                    | hir::ExprKind::Continue(..)
                    | hir::ExprKind::Ret(..)
            ) {
                self.hold = Some(CursorHold::ScheduleMissing);
                return;
            }
            if self.length(expr) {
                self.push(expr, format!("({}).0.len()", self.name), "cursor-length");
                return;
            }
            if let hir::ExprKind::Unary(hir::UnOp::Deref, pointer) = expr.kind
                && local(pointer) == Some(self.subject.hir_id)
            {
                self.push(
                    expr,
                    format!("({}).0[({}).1]", self.name, self.name),
                    "cursor-element",
                );
                return;
            }
            if let hir::ExprKind::Call(callee, [argument]) = expr.kind
                && local(argument) == Some(self.subject.hir_id)
                && let Some(callee) = emission::scalar_reader(self.ctx.tcx, callee)
            {
                let pointer = if self.subject.mutable {
                    format!(
                        "({}).0.as_mut_ptr().add(({}).1).cast_const()",
                        self.name, self.name
                    )
                } else {
                    format!("({}).0.as_ptr().add(({}).1)", self.name, self.name)
                };
                let pointer = crate::bo_rewriter::mechanical_receipt::present_unsafe_text(
                    pointer,
                    self.ctx
                        .tcx
                        .fn_sig(self.subject.fn_did)
                        .skip_binder()
                        .skip_binder()
                        .safety
                        .is_unsafe(),
                );
                self.push(argument, pointer, "raw-op-cursor-t1");
                self.bridges.push(CursorBridge {
                    call_hir: expr.hir_id,
                    callee,
                    argument_span: argument.span,
                    argument_index: 0,
                });
                return;
            }
        }
        if local(expr) == Some(self.subject.hir_id) {
            self.hold = Some(CursorHold::UseUnbuilt);
        }
        if local(expr) == Some(self.base)
            && expr.span.lo() >= self.active_from
            && expr.span.hi() <= self.loop_span.hi()
        {
            self.hold = Some(CursorHold::ScheduleMissing);
        }
        intravisit::walk_expr(self, expr);
    }
}

pub(super) fn plan(
    ctx: &Ctx<'_, '_>,
    subject: &Subject,
    entries: &[(Subject, Decision)],
) -> Option<Result<CursorPlan, CursorHold>> {
    if !matches!(subject.kind, SubjectKind::Local)
        || subject.ptr_depth != 1
        || subject.ty_span.is_none()
    {
        return None;
    }
    let init_id = *ctx
        .constructions
        .init_hirs
        .get(&(subject.fn_did, subject.hir_id))?;
    let init = ctx.tcx.hir_node(init_id).expect_expr();
    let receiver = match init.kind {
        hir::ExprKind::MethodCall(_, receiver, [], _)
            if emission::method(ctx.tcx, subject.fn_did, init, &["as_ptr", "as_mut_ptr"]) =>
        {
            receiver
        }
        hir::ExprKind::Path(_) => init,
        _ => return None,
    };
    let base = local(receiver)?;
    let pointer_ty = ctx.tcx.typeck(subject.fn_did).node_type(subject.hir_id);
    let ty::RawPtr(element, _) = *pointer_ty.kind() else { return None };
    if !matches!(
        element.kind(),
        ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Bool | ty::Char
    ) {
        return Some(Err(CursorHold::LayoutUnbuilt));
    }
    let source_ty = ctx.tcx.typeck(subject.fn_did).expr_ty(receiver);
    let (provider, mutable) = if let ty::Ref(_, pointee, mutable) = *source_ty.kind()
        && let ty::Slice(source_element) = *pointee.kind()
    {
        if source_element != element {
            return Some(Err(CursorHold::LayoutUnbuilt));
        }
        (DeliveredBaseProvider::OriginalSlice, mutable.is_mut())
    } else {
        let (base_subject, choice) = entries
            .iter()
            .find(|(s, _)| s.fn_did == subject.fn_did && s.hir_id == base)?;
        match choice {
            Decision::Slice { mutable, .. } => {
                let table = crate::bo_rewriter::decision::DecisionTable {
                    entries: entries.to_vec(),
                    input_interfaces: ctx.input_interfaces.clone(),
                    return_receivers: ctx.return_receivers.cloned().unwrap_or_default(),
                    ..Default::default()
                };
                let producers =
                    crate::bo_rewriter::decision::construction::plan_slice_constructions(
                        ctx.tcx,
                        &table,
                        ctx.constructions,
                        ctx.family_policy,
                    );
                let Some(producer) = producers
                    .into_iter()
                    .find(|p| p.node == (subject.fn_did, base))
                else {
                    return Some(Err(CursorHold::BaseMissing));
                };
                if producer.hold_reason.is_some()
                    || producer.replacement.is_none()
                    || producer.nullable
                {
                    return Some(Err(CursorHold::BaseMissing));
                }
                (DeliveredBaseProvider::Slice { producer }, *mutable)
            }
            Decision::Box(producer) => {
                let Some(elements) = ctx
                    .ownership_fields
                    .selected_slice_elements((base_subject.fn_did, base_subject.hir_id), producer)
                else {
                    return Some(Err(CursorHold::WindowMissing));
                };
                // Box's ordinary use producer has not delegated an existing
                // adapter at this RHS. Never install overlapping owners.
                if producer
                    .expr_edits
                    .iter()
                    .any(|edit| edit.span == init.span)
                {
                    return Some(Err(CursorHold::UseUnbuilt));
                }
                (
                    DeliveredBaseProvider::Box {
                        producer: producer.clone(),
                        elements,
                    },
                    true,
                )
            }
            Decision::NestedSlice { .. }
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Opt { .. }
            | Decision::Cursor { .. }
            | Decision::Degraded(_) => return None,
        }
    };
    Some(build(
        ctx, subject, entries, init, receiver, base, mutable, provider,
    ))
}

fn provider_minimum(provider: &DeliveredBaseProvider) -> Option<u64> {
    match provider {
        DeliveredBaseProvider::OriginalSlice => None,
        DeliveredBaseProvider::Slice { producer } => {
            if producer.length.is_fallback() {
                Some(crate::bo_rewriter::mechanical_receipt::FALLBACK_SLICE_EXTENT as u64)
            } else {
                // Only an unambiguous literal in the sealed producer's length
                // expression is a constant proof; no variable-name inference.
                producer.length.expression.trim().parse::<u64>().ok()
            }
        }
        DeliveredBaseProvider::Box { elements, .. } => Some(*elements),
    }
}

fn literal(expr: &hir::Expr<'_>) -> Option<u64> {
    match peel(expr).kind {
        hir::ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(value, _) => u64::try_from(value.get()).ok(),
            _ => None,
        },
        _ => None,
    }
}

fn provider_length_binding<'tcx>(
    ctx: &Ctx<'_, 'tcx>,
    provider: &DeliveredBaseProvider,
    element: ty::Ty<'tcx>,
) -> Option<hir::HirId> {
    use crate::bo_rewriter::decision::construction::SliceLengthSource;
    let DeliveredBaseProvider::Slice { producer } = provider else { return None };
    let argument = match &producer.length.source {
        SliceLengthSource::AllocationElementCount { argument_index, .. } => *argument_index,
        SliceLengthSource::AllocationByteCount { argument_index, .. }
            if matches!(
                element.kind(),
                ty::Int(ty::IntTy::I8) | ty::Uint(ty::UintTy::U8) | ty::Bool
            ) =>
        {
            *argument_index
        }
        _ => return None,
    };
    let mut allocation = ctx.tcx.hir_node(producer.init_hir).expect_expr();
    while let hir::ExprKind::Cast(inner, _) = allocation.kind {
        allocation = inner;
    }
    let hir::ExprKind::Call(_, args) = allocation.kind else { return None };
    let count = args.get(argument as usize)?;
    if !matches!(
        ctx.tcx
            .typeck(count.hir_id.owner.def_id)
            .expr_ty(count)
            .kind(),
        ty::Uint(ty::UintTy::Usize)
    ) {
        return None;
    }
    local(count)
}

fn build<'tcx>(
    ctx: &Ctx<'_, 'tcx>,
    subject: &Subject,
    entries: &[(Subject, Decision)],
    init: &'tcx hir::Expr<'tcx>,
    receiver: &hir::Expr<'_>,
    base: hir::HirId,
    mutable: bool,
    provider: DeliveredBaseProvider,
) -> Result<CursorPlan, CursorHold> {
    if subject.null_init {
        return Err(CursorHold::OptionalUnbuilt);
    }
    if subject.mutable && !mutable {
        return Err(CursorHold::ScheduleMissing);
    }
    let observed = super::inspect_subject(ctx.tcx, ctx.slots, ctx.model, subject);
    // Authority here is the unchanged original reference-typed binding, not a
    // new Ref slot grant. Keep the actual model unchanged, including Raw caused
    // by self-advance; close the complete use/schedule proof below.
    let body = ctx.tcx.hir_body_owned_by(subject.fn_did);
    let mut inventory = Inventory::default();
    inventory.visit_body(body);
    let loops = inventory
        .loops
        .iter()
        .filter(|(expr, _)| contains(expr, subject.hir_id))
        .collect::<Vec<_>>();
    let [(loop_expr, loop_parent)] = loops.as_slice() else { return Err(CursorHold::UseUnbuilt) };
    if inventory
        .initializers
        .get(&subject.hir_id)
        .map(|(_, parent)| parent)
        != Some(loop_parent)
        || init.span.hi() > loop_expr.span.lo()
    {
        return Err(CursorHold::ScheduleMissing);
    }
    let hir::ExprKind::Loop(block, _, hir::LoopSource::While, _) = loop_expr.kind else {
        return Err(CursorHold::UseUnbuilt);
    };
    if !block.stmts.is_empty() {
        return Err(CursorHold::UseUnbuilt);
    }
    let Some(guard) = block.expr else { return Err(CursorHold::UseUnbuilt) };
    let hir::ExprKind::If(condition, yes, Some(no)) = guard.kind else {
        return Err(CursorHold::UseUnbuilt);
    };
    let hir::ExprKind::Block(exit, _) = no.kind else { return Err(CursorHold::UseUnbuilt) };
    let [exit_stmt] = exit.stmts else { return Err(CursorHold::UseUnbuilt) };
    if exit.expr.is_some()
        || !matches!(statement(exit_stmt).map(|expr| &expr.kind),
        Some(hir::ExprKind::Break(destination, None)) if destination.target_id.is_ok_and(|id| id == loop_expr.hir_id))
    {
        return Err(CursorHold::UseUnbuilt);
    }
    let hir::ExprKind::Binary(op, index, length) = peel(condition).kind else {
        return Err(CursorHold::WindowMissing);
    };
    if op.node != hir::BinOpKind::Lt {
        return Err(CursorHold::WindowMissing);
    }
    let counter = local(index).ok_or(CursorHold::WindowMissing)?;
    if !matches!(
        ctx.tcx.typeck(subject.fn_did).expr_ty(index).kind(),
        ty::Uint(ty::UintTy::Usize)
    ) {
        return Err(CursorHold::IndexRangeMissing);
    }
    let Some((counter_init, counter_parent)) = inventory.initializers.get(&counter) else {
        return Err(CursorHold::WindowMissing);
    };
    if !integer(counter_init, 0)
        || counter_parent != loop_parent
        || counter_init.span.hi() > loop_expr.span.lo()
    {
        return Err(CursorHold::WindowMissing);
    }
    let hir::ExprKind::Block(loop_body, _) = yes.kind else { return Err(CursorHold::UseUnbuilt) };
    if loop_body.expr.is_some() || loop_body.stmts.len() < 2 {
        return Err(CursorHold::UseUnbuilt);
    }
    let last = loop_body.stmts.len();
    let increment = statement(&loop_body.stmts[last - 1]).ok_or(CursorHold::UseUnbuilt)?;
    let tail = statement(&loop_body.stmts[last - 2]).ok_or(CursorHold::UseUnbuilt)?;
    let (advance, prefix_end, local_flow) = if matches!(tail.kind,
        hir::ExprKind::Assign(lhs, _, _) if local(lhs) == Some(subject.hir_id))
    {
        (tail, last - 2, None)
    } else {
        if last < 4 || !subject.mutable {
            return Err(CursorHold::UseUnbuilt);
        }
        let hir::StmtKind::Let(decl) = loop_body.stmts[last - 4].kind else {
            return Err(CursorHold::UseUnbuilt);
        };
        let hir::PatKind::Binding(mode, destination, _, None) = decl.pat.kind else {
            return Err(CursorHold::UseUnbuilt);
        };
        if mode.0 != rustc_ast::ByRef::No {
            return Err(CursorHold::UseUnbuilt);
        }
        let raw_destination = match entries
            .iter()
            .find(|(s, _)| s.fn_did == subject.fn_did && s.hir_id == destination)
            .map(|(_, d)| d)
        {
            Some(Decision::Degraded(_)) => true,
            Some(
                Decision::NestedSlice { .. }
                | Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_)
                | Decision::Cursor { .. },
            )
            | None => false,
        };
        if !raw_destination {
            return Err(CursorHold::ComponentAliasUnbuilt);
        }
        let Some(capture) = decl.init else { return Err(CursorHold::UseUnbuilt) };
        if local(capture) != Some(subject.hir_id) {
            return Err(CursorHold::UseUnbuilt);
        }
        let hir::ExprKind::Assign(access, value, _) = tail.kind else {
            return Err(CursorHold::UseUnbuilt);
        };
        let hir::ExprKind::Unary(hir::UnOp::Deref, pointer) = access.kind else {
            return Err(CursorHold::UseUnbuilt);
        };
        if local(pointer) != Some(destination)
            || contains(value, subject.hir_id)
            || contains(value, base)
            || contains(value, destination)
        {
            return Err(CursorHold::ComponentAliasUnbuilt);
        }
        struct UsesOf {
            binding: hir::HirId,
            ids: Vec<hir::HirId>,
        }
        impl<'v> Visitor<'v> for UsesOf {
            fn visit_expr(&mut self, expr: &'v hir::Expr<'v>) {
                if local(expr) == Some(self.binding) {
                    self.ids.push(expr.hir_id);
                }
                intravisit::walk_expr(self, expr);
            }
        }
        let mut all = UsesOf {
            binding: destination,
            ids: vec![],
        };
        all.visit_body(body);
        if all.ids != [pointer.hir_id] {
            return Err(CursorHold::ComponentAliasUnbuilt);
        }
        (
            statement(&loop_body.stmts[last - 3]).ok_or(CursorHold::UseUnbuilt)?,
            last - 4,
            Some((destination, capture, access, value)),
        )
    };

    if !matches!(increment.kind, hir::ExprKind::AssignOp(op, lhs, rhs)
        if op.node == hir::AssignOpKind::AddAssign && local(lhs) == Some(counter) && integer(rhs, 1))
    {
        return Err(CursorHold::WindowMissing);
    }
    let hir::ExprKind::Assign(lhs, rhs, _) = advance.kind else {
        return Err(CursorHold::UseUnbuilt);
    };
    if local(lhs) != Some(subject.hir_id) {
        return Err(CursorHold::UseUnbuilt);
    }
    if !matches!(rhs.kind, hir::ExprKind::MethodCall(_, pointer, [delta], _)
        if local(pointer) == Some(subject.hir_id) && integer(delta, 1)
        && emission::method(ctx.tcx, subject.fn_did, rhs, &["add", "offset"]))
    {
        return Err(CursorHold::WindowMissing);
    }
    if entries.iter().any(|(other, _)| {
        other.fn_did == subject.fn_did
            && other.hir_id != subject.hir_id
            && other.hir_id != base
            && local_flow
                .as_ref()
                .is_none_or(|(destination, _, _, _)| other.hir_id != *destination)
            && observed.component.contains(&other.local)
            && matches!(other.kind, SubjectKind::Local)
    }) {
        return Err(CursorHold::ComponentAliasUnbuilt);
    }
    let name = emission::binding_name(ctx.tcx, subject)?;
    let mut uses = Uses {
        ctx,
        subject,
        base,
        counter,
        length_binding: local(length),
        init: init.hir_id,
        loop_id: loop_expr.hir_id,
        loop_span: loop_expr.span,
        active_from: init.span.hi(),
        inside: true,
        name: name.clone(),
        hold: None,
        edits: vec![],
        hirs: vec![],
        bridges: vec![],
    };
    let minimum = provider_minimum(&provider);
    let fixed_bound = literal(length).or_else(|| {
        local(length)
            .and_then(|binding| inventory.initializers.get(&binding))
            .and_then(|(expr, parent)| {
                (parent == loop_parent && expr.span.hi() < init.span.lo())
                    .then(|| literal(expr))
                    .flatten()
            })
    });
    let ty::RawPtr(element, _) = *ctx
        .tcx
        .typeck(subject.fn_did)
        .node_type(subject.hir_id)
        .kind()
    else {
        return Err(CursorHold::LayoutUnbuilt);
    };
    let inherited_binding = provider_length_binding(ctx, &provider, element);
    let constant_window = fixed_bound
        .zip(minimum)
        .is_some_and(|(bound, window)| bound <= window);
    let inherited_window = inherited_binding.is_some_and(|binding| local(length) == Some(binding));
    if !uses.length(length) && !constant_window && !inherited_window {
        let Some((length_init, length_parent)) =
            local(length).and_then(|binding| inventory.initializers.get(&binding))
        else {
            return Err(CursorHold::WindowMissing);
        };
        uses.active_from = length_init.span.hi();
        if !uses.length(length_init)
            || length_parent != loop_parent
            || length_init.span.hi() > init.span.lo()
        {
            return Err(CursorHold::WindowMissing);
        }
    }
    if uses.length(length) {
        uses.push(length, format!("({name}).0.len()"), "cursor-length");
    }
    for stmt in &loop_body.stmts[..prefix_end] {
        uses.visit_stmt(stmt);
    }
    if let Some((_, _, _, value)) = &local_flow {
        uses.visit_expr(value);
    }
    uses.inside = false;
    uses.visit_body(body);
    if let Some(hold) = uses.hold {
        return Err(hold);
    }
    for bridge in &uses.bridges {
        let target = entries.iter().find(|(s, _)| {
            s.fn_did == bridge.callee && matches!(s.kind, SubjectKind::Param { hir_index: 0 })
        });
        let raw = match target.map(|(_, decision)| decision) {
            Some(Decision::Degraded(_)) => true,
            Some(
                Decision::NestedSlice { .. }
                | Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_)
                | Decision::Cursor { .. },
            )
            | None => false,
        };
        if !raw {
            return Err(CursorHold::RawBoundaryUnbuilt);
        }
    }
    let mut temporary = format!("__crat_cursor_next_{}", subject.local.as_u32());
    if temporary == name.trim_start_matches("r#") {
        temporary.push('_');
    }
    let mut local_bridges = vec![];
    if let Some((destination, capture, access, _)) = local_flow {
        // No base reborrow may intervene before the raw temporary's one access.
        // Header index==counter<N proves the +1 successor<=N; this operation
        // touches only the index field, preserving the pre-existing raw use.
        let view = crate::bo_rewriter::mechanical_receipt::present_unsafe_text(
            format!("({name}).0.as_mut_ptr().add(({name}).1)"),
            ctx.tcx
                .fn_sig(subject.fn_did)
                .skip_binder()
                .skip_binder()
                .safety
                .is_unsafe(),
        );
        uses.push(capture, view, "raw-op-cursor-local");
        uses.push(
            advance,
            format!(
                "({name}).1 = ({name}).1.checked_add(1usize).expect(\"cursor index overflow\")"
            ),
            "cursor-advance",
        );
        local_bridges.push(CursorLocalBridge {
            destination,
            initializer: capture.hir_id,
            access: access.hir_id,
        });
    } else {
        uses.push(advance, format!("({name}).1 = ({name}).1.checked_add(1usize).filter(|{temporary}| *{temporary} <= ({name}).0.len()).expect(\"cursor outside delivered window\")"), "cursor-advance");
    }
    let base_name = ctx
        .tcx
        .sess
        .source_map()
        .span_to_snippet(receiver.span)
        .map_err(|_| CursorHold::SourceUnavailable)?;
    let mode = if subject.mutable { "mut " } else { "" };
    uses.push(
        init,
        if matches!(provider, DeliveredBaseProvider::Box { .. }) {
            format!("(&{mode}*({base_name}), 0usize)")
        } else {
            format!("(&{mode}({base_name})[..], 0usize)")
        },
        "cursor-constructor",
    );
    let root_local =
        entries
            .iter()
            .find(|(s, _)| s.fn_did == subject.fn_did && s.hir_id == base)
            .map(|(s, _)| s.local)
            .or_else(|| {
                body.params.iter().position(|p|
            matches!(p.pat.kind, hir::PatKind::Binding(_, id, _, None) if id == base))
            .map(|i| rustc_middle::mir::Local::from_usize(i + 1))
            })
            .ok_or(CursorHold::BaseMissing)?;
    Ok(CursorPlan {
        uses: uses.edits,
        use_hirs: uses.hirs,
        base: root_local,
        component: observed.component,
        extent: 0,
        delivered_base: Some(DeliveredBase {
            provider,
            binding: base,
            window_binding: base,
            initializer: inventory
                .initializers
                .get(&base)
                .map(|(expr, _)| expr.hir_id),
        }),
        bridges: uses.bridges,
        local_bridges,
    })
}
