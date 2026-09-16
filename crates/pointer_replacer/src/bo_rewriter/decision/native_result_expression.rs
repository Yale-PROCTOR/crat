//! wave-6l wave 5 — native borrowed call results consumed at EXPRESSION
//! positions that are neither a receiving local nor a raw call argument.
//!
//! When a callee's return interface changes to a borrowed form, every call
//! site in a delivered caller must present the result the way the caller
//! consumes it. The receiving-local twin (`raw_receiver`) serves
//! `let x = callee(..)`; the outbound-expression carrier serves a native call
//! passed to a raw call argument. Everything else — `*callee(..)` read or
//! written, `callee(..) as *mut U`, `x = callee(..)` into an existing raw
//! local, `let n = callee(..) as *mut U` — was left unadapted, and one such
//! site dropped the callee's whole class (heman `heman_image_texel`, 41 call
//! sites, `raw-receiver-result-unavailable:InitializerNotExactDirectCall`).
//!
//! This module restores the call's ORIGINAL raw type at the call itself with
//! the same twin the receiving-local path uses — `{ let t: <borrowed> =
//! (adapted call); (view) as <raw> }` — so the surrounding deref, cast,
//! assignment or compound assignment applies to exactly what it applied to
//! before. Every site is a receipted T2 view under the named waiver (the raw
//! pointer's retention past the statement is unknown to the rewriter); a call
//! whose result position is outside the four shapes holds the class typed,
//! as before. The callee's model kind is never outrun: the twin converts the
//! callee's own borrowed interface back to the raw type the caller already
//! held.

use rustc_hash::FxHashMap;
use rustc_hir::{
    Expr, ExprKind, HirId, Node as HirNode,
    def_id::LocalDefId,
    intravisit::{Visitor, walk_expr},
};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{
    Decision, DecisionTable, SubjectKind,
    raw_boundary::{self, RawBoundaryBlockReason, RawTargetType},
    return_interface::ReturnInterface,
    seam::{self, Form, GlueSpec},
};
use crate::{
    bo_rewriter::bridge_receipt::{
        BridgeCalleeId, BridgeExtentKind, BridgeRetentionTier, BridgeSitePlan,
        RAW_BOUNDARY_T2_WAIVER_ID, SignatureClassId,
    },
    utils::rustc::RustProgram,
};

/// The result positions this carrier serves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ResultPosition {
    /// `*callee(..)` — read, written or compound-assigned through.
    Deref,
    /// `callee(..) as *mut U` (also the initializer `let n = callee(..) as *mut U`).
    Cast,
    /// `x = callee(..)` into an existing raw place.
    Assign,
    /// `let x = callee(..)` where `x` is typed by a sealed constructor over
    /// the raw call (a walking caller of a thin return): the constructor is
    /// composed over this view (the initializer-channel composition).
    Initializer,
}

impl ResultPosition {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::Deref => "deref",
            Self::Cast => "cast",
            Self::Assign => "assign",
            Self::Initializer => "initializer",
        }
    }
}

/// Decide-time (wave 6): the subject is a call-result local of a LOCAL callee
/// whose return this lane delivers THIN, so a sealed slice constructor over
/// the call is rendered over this lane's raw-restoring view of it — the
/// constructor-typing refusal's premise (a constructor over a converted
/// return is ill-typed) does not hold.
pub(crate) fn bridges_local_callee_result(
    ctx: &super::Ctx<'_, '_>,
    subject: &super::Subject,
) -> bool {
    use super::construction::{CallResultTarget, Construction};
    let node = (subject.fn_did, subject.hir_id);
    matches!(
        ctx.constructions.by_binding.get(&node),
        Some(Construction::CallResult)
    ) && match ctx.constructions.call_result_targets.get(&node) {
        Some(CallResultTarget::DirectLocal(callee)) => ctx
            .lifetime_eligibility
            .is_some_and(|eligibility| eligibility.thin_return_permit(*callee)),
        Some(
            CallResultTarget::Indirect | CallResultTarget::Foreign | CallResultTarget::Unresolved,
        )
        | None => false,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeResultExpressionPlan {
    pub(crate) caller: LocalDefId,
    pub(crate) call_hir: HirId,
    pub(crate) call_span: Span,
    /// The enclosing initializer when the call sits inside a `let` initializer
    /// the receiving-local twin refused (`InitializerNotExactDirectCall`).
    pub(crate) covers_initializer: Option<Span>,
    pub(crate) callee: LocalDefId,
    pub(crate) source_interface: ReturnInterface,
    pub(crate) raw_result: RawTargetType,
    pub(crate) position: ResultPosition,
    pub(crate) spec: GlueSpec,
    pub(crate) temporary: String,
    pub(crate) mutable_temporary: bool,
    view: String,
}

impl NativeResultExpressionPlan {
    pub(crate) fn owner_class(&self) -> SignatureClassId {
        SignatureClassId::of(self.callee)
    }

    pub(crate) fn active(&self, classes: &std::collections::BTreeSet<SignatureClassId>) -> bool {
        !classes.contains(&self.owner_class())
    }

    pub(crate) fn bridge(&self) -> BridgeSitePlan {
        BridgeSitePlan {
            caller: self.caller,
            callee: BridgeCalleeId::Local(self.callee),
            arm: "c".into(),
            position: format!(
                "native-result-expression:{}:{}:{}:lifetime_plan={}",
                self.position.key(),
                self.caller.local_def_index.as_u32(),
                self.call_hir.local_id.as_u32(),
                self.source_interface.lifetime_plan_digest
            ),
            bridge_kind: "native-result-expression-raw".into(),
            expected_form: Form::Raw.key().into(),
            found_form: self.source_interface.form.key().into(),
            argument_kind: "return-call-result".into(),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::T2,
            waiver_id: Some(RAW_BOUNDARY_T2_WAIVER_ID.into()),
            unsafe_context: None,
        }
    }

    /// The input is the call after its own argument adapters; binding it once
    /// keeps the evaluation order of the original expression.
    pub(crate) fn render(&self, adapted_call: &str) -> String {
        format!(
            "{{ let {}{}: {} = ({adapted_call}); ({}) as {} }}",
            if self.mutable_temporary { "mut " } else { "" },
            self.temporary,
            self.source_interface.temporary_type(),
            self.view,
            self.raw_result.rendered
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NativeResultExpressionFailure {
    /// The result position is none of the served shapes.
    PositionUnbuilt(&'static str),
    ResultNotRawPointer,
    PointeePresentationMismatch,
    Depth2StorageUnbuilt,
    Template(RawBoundaryBlockReason),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeResultExpressionUnavailable {
    pub(crate) caller: LocalDefId,
    pub(crate) call_hir: HirId,
    pub(crate) call_span: Span,
    pub(crate) callee: LocalDefId,
    pub(crate) reason: NativeResultExpressionFailure,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct NativeResultExpressionPlans {
    pub(crate) plans: FxHashMap<(LocalDefId, HirId), NativeResultExpressionPlan>,
    pub(crate) unavailable: FxHashMap<(LocalDefId, HirId), NativeResultExpressionUnavailable>,
}

impl NativeResultExpressionPlans {
    /// A receiving-local refusal (`InitializerNotExactDirectCall`) whose
    /// initializer this carrier serves does not drop the class.
    pub(crate) fn covers_initializer(&self, initializer: Span) -> bool {
        self.plans
            .values()
            .any(|plan| plan.covers_initializer == Some(initializer))
    }
}

/// Where a call's result goes, read from its HIR parent chain.
enum Consumer {
    Position(ResultPosition, Option<Span>),
    /// A receiving local, a call argument, a return — other carriers' shapes.
    Elsewhere,
    Unbuilt(&'static str),
}

/// Whether the call sits inside a call argument at any depth of the enclosing
/// statement — the outbound-expression carrier's territory (it restores the
/// inner call's raw type there itself).
fn inside_call_argument(tcx: TyCtxt<'_>, call: &Expr<'_>) -> bool {
    let mut child = call.hir_id;
    loop {
        match tcx.parent_hir_node(child) {
            HirNode::Expr(expr) => {
                match expr.kind {
                    ExprKind::Call(callee, arguments)
                        if callee.hir_id != child
                            && arguments.iter().any(|argument| argument.hir_id == child) =>
                    {
                        return true;
                    }
                    ExprKind::MethodCall(_, receiver, arguments, _)
                        if receiver.hir_id != child
                            && arguments.iter().any(|argument| argument.hir_id == child) =>
                    {
                        return true;
                    }
                    ExprKind::Block(..) | ExprKind::Closure(..) => return false,
                    _ => {}
                }
                child = expr.hir_id;
            }
            _ => return false,
        }
    }
}

/// The receiving place of `place = callee(..)`, when it is a local: what the
/// decision table delivers it as. EXHAUSTIVE over the decision vocabulary so
/// a new form is placed on purpose.
enum AssignedPlace {
    /// Stays raw in the output (degraded or undecided): the carrier's.
    Raw,
    /// Another family constructs the place's form OVER the raw call (a
    /// sealed slice, an optional receiver, a cursor): the construction is
    /// rendered over this view.
    ConstructedElsewhere,
    /// A safe reference or box: assigning a raw view into it is unbuilt.
    Delivered,
}

fn assigned_place(table: &DecisionTable, owner: LocalDefId, lhs: &Expr<'_>) -> AssignedPlace {
    let ExprKind::Path(rustc_hir::QPath::Resolved(None, path)) = lhs.kind else {
        return AssignedPlace::Raw;
    };
    let rustc_hir::def::Res::Local(binding) = path.res else {
        return AssignedPlace::Raw;
    };
    assigned_place_of(table, owner, binding)
}

fn assigned_place_of(table: &DecisionTable, owner: LocalDefId, binding: HirId) -> AssignedPlace {
    let decision = table
        .entries
        .iter()
        .find(|(subject, _)| subject.fn_did == owner && subject.hir_id == binding)
        .map(|(_, decision)| decision);
    match decision {
        None | Some(Decision::Degraded(_)) => AssignedPlace::Raw,
        Some(
            Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. },
        ) => AssignedPlace::ConstructedElsewhere,
        Some(Decision::Ref { .. } | Decision::InferredRef { .. } | Decision::Box(_)) => {
            AssignedPlace::Delivered
        }
    }
}

fn consumer_of(tcx: TyCtxt<'_>, table: &DecisionTable, call: &Expr<'_>, form: Form) -> Consumer {
    if inside_call_argument(tcx, call) {
        return Consumer::Elsewhere;
    }
    let mut child = call.hir_id;
    let mut parent = tcx.parent_hir_node(child);
    // Peel parentheses and blocks that merely forward the value.
    loop {
        match parent {
            HirNode::Expr(expr) => match expr.kind {
                ExprKind::DropTemps(_) => {
                    child = expr.hir_id;
                    parent = tcx.parent_hir_node(child);
                }
                _ => break,
            },
            _ => break,
        }
    }
    match parent {
        HirNode::Expr(expr) => match expr.kind {
            // A thin `&T` / `&mut T` result dereferences as it stands; only a
            // slice or optional result needs its raw type back under `*`.
            ExprKind::Unary(rustc_hir::UnOp::Deref, operand) if operand.hir_id == child => {
                match form {
                    Form::Ref { .. } => Consumer::Elsewhere,
                    Form::Slice { .. } | Form::Opt { .. } => {
                        Consumer::Position(ResultPosition::Deref, None)
                    }
                    Form::NestedSlice { .. } | Form::Cursor { .. } | Form::Raw => {
                        Consumer::Unbuilt("deref-of-unsupported-form")
                    }
                }
            }
            ExprKind::Cast(operand, _) if operand.hir_id == child => {
                // The cast may itself be a `let` initializer the receiving
                // twin refused: record that initializer so its refusal does
                // not drop the class.
                let covers = match tcx.parent_hir_node(expr.hir_id) {
                    HirNode::LetStmt(local)
                        if local.init.is_some_and(|init| init.hir_id == expr.hir_id) =>
                    {
                        Some(expr.span)
                    }
                    _ => None,
                };
                Consumer::Position(ResultPosition::Cast, covers)
            }
            ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == child => {
                if !matches!(
                    tcx.typeck(expr.hir_id.owner.def_id).expr_ty(lhs).kind(),
                    TyKind::RawPtr(..)
                ) {
                    return Consumer::Unbuilt("assign-to-non-raw-place");
                }
                // The place's OUTPUT form decides: a raw view may only be
                // assigned into a place that stays raw.
                match assigned_place(table, expr.hir_id.owner.def_id, lhs) {
                    // A place another family constructs OVER the raw call
                    // (an optional store) takes its construction over this
                    // view: the AST pass composes the outer store over the
                    // re-rendered call (`UseGraftVisitor`, wave-6l).
                    AssignedPlace::Raw | AssignedPlace::ConstructedElsewhere => {
                        Consumer::Position(ResultPosition::Assign, None)
                    }
                    AssignedPlace::Delivered => Consumer::Unbuilt("assign-to-delivered-place"),
                }
            }
            // An argument position is the outbound-expression carrier's; the
            // RECEIVER of a method call (`callee(..).is_null()`) is not served.
            ExprKind::Call(..) => Consumer::Elsewhere,
            ExprKind::MethodCall(_, receiver, ..) if receiver.hir_id == child => {
                Consumer::Unbuilt("method-receiver")
            }
            ExprKind::MethodCall(..) => Consumer::Elsewhere,
            ExprKind::Ret(_) => Consumer::Elsewhere,
            ExprKind::Block(..) => Consumer::Elsewhere,
            ExprKind::Field(..) => Consumer::Unbuilt("field-of-result"),
            ExprKind::Index(..) => Consumer::Unbuilt("index-of-result"),
            ExprKind::Binary(..) => Consumer::Unbuilt("binary-operand"),
            ExprKind::AssignOp(..) => Consumer::Unbuilt("assign-op-operand"),
            ExprKind::AddrOf(..) => Consumer::Unbuilt("address-of-result"),
            ExprKind::If(..) | ExprKind::Match(..) => Consumer::Unbuilt("condition-or-scrutinee"),
            _ => Consumer::Unbuilt("other-expression"),
        },
        // The receiving local's own twin types a thin or optional result;
        // a local a sealed constructor types over the RAW call takes this
        // view under the constructor (the initializer-channel composition)
        // when the return is thin — a slice or optional return reaches its
        // receiving local through the return receiver.
        HirNode::LetStmt(local) => match (local.pat.kind, form) {
            (rustc_hir::PatKind::Binding(_, binding, ..), Form::Ref { .. })
                if matches!(
                    assigned_place_of(table, call.hir_id.owner.def_id, binding),
                    AssignedPlace::ConstructedElsewhere
                ) =>
            {
                Consumer::Position(ResultPosition::Initializer, None)
            }
            (_, Form::Ref { .. } | Form::Slice { .. } | Form::Opt { .. }) => Consumer::Elsewhere,
            (_, Form::NestedSlice { .. } | Form::Cursor { .. } | Form::Raw) => Consumer::Elsewhere,
        },
        HirNode::Stmt(_) => Consumer::Unbuilt("discarded-result"),
        _ => Consumer::Elsewhere,
    }
}

struct Calls<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    table: &'a DecisionTable,
    found: Vec<(&'tcx Expr<'tcx>, LocalDefId)>,
}

impl<'tcx> Visitor<'tcx> for Calls<'_, 'tcx> {
    fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
        if let ExprKind::Call(callee, _) = expression.kind
            && let TyKind::FnDef(definition, _) = *self
                .tcx
                .typeck(expression.hir_id.owner.def_id)
                .expr_ty(callee)
                .kind()
            && let Some(definition) = definition.as_local()
            && self
                .table
                .return_interfaces
                .functions
                .get(&definition)
                .is_some_and(|interface| interface.form != Form::Raw)
        {
            self.found.push((expression, definition));
        }
        walk_expr(self, expression);
    }
}

pub(crate) fn plan(
    program: &RustProgram<'_>,
    table: &DecisionTable,
) -> NativeResultExpressionPlans {
    let tcx = program.tcx;
    let mut out = NativeResultExpressionPlans::default();
    for &caller in &program.functions {
        let mut calls = Calls {
            tcx,
            table,
            found: Vec::new(),
        };
        calls.visit_expr(tcx.hir_body_owned_by(caller).value);
        for (call, callee) in calls.found {
            let key = (caller, call.hir_id);
            let interface = &table.return_interfaces.functions[&callee];
            let unavailable = |reason| NativeResultExpressionUnavailable {
                caller,
                call_hir: call.hir_id,
                call_span: call.span,
                callee,
                reason,
            };
            let (position, covers_initializer) = match consumer_of(tcx, table, call, interface.form)
            {
                Consumer::Position(position, covers) => (position, covers),
                Consumer::Elsewhere => continue,
                Consumer::Unbuilt(shape) => {
                    out.unavailable.insert(
                        key,
                        unavailable(NativeResultExpressionFailure::PositionUnbuilt(shape)),
                    );
                    continue;
                }
            };
            let Some(raw_result) =
                raw_boundary::raw_target_type(tcx, tcx.typeck(caller).expr_ty(call))
            else {
                out.unavailable.insert(
                    key,
                    unavailable(NativeResultExpressionFailure::ResultNotRawPointer),
                );
                continue;
            };
            if raw_result.pointee != interface.pointee {
                out.unavailable.insert(
                    key,
                    unavailable(NativeResultExpressionFailure::PointeePresentationMismatch),
                );
                continue;
            }
            if raw_result.depth2.is_some() {
                out.unavailable.insert(
                    key,
                    unavailable(NativeResultExpressionFailure::Depth2StorageUnbuilt),
                );
                continue;
            }
            let Some(source) = seam::decision_for_safe_form(interface.form) else {
                out.unavailable.insert(
                    key,
                    unavailable(NativeResultExpressionFailure::Template(
                        RawBoundaryBlockReason::TemplateUnavailable,
                    )),
                );
                continue;
            };
            let selected =
                raw_boundary::template_for(&source, &raw_result, None, false).and_then(|base| {
                    raw_boundary::returned_child_template(&source, &raw_result, None, base)
                });
            let selected = match selected {
                Ok(selected) => selected,
                Err(reason) => {
                    out.unavailable.insert(
                        key,
                        unavailable(NativeResultExpressionFailure::Template(reason)),
                    );
                    continue;
                }
            };
            let mut spec =
                GlueSpec::raw_boundary(selected.template, raw_result.mutability, false, true);
            if let Some(raw) = spec.raw_boundary.as_mut() {
                raw.cast_pointee = Some(raw_result.pointee.clone());
            }
            let temporary = format!(
                "__crat_native_result_{}_{}",
                caller.local_def_index.as_u32(),
                call.hir_id.local_id.as_u32()
            );
            let Some(view) = spec.render(&temporary) else {
                out.unavailable.insert(
                    key,
                    unavailable(NativeResultExpressionFailure::Template(
                        RawBoundaryBlockReason::TemplateUnavailable,
                    )),
                );
                continue;
            };
            let mutable_temporary = match interface.form {
                Form::NestedSlice { .. } | Form::Cursor { .. } | Form::Raw => continue,
                Form::Opt { mutable, .. } => mutable,
                Form::Ref { .. } | Form::Slice { .. } => selected.mutable_binding_required,
            };
            out.plans.insert(
                key,
                NativeResultExpressionPlan {
                    caller,
                    call_hir: call.hir_id,
                    call_span: call.span,
                    covers_initializer,
                    callee,
                    source_interface: interface.clone(),
                    raw_result,
                    position,
                    spec,
                    temporary,
                    mutable_temporary,
                    view,
                },
            );
        }
    }
    out
}

/// Which subject kinds a call-result subject local can have — kept exhaustive
/// for the receiving-local exclusion the planner relies on.
pub(crate) fn is_receiving_local(kind: SubjectKind) -> bool {
    match kind {
        SubjectKind::Local => true,
        SubjectKind::Param { .. } => false,
    }
}
