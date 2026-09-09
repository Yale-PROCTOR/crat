//! Sealed alternatives for reverting one callee parameter to its input form.
//! Selection consumes only class/atom custody; proof and syntax work stays here.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::FxHashMap;
use rustc_hir::{
    Expr, ExprKind, HirId, QPath,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{
    Decision, DecisionTable, SubjectKind,
    emitability::{Arg, ArgShape, EmitabilityFacts},
    raw_boundary::{self, RawBoundaryDisposition, RawBoundaryDispositionIndex},
    seam::{self, Form, GlueSpec, SeamFamily, SeamInputRendering, SeamPlan},
};
use crate::bo_rewriter::bridge_receipt::{
    BridgeCalleeId, BridgeExtentKind, BridgeRetentionTier, BridgeSitePlan, SignatureClassId,
};

pub(crate) type Key = (SignatureClassId, u32, u32);
pub(crate) type InputPlans = BTreeMap<Key, CalleeParameterInput>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SeamAlternative {
    pub(crate) rendering: SeamInputRendering,
    pub(crate) arg_span: Span,
    pub(crate) bridge: Option<BridgeSitePlan>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CalleeParameterInput {
    pub(crate) caller: LocalDefId,
    pub(crate) node: (LocalDefId, HirId),
    pub(crate) input_form: Form,
    pub(crate) source_node: Option<(LocalDefId, HirId)>,
    pub(crate) target_atom_ids: Vec<String>,
    pub(crate) source_atom_ids: Vec<String>,
    pub(crate) current_source: Result<SeamAlternative, &'static str>,
    pub(crate) input_source: Result<SeamAlternative, &'static str>,
    /// Metadata for the existing source-input AST carrier while the callee
    /// parameter keeps its decided interface. No new rendering is derived.
    pub(crate) kept_target_input_source: Option<SeamAlternative>,
    /// Direct return producers whose original interfaces are needed by the
    /// original argument. The consumer's owned closure restores these first.
    pub(crate) input_source_required_classes: BTreeSet<SignatureClassId>,
    /// Unknown restoration shapes must refuse the target's safe-interface
    /// planning before finalization, not become an AST-time guess.
    pub(crate) preflight_hold: Option<&'static str>,
}

impl CalleeParameterInput {
    pub(crate) fn source_is_input(
        &self,
        classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> bool {
        classes.contains(&SignatureClassId::of(self.caller))
            || self.source_atom_ids.iter().any(|atom| atoms.contains(atom))
    }

    pub(crate) fn select<'a>(
        &'a self,
        classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Option<Result<&'a SeamAlternative, &'static str>> {
        let target_input = classes.contains(&SignatureClassId::of(self.node.0))
            || self.target_atom_ids.iter().any(|atom| atoms.contains(atom));
        if !target_input {
            return None;
        }
        let source_input = self.source_is_input(classes, atoms);
        Some(if source_input {
            if !self.input_source_required_classes.is_subset(classes) {
                Err("callee-parameter-input-source-return-interface-live")
            } else {
                self.input_source.as_ref().map_err(|reason| *reason)
            }
        } else {
            self.current_source.as_ref().map_err(|reason| *reason)
        })
    }

    /// Owners needed when a selected alternative is unavailable. This is
    /// dependency transport, not a decision/model recomputation.
    pub(crate) fn unavailable_owners(&self) -> BTreeSet<SignatureClassId> {
        let mut owners = self.input_source_required_classes.clone();
        owners.insert(SignatureClassId::of(self.caller));
        if self.preflight_hold.is_some() {
            owners.insert(SignatureClassId::of(self.node.0));
        }
        owners
    }
}

fn expressions<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
) -> FxHashMap<(u32, u32), Vec<&'tcx Expr<'tcx>>> {
    struct V<'tcx>(FxHashMap<(u32, u32), Vec<&'tcx Expr<'tcx>>>);
    impl<'tcx> Visitor<'tcx> for V<'tcx> {
        fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
            if !matches!(expression.kind, ExprKind::DropTemps(_)) {
                self.0
                    .entry((expression.span.lo().0, expression.span.hi().0))
                    .or_default()
                    .push(expression);
            }
            intravisit::walk_expr(self, expression);
        }
    }
    let mut visitor = V(FxHashMap::default());
    visitor.visit_body(tcx.hir_body_owned_by(caller));
    visitor.0
}

fn stable_array_pointer(tcx: TyCtxt<'_>, expression: &Expr<'_>) -> bool {
    let typeck = tcx.typeck(expression.hir_id.owner.def_id);
    let mut expression = expression;
    while let ExprKind::Cast(inner, _) = expression.kind {
        if !typeck.expr_ty(inner).is_raw_ptr() || !typeck.expr_ty(expression).is_raw_ptr() {
            return false;
        }
        expression = inner;
    }
    let ExprKind::MethodCall(segment, receiver, args, _) = expression.kind else { return false };
    let ExprKind::Path(QPath::Resolved(_, path)) = receiver.kind else { return false };
    if !matches!(path.res, Res::Local(_))
        || !matches!(typeck.expr_ty(receiver).kind(), TyKind::Array(..))
        || !matches!(segment.ident.name.as_str(), "as_ptr" | "as_mut_ptr")
        || !args.is_empty()
    {
        return false;
    }
    typeck
        .type_dependent_def_id(expression.hir_id)
        .is_some_and(|callee| tcx.crate_name(callee.krate).as_str() == "core")
        && typeck.expr_ty(expression).is_raw_ptr()
}

fn return_dependencies<'tcx>(
    tcx: TyCtxt<'tcx>,
    expression: &'tcx Expr<'tcx>,
    table: &DecisionTable,
) -> BTreeSet<SignatureClassId> {
    struct V<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        table: &'a DecisionTable,
        owners: BTreeSet<SignatureClassId>,
    }
    impl<'tcx> Visitor<'tcx> for V<'_, 'tcx> {
        fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
            let typeck = self.tcx.typeck(expression.hir_id.owner.def_id);
            let callee = match expression.kind {
                ExprKind::Call(callee, _) => match typeck.expr_ty(callee).kind() {
                    TyKind::FnDef(callee, _) => callee.as_local(),
                    _ => None,
                },
                ExprKind::MethodCall(..) => typeck
                    .type_dependent_def_id(expression.hir_id)
                    .and_then(|callee| callee.as_local()),
                _ => None,
            };
            if let Some(callee) = callee
                && self.table.return_interfaces.functions.contains_key(&callee)
            {
                self.owners.insert(SignatureClassId::of(callee));
            }
            if let ExprKind::Path(QPath::Resolved(_, path)) = expression.kind
                && let Res::Local(binding) = path.res
            {
                let node = (expression.hir_id.owner.def_id, binding);
                if let Some(receiver) = self.table.return_receivers.plans.get(&node) {
                    self.owners.insert(SignatureClassId::of(receiver.callee));
                }
                if let Some((_, decision)) = self
                    .table
                    .entries
                    .iter()
                    .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)
                {
                    match decision {
                        Decision::InferredRef { callee, .. } => {
                            self.owners.insert(SignatureClassId::of(*callee));
                        }
                        Decision::Ref { .. }
                        | Decision::Slice { .. }
                        | Decision::Opt { .. }
                        | Decision::Box(_)
                        | Decision::Degraded(_) => {}
                    }
                }
            }
            intravisit::walk_expr(self, expression);
        }
    }
    let mut visitor = V {
        tcx,
        table,
        owners: BTreeSet::new(),
    };
    visitor.visit_expr(expression);
    visitor.owners
}

fn zero(arg: &Arg, found: Form) -> SeamAlternative {
    SeamAlternative {
        rendering: SeamInputRendering::ZeroSyntax { found },
        arg_span: arg.span,
        bridge: None,
    }
}

fn kept_target_source_receipt(
    tcx: TyCtxt<'_>,
    seams: &SeamPlan,
    caller: LocalDefId,
    callee: LocalDefId,
    arg: &Arg,
    expected: Form,
) -> Option<SeamAlternative> {
    let owner = SignatureClassId::of(callee);
    let ordinary = seams
        .edits
        .iter()
        .filter(|edit| {
            edit.owner_class == owner
                && edit.span == arg.span
                && edit.bridge.caller == caller
                && edit.source_node.is_some_and(|node| node.0 == caller)
                && edit.bridge.callee == BridgeCalleeId::Local(callee)
                && matches!(edit.bridge.arm.as_str(), "c" | "glue")
        })
        .filter_map(|edit| {
            edit.input_rendering
                .as_ref()
                .map(|input| (edit.arg_span, input))
        });
    let identities = seams
        .revert_found_form_edits
        .iter()
        .filter(|edit| {
            edit.owner_class == owner && edit.span == arg.span && edit.source_node.0 == caller
        })
        .map(|edit| (edit.arg_span, &edit.input));
    let candidates = ordinary.chain(identities).collect::<Vec<_>>();
    let [(arg_span, rendering)] = candidates.as_slice() else { return None };
    let (found, kind, extent, retention, waiver_id, unsafe_context) = match rendering {
        SeamInputRendering::ZeroSyntax { found } => (
            *found,
            "source-input:zero-syntax".to_owned(),
            BridgeExtentKind::None,
            BridgeRetentionTier::None,
            None,
            None,
        ),
        SeamInputRendering::Adapter {
            found,
            spec,
            retention,
            waiver_id,
            ..
        } => (
            *found,
            format!("source-input:{}", spec.template_key()),
            seam::receipt_extent(spec),
            *retention,
            waiver_id.clone(),
            seam::unsafe_context_for(tcx, caller, spec),
        ),
    };
    Some(SeamAlternative {
        rendering: (*rendering).clone(),
        arg_span: *arg_span,
        bridge: Some(BridgeSitePlan {
            caller,
            callee: BridgeCalleeId::Local(callee),
            arm: seam::receipt_arm(expected, found).to_owned(),
            position: format!("arg{}", arg.index),
            bridge_kind: kind,
            expected_form: expected.key().to_owned(),
            found_form: found.key().to_owned(),
            argument_kind: arg.shape.key().to_owned(),
            extent,
            retention,
            waiver_id,
            unsafe_context,
        }),
    })
}

fn current_alternative(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    raw: &RawBoundaryDispositionIndex,
    caller: LocalDefId,
    callee: LocalDefId,
    call_span: Span,
    arg: &Arg,
    expression: Option<&Expr<'_>>,
    found: Form,
    input_form: Form,
) -> Result<SeamAlternative, &'static str> {
    if input_form != Form::Raw {
        return Err("callee-parameter-input-native-target-unbuilt");
    }
    if matches!(arg.shape, ArgShape::RawExpr { .. })
        && !expression.is_some_and(|expression| stable_array_pointer(tcx, expression))
    {
        return Err("callee-parameter-input-raw-expression-not-proven-stable");
    }
    if matches!(arg.shape, ArgShape::Other | ArgShape::Cast { .. }) {
        return Err("callee-parameter-input-source-shape-unbuilt");
    }
    if let Some(root) = arg.shape.place_root()
        && table.entries.iter().any(|(subject, decision)| {
            subject.fn_did == caller
                && subject.hir_id == root
                && match decision {
                    Decision::Box(_) | Decision::InferredRef { .. } => true,
                    Decision::Ref { .. }
                    | Decision::Slice { .. }
                    | Decision::Opt { .. }
                    | Decision::Degraded(_) => false,
                }
        })
    {
        return Err("callee-parameter-input-owned-or-inferred-source-unbuilt");
    }
    if found == Form::Raw {
        return Ok(zero(arg, found));
    }
    let matches = raw
        .inventoried_sites()
        .filter(|(key, _, site)| {
            site.callee_local == Some(callee)
                && key.caller == tcx.def_path_str(caller.to_def_id())
                && key.argument_index == arg.index
                && site.call_span == call_span
                && site.span == arg.span
        })
        .collect::<Vec<_>>();
    let [(key, disposition, site)] = matches.as_slice() else {
        return Err("callee-parameter-input-raw-boundary-evidence-unavailable");
    };
    let (retention, waiver_id) = match disposition {
        RawBoundaryDisposition::T1 { .. } => (BridgeRetentionTier::T1, None),
        RawBoundaryDisposition::T2 { waiver_id, .. } => {
            (BridgeRetentionTier::T2, Some((*waiver_id).to_owned()))
        }
        RawBoundaryDisposition::Blocked { .. } | RawBoundaryDisposition::OwnedByOtherArm { .. } => {
            return Err("callee-parameter-input-raw-boundary-held");
        }
    };
    let source = seam::decision_for_safe_form(found)
        .ok_or("callee-parameter-input-source-form-unavailable")?;
    let child = raw.returned_child_evidence(key);
    seam::terminal_returned_child_permission(child, arg.shape.key(), found)
        .map_err(|_| "callee-parameter-input-returned-child-permission")?;
    let mut template = raw_boundary::template_for(
        &source,
        &site.target,
        None,
        raw.negative_write_evidence(key).is_some(),
    )
    .map_err(|_| "callee-parameter-input-raw-view-unavailable")?;
    if let Some(child) =
        child.filter(|child| !(child.raw_field_parent && arg.shape.key() == "raw-expr"))
    {
        let selected = raw_boundary::returned_child_template(
            &source,
            &site.target,
            child.child.as_ref().ok().map(|child| &child.access),
            template,
        )
        .map_err(|_| "callee-parameter-input-returned-child-template")?;
        if selected.mutable_binding_required
            && !arg
                .shape
                .place_root()
                .is_some_and(|root| table.option_mut_bindings.contains(&(caller, root)))
        {
            return Err("callee-parameter-input-mutable-binding-unplanned");
        }
        template = selected.template;
    }
    let spec = GlueSpec::raw_boundary_target(template, &site.target, false, true);
    let arg_span = site
        .direct_storage_span
        .unwrap_or(site.adapter_operand_span);
    let text = tcx
        .sess
        .source_map()
        .span_to_snippet(arg_span)
        .map_err(|_| "callee-parameter-input-operand-unplaceable")?;
    let unsafe_fn = tcx
        .fn_sig(caller.to_def_id())
        .skip_binder()
        .skip_binder()
        .safety
        .is_unsafe();
    let replacement = spec
        .render_in_context(&text, unsafe_fn)
        .ok_or("callee-parameter-input-raw-view-unrenderable")?;
    let bridge = BridgeSitePlan {
        caller,
        callee: BridgeCalleeId::Local(callee),
        arm: "c".into(),
        position: format!("arg{}", arg.index),
        bridge_kind: template.key().into(),
        expected_form: input_form.key().into(),
        found_form: found.key().into(),
        argument_kind: arg.shape.key().into(),
        extent: BridgeExtentKind::None,
        retention,
        waiver_id: waiver_id.clone(),
        unsafe_context: seam::unsafe_context_for(tcx, caller, &spec),
    };
    Ok(SeamAlternative {
        rendering: SeamInputRendering::Adapter {
            replacement,
            spec,
            family: SeamFamily::Safe,
            found,
            len_arm: None,
            retention,
            waiver_id,
        },
        arg_span,
        bridge: Some(bridge),
    })
}

pub(crate) fn plan(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    facts: &EmitabilityFacts,
    seams: &SeamPlan,
    raw: &RawBoundaryDispositionIndex,
) -> InputPlans {
    let decisions = table
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect::<FxHashMap<_, _>>();
    let mut expression_maps = FxHashMap::default();
    let mut result = InputPlans::new();
    for (&callee, calls) in &facts.call_args {
        for call in calls {
            let expressions = expression_maps
                .entry(call.caller)
                .or_insert_with(|| expressions(tcx, call.caller));
            for arg in &call.args {
                let owner = SignatureClassId::of(callee);
                // PAIR/A5 whole-call carriers own their own input alternatives.
                // This carrier governs ordinary argument adapters and their
                // explicit identity receipts only.
                let ordinary = seams.edits.iter().any(|edit| {
                    edit.owner_class == owner
                        && edit.span == arg.span
                        && edit.param_index == arg.index
                        && edit.bridge.caller == call.caller
                        && edit.bridge.callee == BridgeCalleeId::Local(callee)
                        && matches!(edit.bridge.arm.as_str(), "c" | "glue")
                        && edit.bridge.position == format!("arg{}", arg.index)
                }) || seams.zero_bridges.iter().any(|site| {
                    site.owner_class == owner
                        && site.caller == call.caller
                        && site.span == Some(arg.span)
                        && matches!(site.arm, "c" | "glue")
                        && site.bridge_kind == "interface-call-zero-syntax"
                });
                if !ordinary {
                    continue;
                }
                let Some((parameter, choice)) = table.entries.iter().find(|(subject, _)| subject.fn_did == callee
                    && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == arg.index)) else { continue };
                let expected = match choice {
                    Decision::Ref { .. }
                    | Decision::InferredRef { .. }
                    | Decision::Slice { .. }
                    | Decision::Opt { .. } => seam::form_of(choice),
                    Decision::Box(_) | Decision::Degraded(_) => continue,
                };
                let input_form = *table
                    .input_interfaces
                    .parameter_forms
                    .get(&(callee, arg.index))
                    .expect("settled callee parameter has its original input interface");
                if input_form == expected {
                    continue;
                }
                let node = (parameter.fn_did, parameter.hir_id);
                let source_node = arg.shape.place_root().map(|root| (call.caller, root));
                let expression_candidates = expressions.get(&(arg.span.lo().0, arg.span.hi().0));
                let expression = expression_candidates.and_then(|found| match found.as_slice() {
                    [expression] => Some(*expression),
                    _ => None,
                });
                let input_subject = source_node
                    .and_then(|node| table.input_interfaces.subject_forms.get(&node))
                    .copied()
                    .unwrap_or(Form::Raw);
                let input_found = seam::a5_argument_expression_form(arg.shape.key(), input_subject)
                    .unwrap_or(Form::Raw);
                let found = seam::argument_form(call.caller, &arg.shape, &decisions);
                let required = expression_candidates
                    .into_iter()
                    .flatten()
                    .flat_map(|expression| return_dependencies(tcx, expression, table))
                    .collect();
                // The caller owns local/parameter presentation and body-use
                // edits. Once it and every referenced changed return producer
                // are restored, this exact original HIR argument retains its
                // original type (including native raw-pointer coercions).
                let input_source = if expression_candidates.is_some_and(|found| !found.is_empty()) {
                    Ok(zero(arg, input_found))
                } else {
                    Err("callee-parameter-input-original-expression-unlocated")
                };
                let current_source = current_alternative(
                    tcx,
                    table,
                    raw,
                    call.caller,
                    callee,
                    call.span,
                    arg,
                    expression,
                    found,
                    input_form,
                );
                let atoms = |node| {
                    seams
                        .raw_boundary_atom_groups
                        .get(&node)
                        .into_iter()
                        .flatten()
                        .map(|atom| atom.id.clone())
                        .collect::<Vec<_>>()
                };
                let key = (
                    SignatureClassId::of(callee),
                    arg.span.lo().0,
                    arg.span.hi().0,
                );
                let entry = CalleeParameterInput {
                    caller: call.caller,
                    node,
                    input_form,
                    source_node,
                    target_atom_ids: atoms(node),
                    source_atom_ids: source_node.map(atoms).unwrap_or_default(),
                    preflight_hold: input_source.as_ref().err().copied(),
                    current_source,
                    input_source,
                    kept_target_input_source: kept_target_source_receipt(
                        tcx,
                        seams,
                        call.caller,
                        callee,
                        arg,
                        expected,
                    ),
                    input_source_required_classes: required,
                };
                if let Some(previous) = result.get_mut(&key) {
                    previous.current_source = Err("callee-parameter-input-ambiguous-site");
                    previous.input_source = Err("callee-parameter-input-ambiguous-site");
                    previous.preflight_hold = Some("callee-parameter-input-ambiguous-site");
                    previous.target_atom_ids.extend(entry.target_atom_ids);
                    previous.source_atom_ids.extend(entry.source_atom_ids);
                } else {
                    result.insert(key, entry);
                }
            }
        }
    }
    result
}
