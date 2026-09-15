//! **wave-6a rule W6A-C1 — Box parameters of consuming callees under the
//! closed world.** (charter wave-6a/001 §1(c); seat addendum 400, R400-3)
//!
//! A local callee that FREES its raw parameter `p` exactly once, and uses it
//! otherwise only through derefs / element accesses, takes `Box<T>` (or
//! `Box<[T]>`) when EVERY call site in the crate — direct calls; the
//! closed-world attestation makes them enumerable — passes an allocation
//! local the ordinary Box arm plans, and never uses that local afterwards.
//! The chain is planned whole: each caller local's plan is the ordinary Box
//! plan with the transfer's boundary hold lifted (the move IS the transfer, so
//! the local has a retained sink and no scope-exit close); the callee's plan
//! turns `free(p)` into `drop(p)` and each `*p.offset(e)` into
//! `p[(e) as usize]`. Drops stay at C free sites; the leak-parity waiver is
//! not widened (no implicit close is added anywhere).
//!
//! Every other shape is a typed hold on the parameter, replacing the untyped
//! `box-param-caller-unknown`:
//! `box-param-callee-lends:<callee>` — the callee never frees the formal (a
//! lend; ownership-fields' `FormalForm`, not a Box);
//! `box-param-no-callers:<callee>` — nothing in the program calls it;
//! `box-param-indirect-callers:<callee>` — the function's address is taken;
//! `box-param-callee-use:<callee>:<form>` — a use of the formal this rule
//! does not rewrite (a second free, a store, a call argument, a return);
//! `box-param-caller-retains:<caller>:{not-a-local|not-an-allocation|
//! unplanned-argument:<failure>|other-call-use|used-after-transfer}`;
//! `box-param-model:<subject>:<kind>` — a chain member the model does not
//! call Owning; `box-param-shape:<detail>` — the callers' allocations do not
//! agree on one shape.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, QPath,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{
    Ctx, Decision, DecisionTable, Subject, SubjectKind,
    box_facts::{BoxExprEdit, BoxOwnershipFacts, BoxPlan, BoxPlanFailure, BoxShape},
    construction::{Construction, ConstructionFacts},
    declaration::pointee_source,
    emitability::UseEdit,
    seam::ExplicitDeclarationSite,
};
use crate::{
    analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef},
    bo_rewriter::bridge_receipt::SignatureClassId,
};

#[derive(Clone, Debug, Default)]
pub(crate) struct Chains {
    /// Every subject a chain plans: (function, binding) → plan.
    pub(crate) plans: FxHashMap<(LocalDefId, HirId), BoxPlan>,
    /// Parameters examined and refused: binding → (label, typed reason).
    pub(crate) holds: FxHashMap<(LocalDefId, HirId), (String, String)>,
    /// One receipt line per admitted chain.
    pub(crate) receipts: Vec<String>,
}

impl Chains {
    pub(crate) fn receipts_tsv(&self) -> String {
        let mut out = String::from("parameter\tkind\tdetail\n");
        for receipt in &self.receipts {
            out.push_str(&format!("-\tadmitted\t{receipt}\n"));
        }
        let mut holds: Vec<&(String, String)> = self.holds.values().collect();
        holds.sort();
        for (parameter, hold) in holds {
            out.push_str(&format!("{parameter}\theld\t{hold}\n"));
        }
        out
    }
}

/// Decision-phase hook, after the flexible-tail one: a prior parameter /
/// boundary hold on a chain member is replaced by the chain's plan; a prior
/// parameter hold on an examined parameter carries the typed reason.
pub(crate) fn override_plan(
    ctx: &Ctx<'_, '_>,
    subject: &Subject,
    prior: Result<BoxPlan, BoxPlanFailure>,
) -> Result<BoxPlan, BoxPlanFailure> {
    match prior {
        Ok(plan) => Ok(plan),
        Err(failure @ (BoxPlanFailure::ParameterHeld | BoxPlanFailure::BoundaryHeld)) => {
            if let Some(plan) = ctx.box_params.plans.get(&(subject.fn_did, subject.hir_id)) {
                return Ok(plan.clone());
            }
            if matches!(failure, BoxPlanFailure::ParameterHeld)
                && let Some((_, hold)) = ctx.box_params.holds.get(&(subject.fn_did, subject.hir_id))
            {
                return Err(BoxPlanFailure::NativeEvidenceHeld {
                    prior_key: typed_key(hold),
                    detail: hold.to_owned(),
                });
            }
            Err(failure)
        }
        Err(failure) => Err(failure),
    }
}

/// After the decisions: a chain member planned on an unannotated binding gets
/// its `Box<..>` declaration spelled out (the custody instrument reads only
/// explicit types), exactly as W6A-B1 does for its slice locals.
pub(crate) fn append_explicit_declarations(tcx: TyCtxt<'_>, table: &mut DecisionTable) {
    let mut sites = Vec::new();
    for (subject, decision) in &table.entries {
        let node = (subject.fn_did, subject.hir_id);
        let plan = match decision {
            Decision::Box(plan) => plan,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Opt { .. }
            | Decision::Degraded(_) => continue,
        };
        if !plan.inferred_binding
            || !table.box_params.plans.contains_key(&node)
            || subject.ty_span.is_some()
        {
            continue;
        }
        let Some(name) = subject.param_name.as_deref() else { continue };
        if table
            .seams
            .explicit_declarations
            .iter()
            .any(|site| site.category == "local" && site.node == Some(node))
        {
            continue;
        }
        let binding_type = tcx.typeck(subject.fn_did).node_type(subject.hir_id);
        let TyKind::RawPtr(pointee, _) = binding_type.kind() else { continue };
        let element = pointee_source(tcx, *pointee);
        let emitted_type = match plan.shape {
            BoxShape::Sized => format!("Box<{element}>"),
            BoxShape::Slice => format!("Box<[{element}]>"),
        };
        sites.push(ExplicitDeclarationSite {
            owner_class: SignatureClassId::of(subject.fn_did),
            caller: subject.fn_did,
            node: Some(node),
            span: Some(subject.binding_span),
            category: "local",
            replacement: Some(format!("{name}: {emitted_type}")),
            emitted_type,
            arm: "surface",
        });
    }
    table.seams.explicit_declarations.extend(sites);
}

/// The hold's family as a stable reason key (the receipt keeps the detail).
fn typed_key(hold: &str) -> &'static str {
    const KEYS: [&str; 7] = [
        "box-param-callee-lends",
        "box-param-no-callers",
        "box-param-indirect-callers",
        "box-param-callee-use",
        "box-param-caller-retains",
        "box-param-model",
        "box-param-shape",
    ];
    KEYS.iter()
        .copied()
        .find(|key| hold.starts_with(key))
        .unwrap_or("box-param-caller-unknown")
}

fn peel_casts<'h>(mut e: &'h Expr<'h>) -> &'h Expr<'h> {
    while let ExprKind::Cast(inner, _) = &e.kind {
        e = inner;
    }
    e
}

fn bare_local(e: &Expr<'_>) -> Option<HirId> {
    match &peel_casts(e).kind {
        ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
            Res::Local(hir) => Some(hir),
            _ => None,
        },
        _ => None,
    }
}

fn foreign_fn(tcx: TyCtxt<'_>, did: DefId) -> bool {
    matches!(tcx.def_kind(did), DefKind::Fn)
        && did.as_local().is_some_and(|local| {
            matches!(
                tcx.hir_node_by_def_id(local),
                rustc_hir::Node::ForeignItem(_)
            )
        })
}

/// Everything one body tells the rule about its locals and calls.
#[derive(Default)]
struct Scan<'tcx> {
    tcx: Option<TyCtxt<'tcx>>,
    /// Bare-local occurrences with spans.
    local_uses: Vec<(HirId, Span)>,
    /// Direct calls of local functions: (callee, call span, bare-local args
    /// with their argument spans).
    calls: Vec<(DefId, Span, Vec<Option<(HirId, Span)>>)>,
    /// `free(x)` calls whose operand is a bare local: (local, call span,
    /// argument span).
    frees: Vec<(HirId, Span, Span)>,
    /// Local functions whose address is taken (a value, not a callee).
    fn_values: FxHashSet<DefId>,
}

impl<'tcx> Visitor<'tcx> for Scan<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx.expect("scan tcx")
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        match &e.kind {
            ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                Res::Local(hir) => self.local_uses.push((hir, e.span)),
                Res::Def(DefKind::Fn, did) if did.is_local() => {
                    self.fn_values.insert(did);
                }
                _ => {}
            },
            ExprKind::Call(callee, args) => {
                let callee_def = match &callee.kind {
                    ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                        Res::Def(DefKind::Fn, did) => Some(did),
                        _ => None,
                    },
                    _ => None,
                };
                match callee_def {
                    Some(did) if foreign_fn(self.tcx.expect("scan tcx"), did) => {
                        if self.tcx.expect("scan tcx").item_name(did).as_str() == "free"
                            && let [arg] = args
                            && let Some(hir) = bare_local(arg)
                        {
                            self.frees.push((hir, e.span, arg.span));
                        }
                    }
                    Some(did) if did.is_local() => {
                        self.calls.push((
                            did,
                            e.span,
                            args.iter()
                                .map(|arg| bare_local(arg).map(|hir| (hir, arg.span)))
                                .collect(),
                        ));
                    }
                    _ => {}
                }
                // The callee path is not a taken address; walk the arguments only.
                for arg in *args {
                    self.visit_expr(arg);
                }
                return;
            }
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }
}

/// The subject's uses as the slice-use collector sees them, with `boundaries`
/// (the free / the transfer call) its only admitted raw seams. `Err` names the
/// use form that is not a deref / element access.
fn slice_uses_of(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    boundaries: &[Span],
) -> Result<Vec<UseEdit>, String> {
    let key = (subject.fn_did, subject.hir_id);
    let name = subject.param_name.clone().unwrap_or_else(|| "?".to_owned());
    let names = FxHashMap::from_iter([(key, name)]);
    let mutable = FxHashSet::from_iter([key]);
    let boundary_arguments = boundaries
        .iter()
        .map(|span| (subject.fn_did, subject.hir_id, span.lo().0, span.hi().0))
        .collect::<FxHashSet<_>>();
    let uses = super::emitability::collect_slice_uses(
        tcx,
        &[subject.fn_did],
        &names,
        &mutable,
        &FxHashSet::default(),
        &boundary_arguments,
    );
    let Some(uses) = uses.get(&key) else {
        return Err("uses-uncollected".to_owned());
    };
    if let Some(span) = uses.unsupported {
        return Err(format!(
            "unsupported:{}",
            tcx.sess
                .source_map()
                .span_to_snippet(span)
                .unwrap_or_default()
        ));
    }
    if !uses.return_handoffs.is_empty() {
        return Err("returned".to_owned());
    }
    for raw in &uses.raw_uses {
        let admitted = raw
            .boundary_span
            .is_some_and(|b| boundaries.iter().any(|allowed| allowed.contains(b)));
        if !admitted {
            return Err(format!(
                "raw-use:{}",
                tcx.sess
                    .source_map()
                    .span_to_snippet(raw.span)
                    .unwrap_or_default()
            ));
        }
    }
    let mut rewrites = uses.rewrites.clone();
    rewrites.sort_by_key(|e| (e.span.lo(), e.span.hi()));
    if rewrites.windows(2).any(|w| w[0].span.hi() > w[1].span.lo()) {
        return Err("nested-element-access".to_owned());
    }
    Ok(rewrites)
}

/// Derive every chain for the crate. Runs once, before the family stages; the
/// model is read only to refuse a chain whose members are not all Owning.
pub(crate) fn derive<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    constructions: &ConstructionFacts,
    subjects: &[Subject],
    box_facts: &BoxOwnershipFacts,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> Chains {
    let mut out = Chains::default();
    let mut scans: FxHashMap<LocalDefId, Scan<'tcx>> = FxHashMap::default();
    for &function in functions {
        let mut scan = Scan {
            tcx: Some(tcx),
            ..Scan::default()
        };
        let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else { continue };
        scan.visit_body(tcx.hir_body(body_id));
        scans.insert(function, scan);
    }
    let fn_values: FxHashSet<DefId> = scans
        .values()
        .flat_map(|s| s.fn_values.iter().copied())
        .collect();
    let slot_of = |s: &Subject| {
        slots
            .fn_local_slots
            .get(&s.fn_did)
            .and_then(|u| u.slot_for_local_depth(s.local, 0))
            .map(|slot| SlotRef::Local(s.fn_did, slot))
    };
    let mut params: Vec<&Subject> = subjects
        .iter()
        .filter(|s| matches!(s.kind, SubjectKind::Param { .. }) && s.ptr_depth == 1)
        .collect();
    params.sort_by_key(|s| (s.fn_did.local_def_index.as_u32(), s.local.as_u32()));
    for param in params {
        let SubjectKind::Param { hir_index } = param.kind else { continue };
        let callee_path = tcx.def_path_str(param.fn_did.to_def_id());
        let Some(scan) = scans.get(&param.fn_did) else { continue };
        let frees: Vec<(Span, Span)> = scan
            .frees
            .iter()
            .filter(|(hir, _, _)| *hir == param.hir_id)
            .map(|(_, call, arg)| (*call, *arg))
            .collect();
        if frees.is_empty() {
            // Not a consumer: a lend. Only reported for an Owning-modeled formal
            // (the rows the Box arm holds today); a Ref/Raw formal is not (c).
            if slot_of(param).is_some_and(|slot| model.get(&slot) == Some(&SlotKind::Owning)) {
                out.holds.insert(
                    (param.fn_did, param.hir_id),
                    (
                        param.label.clone(),
                        format!("box-param-callee-lends:{callee_path}"),
                    ),
                );
            }
            continue;
        }
        let name = param.param_name.clone().unwrap_or_else(|| "?".to_owned());
        let hold = |reason: String, out: &mut Chains| {
            out.holds
                .insert((param.fn_did, param.hir_id), (param.label.clone(), reason));
        };
        if frees.len() != 1 {
            hold(
                format!("box-param-callee-use:{callee_path}:second-free"),
                &mut out,
            );
            continue;
        }
        // Every other use of the formal is a deref / element access the
        // slice-use collector rewrites; the free is its one raw boundary.
        let param_uses = match slice_uses_of(tcx, param, &[frees[0].1]) {
            Ok(uses) => uses,
            Err(form) => {
                hold(
                    format!("box-param-callee-use:{callee_path}:{form}"),
                    &mut out,
                );
                continue;
            }
        };
        if fn_values.contains(&param.fn_did.to_def_id()) {
            hold(
                format!("box-param-indirect-callers:{callee_path}"),
                &mut out,
            );
            continue;
        }
        // Every direct call site passes an allocation local, planned by the
        // ordinary Box arm with the transfer's boundary lifted, dead afterwards.
        let mut call_count = 0usize;
        let mut member_plans: Vec<((LocalDefId, HirId), BoxPlan, String, Vec<UseEdit>)> =
            Vec::new();
        let mut failure: Option<String> = None;
        let mut callers: Vec<(&LocalDefId, &Scan<'tcx>)> = scans.iter().collect();
        callers.sort_by_key(|(f, _)| f.local_def_index.as_u32());
        'callers: for (caller, caller_scan) in callers {
            let caller_path = tcx.def_path_str(caller.to_def_id());
            for (callee, call_span, args) in &caller_scan.calls {
                if *callee != param.fn_did.to_def_id() {
                    continue;
                }
                call_count += 1;
                let Some(Some((arg, arg_span))) = args.get(hir_index) else {
                    failure = Some(format!(
                        "box-param-caller-retains:{caller_path}:not-a-local"
                    ));
                    break 'callers;
                };
                let key = (*caller, *arg);
                let Some(local) = subjects.iter().find(|s| {
                    s.fn_did == *caller && s.hir_id == *arg && s.kind == SubjectKind::Local
                }) else {
                    failure = Some(format!(
                        "box-param-caller-retains:{caller_path}:not-a-local"
                    ));
                    break 'callers;
                };
                if !matches!(
                    constructions.by_binding.get(&key),
                    Some(Construction::Alloc { .. })
                ) {
                    failure = Some(format!(
                        "box-param-caller-retains:{caller_path}:not-an-allocation"
                    ));
                    break 'callers;
                }
                let Some(slot) = slot_of(local) else {
                    failure = Some(format!(
                        "box-param-caller-retains:{caller_path}:not-a-local"
                    ));
                    break 'callers;
                };
                if model.get(&slot) != Some(&SlotKind::Owning) {
                    failure = Some(format!(
                        "box-param-model:{}:{:?}",
                        local.label,
                        model.get(&slot)
                    ));
                    break 'callers;
                }
                // The transfer is the local's only call argument.
                let other_call = caller_scan.calls.iter().any(|(_, span, other_args)| {
                    span != call_span && other_args.iter().any(|a| a.map(|(h, _)| h) == Some(*arg))
                });
                if other_call {
                    failure = Some(format!(
                        "box-param-caller-retains:{caller_path}:other-call-use"
                    ));
                    break 'callers;
                }
                if caller_scan
                    .local_uses
                    .iter()
                    .any(|(hir, span)| *hir == *arg && span.lo() > call_span.hi())
                {
                    failure = Some(format!(
                        "box-param-caller-retains:{caller_path}:used-after-transfer"
                    ));
                    break 'callers;
                }
                let mut local_uses = match slice_uses_of(tcx, local, &[*arg_span]) {
                    Ok(uses) => uses,
                    Err(form) => {
                        failure = Some(format!(
                            "box-param-caller-retains:{caller_path}:owner-use:{form}"
                        ));
                        break 'callers;
                    }
                };
                let plan = box_facts.without_boundary_hold(slot).plan_for_subject(
                    tcx,
                    local,
                    slot,
                    constructions,
                    slots,
                    subjects,
                );
                match plan {
                    Ok(mut plan) => {
                        if plan.optional {
                            failure = Some(format!(
                                "box-param-caller-retains:{caller_path}:optional-owner"
                            ));
                            break 'callers;
                        }
                        // The move at the call is the sink; nothing closes at
                        // scope exit, so the scope-exit waiver line goes.
                        plan.receipts
                            .retain(|receipt| !receipt.starts_with("waiver-drop(scope-exit)"));
                        plan.receipts.push(format!(
                            "box-param-transfer callee={callee_path} index={hir_index}"
                        ));
                        plan.retained_sink = true;
                        plan.implicit_scope_close = false;
                        // A use inside a statement the initializer absorbs
                        // (the literal first store) is deleted, not rewritten.
                        local_uses.retain(|edit| {
                            !plan.delete_statements.iter().any(|d| d.contains(edit.span))
                        });
                        member_plans.push((key, plan, local.label.clone(), local_uses));
                    }
                    Err(failure_) => {
                        failure = Some(format!(
                            "box-param-caller-retains:{caller_path}:unplanned-argument:{}",
                            failure_.key()
                        ));
                        break 'callers;
                    }
                }
            }
        }
        if let Some(reason) = failure {
            hold(reason, &mut out);
            continue;
        }
        if call_count == 0 {
            hold(format!("box-param-no-callers:{callee_path}"), &mut out);
            continue;
        }
        let Some(param_slot) = slot_of(param) else { continue };
        if model.get(&param_slot) != Some(&SlotKind::Owning) {
            hold(
                format!(
                    "box-param-model:{}:{:?}",
                    param.label,
                    model.get(&param_slot)
                ),
                &mut out,
            );
            continue;
        }
        // One shape for the whole chain.
        let shapes: FxHashSet<(bool, Option<&'static str>)> = member_plans
            .iter()
            .map(|(_, plan, _, _)| {
                (
                    matches!(plan.shape, BoxShape::Slice),
                    plan.pointee_override.map(|o| o.source_name()),
                )
            })
            .collect();
        if shapes.len() != 1 {
            hold(
                format!("box-param-shape:{callee_path}:callers-disagree"),
                &mut out,
            );
            continue;
        }
        let (slice, pointee_override) = shapes.into_iter().next().expect("one shape");
        if pointee_override.is_some() {
            hold(
                format!("box-param-shape:{callee_path}:pointee-override"),
                &mut out,
            );
            continue;
        }
        // The chain's element accesses: slice owners index, sized owners deref.
        let mut expr_edits = vec![BoxExprEdit {
            span: frees[0].0,
            replacement: format!("drop({name})"),
            receipt: "box-param-c-free-site-drop",
        }];
        let mut shape_failure = None;
        for (edit, owner) in param_uses.iter().map(|e| (e, &name)).chain(
            member_plans
                .iter()
                .flat_map(|(_, _, label, uses)| uses.iter().map(move |e| (e, label))),
        ) {
            let _ = owner;
            let text = tcx
                .sess
                .source_map()
                .span_to_snippet(edit.span)
                .unwrap_or_default();
            let replacement = if slice {
                edit.replacement.clone()
            } else if let Some(root) = text.strip_prefix('*')
                && !root.contains('.')
            {
                format!("(*{root})")
            } else {
                shape_failure = Some(format!("box-param-shape:{callee_path}:sized-owner-indexed"));
                break;
            };
            expr_edits.push(BoxExprEdit {
                span: edit.span,
                replacement,
                receipt: "box-param-element-access",
            });
        }
        if let Some(reason) = shape_failure {
            hold(reason, &mut out);
            continue;
        }
        let member_edit_count = member_plans
            .iter()
            .map(|(_, _, _, uses)| uses.len())
            .sum::<usize>();
        let param_edits: Vec<BoxExprEdit> = expr_edits
            .drain(..expr_edits.len() - member_edit_count)
            .collect();
        let mut member_edits = expr_edits;
        let pointee = {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(param.fn_did)
                .borrow();
            let ty = body.local_decls[param.local].ty;
            match ty.kind() {
                TyKind::RawPtr(pointee, _) => format!("{pointee}"),
                _ => continue,
            }
        };
        let members: Vec<String> = member_plans
            .iter()
            .map(|(_, _, label, _)| label.clone())
            .collect();
        out.receipts.push(format!(
            "box-param-chain callee={callee_path} index={hir_index} pointee={pointee} shape={} callers={call_count} members={}",
            if slice { "slice" } else { "sized" },
            members.join(",")
        ));
        for (key, mut plan, _, uses) in member_plans {
            plan.expr_edits.extend(member_edits.drain(..uses.len()));
            out.plans.insert(key, plan);
        }
        out.plans.insert(
            (param.fn_did, param.hir_id),
            BoxPlan {
                shape: if slice { BoxShape::Slice } else { BoxShape::Sized },
                optional: false,
                expr_edits: param_edits,
                delete_statements: Vec::new(),
                receipts: vec![format!(
                    "box-param-owning-formal callee={callee_path} index={hir_index} callers={call_count}"
                )],
                fabricated_extent: false,
                pointee_override: None,
                inferred_binding: false,
                overwrite_spans: Vec::new(),
                retained_sink: true,
                implicit_scope_close: false,
            },
        );
    }
    out
}
