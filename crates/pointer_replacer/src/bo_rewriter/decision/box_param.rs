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
    /// R419-3: every admitted chain's classes — the consuming callee and its
    /// callers — revert together.
    pub(crate) chains: Vec<(LocalDefId, Vec<LocalDefId>)>,
    /// W6A-C2: the caller locals of a STORE chain. The model calls such an
    /// allocation Raw (it never sees it freed), so the ladder would degrade
    /// `kind-raw` before the Box arm; the chain's source proof supersedes it
    /// exactly as the allocation-return certificate's does, applied at the
    /// same pre-model hook.
    pub(crate) store_members: FxHashSet<(LocalDefId, HirId)>,
    /// **W6A-A9** — the formals whose bodies PROVE a lend, so the owning arm
    /// declines them and the borrowing arms below decide.
    pub(crate) lends: FxHashSet<(LocalDefId, HirId)>,
    /// One `yielded` receipt per declined ownership claim: (label, reason).
    pub(crate) lend_receipts: Vec<(String, String)>,
    /// **R531-4 (vii)**: the declined formals whose pointee has model-`Owning`
    /// fields — binding → (label, callee, those fields). The decline stands
    /// only while no transaction delivers one of them
    /// (`withdraw_delivered_owned_field_lends`).
    pub(crate) owned_field_lends:
        FxHashMap<(LocalDefId, HirId), (String, String, Vec<(LocalDefId, usize)>)>,
    /// **R536-3 — re-seated formals**: binding → (label, callee, the owned
    /// fields its call sites move out of). The plan stands only while every
    /// one of those fields is delivered as an owned transaction
    /// (`withdraw_undelivered_reseats`).
    pub(crate) reseat_fields:
        FxHashMap<(LocalDefId, HirId), (String, String, Vec<(LocalDefId, usize)>)>,
}

/// **wave-6a rule W6A-A9 — a proven lend leaves the owning arm** (relay
/// wave-6a/043 §A9). The model calls some lent formals `Owning`, and the
/// decide ladder's owning arm claims every such subject: it asks this family
/// for a plan, finds no consumer, and degrades. The body says the claim is
/// wrong — the callee never frees the formal, never stores it, never moves it
/// on, so nothing in this body releases the allocation
/// and the caller keeps the owner.
///
/// This rule decides NOTHING about what the subject becomes. It declines the
/// ownership claim its body disproves and lets the borrowing arms below decide
/// under their own gates — exactly as they already do for a `Ref`-modeled
/// formal of the same shape (the `w6a_a9_the_model_ref_lend_needs_no_rule`
/// control emits `area(settings: &Settings)` / `area(&*s)` with no rule at
/// all). It claims strictly LESS ownership than the model does, never more,
/// which is the side of R487-3(d)'s asymmetry that evidence may move.
pub(crate) fn lend_leaves_owning(ctx: &Ctx<'_, '_>, subject: &Subject) -> bool {
    ctx.box_params
        .lends
        .contains(&(subject.fn_did, subject.hir_id))
}

/// After the seams: a chain reverts whole (R419-3) — the consuming callee's
/// class and every caller's class depend on each other both ways.
pub(crate) fn append_interface_dependencies(table: &mut DecisionTable) {
    let mut edges = Vec::new();
    for (callee, callers) in &table.box_params.chains {
        let callee_class = SignatureClassId::of(*callee);
        for caller in callers {
            let caller_class = SignatureClassId::of(*caller);
            if caller_class != callee_class {
                edges.push((callee_class, caller_class));
                edges.push((caller_class, callee_class));
            }
        }
    }
    table.seams.interface_dependencies.extend(edges);
    table.seams.interface_dependencies.sort();
    table.seams.interface_dependencies.dedup();
}

impl Chains {
    pub(crate) fn receipts_tsv(&self) -> String {
        let mut out = String::from("parameter\tkind\tdetail\n");
        for receipt in &self.receipts {
            out.push_str(&format!("-\tadmitted\t{receipt}\n"));
        }
        let mut lends = self.lend_receipts.clone();
        lends.sort();
        for (parameter, reason) in &lends {
            out.push_str(&format!("{parameter}\tyielded\t{reason}\n"));
        }
        let mut holds: Vec<&(String, String)> = self.holds.values().collect();
        holds.sort();
        for (parameter, hold) in holds {
            out.push_str(&format!("{parameter}\theld\t{hold}\n"));
        }
        out
    }
}

/// **R531-4 (vii) — A9's companion gate keyed on the DELIVERED field form**,
/// the parameter-side mirror of `return_certificate::withdraw_delivered_owned_fields`:
/// after `field_reference::finalize`, a declined formal whose pointee has a
/// field an APPLIED owning transaction delivers loses its decline and takes
/// the gate's hold; the caller re-derives the stage. Declines only shrink,
/// so it terminates.
pub(crate) fn withdraw_delivered_owned_field_lends(
    chains: &mut Chains,
    delivered: &dyn Fn(LocalDefId, usize) -> bool,
) -> bool {
    let withdrawn = chains
        .owned_field_lends
        .iter()
        .filter(|(key, (_, _, fields))| {
            chains.lends.contains(*key) && fields.iter().any(|(did, index)| delivered(*did, *index))
        })
        .map(|(key, (label, callee, _))| (*key, label.clone(), callee.clone()))
        .collect::<Vec<_>>();
    for (key, label, callee) in &withdrawn {
        chains.lends.remove(key);
        chains.lend_receipts.retain(|(l, _)| l != label);
        chains.holds.insert(
            *key,
            (
                label.clone(),
                format!("box-param-callee-lends-owned-field:{callee}"),
            ),
        );
    }
    !withdrawn.is_empty()
}

/// **R536-3** — after `field_reference::finalize`: a re-seated formal whose
/// call sites move out of a field no applied OWNING transaction delivers
/// would take a raw pointer into its `Option<Box<T>>`, so its plan is
/// withdrawn with a typed hold and the caller re-derives the stage.
pub(crate) fn withdraw_undelivered_reseats(
    chains: &mut Chains,
    delivered: &dyn Fn(LocalDefId, usize) -> bool,
) -> bool {
    let withdrawn = chains
        .reseat_fields
        .iter()
        .filter(|(key, (_, _, fields))| {
            chains.plans.contains_key(*key)
                && fields.iter().any(|(did, index)| !delivered(*did, *index))
        })
        .map(|(key, (label, callee, _))| (*key, label.clone(), callee.clone()))
        .collect::<Vec<_>>();
    for (key, label, callee) in &withdrawn {
        chains.plans.remove(key);
        chains
            .receipts
            .retain(|r| !r.starts_with(&format!("box-param-reseat callee={callee} ")));
        chains.holds.insert(
            *key,
            (
                label.clone(),
                format!("box-param-reseat-field-not-delivered:{callee}"),
            ),
        );
    }
    !withdrawn.is_empty()
}

enum Reseat {
    /// The body does not return the formal: A9's lend question applies.
    NotReturned,
    Held(String),
    Planned(BoxPlan, Vec<(LocalDefId, usize)>),
}

/// **R536-3 — a formal consumed AND returned** (`root = insert(root, key)`,
/// the re-seat `x = f(x)`). The formal is an owner the body hands back: it
/// takes `Option<Box<T>>` (a C tree's null child is `None`), its uses are the
/// certificate's owner walk's (null tests `is_none`, derefs through
/// `as_deref_mut().unwrap()`), and each `return x` hands the owner back out
/// through `Box::into_raw` — the function's return stays the raw pointer the
/// source declares, so every other return (`return newNode(key)`) is
/// untouched. Every in-program call must re-seat an owned FIELD — `(*p).f =
/// f((*p).f, ..)`, the same place on both sides — so the move out
/// (`.take()`, wave-6f's owned-field move into an optional Box consumer) is
/// followed by the move back in (their `from_raw` store of the raw result):
/// a call that discarded or redirected the result would leave the field
/// `None` where C left it intact, so it holds. An exported function's
/// outside callers pass a handle and get it back (the surface pointer is the
/// same allocation both ways).
#[allow(clippy::too_many_arguments)]
fn reseat_plan<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    consuming: &FxHashSet<(DefId, usize)>,
    fn_values: &FxHashSet<DefId>,
    param: &Subject,
    frees: &[(Span, Span)],
) -> Reseat {
    let SubjectKind::Param { hir_index } = param.kind else { return Reseat::NotReturned };
    let slot = slots
        .fn_local_slots
        .get(&param.fn_did)
        .and_then(|u| u.slot_for_local_depth(param.local, 0))
        .map(|slot| SlotRef::Local(param.fn_did, slot));
    if slot.and_then(|slot| model.get(&slot).copied()) != Some(SlotKind::Owning) {
        return Reseat::NotReturned;
    }
    let lend_oracle = super::return_certificate::LendOracle::new(tcx, functions, slots, model);
    let Ok(uses) = super::return_certificate::owner_uses(
        tcx,
        param,
        BoxShape::Sized,
        true,
        false,
        frees,
        &|did, index| lend_oracle.lend(did, index),
        &|did, index| consuming.contains(&(did, index)),
        &|_| false,
    ) else {
        return Reseat::NotReturned;
    };
    if uses.returns.is_empty() {
        return Reseat::NotReturned;
    }
    let callee_path = tcx.def_path_str(param.fn_did.to_def_id());
    if !uses.stores.is_empty() || !uses.transfers.is_empty() {
        return Reseat::Held(format!("box-param-reseat-escapes:{callee_path}"));
    }
    if fn_values.contains(&param.fn_did.to_def_id()) {
        return Reseat::Held(format!("box-param-indirect-callers:{callee_path}"));
    }
    let mut calls = ReseatCalls {
        tcx,
        callee: param.fn_did.to_def_id(),
        index: hir_index,
        fields: Vec::new(),
        refusal: None,
    };
    for &function in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else { continue };
        calls.visit_body(tcx.hir_body(body_id));
    }
    if let Some(refusal) = calls.refusal {
        return Reseat::Held(format!("box-param-reseat-caller:{callee_path}:{refusal}"));
    }
    if calls.fields.is_empty() && !super::exported_pair::exported(tcx, param.fn_did) {
        return Reseat::Held(format!("box-param-no-callers:{callee_path}"));
    }
    let name = param.param_name.clone().unwrap_or_else(|| "?".to_owned());
    let mut expr_edits = uses.edits;
    // A C free of the owner on some path is its drop there; Rust's move
    // checking proves no path frees it twice or uses it after.
    expr_edits.extend(frees.iter().map(|(call, _)| BoxExprEdit {
        span: *call,
        replacement: format!("drop({name})"),
        receipt: "box-param-c-free-site-drop",
    }));
    expr_edits.extend(uses.returns.iter().map(|span| BoxExprEdit {
        span: *span,
        replacement: format!("return {name}.map_or(core::ptr::null_mut(), Box::into_raw)"),
        receipt: "box-param-reseat-return",
    }));
    let mut fields = calls.fields;
    fields.sort_by_key(|(did, index)| (did.local_def_index.as_u32(), *index));
    fields.dedup();
    Reseat::Planned(
        BoxPlan {
            shape: BoxShape::Sized,
            optional: true,
            expr_edits,
            delete_statements: Vec::new(),
            receipts: vec![format!(
                "box-param-reseat callee={callee_path} index={hir_index}"
            )],
            fabricated_extent: false,
            pointee_override: None,
            inferred_binding: false,
            overwrite_spans: Vec::new(),
            retained_sink: true,
            implicit_scope_close: false,
        },
        fields,
    )
}

/// Every call of the re-seated callee: the argument at its index must be an
/// owned-field place `(*p).f`, and the call's result must be assigned back to
/// that same place.
struct ReseatCalls<'tcx> {
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    index: usize,
    fields: Vec<(LocalDefId, usize)>,
    refusal: Option<String>,
}

impl<'tcx> Visitor<'tcx> for ReseatCalls<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if let ExprKind::Call(callee, args) = &e.kind
            && let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind
            && let Res::Def(DefKind::Fn, did) = path.res
            && did == self.callee
            && self.refusal.is_none()
        {
            let snippet = |span: Span| {
                self.tcx
                    .sess
                    .source_map()
                    .span_to_snippet(span)
                    .unwrap_or_default()
            };
            let field = args.get(self.index).and_then(|arg| {
                let ExprKind::Field(base, _) = &arg.kind else { return None };
                if !matches!(base.kind, ExprKind::Unary(rustc_hir::UnOp::Deref, _)) {
                    return None;
                }
                let owner = arg.hir_id.owner.def_id;
                let typeck = self.tcx.typeck(owner);
                let index = typeck.opt_field_index(arg.hir_id)?.as_usize();
                let TyKind::Adt(adt, _) = typeck.expr_ty(base).kind() else { return None };
                Some(((adt.did().as_local()?, index), arg.span))
            });
            let reseated = field.filter(|(_, arg_span)| {
                matches!(
                    self.tcx.parent_hir_node(e.hir_id),
                    rustc_hir::Node::Expr(parent)
                        if matches!(parent.kind, ExprKind::Assign(lhs, rhs, _)
                            if rhs.hir_id == e.hir_id && snippet(lhs.span) == snippet(*arg_span))
                )
            });
            match reseated {
                Some((field, _)) => self.fields.push(field),
                None => self.refusal = Some(snippet(e.span)),
            }
        }
        intravisit::walk_expr(self, e);
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
        let base = match plan.shape {
            BoxShape::Sized => format!("Box<{element}>"),
            BoxShape::Slice => format!("Box<[{element}]>"),
        };
        // R531-4 (iii): a member an optional producer certified is an
        // `Option<Box<T>>`, as the certificate's own appender spells it.
        let emitted_type = if plan.optional {
            format!("Option<{base}>")
        } else {
            base
        };
        sites.push(ExplicitDeclarationSite {
            owner_class: SignatureClassId::of(subject.fn_did),
            caller: subject.fn_did,
            node: Some(node),
            span: Some(subject.binding_span),
            category: "local",
            replacement: Some(format!(
                "{}{name}: {emitted_type}",
                if subject.mut_binding { "mut " } else { "" }
            )),
            emitted_type,
            arm: "surface",
        });
    }
    table.seams.explicit_declarations.extend(sites);
}

/// The hold's family as a stable reason key (the receipt keeps the detail).
fn typed_key(hold: &str) -> &'static str {
    const KEYS: [&str; 8] = [
        "chain-endpoint-raw",
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

/// The struct field a place expression projects (`(*x).f`, `(*x.offset(i)).f`,
/// `x.f`), as its own `DefId`.
fn field_of(tcx: TyCtxt<'_>, place: &Expr<'_>) -> Option<DefId> {
    let ExprKind::Field(base, _) = peel_casts(place).kind else { return None };
    let typeck = tcx.typeck(place.hir_id.owner.def_id);
    let base_ty = typeck.expr_ty_adjusted(base);
    let rustc_middle::ty::TyKind::Adt(adt, _) = base_ty.peel_refs().kind() else { return None };
    let index = typeck.field_index(peel_casts(place).hir_id);
    adt.non_enum_variant()
        .fields
        .get(index)
        .map(|field| field.did)
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
    /// W6A-C2: `<raw place> = x` with `x` a bare local (the cast peeled):
    /// (local, the local's own span, the assignment's span). A store into a
    /// bare local is a copy, not a sink, and is not recorded here.
    stores: Vec<(HirId, Span, Span)>,
    /// The store expressions' own ids, for the enclosing-loop test.
    store_ids: Vec<(HirId, HirId)>,
    /// The field each store targets: (local, the field's `DefId`).
    store_fields: Vec<(HirId, DefId)>,
    /// Every field a C `free` releases anywhere in this body.
    freed_fields: FxHashSet<DefId>,
    /// Local functions whose address is taken (a value, not a callee).
    fn_values: FxHashSet<DefId>,
    /// R561-4 W1: `x = ..` with `x` a bare local: (local, the assignment's span).
    assigns: Vec<(HirId, Span)>,
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
            ExprKind::Assign(lhs, rhs, _) => {
                if let Some(hir) = bare_local(lhs) {
                    self.assigns.push((hir, e.span));
                }
                if bare_local(lhs).is_none()
                    && let Some(hir) = bare_local(rhs)
                {
                    let tcx = self.tcx.expect("scan tcx");
                    let typeck = tcx.typeck(lhs.hir_id.owner.def_id);
                    if typeck.expr_ty(lhs).is_raw_ptr() {
                        self.stores.push((hir, peel_casts(rhs).span, e.span));
                        self.store_ids.push((hir, e.hir_id));
                        if let Some(field) = field_of(tcx, lhs) {
                            self.store_fields.push((hir, field));
                        }
                    }
                }
            }
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
                        {
                            if let Some(hir) = bare_local(arg) {
                                self.frees.push((hir, e.span, arg.span));
                            }
                            // W6A-C2: which FIELD C releases here, so a store
                            // into that field is never admitted as a move.
                            if let Some(field) =
                                field_of(self.tcx.expect("scan tcx"), peel_casts(arg))
                            {
                                self.freed_fields.insert(field);
                            }
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

/// Every occurrence of the subject that is the BASE of a field projection —
/// `(*node).left`, `(*y).height`. On a sized `Box<T>` those compile exactly as
/// written (`*y` derefs the Box), so they need no edit at all; the slice-use
/// collector, which reads uses as element accesses, reports them as raw and
/// this is how the chain tells them apart (relay wave-6a/026: avl's rotations).
fn field_projection_bases(tcx: TyCtxt<'_>, subject: &Subject) -> Vec<Span> {
    struct Walk<'tcx> {
        tcx: TyCtxt<'tcx>,
        hir: HirId,
        out: Vec<Span>,
    }
    impl<'tcx> Visitor<'tcx> for Walk<'tcx> {
        type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

        fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
            self.tcx
        }

        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if let ExprKind::Field(base, _) = &e.kind
                && let ExprKind::Unary(rustc_hir::UnOp::Deref, inner) = &base.kind
                && let ExprKind::Path(QPath::Resolved(_, path)) = &inner.kind
                && let Res::Local(hir) = path.res
                && hir == self.hir
            {
                self.out.push(inner.span);
            }
            intravisit::walk_expr(self, e);
        }
    }
    let Some(body_id) = tcx.hir_node_by_def_id(subject.fn_did).body_id() else {
        return Vec::new();
    };
    let mut walk = Walk {
        tcx,
        hir: subject.hir_id,
        out: Vec::new(),
    };
    walk.visit_body(tcx.hir_body(body_id));
    walk.out
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
    let fields = field_projection_bases(tcx, subject);
    for raw in &uses.raw_uses {
        let admitted = raw
            .boundary_span
            .is_some_and(|b| boundaries.iter().any(|allowed| allowed.contains(b)))
            || fields.iter().any(|field| *field == raw.span);
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

/// The formals a chain COULD plan as consuming owners — syntactically: a
/// depth-1 raw parameter freed exactly once whose other uses the slice-use
/// collector rewrites, of a callee whose address is not taken. The
/// allocation-return certificate (A1) asks this to admit a receiver's
/// transfer into such a formal; the chain itself then confirms or not.
pub(crate) fn consuming_formals<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    subjects: &[Subject],
) -> FxHashSet<(DefId, usize)> {
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
    let mut out = FxHashSet::default();
    // **R450-8 rung 2** — the set is a depth-bounded FIXPOINT. Its seed is the
    // formals with a sink of their own (a free, or W6A-C2's store); each pass
    // then adds a formal whose only sink is the MOVE ON — `pass_on(q)` handing
    // `q` to a callee already in the set. Each pass adds exactly one level of
    // the chain, and the loop stops as soon as one adds nothing.
    for _ in 0..RUNG2_DEPTH {
        let mut added = false;
        for param in subjects {
            let SubjectKind::Param { hir_index } = param.kind else { continue };
            if param.ptr_depth != 1 || fn_values.contains(&param.fn_did.to_def_id()) {
                continue;
            }
            if out.contains(&(param.fn_did.to_def_id(), hir_index)) {
                continue;
            }
            let Some(scan) = scans.get(&param.fn_did) else { continue };
            let frees: Vec<(Span, Span)> = scan
                .frees
                .iter()
                .filter(|(hir, _, _)| *hir == param.hir_id)
                .map(|(_, call, arg)| (*call, *arg))
                .collect();
            let sink = match (
                frees.as_slice(),
                store_sink(tcx, scan, param),
                move_on_sink(scan, param, &out),
            ) {
                ([(_, argument)], None, None) => *argument,
                ([], Some((value, _)), None) => value,
                ([], None, Some(argument)) => argument,
                _ => continue,
            };
            if slice_uses_of(tcx, param, &[sink]).is_err() {
                continue;
            }
            out.insert((param.fn_did.to_def_id(), hir_index));
            added = true;
        }
        if !added {
            break;
        }
    }
    out
}

/// How deep a parameter-to-parameter chain this rule follows (R450-8 rung 2).
/// Each pass of [`consuming_formals`] adds one level; four covers every shape
/// the corpus carries and bounds the cost of a program whose call graph is
/// deep.
const RUNG2_DEPTH: usize = 4;

/// **R450-8 rung 2** — the formal's only sink is the MOVE ON: exactly one call
/// in the body passes it, at an index whose callee formal is already known to
/// consume, and it is passed nowhere else. The argument's span is the sink, so
/// every other use of the formal must still be one the slice-use collector
/// rewrites — the same test a free or a store sink takes.
fn move_on_sink(
    scan: &Scan<'_>,
    param: &Subject,
    known: &FxHashSet<(DefId, usize)>,
) -> Option<Span> {
    let mut passes = scan.calls.iter().filter_map(|(callee, _, args)| {
        let index = args
            .iter()
            .position(|a| a.map(|(hir, _)| hir) == Some(param.hir_id))?;
        let (_, span) = args[index]?;
        Some((*callee, index, span))
    });
    let (callee, index, span) = passes.next()?;
    if passes.next().is_some() || !known.contains(&(callee, index)) {
        return None;
    }
    Some(span)
}

/// **W6A-C2: the store sink.** A formal the callee neither frees nor returns
/// but STORES exactly once into a raw place it reaches (`(*t).f = p`,
/// `(*entries.offset(i)).key = p`) hands its allocation to the program's own
/// storage: the move ends at the store, which emits `Box::into_raw(p)` — the
/// batch-6 deallocator-transfer discipline with the store as the sink (the C
/// free of that place stays a C free, someone else's subject). Admitted only
/// when the move is the formal's LAST act: no assignment to the formal
/// the store outside every loop, and no use of the formal after it (a use
/// after a move is not a use after a free — C keeps the pointer valid, so
/// this is a refusal the input does not owe us). A formal RE-SEATED before
/// the store (ht's `key = strdup(key)`) needs no clause of its own: the
/// re-seating expression is itself a raw use of the formal, which the
/// slice-use collector refuses (the "reassigned" control measures it).
fn store_sink<'tcx>(tcx: TyCtxt<'tcx>, scan: &Scan<'tcx>, param: &Subject) -> Option<(Span, Span)> {
    let stores: Vec<(Span, Span)> = scan
        .stores
        .iter()
        .filter(|(hir, _, _)| *hir == param.hir_id)
        .map(|(_, value, statement)| (*value, *statement))
        .collect();
    let [(value, statement)] = stores.as_slice() else { return None };
    if scan
        .local_uses
        .iter()
        .any(|(hir, span)| *hir == param.hir_id && span.lo() > statement.hi())
    {
        return None;
    }
    scan.store_ids
        .iter()
        .find(|(hir, id)| *hir == param.hir_id && !inside_loop(tcx, *id))
        .map(|_| (*value, *statement))
}

/// The store sits inside a loop: the move would run twice.
fn inside_loop(tcx: TyCtxt<'_>, mut hir: HirId) -> bool {
    loop {
        match tcx.parent_hir_node(hir) {
            rustc_hir::Node::Expr(parent) => {
                if matches!(parent.kind, ExprKind::Loop(..)) {
                    return true;
                }
                hir = parent.hir_id;
            }
            rustc_hir::Node::Block(block) => hir = block.hir_id,
            rustc_hir::Node::Stmt(statement) => hir = statement.hir_id,
            _ => return false,
        }
    }
}

/// **W6A-A9's companion gate** (report 044). The pointee of `param` is a
/// struct one of whose fields the model calls `Owning`: another family owns
/// that field, its edit is an owned one, and an owned edit cannot sit inside
/// the A5 raw view a reference formal creates at a deallocator argument.
fn owned_fields_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    param: &Subject,
) -> Vec<(LocalDefId, usize)> {
    let body = tcx
        .mir_drops_elaborated_and_const_checked(param.fn_did)
        .borrow();
    let Some(decl) = body.local_decls.get(param.local) else {
        return Vec::new();
    };
    let TyKind::RawPtr(pointee, _) = decl.ty.kind() else {
        return Vec::new();
    };
    let TyKind::Adt(adt, _) = pointee.kind() else {
        return Vec::new();
    };
    let Some(struct_did) = adt.did().as_local() else {
        return Vec::new();
    };
    (0..adt.all_fields().count())
        .filter(|&field_index| {
            slots
                .field_slots
                .slot_for_field_depth(
                    crate::analyses::borrow_ownership::slots::StructFieldSlot {
                        struct_did,
                        field_index,
                    },
                    0,
                )
                .map(SlotRef::Field)
                .and_then(|slot| model.get(&slot).copied())
                == Some(SlotKind::Owning)
        })
        .map(|field_index| (struct_did, field_index))
        .collect()
}

/// Derive every chain for the crate. Runs once, before the family stages; the
/// model is read only to refuse a chain whose members are not all Owning.
#[allow(clippy::too_many_arguments)]
pub(crate) fn derive<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    constructions: &ConstructionFacts,
    subjects: &[Subject],
    box_facts: &BoxOwnershipFacts,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    certificates: &super::return_certificate::Certificates,
    contract_plans: &FxHashMap<(LocalDefId, HirId), BoxPlan>,
    consuming: &FxHashSet<(DefId, usize)>,
    raw_surface: &dyn Fn(LocalDefId) -> bool,
    exported_pairs: &super::exported_pair::Closure,
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
    // **R450-8 rung 2 — the order the chains are planned in.** A formal whose
    // sink is the MOVE ON is a caller MEMBER of the chain it moves into, so
    // its own plan must exist before that chain's caller loop reads it. Its
    // depth in the move-on relation says when: the outermost formal is planned
    // first, and the innermost — the one that frees or stores — last. Every
    // other formal has depth 0 and keeps the old order among themselves.
    let mut depth: FxHashMap<(DefId, usize), usize> = FxHashMap::default();
    for _ in 0..RUNG2_DEPTH {
        for param in &params {
            let SubjectKind::Param { hir_index } = param.kind else { continue };
            let key = (param.fn_did.to_def_id(), hir_index);
            let Some(scan) = scans.get(&param.fn_did) else { continue };
            if !scan.frees.iter().any(|(hir, _, _)| *hir == param.hir_id)
                && store_sink(tcx, scan, param).is_none()
                && let Some(call) = scan.calls.iter().find_map(|(callee, _, args)| {
                    let index = args
                        .iter()
                        .position(|a| a.map(|(hir, _)| hir) == Some(param.hir_id))?;
                    Some((*callee, index))
                })
            {
                let inner = depth.get(&call).copied().unwrap_or(0);
                depth.insert(key, inner + 1);
            }
        }
    }
    params.sort_by_key(|s| {
        let hir_index = match s.kind {
            SubjectKind::Param { hir_index } => hir_index,
            _ => 0,
        };
        let order = depth
            .get(&(s.fn_did.to_def_id(), hir_index))
            .copied()
            .unwrap_or(0);
        (
            std::cmp::Reverse(order),
            s.fn_did.local_def_index.as_u32(),
            s.local.as_u32(),
        )
    });
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
        // W6A-C2: a formal the callee stores into a raw place instead of
        // freeing hands its allocation to the program's own storage; the
        // store is the sink and the move ends there.
        let store = store_sink(tcx, scan, param);
        // **R450-8 rung 2**: the formal's sink may be the MOVE ON — `pass_on(q)`
        // handing `q` to a callee that consumes it. `consuming_formals` is a
        // fixpoint over exactly that relation, so the question is already
        // answered when this rule reads it; the emission for such a formal adds
        // NO edit at the sink (a `Box` argument at a `Box` formal moves).
        let moved_on = if frees.is_empty() && store.is_none() {
            move_on_sink(scan, param, consuming)
        } else {
            None
        };
        // **R536-3 — the re-seat** is asked first: a formal the body RETURNS
        // is consumed and handed back — freed on some paths, perhaps
        // (`deleteNode`) — not lent, and neither A9's question nor the
        // second-free count applies to it.
        if store.is_none() && moved_on.is_none() {
            match reseat_plan(
                tcx, functions, slots, model, consuming, &fn_values, param, &frees,
            ) {
                Reseat::NotReturned => {}
                Reseat::Held(reason) => {
                    out.holds
                        .insert((param.fn_did, param.hir_id), (param.label.clone(), reason));
                    continue;
                }
                Reseat::Planned(plan, fields) => {
                    out.receipts.push(format!(
                        "box-param-reseat callee={callee_path} index={hir_index} fields={}",
                        fields.len()
                    ));
                    out.reseat_fields.insert(
                        (param.fn_did, param.hir_id),
                        (param.label.clone(), callee_path.clone(), fields),
                    );
                    out.plans.insert((param.fn_did, param.hir_id), plan);
                    continue;
                }
            }
        }
        if frees.is_empty() && store.is_none() && moved_on.is_none() {
            // Not a consumer: a lend. Only reported for an Owning-modeled formal
            // (the rows the Box arm holds today); a Ref/Raw formal is not (c).
            if slot_of(param).is_some_and(|slot| model.get(&slot) == Some(&SlotKind::Owning)) {
                // **W6A-A9's companion gate**, the mirror of A1-e's (report
                // 044): a formal whose pointee struct has a field another
                // family OWNS and DELIVERS is not declined — a reference
                // formal puts the deallocator argument behind an A5 raw view,
                // and the owned field's edit cannot live inside one (wave-6f's
                // transaction declines it and the refusal aborts the program's
                // rewrite). Whether the field is delivered is known only after
                // the transactions finalize, so the model-`Owning` fields are
                // recorded here and the decline is withdrawn then if one is
                // delivered (R531-4 (vii)); a HELD field has no edit to put
                // inside a view.
                let owned_fields = owned_fields_of(tcx, slots, model, param);
                if !owned_fields.is_empty() {
                    out.owned_field_lends.insert(
                        (param.fn_did, param.hir_id),
                        (param.label.clone(), callee_path.clone(), owned_fields),
                    );
                }
                // **W6A-A9.** The three sinks are all absent, so nothing in
                // this body releases the allocation and the caller keeps the
                // owner. The one act left that could carry it out — handing
                // the formal BACK — needs no clause of its own at this frame:
                // a lend that returns its formal is not Owning-modeled, so it
                // never reaches here. The `..._returns_...` control measures
                // exactly that, and a guard goes in the moment it fails.
                out.lends.insert((param.fn_did, param.hir_id));
                out.lend_receipts.push((
                    param.label.clone(),
                    format!("box-param-lend-leaves-owning:{callee_path}"),
                ));
            }
            continue;
        }
        let name = param.param_name.clone().unwrap_or_else(|| "?".to_owned());
        let hold = |reason: String, out: &mut Chains| {
            out.holds
                .insert((param.fn_did, param.hir_id), (param.label.clone(), reason));
        };
        if frees.len() > 1 {
            hold(
                format!("box-param-callee-use:{callee_path}:second-free"),
                &mut out,
            );
            continue;
        }
        if !frees.is_empty() && store.is_some() {
            hold(
                format!("box-param-callee-use:{callee_path}:freed-and-stored"),
                &mut out,
            );
            continue;
        }
        // W6A-C2: the store hands the allocation to the program's own storage
        // and emits NO drop — so it is admitted only where the input itself
        // never releases that field (the leak-parity shape, addendum 101: the
        // emitted program leaks exactly what the input leaks). A field some C
        // `free` releases would take a Rust-allocated block to libc's
        // `free`; that composition is wave-6f's owned FIELD (W6F-3), where the
        // store is a move into an owned field and the drop is theirs.
        if let Some((_, statement)) = store {
            let _ = statement;
            let field = scan
                .store_fields
                .iter()
                .find(|(hir, _)| *hir == param.hir_id)
                .map(|(_, field)| *field);
            match field {
                None => {
                    hold(
                        format!("box-param-store-destination:{callee_path}:not-a-field"),
                        &mut out,
                    );
                    continue;
                }
                Some(field) if scans.values().any(|s| s.freed_fields.contains(&field)) => {
                    hold(
                        format!(
                            "box-param-store-c-free:{callee_path}:{}",
                            tcx.def_path_str(field)
                        ),
                        &mut out,
                    );
                    continue;
                }
                Some(_) => {}
            }
        }
        let sink = match (frees.first(), store, moved_on) {
            (Some((_, argument)), None, None) => *argument,
            (None, Some((value, _)), None) => value,
            (None, None, Some(argument)) => argument,
            _ => unreachable!("exactly one sink reaches here"),
        };
        // Every other use of the formal is a deref / element access the
        // slice-use collector rewrites; the sink is its one raw boundary.
        // R531-4 (vi): an exported function nothing in the program calls
        // may take the consumer waiver, whose `Option` formal renders its
        // formal through the certificate's owner walk instead — so a use the
        // slice-use collector cannot rewrite (`is_null()`) is decided there.
        let no_caller_export = super::exported_pair::exported(tcx, param.fn_did)
            && !scans.values().any(|s| {
                s.calls
                    .iter()
                    .any(|(callee, _, _)| *callee == param.fn_did.to_def_id())
            });
        let (param_uses, deferred_use) = match slice_uses_of(tcx, param, &[sink]) {
            Ok(uses) => (uses, None),
            Err(form) if no_caller_export => (Vec::new(), Some(form)),
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
        // Rung 2: members that are the caller's own PARAMETER — their plan
        // belongs to the chain that planned that formal, not to this one.
        let mut moved_on_members: FxHashSet<(LocalDefId, HirId)> = FxHashSet::default();
        // R531-4 (iii): members whose owner is an `Option<Box<T>>`.
        let mut optional_members = 0usize;
        // R561-4 W2: each member's argument at its call, for the `Some(..)`
        // a non-optional member needs at an optional formal.
        let mut member_args: Vec<((LocalDefId, HirId), Span)> = Vec::new();
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
                member_args.push((key, *arg_span));
                let Some(local) = subjects.iter().find(|s| {
                    s.fn_did == *caller && s.hir_id == *arg && s.kind == SubjectKind::Local
                }) else {
                    // **R450-8 rung 2**: the caller hands its OWN PARAMETER —
                    // `pass_on(q)` into `sink_free(p)`. That is a move when the
                    // caller's formal is itself an owner, which is exactly what
                    // this chain planned one step earlier (the depth order
                    // above). The member carries that plan for the shape and
                    // the licensing; the binding stays the other chain's, so
                    // nothing is inserted for it here.
                    if let Some(member) = subjects.iter().find(|s| {
                        s.fn_did == *caller
                            && s.hir_id == *arg
                            && matches!(s.kind, SubjectKind::Param { .. })
                    }) && let Some(plan) = out.plans.get(&(*caller, *arg)).cloned()
                    {
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
                        moved_on_members.insert(key);
                        member_plans.push((key, plan, member.label.clone(), Vec::new()));
                        continue;
                    }
                    failure = Some(format!(
                        "box-param-caller-retains:{caller_path}:not-a-local"
                    ));
                    break 'callers;
                };
                // A1-c: a receiver an allocation-return certificate plans is
                // an owner too — its plan is the certificate's (the transfer
                // at this call is what that plan admitted as a sink).
                if let Some(plan) = certificates.plans.get(&key) {
                    // R531-4 (iii): an optional owner moves as written; the
                    // formal takes its type (checked once the chain is known).
                    if plan.optional {
                        optional_members += 1;
                    }
                    // R561-4 W1: a receiver the certificate re-seats is one
                    // local over several generations, and every overwrite of
                    // it is a certified re-seat. A use behind a re-seat that
                    // follows this call belongs to the next generation.
                    let reseated = plan
                        .receipts
                        .iter()
                        .any(|r| r.starts_with(super::return_certificate::RESEAT_RECEIPT));
                    let next_generation = |use_span: &Span| {
                        reseated
                            && caller_scan.assigns.iter().any(|(hir, assign)| {
                                *hir == *arg
                                    && assign.lo() > call_span.hi()
                                    && assign.lo() <= use_span.lo()
                            })
                    };
                    if caller_scan.local_uses.iter().any(|(hir, span)| {
                        *hir == *arg && span.lo() > call_span.hi() && !next_generation(span)
                    }) {
                        failure = Some(format!(
                            "box-param-caller-retains:{caller_path}:used-after-transfer"
                        ));
                        break 'callers;
                    }
                    let mut plan = plan.clone();
                    plan.receipts.push(format!(
                        "box-param-transfer callee={callee_path} index={hir_index} source=return-certificate"
                    ));
                    member_plans.push((key, plan, local.label.clone(), Vec::new()));
                    continue;
                }
                // **R450-8 rung 3**: the CONTRACT row owns a local whose
                // allocation is the contract's and whose release is THIS call.
                // Its plan carries the construction (a struct pointee included,
                // which the ordinary Box arm has no initializer form for) and
                // its own simulation has already proved the transfer is the
                // generation's release — no free of its own, nothing after it,
                // every cast spelled. The chain consumes that plan exactly as
                // it consumes a certificate's above, and
                // `allocator_contract::confirm_transfers` withdraws the
                // owner if this chain does not plan the formal.
                if let Some(plan) = contract_plans.get(&key) {
                    // R531-4 (iii): an optional owner moves as written; the
                    // formal takes its type (checked once the chain is known).
                    if plan.optional {
                        optional_members += 1;
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
                    let mut plan = plan.clone();
                    plan.receipts.push(format!(
                        "box-param-transfer callee={callee_path} index={hir_index} source=allocator-contract"
                    ));
                    member_plans.push((key, plan, local.label.clone(), Vec::new()));
                    continue;
                }
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
                // The model's kind licenses a FREEING chain (C1): the free is
                // what makes the local Owning at this frame. A STORE sink is
                // the licensing wall itself — an allocation handed to the
                // program's own storage reads Raw everywhere (report 004's
                // STOP 1, R410-5 §1 / R413-3) — so the store chain rests on
                // the same source proof the certificates do: the allocation
                // is the ordinary Box arm's, the transfer is the local's only
                // call position, nothing reads it afterwards, and the callee's
                // one sink is the store. The model may not CONTRADICT it:
                // `Ref` is a lend verdict and refuses.
                let licensed = match model.get(&slot) {
                    Some(SlotKind::Owning) => true,
                    Some(SlotKind::Raw) => store.is_some(),
                    Some(SlotKind::Ref) | None => false,
                };
                if !licensed {
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
                // The ordinary arm's endpoints come from the model, which
                // calls an allocation handed to C storage Raw (its source
                // endpoint is not Active): a direct allocator initializer is
                // planned from source with ownership/fields' constructor
                // rule, exactly as the allocation-return certificate does.
                let plan = match plan {
                    Err(BoxPlanFailure::EndpointInactive) if store.is_some() => {
                        let body = tcx
                            .mir_drops_elaborated_and_const_checked(local.fn_did)
                            .borrow();
                        let element = match body.local_decls[local.local].ty.kind() {
                            TyKind::RawPtr(pointee, _) => Some(*pointee),
                            _ => None,
                        };
                        drop(body);
                        match (constructions.init_hirs.get(&key), element) {
                            (Some(&init_hir), Some(element)) => {
                                super::ownership_fields_constructor::derive(
                                    tcx,
                                    local.fn_did,
                                    tcx.hir_node(init_hir).expect_expr(),
                                    element,
                                )
                                .map(|constructor| BoxPlan {
                                    shape: constructor.shape,
                                    optional: false,
                                    expr_edits: vec![constructor.edit],
                                    delete_statements: Vec::new(),
                                    receipts: vec![format!(
                                        "box-param-constructor count={} shape={:?}",
                                        constructor.count, constructor.shape
                                    )],
                                    fabricated_extent: false,
                                    pointee_override: None,
                                    inferred_binding: local.ty_span.is_none(),
                                    overwrite_spans: Vec::new(),
                                    retained_sink: true,
                                    implicit_scope_close: false,
                                })
                                .map_err(|_| BoxPlanFailure::EndpointInactive)
                            }
                            _ => Err(BoxPlanFailure::EndpointInactive),
                        }
                    }
                    other => other,
                };
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
        // **R531-4 (iii) — an OPTIONAL owner moves into the consuming formal.**
        // A producer that can return null makes its certified receiver an
        // `Option<Box<T>>`, and the call hands that owner on as written, so
        // the formal takes the same type: `free(NULL)` is legal C and
        // `drop(None)` is its image. The formal's derefs read through
        // `as_deref_mut().unwrap()` — rendered by the certificate's own owner
        // walk — and a `None` reaching one is a null deref in the input (§28).
        // Admitted only where one type serves the whole chain and nothing
        // else needs an edit: every member optional, the sink a free, a sized
        // owner, and no raw exposure wrapper to re-enter ownership.
        let optional = optional_members > 0;
        // **R561-4 W2 — a MIXED chain.** One member optional (buffer's
        // `buffer_slice` returns null on a range error) and the rest not: the
        // formal is `Option<Box<T>>` for all of them and each non-optional
        // member passes `Some(x)` at its call — `drop(Some(b))` frees as
        // `free(b)`, `drop(None)` is `free(NULL)`. A member that is the
        // caller's own parameter (rung 2) belongs to another chain, which
        // makes no such edit, so the mix still holds there.
        let mut optional_wraps: Vec<BoxExprEdit> = Vec::new();
        let mut mixed_refusal = None;
        if optional && optional_members != member_plans.len() {
            // Per CALL, not per member: a re-seated member (W1) passes one
            // generation at each of its calls.
            for (key, span) in &member_args {
                if member_plans
                    .iter()
                    .any(|(k, plan, _, _)| k == key && plan.optional)
                {
                    continue;
                }
                if moved_on_members.contains(key) {
                    mixed_refusal =
                        Some("box-param-caller-retains:{callee_path}:optional-owner-mixed");
                    break;
                }
                let span = *span;
                let text = tcx
                    .sess
                    .source_map()
                    .span_to_snippet(span)
                    .unwrap_or_default();
                optional_wraps.push(BoxExprEdit {
                    span,
                    replacement: format!("Some({text})"),
                    receipt: "box-param-optional-formal-some",
                });
            }
        }
        if optional {
            let refusal = if mixed_refusal.is_some() {
                mixed_refusal
            } else if frees.len() != 1 || store.is_some() || moved_on.is_some() {
                Some("box-param-shape:{callee_path}:optional-owner-sink")
            } else if member_plans
                .iter()
                .any(|(_, plan, _, _)| matches!(plan.shape, BoxShape::Slice))
            {
                Some("box-param-shape:{callee_path}:optional-owner-slice")
            } else if raw_surface(param.fn_did) {
                Some("chain-endpoint-raw:{callee_path}:optional-owner")
            } else {
                None
            };
            if let Some(refusal) = refusal {
                hold(refusal.replace("{callee_path}", &callee_path), &mut out);
                continue;
            }
        }
        // R427-4: an EXPORTED consumer whose pointee's surface closes HAS a
        // caller — the exposure family's wrapper, which re-enters ownership
        // (`__crat_safe_f(Box::from_raw(p))`, report 010's arm) — so the
        // chain is the formal alone. Every other no-caller formal keeps the
        // hold.
        let exported_pair = call_count == 0 && {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(param.fn_did)
                .borrow();
            matches!(body.local_decls[param.local].ty.kind(),
                    TyKind::RawPtr(pointee, _) if exported_pairs.closes(tcx, *pointee))
        };
        // **R531-4 (vi) / R534-1 (USER) — the exported-consumer waiver**, the
        // mirror of R517-9's producer waiver: an exported
        // consumer nothing in the program calls, whose body consumes the
        // formal (one free, no store, no move on), takes the owner — the
        // caller is outside the program, and under R443 the block it hands in
        // is one the system allocator made, released by our drop. A body that
        // tests the formal for null — or simply hands it on from a producer
        // that returned `None` — passes `NULL` legally, so the formal is an
        // `Option<Box<T>>` (below). CONFIRMED by the user (R534-1). Receipted
        // per site; never a lending body, never an unexported consumer.
        let consumer_waiver = call_count == 0
            && !exported_pair
            // The sink must be the free. A lending body never reaches here (A9's
            // lend branch above); a store or a move on of the waived
            // `Option` formal is refused by the owner walk below
            // (`optional-owner-escapes`).
            && no_caller_export;
        if call_count == 0 && !exported_pair && !consumer_waiver {
            hold(format!("box-param-no-callers:{callee_path}"), &mut out);
            continue;
        }
        if let Some(form) = deferred_use.filter(|_| !consumer_waiver) {
            hold(
                format!("box-param-callee-use:{callee_path}:{form}"),
                &mut out,
            );
            continue;
        }
        // The waived formal is ALWAYS `Option<Box<T>>`: its caller is outside
        // the program, and a C handle may be null there (`ht_create` returns
        // `None` on failure; `free(NULL)` is legal C) — `None` is null's image
        // (R534-1: ht's pair closes as `ht_create() -> Option<Box<ht>>` /
        // `ht_destroy(table: Option<Box<ht>>)`). Its uses are the owner walk's.
        let optional = optional || consumer_waiver;
        let Some(param_slot) = slot_of(param) else { continue };
        // The formal's kind: Owning admits; Raw admits when every caller
        // transfers a CERTIFIED owner (A1-c) — the same licensing wall R410-5
        // §1 named for the allocation local, superseded on the same source
        // proof (the formal is freed once, its other uses are derefs, every
        // caller moves an owner it never touches again). A STORE sink
        // (W6A-C2) supersedes Raw AND Ref on its own proof: the model reads a
        // formal it never sees freed as a borrow, and the store through
        // memory is exactly what refutes that reading — the same finding
        // A1-d's lend walk made (`*slot = it` is not a lend, report 006).
        let formal_kind = model.get(&param_slot).copied();
        let certified_callers = member_plans.iter().all(|(k, _, _, _)| {
            certificates.plans.contains_key(k) || contract_plans.contains_key(k)
        });
        if !(formal_kind == Some(SlotKind::Owning)
            || (formal_kind == Some(SlotKind::Raw) && certified_callers)
            || (store.is_some() && matches!(formal_kind, Some(SlotKind::Raw | SlotKind::Ref))))
        {
            hold(
                format!("box-param-model:{}:{formal_kind:?}", param.label),
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
        if shapes.len() > 1 || (shapes.is_empty() && !(exported_pair || consumer_waiver)) {
            hold(
                format!("box-param-shape:{callee_path}:callers-disagree"),
                &mut out,
            );
            continue;
        }
        let (slice, pointee_override) = match shapes.into_iter().next() {
            Some(shape) => shape,
            // R427-4: the exported pair has no caller to read a shape from;
            // the formal's own pointee decides, and only a SIZED one — a
            // `Box<[T]>` formal would need an extent the surface does not
            // carry.
            None if exported_pair || consumer_waiver => (false, None),
            None => {
                hold(format!("box-param-shape:{callee_path}:no-shape"), &mut out);
                continue;
            }
        };
        // R419-3 / R423-7 (relays wave-6a/011, /013): the consuming callee is
        // a fn-pointer-web member or a positive seed, so its converted
        // signature sits behind the exposure family's raw wrapper. The wrapper
        // re-enters ownership for a SIZED formal
        // (`__crat_safe_f(Box::from_raw(p))`) and every in-crate caller binds
        // to the safe inner name; a `Box<[T]>` formal has no extent at the raw
        // surface, so that chain still holds typed.
        if slice && raw_surface(param.fn_did) {
            hold(format!("chain-endpoint-raw:{callee_path}:slice"), &mut out);
            continue;
        }
        if pointee_override.is_some() {
            hold(
                format!("box-param-shape:{callee_path}:pointee-override"),
                &mut out,
            );
            continue;
        }
        let pointee_text = {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(param.fn_did)
                .borrow();
            match body.local_decls[param.local].ty.kind() {
                TyKind::RawPtr(pointee, _) => format!("{pointee}"),
                _ => String::new(),
            }
        };
        // The chain's element accesses: slice owners index, sized owners deref.
        let mut expr_edits: Vec<BoxExprEdit> = match (frees.first(), store) {
            (Some((call, _)), _) => vec![BoxExprEdit {
                span: *call,
                replacement: format!("drop({name})"),
                receipt: "box-param-c-free-site-drop",
            }],
            // W6A-C2: ownership leaves Rust's hands into C's storage exactly
            // where the source stored it; the cast the source wrote around
            // the value stays (the raw place keeps its own type).
            (None, Some((value, _))) => vec![BoxExprEdit {
                span: value,
                // A slice owner's `into_raw` is a fat pointer; the place keeps
                // the thin type the source gave it.
                replacement: if slice {
                    format!("Box::into_raw({name}) as *mut {pointee_text}")
                } else {
                    format!("Box::into_raw({name})")
                },
                receipt: "box-param-store-transfer",
            }],
            // **Rung 2**: the move on needs no edit at all — the argument is
            // the owner itself and the callee's formal is a `Box` too, so the
            // call keeps every character it had.
            (None, None) => Vec::new(),
        };
        let mut shape_failure = None;
        for (edit, is_formals) in param_uses.iter().map(|e| (e, true)).chain(
            member_plans
                .iter()
                .flat_map(|(_, _, _, uses)| uses.iter().map(|e| (e, false))),
        ) {
            let text = tcx
                .sess
                .source_map()
                .span_to_snippet(edit.span)
                .unwrap_or_default();
            // A SIZED owner's use that is ALREADY the deref — `(*p)`, the
            // whole of a struct owner's field projections (rung 1 of avl's
            // ladder admitted them as uses; R450-8 rung 3 is the first chain
            // whose formal has only these) — reads a `Box<T>` exactly as it
            // read the raw pointer. It needs no edit, and emitting one would
            // claim an interval for no change. Only the FORMAL's own uses take
            // this exit: a member's edits are counted for the split below.
            if !slice
                && is_formals
                && let Some(root) = text.strip_prefix("(*").and_then(|t| t.strip_suffix(')'))
                && !root.contains('.')
            {
                continue;
            }
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
        // R531-4 (iii): an optional formal's uses are the certificate's owner
        // walk's (derefs through `as_deref_mut().unwrap()`, null tests as
        // `is_none` / `is_some`, lends bridged); only the free is this
        // chain's (`drop`, above). A store, a transfer or a return of the
        // formal would need a sink of its own, so it holds.
        let param_edits = if optional {
            let lend_oracle =
                super::return_certificate::LendOracle::new(tcx, functions, slots, model);
            match super::return_certificate::owner_uses(
                tcx,
                param,
                BoxShape::Sized,
                true,
                false,
                &frees,
                &|did, index| lend_oracle.lend(did, index),
                &|did, index| consuming.contains(&(did, index)),
                &|_| false,
            ) {
                Ok(uses)
                    if uses.stores.is_empty()
                        && uses.transfers.is_empty()
                        && uses.returns.is_empty() =>
                {
                    let mut edits = param_edits
                        .into_iter()
                        .filter(|edit| edit.receipt == "box-param-c-free-site-drop")
                        .collect::<Vec<_>>();
                    edits.extend(uses.edits);
                    edits
                }
                Ok(_) => {
                    hold(
                        format!("box-param-callee-use:{callee_path}:optional-owner-escapes"),
                        &mut out,
                    );
                    continue;
                }
                Err(form) => {
                    hold(
                        format!("box-param-callee-use:{callee_path}:optional:{form}"),
                        &mut out,
                    );
                    continue;
                }
            }
        } else {
            param_edits
        };
        let wrapped_members = optional_wraps.len();
        let mut param_edits = param_edits;
        param_edits.extend(optional_wraps);
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
            "box-param-chain callee={callee_path} index={hir_index} sink={} pointee={pointee} shape={} callers={call_count}{} members={} formal_model={formal_kind:?}",
            // R450-8 rung 2: a chain whose sink is the MOVE ON says so, or the
            // census would read it as a free it never emitted.
            match (store.is_some(), moved_on.is_some()) {
                (true, _) => "store",
                (_, true) => "move-on",
                _ => "free",
            },
            if slice { "slice" } else { "sized" },
            if exported_pair { " exported-pair-closure" } else { "" },
            members.join(",")
        ));
        if consumer_waiver {
            out.receipts
                .push(format!("exported-consumer-waiver callee={callee_path}"));
        }
        let mut chain_callers: Vec<LocalDefId> = Vec::new();
        if store.is_some() {
            out.store_members
                .extend(member_plans.iter().map(|(key, _, _, _)| *key));
        }
        for (key, mut plan, _, uses) in member_plans {
            plan.expr_edits.extend(member_edits.drain(..uses.len()));
            if !chain_callers.contains(&key.0) {
                chain_callers.push(key.0);
            }
            if moved_on_members.contains(&key) {
                continue;
            }
            out.plans.insert(key, plan);
        }
        out.chains.push((param.fn_did, chain_callers));
        out.plans.insert(
            (param.fn_did, param.hir_id),
            BoxPlan {
                shape: if slice { BoxShape::Slice } else { BoxShape::Sized },
                optional,
                expr_edits: param_edits,
                delete_statements: Vec::new(),
                receipts: vec![format!(
                    "box-param-owning-formal callee={callee_path} index={hir_index} callers={call_count}{}{}",
                    if optional { " optional-owner" } else { "" },
                    if wrapped_members > 0 {
                        format!(" some-wrapped-members={wrapped_members}")
                    } else {
                        String::new()
                    }
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
