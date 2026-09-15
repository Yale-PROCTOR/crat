//! **wave-6f — struct fields as references (rule W6F-1).**
//!
//! A program-defined struct's raw-pointer FIELD whose depth-0 slot the frozen
//! model settles `Ref` becomes a shared borrowed form — `&'a T`, `&'a [T]`, or
//! their `Option` twins under §29 — with one generated lifetime parameter on
//! the struct. The field conversion is a TRANSACTION over every creator, store,
//! load, read and signature mention of the field (design of record:
//! `2026-09-06-field-and-depth-wave-design.md` §2.1): all sites admit, or the
//! field stays raw with a typed hold and every subject that depended on it
//! keeps its prior reason.
//!
//! # What the rule decides, and from which facts
//!
//! - **Kind**: `SlotRef::Field` at depth 0 in the frozen model. Never a
//!   rewriter guess.
//! - **Mutability**: the Foster mutability qualifier of the field. Only
//!   SHARED fields are admitted this wave (`&'a mut` fields need the
//!   view-pair analysis; `field-mutable-held`).
//! - **Form**: the field's own uses. An element read through the field
//!   (`*(s.f).offset(k)`) or an offset of it asks for `&[T]`; Foster fatness
//!   must corroborate (`Arr`), exactly the S3.2′-2 authority split.
//! - **Nullability** (§29): a null literal at a struct literal or store, or an
//!   `is_null` test on a load, selects the `Option` twin.
//! - **Lifetime**: a store `s.f = p` where `p` is a PARAMETER of the storing
//!   function ties the struct instance to that parameter's borrow: the
//!   function gains one generated lifetime, placed on `p`'s reference type and
//!   on every mention of the struct in that signature. A store from a local or
//!   from a raw expression is held this wave.
//!
//! # Soundness (conditional on a UB-free input, §28)
//!
//! Every dereference through the field in the emitted program is one the
//! input performs at the same point, so the referent is live there; the
//! struct's lifetime parameter only NARROWS where Rust lets the struct be used
//! (the compile gate reverts a struct that outlives its referent, it never
//! widens). A shared field never forms a `&mut`. A null literal becomes `None`
//! and a load into a non-nullable local carries the `.unwrap()` bridge that
//! the local's own thin decision already assumes. `&'a T` and `Option<&'a T>`
//! have the layout of the raw pointer they replace, so a struct that crosses a
//! foreign boundary keeps its ABI.

use std::collections::BTreeMap;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, Node, QPath, UnOp,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_span::Span;

use super::{
    Decision, DecisionTable, Subject, SubjectKind,
    exposure::ExposureSurfacePlan,
    seam::{self, Form},
};
use crate::{
    analyses::{
        borrow_ownership::{
            SlotKind, crate_slots::CrateSlots, slots::StructFieldSlot, solver::SlotRef,
        },
        type_qualifier::foster::{
            fatness::{Fatness, fatness_analysis},
            mutability::mutability_analysis,
        },
    },
    utils::rustc::RustProgram,
};

pub(crate) type NodeKey = (LocalDefId, HirId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct FieldKey {
    pub struct_did: LocalDefId,
    pub field_index: usize,
}

impl FieldKey {
    fn order_key(self) -> (u32, usize) {
        (self.struct_did.local_def_index.as_u32(), self.field_index)
    }
}

impl PartialOrd for FieldKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FieldKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.order_key().cmp(&other.order_key())
    }
}

fn sorted_owners(owners: impl IntoIterator<Item = LocalDefId>) -> Vec<LocalDefId> {
    let mut out: Vec<LocalDefId> = owners.into_iter().collect();
    out.sort_by_key(|did| did.local_def_index.as_u32());
    out.dedup();
    out
}

/// What the right-hand side of a store or literal initializer is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Rhs {
    /// `0 as *mut T` — becomes `None`.
    Null,
    /// A subject binding of the storing function (a parameter or a local).
    Subject(NodeKey),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SiteKind {
    /// `S { .., f: RHS, .. }` — the initializer expression span.
    Literal,
    /// `PLACE.f = RHS` — the right-hand side expression span.
    Store,
    /// `let x = PLACE.f;` — the initializer expression span; `x` is a subject.
    Load,
    /// `*PLACE.f` on a thin field — the field expression span.
    Deref,
    /// `*(PLACE.f).offset(k)` on a slice field — the outer deref span.
    Element,
    /// `(PLACE.f).offset(k)` used as a pointer value — the method call span.
    Offset,
    /// `(PLACE.f).is_null()` — the method call span.
    IsNull,
}

#[derive(Clone, Debug)]
pub(crate) struct Site {
    pub owner: LocalDefId,
    pub kind: SiteKind,
    /// The span the emitted replacement is grafted onto.
    pub span: Span,
    /// Source text of the field expression itself (`(*it)._table`).
    pub field_text: String,
    pub rhs: Option<Rhs>,
    /// The loaded local (`Load` only).
    pub local: Option<NodeKey>,
    /// The index/offset operand rendered as a `usize` expression
    /// (`Element` / `Offset` only).
    pub index_text: Option<String>,
}

/// One function whose signature mentions the struct.
#[derive(Clone, Debug)]
pub(crate) struct Mention {
    pub owner: LocalDefId,
    /// Parameter subjects of `owner` stored into the field (the lifetime tie).
    pub stored_params: Vec<NodeKey>,
}

#[derive(Clone, Debug)]
pub(crate) struct Candidate {
    pub key: FieldKey,
    pub struct_path: String,
    pub field_name: String,
    pub form: Form,
    pub sites: Vec<Site>,
    pub mentions: Vec<Mention>,
    /// `impl … for S` items that must carry the struct's lifetime.
    pub impls: Vec<LocalDefId>,
    /// Every function carrying a site or a mention, in definition order.
    pub owners: Vec<LocalDefId>,
}

/// The candidate table handed to the ladder: which escapes are discharged and
/// which unannotated locals may take their type from a converting field.
#[derive(Clone, Debug, Default)]
pub(crate) struct FieldCandidates {
    pub candidates: BTreeMap<FieldKey, Candidate>,
    /// `(subject, rhs span)` of every store / literal whose RHS is a subject.
    store_permits: FxHashSet<(NodeKey, Span)>,
    /// Loaded local → the field it takes its form from.
    load_permits: FxHashMap<NodeKey, FieldKey>,
    /// Fields that were candidates by the model but are held, with the cause.
    pub holds: Vec<(FieldKey, String, String, String)>,
}

impl FieldCandidates {
    pub(crate) fn load_permit(&self, local: NodeKey) -> Option<&Candidate> {
        self.load_permits
            .get(&local)
            .and_then(|key| self.candidates.get(key))
    }

    /// The form a stored subject must take so the store is a zero-syntax or
    /// glued site: the field's own form, offered when the subject carries no
    /// contrary use of its own.
    pub(crate) fn required_store_form(&self, subject: NodeKey) -> Option<Form> {
        self.store_permits
            .iter()
            .filter(|(node, _)| *node == subject)
            .find_map(|(_, span)| {
                self.candidates.values().find_map(|candidate| {
                    candidate
                        .sites
                        .iter()
                        .any(|site| {
                            site.span == *span
                                && matches!(site.kind, SiteKind::Store | SiteKind::Literal)
                        })
                        .then_some(candidate.form)
                })
            })
    }

    pub(crate) fn store_permit_pairs(&self) -> impl Iterator<Item = (NodeKey, Span)> + '_ {
        self.store_permits.iter().copied()
    }
}

/// One expression-level edit of the finalized transaction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExpressionEdit {
    pub owner: LocalDefId,
    pub span: Span,
    pub replacement: String,
    pub kind: &'static str,
}

/// A function's signature plan: the generated lifetime, the parameters that
/// carry it and whether the return type mentions the struct.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SignaturePlan {
    pub owner: LocalDefId,
    pub lifetime_params: Vec<NodeKey>,
    /// The same parameters as HIR input positions.
    pub lifetime_positions: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FieldTransaction {
    pub key: FieldKey,
    pub struct_path: String,
    pub field_name: String,
    pub form: Form,
    /// Every function carrying a site or a mention.
    pub owners: Vec<LocalDefId>,
    /// The owners whose sites depend on a SUBJECT decision (a store or
    /// literal from a subject, a load into a subject, a signature plan): the
    /// transaction is withdrawn when any of them is reverted, and they revert
    /// together. Owners of value-independent sites (a null literal, an element
    /// read) keep their edits under any revert set.
    pub dependent_owners: Vec<LocalDefId>,
    pub impls: Vec<LocalDefId>,
    pub signature_plans: Vec<SignaturePlan>,
    pub expression_edits: Vec<ExpressionEdit>,
    /// Loaded locals that receive an explicit declaration.
    pub load_locals: Vec<(NodeKey, String)>,
    pub site_count: usize,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FieldTransactions {
    pub applied: Vec<FieldTransaction>,
    /// `(struct path, field, cause)` per held field, model-Ref or withdrawn.
    pub held: Vec<(String, String, String)>,
}

impl FieldTransactions {
    /// Parameter positions (HIR index) of `callee` that a signature plan ties
    /// to the struct's lifetime.
    pub(crate) fn tied_parameters(&self, callee: LocalDefId) -> std::collections::BTreeSet<usize> {
        self.applied
            .iter()
            .flat_map(|t| t.signature_plans.iter())
            .filter(|plan| plan.owner == callee)
            .flat_map(|plan| plan.lifetime_positions.iter().copied())
            .collect()
    }

    pub(crate) fn owner_sets(&self) -> Vec<Vec<LocalDefId>> {
        self.applied
            .iter()
            .map(|t| t.dependent_owners.clone())
            .collect()
    }

    /// A transaction survives a revert set iff none of its dependent owners
    /// is reverted.
    pub(crate) fn active<'a>(
        &'a self,
        reverted: &FxHashSet<LocalDefId>,
    ) -> impl Iterator<Item = &'a FieldTransaction> + 'a {
        let reverted = reverted.clone();
        self.applied.iter().filter(move |t| {
            t.dependent_owners
                .iter()
                .all(|owner| !reverted.contains(owner))
        })
    }

    pub(crate) fn receipt_tsv(&self, tcx: TyCtxt<'_>) -> String {
        let mut out = String::from(
            "struct\tfield\tstatus\tform\tsites\towners\timpls\tsignature_plans\tcause\n",
        );
        for t in &self.applied {
            out.push_str(&format!(
                "{}\t{}\tapplied\t{}\t{}\t{}\t{}\t{}\t-\n",
                t.struct_path,
                t.field_name,
                t.form.key(),
                t.site_count,
                t.owners
                    .iter()
                    .map(|o| tcx.def_path_str(o.to_def_id()))
                    .collect::<Vec<_>>()
                    .join(","),
                t.impls.len(),
                t.signature_plans
                    .iter()
                    .map(|p| tcx.def_path_str(p.owner.to_def_id()))
                    .collect::<Vec<_>>()
                    .join(","),
            ));
        }
        for (struct_path, field, cause) in &self.held {
            out.push_str(&format!(
                "{struct_path}\t{field}\theld\t-\t-\t-\t-\t-\t{cause}\n"
            ));
        }
        out
    }
}

fn adt_local(ty: Ty<'_>) -> Option<LocalDefId> {
    match ty.kind() {
        TyKind::Adt(def, _) => def.did().as_local(),
        _ => None,
    }
}

/// Peel references and raw pointers to the struct they point at.
fn struct_of(ty: Ty<'_>) -> Option<LocalDefId> {
    let mut ty = ty;
    loop {
        match ty.kind() {
            TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) => ty = *inner,
            _ => return adt_local(ty),
        }
    }
}

fn mentions_struct(ty: Ty<'_>, target: LocalDefId) -> bool {
    ty.walk().any(|arg| {
        arg.as_type()
            .and_then(adt_local)
            .is_some_and(|did| did == target)
    })
}

fn is_unsigned(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Uint(_))
}

/// The index operand of `offset(k)` as a `usize` expression, admitted only
/// when `k` is `E as isize` with `E` unsigned or a non-negative literal.
fn index_text(tcx: TyCtxt<'_>, owner: LocalDefId, operand: &Expr<'_>) -> Option<String> {
    let typeck = tcx.typeck(owner);
    let sm = tcx.sess.source_map();
    match operand.kind {
        ExprKind::Cast(inner, _) if is_unsigned(typeck.expr_ty(inner)) => {
            let text = sm.span_to_snippet(inner.span).ok()?;
            Some(format!("({text}) as usize"))
        }
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(value, _) => Some(format!("{}usize", value.get())),
            _ => None,
        },
        _ => None,
    }
}

struct Collector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    subjects: &'a FxHashMap<HirId, NodeKey>,
    targets: &'a FxHashMap<FieldKey, usize>,
    struct_dids: &'a FxHashSet<LocalDefId>,
    sites: &'a mut FxHashMap<FieldKey, Vec<Site>>,
    holds: &'a mut FxHashMap<FieldKey, String>,
}

impl<'tcx> Collector<'_, 'tcx> {
    fn hold(&mut self, key: FieldKey, cause: String) {
        self.holds.entry(key).or_insert(cause);
    }

    fn rhs(&self, expr: &Expr<'_>) -> Result<Rhs, &'static str> {
        if super::emitability::is_zero_literal(expr) {
            return Ok(Rhs::Null);
        }
        if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
            && let Res::Local(binding) = path.res
        {
            return match self.subjects.get(&binding) {
                Some(node) => Ok(Rhs::Subject(*node)),
                None => Err("store-source-not-a-subject"),
            };
        }
        Err("store-source-raw-expression")
    }

    fn field_key(&self, field: &Expr<'tcx>) -> Option<FieldKey> {
        let ExprKind::Field(base, _) = field.kind else { return None };
        let typeck = self.tcx.typeck(self.owner);
        let struct_did = adt_local(typeck.expr_ty_adjusted(base))?;
        if !self.struct_dids.contains(&struct_did) {
            return None;
        }
        let field_index = typeck.opt_field_index(field.hir_id)?.as_usize();
        let key = FieldKey {
            struct_did,
            field_index,
        };
        self.targets.contains_key(&key).then_some(key)
    }

    fn push(&mut self, key: FieldKey, site: Site) {
        self.sites.entry(key).or_default().push(site);
    }

    fn classify_field_use(&mut self, key: FieldKey, field: &Expr<'tcx>) {
        let tcx = self.tcx;
        let sm = tcx.sess.source_map();
        let Ok(field_text) = sm.span_to_snippet(field.span) else {
            self.hold(key, "field-text-unrenderable".to_owned());
            return;
        };
        let owner = self.owner;
        let site = |kind, span, rhs, local, index_text| Site {
            owner,
            kind,
            span,
            field_text: field_text.clone(),
            rhs,
            local,
            index_text,
        };
        let Node::Expr(parent) = tcx.parent_hir_node(field.hir_id) else {
            // `let x = PLACE.f;`
            if let Node::LetStmt(local) = tcx.parent_hir_node(field.hir_id)
                && local.init.is_some_and(|init| init.hir_id == field.hir_id)
            {
                if local.ty.is_some() {
                    self.hold(key, "load-into-annotated-local".to_owned());
                    return;
                }
                let rustc_hir::PatKind::Binding(_, binding, _, None) = local.pat.kind else {
                    self.hold(key, "load-into-pattern".to_owned());
                    return;
                };
                let Some(node) = self.subjects.get(&binding).copied() else {
                    self.hold(key, "load-consumer-not-a-subject".to_owned());
                    return;
                };
                self.push(
                    key,
                    site(SiteKind::Load, field.span, None, Some(node), None),
                );
                return;
            }
            self.hold(key, "field-use-outside-expression".to_owned());
            return;
        };
        match parent.kind {
            ExprKind::Assign(lhs, rhs, _) if lhs.hir_id == field.hir_id => match self.rhs(rhs) {
                Ok(value) => self.push(
                    key,
                    site(SiteKind::Store, rhs.span, Some(value), None, None),
                ),
                Err(cause) => self.hold(key, cause.to_owned()),
            },
            ExprKind::Unary(UnOp::Deref, _) => {
                self.push(key, site(SiteKind::Deref, field.span, None, None, None));
            }
            ExprKind::MethodCall(segment, receiver, args, _) if receiver.hir_id == field.hir_id => {
                let method = segment.ident.name.as_str().to_owned();
                match (method.as_str(), args) {
                    ("is_null", []) => {
                        self.push(key, site(SiteKind::IsNull, parent.span, None, None, None));
                    }
                    ("offset" | "add", [operand]) => {
                        let Some(index) = index_text(tcx, owner, operand) else {
                            self.hold(key, "field-offset-sign-unknown".to_owned());
                            return;
                        };
                        match tcx.parent_hir_node(parent.hir_id) {
                            Node::Expr(grand)
                                if matches!(grand.kind, ExprKind::Unary(UnOp::Deref, _)) =>
                            {
                                self.push(
                                    key,
                                    site(SiteKind::Element, grand.span, None, None, Some(index)),
                                );
                            }
                            Node::Expr(grand) if matches!(grand.kind, ExprKind::Cast(..)) => {
                                self.push(
                                    key,
                                    site(SiteKind::Offset, parent.span, None, None, Some(index)),
                                );
                            }
                            _ => self.hold(key, "field-offset-consumer-unsupported".to_owned()),
                        }
                    }
                    _ => self.hold(key, format!("field-method-unsupported:{method}")),
                }
            }
            ExprKind::Call(..) => {
                self.hold(key, "field-transaction-incomplete:call-argument".to_owned())
            }
            ExprKind::AddrOf(..) => self.hold(
                key,
                "field-transaction-incomplete:address-of-field".to_owned(),
            ),
            ExprKind::Cast(..) => {
                self.hold(key, "field-transaction-incomplete:cast-of-field".to_owned())
            }
            _ => self.hold(key, "field-transaction-incomplete:use-shape".to_owned()),
        }
    }
}

impl<'tcx> Visitor<'tcx> for Collector<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Struct(_, fields, _) => {
                let typeck = self.tcx.typeck(self.owner);
                if let Some(struct_did) = adt_local(typeck.expr_ty(expr))
                    && self.struct_dids.contains(&struct_did)
                {
                    for field in fields {
                        let Some(field_index) = typeck.opt_field_index(field.hir_id) else {
                            continue;
                        };
                        let key = FieldKey {
                            struct_did,
                            field_index: field_index.as_usize(),
                        };
                        if !self.targets.contains_key(&key) {
                            continue;
                        }
                        match self.rhs(field.expr) {
                            Ok(value) => {
                                let owner = self.owner;
                                self.push(
                                    key,
                                    Site {
                                        owner,
                                        kind: SiteKind::Literal,
                                        span: field.expr.span,
                                        field_text: field.ident.to_string(),
                                        rhs: Some(value),
                                        local: None,
                                        index_text: None,
                                    },
                                );
                            }
                            Err(cause) => self.hold(key, format!("literal-{cause}")),
                        }
                    }
                }
            }
            ExprKind::Field(..) => {
                if let Some(key) = self.field_key(expr) {
                    self.classify_field_use(key, expr);
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

/// Derive the candidate transactions from the frozen model and the program's
/// syntax. `withdrawn` carries the fields a previous finalization refused.
pub(crate) fn derive(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    subjects: &[Subject],
    withdrawn: &BTreeMap<FieldKey, String>,
) -> FieldCandidates {
    let tcx = program.tcx;
    let mut out = FieldCandidates::default();
    let struct_dids: FxHashSet<LocalDefId> = program.structs.iter().copied().collect();
    let mutability = mutability_analysis(program);
    let fatness = fatness_analysis(program);

    // 1. Model-Ref, depth-1, shared fields of program-defined structs.
    let mut targets: FxHashMap<FieldKey, usize> = FxHashMap::default();
    let mut names: BTreeMap<FieldKey, (String, String)> = BTreeMap::new();
    let mut fat: FxHashSet<FieldKey> = FxHashSet::default();
    for &struct_did in &program.structs {
        let ty = tcx.type_of(struct_did).skip_binder();
        let TyKind::Adt(adt, substs) = ty.kind() else { continue };
        if !adt.is_struct() {
            continue;
        }
        let struct_path = tcx.def_path_str(struct_did.to_def_id());
        let named_fields = adt.non_enum_variant().ctor.is_none();
        let self_referential = adt
            .all_fields()
            .any(|field_def| mentions_struct(field_def.ty(tcx, substs), struct_did));
        for (field_index, field_def) in adt.all_fields().enumerate() {
            let field_ty = field_def.ty(tcx, substs);
            let TyKind::RawPtr(..) = field_ty.kind() else { continue };
            let key = FieldKey {
                struct_did,
                field_index,
            };
            let slot = StructFieldSlot {
                struct_did,
                field_index,
            };
            let Some(slot_id) = slots.field_slots.slot_for_field_depth(slot, 0) else { continue };
            if model.get(&SlotRef::Field(slot_id)) != Some(&SlotKind::Ref) {
                continue;
            }
            let field_name = field_def.name.to_string();
            names.insert(key, (struct_path.clone(), field_name.clone()));
            if let Some(cause) = withdrawn.get(&key) {
                out.holds
                    .push((key, struct_path.clone(), field_name, cause.clone()));
                continue;
            }
            if let TyKind::RawPtr(pointee, _) = field_ty.kind()
                && matches!(pointee.kind(), TyKind::Adt(def, _) if tcx.lang_items().c_void() == Some(def.did()))
            {
                out.holds.push((
                    key,
                    struct_path.clone(),
                    field_name,
                    "held:void-pointee".into(),
                ));
                continue;
            }
            if crate::analyses::borrow_ownership::crate_slots::ptr_chain_depth(field_ty) != 1 {
                out.holds.push((
                    key,
                    struct_path.clone(),
                    field_name,
                    "field-depth-unsupported".into(),
                ));
                continue;
            }
            if tcx.def_span(struct_did).from_expansion() {
                out.holds.push((
                    key,
                    struct_path.clone(),
                    field_name,
                    "struct-from-expansion".into(),
                ));
                continue;
            }
            if !named_fields {
                out.holds.push((
                    key,
                    struct_path.clone(),
                    field_name,
                    "struct-tuple-shape".into(),
                ));
                continue;
            }
            if self_referential {
                out.holds.push((
                    key,
                    struct_path.clone(),
                    field_name,
                    "field-transaction-incomplete:self-reference".into(),
                ));
                continue;
            }
            if mutability
                .struct_field_fact(struct_did, field_index, 0)
                .is_none_or(|fact| fact.is_mutable())
            {
                out.holds.push((
                    key,
                    struct_path.clone(),
                    field_name,
                    "field-mutable-held".into(),
                ));
                continue;
            }
            if matches!(
                fatness.struct_field_fact(struct_did, field_index, 0),
                Some(Fatness::Arr)
            ) {
                fat.insert(key);
            }
            targets.insert(key, field_index);
        }
    }
    if targets.is_empty() {
        return out;
    }

    // 2. Every site, over every program function.
    let subject_by_binding: FxHashMap<HirId, NodeKey> = subjects
        .iter()
        .map(|s| (s.hir_id, (s.fn_did, s.hir_id)))
        .collect();
    let mut sites: FxHashMap<FieldKey, Vec<Site>> = FxHashMap::default();
    let mut holds: FxHashMap<FieldKey, String> = FxHashMap::default();
    for &owner in &program.functions {
        let Some(body_id) = tcx.hir_node_by_def_id(owner).body_id() else { continue };
        let mut collector = Collector {
            tcx,
            owner,
            subjects: &subject_by_binding,
            targets: &targets,
            struct_dids: &struct_dids,
            sites: &mut sites,
            holds: &mut holds,
        };
        collector.visit_body(tcx.hir_body(body_id));
    }

    // 3. Type mentions: signatures, other struct fields, statics, impls.
    let mut impls_of: FxHashMap<LocalDefId, Vec<LocalDefId>> = FxHashMap::default();
    let mut container_holds: FxHashMap<LocalDefId, String> = FxHashMap::default();
    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        match item.kind {
            rustc_hir::ItemKind::Impl(im) => {
                let self_ty = tcx.type_of(item.owner_id.def_id).skip_binder();
                if let Some(did) = adt_local(self_ty)
                    && struct_dids.contains(&did)
                {
                    if item.span.from_expansion() || im.of_trait.is_none() {
                        container_holds
                            .entry(did)
                            .or_insert_with(|| "impl-shape-unsupported".to_owned());
                    }
                    impls_of.entry(did).or_default().push(item.owner_id.def_id);
                }
            }
            rustc_hir::ItemKind::Struct(..) | rustc_hir::ItemKind::Union(..) => {
                let did = item.owner_id.def_id;
                let ty = tcx.type_of(did).skip_binder();
                if let TyKind::Adt(adt, substs) = ty.kind() {
                    for field_def in adt.all_fields() {
                        let field_ty = field_def.ty(tcx, substs);
                        for target in &struct_dids {
                            if *target != did && mentions_struct(field_ty, *target) {
                                container_holds.entry(*target).or_insert_with(|| {
                                    "field-transaction-incomplete:nested-container".to_owned()
                                });
                            }
                        }
                    }
                }
            }
            rustc_hir::ItemKind::Static(..) | rustc_hir::ItemKind::Const(..) => {
                let ty = tcx.type_of(item.owner_id.def_id).skip_binder();
                for target in &struct_dids {
                    if mentions_struct(ty, *target) {
                        container_holds.entry(*target).or_insert_with(|| {
                            "field-transaction-incomplete:static-container".to_owned()
                        });
                    }
                }
            }
            rustc_hir::ItemKind::TyAlias(..) => {
                let ty = tcx.type_of(item.owner_id.def_id).skip_binder();
                for target in &struct_dids {
                    if mentions_struct(ty, *target) {
                        container_holds.entry(*target).or_insert_with(|| {
                            "field-transaction-incomplete:type-alias".to_owned()
                        });
                    }
                }
            }
            _ => {}
        }
    }
    let mut mentions_of: FxHashMap<LocalDefId, Vec<(LocalDefId, bool, bool)>> =
        FxHashMap::default();
    for &owner in &program.functions {
        let sig = tcx.fn_sig(owner).skip_binder().skip_binder();
        for target in &struct_dids {
            let in_inputs = sig.inputs().iter().any(|ty| mentions_struct(*ty, *target));
            let in_return = mentions_struct(sig.output(), *target);
            if in_inputs || in_return {
                // A mention inside a fn-pointer or a nested container type
                // cannot take the elided instantiation.
                let simple = sig
                    .inputs()
                    .iter()
                    .chain(std::iter::once(&sig.output()))
                    .all(|ty| !mentions_struct(*ty, *target) || struct_of(*ty) == Some(*target));
                mentions_of
                    .entry(*target)
                    .or_default()
                    .push((owner, in_return, simple));
            }
        }
    }

    // 4. Assemble candidates, in declaration order; one converting field per
    // struct this wave (one generated lifetime per struct).
    let mut converting_structs: FxHashSet<LocalDefId> = FxHashSet::default();
    for (&key, (struct_path, field_name)) in &names {
        if !targets.contains_key(&key) {
            continue;
        }
        let (struct_path, field_name) = (struct_path.clone(), field_name.clone());
        let key_sites = sites.remove(&key).unwrap_or_default();
        let mut cause = holds.remove(&key);
        if cause.is_none() && converting_structs.contains(&key.struct_did) {
            cause = Some("field-transaction-incomplete:multi-field-struct".to_owned());
        }
        if cause.is_none() {
            cause = container_holds.get(&key.struct_did).cloned();
        }
        let wants_slice = key_sites
            .iter()
            .any(|site| matches!(site.kind, SiteKind::Element | SiteKind::Offset));
        if cause.is_none() && wants_slice && !fat.contains(&key) {
            cause = Some("field-fat-unlicensed".to_owned());
        }
        if cause.is_none()
            && key_sites.iter().any(|site| site.kind == SiteKind::Deref)
            && wants_slice
        {
            cause = Some("field-mixed-thin-and-fat-uses".to_owned());
        }
        if cause.is_none()
            && !key_sites
                .iter()
                .any(|site| matches!(site.kind, SiteKind::Literal | SiteKind::Store))
        {
            cause = Some("field-never-constructed".to_owned());
        }
        let nullable = key_sites
            .iter()
            .any(|site| site.kind == SiteKind::IsNull || site.rhs == Some(Rhs::Null));
        let form = if wants_slice {
            if nullable {
                Form::Opt {
                    mutable: false,
                    slice: true,
                }
            } else {
                Form::Slice { mutable: false }
            }
        } else if nullable {
            Form::Opt {
                mutable: false,
                slice: false,
            }
        } else {
            Form::Ref { mutable: false }
        };
        // Lifetime ties: a store from a local, or a stored parameter of a
        // function whose signature does not name the struct, is held.
        let mut mentions = Vec::new();
        let mut stored_by_fn: FxHashMap<LocalDefId, Vec<NodeKey>> = FxHashMap::default();
        for site in &key_sites {
            let Some(Rhs::Subject(node)) = site.rhs else { continue };
            let Some(subject) = subjects.iter().find(|s| (s.fn_did, s.hir_id) == node) else {
                continue;
            };
            match subject.kind {
                SubjectKind::Param { .. } => stored_by_fn.entry(site.owner).or_default().push(node),
                SubjectKind::Local => {
                    cause.get_or_insert_with(|| "field-store-source-local".to_owned());
                }
            }
        }
        let fn_mentions = mentions_of
            .get(&key.struct_did)
            .cloned()
            .unwrap_or_default();
        for (owner, in_return, simple) in &fn_mentions {
            if !simple {
                cause.get_or_insert_with(|| {
                    "field-transaction-incomplete:signature-shape".to_owned()
                });
            }
            let stored_params = stored_by_fn.remove(owner).unwrap_or_default();
            if *in_return && stored_params.is_empty() {
                cause.get_or_insert_with(|| "return-lifetime-unplanned".to_owned());
            }
            mentions.push(Mention {
                owner: *owner,
                stored_params,
            });
        }
        if !stored_by_fn.is_empty() {
            // A parameter stored into a struct the signature never names: the
            // struct instance is a local whose lifetime is inferred, so the
            // tie has nowhere to go unless the struct is returned (covered).
            cause.get_or_insert_with(|| "field-store-into-unmentioned-struct".to_owned());
        }
        let owners = sorted_owners(
            key_sites
                .iter()
                .map(|s| s.owner)
                .chain(mentions.iter().map(|m| m.owner)),
        );
        if let Some(cause) = cause {
            out.holds.push((key, struct_path, field_name, cause));
            continue;
        }
        converting_structs.insert(key.struct_did);
        for site in &key_sites {
            match site.kind {
                SiteKind::Store | SiteKind::Literal => {
                    if let Some(Rhs::Subject(node)) = site.rhs {
                        out.store_permits.insert((node, site.span));
                    }
                }
                SiteKind::Load => {
                    if let Some(local) = site.local {
                        out.load_permits.insert(local, key);
                    }
                }
                _ => {}
            }
        }
        out.candidates.insert(
            key,
            Candidate {
                key,
                struct_path,
                field_name,
                form,
                sites: key_sites,
                mentions,
                impls: impls_of.remove(&key.struct_did).unwrap_or_default(),
                owners,
            },
        );
    }
    out
}

/// Lift the slice-use wall of a stored subject whose EVERY use is a store
/// into a converting field: the store is the field transaction's site, and a
/// subject with no other use has no other use that could be unsupported.
/// Exact by construction — the count is over every path use of the binding.
pub(crate) fn lift_store_walls(
    tcx: TyCtxt<'_>,
    candidates: &FieldCandidates,
    slice_uses: &mut FxHashMap<NodeKey, super::emitability::SliceUses>,
) {
    let mut permitted: FxHashMap<NodeKey, FxHashSet<Span>> = FxHashMap::default();
    for (node, span) in candidates.store_permit_pairs() {
        permitted.entry(node).or_default().insert(span);
    }
    struct Uses<'a> {
        binding: HirId,
        spans: &'a mut Vec<Span>,
    }
    impl<'tcx> Visitor<'tcx> for Uses<'_> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && let Res::Local(binding) = path.res
                && binding == self.binding
            {
                self.spans.push(expr.span);
            }
            intravisit::walk_expr(self, expr);
        }
    }
    for (node, stores) in permitted {
        let Some(uses) = slice_uses.get_mut(&node) else { continue };
        let Some(unsupported) = uses.unsupported else { continue };
        if !stores.contains(&unsupported) {
            continue;
        }
        let Some(body_id) = tcx.hir_node_by_def_id(node.0).body_id() else { continue };
        let mut spans = Vec::new();
        Uses {
            binding: node.1,
            spans: &mut spans,
        }
        .visit_body(tcx.hir_body(body_id));
        if spans.iter().all(|span| stores.contains(span)) {
            uses.unsupported = None;
            uses.unsupported_is_cursor = false;
        }
    }
}

/// The finalization: every site's replacement from the FINAL decisions, or the
/// field is refused with a typed cause.
pub(crate) fn finalize(
    tcx: TyCtxt<'_>,
    candidates: &FieldCandidates,
    table: &DecisionTable,
    exposure: &super::exposure::ExposurePolicy,
) -> (FieldTransactions, BTreeMap<FieldKey, String>) {
    let mut out = FieldTransactions::default();
    let mut refused = BTreeMap::new();
    for (key, _, field, cause) in &candidates.holds {
        let struct_path = tcx.def_path_str(key.struct_did.to_def_id());
        out.held.push((struct_path, field.clone(), cause.clone()));
    }
    let decision_of = |node: NodeKey| -> Option<&Decision> {
        table
            .entries
            .iter()
            .find(|(s, _)| (s.fn_did, s.hir_id) == node)
            .map(|(_, d)| d)
    };
    let accessor = |field_text: &str, form: Form| -> String {
        match form {
            Form::Opt { .. } => format!("{field_text}.unwrap()"),
            _ => field_text.to_owned(),
        }
    };
    for candidate in candidates.candidates.values() {
        let mut cause: Option<String> = None;
        let mut edits = Vec::new();
        let mut load_locals = Vec::new();
        for owner in &candidate.owners {
            if matches!(
                exposure.plan(*owner),
                ExposureSurfacePlan::PositiveSeedShim | ExposureSurfacePlan::FnPtrRawWrapper
            ) {
                cause.get_or_insert_with(|| "field-transaction-incomplete:surface-plan".to_owned());
            }
        }
        for site in &candidate.sites {
            let field = candidate.form;
            match site.kind {
                SiteKind::Literal | SiteKind::Store => match site.rhs {
                    Some(Rhs::Null) => edits.push(ExpressionEdit {
                        owner: site.owner,
                        span: site.span,
                        replacement: "None".to_owned(),
                        kind: "field-null",
                    }),
                    Some(Rhs::Subject(node)) => {
                        let Some(decision) = decision_of(node) else {
                            cause.get_or_insert_with(|| "store-source-unknown".to_owned());
                            continue;
                        };
                        let found = seam::form_of(decision);
                        if found == Form::Raw {
                            cause.get_or_insert_with(|| {
                                format!("store-source-degraded:{}", subject_label(table, node))
                            });
                            continue;
                        }
                        // R395-2: a thin reference is a one-element claim and
                        // is never widened into a buffer the field's readers
                        // index.
                        let field_fat =
                            matches!(field, Form::Slice { .. } | Form::Opt { slice: true, .. });
                        let found_thin =
                            matches!(found, Form::Ref { .. } | Form::Opt { slice: false, .. });
                        if field_fat && found_thin {
                            cause.get_or_insert_with(|| {
                                format!("store-thin-into-fat-field:{}", subject_label(table, node))
                            });
                            continue;
                        }
                        match seam::glue(field, found, None) {
                            Ok(None) => {}
                            Ok(Some((spec, _))) => {
                                let Ok(text) = tcx.sess.source_map().span_to_snippet(site.span)
                                else {
                                    cause.get_or_insert_with(|| {
                                        "store-text-unrenderable".to_owned()
                                    });
                                    continue;
                                };
                                let Some(rendered) = spec.render(&text) else {
                                    cause.get_or_insert_with(|| {
                                        "store-glue-unrenderable".to_owned()
                                    });
                                    continue;
                                };
                                edits.push(ExpressionEdit {
                                    owner: site.owner,
                                    span: site.span,
                                    replacement: rendered,
                                    kind: "field-store-glue",
                                });
                            }
                            Err(block) => {
                                cause
                                    .get_or_insert_with(|| format!("store-glue-blocked:{block:?}"));
                            }
                        }
                    }
                    None => {
                        cause.get_or_insert_with(|| "store-source-unknown".to_owned());
                    }
                },
                SiteKind::Load => {
                    let Some(local) = site.local else { continue };
                    let Some(decision) = decision_of(local) else {
                        cause.get_or_insert_with(|| "load-consumer-unknown".to_owned());
                        continue;
                    };
                    let wanted = seam::form_of(decision);
                    if wanted == Form::Raw {
                        cause.get_or_insert_with(|| {
                            format!("load-consumer-degraded:{}", subject_label(table, local))
                        });
                        continue;
                    }
                    match seam::glue(wanted, field, None) {
                        Ok(None) => {}
                        Ok(Some((spec, _))) => {
                            let Some(rendered) = spec.render(&site.field_text) else {
                                cause.get_or_insert_with(|| "load-glue-unrenderable".to_owned());
                                continue;
                            };
                            edits.push(ExpressionEdit {
                                owner: site.owner,
                                span: site.span,
                                replacement: rendered,
                                kind: "field-load-glue",
                            });
                        }
                        Err(block) => {
                            cause.get_or_insert_with(|| format!("load-glue-blocked:{block:?}"));
                        }
                    }
                    let Some((subject, _)) = table
                        .entries
                        .iter()
                        .find(|(s, _)| (s.fn_did, s.hir_id) == local)
                    else {
                        continue;
                    };
                    let Some(pointee) = local_pointee(tcx, subject) else {
                        cause.get_or_insert_with(|| "load-consumer-pointee-unnameable".to_owned());
                        continue;
                    };
                    let Some(emitted) = super::declaration::emitted_type(decision, &pointee, None)
                    else {
                        cause.get_or_insert_with(|| "load-consumer-form-unrenderable".to_owned());
                        continue;
                    };
                    load_locals.push((local, emitted));
                }
                SiteKind::Deref => {
                    if matches!(field, Form::Opt { .. }) {
                        edits.push(ExpressionEdit {
                            owner: site.owner,
                            span: site.span,
                            replacement: accessor(&site.field_text, field),
                            kind: "field-deref",
                        });
                    }
                }
                SiteKind::Element => {
                    let Some(index) = &site.index_text else { continue };
                    edits.push(ExpressionEdit {
                        owner: site.owner,
                        span: site.span,
                        replacement: format!("{}[{index}]", accessor(&site.field_text, field)),
                        kind: "field-element",
                    });
                }
                SiteKind::Offset => {
                    let Some(index) = &site.index_text else { continue };
                    edits.push(ExpressionEdit {
                        owner: site.owner,
                        span: site.span,
                        replacement: format!(
                            "{}[{index}..].as_ptr()",
                            accessor(&site.field_text, field)
                        ),
                        kind: "field-offset",
                    });
                }
                SiteKind::IsNull => edits.push(ExpressionEdit {
                    owner: site.owner,
                    span: site.span,
                    replacement: format!("{}.is_none()", site.field_text),
                    kind: "field-is-null",
                }),
            }
        }
        // A stored parameter must itself be a delivered reference form so the
        // lifetime has a reference layer to sit on.
        for mention in &candidate.mentions {
            for node in &mention.stored_params {
                if decision_of(*node).is_none_or(|d| seam::form_of(d) == Form::Raw) {
                    cause.get_or_insert_with(|| {
                        format!("store-source-degraded:{}", subject_label(table, *node))
                    });
                }
            }
        }
        if let Some(cause) = cause {
            out.held.push((
                candidate.struct_path.clone(),
                candidate.field_name.clone(),
                cause.clone(),
            ));
            refused.insert(candidate.key, cause);
            continue;
        }
        let signature_plans = candidate
            .mentions
            .iter()
            .filter(|m| !m.stored_params.is_empty())
            .map(|m| SignaturePlan {
                owner: m.owner,
                lifetime_params: m.stored_params.clone(),
                lifetime_positions: m
                    .stored_params
                    .iter()
                    .filter_map(|node| {
                        table
                            .entries
                            .iter()
                            .find(|(s, _)| (s.fn_did, s.hir_id) == *node)
                            .and_then(|(s, _)| match s.kind {
                                SubjectKind::Param { hir_index } => Some(hir_index),
                                SubjectKind::Local => None,
                            })
                    })
                    .collect(),
            })
            .collect();
        let dependent_owners = sorted_owners(
            candidate
                .sites
                .iter()
                .filter(|site| {
                    matches!(site.kind, SiteKind::Load) || matches!(site.rhs, Some(Rhs::Subject(_)))
                })
                .map(|site| site.owner)
                .chain(
                    candidate
                        .mentions
                        .iter()
                        .filter(|m| !m.stored_params.is_empty())
                        .map(|m| m.owner),
                ),
        );
        out.applied.push(FieldTransaction {
            key: candidate.key,
            struct_path: candidate.struct_path.clone(),
            field_name: candidate.field_name.clone(),
            form: candidate.form,
            owners: candidate.owners.clone(),
            dependent_owners,
            impls: candidate.impls.clone(),
            signature_plans,
            expression_edits: edits,
            load_locals,
            site_count: candidate.sites.len(),
        });
    }
    (out, refused)
}

fn subject_label(table: &DecisionTable, node: NodeKey) -> String {
    table
        .entries
        .iter()
        .find(|(s, _)| (s.fn_did, s.hir_id) == node)
        .map(|(s, d)| match d {
            Decision::Degraded(record) => format!("{}:{}", s.label, record.reason.key()),
            _ => s.label.clone(),
        })
        .unwrap_or_else(|| "?".to_owned())
}

fn local_pointee(tcx: TyCtxt<'_>, subject: &Subject) -> Option<String> {
    let Node::Pat(pattern) = tcx.hir_node(subject.hir_id) else { return None };
    let ty = tcx.typeck(subject.fn_did).pat_ty(pattern);
    let TyKind::RawPtr(pointee, _) = ty.kind() else { return None };
    super::declaration::pointee_is_nameable(tcx, subject.fn_did, *pointee)
        .then(|| super::declaration::pointee_source(tcx, *pointee))
}
