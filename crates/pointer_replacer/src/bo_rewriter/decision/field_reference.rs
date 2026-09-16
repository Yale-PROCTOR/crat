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
    /// Any other raw-pointer expression (a call result, a field read); an
    /// OWNED field takes it through the `from_raw` bridge, a reference field
    /// holds.
    RawExpression,
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
    /// `callee(.., PLACE.f, ..)` — the argument span (owned fields only).
    CallArgument,
    /// `local = PLACE.f` — the field span; the local is an already-declared
    /// subject (owned fields only).
    Assignment,
    /// `PLACE.f as *T` handed to a callee (owned fields only) — the cast
    /// expression span; the callee decides transfer (a deallocator) or view.
    Cast,
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
    /// `CallArgument` only: the local callee's parameter node and its
    /// depth-0 MODEL kind (the ownership verdict that decides move vs view).
    pub consumer: Option<(NodeKey, SlotKind)>,
    /// The field's base place `(*base).f`: the base local when it is a
    /// subject, and whether its declared type is a raw pointer.
    pub base: Option<NodeKey>,
    pub raw_base: bool,
    /// `Store` only: the whole assignment expression.
    pub assign_span: Option<Span>,
    /// `Store` only (E5C-3): later arguments of the stored call that are pure
    /// `Copy` reads evaluated AFTER an earlier argument moves an owned field
    /// out — hoisted before the statement so no view is read past the move.
    pub hoists: Vec<Span>,
    /// `Cast` only: the cast's target type text, its mutability, and the
    /// callee the cast is an argument of (`None` for a foreign callee) with
    /// the argument index, plus the foreign symbol when foreign.
    pub cast: Option<CastSite>,
    /// `Element` only: the read is the place of an assignment (a write).
    pub written: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct CastSite {
    pub target: String,
    pub mutable: bool,
    pub callee: Option<LocalDefId>,
    pub foreign: Option<String>,
    pub index: usize,
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
    /// W6F-3: the field is model-`Owning` and becomes `Option<Box<T>>`.
    pub owning: bool,
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
    /// E5C-3 over moving owned locals (independent of any field).
    pub local_move_hoists: Vec<LocalMoveHoist>,
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
    /// W6F-3: the replacement WRAPS the node — `replacement` is a template
    /// with [`WRAP_PLACEHOLDER`] standing for the node's current expression,
    /// applied structurally after the use grafts so inner rewrites survive.
    pub wrap: bool,
}

/// The placeholder an owned-field wrap template carries for the wrapped node.
pub(crate) const WRAP_PLACEHOLDER: &str = "__crat_inner";
/// The assigned place of a raw-base store (`owned-field-raw-store` edits);
/// the offset operand of an `owned-field-raw-view` offset.
pub(crate) const WRAP_PLACE: &str = "__crat_place";
/// Edit kinds of a C free site taking the owned allocation: through a `free`
/// / source-proved deallocator, and through a user-named allocator contract.
pub(crate) const DEALLOC_TRANSFER: &str = "owned-field-dealloc-transfer";
pub(crate) const DEALLOC_TRANSFER_CONTRACT: &str = "owned-field-dealloc-transfer-contract";

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
    /// W6F-3: an owned field (`Option<Box<T>>`); no lifetime, the struct's
    /// derived `Copy` / `Clone` impls become empty inherent impls.
    pub owning: bool,
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
    /// W6F-3: the rendered form of each owned call-argument site (its
    /// consumer's decided form), so the seam glues by identity.
    pub argument_forms: Vec<(Span, Form)>,
    /// E5C-3: `(owner, the assignment, the read to hoist before it)`.
    pub hoists: Vec<(LocalDefId, Span, Span)>,
    /// Struct VALUE instances (literals) of an owning struct: each is a
    /// scope exit the language drops — addendum 101's
    /// `waiver-drop(scope-exit)` for a libc-freed allocation, receipted.
    pub value_instances: usize,
    pub site_count: usize,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FieldTransactions {
    pub applied: Vec<FieldTransaction>,
    /// `(struct path, field, cause)` per held field, model-Ref or withdrawn.
    pub held: Vec<(String, String, String)>,
    /// E5C-3 over moving owned locals: `(owner, local, statement, read)`.
    pub local_move_hoists: Vec<(LocalDefId, NodeKey, Span, Span)>,
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

    /// W6F-3: the form an owned-field call argument renders to.
    pub(crate) fn argument_form(&self, span: Span) -> Option<Form> {
        self.applied
            .iter()
            .flat_map(|t| t.argument_forms.iter())
            .find(|(argument, _)| *argument == span)
            .map(|(_, form)| *form)
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
            "struct\tfield\tstatus\tform\tsites\towners\timpls\tsignature_plans\tbridges\tcause\n",
        );
        for t in &self.applied {
            let count = |kind: &str| {
                t.expression_edits
                    .iter()
                    .filter(|edit| edit.kind == kind)
                    .count()
            };
            out.push_str(&format!(
                "{}\t{}\tapplied\t{}\t{}\t{}\t{}\t{}\traw-move={};raw-view={};raw-store={};dealloc-transfer={};allocator-contract={};waiver-drop-scope-exit={}\t-\n",
                t.struct_path,
                t.field_name,
                if t.owning {
                    if matches!(t.form, Form::Slice { .. } | Form::Opt { slice: true, .. }) {
                        "opt-box-slice"
                    } else {
                        "opt-box"
                    }
                } else {
                    t.form.key()
                },
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
                count("owned-field-raw-move"),
                count("owned-field-raw-view"),
                count("owned-field-raw-store"),
                count(DEALLOC_TRANSFER) + count(DEALLOC_TRANSFER_CONTRACT),
                count(DEALLOC_TRANSFER_CONTRACT),
                t.value_instances,
            ));
        }
        for (struct_path, field, cause) in &self.held {
            out.push_str(&format!(
                "{struct_path}\t{field}\theld\t-\t-\t-\t-\t-\t-\t{cause}\n"
            ));
        }
        out
    }
}

fn wants_slice_of(sites: &[Site]) -> bool {
    sites
        .iter()
        .any(|site| matches!(site.kind, SiteKind::Element | SiteKind::Offset))
}

/// The structs the program handles BY VALUE somewhere: a `*p` read as a
/// value (not as the base of a field place), a by-value parameter, local or
/// return of the struct type. An owned field cannot live in such a struct
/// (`Copy` is gone, and a copy would duplicate the owner).
fn structs_copied_by_value(
    program: &RustProgram<'_>,
    struct_dids: &FxHashSet<LocalDefId>,
) -> FxHashSet<LocalDefId> {
    struct ByValue<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        structs: &'a FxHashSet<LocalDefId>,
        out: &'a mut FxHashSet<LocalDefId>,
    }
    impl<'tcx> Visitor<'tcx> for ByValue<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Unary(UnOp::Deref, _) = expr.kind
                && let Some(did) = adt_local(self.tcx.typeck(self.owner).expr_ty(expr))
                && self.structs.contains(&did)
            {
                let base_of_place = match self.tcx.parent_hir_node(expr.hir_id) {
                    Node::Expr(parent) => match parent.kind {
                        ExprKind::Field(base, _) => base.hir_id == expr.hir_id,
                        ExprKind::AddrOf(_, _, inner) => inner.hir_id == expr.hir_id,
                        ExprKind::Assign(lhs, _, _) => lhs.hir_id == expr.hir_id,
                        _ => false,
                    },
                    _ => false,
                };
                if !base_of_place {
                    self.out.insert(did);
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let tcx = program.tcx;
    let mut out = FxHashSet::default();
    for &owner in &program.functions {
        let sig = tcx.fn_sig(owner).skip_binder().skip_binder();
        for ty in sig.inputs().iter().chain(std::iter::once(&sig.output())) {
            if let Some(did) = adt_local(*ty)
                && struct_dids.contains(&did)
            {
                out.insert(did);
            }
        }
        let Some(body_id) = tcx.hir_node_by_def_id(owner).body_id() else { continue };
        ByValue {
            tcx,
            owner,
            structs: struct_dids,
            out: &mut out,
        }
        .visit_body(tcx.hir_body(body_id));
    }
    out
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
        // `2 as isize`: a non-negative literal under the cast.
        ExprKind::Cast(inner, _) => match inner.kind {
            ExprKind::Lit(lit) => match lit.node {
                rustc_ast::LitKind::Int(value, _) => Some(format!("{}usize", value.get())),
                _ => None,
            },
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
    /// The owned-field candidates among `targets`.
    owning: &'a FxHashSet<FieldKey>,
    /// `(callee, hir index)` → the parameter subject.
    parameters: &'a FxHashMap<(LocalDefId, usize), NodeKey>,
    /// Depth-0 model kind per parameter subject.
    parameter_kinds: &'a FxHashMap<NodeKey, SlotKind>,
    struct_dids: &'a FxHashSet<LocalDefId>,
    sites: &'a mut FxHashMap<FieldKey, Vec<Site>>,
    holds: &'a mut FxHashMap<FieldKey, String>,
}

impl<'tcx> Collector<'_, 'tcx> {
    fn hold(&mut self, key: FieldKey, cause: String) {
        self.holds.entry(key).or_insert(cause);
    }

    fn rhs(&self, key: FieldKey, expr: &Expr<'_>) -> Result<Rhs, &'static str> {
        if super::emitability::is_zero_literal(expr) {
            return Ok(Rhs::Null);
        }
        if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
            && let Res::Local(binding) = path.res
        {
            return match self.subjects.get(&binding) {
                Some(node) => Ok(Rhs::Subject(*node)),
                None if self.owning.contains(&key) => Ok(Rhs::RawExpression),
                None => Err("store-source-not-a-subject"),
            };
        }
        if self.owning.contains(&key) {
            return Ok(Rhs::RawExpression);
        }
        Err("store-source-raw-expression")
    }

    /// The local callee's parameter at `index`, with its depth-0 model kind.
    fn callee_parameter(&self, callee: &Expr<'_>, index: usize) -> Option<(NodeKey, SlotKind)> {
        let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind else { return None };
        let Res::Def(rustc_hir::def::DefKind::Fn, did) = path.res else { return None };
        let callee = did.as_local()?;
        let node = *self.parameters.get(&(callee, index))?;
        let kind = *self.parameter_kinds.get(&node)?;
        Some((node, kind))
    }

    /// `(*base).f`: the base local when it is a subject, and whether the
    /// base's declared type is a raw pointer (the place may be uninitialized
    /// memory — a fresh allocation — so no store through it may drop).
    fn field_base(&self, field: &Expr<'tcx>) -> (Option<NodeKey>, bool) {
        let ExprKind::Field(base, _) = field.kind else { return (None, false) };
        let ExprKind::Unary(UnOp::Deref, pointer) = base.kind else { return (None, false) };
        let raw = matches!(
            self.tcx.typeck(self.owner).expr_ty(pointer).kind(),
            TyKind::RawPtr(..)
        );
        let subject = match pointer.kind {
            ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                Res::Local(binding) => self.subjects.get(&binding).copied(),
                _ => None,
            },
            _ => None,
        };
        (subject, raw)
    }

    /// E5C-3: for a stored value that is a call, the later arguments that
    /// are pure `Copy` reads once an EARLIER argument is an owned target
    /// field handed to an owning parameter (a move out of the field). Every
    /// argument between the move and the read must be pure too, so the
    /// hoisted read sees the same values it saw in place (a move relocates
    /// a pointer, it writes nothing the read can observe).
    fn hoisted_reads(&self, value: &Expr<'tcx>) -> Vec<Span> {
        let ExprKind::Call(callee, args) = value.kind else { return Vec::new() };
        let typeck = self.tcx.typeck(self.owner);
        let moving = args.iter().enumerate().position(|(index, arg)| {
            self.field_key(arg)
                .is_some_and(|key| self.owning.contains(&key))
                && self
                    .callee_parameter(callee, index)
                    .is_some_and(|(_, kind)| kind == SlotKind::Owning)
        });
        let Some(moving) = moving else { return Vec::new() };
        let _ = typeck;
        reads_after_move(self.tcx, self.owner, args, moving)
    }

    /// `let ref mut b = PLACE.f;` — `b`'s uses in the owner. The idiom is
    /// admitted only when the binding is used exactly once, as the place of a
    /// plain assignment `*b = v`; returns that assignment and `v`.
    fn ref_binding_store(&self, binding: HirId) -> Option<(&'tcx Expr<'tcx>, &'tcx Expr<'tcx>)> {
        struct Uses<'tcx> {
            binding: HirId,
            uses: Vec<&'tcx Expr<'tcx>>,
        }
        impl<'tcx> Visitor<'tcx> for Uses<'tcx> {
            fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
                if let ExprKind::Path(QPath::Resolved(_, path)) = expr.kind
                    && path.res == Res::Local(self.binding)
                {
                    self.uses.push(expr);
                }
                intravisit::walk_expr(self, expr);
            }
        }
        let body = self.tcx.hir_body_owned_by(self.owner);
        let mut uses = Uses {
            binding,
            uses: Vec::new(),
        };
        uses.visit_body(body);
        let [use_expr] = uses.uses.as_slice() else { return None };
        let Node::Expr(deref) = self.tcx.parent_hir_node(use_expr.hir_id) else { return None };
        if !matches!(deref.kind, ExprKind::Unary(UnOp::Deref, inner) if inner.hir_id == use_expr.hir_id)
        {
            return None;
        }
        let Node::Expr(assign) = self.tcx.parent_hir_node(deref.hir_id) else { return None };
        match assign.kind {
            ExprKind::Assign(lhs, rhs, _) if lhs.hir_id == deref.hir_id => Some((assign, rhs)),
            _ => None,
        }
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
        let (base, raw_base) = self.field_base(field);
        let site = |kind, span, rhs, local, index_text| Site {
            owner,
            kind,
            span,
            field_text: field_text.clone(),
            rhs,
            local,
            index_text,
            consumer: None,
            base,
            raw_base,
            assign_span: None,
            hoists: Vec::new(),
            cast: None,
            written: false,
        };
        let owning = self.owning.contains(&key);
        let Node::Expr(parent) = tcx.parent_hir_node(field.hir_id) else {
            // `let x = PLACE.f;`
            if let Node::LetStmt(local) = tcx.parent_hir_node(field.hir_id)
                && local.init.is_some_and(|init| init.hir_id == field.hir_id)
            {
                if local.ty.is_some() {
                    self.hold(key, "load-into-annotated-local".to_owned());
                    return;
                }
                let rustc_hir::PatKind::Binding(mode, binding, _, None) = local.pat.kind else {
                    self.hold(key, "load-into-pattern".to_owned());
                    return;
                };
                // c2rust's field-store idiom (E): `let ref mut fresh = PLACE.f;
                // *fresh = v;` — a by-reference binding whose one use is the
                // write through it IS the store of `v` into the field.
                if let rustc_hir::ByRef::Yes(mutability) = mode.0 {
                    match self.ref_binding_store(binding) {
                        Some((assign, value)) if mutability.is_mut() => {
                            match self.rhs(key, value) {
                                Ok(rhs) => {
                                    let mut store =
                                        site(SiteKind::Store, value.span, Some(rhs), None, None);
                                    store.assign_span = Some(assign.span);
                                    store.hoists = self.hoisted_reads(value);
                                    self.push(key, store);
                                }
                                Err(cause) => self.hold(key, cause.to_owned()),
                            }
                        }
                        _ => self.hold(
                            key,
                            "field-transaction-incomplete:ref-binding-use".to_owned(),
                        ),
                    }
                    return;
                }
                let Some(node) = self.subjects.get(&binding).copied() else {
                    self.hold(key, "load-consumer-not-a-subject".to_owned());
                    return;
                };
                let mut load = site(SiteKind::Load, field.span, None, Some(node), None);
                if owning {
                    load.consumer = self.parameter_kinds.get(&node).map(|kind| (node, *kind));
                }
                self.push(key, load);
                return;
            }
            self.hold(key, "field-use-outside-expression".to_owned());
            return;
        };
        match parent.kind {
            // `local = PLACE.f` — a load into an already-declared subject
            // (owned fields only: the value moves or is viewed by the local's
            // ownership verdict; a reference field holds).
            ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == field.hir_id && owning => {
                let target = match lhs.kind {
                    ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                        Res::Local(binding) => self.subjects.get(&binding).copied(),
                        _ => None,
                    },
                    _ => None,
                };
                let Some(node) = target else {
                    self.hold(
                        key,
                        "field-transaction-incomplete:assigned-to-non-subject".to_owned(),
                    );
                    return;
                };
                let mut load = site(SiteKind::Assignment, field.span, None, Some(node), None);
                load.consumer = self.parameter_kinds.get(&node).map(|kind| (node, *kind));
                self.push(key, load);
            }
            ExprKind::Assign(lhs, rhs, _) if lhs.hir_id == field.hir_id => match self.rhs(key, rhs)
            {
                Ok(value) => {
                    let mut store = site(SiteKind::Store, rhs.span, Some(value), None, None);
                    store.assign_span = Some(parent.span);
                    store.hoists = self.hoisted_reads(rhs);
                    self.push(key, store);
                }
                Err(cause) => self.hold(key, cause.to_owned()),
            },
            ExprKind::Unary(UnOp::Deref, _) => {
                let mut deref = site(SiteKind::Deref, field.span, None, None, None);
                // `*PLACE.f = v` writes through the field; a read takes the
                // shared view.
                deref.written = matches!(
                    tcx.parent_hir_node(parent.hir_id),
                    Node::Expr(assign)
                        if matches!(assign.kind, ExprKind::Assign(lhs, _, _) if lhs.hir_id == parent.hir_id)
                );
                self.push(key, deref);
            }
            ExprKind::MethodCall(segment, receiver, args, _) if receiver.hir_id == field.hir_id => {
                let method = segment.ident.name.as_str().to_owned();
                match (method.as_str(), args) {
                    ("is_null", []) => {
                        self.push(key, site(SiteKind::IsNull, parent.span, None, None, None));
                    }
                    ("offset" | "add", [operand]) => {
                        let index = index_text(tcx, owner, operand);
                        match tcx.parent_hir_node(parent.hir_id) {
                            Node::Expr(grand)
                                if matches!(grand.kind, ExprKind::Unary(UnOp::Deref, _)) =>
                            {
                                let Some(index) = index else {
                                    self.hold(key, "field-offset-sign-unknown".to_owned());
                                    return;
                                };
                                let mut element =
                                    site(SiteKind::Element, grand.span, None, None, Some(index));
                                // `*(f).offset(k) = v` writes the element.
                                element.written = matches!(
                                    tcx.parent_hir_node(grand.hir_id),
                                    Node::Expr(assign)
                                        if matches!(assign.kind, ExprKind::Assign(lhs, _, _) if lhs.hir_id == grand.hir_id)
                                );
                                self.push(key, element);
                            }
                            // The offset as a pointer VALUE: under a cast (a
                            // reference field's slice view) or, for an owned
                            // field, stored / passed as a raw cursor.
                            Node::Expr(grand)
                                if matches!(grand.kind, ExprKind::Cast(..)) || owning =>
                            {
                                // A reference field's slice view needs the
                                // index as `usize`; an owned field's raw
                                // cursor keeps the operand as written.
                                if index.is_none() && !owning {
                                    self.hold(key, "field-offset-sign-unknown".to_owned());
                                    return;
                                }
                                self.push(
                                    key,
                                    site(SiteKind::Offset, parent.span, None, None, index),
                                );
                            }
                            _ => self.hold(key, "field-offset-consumer-unsupported".to_owned()),
                        }
                    }
                    _ => self.hold(key, format!("field-method-unsupported:{method}")),
                }
            }
            ExprKind::Call(callee, args) if owning => {
                let Some(index) = args.iter().position(|arg| arg.hir_id == field.hir_id) else {
                    self.hold(key, "field-transaction-incomplete:call-argument".to_owned());
                    return;
                };
                match self.callee_parameter(callee, index) {
                    Some(consumer) => {
                        let mut site = site(SiteKind::CallArgument, field.span, None, None, None);
                        site.consumer = Some(consumer);
                        self.push(key, site);
                    }
                    None => self.hold(
                        key,
                        "field-transaction-incomplete:call-argument-foreign".to_owned(),
                    ),
                }
            }
            // E: a reference field at a LOCAL callee's parameter is a seam
            // position whose found form is the field's own (`argument_form`);
            // the seam glues it like any other argument. A foreign callee (or
            // the callee expression itself) holds.
            ExprKind::Call(callee, args) => {
                let is_argument = args.iter().any(|arg| arg.hir_id == field.hir_id);
                if !is_argument {
                    self.hold(key, "field-transaction-incomplete:call-argument".to_owned());
                    return;
                }
                if !matches!(
                    callee.kind,
                    ExprKind::Path(QPath::Resolved(_, path))
                        if matches!(path.res, Res::Def(rustc_hir::def::DefKind::Fn, did) if did.is_local())
                ) {
                    self.hold(
                        key,
                        "field-transaction-incomplete:call-argument-foreign".to_owned(),
                    );
                    return;
                }
                self.push(
                    key,
                    site(SiteKind::CallArgument, field.span, None, None, None),
                );
            }
            ExprKind::AddrOf(..) => self.hold(
                key,
                "field-transaction-incomplete:address-of-field".to_owned(),
            ),
            // An owned field cast to a raw pointer and handed to a callee: a
            // deallocator takes the allocation (transfer), anything else a
            // raw view; the callee is read at finalization.
            ExprKind::Cast(_, target_ty) if owning => {
                let typeck = tcx.typeck(owner);
                let TyKind::RawPtr(_, mutability) = typeck.expr_ty(parent).kind() else {
                    self.hold(key, "field-transaction-incomplete:cast-of-field".to_owned());
                    return;
                };
                let Ok(target) = sm.span_to_snippet(target_ty.span) else {
                    self.hold(key, "field-transaction-incomplete:cast-of-field".to_owned());
                    return;
                };
                let Node::Expr(call) = tcx.parent_hir_node(parent.hir_id) else {
                    self.hold(key, "field-transaction-incomplete:cast-of-field".to_owned());
                    return;
                };
                let ExprKind::Call(callee, args) = call.kind else {
                    self.hold(key, "field-transaction-incomplete:cast-of-field".to_owned());
                    return;
                };
                let Some(index) = args.iter().position(|arg| arg.hir_id == parent.hir_id) else {
                    self.hold(key, "field-transaction-incomplete:cast-of-field".to_owned());
                    return;
                };
                let (local_callee, foreign) = match callee.kind {
                    ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                        Res::Def(rustc_hir::def::DefKind::Fn, did) => (
                            did.as_local().filter(|local| {
                                !matches!(tcx.hir_node_by_def_id(*local), Node::ForeignItem(_))
                            }),
                            did.as_local()
                                .filter(|local| {
                                    matches!(tcx.hir_node_by_def_id(*local), Node::ForeignItem(_))
                                })
                                .map(|_| tcx.item_name(did).to_string()),
                        ),
                        _ => (None, None),
                    },
                    _ => (None, None),
                };
                if local_callee.is_none() && foreign.is_none() {
                    self.hold(
                        key,
                        "field-transaction-incomplete:cast-of-field-callee".to_owned(),
                    );
                    return;
                }
                let mut cast_site = site(SiteKind::Cast, parent.span, None, None, None);
                cast_site.cast = Some(CastSite {
                    target,
                    mutable: mutability.is_mut(),
                    callee: local_callee,
                    foreign,
                    index,
                });
                self.push(key, cast_site);
            }
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
                        match self.rhs(key, field.expr) {
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
                                        consumer: None,
                                        base: None,
                                        raw_base: false,
                                        assign_span: None,
                                        hoists: Vec::new(),
                                        cast: None,
                                        written: false,
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

    // W6F-3 inputs: the parameter subjects with their depth-0 model kinds
    // (the ownership verdict a call-argument site is decided by), and the
    // structs the program copies by value (`*p` read as a value, a by-value
    // parameter / local / return) — an owned field cannot live in a `Copy`.
    let parameters: FxHashMap<(LocalDefId, usize), NodeKey> = subjects
        .iter()
        .filter_map(|s| match s.kind {
            SubjectKind::Param { hir_index } => Some(((s.fn_did, hir_index), (s.fn_did, s.hir_id))),
            SubjectKind::Local => None,
        })
        .collect();
    let parameter_kinds: FxHashMap<NodeKey, SlotKind> = subjects
        .iter()
        .filter_map(|s| {
            let slot = slots
                .fn_local_slots
                .get(&s.fn_did)?
                .slot_for_local_depth(s.local, 0)?;
            Some((
                (s.fn_did, s.hir_id),
                *model.get(&SlotRef::Local(s.fn_did, slot))?,
            ))
        })
        .collect();
    let copied_by_value = structs_copied_by_value(program, &struct_dids);
    let mut owning_fields: FxHashSet<FieldKey> = FxHashSet::default();

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
            let owning = match model.get(&SlotRef::Field(slot_id)) {
                Some(SlotKind::Ref) => false,
                // W6F-3: an owned field — `Option<Box<T>>`.
                Some(SlotKind::Owning) => true,
                Some(SlotKind::Raw) | None => continue,
            };
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
            if owning {
                if copied_by_value.contains(&struct_did) {
                    out.holds.push((
                        key,
                        struct_path.clone(),
                        field_name,
                        "field-transaction-incomplete:struct-copied-by-value".into(),
                    ));
                    continue;
                }
                if matches!(
                    fatness.struct_field_fact(struct_did, field_index, 0),
                    Some(Fatness::Arr)
                ) {
                    fat.insert(key);
                }
                owning_fields.insert(key);
                targets.insert(key, field_index);
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
    // E5C-3 for moving owned locals — independent of the field candidates.
    let subject_by_binding: FxHashMap<HirId, NodeKey> = subjects
        .iter()
        .map(|s| (s.hir_id, (s.fn_did, s.hir_id)))
        .collect();
    out.local_move_hoists = local_move_hoists(
        tcx,
        &program.functions,
        &subject_by_binding,
        &parameters,
        &parameter_kinds,
    );
    if targets.is_empty() {
        return out;
    }

    // 2. Every site, over every program function.
    let mut sites: FxHashMap<FieldKey, Vec<Site>> = FxHashMap::default();
    let mut holds: FxHashMap<FieldKey, String> = FxHashMap::default();
    for &owner in &program.functions {
        let Some(body_id) = tcx.hir_node_by_def_id(owner).body_id() else { continue };
        let mut collector = Collector {
            tcx,
            owner,
            subjects: &subject_by_binding,
            targets: &targets,
            owning: &owning_fields,
            parameters: &parameters,
            parameter_kinds: &parameter_kinds,
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

    // 4. Assemble candidates, in declaration order. Every converting
    // reference field of a struct shares the struct's ONE generated lifetime
    // (E lifted the one-field-per-struct hold: brotli's `BlockEncoder`
    // stores `block_types_` and `block_lengths_` from one signature).
    let mut converting_structs: FxHashSet<LocalDefId> = FxHashSet::default();
    let mut owning_structs: FxHashSet<LocalDefId> = FxHashSet::default();
    // A struct with both a reference candidate and an owned candidate takes
    // the reference one (declaration order); the owned one holds typed.
    let reference_structs: FxHashSet<LocalDefId> = targets
        .keys()
        .filter(|key| !owning_fields.contains(key))
        .map(|key| key.struct_did)
        .collect();
    for (&key, (struct_path, field_name)) in &names {
        if !targets.contains_key(&key) {
            continue;
        }
        let (struct_path, field_name) = (struct_path.clone(), field_name.clone());
        let key_sites = sites.remove(&key).unwrap_or_default();
        let owning = owning_fields.contains(&key);
        let mut cause = holds.remove(&key);
        if cause.is_none() && owning && reference_structs.contains(&key.struct_did) {
            cause = Some("field-transaction-incomplete:mixed-owning-and-reference".to_owned());
        }
        if cause.is_none() && !owning {
            cause = container_holds.get(&key.struct_did).cloned();
        }
        if cause.is_none() && owning {
            // The union / static / alias holds still apply; a struct that
            // contains the struct is fine (the container needs no lifetime).
            if let Some(hold) = container_holds.get(&key.struct_did)
                && !hold.ends_with("nested-container")
            {
                cause = Some(hold.clone());
            }
        }
        // An owned field walked by element / offset is `Option<Box<[T]>>`
        // under Foster's `Arr` licence (the same corroboration as a slice
        // field); unlicensed it holds.
        if cause.is_none() && owning && wants_slice_of(&key_sites) && !fat.contains(&key) {
            cause = Some("field-fat-unlicensed".to_owned());
        }
        // The field is fat when it is walked itself, or (E) when it is handed
        // to a callee that walks it — Foster's `Arr` fact is flow-insensitive
        // over the program, so a call-argument site of an array-walking callee
        // marks the field `Arr`; a thin field there would be widened at the
        // callee, which is never done.
        let wants_slice = key_sites.iter().any(|site| {
            matches!(site.kind, SiteKind::Element | SiteKind::Offset)
                || (site.kind == SiteKind::CallArgument && !owning && fat.contains(&key))
        });
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
        for site in key_sites.iter().filter(|_| !owning) {
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
        // E: a mention that forwards its own parameter, bare, into a tied
        // position of a storing (or itself tied) callee carries the same tie
        // — transitively, to a fixpoint over the mentions.
        if !owning {
            forward_ties(
                tcx,
                &fn_mentions,
                &parameters,
                &subject_by_binding,
                &mut stored_by_fn,
            );
        }
        for (owner, in_return, simple) in fn_mentions.iter().filter(|_| !owning) {
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
        if owning {
            owning_structs.insert(key.struct_did);
        } else {
            converting_structs.insert(key.struct_did);
        }
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
                owning,
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

/// The transitive lifetime tie (E): for every mention `F` of the struct, a
/// call `G(.., p, ..)` where `G` ties that position and `p` is a bare
/// parameter of `F` ties `p` in `F` too. Iterated to a fixpoint; each owner
/// is walked once per round.
/// The later arguments of a call that are pure `Copy` reads through a place
/// once the argument at `moving` moves an owned value; the scan stops at the
/// first non-pure argument (an intervening call could write).
fn reads_after_move<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    args: &[Expr<'tcx>],
    moving: usize,
) -> Vec<Span> {
    let typeck = tcx.typeck(owner);
    let mut out = Vec::new();
    for arg in &args[moving + 1..] {
        if !pure_read(arg) {
            break;
        }
        // A bare local or literal reads through nothing a move could
        // invalidate; only a read THROUGH a place is hoisted.
        if !reads_through(arg) {
            continue;
        }
        let ty = typeck.expr_ty(arg);
        if tcx
            .type_is_copy_modulo_regions(rustc_middle::ty::TypingEnv::post_analysis(tcx, owner), ty)
        {
            out.push(arg.span);
        }
    }
    out
}

/// E5C-3 for a moving owned LOCAL (R410 STOP 1): a call whose argument is a
/// bare local subject the model decides Owning, handed to a parameter the
/// model decides Owning, moves the local; the later pure reads through a
/// place are planned for hoisting before the call's statement. Planned on
/// the model; applied only while the local DELIVERS as a `Box` (a raw local
/// moves nothing the checker sees).
#[derive(Clone, Debug)]
pub(crate) struct LocalMoveHoist {
    pub owner: LocalDefId,
    pub local: NodeKey,
    /// The statement holding the call.
    pub statement: Span,
    pub read: Span,
}

fn local_move_hoists<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    subjects: &FxHashMap<HirId, NodeKey>,
    parameters: &FxHashMap<(LocalDefId, usize), NodeKey>,
    kinds: &FxHashMap<NodeKey, SlotKind>,
) -> Vec<LocalMoveHoist> {
    struct Calls<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        subjects: &'a FxHashMap<HirId, NodeKey>,
        parameters: &'a FxHashMap<(LocalDefId, usize), NodeKey>,
        kinds: &'a FxHashMap<NodeKey, SlotKind>,
        out: Vec<LocalMoveHoist>,
    }
    impl<'tcx> Visitor<'tcx> for Calls<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Call(callee, args) = expr.kind
                && let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind
                && let Res::Def(rustc_hir::def::DefKind::Fn, did) = path.res
                && let Some(callee) = did.as_local()
            {
                let moving = args.iter().enumerate().find_map(|(index, arg)| {
                    let ExprKind::Path(QPath::Resolved(_, path)) = arg.kind else { return None };
                    let Res::Local(binding) = path.res else { return None };
                    let local = *self.subjects.get(&binding)?;
                    let target = *self.parameters.get(&(callee, index))?;
                    (self.kinds.get(&local) == Some(&SlotKind::Owning)
                        && self.kinds.get(&target) == Some(&SlotKind::Owning))
                    .then_some((index, local))
                });
                if let Some((index, local)) = moving {
                    let reads = reads_after_move(self.tcx, self.owner, args, index);
                    if !reads.is_empty()
                        && let Some(statement) = enclosing_statement(self.tcx, expr.hir_id)
                    {
                        for read in reads {
                            self.out.push(LocalMoveHoist {
                                owner: self.owner,
                                local,
                                statement,
                                read,
                            });
                        }
                    }
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut out = Vec::new();
    for &owner in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(owner).body_id() else { continue };
        let mut calls = Calls {
            tcx,
            owner,
            subjects,
            parameters,
            kinds,
            out: Vec::new(),
        };
        calls.visit_body(tcx.hir_body(body_id));
        out.extend(calls.out);
    }
    out
}

/// The span of the statement an expression belongs to.
fn enclosing_statement(tcx: TyCtxt<'_>, mut hir_id: HirId) -> Option<Span> {
    loop {
        match tcx.parent_hir_node(hir_id) {
            Node::Stmt(stmt) => return Some(stmt.span),
            Node::Expr(expr) => hir_id = expr.hir_id,
            _ => return None,
        }
    }
}

/// A read with no call, no write and no address-taking: field projections,
/// dereferences, locals, literals, casts and unary/binary arithmetic of the
/// same.
fn pure_read(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Lit(_) => true,
        ExprKind::Path(QPath::Resolved(_, path)) => matches!(path.res, Res::Local(_)),
        ExprKind::Field(base, _) => pure_read(base),
        ExprKind::Unary(UnOp::Deref | UnOp::Neg | UnOp::Not, inner) => pure_read(inner),
        ExprKind::Cast(inner, _) => pure_read(inner),
        ExprKind::Binary(_, left, right) => pure_read(left) && pure_read(right),
        _ => false,
    }
}

/// Whether a pure read goes through a place (a field projection or a
/// dereference) rather than naming a local or a literal.
fn reads_through(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Field(..) | ExprKind::Unary(UnOp::Deref, _) => true,
        ExprKind::Unary(_, inner) | ExprKind::Cast(inner, _) => reads_through(inner),
        ExprKind::Binary(_, left, right) => reads_through(left) || reads_through(right),
        _ => false,
    }
}

fn forward_ties(
    tcx: TyCtxt<'_>,
    mentions: &[(LocalDefId, bool, bool)],
    parameters: &FxHashMap<(LocalDefId, usize), NodeKey>,
    subjects: &FxHashMap<HirId, NodeKey>,
    tied: &mut FxHashMap<LocalDefId, Vec<NodeKey>>,
) {
    struct Calls<'a, 'tcx> {
        subjects: &'a FxHashMap<HirId, NodeKey>,
        /// `(callee, argument index, the bare local argument's subject)`
        out: Vec<(LocalDefId, usize, NodeKey)>,
        _marker: std::marker::PhantomData<&'tcx ()>,
    }
    impl<'tcx> Visitor<'tcx> for Calls<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Call(callee, args) = expr.kind
                && let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind
                && let Res::Def(rustc_hir::def::DefKind::Fn, did) = path.res
                && let Some(callee) = did.as_local()
            {
                for (index, arg) in args.iter().enumerate() {
                    if let ExprKind::Path(QPath::Resolved(_, path)) = arg.kind
                        && let Res::Local(binding) = path.res
                        && let Some(node) = self.subjects.get(&binding)
                    {
                        self.out.push((callee, index, *node));
                    }
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    // Position of each parameter subject in its function.
    let position_of: FxHashMap<NodeKey, usize> = parameters
        .iter()
        .map(|(&(_, index), &node)| (node, index))
        .collect();
    let calls: Vec<(LocalDefId, Vec<(LocalDefId, usize, NodeKey)>)> = mentions
        .iter()
        .filter_map(|&(owner, _, _)| {
            let body_id = tcx.hir_node_by_def_id(owner).body_id()?;
            let mut calls = Calls {
                subjects,
                out: Vec::new(),
                _marker: std::marker::PhantomData,
            };
            calls.visit_body(tcx.hir_body(body_id));
            Some((owner, calls.out))
        })
        .collect();
    loop {
        let mut changed = false;
        for (owner, calls) in &calls {
            for &(callee, index, node) in calls {
                let tied_position = tied
                    .get(&callee)
                    .is_some_and(|nodes| nodes.iter().any(|n| position_of.get(n) == Some(&index)));
                // Only a PARAMETER of the caller can carry the tie.
                if tied_position
                    && node.0 == *owner
                    && position_of.contains_key(&node)
                    && !tied.get(owner).is_some_and(|nodes| nodes.contains(&node))
                {
                    tied.entry(*owner).or_default().push(node);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
}

/// An A5 raw-view call snapshots its argument from PLAN-TIME TEXT
/// (`A5RawViewTemp::raw_expression`), so a field edit nested in that
/// argument would be lost when the snapshot is grafted (`((*reader).data)
/// .offset(..)` on a field that is now `Option<&[u8]>`). The field
/// transaction owns the field's text: its non-wrapping edits are applied to
/// the view's texts here, after the seam plan. A wrapping (owned) edit
/// inside a raw view cannot be composed as text and is an error.
pub(crate) fn reconcile_a5_raw_views(
    tcx: TyCtxt<'_>,
    table: &mut DecisionTable,
) -> Result<(), String> {
    let sm = tcx.sess.source_map();
    let edits: Vec<(LocalDefId, Span, String, String, bool)> = table
        .field_transactions
        .applied
        .iter()
        .flat_map(|t| t.expression_edits.iter())
        .filter_map(|e| {
            sm.span_to_snippet(e.span)
                .ok()
                .map(|original| (e.owner, e.span, original, e.replacement.clone(), e.wrap))
        })
        .collect();
    if edits.is_empty() {
        return Ok(());
    }
    for call in &mut table.seams.a5_raw_calls {
        for (owner, span, original, replacement, wrap) in &edits {
            if *owner != call.caller || !call.call_span.contains(*span) {
                continue;
            }
            for view in &mut call.views {
                let mut texts: Vec<&mut String> = vec![
                    &mut view.raw_expression,
                    &mut view.adapted_expression,
                    &mut view.argument_expression,
                ];
                if let Some(rendering) = view.input_rendering.as_mut() {
                    texts.push(&mut rendering.raw_expression);
                    texts.push(&mut rendering.adapted_expression);
                }
                for text in texts {
                    if !text.contains(original.as_str()) {
                        continue;
                    }
                    if *wrap {
                        return Err(format!(
                            "field-transaction-a5-raw-view:owned-edit-inside-view:{}",
                            sm.span_to_diagnostic_string(*span)
                        ));
                    }
                    *text = text.replace(original.as_str(), replacement);
                }
            }
        }
    }
    Ok(())
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
/// `deallocator(callee, foreign symbol, argument)` answers with the receipt
/// key when the callee frees that argument exactly once (`free` itself, a
/// source-proved local deallocator, or a user-named allocator contract).
pub(crate) type DeallocatorPredicate<'p> =
    dyn Fn(Option<LocalDefId>, Option<&str>, usize) -> Option<&'static str> + 'p;

pub(crate) fn finalize(
    tcx: TyCtxt<'_>,
    candidates: &FieldCandidates,
    table: &DecisionTable,
    exposure: &super::exposure::ExposurePolicy,
    deallocator: &DeallocatorPredicate<'_>,
) -> (FieldTransactions, BTreeMap<FieldKey, String>) {
    let mut out = FieldTransactions::default();
    out.local_move_hoists = candidates
        .local_move_hoists
        .iter()
        .map(|h| (h.owner, h.local, h.statement, h.read))
        .collect();
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
        let mut argument_forms = Vec::new();
        for owner in &candidate.owners {
            if matches!(
                exposure.plan(*owner),
                ExposureSurfacePlan::PositiveSeedShim | ExposureSurfacePlan::FnPtrRawWrapper
            ) {
                cause.get_or_insert_with(|| "field-transaction-incomplete:surface-plan".to_owned());
            }
        }
        if candidate.owning {
            owned_sites(
                tcx,
                candidate,
                table,
                &decision_of,
                deallocator,
                &mut cause,
                &mut edits,
                &mut load_locals,
                &mut argument_forms,
            );
        }
        for site in candidate.sites.iter().filter(|_| !candidate.owning) {
            let field = candidate.form;
            match site.kind {
                SiteKind::Literal | SiteKind::Store => match site.rhs {
                    Some(Rhs::Null) => edits.push(ExpressionEdit {
                        owner: site.owner,
                        span: site.span,
                        replacement: "None".to_owned(),
                        kind: "field-null",
                        wrap: false,
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
                                    wrap: false,
                                });
                            }
                            Err(block) => {
                                cause
                                    .get_or_insert_with(|| format!("store-glue-blocked:{block:?}"));
                            }
                        }
                    }
                    Some(Rhs::RawExpression) | None => {
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
                                wrap: false,
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
                            wrap: false,
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
                        wrap: false,
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
                        wrap: false,
                    });
                }
                SiteKind::IsNull => edits.push(ExpressionEdit {
                    owner: site.owner,
                    span: site.span,
                    replacement: format!("{}.is_none()", site.field_text),
                    kind: "field-is-null",
                    wrap: false,
                }),
                // E: the seam reads the argument in the field's own form and
                // glues it to the callee's (identity for `&T` at `&T`,
                // `.unwrap()` for `Option<&T>` at `&T`, a hold otherwise).
                SiteKind::CallArgument => argument_forms.push((site.span, field)),
                SiteKind::Assignment => {
                    cause.get_or_insert_with(|| {
                        "field-transaction-incomplete:assignment".to_owned()
                    });
                }
                // Never collected for a reference field (the collector holds
                // `cast-of-field`); exhaustive rather than silent.
                SiteKind::Cast => {
                    cause.get_or_insert_with(|| {
                        "field-transaction-incomplete:cast-of-field".to_owned()
                    });
                }
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
        // R409-3: an allocation released through a user-named allocator
        // contract must never meet a Rust drop. A struct VALUE instance
        // (a struct literal: a local the language drops at scope exit) could
        // drop the field while it still holds the allocation — a typed hold
        // for contract allocations; for libc-`free` allocations the same
        // exit is addendum 101's `waiver-drop(scope-exit)`, receipted per
        // value instance.
        if cause.is_none()
            && candidate.owning
            && edits.iter().any(|e| e.kind == DEALLOC_TRANSFER_CONTRACT)
            && candidate
                .sites
                .iter()
                .any(|site| site.kind == SiteKind::Literal)
        {
            cause = Some("contract-allocation:implicit-close".to_owned());
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
                    matches!(
                        site.kind,
                        SiteKind::Load | SiteKind::CallArgument | SiteKind::Assignment
                    ) || matches!(site.rhs, Some(Rhs::Subject(_)))
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
            owning: candidate.owning,
            form: candidate.form,
            owners: candidate.owners.clone(),
            dependent_owners,
            impls: candidate.impls.clone(),
            signature_plans,
            expression_edits: edits,
            load_locals,
            argument_forms,
            value_instances: if candidate.owning {
                candidate
                    .sites
                    .iter()
                    .filter(|site| site.kind == SiteKind::Literal)
                    .count()
            } else {
                0
            },
            hoists: candidate
                .sites
                .iter()
                .filter(|site| candidate.owning && site.kind == SiteKind::Store)
                .flat_map(|site| {
                    site.hoists.iter().filter_map(move |read| {
                        site.assign_span.map(|assign| (site.owner, assign, *read))
                    })
                })
                .collect(),
            site_count: candidate.sites.len(),
        });
    }
    // One generated lifetime per struct: a function whose signature would
    // carry the lifetimes of TWO structs is held on the later struct (in
    // declaration order) — the plan has one name per signature this wave.
    let mut struct_of_owner: FxHashMap<LocalDefId, LocalDefId> = FxHashMap::default();
    let mut two_struct: Vec<FieldKey> = Vec::new();
    for transaction in &out.applied {
        if transaction.owning {
            continue;
        }
        for plan in &transaction.signature_plans {
            match struct_of_owner.get(&plan.owner) {
                Some(other) if *other != transaction.key.struct_did => {
                    two_struct.push(transaction.key);
                }
                Some(_) => {}
                None => {
                    struct_of_owner.insert(plan.owner, transaction.key.struct_did);
                }
            }
        }
    }
    for key in two_struct {
        if let Some(index) = out.applied.iter().position(|t| t.key == key) {
            let transaction = out.applied.remove(index);
            let cause = "field-transaction-incomplete:two-struct-signature".to_owned();
            out.held.push((
                transaction.struct_path,
                transaction.field_name,
                cause.clone(),
            ));
            refused.insert(key, cause);
        }
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

/// W6F-3 — the site vocabulary of an OWNED field (`Option<Box<T>>`).
///
/// Every consumer is decided by the MODEL's ownership verdict on the slot the
/// field's value reaches (a call-argument parameter, a loaded local): `Owning`
/// moves the value out (`take()`), `Ref` views it (`as_deref`), and the form
/// the consumer was DECIDED into picks the bridge — a delivered `Box` /
/// reference takes the value directly, a raw-decided consumer takes it through
/// `Box::into_raw` / `core::ptr::from_mut` (R130). A store takes a delivered
/// `Box` directly and any raw pointer through the `from_raw` bridge (the field's
/// own `Owning` verdict is the ownership evidence for the stored value).
/// A decision that keeps the subject's declared raw type is NOT a safe form;
/// every other disposition is (exhaustive, so a new disposition is decided
/// here rather than falling through).
fn delivers_safe_form(decision: &Decision) -> bool {
    match decision {
        Decision::Degraded(_) => false,
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_) => true,
    }
}

fn owned_sites<'t>(
    tcx: TyCtxt<'_>,
    candidate: &Candidate,
    table: &'t DecisionTable,
    decision_of: &dyn Fn(NodeKey) -> Option<&'t Decision>,
    deallocator: &DeallocatorPredicate<'_>,
    cause: &mut Option<String>,
    edits: &mut Vec<ExpressionEdit>,
    load_locals: &mut Vec<(NodeKey, String)>,
    argument_forms: &mut Vec<(Span, Form)>,
) {
    let null_mut = "core::ptr::null_mut()";
    let null_const = "core::ptr::null()";
    // A fat owned field is `Option<Box<[T]>>`: its raw views are the slice's
    // pointers, its move hands the whole allocation over.
    let fat = matches!(
        candidate.form,
        Form::Slice { .. } | Form::Opt { slice: true, .. }
    );
    // Move the owned value out to a raw owning consumer.
    // Every owned template is rendered around the WRAP placeholder: the AST
    // wrap pass substitutes the node's current (inner-edited) expression.
    let inner = WRAP_PLACEHOLDER;
    let move_to_raw = || {
        if fat {
            format!("{inner}.take().map_or({null_mut}, |__b| Box::into_raw(__b) as *mut _)")
        } else {
            format!("{inner}.take().map_or({null_mut}, Box::into_raw)")
        }
    };
    // A raw VIEW of the owned value (the C alias), mutability by the target.
    let view_to_raw = |mutable: bool| match (fat, mutable) {
        (true, true) => {
            format!("{inner}.as_deref_mut().map_or({null_mut}, |__s| __s.as_mut_ptr())")
        }
        (true, false) => format!("{inner}.as_deref().map_or({null_const}, |__s| __s.as_ptr())"),
        (false, true) => format!("{inner}.as_deref_mut().map_or({null_mut}, core::ptr::from_mut)"),
        (false, false) => format!("{inner}.as_deref().map_or({null_const}, core::ptr::from_ref)"),
    };
    let from_raw =
        || format!("core::ptr::NonNull::new({inner}).map(|__p| Box::from_raw(__p.as_ptr()))");
    // A raw-decided consumer keeps its DECLARED pointer type; the view's
    // mutability follows it (`*mut` takes `from_mut`, `*const` `from_ref`).
    let raw_target_mutable = |node: NodeKey| -> bool {
        table
            .entries
            .iter()
            .find(|(s, _)| (s.fn_did, s.hir_id) == node)
            .is_some_and(|(s, _)| {
                let Node::Pat(pattern) = tcx.hir_node(s.hir_id) else { return s.mutable };
                match tcx.typeck(s.fn_did).pat_ty(pattern).kind() {
                    TyKind::RawPtr(_, mutability) => mutability.is_mut(),
                    _ => s.mutable,
                }
            })
    };
    // The form a delivered consumer takes the value in.
    // Returns the template and the edit kind (`raw-move` / `raw-view` are the
    // receipted bridges: the value leaves the safe form at that site).
    let consumer_edit = |node: NodeKey, kind: SlotKind| -> Result<(String, &'static str), String> {
        let decision = decision_of(node).ok_or_else(|| "consumer-unknown".to_owned())?;
        match (kind, decision) {
            (SlotKind::Owning, Decision::Box(plan)) => Ok((
                if plan.optional {
                    format!("{inner}.take()")
                } else {
                    format!("{inner}.take().unwrap()")
                },
                "owned-field-move",
            )),
            (SlotKind::Owning, Decision::Degraded(_)) => {
                Ok((move_to_raw(), "owned-field-raw-move"))
            }
            (SlotKind::Ref, Decision::Ref { mutable }) => Ok((
                format!(
                    "{inner}.{}().unwrap()",
                    if *mutable { "as_deref_mut" } else { "as_deref" }
                ),
                "owned-field-view",
            )),
            (
                SlotKind::Ref,
                Decision::Opt {
                    mutable,
                    slice: false,
                    ..
                },
            ) => Ok((
                format!(
                    "{inner}.{}()",
                    if *mutable { "as_deref_mut" } else { "as_deref" }
                ),
                "owned-field-view",
            )),
            (SlotKind::Ref, Decision::Degraded(_)) => Ok((
                view_to_raw(raw_target_mutable(node)),
                "owned-field-raw-view",
            )),
            (SlotKind::Raw, _) => Err(format!("consumer-model-raw:{}", subject_label(table, node))),
            (_, other) => Err(format!(
                "consumer-form-unsupported:{}:{}",
                subject_label(table, node),
                seam::form_of(other).key()
            )),
        }
    };
    for site in &candidate.sites {
        match site.kind {
            SiteKind::Literal | SiteKind::Store => {
                let replacement = match site.rhs {
                    Some(Rhs::Null) => "None".to_owned(),
                    Some(Rhs::Subject(node)) => match decision_of(node) {
                        Some(Decision::Box(plan)) => {
                            // The source's shape must be the field's: a
                            // sized Box cannot fill a slice field.
                            let source_fat = plan.shape == super::box_facts::BoxShape::Slice;
                            if source_fat != fat {
                                cause.get_or_insert_with(|| {
                                    "field-transaction-incomplete:owned-store-shape".to_owned()
                                });
                                continue;
                            }
                            if plan.optional {
                                inner.to_owned()
                            } else {
                                format!("Some({inner})")
                            }
                        }
                        // A raw source reclaims the allocation; a fat field
                        // needs its length, which a raw pointer does not carry.
                        Some(Decision::Degraded(_)) | None if fat => {
                            cause.get_or_insert_with(|| {
                                "field-transaction-incomplete:owned-slice-store-length".to_owned()
                            });
                            continue;
                        }
                        Some(Decision::Degraded(_)) | None => from_raw(),
                        Some(other) => {
                            cause.get_or_insert_with(|| {
                                format!(
                                    "store-source-form-unsupported:{}:{}",
                                    subject_label(table, node),
                                    seam::form_of(other).key()
                                )
                            });
                            continue;
                        }
                    },
                    Some(Rhs::RawExpression) if fat => {
                        cause.get_or_insert_with(|| {
                            "field-transaction-incomplete:owned-slice-store-length".to_owned()
                        });
                        continue;
                    }
                    Some(Rhs::RawExpression) => from_raw(),
                    None => {
                        cause.get_or_insert_with(|| "store-source-unknown".to_owned());
                        continue;
                    }
                };
                // Through a raw base the place may be uninitialized memory (a
                // fresh allocation), so the store never drops: `ptr::write`
                // keeps C's overwrite semantics (the old value, if any, leaks
                // exactly as C leaked it). Through a safe base the place is
                // valid and the assignment drops the old owner (waiver 101).
                let through_raw = site.raw_base
                    && site
                        .base
                        .is_none_or(|node| !decision_of(node).is_some_and(delivers_safe_form));
                match (through_raw, site.kind, site.assign_span) {
                    (true, SiteKind::Store, Some(assign_span)) => {
                        edits.push(ExpressionEdit {
                            owner: site.owner,
                            span: assign_span,
                            replacement: format!(
                                "core::ptr::write(&raw mut {WRAP_PLACE}, {replacement})"
                            ),
                            kind: "owned-field-raw-store",
                            wrap: true,
                        });
                    }
                    _ => edits.push(ExpressionEdit {
                        owner: site.owner,
                        span: site.span,
                        replacement,
                        kind: "owned-field-store",
                        wrap: true,
                    }),
                }
            }
            SiteKind::Load => {
                let Some(local) = site.local else { continue };
                let Some(kind) = site.consumer.map(|(_, kind)| kind) else {
                    cause.get_or_insert_with(|| "load-consumer-model-unknown".to_owned());
                    continue;
                };
                match consumer_edit(local, kind) {
                    Ok((replacement, kind)) => edits.push(ExpressionEdit {
                        owner: site.owner,
                        span: site.span,
                        replacement,
                        kind,
                        wrap: true,
                    }),
                    Err(why) => {
                        cause.get_or_insert_with(|| format!("load-{why}"));
                        continue;
                    }
                }
                // A delivered local receives an explicit declaration.
                if let Some(decision) = decision_of(local)
                    && let Some((subject, _)) = table
                        .entries
                        .iter()
                        .find(|(s, _)| (s.fn_did, s.hir_id) == local)
                    && delivers_safe_form(decision)
                    && let Some(pointee) = local_pointee(tcx, subject)
                    && let Some(emitted) =
                        super::declaration::emitted_type(decision, &pointee, None)
                {
                    load_locals.push((local, emitted));
                }
            }
            SiteKind::CallArgument | SiteKind::Assignment => {
                let Some((node, kind)) = site.consumer else {
                    cause.get_or_insert_with(|| "call-argument-consumer-unknown".to_owned());
                    continue;
                };
                match consumer_edit(node, kind) {
                    Ok((replacement, kind)) => {
                        if site.kind == SiteKind::CallArgument
                            && let Some(decision) = decision_of(node)
                        {
                            argument_forms.push((site.span, seam::form_of(decision)));
                        }
                        edits.push(ExpressionEdit {
                            owner: site.owner,
                            span: site.span,
                            replacement,
                            kind,
                            wrap: true,
                        })
                    }
                    Err(why) => {
                        cause.get_or_insert_with(|| format!("argument-{why}"));
                    }
                }
            }
            SiteKind::Deref => edits.push(ExpressionEdit {
                owner: site.owner,
                span: site.span,
                replacement: if site.written {
                    format!("{inner}.as_deref_mut().unwrap()")
                } else {
                    format!("{inner}.as_deref().unwrap()")
                },
                kind: "owned-field-deref",
                wrap: true,
            }),
            SiteKind::IsNull => edits.push(ExpressionEdit {
                owner: site.owner,
                span: site.span,
                replacement: format!("{inner}.is_none()"),
                kind: "owned-field-is-null",
                wrap: true,
            }),
            // `*(f).offset(k)` on a fat owned field indexes the slice.
            SiteKind::Element => {
                let Some(index) = &site.index_text else { continue };
                if !fat {
                    cause.get_or_insert_with(|| "field-fat-unlicensed".to_owned());
                    continue;
                }
                edits.push(ExpressionEdit {
                    owner: site.owner,
                    span: site.span,
                    replacement: if site.written {
                        format!("{inner}.as_deref_mut().unwrap()[{index}]")
                    } else {
                        format!("{inner}.as_deref().unwrap()[{index}]")
                    },
                    kind: "owned-field-element",
                    wrap: true,
                });
            }
            // `(f).offset(k)` as a pointer value: the raw view of the slice,
            // offset as written (a C cursor into the owned buffer; receipted
            // as a raw view).
            SiteKind::Offset => {
                if !fat {
                    cause.get_or_insert_with(|| "field-fat-unlicensed".to_owned());
                    continue;
                }
                edits.push(ExpressionEdit {
                    owner: site.owner,
                    span: site.span,
                    replacement: format!("{}.offset({WRAP_PLACE})", view_to_raw(true)),
                    kind: "owned-field-raw-view",
                    wrap: true,
                });
            }
            // `f as *T` at a callee: a deallocator takes the allocation
            // (`take()` + `Box::into_raw`, the C free site kept as the call);
            // any other callee gets the raw view.
            SiteKind::Cast => {
                let Some(cast) = &site.cast else { continue };
                let null = if cast.mutable { null_mut } else { null_const };
                match deallocator(cast.callee, cast.foreign.as_deref(), cast.index) {
                    Some(receipt) => edits.push(ExpressionEdit {
                        owner: site.owner,
                        span: site.span,
                        replacement: format!(
                            "{inner}.take().map_or({null}, |__b| Box::into_raw(__b) as {})",
                            cast.target
                        ),
                        kind: receipt,
                        wrap: true,
                    }),
                    None => edits.push(ExpressionEdit {
                        owner: site.owner,
                        span: site.span,
                        replacement: format!("{} as {}", view_to_raw(cast.mutable), cast.target),
                        kind: "owned-field-raw-view",
                        wrap: true,
                    }),
                }
            }
        }
    }
}

fn local_pointee(tcx: TyCtxt<'_>, subject: &Subject) -> Option<String> {
    let Node::Pat(pattern) = tcx.hir_node(subject.hir_id) else { return None };
    let ty = tcx.typeck(subject.fn_did).pat_ty(pattern);
    let TyKind::RawPtr(pointee, _) = ty.kind() else { return None };
    super::declaration::pointee_is_nameable(tcx, subject.fn_did, *pointee)
        .then(|| super::declaration::pointee_source(tcx, *pointee))
}
