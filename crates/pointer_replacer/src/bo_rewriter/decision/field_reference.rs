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
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Rhs {
    /// `0 as *mut T` — becomes `None`.
    Null,
    /// A subject binding of the storing function (a parameter or a local).
    Subject(NodeKey),
    /// Any other raw-pointer expression (a call result, a field read); an
    /// OWNED field takes it through the `from_raw` bridge, a reference field
    /// holds.
    RawExpression,
    /// An allocation whose element count its own size argument proves (G
    /// build 3): a fat owned place reclaims it as a boxed slice of that
    /// length — no fabricated extent.
    AllocationWithLength(String),
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
    /// `arr.as_ptr()` on a converted array local (G) — the method-call span.
    /// `Option<&T>` has the layout and ABI of `*const T` (the null-pointer
    /// optimisation, `None` = null), so the array's bytes are unchanged and
    /// the view is a cast, not a copy.
    ArrayView,
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

/// `f(.., data /* i */, .., size /* j */)` stores `data` into the fat field
/// and `size` into the sibling that bounds the fat field's reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CountCompanion {
    pub callee: LocalDefId,
    pub stored: usize,
    pub count: usize,
    pub sibling: String,
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
    /// G: the candidate is a local array of pointers, not a struct field.
    pub array: Option<ArrayLocal>,
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
    /// G: a load permit from an ARRAY local lifts the model's opaque-provenance
    /// `Raw` on the loaded local (locals' arrays are not slot-registered).
    pub(crate) fn array_load_lift(&self, local: NodeKey) -> bool {
        self.load_permit(local).is_some_and(|c| c.array.is_some())
    }

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
    /// G: a local array of pointers rather than a struct field.
    pub array: Option<ArrayLocal>,
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
    /// R411 §2: the count companions of a fat field — the storing
    /// function's parameter that fills the SIBLING field bounding the fat
    /// field's element reads: `(callee, stored parameter index, count
    /// parameter index, sibling field name)`.
    pub count_companions: Vec<CountCompanion>,
    pub site_count: usize,
}

impl FieldTransaction {
    /// The delivered form of this transaction, as the receipt's `form` column
    /// spells it and as [`owning_field_form`] answers it. ONE definition, so
    /// the seam a consumer reads and the receipt an audit reads cannot drift.
    pub(crate) fn delivered_form_key(&self) -> &'static str {
        if let Some(array) = self.array.as_ref() {
            if array.owning {
                "array-opt-box-slice"
            } else {
                "array-opt-ref-shared"
            }
        } else if self.owning {
            if matches!(
                self.form,
                Form::Slice { .. } | Form::Opt { slice: true, .. }
            ) {
                "opt-box-slice"
            } else {
                "opt-box"
            }
        } else {
            self.form.key()
        }
    }
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

    /// R411 §2: the parameter positions of `callee` that a field transaction
    /// proves to be the COUNT of the fat parameter at `index` (the sibling
    /// field the same store fills bounds the fat field's reads).
    pub(crate) fn count_companions(&self, callee: LocalDefId, index: usize) -> Vec<usize> {
        self.applied
            .iter()
            .flat_map(|t| t.count_companions.iter())
            .filter(|c| c.callee == callee && c.stored == index)
            .map(|c| c.count)
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
}

/// **R448-5 — the field-transaction seam, as a query.**
///
/// The delivered form of an OWNING struct field, in the vocabulary the
/// ownership-fields family's `owning_field_form` seam reads (`box`,
/// `opt-box`, `opt-box-slice`), or `None` where no transaction of this family
/// owns that field. A consumer uses it to type the local a field is moved OUT
/// of: only an owning field licenses a `Box` local, because a `Box` out of a
/// field this family delivers as a BORROW (or does not deliver at all) would
/// close memory the container's raw copy still points into.
///
/// Fail-closed by construction — every arm that is not a delivered owning
/// field of `struct_did` answers `None`:
///
/// - a foreign / non-local struct (this family only rewrites local structs);
/// - a field with no transaction, or one held;
/// - a transaction that delivers a reference form (`owning == false`);
/// - an ARRAY transaction, whose key names the owning FUNCTION and a local's
///   `HirId`, not a struct and a field index.
///
/// This line has no production caller: the consumer is the ownership-fields
/// producer, which composes with this one (relay 032 / their report 035
/// claim 1). The witnesses below are its callers here.
#[allow(dead_code)]
pub(crate) fn owning_field_form(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    struct_did: rustc_span::def_id::DefId,
    field_index: usize,
) -> Option<String> {
    let _ = tcx;
    let key = FieldKey {
        struct_did: struct_did.as_local()?,
        field_index,
    };
    table
        .field_transactions
        .applied
        .iter()
        .find(|t| t.key == key && t.array.is_none() && t.owning)
        .map(|t| t.delivered_form_key().to_owned())
}

impl FieldTransactions {
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
                "{}\t{}\tapplied\t{}\t{}\t{}\t{}\t{}\traw-move={};raw-view={};raw-store={};dealloc-transfer={};allocator-contract={};waiver-drop-scope-exit={};count-companion={}\t-\n",
                t.struct_path,
                t.field_name,
                t.delivered_form_key(),
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
                count("owned-field-raw-view") + count("array-raw-view"),
                count("owned-field-raw-store"),
                count(DEALLOC_TRANSFER) + count(DEALLOC_TRANSFER_CONTRACT),
                count(DEALLOC_TRANSFER_CONTRACT),
                t.value_instances,
                t.count_companions
                    .iter()
                    .map(|c| format!(
                        "{}:{}<-{}({})",
                        tcx.def_path_str(c.callee.to_def_id()),
                        c.stored,
                        c.count,
                        c.sibling
                    ))
                    .collect::<Vec<_>>()
                    .join("|"),
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
    // G: local arrays of pointers, independent of the struct fields.
    array_local_candidates(
        tcx,
        &program.functions,
        &subject_by_binding,
        &parameter_kinds,
        withdrawn,
        &mut out,
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
                array: None,
            },
        );
    }
    out
}

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

/// The transitive lifetime tie (E): for every mention `F` of the struct, a
/// call `G(.., p, ..)` where `G` ties that position and `p` is a bare
/// parameter of `F` ties `p` in `F` too. Iterated to a fixpoint; each owner
/// is walked once per round.
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

/// G — a LOCAL ARRAY OF POINTERS (`let mut points: [*const T; N] = [0 as
/// *const T; N]; points[k] = p; let x = points[i];`) is a transaction of the
/// same site vocabulary: the array is the container, its elements the one
/// "field". Every store's source must be a subject the model decides `Ref`
/// (the stored parameters of heman's `kmRay2IntersectBox`), every load a
/// subject that takes its type from the element; the array's declared type
/// becomes `[Option<&T>; N]` (null = `None`), the null repeat `[None; N]`,
/// stores `Some(p)`, loads `points[i].unwrap()`. No lifetime is written: the
/// elements' borrows unify at the local's scope. Anything else holds typed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ArrayLocal {
    pub owner: LocalDefId,
    /// The binding pattern of the local (the AST `Local.pat` maps to it).
    pub binding: HirId,
    pub name: String,
    pub len: String,
    pub pointee: String,
    /// G build 3: every element is its own allocation, released at its own C
    /// free — the array is `[Option<Box<[T]>>; N]`, not `[Option<&T>; N]`.
    pub owning: bool,
}

/// The sites of an OWNED-element array (G build 3 stage 2): the allocation
/// stores, the null tests, the raw views a callee takes, the element reads
/// through an offset, and the release casts. Every other use of an element
/// is a typed hold — the transaction never skips a site in silence.
fn owned_element_uses<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    info: &ArrayLocal,
    body: &'tcx rustc_hir::Body<'tcx>,
    subjects: &FxHashMap<HirId, NodeKey>,
    kinds: &FxHashMap<NodeKey, SlotKind>,
) -> (Vec<Site>, Option<String>) {
    struct Owned<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        binding: HirId,
        name: String,
        subjects: &'a FxHashMap<HirId, NodeKey>,
        kinds: &'a FxHashMap<NodeKey, SlotKind>,
        sites: Vec<Site>,
        hold: Option<String>,
    }
    impl<'tcx> Owned<'_, 'tcx> {
        fn hold(&mut self, reason: &str) {
            self.hold
                .get_or_insert_with(|| format!("array-owned-incomplete:{reason}"));
        }

        fn site(&self, kind: SiteKind, span: Span) -> Site {
            Site {
                owner: self.owner,
                kind,
                span,
                field_text: self.name.clone(),
                rhs: None,
                local: None,
                index_text: None,
                consumer: None,
                base: None,
                raw_base: false,
                assign_span: None,
                hoists: Vec::new(),
                cast: None,
                written: false,
            }
        }

        fn is_element(&self, expr: &rustc_hir::Expr<'_>) -> bool {
            matches!(expr.kind, ExprKind::Index(base, _, _)
                if matches!(base.kind, ExprKind::Path(QPath::Resolved(_, path))
                    if matches!(path.res, Res::Local(id) if id == self.binding)))
        }

        /// The callee's parameter subject at `index`, when the callee is a
        /// local function whose parameter is a subject of the table.
        fn callee_parameter(
            &self,
            callee: &rustc_hir::Expr<'_>,
            index: usize,
        ) -> Option<(NodeKey, SlotKind)> {
            let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind else { return None };
            let Res::Def(rustc_hir::def::DefKind::Fn, did) = path.res else { return None };
            let local = did.as_local()?;
            let body_id = self.tcx.hir_node_by_def_id(local).body_id()?;
            let param = self.tcx.hir_body(body_id).params.get(index)?;
            let node = *self.subjects.get(&param.pat.hir_id)?;
            let kind = *self.kinds.get(&node)?;
            Some((node, kind))
        }
    }
    impl<'tcx> Visitor<'tcx> for Owned<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            let tcx = self.tcx;
            let sm = tcx.sess.source_map();
            // The element's own uses are classified from the element
            // expression; every other expression walks on — except a use of
            // the ARRAY itself, which holds: an owned element is a boxed
            // SLICE (two words), so the whole-array raw view of G build 2
            // (which rests on `Option<&T>` having `*const T`'s layout) is not
            // available here, and no other whole-array shape is expressed.
            if !self.is_element(expr) {
                if matches!(expr.kind, ExprKind::Path(QPath::Resolved(_, path))
                    if matches!(path.res, Res::Local(id) if id == self.binding))
                    && !matches!(tcx.parent_hir_node(expr.hir_id),
                        Node::Expr(p) if matches!(p.kind, ExprKind::Index(base, _, _) if base.hir_id == expr.hir_id))
                {
                    self.hold("array-use-shape");
                    return;
                }
                intravisit::walk_expr(self, expr);
                return;
            }
            let parent = tcx.parent_hir_node(expr.hir_id);
            match parent {
                // `arr[i] = <allocation>` — the element takes the allocation.
                Node::Expr(p) if matches!(p.kind, ExprKind::Assign(lhs, _, _) if lhs.hir_id == expr.hir_id) =>
                {
                    let ExprKind::Assign(_, rhs, _) = p.kind else { return };
                    let mut source = rhs;
                    while let ExprKind::Cast(inner, _) = source.kind {
                        source = inner;
                    }
                    let ExprKind::Call(_, args) = source.kind else {
                        self.hold("store-source-not-an-allocation");
                        return;
                    };
                    if args.len() != 1 {
                        self.hold("allocation-shape");
                        return;
                    }
                    let Ok(size) = sm.span_to_snippet(args[0].span) else {
                        self.hold("allocation-size-text");
                        return;
                    };
                    let mut site = self.site(SiteKind::Store, rhs.span);
                    site.rhs = Some(Rhs::AllocationWithLength(size));
                    site.assign_span = Some(p.span);
                    self.sites.push(site);
                }
                // `(arr[i]).is_null()` and `*(arr[i]).offset(k)`.
                Node::Expr(p) if matches!(p.kind, ExprKind::MethodCall(..)) => {
                    let ExprKind::MethodCall(segment, _, args, _) = p.kind else { return };
                    match segment.ident.name.as_str() {
                        "is_null" => self.sites.push(self.site(SiteKind::IsNull, p.span)),
                        "offset" | "add" => {
                            let Node::Expr(grand) = tcx.parent_hir_node(p.hir_id) else {
                                self.hold("offset-consumer");
                                return;
                            };
                            let ExprKind::Unary(UnOp::Deref, _) = grand.kind else {
                                self.hold("offset-consumer");
                                return;
                            };
                            let Ok(index) = args
                                .first()
                                .map(|arg| sm.span_to_snippet(arg.span))
                                .unwrap_or(Ok(String::new()))
                            else {
                                self.hold("offset-index-text");
                                return;
                            };
                            // A slice is indexed by `usize`; the C cursor is
                            // written as an `isize` offset.
                            let mut site = self.site(SiteKind::Element, grand.span);
                            site.index_text = Some(format!("({index}) as usize"));
                            site.written = matches!(
                                tcx.parent_hir_node(grand.hir_id),
                                Node::Expr(a)
                                    if matches!(a.kind, ExprKind::Assign(lhs, _, _) if lhs.hir_id == grand.hir_id)
                                        || matches!(a.kind, ExprKind::AssignOp(_, lhs, _) if lhs.hir_id == grand.hir_id)
                            );
                            self.sites.push(site);
                        }
                        other => self.hold(&format!("element-method:{other}")),
                    }
                }
                // `f(.., arr[i], ..)` — a callee takes a view of the element.
                Node::Expr(p) if matches!(p.kind, ExprKind::Call(..)) => {
                    let ExprKind::Call(callee, args) = p.kind else { return };
                    let Some(index) = args.iter().position(|arg| arg.hir_id == expr.hir_id) else {
                        self.hold("call-shape");
                        return;
                    };
                    match self.callee_parameter(callee, index) {
                        Some(consumer) => {
                            let mut site = self.site(SiteKind::CallArgument, expr.span);
                            site.consumer = Some(consumer);
                            self.sites.push(site);
                        }
                        None => self.hold("call-argument-foreign"),
                    }
                }
                // `free(arr[i] as *mut c_void)` — the release site; the
                // deallocator is read at finalization.
                Node::Expr(p) if matches!(p.kind, ExprKind::Cast(..)) => {
                    let ExprKind::Cast(_, target_ty) = p.kind else { return };
                    let Ok(target) = sm.span_to_snippet(target_ty.span) else {
                        self.hold("release-cast-text");
                        return;
                    };
                    let Node::Expr(call) = tcx.parent_hir_node(p.hir_id) else {
                        self.hold("release-consumer");
                        return;
                    };
                    let ExprKind::Call(callee, args) = call.kind else {
                        self.hold("release-consumer");
                        return;
                    };
                    let Some(index) = args.iter().position(|arg| arg.hir_id == p.hir_id) else {
                        self.hold("release-consumer");
                        return;
                    };
                    let (local, foreign) = match callee.kind {
                        ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                            Res::Def(rustc_hir::def::DefKind::Fn, did) => (
                                did.as_local(),
                                Some(
                                    tcx.def_path_str(did)
                                        .rsplit("::")
                                        .next()
                                        .unwrap_or_default()
                                        .to_owned(),
                                ),
                            ),
                            _ => (None, None),
                        },
                        _ => (None, None),
                    };
                    let mutable = matches!(
                        tcx.typeck(self.owner).expr_ty(p).kind(),
                        TyKind::RawPtr(_, mutability) if mutability.is_mut()
                    );
                    let mut site = self.site(SiteKind::Cast, p.span);
                    site.cast = Some(CastSite {
                        target,
                        mutable,
                        callee: local,
                        foreign,
                        index,
                    });
                    self.sites.push(site);
                }
                _ => self.hold("element-use-shape"),
            }
        }
    }
    let mut owned = Owned {
        tcx,
        owner,
        binding: info.binding,
        name: info.name.clone(),
        subjects,
        kinds,
        sites: Vec::new(),
        hold: None,
    };
    owned.visit_body(body);
    (owned.sites, owned.hold)
}

/// Which family a `*mut`-element array local belongs to (G build 3): the
/// element stores' sources and the release sites decide. An OWNED-element
/// array stores a fresh allocation into every element and hands every
/// element to a releasing call; anything else stays the borrowed shape.
fn mutable_element_family<'tcx>(
    binding: HirId,
    body: &'tcx rustc_hir::Body<'tcx>,
) -> Result<(), String> {
    struct Elements {
        binding: HirId,
        stores: usize,
        allocated: usize,
        released: usize,
    }
    fn peel<'tcx>(mut expr: &'tcx rustc_hir::Expr<'tcx>) -> &'tcx rustc_hir::Expr<'tcx> {
        while let ExprKind::Cast(inner, _) = expr.kind {
            expr = inner;
        }
        expr
    }
    impl<'tcx> Visitor<'tcx> for Elements {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            let indexes_binding = |e: &rustc_hir::Expr<'_>| {
                matches!(e.kind, ExprKind::Index(base, _, _)
                    if matches!(base.kind, ExprKind::Path(QPath::Resolved(_, path))
                        if matches!(path.res, Res::Local(id) if id == self.binding)))
            };
            if let ExprKind::Assign(lhs, rhs, _) = expr.kind
                && indexes_binding(lhs)
            {
                self.stores += 1;
                if matches!(peel(rhs).kind, ExprKind::Call(..)) {
                    self.allocated += 1;
                }
            }
            if let ExprKind::Call(_, args) = expr.kind {
                for arg in args {
                    if indexes_binding(peel(arg)) {
                        self.released += 1;
                    }
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut elements = Elements {
        binding,
        stores: 0,
        allocated: 0,
        released: 0,
    };
    elements.visit_body(body);
    let (stores, allocated, released) = (elements.stores, elements.allocated, elements.released);
    if stores == 0 || allocated != stores {
        // Some element is written from something other than a fresh call:
        // the borrowed-element family, whose `&mut` elements need a
        // disjointness argument nothing here supplies.
        return Err("array-local-incomplete:mutable-elements".to_owned());
    }
    if released == 0 {
        return Err("array-owned-incomplete:no-release".to_owned());
    }
    // Every element is allocated and handed to a releasing call: the owned
    // family. Its element count must come from the allocation itself.
    Ok(())
}

fn array_local_candidates(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    subjects: &FxHashMap<HirId, NodeKey>,
    kinds: &FxHashMap<NodeKey, SlotKind>,
    withdrawn: &BTreeMap<FieldKey, String>,
    out: &mut FieldCandidates,
) {
    struct Arrays<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        subjects: &'a FxHashMap<HirId, NodeKey>,
        kinds: &'a FxHashMap<NodeKey, SlotKind>,
        /// binding → (info, sites, hold)
        found: Vec<(ArrayLocal, Vec<Site>, Option<String>)>,
    }
    impl<'tcx> Arrays<'_, 'tcx> {
        fn classify(
            &self,
            info: &ArrayLocal,
            body: &'tcx rustc_hir::Body<'tcx>,
        ) -> (Vec<Site>, Option<String>) {
            struct Uses<'a, 'tcx> {
                tcx: TyCtxt<'tcx>,
                owner: LocalDefId,
                binding: HirId,
                subjects: &'a FxHashMap<HirId, NodeKey>,
                kinds: &'a FxHashMap<NodeKey, SlotKind>,
                sites: Vec<Site>,
                hold: Option<String>,
            }
            impl Uses<'_, '_> {
                fn hold(&mut self, cause: &str) {
                    if self.hold.is_none() {
                        self.hold = Some(format!("array-local-incomplete:{cause}"));
                    }
                }
            }
            impl<'tcx> Visitor<'tcx> for Uses<'_, 'tcx> {
                fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
                    let tcx = self.tcx;
                    let is_array = |e: &Expr<'_>| matches!(e.kind, ExprKind::Path(QPath::Resolved(_, path)) if path.res == Res::Local(self.binding));
                    // An indexed element `points[i]`.
                    if let ExprKind::Index(base, _, _) = expr.kind
                        && is_array(base)
                    {
                        let sm = tcx.sess.source_map();
                        let Ok(text) = sm.span_to_snippet(expr.span) else {
                            self.hold("element-text");
                            return;
                        };
                        let owner = self.owner;
                        let site = |kind, span, rhs, local| Site {
                            owner,
                            kind,
                            span,
                            field_text: text.clone(),
                            rhs,
                            local,
                            index_text: None,
                            consumer: None,
                            base: None,
                            raw_base: false,
                            assign_span: None,
                            hoists: Vec::new(),
                            cast: None,
                            written: false,
                        };
                        match tcx.parent_hir_node(expr.hir_id) {
                            Node::Expr(parent) => match parent.kind {
                                ExprKind::Assign(lhs, rhs, _) if lhs.hir_id == expr.hir_id => {
                                    let value = if super::emitability::is_zero_literal(rhs) {
                                        Some(Rhs::Null)
                                    } else if let ExprKind::Path(QPath::Resolved(_, path)) =
                                        rhs.kind
                                        && let Res::Local(b) = path.res
                                        && let Some(node) = self.subjects.get(&b)
                                    {
                                        (self.kinds.get(node) == Some(&SlotKind::Ref))
                                            .then_some(Rhs::Subject(*node))
                                    } else {
                                        None
                                    };
                                    match value {
                                        Some(rhs_value) => {
                                            let mut store = site(
                                                SiteKind::Store,
                                                rhs.span,
                                                Some(rhs_value),
                                                None,
                                            );
                                            store.assign_span = Some(parent.span);
                                            self.sites.push(store);
                                        }
                                        None => self.hold("store-source"),
                                    }
                                }
                                ExprKind::Unary(UnOp::Deref, _) => {
                                    self.sites
                                        .push(site(SiteKind::Deref, expr.span, None, None));
                                }
                                ExprKind::MethodCall(segment, receiver, [], _)
                                    if receiver.hir_id == expr.hir_id
                                        && segment.ident.name.as_str() == "is_null" =>
                                {
                                    self.sites.push(site(
                                        SiteKind::IsNull,
                                        parent.span,
                                        None,
                                        None,
                                    ));
                                }
                                ExprKind::Call(callee, args)
                                    if args.iter().any(|a| a.hir_id == expr.hir_id)
                                        && matches!(callee.kind, ExprKind::Path(QPath::Resolved(_, p)) if matches!(p.res, Res::Def(rustc_hir::def::DefKind::Fn, did) if did.is_local())) =>
                                {
                                    self.sites.push(site(
                                        SiteKind::CallArgument,
                                        expr.span,
                                        None,
                                        None,
                                    ));
                                }
                                _ => self.hold("element-use-shape"),
                            },
                            // `let x = if c { points[1] } else { points[0] };` —
                            // the element is a block's tail under an `if` a
                            // `let` consumes: a load of the `let`'s local.
                            Node::Block(block)
                                if block.expr.is_some_and(|e| e.hir_id == expr.hir_id) =>
                            {
                                let mut at = block.hir_id;
                                let mut consumer = None;
                                for _ in 0..4 {
                                    match tcx.parent_hir_node(at) {
                                        Node::Expr(e)
                                            if matches!(
                                                e.kind,
                                                ExprKind::If(..) | ExprKind::Block(..)
                                            ) =>
                                        {
                                            at = e.hir_id;
                                        }
                                        Node::LetStmt(local)
                                            if local.init.is_some_and(|init| init.hir_id == at) =>
                                        {
                                            consumer = Some(local);
                                            break;
                                        }
                                        _ => break,
                                    }
                                }
                                let Some(local) = consumer else {
                                    self.hold("element-use-shape");
                                    return;
                                };
                                let rustc_hir::PatKind::Binding(_, b, _, None) = local.pat.kind
                                else {
                                    self.hold("load-pattern");
                                    return;
                                };
                                if local.ty.is_some() {
                                    self.hold("load-annotated");
                                    return;
                                }
                                let Some(node) = self.subjects.get(&b) else {
                                    self.hold("load-consumer-not-a-subject");
                                    return;
                                };
                                self.sites
                                    .push(site(SiteKind::Load, expr.span, None, Some(*node)));
                            }
                            Node::LetStmt(local)
                                if local.init.is_some_and(|init| init.hir_id == expr.hir_id) =>
                            {
                                let rustc_hir::PatKind::Binding(_, b, _, None) = local.pat.kind
                                else {
                                    self.hold("load-pattern");
                                    return;
                                };
                                if local.ty.is_some() {
                                    self.hold("load-annotated");
                                    return;
                                }
                                let Some(node) = self.subjects.get(&b) else {
                                    self.hold("load-consumer-not-a-subject");
                                    return;
                                };
                                self.sites
                                    .push(site(SiteKind::Load, expr.span, None, Some(*node)));
                            }
                            _ => self.hold("element-use-shape"),
                        }
                        return;
                    }
                    // The array itself: `arr.as_ptr()` handed on is the
                    // receipted raw view (G build 2); `as_mut_ptr` belongs to
                    // the written-element family; anything else (its address,
                    // a copy) holds.
                    if is_array(expr) {
                        let parent = tcx.parent_hir_node(expr.hir_id);
                        let indexed = matches!(parent, Node::Expr(p) if matches!(p.kind, ExprKind::Index(base, _, _) if base.hir_id == expr.hir_id));
                        if indexed {
                            return;
                        }
                        if let Node::Expr(p) = parent
                            && let ExprKind::MethodCall(segment, receiver, args, _) = p.kind
                            && receiver.hir_id == expr.hir_id
                            && args.is_empty()
                        {
                            // Only the SHARED view: a written element holds
                            // earlier (`mutable-elements`), so `as_mut_ptr`
                            // needs no arm of its own — it falls through to
                            // the shape hold below.
                            match segment.ident.name.as_str() {
                                "as_ptr" => {
                                    self.sites.push(Site {
                                        owner: self.owner,
                                        kind: SiteKind::ArrayView,
                                        span: p.span,
                                        field_text: String::new(),
                                        rhs: None,
                                        local: None,
                                        index_text: None,
                                        consumer: None,
                                        base: None,
                                        raw_base: false,
                                        assign_span: None,
                                        hoists: Vec::new(),
                                        cast: None,
                                        written: false,
                                    });
                                    return;
                                }
                                _ => {}
                            }
                        }
                        self.hold("array-use-shape");
                        return;
                    }
                    intravisit::walk_expr(self, expr);
                }
            }
            let mut uses = Uses {
                tcx: self.tcx,
                owner: self.owner,
                binding: info.binding,
                subjects: self.subjects,
                kinds: self.kinds,
                sites: Vec::new(),
                hold: None,
            };
            uses.visit_body(body);
            (uses.sites, uses.hold)
        }
    }
    impl<'tcx> Visitor<'tcx> for Arrays<'_, 'tcx> {
        fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
            let tcx = self.tcx;
            if let Some(ty) = local.ty
                && let rustc_hir::TyKind::Array(elem, len) = ty.kind
                && let rustc_hir::TyKind::Ptr(mut_ty) = elem.kind
                && let rustc_hir::PatKind::Binding(_, binding, name, None) = local.pat.kind
            {
                let sm = tcx.sess.source_map();
                let (Ok(pointee), Ok(len)) = (
                    sm.span_to_snippet(mut_ty.ty.span),
                    sm.span_to_snippet(len.span()),
                ) else {
                    return;
                };
                let mut info = ArrayLocal {
                    owner: self.owner,
                    binding,
                    name: name.to_string(),
                    len,
                    pointee,
                    owning: false,
                };
                // The initializer: a repeated null literal, an element LIST
                // of null literals (the substrate's other spelling of the
                // same array — tulip writes `[0 as *const f64, 0 as ...]`),
                // or nothing. A list with a VALUE element is a different
                // family: each element is a store whose source must deliver,
                // and it holds under its own reason until that arm is built.
                let mut hold = None;
                let mut sites = Vec::new();
                let all_null = |elems: &[rustc_hir::Expr<'_>]| {
                    !elems.is_empty() && elems.iter().all(super::emitability::is_zero_literal)
                };
                match local.init {
                    None => {}
                    Some(init) => match init.kind {
                        ExprKind::Array(elems) if !all_null(elems) => {
                            // A value element that is a BUFFER (a local
                            // array's `as_ptr`, a byte-string literal) cannot
                            // become `Option<&T>`: its readers index past the
                            // first element, and R395-2 never widens a thin
                            // reference. The fat element form is excluded in
                            // turn by the whole-array view these arrays are
                            // handed on through (a fat element is two words).
                            let buffer_source = elems.iter().any(|elem| {
                                let mut source = elem;
                                while let ExprKind::Cast(inner, _) = source.kind {
                                    source = inner;
                                }
                                match source.kind {
                                    ExprKind::MethodCall(segment, ..) => matches!(
                                        segment.ident.name.as_str(),
                                        "as_ptr" | "as_mut_ptr"
                                    ),
                                    ExprKind::Lit(literal) => {
                                        matches!(literal.node, rustc_ast::LitKind::ByteStr(..))
                                    }
                                    _ => false,
                                }
                            });
                            hold = Some(if buffer_source {
                                "array-local-incomplete:initializer-element-buffer-source"
                                    .to_owned()
                            } else {
                                "array-local-incomplete:initializer-element-source".to_owned()
                            });
                        }
                        ExprKind::Repeat(elem, _) if super::emitability::is_zero_literal(elem) => {
                            sites.push(Site {
                                owner: self.owner,
                                kind: SiteKind::Literal,
                                span: init.span,
                                field_text: info.name.clone(),
                                rhs: Some(Rhs::Null),
                                local: None,
                                index_text: None,
                                consumer: None,
                                base: None,
                                raw_base: false,
                                assign_span: None,
                                hoists: Vec::new(),
                                cast: None,
                                written: false,
                            });
                        }
                        ExprKind::Array(_) => {
                            // Every element is the null literal: the same
                            // array as the repeat form, spelled out.
                            sites.push(Site {
                                owner: self.owner,
                                kind: SiteKind::Literal,
                                span: init.span,
                                field_text: info.name.clone(),
                                rhs: Some(Rhs::Null),
                                local: None,
                                index_text: None,
                                consumer: None,
                                base: None,
                                raw_base: false,
                                assign_span: None,
                                hoists: Vec::new(),
                                cast: None,
                                written: false,
                            });
                        }
                        _ => hold = Some("array-local-incomplete:initializer".to_owned()),
                    },
                }
                let body = tcx.hir_body(
                    tcx.hir_node_by_def_id(self.owner)
                        .body_id()
                        .expect("a function body"),
                );
                if mut_ty.mutbl.is_mut() {
                    // A written element is not one family but two: an array
                    // of BORROWED writable elements, and an array of OWNED
                    // buffers (one allocation per element, each released at
                    // its own C free) — six of the seven corpus arrays are
                    // the second. They are told apart by the element stores'
                    // sources and the release sites, and named apart so the
                    // census does not read one market as the other.
                    match mutable_element_family(info.binding, body) {
                        Ok(()) => info.owning = true,
                        Err(reason) => {
                            hold.get_or_insert(reason);
                        }
                    }
                }
                let (uses, use_hold) = if info.owning {
                    owned_element_uses(tcx, self.owner, &info, body, self.subjects, self.kinds)
                } else {
                    self.classify(&info, body)
                };
                sites.extend(uses);
                if hold.is_none() {
                    hold = use_hold;
                }
                self.found.push((info, sites, hold));
            }
            intravisit::walk_local(self, local);
        }
    }
    for &owner in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(owner).body_id() else { continue };
        let mut arrays = Arrays {
            tcx,
            owner,
            subjects,
            kinds,
            found: Vec::new(),
        };
        arrays.visit_body(tcx.hir_body(body_id));
        for (info, sites, hold) in arrays.found {
            let key = FieldKey {
                struct_did: info.owner,
                field_index: info.binding.local_id.as_usize(),
            };
            let struct_path = tcx.def_path_str(info.owner.to_def_id());
            let field_name = info.name.clone();
            let mut hold = hold;
            if let Some(cause) = withdrawn.get(&key) {
                hold = Some(cause.clone());
            }
            if hold.is_none() && !sites.iter().any(|s| s.kind == SiteKind::Store) {
                hold = Some("array-local-incomplete:never-stored".to_owned());
            }
            if let Some(cause) = hold {
                out.holds.push((key, struct_path, field_name, cause));
                continue;
            }
            for site in &sites {
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
            let nullable = true; // initialised from a null repeat: `Option` always
            let _ = nullable;
            out.candidates.insert(
                key,
                Candidate {
                    key,
                    struct_path,
                    field_name,
                    owning: info.owning,
                    form: Form::Opt {
                        mutable: info.owning,
                        slice: info.owning,
                    },
                    sites,
                    mentions: Vec::new(),
                    impls: Vec::new(),
                    owners: vec![info.owner],
                    array: Some(info),
                },
            );
        }
    }
}

/// R411 §2 — the field-side count companion. For a FAT field stored from a
/// parameter `p_i` of `G`, a sibling integer field `C` of the same struct
/// stored in `G` from a parameter `p_j` is the fat field's count when some
/// element read of the fat field is guarded by a comparison against `C`
/// (a local loaded from `C`, or `C` read in place): the index's variables
/// appear on one side, `C`'s value on the other. Evidence, not a guess;
/// receipted per companion.
fn count_companions(
    tcx: TyCtxt<'_>,
    candidate: &Candidate,
    table: &DecisionTable,
) -> Vec<CountCompanion> {
    if !matches!(
        candidate.form,
        Form::Slice { .. } | Form::Opt { slice: true, .. }
    ) {
        return Vec::new();
    }
    // The element reads' index texts by owner.
    let mut index_texts: FxHashMap<LocalDefId, Vec<String>> = FxHashMap::default();
    for site in &candidate.sites {
        if site.kind == SiteKind::Element
            && let Some(index) = &site.index_text
        {
            index_texts
                .entry(site.owner)
                .or_default()
                .push(index.clone());
        }
    }
    if index_texts.is_empty() {
        return Vec::new();
    }
    let words = |text: &str| -> Vec<String> {
        text.split(|c: char| !(c.is_alphanumeric() || c == '_'))
            .filter(|w| {
                !w.is_empty()
                    && !w.chars().all(|c| c.is_ascii_digit())
                    && *w != "as"
                    && *w != "usize"
            })
            .map(str::to_owned)
            .collect()
    };
    let mut out = Vec::new();
    for site in &candidate.sites {
        if site.kind != SiteKind::Store {
            continue;
        }
        let Some(Rhs::Subject(node)) = site.rhs else { continue };
        let Some((subject, _)) = table
            .entries
            .iter()
            .find(|(s, _)| (s.fn_did, s.hir_id) == node)
        else {
            continue;
        };
        let SubjectKind::Param { hir_index: stored } = subject.kind else { continue };
        let callee = site.owner;
        for (sibling, count) in sibling_parameter_stores(tcx, callee, candidate.key.struct_did) {
            if sibling == candidate.field_name {
                continue;
            }
            // The bound: a comparison in an element-reading owner between the
            // sibling's value and the index's variables.
            let bounded = index_texts.iter().any(|(owner, indices)| {
                comparisons_against_field(tcx, *owner, &sibling)
                    .iter()
                    .any(|other| {
                        let other_words = words(other);
                        indices
                            .iter()
                            .any(|index| words(index).iter().any(|v| other_words.contains(v)))
                    })
            });
            if bounded {
                out.push(CountCompanion {
                    callee,
                    stored,
                    count,
                    sibling: sibling.clone(),
                });
            }
        }
    }
    out.sort_by(|a, b| (a.stored, a.count).cmp(&(b.stored, b.count)));
    out.dedup();
    out
}

/// `(*s).C = p_j` in `callee` for integer fields `C` of `struct_did` and
/// parameters `p_j`: `(field name, parameter position)`.
fn sibling_parameter_stores(
    tcx: TyCtxt<'_>,
    callee: LocalDefId,
    struct_did: LocalDefId,
) -> Vec<(String, usize)> {
    struct Stores<'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        struct_did: LocalDefId,
        params: FxHashMap<HirId, usize>,
        out: Vec<(String, usize)>,
    }
    impl<'tcx> Visitor<'tcx> for Stores<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let ExprKind::Field(base, ident) = lhs.kind
                && adt_local(self.tcx.typeck(self.owner).expr_ty_adjusted(base))
                    == Some(self.struct_did)
                && self.tcx.typeck(self.owner).expr_ty(rhs).is_integral()
                && let ExprKind::Path(QPath::Resolved(_, path)) = rhs.kind
                && let Res::Local(binding) = path.res
                && let Some(&index) = self.params.get(&binding)
            {
                self.out.push((ident.to_string(), index));
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let Some(body_id) = tcx.hir_node_by_def_id(callee).body_id() else { return Vec::new() };
    let body = tcx.hir_body(body_id);
    let params: FxHashMap<HirId, usize> = body
        .params
        .iter()
        .enumerate()
        .filter_map(|(index, param)| match param.pat.kind {
            rustc_hir::PatKind::Binding(_, binding, _, _) => Some((binding, index)),
            _ => None,
        })
        .collect();
    let mut stores = Stores {
        tcx,
        owner: callee,
        struct_did,
        params,
        out: Vec::new(),
    };
    stores.visit_body(body);
    stores.out
}

/// The texts on the OTHER side of every comparison in `owner` whose one side
/// reads the field `sibling` (`(*s).C`) or a local initialised from it.
fn comparisons_against_field(tcx: TyCtxt<'_>, owner: LocalDefId, sibling: &str) -> Vec<String> {
    struct Cmp<'tcx> {
        tcx: TyCtxt<'tcx>,
        sibling: String,
        loaded: FxHashSet<HirId>,
        out: Vec<String>,
    }
    impl Cmp<'_> {
        fn reads_sibling(&self, expr: &Expr<'_>) -> bool {
            match expr.kind {
                ExprKind::Field(_, ident) => ident.as_str() == self.sibling,
                ExprKind::Path(QPath::Resolved(_, path)) => {
                    matches!(path.res, Res::Local(b) if self.loaded.contains(&b))
                }
                _ => false,
            }
        }
    }
    impl<'tcx> Visitor<'tcx> for Cmp<'tcx> {
        fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
            if let Some(init) = local.init
                && let ExprKind::Field(_, ident) = init.kind
                && ident.as_str() == self.sibling
                && let rustc_hir::PatKind::Binding(_, binding, _, _) = local.pat.kind
            {
                self.loaded.insert(binding);
            }
            intravisit::walk_local(self, local);
        }

        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Binary(op, left, right) = expr.kind
                && matches!(
                    op.node,
                    rustc_hir::BinOpKind::Lt
                        | rustc_hir::BinOpKind::Le
                        | rustc_hir::BinOpKind::Gt
                        | rustc_hir::BinOpKind::Ge
                )
            {
                let sm = self.tcx.sess.source_map();
                if self.reads_sibling(right)
                    && let Ok(text) = sm.span_to_snippet(left.span)
                {
                    self.out.push(text);
                }
                if self.reads_sibling(left)
                    && let Ok(text) = sm.span_to_snippet(right.span)
                {
                    self.out.push(text);
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let Some(body_id) = tcx.hir_node_by_def_id(owner).body_id() else { return Vec::new() };
    let mut cmp = Cmp {
        tcx,
        sibling: sibling.to_owned(),
        loaded: FxHashSet::default(),
        out: Vec::new(),
    };
    cmp.visit_body(tcx.hir_body(body_id));
    cmp.out
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
                // G build 2: the whole array handed on as `arr.as_ptr()`.
                // `[Option<&T>; N]` has the layout of `[*const T; N]` (NPO),
                // so the callee reads the same bytes; the cast is the bridge
                // (R130's second tier, receipted per site).
                SiteKind::ArrayView => {
                    let Some(array) = candidate.array.as_ref() else {
                        cause.get_or_insert_with(|| "array-view-without-array".to_owned());
                        continue;
                    };
                    edits.push(ExpressionEdit {
                        owner: site.owner,
                        span: site.span,
                        replacement: format!(
                            "{}.as_ptr() as *const *const {}",
                            array.name, array.pointee
                        ),
                        kind: "array-raw-view",
                        wrap: false,
                    });
                }
                // G: the array's null repeat is `[None; N]`.
                SiteKind::Literal if candidate.array.is_some() => {
                    let len = candidate
                        .array
                        .as_ref()
                        .map(|a| a.len.clone())
                        .unwrap_or_default();
                    edits.push(ExpressionEdit {
                        owner: site.owner,
                        span: site.span,
                        replacement: format!("[None; {len}]"),
                        kind: "array-null-repeat",
                        wrap: false,
                    });
                }
                SiteKind::Literal | SiteKind::Store => match site.rhs {
                    // An allocation belongs to the owned family; a reference
                    // place never takes one.
                    Some(Rhs::AllocationWithLength(_)) => {
                        cause.get_or_insert_with(|| {
                            "field-transaction-incomplete:allocation-into-a-reference".to_owned()
                        });
                        continue;
                    }
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
                    // Both arms of an `if` load the same local: one declaration.
                    if !load_locals.iter().any(|(node, _)| *node == local) {
                        load_locals.push((local, emitted));
                    }
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
            array: candidate.array.clone(),
            form: candidate.form,
            owners: candidate.owners.clone(),
            dependent_owners,
            impls: candidate.impls.clone(),
            signature_plans,
            expression_edits: edits,
            load_locals,
            argument_forms,
            count_companions: count_companions(tcx, candidate, table),
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
            // R440-4 (the joint shape with ownership-fields): an owning field
            // is `Option<Box<T>>` — null is `None` (R395-2) — so a move out
            // of it is an `Option<Box<T>>`, and the consumer must be the
            // OPTIONAL form. A non-optional Box consumer would need
            // `take().unwrap()`, which panics exactly where C read a null
            // child, so the transaction holds and names the contract instead.
            (SlotKind::Owning, Decision::Box(plan)) if plan.optional => {
                Ok((format!("{inner}.take()"), "owned-field-move"))
            }
            (SlotKind::Owning, Decision::Box(_)) => Err(format!(
                "owned-move-needs-optional-box:{}",
                subject_label(table, node)
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
            // A consumer delivered as a SLICE takes the owned buffer's own
            // slice — the boxed slice IS the extent, so nothing is
            // fabricated and no raw bridge is needed (G build 3: heman's and
            // lodepng's element buffers reach their walkers this way).
            (SlotKind::Ref, Decision::Slice { mutable, .. }) if fat => Ok((
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
                    slice: true,
                    ..
                },
            ) if fat => Ok((
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
            // G build 3: an owned ARRAY's null initializer is the whole
            // array's, exactly as the reference form's is — but an owned
            // element is not `Copy`, so the repeat takes the const form.
            SiteKind::Literal if candidate.array.is_some() => {
                let len = candidate
                    .array
                    .as_ref()
                    .map(|a| a.len.clone())
                    .unwrap_or_default();
                edits.push(ExpressionEdit {
                    owner: site.owner,
                    span: site.span,
                    replacement: format!("[const {{ None }}; {len}]"),
                    kind: "array-null-repeat",
                    wrap: false,
                });
            }
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
                    // G build 3: a fresh allocation whose own size argument
                    // proves the element count — the fat place reclaims it as
                    // a boxed slice of exactly that length (no fabricated
                    // extent; the allocation and the box are the same bytes).
                    Some(Rhs::AllocationWithLength(ref elements)) if fat => format!(
                        "core::ptr::NonNull::new({inner}).map(|__p| Box::from_raw(core::ptr::slice_from_raw_parts_mut(__p.as_ptr(), ({elements}) as usize)))"
                    ),
                    Some(Rhs::AllocationWithLength(_)) => from_raw(),
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
            // An owning FIELD has no array form: G's view site cannot occur
            // here, and a stray one is a typed hold, never a silent skip.
            SiteKind::ArrayView => {
                cause.get_or_insert_with(|| {
                    "field-transaction-incomplete:array-view-on-an-owned-field".to_owned()
                });
                continue;
            }
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
                    // G build 3: an owned ARRAY's element reaches a cast
                    // only at its release. If the callee is not a known
                    // deallocator the site cannot be a view — C would free
                    // memory the Box still owns — so the transaction holds.
                    None if candidate.array.is_some() => {
                        cause.get_or_insert_with(|| {
                            "array-owned-incomplete:release-not-a-deallocator".to_owned()
                        });
                        continue;
                    }
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
