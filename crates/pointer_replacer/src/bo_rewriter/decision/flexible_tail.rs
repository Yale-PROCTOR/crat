//! **wave-6a rule W6A-T1 — the split struct for a program-private flexible
//! tail.** (seat addendum 404, R404-2; relay wave-6a/003)
//!
//! A C struct hack `struct S { header…; T tail[1]; }` allocated as
//! `malloc(sizeof(S) + (n - 1) * sizeof(T))` becomes
//! `struct S { header…, tail: Box<[T]> }` with the allocation
//! `Box::new(S { header defaults…, tail: vec![0 as T; n].into_boxed_slice() })`,
//! every tail access `*(*p).tail.as_mut_ptr().offset(e)` → `(*p).tail[(e) as usize]`,
//! the allocating callee returning `Box<S>` (its C-ABI wrapper `Box::into_raw`),
//! every receiver a `Box<S>` local, the freeing callee taking `Box<S>` (its
//! wrapper `Box::from_raw`) with `free(p)` → `drop(p)`.
//!
//! **All or nothing per struct.** The layout change is visible to every
//! pointer to `S`, so the transaction admits only when every allocation of
//! `S`, every receiver, every freeing parameter and every tail access in the
//! crate is planned, and no foreign, fn-pointer or by-value consumer takes
//! `S` (the user's layout decision covers program-private structs only).
//! Otherwise the whole struct stays held with a typed reason, and every
//! subject keeps its prior `box-flexible-tail-held` disposition.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, QPath, UnOp,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_span::Span;

use super::{
    Ctx, Subject, SubjectKind,
    box_facts::{BoxExprEdit, BoxPlan, BoxPlanFailure, BoxShape, scalar_initializer_supported},
    construction::{CallResultTarget, ConstructionFacts},
    declaration::pointee_source,
};

/// One admitted struct transaction.
#[derive(Clone, Debug)]
pub(crate) struct StructTransaction {
    pub(crate) struct_did: LocalDefId,
    pub(crate) struct_path: String,
    pub(crate) tail_field_index: usize,
    pub(crate) tail_field_name: String,
    /// `Box<[T]>` element type as the declaration family renders it.
    pub(crate) element_type: String,
    /// Header field initializers in declaration order (`name: 0 as T`).
    pub(crate) header_initializers: Vec<String>,
    /// `impl Copy` / `impl Clone` items for the struct, removed with the split.
    pub(crate) impls_to_remove: Vec<LocalDefId>,
    /// Functions whose `*mut S` return becomes `Box<S>`.
    pub(crate) owning_returns: Vec<LocalDefId>,
    /// `(function, parameter index)` whose `*mut S` becomes `Box<S>`.
    pub(crate) owning_params: Vec<(LocalDefId, usize)>,
    /// Crate-wide tail-access rewrites (span → replacement).
    pub(crate) tail_edits: Vec<(Span, String)>,
    /// Item-level span edits for the span layer (the AST layer performs the
    /// same changes as node transforms): the tail field's type, each removed
    /// impl's item, each owning signature's output / parameter type.
    pub(crate) item_edits: Vec<(Span, String)>,
    /// The class every item edit is charged to (the first owning function).
    pub(crate) owner_class_fn: LocalDefId,
    /// Receipt lines (auditable).
    pub(crate) receipts: Vec<String>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Transactions {
    pub(crate) structs: FxHashMap<LocalDefId, StructTransaction>,
    /// Every subject the transaction plans: (function, binding) → plan.
    pub(crate) plans: FxHashMap<(LocalDefId, HirId), BoxPlan>,
    /// Structs examined and refused, with the typed reason.
    pub(crate) holds: Vec<(String, String)>,
}

impl Transactions {
    pub(crate) fn is_empty(&self) -> bool {
        self.structs.is_empty()
    }

    pub(crate) fn owning_return(&self, function: LocalDefId) -> Option<&StructTransaction> {
        self.structs
            .values()
            .find(|t| t.owning_returns.contains(&function))
    }

    pub(crate) fn owning_param(
        &self,
        function: LocalDefId,
        index: usize,
    ) -> Option<&StructTransaction> {
        self.structs
            .values()
            .find(|t| t.owning_params.contains(&(function, index)))
    }

    pub(crate) fn receipts_tsv(&self) -> String {
        let mut out = String::from("struct\tkind\tdetail\n");
        for transaction in self.structs.values() {
            for receipt in &transaction.receipts {
                out.push_str(&format!(
                    "{}\tadmitted\t{receipt}\n",
                    transaction.struct_path
                ));
            }
        }
        for (struct_path, hold) in &self.holds {
            out.push_str(&format!("{struct_path}\theld\t{hold}\n"));
        }
        out
    }
}

/// Decision-phase hook: a prior Box failure on a subject the transaction
/// plans is replaced by the transaction's plan; every other prior stands.
pub(crate) fn override_plan(
    ctx: &Ctx<'_, '_>,
    subject: &Subject,
    prior: Result<BoxPlan, BoxPlanFailure>,
) -> Result<BoxPlan, BoxPlanFailure> {
    match prior {
        Ok(plan) => Ok(plan),
        Err(failure) => match ctx
            .flexible_tails
            .plans
            .get(&(subject.fn_did, subject.hir_id))
        {
            Some(plan) => Ok(plan.clone()),
            None => Err(failure),
        },
    }
}

fn struct_of_pointer<'tcx>(ty: Ty<'tcx>) -> Option<DefId> {
    let TyKind::RawPtr(pointee, _) = ty.kind() else { return None };
    let TyKind::Adt(adt, _) = pointee.kind() else { return None };
    adt.is_struct().then(|| adt.did())
}

fn mentions_struct<'tcx>(ty: Ty<'tcx>, struct_did: DefId) -> bool {
    ty.walk().any(|arg| {
        matches!(arg.as_type().map(|t| t.kind()), Some(TyKind::Adt(adt, _)) if adt.did() == struct_did)
    })
}

fn snippet(tcx: TyCtxt<'_>, span: Span) -> String {
    tcx.sess
        .source_map()
        .span_to_snippet(span)
        .unwrap_or_else(|_| "<unrenderable>".to_owned())
}

fn peel_casts<'h>(mut e: &'h Expr<'h>) -> &'h Expr<'h> {
    while let ExprKind::Cast(inner, _) | ExprKind::AddrOf(_, _, inner) = &e.kind {
        e = inner;
    }
    e
}

fn is_size_of_call<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId, e: &Expr<'_>, of: Ty<'tcx>) -> bool {
    let e = peel_casts(e);
    let ExprKind::Call(callee, []) = &e.kind else { return false };
    let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind else { return false };
    let Some(last) = path.segments.last() else { return false };
    if last.ident.name.as_str() != "size_of" {
        return false;
    }
    let typeck = tcx.typeck(owner);
    let Some(args) = typeck.node_args_opt(callee.hir_id) else { return false };
    args.types().next().is_some_and(|t| t == of)
}

/// `sizeof(S) + (E) * sizeof(T)` (either operand order, `+`/`wrapping_add`,
/// `*`/`wrapping_mul`, casts peeled) → the element-count text `E`.
fn trailing_count<'h, 'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    e: &'h Expr<'h>,
    struct_ty: Ty<'tcx>,
    element_ty: Ty<'tcx>,
) -> Option<String> {
    let e = peel_casts(e);
    let (left, right) = match &e.kind {
        ExprKind::Binary(op, l, r) if op.node == rustc_hir::BinOpKind::Add => (*l, *r),
        ExprKind::MethodCall(seg, recv, [arg], _) if seg.ident.name.as_str() == "wrapping_add" => {
            (*recv, arg)
        }
        _ => return None,
    };
    let (_header, region) = if is_size_of_call(tcx, owner, left, struct_ty) {
        (left, right)
    } else if is_size_of_call(tcx, owner, right, struct_ty) {
        (right, left)
    } else {
        return None;
    };
    let region = peel_casts(region);
    let (l, r) = match &region.kind {
        ExprKind::Binary(op, l, r) if op.node == rustc_hir::BinOpKind::Mul => (*l, *r),
        ExprKind::MethodCall(seg, recv, [arg], _) if seg.ident.name.as_str() == "wrapping_mul" => {
            (*recv, arg)
        }
        _ => return None,
    };
    let count = if is_size_of_call(tcx, owner, l, element_ty) {
        r
    } else if is_size_of_call(tcx, owner, r, element_ty) {
        l
    } else {
        return None;
    };
    Some(snippet(tcx, count.span))
}

/// Collects, over one body, everything the transaction must know about `S`.
struct Scan<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    struct_did: DefId,
    struct_ty: Ty<'tcx>,
    tail_name: &'a str,
    /// `*(*p).tail.as_mut_ptr().offset(e)` sites → replacement.
    tail_edits: Vec<(Span, String)>,
    /// A `.tail` mention this rule cannot rewrite.
    unsupported_tail_uses: Vec<Span>,
    /// A place of type `S` read by value, a literal, or a foreign/indirect
    /// call taking `S` by pointer.
    boundary_uses: Vec<(Span, &'static str)>,
    /// Bare-local occurrences with spans (for the "not used after" check).
    local_uses: Vec<(HirId, Span)>,
    /// Direct calls: (callee def, argument spans + bare-local ids).
    calls: Vec<(DefId, Span, Vec<Option<HirId>>)>,
    /// `free(x as *mut c_void)` calls whose operand is a bare local of `*mut S`.
    frees: Vec<(HirId, Span)>,
    /// `return x` of a bare local.
    returned: Vec<HirId>,
    /// Deref sites consumed as a field base (`(*p).f`), never by value.
    consumed_derefs: FxHashSet<HirId>,
    /// Tail field expressions already rewritten as part of an access.
    handled_fields: FxHashSet<HirId>,
}

impl<'tcx> Scan<'_, 'tcx> {
    fn ty(&self, e: &Expr<'_>) -> Ty<'tcx> {
        self.tcx.typeck(self.owner).expr_ty(e)
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

    fn tail_access(&self, e: &Expr<'_>) -> Option<(Span, String)> {
        let ExprKind::Unary(UnOp::Deref, offset_call) = &e.kind else { return None };
        let ExprKind::MethodCall(offset, receiver, [index], _) = &offset_call.kind else {
            return None;
        };
        if offset.ident.name.as_str() != "offset" {
            return None;
        }
        let ExprKind::MethodCall(decay, field_expr, [], _) = &receiver.kind else { return None };
        if !matches!(decay.ident.name.as_str(), "as_mut_ptr" | "as_ptr") {
            return None;
        }
        let ExprKind::Field(base, field) = &field_expr.kind else { return None };
        if field.name.as_str() != self.tail_name || self.ty(base) != self.struct_ty {
            return None;
        }
        // `offset` takes `isize`; the index cast the source wrote for it is
        // peeled once so the emitted index reads `(e) as usize`, not
        // `(e as isize) as usize`.
        let index = match &index.kind {
            ExprKind::Cast(inner, ty)
                if matches!(&ty.kind, rustc_hir::TyKind::Path(QPath::Resolved(None, path))
                    if path.segments.last().is_some_and(|s| s.ident.name.as_str() == "isize")) =>
            {
                *inner
            }
            _ => index,
        };
        Some((
            e.span,
            format!(
                "{}.{}[({}) as usize]",
                snippet(self.tcx, base.span),
                self.tail_name,
                snippet(self.tcx, index.span)
            ),
        ))
    }
}

impl<'tcx> Visitor<'tcx> for Scan<'_, 'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if let Some(edit) = self.tail_access(e) {
            self.tail_edits.push(edit);
            // The base place is a deref consumed by the field access.
            if let ExprKind::Unary(_, call) = &e.kind
                && let ExprKind::MethodCall(_, recv, _, _) = &call.kind
                && let ExprKind::MethodCall(_, field_expr, _, _) = &recv.kind
                && let ExprKind::Field(base, _) = &field_expr.kind
            {
                self.consumed_derefs.insert(base.hir_id);
                self.handled_fields.insert(field_expr.hir_id);
            }
            intravisit::walk_expr(self, e);
            return;
        }
        match &e.kind {
            ExprKind::Field(base, field) => {
                if self.ty(base) == self.struct_ty {
                    self.consumed_derefs.insert(base.hir_id);
                    if field.name.as_str() == self.tail_name
                        && !self.handled_fields.contains(&e.hir_id)
                    {
                        self.unsupported_tail_uses.push(e.span);
                    }
                }
            }
            ExprKind::Unary(UnOp::Deref, _) if self.ty(e) == self.struct_ty => {
                if !self.consumed_derefs.contains(&e.hir_id) {
                    self.boundary_uses.push((e.span, "by-value-read"));
                }
            }
            ExprKind::Struct(..) if self.ty(e) == self.struct_ty => {
                self.boundary_uses.push((e.span, "struct-literal"));
            }
            ExprKind::Path(QPath::Resolved(_, path)) => {
                if let Res::Local(hir) = path.res {
                    self.local_uses.push((hir, e.span));
                }
                if self.ty(e) == self.struct_ty {
                    self.boundary_uses.push((e.span, "by-value-local"));
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
                let takes_struct = args
                    .iter()
                    .any(|arg| mentions_struct(self.ty(arg), self.struct_did));
                match callee_def {
                    Some(did) if foreign_fn(self.tcx, did) => {
                        if self.tcx.item_name(did).as_str() == "free"
                            && let [arg] = args
                            && let Some(hir) = Self::bare_local(arg)
                            && struct_of_pointer(self.ty(peel_casts(arg))) == Some(self.struct_did)
                        {
                            self.frees.push((hir, e.span));
                        } else if takes_struct {
                            self.boundary_uses.push((e.span, "foreign-call"));
                        }
                    }
                    Some(did) if did.is_local() => {
                        self.calls.push((
                            did,
                            e.span,
                            args.iter().map(|arg| Self::bare_local(arg)).collect(),
                        ));
                    }
                    Some(_) => {
                        if takes_struct {
                            self.boundary_uses.push((e.span, "external-call"));
                        }
                    }
                    None => {
                        if takes_struct {
                            self.boundary_uses.push((e.span, "indirect-call"));
                        }
                    }
                }
            }
            ExprKind::Ret(Some(value)) => {
                if let Some(hir) = Self::bare_local(value)
                    && struct_of_pointer(self.ty(value)) == Some(self.struct_did)
                {
                    self.returned.push(hir);
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, e);
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

/// Derive every transaction for the crate. Runs once, before the family
/// stages; no analysis fact and no model kind is read — the model's `Owning`
/// verdict on each planned subject is checked where the plan is consumed
/// (the owning arm of the ladder).
pub(crate) fn derive<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    constructions: &ConstructionFacts,
    subjects: &[Subject],
) -> Transactions {
    let mut out = Transactions::default();
    // 1. Candidate structs from the flexible-tail allocation sites.
    let mut candidates: FxHashMap<DefId, Vec<(LocalDefId, HirId)>> = FxHashMap::default();
    for &(owner, hir) in constructions.flexible_tail_allocations.keys() {
        let ty = tcx.typeck(owner).node_type(hir);
        if let Some(did) = struct_of_pointer(ty) {
            candidates.entry(did).or_default().push((owner, hir));
        }
    }
    let mut candidates = candidates.into_iter().collect::<Vec<_>>();
    candidates.sort_by_key(|(did, _)| did.index.as_u32());
    for (struct_did, mut alloc_sites) in candidates {
        alloc_sites
            .sort_by_key(|(owner, hir)| (owner.local_def_index.as_u32(), hir.local_id.as_u32()));
        // Crate-absolute, so the literal resolves from the allocating function's
        // module whatever it imports (`Box::new(crate::a::b::S { .. })`).
        let struct_path = format!("crate::{}", tcx.def_path_str(struct_did));
        let hold_path = struct_path.clone();
        let hold = |reason: String, out: &mut Transactions| {
            out.holds.push((hold_path.clone(), reason));
        };
        let Some(struct_local) = struct_did.as_local() else {
            hold("flexible-tail-struct-not-local".to_owned(), &mut out);
            continue;
        };
        let adt = tcx.adt_def(struct_did);
        let variant = adt.non_enum_variant();
        let struct_ty = tcx.type_of(struct_did).instantiate_identity();
        // 2. Shape: numeric header, trailing `[T; 0|1]` with numeric `T`.
        let Some((tail_index, tail_field)) = variant.fields.iter().enumerate().last() else {
            hold("flexible-tail-shape:no-fields".to_owned(), &mut out);
            continue;
        };
        let tail_ty = tcx.type_of(tail_field.did).instantiate_identity();
        let TyKind::Array(element_ty, len) = tail_ty.kind() else {
            hold(
                "flexible-tail-shape:last-field-not-array".to_owned(),
                &mut out,
            );
            continue;
        };
        let Some(declared_len) = len.try_to_target_usize(tcx) else {
            hold(
                "flexible-tail-shape:tail-length-unknown".to_owned(),
                &mut out,
            );
            continue;
        };
        if declared_len > 1 {
            hold(
                format!("flexible-tail-shape:tail-length={declared_len}"),
                &mut out,
            );
            continue;
        }
        let element_source = pointee_source(tcx, *element_ty);
        if !scalar_initializer_supported(&format!("{element_ty}")) {
            hold(
                format!("flexible-tail-shape:element-not-numeric:{element_ty}"),
                &mut out,
            );
            continue;
        }
        let mut header_initializers = Vec::new();
        let mut header_ok = true;
        for field in variant.fields.iter().take(tail_index) {
            let field_ty = tcx.type_of(field.did).instantiate_identity();
            if !matches!(
                field_ty.kind(),
                TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) | TyKind::Bool
            ) {
                hold(
                    format!("flexible-tail-header-unsupported:{}:{field_ty}", field.name),
                    &mut out,
                );
                header_ok = false;
                break;
            }
            let zero = if field_ty.is_bool() {
                "false".to_owned()
            } else {
                format!("0 as {}", pointee_source(tcx, field_ty))
            };
            header_initializers.push(format!("{}: {zero}", field.name));
        }
        if !header_ok {
            continue;
        }
        // 3. Every allocation site's count, from the byte expression.
        let mut counts: FxHashMap<(LocalDefId, HirId), String> = FxHashMap::default();
        let mut count_ok = true;
        for &(owner, hir) in &alloc_sites {
            let Some(&init_hir) = constructions.init_hirs.get(&(owner, hir)) else {
                hold("flexible-tail-count:no-initializer".to_owned(), &mut out);
                count_ok = false;
                break;
            };
            let init = tcx.hir_node(init_hir).expect_expr();
            let call = peel_casts(init);
            let ExprKind::Call(_, args) = &call.kind else {
                hold("flexible-tail-count:not-a-call".to_owned(), &mut out);
                count_ok = false;
                break;
            };
            let Some(size_arg) = args.last() else {
                hold("flexible-tail-count:no-size".to_owned(), &mut out);
                count_ok = false;
                break;
            };
            // The size is either inline or a local whose initializer holds it.
            let size_expr = match Scan::bare_local(size_arg) {
                Some(local) => constructions
                    .init_hirs
                    .get(&(owner, local))
                    .map(|h| tcx.hir_node(*h).expect_expr()),
                None => Some(size_arg),
            };
            let count =
                size_expr.and_then(|e| trailing_count(tcx, owner, e, struct_ty, *element_ty));
            let Some(count) = count else {
                hold(
                    format!(
                        "flexible-tail-count-unrecognized:{}",
                        snippet(tcx, size_arg.span).replace(['\n', '\t'], " ")
                    ),
                    &mut out,
                );
                count_ok = false;
                break;
            };
            counts.insert(
                (owner, hir),
                format!("(({count}) + {declared_len}) as usize"),
            );
        }
        if !count_ok {
            continue;
        }
        // 4. Scan every body: boundary uses, tail accesses, calls, frees.
        let tail_name = tail_field.name.to_string();
        let mut scans: FxHashMap<LocalDefId, Scan<'_, '_>> = FxHashMap::default();
        for &function in functions {
            let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else { continue };
            let mut scan = Scan {
                tcx,
                owner: function,
                struct_did,
                struct_ty,
                tail_name: &tail_name,
                tail_edits: Vec::new(),
                unsupported_tail_uses: Vec::new(),
                boundary_uses: Vec::new(),
                local_uses: Vec::new(),
                calls: Vec::new(),
                frees: Vec::new(),
                returned: Vec::new(),
                consumed_derefs: FxHashSet::default(),
                handled_fields: FxHashSet::default(),
            };
            scan.visit_body(tcx.hir_body(body_id));
            scans.insert(function, scan);
        }
        // 4a. Foreign signatures mentioning the struct, statics of its type.
        let mut crossing = None;
        for item in tcx.hir_crate_items(()).foreign_items() {
            let did = item.owner_id.to_def_id();
            if matches!(tcx.def_kind(did), DefKind::Fn) {
                let sig = tcx.fn_sig(did).skip_binder().skip_binder();
                if sig
                    .inputs()
                    .iter()
                    .chain([&sig.output()])
                    .any(|t| mentions_struct(*t, struct_did))
                {
                    crossing = Some(format!(
                        "flexible-tail-crosses-boundary:extern:{}",
                        tcx.def_path_str(did)
                    ));
                }
            }
        }
        if crossing.is_none() {
            for (function, scan) in &scans {
                if let Some((span, kind)) = scan.boundary_uses.first() {
                    crossing = Some(format!(
                        "flexible-tail-crosses-boundary:{kind}:{}:{}",
                        tcx.def_path_str(function.to_def_id()),
                        snippet(tcx, *span).replace(['\n', '\t'], " ")
                    ));
                    break;
                }
                if let Some(span) = scan.unsupported_tail_uses.first() {
                    crossing = Some(format!(
                        "flexible-tail-access-unsupported:{}:{}",
                        tcx.def_path_str(function.to_def_id()),
                        snippet(tcx, *span).replace(['\n', '\t'], " ")
                    ));
                    break;
                }
            }
        }
        if let Some(reason) = crossing {
            hold(reason, &mut out);
            continue;
        }
        // 4b. Every `*mut S` local/param in the crate must be planned.
        let pointer_subjects: Vec<&Subject> = subjects
            .iter()
            .filter(|s| {
                let ty = tcx.typeck(s.fn_did).node_type(s.hir_id);
                struct_of_pointer(ty) == Some(struct_did)
            })
            .collect();
        let alloc_set: FxHashSet<(LocalDefId, HirId)> = alloc_sites.iter().copied().collect();
        // Allocating callees: functions returning `*mut S` that return an
        // allocation local (or a receiver of one) by bare local.
        let mut owning_returns: Vec<LocalDefId> = Vec::new();
        let mut plans: FxHashMap<(LocalDefId, HirId), BoxPlan> = FxHashMap::default();
        let mut receipts = Vec::new();
        let mut planned_locals: FxHashSet<(LocalDefId, HirId)> = FxHashSet::default();
        let mut owning_params: Vec<(LocalDefId, usize)> = Vec::new();
        let mut failure: Option<String> = None;
        // Pass A: allocation locals and receivers (iterate to a fixpoint so a
        // receiver of a receiver-returning callee is reached).
        let mut receivers: Vec<(LocalDefId, HirId)> = Vec::new();
        let mut changed = true;
        while changed {
            changed = false;
            for s in &pointer_subjects {
                let key = (s.fn_did, s.hir_id);
                if planned_locals.contains(&key) || !matches!(s.kind, SubjectKind::Local) {
                    continue;
                }
                let admitted = alloc_set.contains(&key)
                    || match constructions.call_result_targets.get(&key) {
                        Some(CallResultTarget::DirectLocal(callee)) => {
                            owning_returns.contains(callee)
                        }
                        _ => false,
                    };
                if !admitted {
                    continue;
                }
                planned_locals.insert(key);
                if !alloc_set.contains(&key) {
                    receivers.push(key);
                }
                // A function returning this local by bare local returns `Box<S>`.
                if scans
                    .get(&s.fn_did)
                    .is_some_and(|scan| scan.returned.contains(&s.hir_id))
                    && !owning_returns.contains(&s.fn_did)
                {
                    owning_returns.push(s.fn_did);
                    changed = true;
                }
            }
        }
        // Pass B: freeing parameters — every caller passes a planned local
        // that is never used afterwards.
        for s in &pointer_subjects {
            let SubjectKind::Param { hir_index } = s.kind else { continue };
            let key = (s.fn_did, s.hir_id);
            let Some(scan) = scans.get(&s.fn_did) else { continue };
            let frees: Vec<Span> = scan
                .frees
                .iter()
                .filter(|(hir, _)| *hir == s.hir_id)
                .map(|(_, span)| *span)
                .collect();
            if frees.is_empty() {
                continue;
            }
            // The parameter must do nothing but be freed once: no other use.
            let other_uses = scan
                .local_uses
                .iter()
                .filter(|(hir, span)| *hir == s.hir_id && !frees.iter().any(|f| f.contains(*span)))
                .count();
            if other_uses != 0 || frees.len() != 1 {
                failure = Some(format!(
                    "flexible-tail-param-retained:{}:{}",
                    tcx.def_path_str(s.fn_did.to_def_id()),
                    s.param_name.as_deref().unwrap_or("?")
                ));
                break;
            }
            // Every direct call site passes a planned local, dead afterwards.
            let mut every_caller_transfers = true;
            let mut call_count = 0usize;
            for (caller, caller_scan) in &scans {
                for (callee, call_span, args) in &caller_scan.calls {
                    if *callee != s.fn_did.to_def_id() {
                        continue;
                    }
                    call_count += 1;
                    let Some(Some(arg)) = args.get(hir_index) else {
                        every_caller_transfers = false;
                        failure = Some(format!(
                            "flexible-tail-param-caller-retains:{}:not-a-local",
                            tcx.def_path_str(caller.to_def_id())
                        ));
                        break;
                    };
                    if !planned_locals.contains(&(*caller, *arg)) {
                        every_caller_transfers = false;
                        failure = Some(format!(
                            "flexible-tail-param-caller-retains:{}:unplanned-argument",
                            tcx.def_path_str(caller.to_def_id())
                        ));
                        break;
                    }
                    let used_after = caller_scan
                        .local_uses
                        .iter()
                        .any(|(hir, span)| *hir == *arg && span.lo() > call_span.hi());
                    if used_after {
                        every_caller_transfers = false;
                        failure = Some(format!(
                            "flexible-tail-param-caller-retains:{}:used-after-transfer",
                            tcx.def_path_str(caller.to_def_id())
                        ));
                        break;
                    }
                }
                if !every_caller_transfers {
                    break;
                }
            }
            if !every_caller_transfers {
                break;
            }
            planned_locals.insert(key);
            owning_params.push((s.fn_did, hir_index));
            plans.insert(
                key,
                BoxPlan {
                    shape: BoxShape::Sized,
                    optional: false,
                    expr_edits: vec![BoxExprEdit {
                        span: frees[0],
                        replacement: format!("drop({})", s.param_name.as_deref().unwrap_or("?")),
                        receipt: "flexible-tail-param-free-drop",
                    }],
                    delete_statements: Vec::new(),
                    receipts: vec![format!(
                        "flexible-tail-owning-param fn={} index={hir_index} callers={call_count}",
                        tcx.def_path_str(s.fn_did.to_def_id())
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
        if let Some(reason) = failure {
            hold(reason, &mut out);
            continue;
        }
        // Pass C: plans for allocation locals and receivers.
        for s in &pointer_subjects {
            let key = (s.fn_did, s.hir_id);
            if !planned_locals.contains(&key) || !matches!(s.kind, SubjectKind::Local) {
                continue;
            }
            let Some(scan) = scans.get(&s.fn_did) else { continue };
            let name = s.param_name.clone().unwrap_or_else(|| "?".to_owned());
            let mut expr_edits = Vec::new();
            let mut plan_receipts = Vec::new();
            if let Some(count) = counts.get(&key) {
                let init_span = constructions.init_spans[&key];
                expr_edits.push(BoxExprEdit {
                    span: init_span,
                    // Trailing comma: the AST printer's round trip keeps one.
                    replacement: format!(
                        "Box::new({} {{ {}{}{}: vec![0 as {element_source}; {count}].into_boxed_slice(), }})",
                        struct_path,
                        header_initializers.join(", "),
                        if header_initializers.is_empty() { "" } else { ", " },
                        tail_name
                    ),
                    receipt: "flexible-tail-split-allocation",
                });
                plan_receipts.push(format!("flexible-tail-allocation count={count}"));
            } else {
                plan_receipts.push("flexible-tail-receiver".to_owned());
            }
            let frees: Vec<Span> = scan
                .frees
                .iter()
                .filter(|(hir, _)| *hir == s.hir_id)
                .map(|(_, span)| *span)
                .collect();
            for span in &frees {
                expr_edits.push(BoxExprEdit {
                    span: *span,
                    replacement: format!("drop({name})"),
                    receipt: "flexible-tail-c-free-site-drop",
                });
            }
            let transferred = scan.calls.iter().any(|(callee, _, args)| {
                args.iter().enumerate().any(|(index, arg)| {
                    *arg == Some(s.hir_id)
                        && callee
                            .as_local()
                            .is_some_and(|callee| owning_params.contains(&(callee, index)))
                })
            });
            let returned = scan.returned.contains(&s.hir_id);
            let retained_sink = !frees.is_empty() || transferred || returned;
            // Any other use of the local at a call is a retention this rule
            // does not model (a raw callee keeping the pointer).
            let other_call_use = scan.calls.iter().any(|(callee, _, args)| {
                args.iter().enumerate().any(|(index, arg)| {
                    *arg == Some(s.hir_id)
                        && !callee
                            .as_local()
                            .is_some_and(|callee| owning_params.contains(&(callee, index)))
                        && !(foreign_fn(tcx, *callee) && tcx.item_name(*callee).as_str() == "free")
                })
            });
            if other_call_use {
                failure = Some(format!(
                    "flexible-tail-local-retained-at-call:{}:{name}",
                    tcx.def_path_str(s.fn_did.to_def_id())
                ));
                break;
            }
            if !retained_sink {
                plan_receipts.push("waiver-drop(scope-exit)".to_owned());
            }
            plans.insert(
                key,
                BoxPlan {
                    shape: BoxShape::Sized,
                    optional: false,
                    expr_edits,
                    delete_statements: Vec::new(),
                    receipts: plan_receipts,
                    fabricated_extent: false,
                    pointee_override: None,
                    inferred_binding: false,
                    overwrite_spans: Vec::new(),
                    retained_sink,
                    implicit_scope_close: !retained_sink,
                },
            );
        }
        if let Some(reason) = failure {
            hold(reason, &mut out);
            continue;
        }
        // 4c. Coverage: every pointer subject is planned.
        if let Some(uncovered) = pointer_subjects
            .iter()
            .find(|s| !planned_locals.contains(&(s.fn_did, s.hir_id)))
        {
            hold(
                format!("flexible-tail-uncovered-subject:{}", uncovered.label),
                &mut out,
            );
            continue;
        }
        // 4d. Every allocating callee is returned as a bare local only.
        let mut tail_edits = Vec::new();
        for scan in scans.values() {
            tail_edits.extend(scan.tail_edits.iter().cloned());
        }
        tail_edits.sort_by_key(|(span, _)| (span.lo().0, span.hi().0));
        // Impls of Copy / Clone for the struct.
        let mut impls_to_remove = Vec::new();
        for item_id in tcx.hir_crate_items(()).free_items() {
            let did = item_id.owner_id.def_id;
            if matches!(tcx.def_kind(did), DefKind::Impl { of_trait: true })
                && let Some(trait_ref) = tcx.impl_trait_ref(did)
            {
                let trait_did = trait_ref.skip_binder().def_id;
                let is_copy_or_clone = tcx.lang_items().copy_trait() == Some(trait_did)
                    || tcx.lang_items().clone_trait() == Some(trait_did);
                let self_ty = tcx.type_of(did).instantiate_identity();
                if is_copy_or_clone && self_ty == struct_ty {
                    impls_to_remove.push(did);
                }
            }
        }
        // A `#[derive(Copy, Clone)]` lives in the substrate text OUTSIDE the
        // struct item's reprint span and regenerates the impl at compile time;
        // only source-spelled impls (c2rust's `#[automatically_derived] impl`)
        // can be replaced at their own span.
        if let Some(generated) = impls_to_remove
            .iter()
            .find(|did| tcx.def_span(did.to_def_id()).from_expansion())
        {
            hold(
                format!(
                    "flexible-tail-derive-impl-unsupported:{}",
                    tcx.def_path_str(generated.to_def_id())
                ),
                &mut out,
            );
            continue;
        }
        // Item-level span edits: the field type, the impls, the signatures.
        let mut item_edits: Vec<(Span, String)> = Vec::new();
        if let rustc_hir::Node::Field(field) = tcx.hir_node_by_def_id(tail_field.did.expect_local())
        {
            item_edits.push((field.ty.span, format!("Box<[{element_source}]>")));
        }
        for &impl_did in &impls_to_remove {
            if let rustc_hir::Node::Item(item) = tcx.hir_node_by_def_id(impl_did)
                && let rustc_hir::ItemKind::Impl(im) = item.kind
            {
                item_edits.push((
                    item.span,
                    format!("impl {} {{ }}", snippet(tcx, im.self_ty.span)),
                ));
            }
        }
        for &function in &owning_returns {
            if let Some(decl) = tcx.hir_node_by_def_id(function).fn_decl()
                && let rustc_hir::FnRetTy::Return(ty) = decl.output
                && let rustc_hir::TyKind::Ptr(pointer) = ty.kind
            {
                item_edits.push((ty.span, format!("Box<{}>", snippet(tcx, pointer.ty.span))));
            }
        }
        // Owning parameters are subjects of their own: their `Box<S>` declaration
        // is the Box decision's, in both layers.
        let owner_class_fn = owning_returns
            .first()
            .or(owning_params.first().map(|(f, _)| f))
            .copied()
            .unwrap_or_else(|| alloc_sites[0].0);
        receipts.push(format!(
            "flexible-tail-split struct={struct_path} tail={tail_name} element={element_source} declared_len={declared_len} allocations={} receivers={} owning_returns={} owning_params={} tail_edits={} impls_removed={}",
            alloc_sites.len(),
            receivers.len(),
            owning_returns.len(),
            owning_params.len(),
            tail_edits.len(),
            impls_to_remove.len()
        ));
        out.plans.extend(plans);
        out.structs.insert(
            struct_local,
            StructTransaction {
                struct_did: struct_local,
                struct_path,
                tail_field_index: tail_index,
                tail_field_name: tail_name,
                element_type: element_source,
                header_initializers,
                impls_to_remove,
                owning_returns,
                owning_params,
                tail_edits,
                item_edits,
                owner_class_fn,
                receipts,
            },
        );
    }
    out
}
