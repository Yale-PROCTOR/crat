//! **wave-6a rule W6A-A1 — allocation-returning callees under a per-callee
//! certificate.** (charter wave-6a/001 §1(a); relay wave-6a/005 §1, R407-9)
//!
//! A local callee whose every `return` is either ONE bare local — an
//! allocation the ordinary Box arm plans, or a receiver of an already
//! certified callee — or a null literal returns `Box<T>` (`Option<Box<T>>`
//! when a null return or an optional allocation exists). Every receiver
//! `let r = callee(..)` in the crate becomes a `Box<T>` / `Option<Box<T>>`
//! local whose sinks are a C free (`drop` there), a return (the chain
//! continues through its own function's certificate) and deref / index
//! uses; a call argument stays a raw seam the ordinary bridge machinery
//! settles. Rust's move checking is the load-bearing guarantee (a use after
//! a transfer is E0382 and the class reverts); the Box filters (unique owner,
//! no alias, no overwrite) are the ordinary arm's, untouched — only the
//! RETURN boundary hold is lifted, because the return IS the transfer.
//!
//! The certificate supersedes the model's `Ref` on a receiver (relay 005:
//! a strictly stricter form on the evidence the certificate proves). It ALSO
//! supersedes `Raw` on the callee's allocation local and on a receiver when
//! the certificate proves the allocation from source — the frames of record
//! (L01″, and every fixture solve) call a returned allocation `Raw` on both
//! ends by the ownership-licensing wall, so the rule delivers nothing
//! otherwise; report 003 STOP 1 / report 004 STOP 1 name this extension for
//! the seat.
//!
//! Holds (typed, per callee or per receiver): `return-certificate-return-shape`,
//! `return-certificate-return-locals`, `return-certificate-allocation:<key>`,
//! `return-certificate-struct-field:<field>`, `return-certificate-owner-use:<form>`,
//! `return-certificate-receiver-use:<form>`, `return-certificate-receiver-model:<kind>`,
//! `return-certificate-indirect-callers`, `return-certificate-no-receivers`.

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
    construction::{CallResultTarget, Construction, ConstructionFacts},
    declaration::pointee_source,
    seam::ExplicitDeclarationSite,
};
use crate::{
    analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef},
    bo_rewriter::bridge_receipt::SignatureClassId,
};

/// One certified callee.
#[derive(Clone, Debug)]
pub(crate) struct Certificate {
    pub(crate) callee: LocalDefId,
    pub(crate) callee_path: String,
    /// The pointee as the source spells it.
    pub(crate) pointee: String,
    pub(crate) optional: bool,
    pub(crate) shape: BoxShape,
    /// The output type text (`Box<T>` / `Option<Box<T>>`).
    pub(crate) output_type: String,
    /// The output type's span (the span layer's edit target).
    pub(crate) output_span: Span,
    /// The returned local.
    pub(crate) returned: (LocalDefId, HirId),
    /// Receivers planned for this callee.
    pub(crate) receivers: Vec<(LocalDefId, HirId)>,
    /// Receivers returned by their own function: planned by THAT function's
    /// certificate, which must exist for this one to stand.
    pub(crate) returned_receivers: Vec<(LocalDefId, HirId)>,
    /// The callee this one's returned local is a receiver of (a chain).
    pub(crate) chained_from: Option<LocalDefId>,
    pub(crate) receipts: Vec<String>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Certificates {
    pub(crate) callees: FxHashMap<LocalDefId, Certificate>,
    /// Every subject a certificate plans: (function, binding) → plan.
    pub(crate) plans: FxHashMap<(LocalDefId, HirId), BoxPlan>,
    /// Refusals: binding → (label, typed reason). Keyed by the returned local
    /// for a callee hold, by the receiver for a receiver hold.
    pub(crate) holds: FxHashMap<(LocalDefId, HirId), (String, String)>,
}

impl Certificates {
    pub(crate) fn is_empty(&self) -> bool {
        self.callees.is_empty()
    }

    pub(crate) fn receipts_tsv(&self) -> String {
        let mut out = String::from("callee\tkind\tdetail\n");
        let mut callees: Vec<&Certificate> = self.callees.values().collect();
        callees.sort_by(|a, b| a.callee_path.cmp(&b.callee_path));
        for c in callees {
            for receipt in &c.receipts {
                out.push_str(&format!("{}\tadmitted\t{receipt}\n", c.callee_path));
            }
        }
        let mut holds: Vec<&(String, String)> = self.holds.values().collect();
        holds.sort();
        for (label, hold) in holds {
            out.push_str(&format!("{label}\theld\t{hold}\n"));
        }
        out
    }

    /// Every function a certificate touches (the callee and its receivers'
    /// owners): the AST layer applies a certificate only while none reverted.
    pub(crate) fn owners(&self, callee: LocalDefId) -> FxHashSet<LocalDefId> {
        let mut owners = FxHashSet::default();
        if let Some(c) = self.callees.get(&callee) {
            owners.insert(c.callee);
            owners.extend(c.receivers.iter().map(|(f, _)| *f));
            owners.extend(c.returned_receivers.iter().map(|(f, _)| *f));
        }
        owners
    }
}

/// Decision-phase hook, before the model's verdict is applied: a subject a
/// certificate plans is a Box whatever kind the model gave it (relay 005).
pub(crate) fn planned(ctx: &Ctx<'_, '_>, subject: &Subject) -> Option<Decision> {
    ctx.return_certificates
        .plans
        .get(&(subject.fn_did, subject.hir_id))
        .map(|plan| Decision::Box(plan.clone()))
}

/// After the decisions: unannotated receivers get their `Box<..>` spelled out.
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
        if !table.return_certificates.plans.contains_key(&node) || subject.ty_span.is_some() {
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

/// After the seams: a certificate reverts whole — the callee follows every
/// receiver's class and every receiver follows the callee's (the same edge
/// the zero-syntax interface sites register).
pub(crate) fn append_interface_dependencies(table: &mut DecisionTable) {
    let mut edges = Vec::new();
    for c in table.return_certificates.callees.values() {
        let callee = SignatureClassId::of(c.callee);
        for (f, _) in c.receivers.iter().chain(&c.returned_receivers) {
            let receiver = SignatureClassId::of(*f);
            if receiver != callee {
                edges.push((callee, receiver));
                edges.push((receiver, callee));
            }
        }
        if let Some(source) = c.chained_from {
            let source = SignatureClassId::of(source);
            if source != callee {
                edges.push((callee, source));
                edges.push((source, callee));
            }
        }
    }
    table.seams.interface_dependencies.extend(edges);
    table.seams.interface_dependencies.sort();
    table.seams.interface_dependencies.dedup();
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

fn null_literal(e: &Expr<'_>) -> bool {
    matches!(
        &peel_casts(e).kind,
        ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(v, _) if v.get() == 0)
    )
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

enum Returned {
    Local(HirId, Span),
    Null(Span),
    Other(Span),
}

#[derive(Default)]
struct Scan<'tcx> {
    tcx: Option<TyCtxt<'tcx>>,
    /// Every `return e` (the operand's span kept for the edit).
    returns: Vec<Returned>,
    /// `free(x)` calls whose operand is a bare local: (local, call, argument).
    frees: Vec<(HirId, Span, Span)>,
    /// Local functions whose address is taken.
    fn_values: FxHashSet<DefId>,
    /// Every direct call of a local function: (callee, call span).
    calls: Vec<(DefId, Span)>,
}

impl<'tcx> Visitor<'tcx> for Scan<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx.expect("scan tcx")
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        match &e.kind {
            ExprKind::Ret(Some(value)) => {
                self.returns.push(if let Some(hir) = bare_local(value) {
                    Returned::Local(hir, value.span)
                } else if null_literal(value) {
                    Returned::Null(value.span)
                } else {
                    Returned::Other(value.span)
                });
            }
            ExprKind::Path(QPath::Resolved(_, path)) => {
                if let Res::Def(DefKind::Fn, did) = path.res
                    && did.is_local()
                {
                    self.fn_values.insert(did);
                }
            }
            ExprKind::Call(callee, args) => {
                if let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind
                    && let Res::Def(DefKind::Fn, did) = path.res
                {
                    let tcx = self.tcx.expect("scan tcx");
                    if foreign_fn(tcx, did)
                        && tcx.item_name(did).as_str() == "free"
                        && let [arg] = args
                        && let Some(hir) = bare_local(arg)
                    {
                        self.frees.push((hir, e.span, arg.span));
                    } else if did.is_local() && !foreign_fn(tcx, did) {
                        self.calls.push((did, e.span));
                    }
                }
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

/// One owner's uses, classified by the parent of each bare occurrence.
struct OwnerUses {
    edits: Vec<BoxExprEdit>,
    /// `if A.is_null() { return null; }` guards of an allocation that cannot
    /// fail as a `Box`: the whole `if` becomes an empty block, and the null
    /// return inside it no longer counts.
    dead_guards: Vec<Span>,
    /// Null returns swallowed by a dead guard.
    dead_null_returns: Vec<Span>,
}

struct UseWalk<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    binding: HirId,
    name: &'a str,
    shape: BoxShape,
    optional: bool,
    /// The owner is the callee's own allocation (its null test is dead).
    allocation: bool,
    frees: &'a [(Span, Span)],
    /// Is the callee's formal at this index a Ref-modeled local formal?
    lend_ok: &'a dyn Fn(DefId, usize) -> bool,
    out: Result<OwnerUses, String>,
}

impl<'tcx> UseWalk<'_, 'tcx> {
    fn snippet(&self, span: Span) -> String {
        self.tcx
            .sess
            .source_map()
            .span_to_snippet(span)
            .unwrap_or_default()
    }

    fn refuse(&mut self, form: String) {
        if self.out.is_ok() {
            self.out = Err(form);
        }
    }

    fn push(&mut self, span: Span, replacement: String, receipt: &'static str) {
        if let Ok(uses) = &mut self.out {
            uses.edits.push(BoxExprEdit {
                span,
                replacement,
                receipt,
            });
        }
    }

    /// The nearest non-cast ancestor expression of `e`, with the cast chain's
    /// outermost expression (what the parent actually holds).
    fn parent_of(&self, e: &Expr<'_>) -> Option<(&'tcx Expr<'tcx>, HirId)> {
        let mut child = e.hir_id;
        loop {
            let rustc_hir::Node::Expr(parent) = self.tcx.parent_hir_node(child) else {
                return None;
            };
            if matches!(parent.kind, ExprKind::Cast(..)) {
                child = parent.hir_id;
                continue;
            }
            return Some((parent, child));
        }
    }

    fn classify(&mut self, e: &Expr<'_>) {
        let Some((parent, child)) = self.parent_of(e) else {
            // A statement-level bare use (`p;`) — nothing to rewrite.
            return;
        };
        let name = self.name.to_owned();
        match &parent.kind {
            ExprKind::MethodCall(seg, recv, args, _) if recv.hir_id == child => {
                match seg.ident.name.as_str() {
                    "is_null" => {
                        let negated = matches!(
                            self.tcx.parent_hir_node(parent.hir_id),
                            rustc_hir::Node::Expr(not) if matches!(not.kind, ExprKind::Unary(rustc_hir::UnOp::Not, _))
                        );
                        // A dead guard: `if A.is_null() { return null; }`.
                        // HIR wraps an `if` condition in `DropTemps`.
                        let mut cond_id = parent.hir_id;
                        if let rustc_hir::Node::Expr(temps) = self.tcx.parent_hir_node(cond_id)
                            && matches!(temps.kind, ExprKind::DropTemps(_))
                        {
                            cond_id = temps.hir_id;
                        }
                        if self.allocation
                            && !negated
                            && let rustc_hir::Node::Expr(if_expr) =
                                self.tcx.parent_hir_node(cond_id)
                            && let ExprKind::If(cond, then, None) = if_expr.kind
                            && cond.hir_id == cond_id
                            && let ExprKind::Block(block, _) = then.kind
                            && block.stmts.len() <= 1
                            && let Some(ret) = block.expr.or_else(|| {
                                match block.stmts.first().map(|st| &st.kind) {
                                    Some(
                                        rustc_hir::StmtKind::Semi(ex)
                                        | rustc_hir::StmtKind::Expr(ex),
                                    ) => Some(ex),
                                    _ => None,
                                }
                            })
                            && let ExprKind::Ret(Some(value)) = ret.kind
                            && null_literal(value)
                        {
                            if let Ok(uses) = &mut self.out {
                                uses.dead_guards.push(if_expr.span);
                                uses.dead_null_returns.push(value.span);
                            }
                            self.push(
                                if_expr.span,
                                "{}".to_owned(),
                                "return-certificate-dead-null-guard",
                            );
                            return;
                        }
                        let (span, replacement) = if negated {
                            let rustc_hir::Node::Expr(not) =
                                self.tcx.parent_hir_node(parent.hir_id)
                            else {
                                unreachable!()
                            };
                            (
                                not.span,
                                if self.optional {
                                    format!("{name}.is_some()")
                                } else {
                                    "true".to_owned()
                                },
                            )
                        } else {
                            (
                                parent.span,
                                if self.optional {
                                    format!("{name}.is_none()")
                                } else {
                                    "false".to_owned()
                                },
                            )
                        };
                        self.push(span, replacement, "return-certificate-null-test");
                    }
                    "offset" | "add" | "wrapping_add" if args.len() == 1 => {
                        // Only as the operand of a deref: `*p.offset(e)`.
                        let Some((grand, _)) = self.parent_of(parent) else {
                            self.refuse(format!(
                                "pointer-arithmetic:{}",
                                self.snippet(parent.span)
                            ));
                            return;
                        };
                        if !matches!(grand.kind, ExprKind::Unary(rustc_hir::UnOp::Deref, _))
                            || self.shape != BoxShape::Slice
                            || self.optional
                        {
                            self.refuse(format!(
                                "pointer-arithmetic:{}",
                                self.snippet(parent.span)
                            ));
                            return;
                        }
                        let mut index: &Expr<'_> = &args[0];
                        if let ExprKind::Cast(inner, ty) = &index.kind
                            && self.snippet(ty.span) == "isize"
                        {
                            index = inner;
                        }
                        let index_text = self.snippet(index.span);
                        self.push(
                            grand.span,
                            format!("{name}[({index_text}) as usize]"),
                            "return-certificate-element-access",
                        );
                    }
                    other => self.refuse(format!("method:{other}")),
                }
            }
            ExprKind::Unary(rustc_hir::UnOp::Deref, _) => {
                let replacement = match (self.shape, self.optional) {
                    (BoxShape::Sized, false) => format!("(*{name})"),
                    (BoxShape::Sized, true) => format!("(*{name}.as_deref_mut().unwrap())"),
                    (BoxShape::Slice, false) => format!("{name}[0]"),
                    (BoxShape::Slice, true) => {
                        self.refuse("optional-slice-deref".to_owned());
                        return;
                    }
                };
                self.push(parent.span, replacement, "return-certificate-deref");
            }
            ExprKind::Ret(_) => {}
            ExprKind::Assign(lhs, _, _) if lhs.hir_id == child => {}
            ExprKind::Call(callee, args) if args.iter().any(|a| a.hir_id == child) => {
                if self.frees.iter().any(|(call, _)| *call == parent.span) {
                    return; // the free: `drop` is planned by the caller
                }
                if self.optional {
                    self.refuse(format!(
                        "optional-owner-call-argument:{}",
                        self.snippet(parent.span)
                    ));
                    return;
                }
                // A lend to a local callee whose formal the model calls Ref
                // (a Ref formal is never freed or kept: the freed-slot gate
                // and the null ruling) is a seam the ordinary bridge settles;
                // any other callee may consume or keep the pointer.
                let index = args
                    .iter()
                    .position(|a| a.hir_id == child)
                    .expect("argument");
                let callee_def = match &callee.kind {
                    ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                        Res::Def(DefKind::Fn, did) => Some(did),
                        _ => None,
                    },
                    _ => None,
                };
                if !callee_def.is_some_and(|did| (self.lend_ok)(did, index)) {
                    self.refuse(format!(
                        "call-argument-not-a-lend:{}",
                        self.snippet(parent.span)
                    ));
                }
            }
            _ => self.refuse(format!("use:{}", self.snippet(parent.span))),
        }
    }
}

impl<'tcx> Visitor<'tcx> for UseWalk<'_, 'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if let ExprKind::Path(QPath::Resolved(_, path)) = &e.kind
            && let Res::Local(hir) = path.res
            && hir == self.binding
        {
            self.classify(e);
        }
        intravisit::walk_expr(self, e);
    }
}

/// The owner's uses as rewrites, or the refused form.
fn owner_uses(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    shape: BoxShape,
    optional: bool,
    allocation: bool,
    frees: &[(Span, Span)],
    lend_ok: &dyn Fn(DefId, usize) -> bool,
) -> Result<OwnerUses, String> {
    let name = subject.param_name.clone().unwrap_or_else(|| "?".to_owned());
    let Some(body_id) = tcx.hir_node_by_def_id(subject.fn_did).body_id() else {
        return Err("no-body".to_owned());
    };
    let mut walk = UseWalk {
        tcx,
        binding: subject.hir_id,
        name: &name,
        shape,
        optional,
        allocation,
        frees,
        lend_ok,
        out: Ok(OwnerUses {
            edits: Vec::new(),
            dead_guards: Vec::new(),
            dead_null_returns: Vec::new(),
        }),
    };
    walk.visit_body(tcx.hir_body(body_id));
    let mut uses = walk.out?;
    uses.edits.sort_by_key(|e| (e.span.lo(), e.span.hi()));
    // An edit inside a dead guard is swallowed by the guard's own edit.
    let guards = uses.dead_guards.clone();
    uses.edits
        .retain(|e| guards.iter().all(|g| *g == e.span || !g.contains(e.span)));
    if uses
        .edits
        .windows(2)
        .any(|w| w[0].span.hi() > w[1].span.lo())
    {
        return Err("nested-owner-access".to_owned());
    }
    Ok(uses)
}

/// `Some(())` when the binding's first occurrence after its declaration lies
/// inside `statement` (the allocation overwrite), i.e. nothing reads the
/// null-initialized value.
fn first_use_is(tcx: TyCtxt<'_>, subject: &Subject, statement: Span) -> Option<()> {
    struct First {
        binding: HirId,
        first: Option<Span>,
    }
    impl<'tcx> Visitor<'tcx> for First {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &e.kind
                && let Res::Local(hir) = path.res
                && hir == self.binding
                && self.first.is_none_or(|f| e.span.lo() < f.lo())
            {
                self.first = Some(e.span);
            }
            intravisit::walk_expr(self, e);
        }
    }
    let body_id = tcx.hir_node_by_def_id(subject.fn_did).body_id()?;
    let mut first = First {
        binding: subject.hir_id,
        first: None,
    };
    first.visit_body(tcx.hir_body(body_id));
    statement.contains(first.first?).then_some(())
}

/// `Box::new(crate::S { .. })` with every field zeroed (numeric, bool, raw
/// pointer), or the field that has no zero.
fn struct_initializer<'tcx>(
    tcx: TyCtxt<'tcx>,
    pointee: rustc_middle::ty::Ty<'tcx>,
) -> Result<String, String> {
    let TyKind::Adt(adt, args) = pointee.kind() else {
        return Err("not-a-struct".to_owned());
    };
    if !adt.is_struct() {
        return Err("not-a-struct".to_owned());
    }
    let mut fields = Vec::new();
    for field in &adt.non_enum_variant().fields {
        let ty = field.ty(tcx, args);
        let zero = match ty.kind() {
            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
                format!("0 as {}", pointee_source(tcx, ty))
            }
            TyKind::Bool => "false".to_owned(),
            TyKind::RawPtr(..) => format!("0 as {}", pointee_source(tcx, ty)),
            _ => return Err(format!("struct-field:{}", field.name)),
        };
        fields.push(format!("{}: {zero}", field.name));
    }
    // Printed once through the AST printer so the use graft's whitespace-
    // insensitive round trip holds whatever line width the printer chooses
    // (a short literal loses its trailing comma, a long one keeps it).
    let text = format!(
        "Box::new(crate::{} {{ {} }})",
        tcx.def_path_str(adt.did()),
        fields.join(", ")
    );
    Ok(rustc_ast_pretty::pprust::expr_to_string(
        &::utils::ast::parse_expr(text),
    ))
}

/// Derive every certificate for the crate (fixpoint over chained returns).
#[allow(clippy::too_many_arguments)]
pub(crate) fn derive<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    constructions: &ConstructionFacts,
    subjects: &[Subject],
    box_facts: &BoxOwnershipFacts,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> Certificates {
    let mut out = Certificates::default();
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
    // Taken addresses anywhere in the crate — function bodies AND the
    // initializers of statics / consts (a fn-pointer table is a static).
    let mut fn_values: FxHashSet<DefId> = scans
        .values()
        .flat_map(|s| s.fn_values.iter().copied())
        .collect();
    for owner in tcx.hir_body_owners() {
        if scans.contains_key(&owner) {
            continue;
        }
        let mut scan = Scan {
            tcx: Some(tcx),
            ..Scan::default()
        };
        let Some(body_id) = tcx.hir_node_by_def_id(owner).body_id() else { continue };
        scan.visit_body(tcx.hir_body(body_id));
        fn_values.extend(scan.fn_values);
    }
    let slot_of = |s: &Subject| {
        slots
            .fn_local_slots
            .get(&s.fn_did)
            .and_then(|u| u.slot_for_local_depth(s.local, 0))
            .map(|slot| SlotRef::Local(s.fn_did, slot))
    };
    // A local callee's formal at `index` the model calls Ref.
    let lend_ok = |did: DefId, index: usize| -> bool {
        let Some(callee) = did.as_local() else { return false };
        if !functions.contains(&callee) {
            return false;
        }
        let body = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
        if index >= body.arg_count {
            return false;
        }
        let local = rustc_middle::mir::Local::from_usize(index + 1);
        slots
            .fn_local_slots
            .get(&callee)
            .and_then(|u| u.slot_for_local_depth(local, 0))
            .is_some_and(|slot| model.get(&SlotRef::Local(callee, slot)) == Some(&SlotKind::Ref))
    };
    let subject_of = |f: LocalDefId, hir: HirId| {
        subjects
            .iter()
            .find(|s| s.fn_did == f && s.hir_id == hir && s.kind == SubjectKind::Local)
    };
    // Candidate callees: local functions returning a depth-1 raw pointer.
    let mut candidates: Vec<LocalDefId> = functions
        .iter()
        .copied()
        .filter(|f| {
            let sig = tcx.fn_sig(f.to_def_id()).skip_binder().skip_binder();
            matches!(sig.output().kind(), TyKind::RawPtr(inner, _) if !inner.is_raw_ptr())
        })
        .collect();
    candidates.sort_by_key(|f| f.local_def_index.as_u32());
    // Receivers by callee, from the construction facts.
    let mut receivers_of: FxHashMap<LocalDefId, Vec<&Subject>> = FxHashMap::default();
    for s in subjects {
        if s.kind != SubjectKind::Local {
            continue;
        }
        let key = (s.fn_did, s.hir_id);
        if matches!(
            constructions.by_binding.get(&key),
            Some(Construction::CallResult)
        ) && let Some(CallResultTarget::DirectLocal(callee)) =
            constructions.call_result_targets.get(&key)
        {
            receivers_of.entry(*callee).or_default().push(s);
        }
    }
    for list in receivers_of.values_mut() {
        list.sort_by_key(|s| (s.fn_did.local_def_index.as_u32(), s.local.as_u32()));
    }
    let mut pending: Vec<LocalDefId> = candidates;
    let mut changed = true;
    while changed {
        changed = false;
        let mut next = Vec::new();
        for callee in pending {
            match certify(
                tcx,
                callee,
                &scans,
                &fn_values,
                constructions,
                subjects,
                box_facts,
                slots,
                model,
                &receivers_of,
                &slot_of,
                &subject_of,
                &lend_ok,
                &out,
            ) {
                Ok(Some((certificate, plans))) => {
                    out.plans.extend(plans);
                    out.callees.insert(callee, certificate);
                    changed = true;
                }
                Ok(None) => next.push(callee),
                Err((key, label, hold)) => {
                    out.holds.insert(key, (label, hold));
                }
            }
        }
        pending = next;
    }
    // A certificate stands only if every receiver its callee hands to a
    // returning function is planned by THAT function's certificate, and only
    // if the callee its own returned local chains from stands: withdraw to a
    // fixpoint, holding each withdrawn callee's returned local typed.
    loop {
        let withdraw: Vec<LocalDefId> = out
            .callees
            .values()
            .filter(|c| {
                c.returned_receivers
                    .iter()
                    .any(|(f, _)| !out.callees.contains_key(f))
                    || c.chained_from
                        .is_some_and(|source| !out.callees.contains_key(&source))
            })
            .map(|c| c.callee)
            .collect();
        if withdraw.is_empty() {
            break;
        }
        for callee in withdraw {
            let Some(c) = out.callees.remove(&callee) else { continue };
            out.plans.remove(&c.returned);
            for r in &c.receivers {
                out.plans.remove(r);
            }
            let label = subject_of(c.returned.0, c.returned.1)
                .map(|s| s.label.clone())
                .unwrap_or_else(|| c.callee_path.clone());
            out.holds.insert(
                c.returned,
                (
                    label,
                    format!(
                        "return-certificate-chain-open:{}:{}",
                        c.callee_path,
                        c.returned_receivers
                            .iter()
                            .map(|(f, _)| tcx.def_path_str(f.to_def_id()))
                            .chain(c.chained_from.map(|f| tcx.def_path_str(f.to_def_id())))
                            .collect::<Vec<_>>()
                            .join(",")
                    ),
                ),
            );
        }
    }
    // Chains that never closed (a receiver of an uncertified callee returned).
    for callee in pending {
        if let Some(scan) = scans.get(&callee)
            && let Some(Returned::Local(hir, _)) = scan
                .returns
                .iter()
                .find(|r| matches!(r, Returned::Local(..)))
            && let Some(s) = subject_of(callee, *hir)
        {
            out.holds.insert(
                (callee, *hir),
                (
                    s.label.clone(),
                    format!(
                        "return-certificate-return-locals:{}:uncertified-source",
                        tcx.def_path_str(callee.to_def_id())
                    ),
                ),
            );
        }
    }
    out
}

type Hold = ((LocalDefId, HirId), String, String);

/// `Ok(Some(..))` certified, `Ok(None)` waiting on another certificate,
/// `Err` refused with the typed hold.
#[allow(clippy::too_many_arguments)]
fn certify<'tcx, 's>(
    tcx: TyCtxt<'tcx>,
    callee: LocalDefId,
    scans: &FxHashMap<LocalDefId, Scan<'tcx>>,
    fn_values: &FxHashSet<DefId>,
    constructions: &ConstructionFacts,
    subjects: &'s [Subject],
    box_facts: &BoxOwnershipFacts,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    receivers_of: &FxHashMap<LocalDefId, Vec<&'s Subject>>,
    slot_of: &dyn Fn(&Subject) -> Option<SlotRef>,
    subject_of: &dyn Fn(LocalDefId, HirId) -> Option<&'s Subject>,
    lend_ok: &dyn Fn(DefId, usize) -> bool,
    done: &Certificates,
) -> Result<Option<(Certificate, Vec<((LocalDefId, HirId), BoxPlan)>)>, Hold> {
    let callee_path = tcx.def_path_str(callee.to_def_id());
    let scan = scans.get(&callee).expect("scanned");
    let mut returned_locals: Vec<HirId> = Vec::new();
    let mut null_returns: Vec<Span> = Vec::new();
    let mut local_returns: Vec<Span> = Vec::new();
    // (`null_returns` shrinks by the dead guards below.)
    for r in &scan.returns {
        match r {
            Returned::Local(hir, span) => {
                if !returned_locals.contains(hir) {
                    returned_locals.push(*hir);
                }
                local_returns.push(*span);
            }
            Returned::Null(span) => null_returns.push(*span),
            Returned::Other(span) => {
                let text = tcx
                    .sess
                    .source_map()
                    .span_to_snippet(*span)
                    .unwrap_or_default();
                let key = returned_locals
                    .first()
                    .and_then(|h| subject_of(callee, *h))
                    .map(|s| (s.fn_did, s.hir_id));
                let Some(key) = key else {
                    // No returned local at all: nothing to hold a row on.
                    return Err((
                        (callee, rustc_hir::CRATE_HIR_ID),
                        callee_path.clone(),
                        format!("return-certificate-return-shape:{callee_path}:{text}"),
                    ));
                };
                return Err((
                    key,
                    callee_path.clone(),
                    format!("return-certificate-return-shape:{callee_path}:{text}"),
                ));
            }
        }
    }
    let [returned] = returned_locals.as_slice() else {
        let key = returned_locals
            .first()
            .map(|h| (callee, *h))
            .unwrap_or((callee, rustc_hir::CRATE_HIR_ID));
        return Err((
            key,
            callee_path.clone(),
            format!(
                "return-certificate-return-locals:{callee_path}:{}",
                returned_locals.len()
            ),
        ));
    };
    let Some(subject) = subject_of(callee, *returned) else {
        return Err((
            (callee, *returned),
            callee_path.clone(),
            format!("return-certificate-return-locals:{callee_path}:not-a-subject"),
        ));
    };
    let key = (callee, *returned);
    let hold = |reason: String| -> Hold { (key, subject.label.clone(), reason) };
    if fn_values.contains(&callee.to_def_id()) {
        return Err(hold(format!(
            "return-certificate-indirect-callers:{callee_path}"
        )));
    }
    let receivers = receivers_of.get(&callee).map(Vec::as_slice).unwrap_or(&[]);
    if receivers.is_empty() {
        return Err(hold(format!(
            "return-certificate-no-receivers:{callee_path}"
        )));
    }
    let name = subject.param_name.clone().unwrap_or_else(|| "?".to_owned());
    let Some(slot) = slot_of(subject) else {
        return Err(hold(format!(
            "return-certificate-allocation:{callee_path}:no-slot"
        )));
    };
    // The returned local's own plan: an allocation the ordinary arm plans
    // (the return boundary lifted), a struct allocation this rule fills, or a
    // receiver of a certified callee.
    let construction = constructions.by_binding.get(&key);
    let body = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
    let return_slot = slots
        .fn_local_slots
        .get(&callee)
        .and_then(|u| u.slot_for_local_depth(rustc_middle::mir::RETURN_PLACE, 0))
        .map(|s| SlotRef::Local(callee, s));
    let pointee_ty = match body.local_decls[subject.local].ty.kind() {
        TyKind::RawPtr(p, _) => *p,
        _ => {
            return Err(hold(
                "return-certificate-allocation:not-a-pointer".to_owned(),
            ));
        }
    };
    let pointee = pointee_source(tcx, pointee_ty);
    let frees: Vec<(Span, Span)> = scan
        .frees
        .iter()
        .filter(|(hir, _, _)| *hir == *returned)
        .map(|(_, call, arg)| (*call, *arg))
        .collect();
    let (mut plan, source_receipt): (BoxPlan, String) = match construction {
        Some(Construction::CallResult) => match constructions.call_result_targets.get(&key) {
            Some(CallResultTarget::DirectLocal(source)) => match done.callees.get(source) {
                Some(source_certificate) => {
                    let plan = receiver_plan(
                        tcx,
                        subject,
                        source_certificate,
                        &frees,
                        lend_ok,
                        &format!(
                            "return-certificate-chained source={}",
                            source_certificate.callee_path
                        ),
                    )
                    .map_err(|reason| hold(reason))?;
                    (
                        plan,
                        format!("chained-from={}", source_certificate.callee_path),
                    )
                }
                None => return Ok(None),
            },
            _ => {
                return Err(hold(format!(
                    "return-certificate-allocation:{callee_path}:call-result-not-local"
                )));
            }
        },
        Some(Construction::Alloc { .. }) | Some(Construction::NullLit) => {
            let facts = match return_slot {
                Some(return_slot) => box_facts.without_boundary_hold(return_slot),
                None => box_facts.clone(),
            };
            let ordinary =
                facts.plan_for_subject(tcx, subject, slot, constructions, slots, subjects);
            match ordinary {
                Ok(plan) => (plan, "ordinary-plan".to_owned()),
                Err(BoxPlanFailure::InitializerUnsupported) => {
                    // A struct pointee: zero-fill the fields the C program then stores.
                    let initializer = struct_initializer(tcx, pointee_ty)
                        .map_err(|reason| hold(format!("return-certificate-{reason}")))?;
                    let overwrites = constructions
                        .owner_overwrites
                        .get(&key)
                        .map(Vec::as_slice)
                        .unwrap_or(&[]);
                    let init_span = *constructions.init_spans.get(&key).ok_or_else(|| {
                        hold("return-certificate-allocation:no-init-span".to_owned())
                    })?;
                    let mut expr_edits = Vec::new();
                    let mut delete_statements = Vec::new();
                    let optional;
                    match (construction, overwrites) {
                        (
                            Some(Construction::Alloc {
                                callee: alloc,
                                count: None,
                                ..
                            }),
                            [],
                        ) if alloc == "malloc" => {
                            optional = false;
                            expr_edits.push(BoxExprEdit {
                                span: init_span,
                                replacement: initializer.clone(),
                                receipt: "return-certificate-struct-allocation",
                            });
                        }
                        // `let mut a = 0 as *mut S; a = malloc(sizeof S) as *mut S;`
                        // with no use between: the allocation IS the
                        // initializer and the overwrite statement goes.
                        (Some(Construction::NullLit), [overwrite])
                            if matches!(
                                &overwrite.construction,
                                Construction::Alloc { callee, count: None, .. } if callee == "malloc"
                            ) =>
                        {
                            if first_use_is(tcx, subject, overwrite.statement_span).is_none() {
                                return Err(hold(format!(
                                    "return-certificate-allocation:{callee_path}:null-init-used-before-allocation"
                                )));
                            }
                            optional = false;
                            expr_edits.push(BoxExprEdit {
                                span: init_span,
                                replacement: initializer.clone(),
                                receipt: "return-certificate-struct-allocation",
                            });
                            delete_statements.push(overwrite.statement_span);
                        }
                        _ => {
                            return Err(hold(format!(
                                "return-certificate-allocation:{callee_path}:shape"
                            )));
                        }
                    }
                    (
                        BoxPlan {
                            shape: BoxShape::Sized,
                            optional,
                            expr_edits,
                            delete_statements,
                            receipts: vec![format!(
                                "return-certificate-struct-fill pointee={pointee}"
                            )],
                            fabricated_extent: false,
                            pointee_override: None,
                            inferred_binding: subject.ty_span.is_none(),
                            overwrite_spans: Vec::new(),
                            retained_sink: true,
                            implicit_scope_close: false,
                        },
                        "struct-fill".to_owned(),
                    )
                }
                // The ordinary arm's endpoints come from the model, which
                // calls a returned allocation Raw (its source endpoint is
                // not Active): a direct allocator initializer is planned
                // from source with ownership/fields' constructor rule (the
                // same `vec![..].into_boxed_slice()` / `Box::new(..)` text).
                Err(BoxPlanFailure::EndpointInactive)
                    if matches!(construction, Some(Construction::Alloc { .. }))
                        && constructions
                            .owner_overwrites
                            .get(&key)
                            .is_none_or(Vec::is_empty) =>
                {
                    let init_hir = *constructions
                        .init_hirs
                        .get(&key)
                        .ok_or_else(|| hold("return-certificate-allocation:no-init".to_owned()))?;
                    let init = tcx.hir_node(init_hir).expect_expr();
                    let constructor = super::ownership_fields_constructor::derive(
                        tcx, callee, init, pointee_ty,
                    )
                    .map_err(|reason| {
                        hold(format!(
                            "return-certificate-allocation:{callee_path}:constructor:{reason:?}"
                        ))
                    })?;
                    (
                        BoxPlan {
                            shape: constructor.shape,
                            optional: false,
                            expr_edits: vec![constructor.edit],
                            delete_statements: Vec::new(),
                            receipts: vec![format!(
                                "return-certificate-constructor count={} shape={:?}",
                                constructor.count, constructor.shape
                            )],
                            fabricated_extent: false,
                            pointee_override: None,
                            inferred_binding: subject.ty_span.is_none(),
                            overwrite_spans: Vec::new(),
                            retained_sink: true,
                            implicit_scope_close: false,
                        },
                        "constructor".to_owned(),
                    )
                }
                Err(failure) => {
                    return Err(hold(format!(
                        "return-certificate-allocation:{callee_path}:{}",
                        failure.key()
                    )));
                }
            }
        }
        _ => {
            return Err(hold(format!(
                "return-certificate-allocation:{callee_path}:construction"
            )));
        }
    };
    // The model: Owning admits; Raw admits only under the source certificate
    // (the frames of record call every returned allocation Raw; report 004
    // STOP 1); Ref never (a borrowed local is not an allocation).
    let kind = model.get(&slot).copied();
    if kind == Some(SlotKind::Ref) && !matches!(construction, Some(Construction::CallResult)) {
        return Err(hold(format!(
            "return-certificate-allocation-model:{callee_path}:ref"
        )));
    }
    if plan.pointee_override.is_some() {
        return Err(hold(format!(
            "return-certificate-allocation:{callee_path}:pointee-override"
        )));
    }
    // The returned local's uses: derefs, element accesses, null tests (a
    // `Box` cannot be null: the guard `if A.is_null() { return null; }` is
    // dead and goes), the return(s), a free on a non-returning path.
    let allocation = !matches!(construction, Some(Construction::CallResult));
    let uses = owner_uses(
        tcx,
        subject,
        plan.shape,
        plan.optional,
        allocation,
        &frees,
        lend_ok,
    )
    .map_err(|form| hold(format!("return-certificate-owner-use:{callee_path}:{form}")))?;
    let dead_null_returns = uses.dead_null_returns.clone();
    // R410-5 §2: each removed malloc guard is receipted (`dead-alloc-guard`,
    // the resource-scope waiver beside addendum 101).
    let dead_guard_receipts: Vec<String> = uses
        .dead_guards
        .iter()
        .map(|span| {
            format!(
                "dead-alloc-guard site={}",
                super::emitability::EmitabilityFacts::site(tcx, *span)
            )
        })
        .collect();
    let deleted = plan.delete_statements.clone();
    let owner_edits: Vec<BoxExprEdit> = uses
        .edits
        .into_iter()
        .filter(|e| !deleted.iter().any(|d| d.contains(e.span)))
        .collect();
    plan.expr_edits.retain(|e| {
        !owner_edits
            .iter()
            .any(|o| o.span == e.span || o.span.contains(e.span))
    });
    plan.expr_edits.extend(owner_edits);
    for (call, _) in &frees {
        if !plan.expr_edits.iter().any(|e| e.span == *call) {
            plan.expr_edits.push(BoxExprEdit {
                span: *call,
                replacement: format!("drop({name})"),
                receipt: "return-certificate-c-free-site-drop",
            });
        }
    }
    null_returns.retain(|span| !dead_null_returns.contains(span));
    plan.receipts
        .retain(|receipt| !receipt.starts_with("waiver-drop(scope-exit)"));
    plan.retained_sink = true;
    plan.implicit_scope_close = false;
    let optional_output = plan.optional || !null_returns.is_empty();
    // Return edits: null → None; a non-optional owner into an optional output → Some(..).
    for span in &null_returns {
        plan.expr_edits.push(BoxExprEdit {
            span: *span,
            replacement: "None".to_owned(),
            receipt: "return-certificate-null-return",
        });
    }
    if optional_output && !plan.optional {
        for span in &local_returns {
            plan.expr_edits.push(BoxExprEdit {
                span: *span,
                replacement: format!("Some({name})"),
                receipt: "return-certificate-some-return",
            });
        }
    }
    plan.receipts.push(format!(
        "return-certificate-owner callee={callee_path} source={source_receipt} model={kind:?}"
    ));
    plan.receipts.extend(dead_guard_receipts.iter().cloned());
    let Some(decl) = tcx.hir_node_by_def_id(callee).fn_decl() else {
        return Err(hold("return-certificate-allocation:no-decl".to_owned()));
    };
    let rustc_hir::FnRetTy::Return(output_ty) = decl.output else {
        return Err(hold("return-certificate-allocation:no-output".to_owned()));
    };
    // The output spells the pointee as the source does (both layers agree).
    let spelled = match output_ty.kind {
        rustc_hir::TyKind::Ptr(p) => tcx
            .sess
            .source_map()
            .span_to_snippet(p.ty.span)
            .unwrap_or_else(|_| pointee.clone()),
        _ => pointee.clone(),
    };
    let base = match plan.shape {
        BoxShape::Sized => format!("Box<{spelled}>"),
        BoxShape::Slice => format!("Box<[{spelled}]>"),
    };
    let output_type = if optional_output {
        format!("Option<{base}>")
    } else {
        base
    };
    // Receivers.
    let mut plans = vec![(key, plan.clone())];
    let mut planned_receivers = Vec::new();
    let mut returned_receivers = Vec::new();
    let mut receiver_labels: Vec<String> = Vec::new();
    let chained_from = match construction {
        Some(Construction::CallResult) => match constructions.call_result_targets.get(&key) {
            Some(CallResultTarget::DirectLocal(source)) => Some(*source),
            _ => None,
        },
        _ => None,
    };
    let certificate_stub = Certificate {
        callee,
        callee_path: callee_path.clone(),
        pointee: pointee.clone(),
        optional: optional_output,
        shape: plan.shape,
        output_type: output_type.clone(),
        output_span: output_ty.span,
        returned: key,
        receivers: Vec::new(),
        returned_receivers: Vec::new(),
        chained_from,
        receipts: Vec::new(),
    };
    for receiver in receivers {
        let rkey = (receiver.fn_did, receiver.hir_id);
        let rscan = scans.get(&receiver.fn_did).expect("scanned");
        let rfrees: Vec<(Span, Span)> = rscan
            .frees
            .iter()
            .filter(|(hir, _, _)| *hir == receiver.hir_id)
            .map(|(_, call, arg)| (*call, *arg))
            .collect();
        // A receiver the model calls Ref or Raw is superseded (relay 005 and
        // report 004 STOP 1); an Owning receiver is admitted as is.
        let rkind = slot_of(receiver).and_then(|s| model.get(&s).copied());
        // A receiver returned by its own function chains: that function's
        // certificate plans it (fixpoint); here it is only refused if that
        // function's returns are not certifiable at all — left to the chain.
        let returned_here = rscan
            .returns
            .iter()
            .any(|r| matches!(r, Returned::Local(h, _) if *h == receiver.hir_id));
        if returned_here {
            returned_receivers.push(rkey);
            continue;
        }
        let rplan = receiver_plan(
            tcx,
            receiver,
            &certificate_stub,
            &rfrees,
            lend_ok,
            &format!("return-certificate-receiver callee={callee_path} model={rkind:?}"),
        )
        .map_err(|reason| (rkey, receiver.label.clone(), reason))?;
        plans.push((rkey, rplan));
        planned_receivers.push(rkey);
        receiver_labels.push(receiver.label.clone());
    }
    // Every call of the callee is one of the receivers' initializers: a call
    // whose result goes anywhere else (a field store, an argument, a bare
    // statement) would meet the new output type untyped.
    let receiver_inits: Vec<Span> = planned_receivers
        .iter()
        .chain(&returned_receivers)
        .filter_map(|rkey| constructions.init_spans.get(rkey).copied())
        .collect();
    for (caller, caller_scan) in scans {
        for (target, call_span) in &caller_scan.calls {
            if *target != callee.to_def_id() {
                continue;
            }
            if !receiver_inits.iter().any(|init| init.contains(*call_span)) {
                return Err(hold(format!(
                    "return-certificate-call-site-not-a-receiver:{callee_path}:{}:{}",
                    tcx.def_path_str(caller.to_def_id()),
                    tcx.sess
                        .source_map()
                        .span_to_snippet(*call_span)
                        .unwrap_or_default()
                )));
            }
        }
    }
    let mut certificate = certificate_stub;
    certificate.receivers = planned_receivers;
    certificate.returned_receivers = returned_receivers;
    certificate.receipts.extend(dead_guard_receipts);
    certificate.receipts.push(format!(
        "return-certificate callee={callee_path} output={output_type} source={source_receipt} model={kind:?} null_returns={} receivers={} [{}] returned_receivers={}",
        null_returns.len(),
        certificate.receivers.len(),
        receiver_labels.join(","),
        certificate.returned_receivers.len()
    ));
    Ok(Some((certificate, plans)))
}

/// A receiver's plan: the callee's shape and optionality, its uses rewritten,
/// its C free a `drop`.
fn receiver_plan(
    tcx: TyCtxt<'_>,
    receiver: &Subject,
    certificate: &Certificate,
    frees: &[(Span, Span)],
    lend_ok: &dyn Fn(DefId, usize) -> bool,
    receipt: &str,
) -> Result<BoxPlan, String> {
    let name = receiver
        .param_name
        .clone()
        .unwrap_or_else(|| "?".to_owned());
    let uses = owner_uses(
        tcx,
        receiver,
        certificate.shape,
        certificate.optional,
        false,
        frees,
        lend_ok,
    )
    .map_err(|form| format!("return-certificate-receiver-use:{form}"))?;
    let mut expr_edits = uses.edits;
    for (call, _) in frees {
        expr_edits.push(BoxExprEdit {
            span: *call,
            replacement: format!("drop({name})"),
            receipt: "return-certificate-c-free-site-drop",
        });
    }
    let retained_sink = !frees.is_empty();
    let mut receipts = vec![receipt.to_owned()];
    if !retained_sink {
        receipts.push("waiver-drop(scope-exit)".to_owned());
    }
    Ok(BoxPlan {
        shape: certificate.shape,
        optional: certificate.optional,
        expr_edits,
        delete_statements: Vec::new(),
        receipts,
        fabricated_extent: false,
        pointee_override: None,
        inferred_binding: receiver.ty_span.is_none(),
        overwrite_spans: Vec::new(),
        retained_sink,
        implicit_scope_close: !retained_sink,
    })
}
