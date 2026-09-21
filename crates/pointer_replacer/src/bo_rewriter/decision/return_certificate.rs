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
    /// The returned local (`None` when every return is a call / null).
    pub(crate) returned: Option<(LocalDefId, HirId)>,
    /// Receivers planned for this callee (`let` and assignment receivers).
    pub(crate) receivers: Vec<(LocalDefId, HirId)>,
    /// Receivers returned by their own function: planned by THAT function's
    /// certificate, which must exist for this one to stand.
    pub(crate) returned_receivers: Vec<(LocalDefId, HirId)>,
    /// Functions that `return callee(..)` directly: certified themselves or
    /// this certificate withdraws.
    pub(crate) returning_callers: Vec<LocalDefId>,
    /// The callees this one's returns chain from (a receiver's source, a
    /// returned call's target).
    pub(crate) chained_from: Vec<LocalDefId>,
    /// Edits outside any subject's plan: a call stored straight into a raw
    /// place (`(*t).root = callee(..)` → `Box::into_raw(..)`), keyed by the
    /// storing function (which then follows this certificate's class).
    pub(crate) site_edits: Vec<(LocalDefId, BoxExprEdit)>,
    /// A1-c: transfers of an owner into a consuming formal a Box-parameter
    /// chain plans: (callee, index, the owner). Admitted on the formal's
    /// syntactic shape; CONFIRMED against the chains after they derive — an
    /// unconfirmed transfer withdraws this certificate (`confirm_transfers`).
    pub(crate) transfers: Vec<(DefId, usize, (LocalDefId, HirId))>,
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
            owners.extend(c.returning_callers.iter().copied());
            owners.extend(c.site_edits.iter().map(|(f, _)| *f));
        }
        owners
    }
}

/// A1-c, after the Box-parameter chains derive: a certificate whose owner
/// was admitted to move into a consuming formal stands only if a chain plans
/// that formal (`confirmed`); otherwise it withdraws — the transfer would
/// have been a raw seam beside a raw free, the double-free path.
pub(crate) fn confirm_transfers(
    certificates: &mut Certificates,
    tcx: TyCtxt<'_>,
    subjects: &[Subject],
    confirmed: &dyn Fn(DefId, usize) -> bool,
) {
    loop {
        let withdraw: Vec<LocalDefId> = certificates
            .callees
            .values()
            .filter(|c| c.transfers.iter().any(|(d, i, _)| !confirmed(*d, *i)))
            .map(|c| c.callee)
            .collect();
        if withdraw.is_empty() {
            break;
        }
        for callee in withdraw {
            let Some(c) = certificates.callees.remove(&callee) else { continue };
            if let Some(returned) = c.returned {
                certificates.plans.remove(&returned);
            }
            for r in &c.receivers {
                certificates.plans.remove(r);
            }
            let unconfirmed = c
                .transfers
                .iter()
                .filter(|(d, i, _)| !confirmed(*d, *i))
                .map(|(d, i, _)| format!("{}#{i}", tcx.def_path_str(*d)))
                .collect::<Vec<_>>()
                .join(",");
            let key = c.returned.unwrap_or((callee, rustc_hir::CRATE_HIR_ID));
            let label = subjects
                .iter()
                .find(|s| s.fn_did == key.0 && s.hir_id == key.1)
                .map(|s| s.label.clone())
                .unwrap_or_else(|| c.callee_path.clone());
            certificates.holds.insert(
                key,
                (
                    label,
                    format!(
                        "return-certificate-transfer-unconfirmed:{}:{unconfirmed}",
                        c.callee_path
                    ),
                ),
            );
        }
        // A withdrawn callee may have been another's source or receiver
        // owner: the ordinary withdrawal rule applies again.
        let withdraw_dependents: Vec<LocalDefId> = certificates
            .callees
            .values()
            .filter(|c| {
                c.chained_from
                    .iter()
                    .any(|s| !certificates.callees.contains_key(s))
                    || c.returned_receivers
                        .iter()
                        .any(|(f, _)| !certificates.callees.contains_key(f))
                    || c.returning_callers
                        .iter()
                        .any(|f| !certificates.callees.contains_key(f))
            })
            .map(|c| c.callee)
            .collect();
        for callee in withdraw_dependents {
            let Some(c) = certificates.callees.remove(&callee) else { continue };
            if let Some(returned) = c.returned {
                certificates.plans.remove(&returned);
            }
            for r in &c.receivers {
                certificates.plans.remove(r);
            }
            let key = c.returned.unwrap_or((callee, rustc_hir::CRATE_HIR_ID));
            certificates.holds.insert(
                key,
                (
                    c.callee_path.clone(),
                    format!("return-certificate-chain-open:{}:transfer", c.callee_path),
                ),
            );
        }
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
        for f in c
            .receivers
            .iter()
            .chain(&c.returned_receivers)
            .map(|(f, _)| *f)
            .chain(c.returning_callers.iter().copied())
            .chain(c.site_edits.iter().map(|(f, _)| *f))
        {
            let other = SignatureClassId::of(f);
            if other != callee {
                edges.push((callee, other));
                edges.push((other, callee));
            }
        }
        for source in &c.chained_from {
            let source = SignatureClassId::of(*source);
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

pub(crate) fn foreign_fn(tcx: TyCtxt<'_>, did: DefId) -> bool {
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
    /// `return callee(..)` of a local callee (the call's span).
    Call(DefId, Span),
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
    /// `x = callee(..)` with `x` a bare local: (local, callee, value span).
    /// (local, callee, value span, statement span)
    assign_calls: Vec<(HirId, DefId, Span, Span)>,
    /// `<place> = callee(..)` with a non-local place: (callee, value span).
    store_calls: Vec<(DefId, Span)>,
    /// Every assignment to a bare local: (local, value span).
    assigns: Vec<(HirId, Span)>,
}

fn local_callee(e: &Expr<'_>) -> Option<DefId> {
    let ExprKind::Call(callee, _) = &peel_casts(e).kind else { return None };
    let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind else { return None };
    match path.res {
        Res::Def(DefKind::Fn, did) if did.is_local() => Some(did),
        _ => None,
    }
}

/// What a `return` hands back, as the certificate reads it: a returned local,
/// a null literal, a local callee's result, or a shape this rule does not
/// read. A returned CONDITIONAL is read through its arms — `return if c {
/// owner } else { null }` is the same certificate as the two `return`
/// statements it abbreviates (urlparser's `get_part`, relay wave-6a/021), and
/// the `Some` / `None` edits land on the arms themselves. An arm with
/// statements of its own is NOT descended into: what those statements do to
/// the owner is exactly what this rule would have to prove.
fn classify_returned<'tcx>(tcx: TyCtxt<'tcx>, value: &'tcx Expr<'tcx>, out: &mut Vec<Returned>) {
    match &value.kind {
        ExprKind::If(_, then, Some(otherwise)) => {
            classify_returned(tcx, then, out);
            classify_returned(tcx, otherwise, out);
        }
        ExprKind::Block(block, _) if block.stmts.is_empty() => match block.expr {
            Some(tail) => classify_returned(tcx, tail, out),
            None => out.push(Returned::Other(value.span)),
        },
        _ => out.push(if let Some(hir) = bare_local(value) {
            Returned::Local(hir, value.span)
        } else if null_literal(value) {
            Returned::Null(value.span)
        } else if let Some(did) = local_callee(value)
            && !foreign_fn(tcx, did)
        {
            Returned::Call(did, value.span)
        } else {
            Returned::Other(value.span)
        }),
    }
}

impl<'tcx> Visitor<'tcx> for Scan<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx.expect("scan tcx")
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        match &e.kind {
            ExprKind::Ret(Some(value)) => {
                let tcx = self.tcx.expect("scan tcx");
                classify_returned(tcx, value, &mut self.returns);
            }
            ExprKind::Assign(lhs, rhs, _) => {
                let tcx = self.tcx.expect("scan tcx");
                if let Some(hir) = bare_local(lhs) {
                    self.assigns.push((hir, rhs.span));
                }
                let statement = match tcx.parent_hir_node(e.hir_id) {
                    rustc_hir::Node::Stmt(stmt) => stmt.span,
                    _ => e.span,
                };
                if let Some(did) = local_callee(rhs)
                    && !foreign_fn(tcx, did)
                {
                    match bare_local(lhs) {
                        Some(hir) => self.assign_calls.push((hir, did, rhs.span, statement)),
                        None => self.store_calls.push((did, rhs.span)),
                    }
                }
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

/// A formal's uses in its own body: `ok` while every occurrence is a deref,
/// an element access, a null test, or an argument onward to a local callee
/// (recorded in `nested` for the caller to certify the same way).
struct LendWalk<'tcx> {
    tcx: TyCtxt<'tcx>,
    binding: HirId,
    ok: bool,
    nested: Vec<(DefId, usize)>,
}

impl<'tcx> Visitor<'tcx> for LendWalk<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if let ExprKind::Path(QPath::Resolved(_, path)) = &e.kind
            && let Res::Local(hir) = path.res
            && hir == self.binding
        {
            // The nearest non-cast ancestor.
            let mut child = e.hir_id;
            let parent = loop {
                match self.tcx.parent_hir_node(child) {
                    rustc_hir::Node::Expr(parent) if matches!(parent.kind, ExprKind::Cast(..)) => {
                        child = parent.hir_id;
                    }
                    rustc_hir::Node::Expr(parent) => break Some((parent, child)),
                    _ => break None,
                }
            };
            match parent {
                Some((parent, child)) => match &parent.kind {
                    ExprKind::Unary(rustc_hir::UnOp::Deref, _) => {}
                    ExprKind::MethodCall(seg, recv, _, _) if recv.hir_id == child => {
                        let name = seg.ident.name.as_str();
                        let under_deref = matches!(
                            self.tcx.parent_hir_node(parent.hir_id),
                            rustc_hir::Node::Expr(g) if matches!(g.kind, ExprKind::Unary(rustc_hir::UnOp::Deref, _))
                        );
                        if !(name == "is_null"
                            || (matches!(name, "offset" | "add" | "wrapping_add") && under_deref))
                        {
                            self.ok = false;
                        }
                    }
                    ExprKind::Call(callee, args) if args.iter().any(|a| a.hir_id == child) => {
                        let index = args
                            .iter()
                            .position(|a| a.hir_id == child)
                            .expect("argument");
                        match &callee.kind {
                            ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                                // A local callee's formal (certified the same
                                // way) or a foreign position (the contract
                                // table) — both resolved by the caller.
                                Res::Def(DefKind::Fn, did) => self.nested.push((did, index)),
                                _ => self.ok = false,
                            },
                            _ => self.ok = false,
                        }
                    }
                    _ => self.ok = false,
                },
                // A `let q = p` copy or a statement-level use.
                None => {
                    if let rustc_hir::Node::LetStmt(local) = self.tcx.parent_hir_node(e.hir_id)
                        && local.init.is_some_and(|init| init.hir_id == e.hir_id)
                    {
                        self.ok = false;
                    }
                }
            }
        }
        intravisit::walk_expr(self, e);
    }
}

/// One owner's uses, classified by the parent of each bare occurrence.
pub(crate) struct OwnerUses {
    pub(crate) edits: Vec<BoxExprEdit>,
    /// `if A.is_null() { return null; }` guards of an allocation that cannot
    /// fail as a `Box`: the whole `if` becomes an empty block, and the null
    /// return inside it no longer counts.
    pub(crate) dead_guards: Vec<Span>,
    /// Null returns swallowed by a dead guard.
    pub(crate) dead_null_returns: Vec<Span>,
    /// Stores of the owner into raw places (`Box::into_raw` transfers).
    pub(crate) stores: Vec<Span>,
    /// Transfers into consuming formals: (callee, index, the call).
    pub(crate) transfers: Vec<(DefId, usize, Span)>,
    /// `return x` of the owner (the certificate chains it; a contract
    /// allocation holds on it).
    pub(crate) returns: Vec<Span>,
    /// Lends admitted: (callee, index, the call).
    pub(crate) lends: Vec<(DefId, usize, Span)>,
}

struct UseWalk<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    binding: HirId,
    name: &'a str,
    shape: BoxShape,
    optional: bool,
    /// The owner can never be null (an allocation, or a receiver of a
    /// non-optional certificate): its null guard is dead.
    never_null: bool,
    frees: &'a [(Span, Span)],
    /// Is the callee's formal at this index a Ref-modeled local formal?
    lend_ok: &'a dyn Fn(DefId, usize) -> bool,
    /// Is the callee's formal at this index a consuming formal a Box-parameter
    /// chain could plan (the move IS the sink)?
    transfer_ok: &'a dyn Fn(DefId, usize) -> bool,
    /// Does an assignment into this LOCAL take the owner's generation (the
    /// allocator-contract consumer's re-seat, `all_histograms = new_array`)?
    /// A certificate's receiver says no: a copy into a local is a second
    /// owner.
    move_ok: &'a dyn Fn(HirId) -> bool,
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

    /// The deref expression is written: the place of an assignment or a
    /// compound assignment, or borrowed mutably.
    /// [`Self::written`] through the places a struct owner's uses go through:
    /// `(*b).f = v` and `(*b).f[i] = v` write `*b` as surely as `*b = v` does,
    /// and a view taken shared for either would not compile.
    fn written_through_places(&self, deref: &'tcx Expr<'tcx>) -> bool {
        let mut node = deref;
        loop {
            if self.written(node) {
                return true;
            }
            match self.tcx.parent_hir_node(node.hir_id) {
                rustc_hir::Node::Expr(parent)
                    if matches!(parent.kind, ExprKind::Field(..) | ExprKind::Index(..)) =>
                {
                    node = parent;
                }
                _ => return false,
            }
        }
    }

    fn written(&self, deref: &Expr<'_>) -> bool {
        match self.tcx.parent_hir_node(deref.hir_id) {
            rustc_hir::Node::Expr(parent) => match parent.kind {
                ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _) => {
                    lhs.hir_id == deref.hir_id
                }
                ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, _) => true,
                _ => false,
            },
            _ => false,
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
            // `let q = p;` copies the owner — a second owner — refused; a
            // statement-level bare use (`p;`) has nothing to rewrite.
            if let rustc_hir::Node::LetStmt(local) = self.tcx.parent_hir_node(e.hir_id)
                && local.init.is_some_and(|init| init.hir_id == e.hir_id)
            {
                self.refuse(format!("copied-into-let:{}", self.snippet(local.span)));
            }
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
                        if self.never_null
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
                        // An optional slice owner (the contract consumer's
                        // conditional allocation) is read through
                        // `as_deref()` and written through `as_deref_mut()`.
                        let owner = if !self.optional {
                            name.clone()
                        } else if self.written(grand) {
                            format!("{name}.as_deref_mut().unwrap()")
                        } else {
                            format!("{name}.as_deref().unwrap()")
                        };
                        self.push(
                            grand.span,
                            format!("{owner}[({index_text}) as usize]"),
                            "return-certificate-element-access",
                        );
                    }
                    other => self.refuse(format!("method:{other}")),
                }
            }
            ExprKind::Unary(rustc_hir::UnOp::Deref, _) => {
                let replacement = match (self.shape, self.optional) {
                    // `*b` on a `Box<T>` is the source's own text: no edit,
                    // so no interval to collide with a bridge around it.
                    (BoxShape::Sized, false) => return,
                    (BoxShape::Sized, true) => format!("(*{name}.as_deref_mut().unwrap())"),
                    (BoxShape::Slice, false) => format!("{name}[0]"),
                    // **A4 / R483-3(i)** — `*b` on an `Option<Box<[T]>>` is the
                    // first element, which is the same view the `.offset` arm
                    // renders with an index of zero; the refusal here was a
                    // missing rendering, not a missing proof. The corpus's two
                    // are lil's `add_func::cmd` and `lil_clone_value::val`:
                    // `calloc(1, size_of::<T>())` owners whose uses are
                    // `(*cmd).field`, so the write must be seen THROUGH the
                    // projection or the view would be taken shared and the
                    // assignment would not compile.
                    (BoxShape::Slice, true) => {
                        if self.written_through_places(parent) {
                            format!("{name}.as_deref_mut().unwrap()[0]")
                        } else {
                            format!("{name}.as_deref().unwrap()[0]")
                        }
                    }
                };
                self.push(parent.span, replacement, "return-certificate-deref");
            }
            ExprKind::Ret(_) => {
                if let Ok(uses) = &mut self.out {
                    uses.returns.push(parent.span);
                }
            }
            ExprKind::Assign(lhs, _, _) if lhs.hir_id == child => {}
            // The owner stored into a raw place: ownership moves into C's
            // storage (`Box::into_raw`), exactly the batch-6 deallocator
            // transfer with the store as the sink; the C free of that place
            // stays a C free.
            ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == child => {
                if let Some(destination) = bare_local(lhs) {
                    // The generation MOVES into another owner (build 2's
                    // re-seat) — no edit, the `Option<Box<..>>` value itself
                    // is assigned; anything else is a second owner.
                    if !(self.move_ok)(destination) {
                        self.refuse(format!("copied-into-local:{}", self.snippet(parent.span)));
                    }
                    return;
                }
                let lhs_ty = self.tcx.typeck(lhs.hir_id.owner.def_id).expr_ty(lhs);
                if !matches!(lhs_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)) {
                    self.refuse(format!(
                        "stored-into-non-raw-place:{}",
                        self.snippet(parent.span)
                    ));
                    return;
                }
                let replacement = if self.optional {
                    format!("{name}.map_or(core::ptr::null_mut(), Box::into_raw)")
                } else {
                    format!("Box::into_raw({name})")
                };
                if let Ok(uses) = &mut self.out {
                    uses.stores.push(rhs.span);
                }
                self.push(rhs.span, replacement, "return-certificate-store-transfer");
            }
            ExprKind::Call(callee, args) if args.iter().any(|a| a.hir_id == child) => {
                if self.frees.iter().any(|(call, _)| *call == parent.span) {
                    return; // the free: `drop` is planned by the caller
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
                if let Some(did) = callee_def
                    && (self.transfer_ok)(did, index)
                {
                    // A1-c: moved into the consuming formal; the chain
                    // confirms it (`confirm_transfers`) or this owner withdraws.
                    if let Ok(uses) = &mut self.out {
                        uses.transfers.push((did, index, parent.span));
                    }
                    return;
                }
                let Some(did) = callee_def.filter(|did| (self.lend_ok)(*did, index)) else {
                    self.refuse(format!(
                        "call-argument-not-a-lend:{}",
                        self.snippet(parent.span)
                    ));
                    return;
                };
                if let Ok(uses) = &mut self.out {
                    uses.lends.push((did, index, parent.span));
                }
                // A LOCAL callee's converted formal is the seam's owner-view
                // glue (R422-5), and a BARE non-optional owner at a foreign
                // position is the ordinary raw-boundary glue's
                // (`x.as_mut_ptr()`). The two shapes with no glue are spelled
                // here, under the argument's own casts: an OPTIONAL owner at a
                // foreign position (the R130 void bridge of report 003 — the
                // view's raw pointer, or null when the owner is `None`), and
                // a CAST argument (`memset(x as *mut c_void, ..)`, brotli's
                // zeroing shape), where the raw-boundary site's operand is the
                // cast rather than the owner.
                // A LOCAL callee's CONVERTED formal is the seam's owner-view
                // glue (R422-5). Every other lend position keeps a raw formal —
                // a foreign callee's always, a local callee's when the model
                // leaves it raw — and there the owner's own view is spelled
                // here, because the ordinary raw bridge would render a bare
                // `as_mut_ptr()` on an `Option` (R451-3; report 023 measured 27
                // of brotli's 44 reverts as exactly that).
                let cast_argument = child != e.hir_id;
                // Two positions the seam's owner-view glue cannot reach, and
                // one it can. It edits the BARE argument of a CONVERTED formal
                // (R422-5), so: a CAST argument is spelled here whatever the
                // formal does (`memset(x as *mut c_void, ..)`, and the same
                // shape at a local callee — 18 of batch 10's brotli reverts),
                // and an OPTIONAL owner at a formal that stays RAW is spelled
                // here because the ordinary raw bridge would render a bare
                // `as_mut_ptr()` on an `Option` (27 more). A bare, non-optional
                // owner at a raw formal is exactly what that bridge renders
                // correctly, and spelling it again would be two edits on one
                // argument.
                if cast_argument || (foreign_fn(self.tcx, did) && self.optional) {
                    let casts = if cast_argument {
                        let outer = self.snippet(args[index].span);
                        let inner = self.snippet(e.span);
                        outer.strip_prefix(&inner).unwrap_or_default().to_owned()
                    } else {
                        String::new()
                    };
                    let view = match (self.shape, self.optional) {
                        (BoxShape::Slice, true) => format!(
                            "{name}.as_deref_mut().map_or(core::ptr::null_mut(), |s| s.as_mut_ptr())"
                        ),
                        (BoxShape::Sized, true) => format!(
                            "{name}.as_deref_mut().map_or(core::ptr::null_mut(), |b| core::ptr::from_mut(b))"
                        ),
                        (BoxShape::Slice, false) => format!("{name}.as_mut_ptr()"),
                        (BoxShape::Sized, false) => {
                            format!("core::ptr::from_mut(&mut *{name})")
                        }
                    };
                    self.push(
                        args[index].span,
                        format!("{view}{casts}"),
                        "return-certificate-foreign-lend",
                    );
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
#[allow(clippy::too_many_arguments)]
pub(crate) fn owner_uses(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    shape: BoxShape,
    optional: bool,
    never_null: bool,
    frees: &[(Span, Span)],
    lend_ok: &dyn Fn(DefId, usize) -> bool,
    transfer_ok: &dyn Fn(DefId, usize) -> bool,
    move_ok: &dyn Fn(HirId) -> bool,
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
        never_null,
        frees,
        lend_ok,
        transfer_ok,
        move_ok,
        out: Ok(OwnerUses {
            edits: Vec::new(),
            dead_guards: Vec::new(),
            dead_null_returns: Vec::new(),
            stores: Vec::new(),
            transfers: Vec::new(),
            returns: Vec::new(),
            lends: Vec::new(),
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

/// Is the callee's formal at `index` a LEND — a position that neither keeps
/// nor consumes the pointer? A local callee's formal the model calls Ref AND
/// whose every use in the callee is a read through it (derefs, element
/// accesses, null tests, lends onward to such formals): the model's Ref
/// alone does not say the callee keeps nothing — a store of the formal
/// through memory still emits as an escape later — so the callee's own body
/// is read (memoized; a cycle is not a lend). A FOREIGN position is a lend
/// when the pinned libc contract table says the callee neither retains nor
/// consumes it (`NoRetain` + `BorrowView`; `sscanf`, `strlen`, `strcmp`,
/// `memcpy`, ..): the ordinary raw-boundary glue bridges the owner at the
/// seam. A variadic tail position (`sscanf`'s `%[..]` target) is
/// `UnboundedWrite` on a byte owner — the same extent the raw program gave it.
/// Shared by the certificates (A1-d) and the allocator-contract consumer.
pub(crate) struct LendOracle<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    functions: &'a [LocalDefId],
    slots: &'a CrateSlots,
    model: &'a FxHashMap<SlotRef, SlotKind>,
    memo: std::cell::RefCell<FxHashMap<(DefId, usize), Option<bool>>>,
}

impl<'a, 'tcx> LendOracle<'a, 'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        functions: &'a [LocalDefId],
        slots: &'a CrateSlots,
        model: &'a FxHashMap<SlotRef, SlotKind>,
    ) -> Self {
        Self {
            tcx,
            functions,
            slots,
            model,
            memo: std::cell::RefCell::new(FxHashMap::default()),
        }
    }

    fn foreign_lend(&self, did: DefId, index: usize) -> bool {
        let tcx = self.tcx;
        if !foreign_fn(tcx, did) {
            return false;
        }
        let key = super::raw_boundary::symbol_key(tcx, did, self.functions);
        let sig = tcx.fn_sig(did).skip_binder().skip_binder();
        let Some(input) = sig.inputs().get(index) else {
            // A variadic position: no declared type; the table's family rows
            // (the scanf / printf tails) decide, at a byte target.
            let target = super::raw_boundary::RawTargetType {
                rendered: "*mut u8".to_owned(),
                pointee: "u8".to_owned(),
                mutability: super::raw_boundary::RawMutability::Mut,
                depth2: None,
            };
            return matches!(
                super::raw_boundary_contracts::classify_contract(&key, index, &target),
                Ok(c) if c.retention == super::raw_boundary_contracts::RetentionContract::NoRetain
                    && c.ownership == super::raw_boundary_contracts::OwnershipContract::BorrowView
            );
        };
        let Some(target) = super::raw_boundary::raw_target_type(tcx, *input) else {
            return false;
        };
        matches!(
            super::raw_boundary_contracts::classify_contract(&key, index, &target),
            Ok(c) if c.retention == super::raw_boundary_contracts::RetentionContract::NoRetain
                && c.ownership == super::raw_boundary_contracts::OwnershipContract::BorrowView
        )
    }

    pub(crate) fn lend(&self, did: DefId, index: usize) -> bool {
        let tcx = self.tcx;
        if foreign_fn(tcx, did) {
            return self.foreign_lend(did, index);
        }
        match self.memo.borrow().get(&(did, index)) {
            Some(Some(answer)) => return *answer,
            Some(None) => return false, // in progress: a cycle is not a lend
            None => {}
        }
        self.memo.borrow_mut().insert((did, index), None);
        let answer = (|| {
            let callee = did.as_local()?;
            if !self.functions.contains(&callee) {
                return Some(false);
            }
            let body = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
            if index >= body.arg_count {
                return Some(false);
            }
            let local = rustc_middle::mir::Local::from_usize(index + 1);
            let is_ref = self
                .slots
                .fn_local_slots
                .get(&callee)
                .and_then(|u| u.slot_for_local_depth(local, 0))
                .is_some_and(|slot| {
                    self.model.get(&SlotRef::Local(callee, slot)) == Some(&SlotKind::Ref)
                });
            if !is_ref {
                return Some(false);
            }
            let hir_body = tcx.hir_body_owned_by(callee);
            let param = hir_body.params.get(index)?;
            let rustc_hir::PatKind::Binding(_, hir, _, None) = param.pat.kind else {
                return Some(false);
            };
            let mut walk = LendWalk {
                tcx,
                binding: hir,
                ok: true,
                nested: Vec::new(),
            };
            walk.visit_body(hir_body);
            if !walk.ok {
                return Some(false);
            }
            Some(walk.nested.into_iter().all(|(d, i)| self.lend(d, i)))
        })()
        .unwrap_or(false);
        self.memo.borrow_mut().insert((did, index), Some(answer));
        answer
    }
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
    consuming_formals: &FxHashSet<(DefId, usize)>,
    raw_surface: &dyn Fn(LocalDefId) -> bool,
    exported_pairs: &super::exported_pair::Closure,
) -> Certificates {
    let mut out = Certificates::default();
    let transfer_ok =
        |did: DefId, index: usize| -> bool { consuming_formals.contains(&(did, index)) };
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
    let lend_oracle = LendOracle::new(tcx, functions, slots, model);
    let lend_ok = |did: DefId, index: usize| -> bool { lend_oracle.lend(did, index) };
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
                &transfer_ok,
                raw_surface,
                exported_pairs,
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
    // A certificate stands only if every function it depends on — one
    // returning a receiver of it, one returning a call of it, the callees its
    // own returns chain from — is certified: withdraw to a fixpoint, holding
    // each withdrawn callee typed (on its returned local where it has one).
    loop {
        let withdraw: Vec<LocalDefId> = out
            .callees
            .values()
            .filter(|c| {
                c.returned_receivers
                    .iter()
                    .any(|(f, _)| !out.callees.contains_key(f))
                    || c.returning_callers
                        .iter()
                        .any(|f| !out.callees.contains_key(f))
                    || c.chained_from
                        .iter()
                        .any(|source| !out.callees.contains_key(source))
            })
            .map(|c| c.callee)
            .collect();
        if withdraw.is_empty() {
            break;
        }
        for callee in withdraw {
            let Some(c) = out.callees.remove(&callee) else { continue };
            if let Some(returned) = c.returned {
                out.plans.remove(&returned);
            }
            for r in &c.receivers {
                out.plans.remove(r);
            }
            let key = c.returned.unwrap_or((callee, rustc_hir::CRATE_HIR_ID));
            let label = c
                .returned
                .and_then(|(f, h)| subject_of(f, h))
                .map(|s| s.label.clone())
                .unwrap_or_else(|| c.callee_path.clone());
            out.holds.insert(
                key,
                (
                    label,
                    format!(
                        "return-certificate-chain-open:{}:{}",
                        c.callee_path,
                        c.returned_receivers
                            .iter()
                            .map(|(f, _)| tcx.def_path_str(f.to_def_id()))
                            .chain(
                                c.returning_callers
                                    .iter()
                                    .map(|f| tcx.def_path_str(f.to_def_id()))
                            )
                            .chain(
                                c.chained_from
                                    .iter()
                                    .map(|f| tcx.def_path_str(f.to_def_id()))
                            )
                            .collect::<Vec<_>>()
                            .join(",")
                    ),
                ),
            );
        }
    }
    // Chains that never closed (a return chained from an uncertified callee).
    for callee in pending {
        let Some(scan) = scans.get(&callee) else { continue };
        let key = scan
            .returns
            .iter()
            .find_map(|r| match r {
                Returned::Local(hir, _) => Some((callee, *hir)),
                _ => None,
            })
            .unwrap_or((callee, rustc_hir::CRATE_HIR_ID));
        let label = subject_of(key.0, key.1)
            .map(|s| s.label.clone())
            .unwrap_or_else(|| tcx.def_path_str(callee.to_def_id()));
        out.holds.insert(
            key,
            (
                label,
                format!(
                    "return-certificate-return-locals:{}:uncertified-source",
                    tcx.def_path_str(callee.to_def_id())
                ),
            ),
        );
    }
    out
}

type Hold = ((LocalDefId, HirId), String, String);

/// What the callee's returns chain from: one owner local, calls to certified
/// callees, nulls.
struct Sources {
    /// The one returned local, its return spans.
    owner: Option<(HirId, Vec<Span>)>,
    /// `return callee(..)` sites: (target, call span).
    calls: Vec<(LocalDefId, Span)>,
    nulls: Vec<Span>,
}

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
    transfer_ok: &dyn Fn(DefId, usize) -> bool,
    raw_surface: &dyn Fn(LocalDefId) -> bool,
    exported_pairs: &super::exported_pair::Closure,
    done: &Certificates,
) -> Result<Option<(Certificate, Vec<((LocalDefId, HirId), BoxPlan)>)>, Hold> {
    let callee_path = tcx.def_path_str(callee.to_def_id());
    let scan = scans.get(&callee).expect("scanned");
    // 1. The returns.
    let mut sources = Sources {
        owner: None,
        calls: Vec::new(),
        nulls: Vec::new(),
    };
    let anon_key = (callee, rustc_hir::CRATE_HIR_ID);
    for r in &scan.returns {
        match r {
            Returned::Local(hir, span) => match &mut sources.owner {
                Some((owner, spans)) if *owner == *hir => spans.push(*span),
                Some((owner, _)) => {
                    let key = (callee, *owner);
                    let label = subject_of(callee, *owner)
                        .map(|s| s.label.clone())
                        .unwrap_or_else(|| callee_path.clone());
                    return Err((
                        key,
                        label,
                        format!("return-certificate-return-locals:{callee_path}:2"),
                    ));
                }
                None => sources.owner = Some((*hir, vec![*span])),
            },
            Returned::Call(target, span) => {
                let Some(local) = target.as_local() else {
                    return Err((
                        anon_key,
                        callee_path.clone(),
                        format!("return-certificate-return-shape:{callee_path}:external-call"),
                    ));
                };
                sources.calls.push((local, *span));
            }
            Returned::Null(span) => sources.nulls.push(*span),
            Returned::Other(span) => {
                let text = tcx
                    .sess
                    .source_map()
                    .span_to_snippet(*span)
                    .unwrap_or_default();
                let key = sources
                    .owner
                    .as_ref()
                    .map_or(anon_key, |(h, _)| (callee, *h));
                let label = subject_of(key.0, key.1)
                    .map(|s| s.label.clone())
                    .unwrap_or_else(|| callee_path.clone());
                return Err((
                    key,
                    label,
                    format!("return-certificate-return-shape:{callee_path}:{text}"),
                ));
            }
        }
    }
    let owner_subject = match &sources.owner {
        Some((hir, _)) => match subject_of(callee, *hir) {
            Some(s) => Some(s),
            None => {
                return Err((
                    (callee, *hir),
                    callee_path.clone(),
                    format!("return-certificate-return-locals:{callee_path}:not-a-subject"),
                ));
            }
        },
        None => None,
    };
    if owner_subject.is_none() && sources.calls.is_empty() {
        return Err((
            anon_key,
            callee_path.clone(),
            format!("return-certificate-return-shape:{callee_path}:no-source"),
        ));
    }
    let key = owner_subject.map_or(anon_key, |s| (s.fn_did, s.hir_id));
    let label = owner_subject.map_or_else(|| callee_path.clone(), |s| s.label.clone());
    let hold = |reason: String| -> Hold { (key, label.clone(), reason) };
    if fn_values.contains(&callee.to_def_id()) {
        return Err(hold(format!(
            "return-certificate-indirect-callers:{callee_path}"
        )));
    }
    // Every returned call's target must be certified (pending otherwise).
    let mut chained_from: Vec<LocalDefId> = Vec::new();
    for (target, _) in &sources.calls {
        if !done.callees.contains_key(target) {
            return Ok(None);
        }
        if !chained_from.contains(target) {
            chained_from.push(*target);
        }
    }
    // 2. The owner local's plan (an allocation, or a receiver of a certified
    // callee), if there is one.
    let mut plans: Vec<((LocalDefId, HirId), BoxPlan)> = Vec::new();
    let mut transfers: Vec<(DefId, usize, (LocalDefId, HirId))> = Vec::new();
    let mut owner_shape: Option<(BoxShape, bool)> = None;
    let mut owner_plan_optional = false;
    let mut source_receipt = String::from("calls");
    let mut kind: Option<SlotKind> = None;
    let mut dead_guard_receipts: Vec<String> = Vec::new();
    let mut null_returns = sources.nulls.clone();
    let mut pointee_ty: Option<rustc_middle::ty::Ty<'tcx>> = None;
    if let Some(subject) = owner_subject {
        let name = subject.param_name.clone().unwrap_or_else(|| "?".to_owned());
        let Some(slot) = slot_of(subject) else {
            return Err(hold(format!(
                "return-certificate-allocation:{callee_path}:no-slot"
            )));
        };
        kind = model.get(&slot).copied();
        let construction = constructions.by_binding.get(&key);
        let body = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
        let return_slot = slots
            .fn_local_slots
            .get(&callee)
            .and_then(|u| u.slot_for_local_depth(rustc_middle::mir::RETURN_PLACE, 0))
            .map(|s| SlotRef::Local(callee, s));
        let ty = match body.local_decls[subject.local].ty.kind() {
            TyKind::RawPtr(p, _) => *p,
            _ => {
                return Err(hold(
                    "return-certificate-allocation:not-a-pointer".to_owned(),
                ));
            }
        };
        pointee_ty = Some(ty);
        let pointee = pointee_source(tcx, ty);
        let frees: Vec<(Span, Span)> = scan
            .frees
            .iter()
            .filter(|(hir, _, _)| *hir == subject.hir_id)
            .map(|(_, call, arg)| (*call, *arg))
            .collect();
        let (mut plan, receipt): (BoxPlan, String) = match construction {
            Some(Construction::CallResult) => match constructions.call_result_targets.get(&key) {
                Some(CallResultTarget::DirectLocal(source)) => match done.callees.get(source) {
                    Some(source_certificate) => {
                        if !chained_from.contains(source) {
                            chained_from.push(*source);
                        }
                        let (plan, owner_transfers) = receiver_plan(
                            tcx,
                            subject,
                            source_certificate,
                            &frees,
                            &[],
                            None,
                            lend_ok,
                            transfer_ok,
                            &format!(
                                "return-certificate-chained source={}",
                                source_certificate.callee_path
                            ),
                        )
                        .map_err(|reason| hold(reason))?;
                        transfers.extend(owner_transfers.into_iter().map(|(d, i, _)| (d, i, key)));
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
            Some(Construction::NullLit)
                if scan
                    .assign_calls
                    .iter()
                    .any(|(hir, _, _, _)| *hir == subject.hir_id) =>
            {
                // An assignment receiver returned by its own function:
                // `let mut node = null; node = callee(..); ..; return node`.
                let assignments: Vec<(LocalDefId, Span, Span)> = scan
                    .assign_calls
                    .iter()
                    .filter(|(hir, _, _, _)| *hir == subject.hir_id)
                    .filter_map(|(_, did, span, stmt)| did.as_local().map(|d| (d, *span, *stmt)))
                    .collect();
                let overwrites = scan
                    .assigns
                    .iter()
                    .filter(|(hir, _)| *hir == subject.hir_id)
                    .count();
                if assignments.len() != overwrites || assignments.is_empty() {
                    return Err(hold(format!(
                        "return-certificate-allocation:{callee_path}:assignment-shape"
                    )));
                }
                let source = assignments[0].0;
                if assignments.iter().any(|(d, _, _)| *d != source) {
                    return Err(hold(format!(
                        "return-certificate-allocation:{callee_path}:assignment-sources"
                    )));
                }
                let Some(source_certificate) = done.callees.get(&source) else {
                    return Ok(None);
                };
                if !chained_from.contains(&source) {
                    chained_from.push(source);
                }
                let (plan, owner_transfers) = receiver_plan(
                    tcx,
                    subject,
                    source_certificate,
                    &frees,
                    &assignments
                        .iter()
                        .map(|(_, s, st)| (*s, *st))
                        .collect::<Vec<_>>(),
                    constructions.init_spans.get(&key).copied(),
                    lend_ok,
                    transfer_ok,
                    &format!(
                        "return-certificate-chained-assignment source={}",
                        source_certificate.callee_path
                    ),
                )
                .map_err(|reason| hold(reason))?;
                transfers.extend(owner_transfers.into_iter().map(|(d, i, _)| (d, i, key)));
                (
                    plan,
                    format!("assigned-from={}", source_certificate.callee_path),
                )
            }
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
                        let initializer = struct_initializer(tcx, ty)
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
                        match (construction, overwrites) {
                            (
                                Some(Construction::Alloc {
                                    callee: alloc,
                                    count: None,
                                    ..
                                }),
                                [],
                            ) if alloc == "malloc" => {
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
                                optional: false,
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
                    // from source with ownership/fields' constructor rule.
                    Err(BoxPlanFailure::EndpointInactive)
                        if matches!(construction, Some(Construction::Alloc { .. }))
                            && constructions
                                .owner_overwrites
                                .get(&key)
                                .is_none_or(Vec::is_empty) =>
                    {
                        let init_hir = *constructions.init_hirs.get(&key).ok_or_else(|| {
                            hold("return-certificate-allocation:no-init".to_owned())
                        })?;
                        let init = tcx.hir_node(init_hir).expect_expr();
                        let constructor = super::ownership_fields_constructor::derive(
                            tcx, callee, init, ty,
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
        // The model: Owning admits; Raw admits under the source certificate
        // (R410-5 §1); Ref never for an allocation (a borrowed local is not
        // one) — a chained receiver's Ref is superseded like any receiver's.
        if kind == Some(SlotKind::Ref)
            && !matches!(
                construction,
                Some(Construction::CallResult | Construction::NullLit)
            )
        {
            return Err(hold(format!(
                "return-certificate-allocation-model:{callee_path}:ref"
            )));
        }
        if plan.pointee_override.is_some() {
            return Err(hold(format!(
                "return-certificate-allocation:{callee_path}:pointee-override"
            )));
        }
        let allocation = !matches!(
            construction,
            Some(Construction::CallResult | Construction::NullLit)
        ) || matches!(
            receipt.as_str(),
            "struct-fill" | "constructor" | "ordinary-plan"
        );
        // The owner's uses (a receiver's were walked by `receiver_plan`).
        if allocation {
            let uses = owner_uses(
                tcx,
                subject,
                plan.shape,
                plan.optional,
                !plan.optional,
                &frees,
                lend_ok,
                transfer_ok,
                &|_| false,
            )
            .map_err(|form| hold(format!("return-certificate-owner-use:{callee_path}:{form}")))?;
            transfers.extend(uses.transfers.iter().map(|(d, i, _)| (*d, *i, key)));
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
            null_returns.retain(|span| !uses.dead_null_returns.contains(span));
            dead_guard_receipts.extend(uses.dead_guards.iter().map(|span| {
                format!(
                    "dead-alloc-guard site={}",
                    super::emitability::EmitabilityFacts::site(tcx, *span)
                )
            }));
        } else {
            // A receiver-owner: its dead guards were folded by `receiver_plan`
            // (receipts carried on the plan).
            for receipt in &plan.receipts {
                if let Some(site) = receipt.strip_prefix("dead-null-guard ") {
                    dead_guard_receipts.push(format!("dead-alloc-guard {site}"));
                }
            }
            null_returns.retain(|span| {
                !plan
                    .receipts
                    .iter()
                    .any(|r| r == &format!("dead-null-return {}", span.lo().0))
            });
        }
        plan.receipts
            .retain(|receipt| !receipt.starts_with("waiver-drop(scope-exit)"));
        plan.retained_sink = true;
        plan.implicit_scope_close = false;
        owner_plan_optional = plan.optional;
        owner_shape = Some((plan.shape, plan.optional));
        source_receipt = receipt;
        plans.push((key, plan));
    }
    // 3. One shape across the sources.
    let mut shapes: Vec<(BoxShape, bool)> = owner_shape.into_iter().collect();
    for (target, _) in &sources.calls {
        let c = &done.callees[target];
        shapes.push((c.shape, c.optional));
    }
    let shape = shapes[0].0;
    // R419-3 / R423-7 (relays wave-6a/011, /013): a fn-pointer-web member or
    // positive seed keeps a raw outer surface (the exposure family's
    // wrapper). The wrapper carries a SIZED owning return across the C ABI
    // (`Box::into_raw(__crat_safe_f(..))`, and the `match` arm for the
    // nullable twin) and every in-crate receiver binds to the safe inner
    // name; a `Box<[T]>` return would lose its extent at the raw surface, so
    // that certificate still holds whole.
    if shape == BoxShape::Slice && raw_surface(callee) {
        return Err(hold(format!("chain-endpoint-raw:{callee_path}:slice")));
    }
    if shapes.iter().any(|(s, _)| *s != shape) {
        return Err(hold(format!(
            "return-certificate-shape:{callee_path}:sources-disagree"
        )));
    }
    let optional_output = !null_returns.is_empty() || shapes.iter().any(|(_, o)| *o);
    // Return edits: null → None; a non-optional source into an optional
    // output → Some(..).
    let mut return_edits: Vec<BoxExprEdit> = Vec::new();
    for span in &null_returns {
        return_edits.push(BoxExprEdit {
            span: *span,
            replacement: "None".to_owned(),
            receipt: "return-certificate-null-return",
        });
    }
    if optional_output
        && !owner_plan_optional
        && let Some((_, spans)) = &sources.owner
        && let Some(subject) = owner_subject
    {
        let name = subject.param_name.clone().unwrap_or_else(|| "?".to_owned());
        for span in spans {
            return_edits.push(BoxExprEdit {
                span: *span,
                replacement: format!("Some({name})"),
                receipt: "return-certificate-some-return",
            });
        }
    }
    for (target, span) in &sources.calls {
        if optional_output && !done.callees[target].optional {
            let text = tcx
                .sess
                .source_map()
                .span_to_snippet(*span)
                .unwrap_or_default();
            return_edits.push(BoxExprEdit {
                span: *span,
                replacement: format!("Some({text})"),
                receipt: "return-certificate-some-return",
            });
        }
    }
    // Where the owner has a plan the return edits ride it; otherwise they
    // are site edits of the callee itself.
    let mut site_edits: Vec<(LocalDefId, BoxExprEdit)> = Vec::new();
    if let Some((_, plan)) = plans.first_mut() {
        plan.expr_edits.extend(return_edits);
    } else {
        site_edits.extend(return_edits.into_iter().map(|e| (callee, e)));
    }
    // 4. The output type, source-spelled.
    let Some(decl) = tcx.hir_node_by_def_id(callee).fn_decl() else {
        return Err(hold("return-certificate-allocation:no-decl".to_owned()));
    };
    let rustc_hir::FnRetTy::Return(output_ty) = decl.output else {
        return Err(hold("return-certificate-allocation:no-output".to_owned()));
    };
    let pointee = match (output_ty.kind, pointee_ty) {
        (rustc_hir::TyKind::Ptr(p), _) => tcx
            .sess
            .source_map()
            .span_to_snippet(p.ty.span)
            .unwrap_or_else(|_| "_".to_owned()),
        (_, Some(ty)) => pointee_source(tcx, ty),
        _ => "_".to_owned(),
    };
    let base = match shape {
        BoxShape::Sized => format!("Box<{pointee}>"),
        BoxShape::Slice => format!("Box<[{pointee}]>"),
    };
    let output_type = if optional_output {
        format!("Option<{base}>")
    } else {
        base
    };
    // 5. Receivers: `let r = callee(..)` (the construction facts) and
    // `r = callee(..)` assignment receivers (null-initialized locals whose
    // every overwrite is a call of this callee).
    let mut planned_receivers = Vec::new();
    let mut returned_receivers = Vec::new();
    let mut receiver_labels: Vec<String> = Vec::new();
    let mut certificate_stub = Certificate {
        callee,
        callee_path: callee_path.clone(),
        pointee: pointee.clone(),
        optional: optional_output,
        shape,
        output_type: output_type.clone(),
        output_span: output_ty.span,
        returned: owner_subject.map(|s| (s.fn_did, s.hir_id)),
        receivers: Vec::new(),
        returned_receivers: Vec::new(),
        returning_callers: Vec::new(),
        chained_from: chained_from.clone(),
        site_edits: Vec::new(),
        transfers: Vec::new(),
        receipts: Vec::new(),
    };
    let let_receivers = receivers_of.get(&callee).map(Vec::as_slice).unwrap_or(&[]);
    let mut assignment_receivers: Vec<(&Subject, Vec<(Span, Span)>)> = Vec::new();
    for s in subjects {
        if s.kind != SubjectKind::Local {
            continue;
        }
        let rkey = (s.fn_did, s.hir_id);
        if !matches!(
            constructions.by_binding.get(&rkey),
            Some(Construction::NullLit)
        ) {
            continue;
        }
        let Some(rscan) = scans.get(&s.fn_did) else { continue };
        let values: Vec<(Span, Span)> = rscan
            .assign_calls
            .iter()
            .filter(|(hir, did, _, _)| *hir == s.hir_id && *did == callee.to_def_id())
            .map(|(_, _, span, stmt)| (*span, *stmt))
            .collect();
        if values.is_empty() {
            continue;
        }
        let overwrites = rscan
            .assigns
            .iter()
            .filter(|(hir, _)| *hir == s.hir_id)
            .count();
        if overwrites != values.len() {
            return Err((
                rkey,
                s.label.clone(),
                format!(
                    "return-certificate-receiver-use:mixed-assignments:{}",
                    s.label
                ),
            ));
        }
        assignment_receivers.push((s, values));
    }
    let mut all_receivers: Vec<(&Subject, Vec<(Span, Span)>)> =
        let_receivers.iter().map(|s| (*s, Vec::new())).collect();
    all_receivers.extend(assignment_receivers);
    for (receiver, assignments) in &all_receivers {
        let rkey = (receiver.fn_did, receiver.hir_id);
        let rscan = scans.get(&receiver.fn_did).expect("scanned");
        let rfrees: Vec<(Span, Span)> = rscan
            .frees
            .iter()
            .filter(|(hir, _, _)| *hir == receiver.hir_id)
            .map(|(_, call, arg)| (*call, *arg))
            .collect();
        let rkind = slot_of(receiver).and_then(|s| model.get(&s).copied());
        let returned_here = rscan
            .returns
            .iter()
            .any(|r| matches!(r, Returned::Local(h, _) if *h == receiver.hir_id));
        if returned_here {
            returned_receivers.push(rkey);
            continue;
        }
        let (rplan, rtransfers) = receiver_plan(
            tcx,
            receiver,
            &certificate_stub,
            &rfrees,
            assignments,
            constructions.init_spans.get(&rkey).copied(),
            lend_ok,
            transfer_ok,
            &format!("return-certificate-receiver callee={callee_path} model={rkind:?}"),
        )
        .map_err(|reason| (rkey, receiver.label.clone(), reason))?;
        transfers.extend(rtransfers.into_iter().map(|(d, i, _)| (d, i, rkey)));
        plans.push((rkey, rplan));
        planned_receivers.push(rkey);
        receiver_labels.push(receiver.label.clone());
    }
    // 6. Every call of the callee is accounted for: a receiver's initializer
    // or assignment, a `return callee(..)` in a function that certifies
    // itself, or a store straight into a raw place (a site edit).
    let mut admitted_calls: Vec<Span> = planned_receivers
        .iter()
        .chain(&returned_receivers)
        .filter_map(|rkey| constructions.init_spans.get(rkey).copied())
        .collect();
    admitted_calls.extend(
        all_receivers
            .iter()
            .flat_map(|(_, a)| a.iter().map(|(v, _)| *v)),
    );
    let mut returning_callers: Vec<LocalDefId> = Vec::new();
    for (caller, caller_scan) in scans {
        for r in &caller_scan.returns {
            if let Returned::Call(target, span) = r
                && *target == callee.to_def_id()
            {
                admitted_calls.push(*span);
                if !returning_callers.contains(caller) {
                    returning_callers.push(*caller);
                }
            }
        }
        for (target, span) in &caller_scan.store_calls {
            if *target != callee.to_def_id() {
                continue;
            }
            let text = tcx
                .sess
                .source_map()
                .span_to_snippet(*span)
                .unwrap_or_default();
            let replacement = if optional_output {
                format!("{text}.map_or(core::ptr::null_mut(), Box::into_raw)")
            } else {
                format!("Box::into_raw({text})")
            };
            site_edits.push((
                *caller,
                BoxExprEdit {
                    span: *span,
                    replacement,
                    receipt: "return-certificate-store-transfer",
                },
            ));
            admitted_calls.push(*span);
        }
    }
    for (caller, caller_scan) in scans {
        for (target, call_span) in &caller_scan.calls {
            if *target != callee.to_def_id() {
                continue;
            }
            if !admitted_calls.iter().any(|init| init.contains(*call_span)) {
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
    if planned_receivers.is_empty()
        && returned_receivers.is_empty()
        && returning_callers.is_empty()
        && site_edits.iter().all(|(f, _)| *f == callee)
    {
        // R427-4: an EXPORTED producer whose pointee's surface closes has a
        // receiver — the exposure family's wrapper, which hands the owner out
        // as `Box::into_raw(__crat_safe_f(..))` (report 010's arm). Every
        // other pointee keeps the hold: without a receiver and without the
        // closure the return would convert with nothing to receive it.
        let output_pointee = tcx
            .fn_sig(callee.to_def_id())
            .skip_binder()
            .skip_binder()
            .output();
        let closed = matches!(output_pointee.kind(), TyKind::RawPtr(pointee, _)
            if exported_pairs.closes(tcx, *pointee));
        if !closed {
            return Err(hold(format!(
                "return-certificate-no-receivers:{callee_path}"
            )));
        }
        certificate_stub
            .receipts
            .push(format!("exported-pair-closure callee={callee_path}"));
    }
    let mut certificate = certificate_stub;
    certificate.receivers = planned_receivers;
    certificate.returned_receivers = returned_receivers;
    certificate.returning_callers = returning_callers;
    certificate.site_edits = site_edits;
    certificate.transfers = transfers;
    certificate.receipts.extend(dead_guard_receipts);
    // **The leak-parity waiver's receipt on the CALLEE side** (addendum 101).
    // A LIVE null return abandons the generation the owner is still holding:
    // the input leaks it, and the emitted `None` arm closes it at scope exit.
    // The callee's plan asserts `retained_sink` because the certificate's
    // return is a sink, which is true of every path that returns the owner
    // and of no path that returns null — so the site is receipted here, where
    // the live null returns are known (a dead null return, the one before the
    // allocation, is already out of this set).
    for span in &null_returns {
        certificate.receipts.push(format!(
            "waiver-drop(scope-exit) site={}",
            super::emitability::EmitabilityFacts::site(tcx, *span)
        ));
    }
    certificate.receipts.push(format!(
        "return-certificate callee={callee_path} output={output_type} source={source_receipt} model={kind:?} null_returns={} receivers={} [{}] returned_receivers={} returning_callers={} store_sites={}",
        null_returns.len(),
        certificate.receivers.len(),
        receiver_labels.join(","),
        certificate.returned_receivers.len(),
        certificate.returning_callers.len(),
        certificate.site_edits.len()
    ));
    Ok(Some((certificate, plans)))
}

/// A receiver's plan: the callee's shape and optionality, its uses rewritten,
/// its C free a `drop`, a store a `Box::into_raw` transfer. An assignment
/// receiver (`let r = null; r = callee(..)`) is `Option<Box<..>>` from `None`,
/// each assignment wrapped `Some(..)` when the callee's output is not
/// optional. A `let` receiver of a non-optional callee can never be null: its
/// null guard is dead (folded like the allocation's, receipted).
fn receiver_plan(
    tcx: TyCtxt<'_>,
    receiver: &Subject,
    certificate: &Certificate,
    frees: &[(Span, Span)],
    assignments: &[(Span, Span)],
    init_span: Option<Span>,
    lend_ok: &dyn Fn(DefId, usize) -> bool,
    transfer_ok: &dyn Fn(DefId, usize) -> bool,
    receipt: &str,
) -> Result<(BoxPlan, Vec<(DefId, usize, Span)>), String> {
    let name = receiver
        .param_name
        .clone()
        .unwrap_or_else(|| "?".to_owned());
    // An assignment receiver of a non-optional callee whose ONE assignment is
    // the binding's first use folds: `let r: Box<T> = callee(..)` with the
    // assignment statement gone (the null init is never read). Otherwise it
    // is `Option<Box<T>>` from `None`.
    let folded = match assignments {
        [(_, statement)] if !certificate.optional => {
            first_use_is(tcx, receiver, *statement).is_some()
        }
        _ => false,
    };
    let optional = certificate.optional || (!assignments.is_empty() && !folded);
    let never_null = !optional;
    let uses = owner_uses(
        tcx,
        receiver,
        certificate.shape,
        optional,
        never_null,
        frees,
        lend_ok,
        transfer_ok,
        &|_| false,
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
    let mut receipts = vec![receipt.to_owned()];
    let mut delete_statements = Vec::new();
    if folded {
        let Some(init_span) = init_span else {
            return Err("return-certificate-receiver-use:assignment-init".to_owned());
        };
        let (value, statement) = assignments[0];
        let text = tcx
            .sess
            .source_map()
            .span_to_snippet(value)
            .unwrap_or_default();
        expr_edits.push(BoxExprEdit {
            span: init_span,
            replacement: text,
            receipt: "return-certificate-folded-assignment",
        });
        delete_statements.push(statement);
        receipts.push("assignment-receiver folded".to_owned());
    } else if !assignments.is_empty() {
        let Some(init_span) = init_span else {
            return Err("return-certificate-receiver-use:assignment-init".to_owned());
        };
        expr_edits.push(BoxExprEdit {
            span: init_span,
            replacement: "None".to_owned(),
            receipt: "return-certificate-null-init",
        });
        if !certificate.optional {
            for (span, _) in assignments {
                let text = tcx
                    .sess
                    .source_map()
                    .span_to_snippet(*span)
                    .unwrap_or_default();
                expr_edits.push(BoxExprEdit {
                    span: *span,
                    replacement: format!("Some({text})"),
                    receipt: "return-certificate-some-assignment",
                });
            }
        }
        receipts.push(format!(
            "assignment-receiver assignments={}",
            assignments.len()
        ));
    }
    for span in &uses.dead_guards {
        receipts.push(format!(
            "dead-null-guard site={}",
            super::emitability::EmitabilityFacts::site(tcx, *span)
        ));
    }
    for span in &uses.dead_null_returns {
        receipts.push(format!("dead-null-return {}", span.lo().0));
    }
    let retained_sink = !frees.is_empty() || !uses.stores.is_empty() || !uses.transfers.is_empty();
    if !retained_sink {
        receipts.push("waiver-drop(scope-exit)".to_owned());
    }
    // An edit inside a deleted statement goes with it.
    expr_edits.retain(|e| !delete_statements.iter().any(|d| d.contains(e.span)));
    let transfers = uses.transfers.clone();
    Ok((
        BoxPlan {
            shape: certificate.shape,
            optional,
            expr_edits,
            delete_statements,
            receipts,
            fabricated_extent: false,
            pointee_override: None,
            inferred_binding: receiver.ty_span.is_none(),
            overwrite_spans: Vec::new(),
            retained_sink,
            implicit_scope_close: !retained_sink,
        },
        transfers,
    ))
}
