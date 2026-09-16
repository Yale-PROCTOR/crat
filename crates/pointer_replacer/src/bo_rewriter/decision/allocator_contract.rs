//! wave-6a: **the allocator-contract consumer** (relay wave-6a/006, USER
//! DECISION seat addendum 409, R409-1/3).
//!
//! brotli's `alloc_func` / `free_func` pair is malloc/free-like — the pinned
//! contract `allocator-contract:brotli-memory-manager/v1@2026-09-15`:
//! `BrotliAllocate(m, size)` returns a fresh owned allocation of `size`
//! bytes, non-null after brotli's `exit(1)` guard; released exactly once
//! through `BrotliFree(m, p)`. era-5c builds the analysis root behind a pin
//! (the ≈ 60 brotli allocation locals become Owning when L01⁗ lands); this
//! consumer plans the rows now, on the contract's evidence, exactly as the
//! allocation-return certificate plans its receivers on the source proof
//! (R410-5 §1: the certificate supersedes the model's Raw).
//!
//! **Emission rule (R409-3), binding on every consumer.** A contract-rooted
//! allocation local emits `Box<T>` / `Box<[T]>` — the count read from the
//! size expression exactly as W6A-B1's sealed-constructor typing reads it
//! (`n.wrapping_mul(size_of::<T>())` → `n`; `size_of::<T>()` → sized) —
//! constructed FROM the contract allocator's result (`Box::from_raw(..)`:
//! the memory manager's accounting stays the program's), and its C free
//! site `BrotliFree(m, x as *mut c_void)` emitted as
//! `BrotliFree(m, Box::into_raw(x) as *mut c_void)` — the source-proved
//! deallocator transfer of batch 6 with the custom deallocator as the sink.
//! **NO implicit close**: addendum 101's `waiver-drop(scope-exit | overwrite
//! | unwind)` does NOT extend to contract allocations (Rust's global
//! allocator dropping memory of a custom `free_func` is UB). A path on which
//! the owner is neither freed, transferred nor stored — a `return` between
//! the allocation and its free, a free inside a branch of the allocating
//! block, no free at all — is the typed hold
//! `contract-allocation:implicit-close`; an overwrite of a live owner
//! likewise (`contract-allocation:overwrite`); the `BROTLI_FREE` null store
//! right after the free (`x = 0 as *mut T`) is `x = None` / deleted. The
//! conditional allocation `if n > 0 { BrotliAllocate(..) } else { null }`
//! is `Option<Box<[T]>>` with `None` on the else arm.
//!
//! Uses are the certificate's receiver walk (`return_certificate::owner_uses`):
//! element accesses (`x[i]`, through `as_deref[_mut]().unwrap()` for an
//! optional owner), derefs, null tests, stores into raw places
//! (`Box::into_raw`), lends to Ref-modeled local formals read from the
//! callee's body and to libc positions the contract table calls `NoRetain`
//! + `BorrowView` (`memset`, `memcpy`, ..) — the optional owner's lend is
//! the R130 void bridge `x.as_deref_mut().map_or(null_mut(), |s|
//! s.as_mut_ptr())`. A `return x` of the owner holds
//! (`contract-allocation:returned`: the return interface is A1's, and a
//! contract allocation must not be closed by a receiver's drop).
//!
//! Receipt `allocator-contract` per site (the receipts table).

use rustc_hash::FxHashMap;
use rustc_hir::{
    Expr, ExprKind, HirId, QPath,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{
    Ctx, Decision, DecisionTable, DegradeReason, Subject, SubjectKind,
    box_facts::{BoxExprEdit, BoxPlan, BoxPlanFailure, BoxShape},
    declaration::pointee_source,
    return_certificate::{LendOracle, owner_uses},
    seam::ExplicitDeclarationSite,
};
use crate::{
    analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef},
    bo_rewriter::bridge_receipt::SignatureClassId,
};

/// One pinned allocator contract.
pub(crate) struct Contract {
    pub(crate) id: &'static str,
    /// The allocator's item name and the index of its size argument.
    pub(crate) allocate: &'static str,
    pub(crate) size_index: usize,
    /// The deallocator's item name and the index of its pointer argument.
    pub(crate) free: &'static str,
    pub(crate) pointer_index: usize,
}

/// The contract table (USER DECISION, seat addendum 409).
pub(crate) const CONTRACTS: &[Contract] = &[Contract {
    id: "allocator-contract:brotli-memory-manager/v1@2026-09-15",
    allocate: "BrotliAllocate",
    size_index: 1,
    free: "BrotliFree",
    pointer_index: 1,
}];

const IMPLICIT_CLOSE: &str = "contract-allocation:implicit-close";
const OVERWRITE: &str = "contract-allocation:overwrite";
const RETURNED: &str = "contract-allocation:returned";
const COUNT: &str = "contract-allocation:count";
const LEND_GLUE: &str = "contract-allocation:lend-glue";
const USE: &str = "contract-allocation:use";

fn typed_key(hold: &str) -> &'static str {
    [IMPLICIT_CLOSE, OVERWRITE, RETURNED, COUNT, LEND_GLUE, USE]
        .into_iter()
        .find(|key| hold.starts_with(key))
        .unwrap_or(USE)
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Plans {
    /// Every subject the consumer plans: (function, binding) → plan.
    pub(crate) plans: FxHashMap<(LocalDefId, HirId), BoxPlan>,
    /// Refusals: binding → (label, typed reason).
    pub(crate) holds: FxHashMap<(LocalDefId, HirId), (String, String)>,
    /// Admitted rows: (label, receipt).
    pub(crate) admitted: Vec<(String, String)>,
}

impl Plans {
    pub(crate) fn receipts_tsv(&self) -> String {
        let mut out = String::from("subject\tkind\tdetail\n");
        let mut admitted = self.admitted.clone();
        admitted.sort();
        for (label, receipt) in admitted {
            out.push_str(&format!("{label}\tadmitted\t{receipt}\n"));
        }
        let mut holds: Vec<&(String, String)> = self.holds.values().collect();
        holds.sort();
        for (label, hold) in holds {
            out.push_str(&format!("{label}\theld\t{hold}\n"));
        }
        out
    }
}

/// Decision-phase hook, before the model's verdict is applied: a subject the
/// consumer plans is a Box on the contract's evidence; a subject it refused
/// carries the typed hold.
pub(crate) fn planned(ctx: &Ctx<'_, '_>, subject: &Subject, site: &str) -> Option<Decision> {
    let node = (subject.fn_did, subject.hir_id);
    if let Some(plan) = ctx.allocator_contracts.plans.get(&node) {
        return Some(Decision::Box(plan.clone()));
    }
    let (_, hold) = ctx.allocator_contracts.holds.get(&node)?;
    Some(Decision::Degraded(super::Degradation {
        subject: subject.label.clone(),
        site: site.to_owned(),
        reason: DegradeReason::BoxFailure {
            failure: BoxPlanFailure::NativeEvidenceHeld {
                prior_key: typed_key(hold),
                detail: hold.clone(),
            },
        },
    }))
}

/// After the decisions: the planned locals get their `Box<..>` spelled out
/// (the custody instrument reads only explicit types).
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
        if !table.allocator_contracts.plans.contains_key(&node) || subject.ty_span.is_some() {
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

fn callee_of(e: &Expr<'_>) -> Option<DefId> {
    let ExprKind::Call(callee, _) = &e.kind else { return None };
    let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind else { return None };
    match path.res {
        Res::Def(DefKind::Fn, did) => Some(did),
        _ => None,
    }
}

/// The contract a callee belongs to, by item name (the pinned symbol).
fn contract_of(tcx: TyCtxt<'_>, did: DefId) -> Option<(&'static Contract, bool)> {
    let name = tcx.item_name(did);
    CONTRACTS.iter().find_map(|c| {
        if name.as_str() == c.allocate {
            Some((c, true))
        } else if name.as_str() == c.free {
            Some((c, false))
        } else {
            None
        }
    })
}

/// The count of a contract allocation from its size argument: `n *
/// size_of::<T>()` (either order, through casts) → `Slice` with count `n`;
/// `size_of::<T>()` alone → `Sized`.
fn shape_of(tcx: TyCtxt<'_>, size: &Expr<'_>) -> Result<(BoxShape, Option<String>), String> {
    fn is_size_of(e: &Expr<'_>) -> bool {
        let e = peel_casts(e);
        let ExprKind::Call(callee, args) = &e.kind else { return false };
        args.is_empty()
            && matches!(
                &callee.kind,
                ExprKind::Path(QPath::Resolved(_, path))
                    if path.segments.last().is_some_and(|s| s.ident.name.as_str() == "size_of")
            )
    }
    let snippet = |span: Span| {
        tcx.sess
            .source_map()
            .span_to_snippet(span)
            .unwrap_or_default()
    };
    let size = peel_casts(size);
    if is_size_of(size) {
        return Ok((BoxShape::Sized, None));
    }
    if let ExprKind::MethodCall(seg, recv, [arg], _) = &size.kind
        && seg.ident.name.as_str() == "wrapping_mul"
    {
        if is_size_of(arg) {
            return Ok((BoxShape::Slice, Some(snippet(recv.span))));
        }
        if is_size_of(recv) {
            return Ok((BoxShape::Slice, Some(snippet(arg.span))));
        }
    }
    if let ExprKind::Binary(op, lhs, rhs) = &size.kind
        && op.node == rustc_hir::BinOpKind::Mul
    {
        if is_size_of(rhs) {
            return Ok((BoxShape::Slice, Some(snippet(lhs.span))));
        }
        if is_size_of(lhs) {
            return Ok((BoxShape::Slice, Some(snippet(rhs.span))));
        }
    }
    Err(format!("{COUNT}:{}", snippet(size.span)))
}

/// A contract allocation expression: `<Allocate>(m, size) as *mut T` (the
/// outermost cast, if any, is the binding's type).
struct Allocation {
    contract: &'static Contract,
    /// The whole cast chain over the call (what the `Box::from_raw` wraps).
    span: Span,
    shape: BoxShape,
    count: Option<String>,
}

fn allocation<'h>(tcx: TyCtxt<'_>, e: &'h Expr<'h>) -> Option<Result<Allocation, String>> {
    let call = peel_casts(e);
    let did = callee_of(call)?;
    let (contract, is_alloc) = contract_of(tcx, did)?;
    if !is_alloc {
        return None;
    }
    let ExprKind::Call(_, args) = &call.kind else { return None };
    let size = args.get(contract.size_index)?;
    Some(shape_of(tcx, size).map(|(shape, count)| Allocation {
        contract,
        span: e.span,
        shape,
        count,
    }))
}

/// A statement of a block that concerns a contract owner.
#[derive(Clone, Copy)]
enum Role {
    /// `let x = <allocation>` / `let x = if c { <allocation> } else { null }`.
    Let,
    /// `<Free>(m, x as *mut c_void);`
    Free,
    /// `x = <null>;`
    NullStore,
    /// Any other assignment to the binding.
    Store,
}

#[derive(Default)]
struct Scan {
    /// (binding, block, statement index, role, statement span).
    statements: Vec<(HirId, HirId, usize, Role, Span)>,
    /// Every `return` in the body.
    returns: Vec<Span>,
    /// `<Free>(m, x)` calls: (binding, call span, argument span).
    frees: Vec<(HirId, Span, Span)>,
    /// Every assignment to a bare local: (binding, value span).
    assigns: Vec<(HirId, Span)>,
}

struct ScanWalk<'tcx> {
    tcx: TyCtxt<'tcx>,
    out: Scan,
}

impl<'tcx> Visitor<'tcx> for ScanWalk<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_block(&mut self, block: &'tcx rustc_hir::Block<'tcx>) {
        for (index, stmt) in block.stmts.iter().enumerate() {
            let role = match &stmt.kind {
                rustc_hir::StmtKind::Let(local) => local.init.and_then(|init| {
                    let rustc_hir::PatKind::Binding(_, hir, _, None) = local.pat.kind else {
                        return None;
                    };
                    let value = match &init.kind {
                        ExprKind::If(_, then, Some(_)) => match then.kind {
                            ExprKind::Block(b, _) => b.expr?,
                            _ => then,
                        },
                        _ => init,
                    };
                    allocation(self.tcx, value).map(|_| (hir, Role::Let))
                }),
                rustc_hir::StmtKind::Semi(e) | rustc_hir::StmtKind::Expr(e) => match &e.kind {
                    ExprKind::Call(_, args) => callee_of(e)
                        .and_then(|did| contract_of(self.tcx, did))
                        .filter(|(_, is_alloc)| !is_alloc)
                        .and_then(|(c, _)| {
                            let arg = args.get(c.pointer_index)?;
                            let hir = bare_local(arg)?;
                            self.out.frees.push((hir, e.span, arg.span));
                            Some((hir, Role::Free))
                        }),
                    ExprKind::Assign(lhs, rhs, _) => bare_local(lhs)
                        .filter(|_| matches!(lhs.kind, ExprKind::Path(_)))
                        .map(|hir| {
                            self.out.assigns.push((hir, rhs.span));
                            (
                                hir,
                                if null_literal(rhs) {
                                    Role::NullStore
                                } else {
                                    Role::Store
                                },
                            )
                        }),
                    _ => None,
                },
                rustc_hir::StmtKind::Item(_) => None,
            };
            if let Some((hir, role)) = role {
                self.out
                    .statements
                    .push((hir, block.hir_id, index, role, stmt.span));
            }
        }
        intravisit::walk_block(self, block);
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        match &e.kind {
            ExprKind::Ret(_) => self.out.returns.push(e.span),
            // An assignment outside statement position (`(x = ..)` as a
            // value) is a store too.
            ExprKind::Assign(lhs, rhs, _) if matches!(lhs.kind, ExprKind::Path(_)) => {
                if let Some(hir) = bare_local(lhs)
                    && !self
                        .out
                        .assigns
                        .iter()
                        .any(|(h, s)| *h == hir && *s == rhs.span)
                {
                    self.out.assigns.push((hir, rhs.span));
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }
}

/// Derive every contract-rooted owner plan for the crate.
pub(crate) fn derive<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    subjects: &[Subject],
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> Plans {
    let mut out = Plans::default();
    let lend_oracle = LendOracle::new(tcx, functions, slots, model);
    let lend_ok = |did: DefId, index: usize| -> bool { lend_oracle.lend(did, index) };
    let transfer_ok = |_: DefId, _: usize| -> bool { false };
    let snippet = |span: Span| {
        tcx.sess
            .source_map()
            .span_to_snippet(span)
            .unwrap_or_default()
    };
    for &function in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else { continue };
        let mut walk = ScanWalk {
            tcx,
            out: Scan::default(),
        };
        walk.visit_body(tcx.hir_body(body_id));
        let scan = walk.out;
        for subject in subjects
            .iter()
            .filter(|s| s.fn_did == function && s.kind == SubjectKind::Local)
        {
            let node = (subject.fn_did, subject.hir_id);
            let Some(&(_, block, let_index, _, let_span)) = scan
                .statements
                .iter()
                .find(|(hir, _, _, role, _)| *hir == subject.hir_id && matches!(role, Role::Let))
            else {
                continue;
            };
            let label = subject.label.clone();
            let hold = |out: &mut Plans, reason: String| {
                out.holds.insert(node, (label.clone(), reason));
            };
            // The initializer: the allocation, or the conditional allocation.
            let Some(local) = tcx.hir_node(subject.hir_id).parent_hir_node_let(tcx) else {
                continue;
            };
            let Some(init) = local.init else { continue };
            let (value, else_null) = match &init.kind {
                ExprKind::If(_, then, Some(otherwise)) => {
                    let value = match then.kind {
                        ExprKind::Block(b, _) => b.expr.unwrap_or(then),
                        _ => then,
                    };
                    let null = match otherwise.kind {
                        ExprKind::Block(b, _) => b.expr.filter(|e| null_literal(e)),
                        _ => None,
                    };
                    let Some(null) = null else {
                        hold(
                            &mut out,
                            format!("{USE}:conditional-else:{}", snippet(otherwise.span)),
                        );
                        continue;
                    };
                    (value, Some(null.span))
                }
                _ => (init, None),
            };
            let allocation = match allocation(tcx, value) {
                Some(Ok(a)) => a,
                Some(Err(reason)) => {
                    hold(&mut out, reason);
                    continue;
                }
                None => continue,
            };
            let optional = else_null.is_some();
            let name = subject.param_name.clone().unwrap_or_else(|| "?".to_owned());
            // The statements of the allocating block that concern the owner,
            // in order.
            let mut rows: Vec<(usize, Role, Span)> = scan
                .statements
                .iter()
                .filter(|(hir, b, _, _, _)| *hir == subject.hir_id && *b == block)
                .map(|(_, _, i, role, span)| (*i, *role, *span))
                .collect();
            rows.sort_by_key(|(i, _, _)| *i);
            let frees: Vec<(Span, Span)> = scan
                .frees
                .iter()
                .filter(|(hir, _, _)| *hir == subject.hir_id)
                .map(|(_, call, arg)| (*call, *arg))
                .collect();
            let block_frees: Vec<(usize, Span)> = rows
                .iter()
                .filter(|(_, role, _)| matches!(role, Role::Free))
                .map(|(i, _, span)| (*i, *span))
                .collect();
            // The uses (the certificate's receiver walk).
            let uses = match owner_uses(
                tcx,
                subject,
                allocation.shape,
                optional,
                !optional,
                &frees,
                &lend_ok,
                &transfer_ok,
            ) {
                Ok(uses) => uses,
                Err(form) => {
                    hold(&mut out, format!("{USE}:{form}"));
                    continue;
                }
            };
            if let Some(span) = uses.returns.first() {
                hold(&mut out, format!("{RETURNED}:{}", snippet(*span)));
                continue;
            }
            // A SLICE owner lent to a local callee: the seam's interface glue
            // reads a Box argument as raw (`form_of(Box) = Raw`) and wraps it
            // `from_raw_parts(x, n)` at a slice-converted formal — E0308 for
            // a `Box<[T]>` — and `&*x` at a thin formal is `&[T]`, not `&T`;
            // the owner-view glue (`&mut *x` / `x.as_deref_mut().unwrap()`)
            // is a seam arm the vocabulary does not have (STOP, report 008).
            // A sized owner rides A1's `&*x` at a thin formal.
            if allocation.shape == BoxShape::Slice
                && let Some((did, _, span)) = uses
                    .lends
                    .iter()
                    .find(|(did, _, _)| !super::return_certificate::foreign_fn(tcx, *did))
            {
                hold(
                    &mut out,
                    format!("{LEND_GLUE}:{}:{}", tcx.item_name(*did), snippet(*span)),
                );
                continue;
            }
            // The sinks: the block's own free (exactly one, after the `let`,
            // with no `return` between), or a store into a raw place.
            let sink_free = match block_frees.as_slice() {
                [(index, span)] if *index > let_index => Some((*index, *span)),
                [] => None,
                _ => {
                    hold(
                        &mut out,
                        format!("{IMPLICIT_CLOSE}:frees={}", block_frees.len()),
                    );
                    continue;
                }
            };
            if frees.len() != block_frees.len() {
                // A free inside a branch of the allocating block: the other
                // arm keeps a live owner.
                hold(&mut out, format!("{IMPLICIT_CLOSE}:free-in-branch"));
                continue;
            }
            let live_end = match (sink_free, uses.stores.first()) {
                (Some((_, span)), _) => span,
                (None, Some(store)) => *store,
                (None, None) => {
                    hold(&mut out, format!("{IMPLICIT_CLOSE}:no-sink"));
                    continue;
                }
            };
            if let Some(ret) = scan
                .returns
                .iter()
                .find(|r| r.lo() > let_span.lo() && r.lo() < live_end.lo())
            {
                hold(
                    &mut out,
                    format!("{IMPLICIT_CLOSE}:return:{}", snippet(*ret)),
                );
                continue;
            }
            // Assignments: only the `BROTLI_FREE` null store right after the
            // free (the owner is moved by then); anything else overwrites a
            // live owner or re-seats a dead one.
            let mut expr_edits = uses.edits;
            let mut delete_statements = Vec::new();
            let mut overwrite = None;
            for (i, role, span) in &rows {
                match role {
                    Role::Let | Role::Free => {}
                    Role::NullStore
                        if sink_free.is_some_and(|(free_index, _)| *i == free_index + 1) =>
                    {
                        if optional {
                            let (_, value) = scan
                                .assigns
                                .iter()
                                .find(|(hir, v)| *hir == subject.hir_id && span.contains(*v))
                                .expect("the null store's value");
                            expr_edits.push(BoxExprEdit {
                                span: *value,
                                replacement: "None".to_owned(),
                                receipt: "allocator-contract-null-store",
                            });
                        } else {
                            delete_statements.push(*span);
                        }
                    }
                    Role::NullStore | Role::Store => {
                        overwrite = Some(*span);
                    }
                }
            }
            let block_assigns = rows
                .iter()
                .filter(|(_, role, _)| matches!(role, Role::NullStore | Role::Store))
                .count();
            let all_assigns = scan
                .assigns
                .iter()
                .filter(|(hir, _)| *hir == subject.hir_id)
                .count();
            if overwrite.is_none() && all_assigns != block_assigns {
                overwrite = scan
                    .assigns
                    .iter()
                    .find(|(hir, _)| *hir == subject.hir_id)
                    .map(|(_, v)| *v);
            }
            if let Some(span) = overwrite {
                hold(&mut out, format!("{OVERWRITE}:{}", snippet(span)));
                continue;
            }
            // The construction and the sink.
            let call_text = snippet(allocation.span);
            let boxed = match (&allocation.shape, &allocation.count) {
                (BoxShape::Sized, _) => format!("Box::from_raw({call_text})"),
                (BoxShape::Slice, Some(count)) => format!(
                    "Box::from_raw(core::ptr::slice_from_raw_parts_mut({call_text}, ({count}) as usize))"
                ),
                (BoxShape::Slice, None) => unreachable!("a slice shape carries its count"),
            };
            expr_edits.push(BoxExprEdit {
                span: allocation.span,
                replacement: if optional {
                    format!("Some({boxed})")
                } else {
                    boxed
                },
                receipt: "allocator-contract-construction",
            });
            if let Some(null) = else_null {
                expr_edits.push(BoxExprEdit {
                    span: null,
                    replacement: "None".to_owned(),
                    receipt: "allocator-contract-none-arm",
                });
            }
            for (_, arg) in &frees {
                let arg_text = snippet(*arg);
                let casts = arg_text
                    .strip_prefix(name.as_str())
                    .unwrap_or_default()
                    .to_owned();
                expr_edits.push(BoxExprEdit {
                    span: *arg,
                    replacement: if optional {
                        format!("{name}.map_or(core::ptr::null_mut(), |b| Box::into_raw(b){casts})")
                    } else {
                        format!("Box::into_raw({name}){casts}")
                    },
                    receipt: "allocator-contract-free-transfer",
                });
            }
            expr_edits.sort_by_key(|e| (e.span.lo(), e.span.hi()));
            expr_edits.retain(|e| !delete_statements.iter().any(|d| d.contains(e.span)));
            let mut receipts = vec![
                format!("allocator-contract {}", allocation.contract.id),
                format!(
                    "shape={} optional={optional} sink={}",
                    match allocation.shape {
                        BoxShape::Sized => "sized",
                        BoxShape::Slice => "slice",
                    },
                    if sink_free.is_some() { "free" } else { "store" }
                ),
            ];
            for (call, _) in &frees {
                receipts.push(format!(
                    "allocator-contract site={}",
                    super::emitability::EmitabilityFacts::site(tcx, *call)
                ));
            }
            for receipt in &receipts {
                out.admitted.push((label.clone(), receipt.clone()));
            }
            out.plans.insert(
                node,
                BoxPlan {
                    shape: allocation.shape,
                    optional,
                    expr_edits,
                    delete_statements,
                    receipts,
                    fabricated_extent: false,
                    pointee_override: None,
                    inferred_binding: subject.ty_span.is_none(),
                    overwrite_spans: Vec::new(),
                    retained_sink: true,
                    implicit_scope_close: false,
                },
            );
        }
    }
    out
}

/// The `let` statement a binding pattern belongs to.
trait ParentLet<'tcx> {
    fn parent_hir_node_let(&self, tcx: TyCtxt<'tcx>) -> Option<&'tcx rustc_hir::LetStmt<'tcx>>;
}

impl<'tcx> ParentLet<'tcx> for rustc_hir::Node<'tcx> {
    fn parent_hir_node_let(&self, tcx: TyCtxt<'tcx>) -> Option<&'tcx rustc_hir::LetStmt<'tcx>> {
        let rustc_hir::Node::Pat(pat) = self else { return None };
        match tcx.parent_hir_node(pat.hir_id) {
            rustc_hir::Node::LetStmt(local) => Some(local),
            _ => None,
        }
    }
}
