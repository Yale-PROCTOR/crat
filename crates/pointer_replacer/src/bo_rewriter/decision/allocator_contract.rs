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
//! s.as_mut_ptr())`; a lend to a LOCAL callee whose formal converts is the
//! seam's owner-view glue (`&*x` at a slice formal, R422-5). A `return x`
//! of the owner holds (`contract-allocation:returned`: the return interface
//! is A1's, and a contract allocation must not be closed by a receiver's
//! drop).
//!
//! Receipt `allocator-contract` per site (the receipts table).

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

/// How one allocator of a contract states the extent of the block it returns.
pub(crate) enum Extent {
    /// The argument at this index is a BYTE count: `malloc(n * size_of::<T>())`
    /// is `n` elements, `malloc(size_of::<T>())` is one.
    SizeArgument(usize),
    /// `calloc(n, size_of::<T>())`: the count is the first argument, and the
    /// second must be the pointee's own size.
    ElementCount {
        count_index: usize,
        size_index: usize,
    },
    /// `strdup(s)`: the block is the NUL-terminated copy of `s`, so its extent
    /// is a POSTCONDITION of the contract — `strlen + 1` — and is read off the
    /// RESULT, never off the argument (R434-4 §1). Reading the result keeps
    /// the count independent of whatever form another family gives `s`.
    NulTerminatedCopy,
}

/// One pinned allocator of a contract.
pub(crate) struct Allocator {
    pub(crate) name: &'static str,
    pub(crate) extent: Extent,
}

/// One pinned allocator contract: a set of allocators and the ONE deallocator
/// that releases what they return.
pub(crate) struct Contract {
    pub(crate) id: &'static str,
    pub(crate) allocators: &'static [Allocator],
    /// The deallocator's item name and the index of its pointer argument.
    pub(crate) free: &'static str,
    pub(crate) pointer_index: usize,
}

/// The contract table (USER DECISION, seat addendum 409; the libc row is
/// R434-4 §3). `realloc` is deliberately ABSENT: it releases one generation
/// and creates another in one call, which is neither of this table's two
/// events, so a local it touches keeps its typed hold.
pub(crate) const CONTRACTS: &[Contract] = &[
    Contract {
        id: "allocator-contract:brotli-memory-manager/v1@2026-09-15",
        allocators: &[Allocator {
            name: "BrotliAllocate",
            extent: Extent::SizeArgument(1),
        }],
        free: "BrotliFree",
        pointer_index: 1,
    },
    Contract {
        id: "allocator-contract:libc/v1@2026-09-17",
        allocators: &[
            Allocator {
                name: "malloc",
                extent: Extent::SizeArgument(0),
            },
            Allocator {
                name: "calloc",
                extent: Extent::ElementCount {
                    count_index: 0,
                    size_index: 1,
                },
            },
            Allocator {
                name: "strdup",
                extent: Extent::NulTerminatedCopy,
            },
        ],
        free: "free",
        pointer_index: 0,
    },
];

const IMPLICIT_CLOSE: &str = "contract-allocation:implicit-close";
const OVERWRITE: &str = "contract-allocation:overwrite";
const RETURNED: &str = "contract-allocation:returned";
const COUNT: &str = "contract-allocation:count";
const USE: &str = "contract-allocation:use";

fn typed_key(hold: &str) -> &'static str {
    [IMPLICIT_CLOSE, OVERWRITE, RETURNED, COUNT, USE]
        .into_iter()
        .find(|key| hold.starts_with(key))
        .unwrap_or(USE)
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Plans {
    /// Every subject the consumer plans: (function, binding) → plan.
    pub(crate) plans: FxHashMap<(LocalDefId, HirId), BoxPlan>,
    /// Refusals: binding → (label, typed reason). These DEGRADE the subject,
    /// so only a contract that owns its subjects records them.
    pub(crate) holds: FxHashMap<(LocalDefId, HirId), (String, String)>,
    /// The libc row's refusals. libc's allocators are the whole corpus's, not
    /// this rule's alone: a local it cannot claim belongs to whichever family
    /// does claim it, so the refusal is a RECEIPT and never a decision.
    pub(crate) yields: Vec<(String, String)>,
    /// Admitted rows: (label, receipt).
    pub(crate) admitted: Vec<(String, String)>,
}

impl Plans {
    pub(crate) fn receipts_tsv(&self) -> String {
        let mut out = String::from("subject\tkind\tdetail\n");
        let mut yielded = self.yields.clone();
        yielded.sort();
        for (label, reason) in yielded {
            out.push_str(&format!("{label}\tyielded\t{reason}\n"));
        }
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
fn contract_of(
    tcx: TyCtxt<'_>,
    did: DefId,
) -> Option<(&'static Contract, Option<&'static Allocator>)> {
    let name = tcx.item_name(did);
    CONTRACTS.iter().find_map(|c| {
        if let Some(allocator) = c.allocators.iter().find(|a| name.as_str() == a.name) {
            Some((c, Some(allocator)))
        } else if name.as_str() == c.free {
            Some((c, None))
        } else {
            None
        }
    })
}

/// The count of a contract allocation from its size argument: `n *
/// size_of::<T>()` (either order, through casts) → `Slice` with count `n`;
/// `size_of::<T>()` alone → `Sized`.
fn size_of_call(e: &Expr<'_>) -> bool {
    let e = peel_casts(e);
    let ExprKind::Call(callee, args) = &e.kind else { return false };
    args.is_empty()
        && matches!(
            &callee.kind,
            ExprKind::Path(QPath::Resolved(_, path))
                if path.segments.last().is_some_and(|s| s.ident.name.as_str() == "size_of")
        )
}

fn shape_of(tcx: TyCtxt<'_>, size: &Expr<'_>) -> Result<(BoxShape, Option<String>), String> {
    let is_size_of = size_of_call;
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
    /// The extent is the contract's own postcondition on the RESULT — a
    /// NUL-terminated copy — so the construction binds the block and measures
    /// it, instead of spelling a count over the allocator's arguments.
    nul_terminated: bool,
}

fn allocation_contract(tcx: TyCtxt<'_>, e: &Expr<'_>) -> Option<&'static Contract> {
    let did = callee_of(peel_casts(e))?;
    let (contract, allocator) = contract_of(tcx, did)?;
    allocator.map(|_| contract)
}

fn allocation<'h>(tcx: TyCtxt<'_>, e: &'h Expr<'h>) -> Option<Result<Allocation, String>> {
    let call = peel_casts(e);
    let did = callee_of(call)?;
    let (contract, allocator) = contract_of(tcx, did)?;
    let allocator = allocator?;
    let ExprKind::Call(_, args) = &call.kind else { return None };
    let snippet = |span: Span| {
        tcx.sess
            .source_map()
            .span_to_snippet(span)
            .unwrap_or_default()
    };
    let read = match &allocator.extent {
        Extent::SizeArgument(index) => shape_of(tcx, args.get(*index)?),
        Extent::ElementCount {
            count_index,
            size_index,
        } => {
            let size = args.get(*size_index)?;
            if size_of_call(size) {
                Ok((BoxShape::Slice, Some(snippet(args.get(*count_index)?.span))))
            } else {
                Err(format!("{COUNT}:element-size:{}", snippet(size.span)))
            }
        }
        // The postcondition, read off the RESULT: the block is a NUL-terminated
        // copy, so its extent is its own `CStr` length plus the terminator.
        // Nothing here depends on the argument's emitted form.
        Extent::NulTerminatedCopy => Ok((BoxShape::Slice, None)),
    };
    let nul_terminated = matches!(allocator.extent, Extent::NulTerminatedCopy);
    Some(read.map(|(shape, count)| Allocation {
        contract,
        span: e.span,
        shape,
        count,
        nul_terminated,
    }))
}

/// A statement of a block that concerns a contract owner.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Role {
    /// `let x = <allocation>` / `let x = if c { <allocation> } else { null }`.
    Let,
    /// `x = <allocation>` — build 2's assignment receiver (brotli's
    /// ensure-capacity idiom allocates into a null-initialized local).
    Alloc,
    /// `x = y` with `y` another contract owner — the generation MOVES in.
    MoveIn,
    /// `y = x` with `y` another contract owner — it moves out.
    MoveOut,
    /// `<Free>(m, x as *mut c_void);`
    Free,
    /// `x = <null>;`
    NullStore,
    /// `let x = <null>;` — build 2: the ensure-capacity idiom declares the
    /// receiver empty and allocates into it further down.
    NullInit,
    /// Any other assignment to the binding.
    Store,
}

impl Role {
    /// The owner's generation after this statement, or `None` when the role
    /// does not change it.
    fn creates(self) -> bool {
        matches!(self, Role::Let | Role::Alloc | Role::MoveIn)
    }

    fn releases(self) -> bool {
        matches!(self, Role::Free | Role::MoveOut)
    }
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
    /// build 2: `x = <allocation>` — (binding, the value's span, its id).
    alloc_assigns: Vec<(HirId, Span, HirId)>,
    /// build 2: `x = y` with `y` a bare local — (binding, source, value span).
    moves: Vec<(HirId, HirId, Span)>,
    /// build 2: `let x = <null>;` — (binding, the initializer's span).
    null_inits: Vec<(HirId, Span)>,
    /// Every CAST of a bare local — (binding, the cast's span). The owner walk
    /// must have spelled each one: a cast this rule leaves alone is a use of
    /// the owner in another pointee's shape, which the emitted `Box` cannot
    /// satisfy (lodepng's `mem as *const c_void`, the counted-void family's).
    casts: Vec<(HirId, Span)>,
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
                    if allocation(self.tcx, value).is_some() {
                        return Some((hir, Role::Let));
                    }
                    if null_literal(init) {
                        self.out.null_inits.push((hir, init.span));
                        return Some((hir, Role::NullInit));
                    }
                    None
                }),
                rustc_hir::StmtKind::Semi(e) | rustc_hir::StmtKind::Expr(e) => match &e.kind {
                    ExprKind::Call(_, args) => callee_of(e)
                        .and_then(|did| contract_of(self.tcx, did))
                        .filter(|(_, allocator)| allocator.is_none())
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
                            // build 2 (relay wave-6a/018): the ensure-capacity
                            // idiom allocates into a null-initialized local
                            // (`new_array = if n > 0 { BrotliAllocate(..) }
                            // else { null }`) and RE-SEATS the owner it
                            // replaces (`all_histograms = new_array`).
                            let value = match &rhs.kind {
                                ExprKind::If(_, then, Some(_)) => match then.kind {
                                    ExprKind::Block(b, _) => b.expr.unwrap_or(rhs),
                                    _ => then,
                                },
                                _ => rhs,
                            };
                            let role = if null_literal(rhs) {
                                Role::NullStore
                            } else if allocation(self.tcx, value).is_some() {
                                self.out.alloc_assigns.push((hir, rhs.span, rhs.hir_id));
                                Role::Alloc
                            } else if let Some(source) = bare_local(rhs) {
                                self.out.moves.push((hir, source, rhs.span));
                                Role::MoveIn
                            } else {
                                Role::Store
                            };
                            (hir, role)
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
        if let ExprKind::Cast(inner, _) = &e.kind
            && let ExprKind::Path(QPath::Resolved(_, path)) = &inner.kind
            && let Res::Local(hir) = path.res
        {
            self.out.casts.push((hir, e.span));
        }
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
        // build 2: the function's contract-owner candidates — a local the
        // contract allocates into itself. The receiver walk consults the set
        // so a RE-SEAT of one contract owner from another reads as a move of
        // the generation; a copy into any other local is a second owner this
        // rule cannot follow, and holds.
        let candidates: FxHashSet<HirId> = scan
            .statements
            .iter()
            .filter(|(_, _, _, role, _)| matches!(role, Role::Let | Role::Alloc))
            .map(|(hir, _, _, _, _)| *hir)
            .collect();
        let move_ok = |destination: HirId| candidates.contains(&destination);
        for subject in subjects
            .iter()
            .filter(|s| s.fn_did == function && s.kind == SubjectKind::Local)
        {
            let node = (subject.fn_did, subject.hir_id);
            let label = subject.label.clone();
            let name = subject.param_name.clone().unwrap_or_else(|| "?".to_owned());
            // Which contract's subject this is, known BEFORE any refusal: the
            // libc row's refusals are receipts, every other contract's are
            // decisions (`Plans::yields` says why).
            let subject_contract = scan
                .statements
                .iter()
                .filter(|(hir, _, _, role, _)| {
                    *hir == subject.hir_id && matches!(role, Role::Let | Role::Alloc)
                })
                .find_map(|(hir, _, _, role, span)| {
                    let init = match role {
                        Role::Let => tcx
                            .hir_node(*hir)
                            .parent_hir_node_let(tcx)
                            .and_then(|local| local.init),
                        _ => scan
                            .alloc_assigns
                            .iter()
                            .find(|(h, value, _)| h == hir && span.contains(*value))
                            .map(|(_, _, id)| tcx.hir_node(*id).expect_expr()),
                    }?;
                    let value = match &init.kind {
                        ExprKind::If(_, then, Some(_)) => match then.kind {
                            ExprKind::Block(b, _) => b.expr.unwrap_or(init),
                            _ => then,
                        },
                        _ => init,
                    };
                    allocation_contract(tcx, value)
                });
            let yields =
                subject_contract.is_some_and(|c| c.id.starts_with("allocator-contract:libc"));
            let hold = |out: &mut Plans, reason: String| {
                if yields {
                    out.yields.push((label.clone(), reason));
                } else {
                    out.holds.insert(node, (label.clone(), reason));
                }
            };
            // **The owner's generations** (build 2, relay wave-6a/018). Every
            // event on the binding, in source order: a CREATION (the `let`'s
            // allocation, an assignment of one — brotli's ensure-capacity
            // idiom allocates into a null-initialized local — or a move in
            // from another owner), a RELEASE (the contract free, or a move
            // out into another owner), the `BROTLI_FREE` null store, and the
            // uses. The simulation below proves the owner is never read while
            // it holds nothing, never re-seated over a live generation, and
            // never live at a `return` or at the body's end — the C free of a
            // Rust block is UB and this rule adds no drop.
            #[derive(Clone, Copy, PartialEq, Eq, Debug)]
            enum Event {
                Create,
                Release,
                NullStore,
                Use,
                Store,
            }
            let mut events: Vec<(Span, HirId, Event, Role)> = Vec::new();
            for (hir, block, _, role, span) in &scan.statements {
                if *hir == subject.hir_id {
                    // A move in from a local that is not itself a contract
                    // owner carries no generation — the value came from
                    // somewhere this rule does not follow, so it reads as an
                    // opaque store (and a local no contract touches keeps
                    // every event it has: none).
                    let role = &if *role == Role::MoveIn
                        && !scan.moves.iter().any(|(dest, source, value)| {
                            dest == hir && span.contains(*value) && candidates.contains(source)
                        }) {
                        Role::Store
                    } else {
                        *role
                    };
                    let event = match role {
                        Role::Let | Role::Alloc | Role::MoveIn => Event::Create,
                        Role::Free | Role::MoveOut => Event::Release,
                        Role::NullStore | Role::NullInit => Event::NullStore,
                        Role::Store => Event::Store,
                    };
                    events.push((*span, *block, event, *role));
                } else if *role == Role::MoveIn
                    && scan
                        .moves
                        .iter()
                        .any(|(dest, source, _)| dest == hir && *source == subject.hir_id)
                {
                    events.push((*span, *block, Event::Release, Role::MoveOut));
                }
            }
            if events.is_empty() {
                continue;
            }
            // The creations decide the shape, the optionality and the text.
            let mut creations: Vec<(Span, Option<Span>, Allocation)> = Vec::new();
            let mut creation_error: Option<String> = None;
            let mut moved_in = 0usize;
            for (span, _, event, role) in &events {
                if *event != Event::Create {
                    continue;
                }
                if *role == Role::MoveIn {
                    moved_in += 1;
                    continue;
                }
                let value_expr = match role {
                    Role::Let => tcx
                        .hir_node(subject.hir_id)
                        .parent_hir_node_let(tcx)
                        .and_then(|local| local.init),
                    _ => scan
                        .alloc_assigns
                        .iter()
                        .find(|(hir, value, _)| *hir == subject.hir_id && span.contains(*value))
                        .map(|(_, _, id)| tcx.hir_node(*id).expect_expr()),
                };
                let Some(init) = value_expr else {
                    creation_error = Some(format!("{USE}:creation-unreadable"));
                    break;
                };
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
                            creation_error = Some(format!(
                                "{USE}:conditional-else:{}",
                                snippet(otherwise.span)
                            ));
                            break;
                        };
                        (value, Some(null.span))
                    }
                    _ => (init, None),
                };
                match allocation(tcx, value) {
                    Some(Ok(a)) => creations.push((a.span, else_null, a)),
                    Some(Err(reason)) => {
                        creation_error = Some(reason);
                        break;
                    }
                    None => {
                        creation_error = Some(format!("{USE}:creation-not-an-allocation"));
                        break;
                    }
                }
            }
            if let Some(reason) = creation_error {
                hold(&mut out, reason);
                continue;
            }
            if creations.is_empty() {
                // Every generation of this local came from another owner; the
                // source owns the contract and this one is its receiver — not
                // a shape this build plans.
                if moved_in > 0 {
                    hold(&mut out, format!("{USE}:moved-in-only"));
                }
                continue;
            }
            let shape = creations[0].2.shape;
            let contract = creations[0].2.contract;
            // **The libc row yields to the fields family on a model-OWNING
            // local.** The licensing-wall supersession this rule applies is for
            // subjects the model calls Raw or Ref — report 017's 82. A local
            // the model already calls Owning is ownership-fields' body-local
            // population (their `box_w1` / `box_w2` / `box2_*` witnesses), and
            // two families planning one binding is an ill-typed function, not
            // an arbitration.
            if contract.id.starts_with("allocator-contract:libc")
                && slots
                    .fn_local_slots
                    .get(&subject.fn_did)
                    .and_then(|u| u.slot_for_local_depth(subject.local, 0))
                    .is_some_and(|slot| {
                        model.get(&SlotRef::Local(subject.fn_did, slot)) == Some(&SlotKind::Owning)
                    })
            {
                hold(&mut out, format!("{USE}:model-owning-is-the-fields-family"));
                continue;
            }
            // **The libc row yields to the fields family on a model-OWNING
            // local** (R434-4 §3). The licensing-wall supersession this rule
            // applies is for subjects the model calls Raw or Ref — report 017's
            // 82. A local the model already calls Owning is ownership-fields'
            // body-local population, and two families planning one subject is
            // exactly what the class layer would have to arbitrate.

            if creations.iter().any(|(_, _, a)| a.shape != shape) {
                hold(&mut out, format!("{USE}:shapes-disagree"));
                continue;
            }
            // One generation created unconditionally and released once is the
            // non-optional owner; anything else (a conditional allocation, a
            // null-initialized local, several generations) carries `None`.
            let optional = creations.len() + moved_in > 1
                || creations
                    .iter()
                    .any(|(_, else_null, _)| else_null.is_some())
                || events[0].2 != Event::Create;
            let frees: Vec<(Span, Span)> = scan
                .frees
                .iter()
                .filter(|(hir, _, _)| *hir == subject.hir_id)
                .map(|(_, call, arg)| (*call, *arg))
                .collect();
            let uses = match owner_uses(
                tcx,
                subject,
                shape,
                optional,
                !optional,
                &frees,
                &lend_ok,
                &transfer_ok,
                &move_ok,
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
            // Every CAST of the owner must be one this rule spelled: an edit
            // covers it, or it is the free's own argument. A cast left alone
            // is the owner used in another pointee's shape — the counted-void
            // family's `mem as *const c_void` — which the emitted `Box` cannot
            // satisfy, so the subject is not this rule's.
            if let Some((_, cast)) = scan.casts.iter().find(|(hir, span)| {
                *hir == subject.hir_id
                    && !uses
                        .edits
                        .iter()
                        .any(|e| e.span == *span || e.span.contains(*span))
                    && !frees.iter().any(|(_, arg)| arg.contains(*span))
                    && !creations.iter().any(|(c, _, _)| c.contains(*span))
            }) {
                hold(&mut out, format!("{USE}:unbridged-cast:{}", snippet(*cast)));
                continue;
            }

            for edit in &uses.edits {
                if !events
                    .iter()
                    .any(|(span, _, _, _)| span.contains(edit.span))
                {
                    events.push((edit.span, events[0].1, Event::Use, Role::Store));
                }
            }
            for store in &uses.stores {
                if !events.iter().any(|(span, _, _, _)| span.contains(*store)) {
                    events.push((*store, events[0].1, Event::Release, Role::MoveOut));
                }
            }
            events.sort_by_key(|(span, _, _, _)| (span.lo(), span.hi()));
            // The simulation: Dead → Create → Live → Release → Dead.
            let mut live = false;
            let mut overwrites: Vec<Span> = Vec::new();
            let mut block_state: FxHashMap<HirId, (bool, bool)> = FxHashMap::default();
            let mut sequence_error = None;
            for (span, block, event, role) in &events {
                let entry = block_state.entry(*block).or_insert((live, live));
                match event {
                    // **The overwrite of a live owner stays REFUSED** — R434-4
                    // §2 admitted it, and Miri refutes the premise it was
                    // admitted on (report 019 §3). An implicit close here
                    // drops a `Box` whose block came from the CONTRACT's
                    // allocator, and `Box`'s drop is Rust's deallocation, not
                    // the contract's: Miri reports "deallocating … C heap
                    // memory using Rust heap deallocation operation" — UB by
                    // the language, whatever glibc does with the layout. The
                    // admission returns when the release at the overwrite is
                    // spelled with the contract's OWN free, which is a build,
                    // not a waiver.
                    Event::Create if live => {
                        sequence_error =
                            Some(format!("{OVERWRITE}:re-seat-over-live:{}", snippet(*span)));
                    }
                    Event::Create => live = true,
                    Event::Release if !live => {
                        sequence_error = Some(format!(
                            "{IMPLICIT_CLOSE}:release-without-generation:{}",
                            snippet(*span)
                        ));
                    }
                    Event::Release => live = false,
                    Event::Use if !live => {
                        sequence_error = Some(format!("{USE}:read-while-empty:{}", snippet(*span)));
                    }
                    Event::Use | Event::NullStore => {}
                    Event::Store => {
                        sequence_error = Some(format!("{OVERWRITE}:{}", snippet(*span)));
                    }
                }
                let _ = role;
                entry.1 = live;
                if sequence_error.is_some() {
                    break;
                }
            }
            if let Some(reason) = sequence_error {
                hold(&mut out, reason);
                continue;
            }
            if live {
                hold(&mut out, format!("{IMPLICIT_CLOSE}:live-at-exit"));
                continue;
            }
            // Every block the owner touches must leave it as it found it: a
            // branch that frees a generation must re-seat one (brotli's
            // ensure-capacity), and one that creates must release.
            if let Some((_, (entry, exit))) = block_state.iter().find(|(_, (a, b))| a != b) {
                hold(
                    &mut out,
                    format!("{IMPLICIT_CLOSE}:block-unbalanced:{entry}->{exit}"),
                );
                continue;
            }
            // A `return` while a generation is live would drop it in Rust.
            let live_spans: Vec<(Span, Span)> = {
                let mut spans = Vec::new();
                let mut open: Option<Span> = None;
                for (span, _, event, _) in &events {
                    match event {
                        Event::Create => open = Some(*span),
                        Event::Release => {
                            if let Some(start) = open.take() {
                                spans.push((start, *span));
                            }
                        }
                        _ => {}
                    }
                }
                spans
            };
            // A return inside a DEAD null guard is not a path of the emitted
            // program: the guard tests a `Box`, which cannot be null, and the
            // owner walk already replaces the whole `if` with `{}`. libc's
            // allocators are the reason this matters — brotli's exits on a
            // null result, so no fixture of this rule had a guard before.
            if let Some(ret) = scan.returns.iter().find(|r| {
                !uses.dead_guards.iter().any(|guard| guard.contains(**r))
                    && live_spans
                        .iter()
                        .any(|(start, end)| r.lo() > start.hi() && r.lo() < end.lo())
            }) {
                hold(
                    &mut out,
                    format!("{IMPLICIT_CLOSE}:return:{}", snippet(*ret)),
                );
                continue;
            }
            // The edits: one construction per generation, `None` on every
            // else arm and every null store, `Box::into_raw` at every free.
            let mut expr_edits = uses.edits;
            let mut delete_statements = Vec::new();
            for (span, _, event, role) in &events {
                if *event != Event::NullStore {
                    continue;
                }
                if *role == Role::NullInit {
                    let (_, init) = scan
                        .null_inits
                        .iter()
                        .find(|(hir, _)| *hir == subject.hir_id)
                        .expect("the null initializer");
                    expr_edits.push(BoxExprEdit {
                        span: *init,
                        replacement: "None".to_owned(),
                        receipt: "allocator-contract-null-init",
                    });
                    continue;
                }
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
            for (span, else_null, a) in &creations {
                // **The construction is TWO INSERTIONS, not a replacement**
                // (relay wave-6a/020 (ii), R432-2). The allocator call text is
                // left exactly where it is and the `Box` is spelled around it:
                // a prefix at the allocation's opening boundary and a suffix at
                // its closing one. A replacement of the whole allocation would
                // CONTAIN every edit another class plans inside the call — at
                // 26 brotli receivers that is the raw-boundary C arm bridging
                // the contract's own manager argument (`BrotliAllocate(&mut *m,
                // ..)`, one byte inside the initializer), and containment holds
                // both classes (`cross-class-interval-collision`, report 014
                // claim 4). Two zero-width insertions at the boundaries contain
                // nothing: the bridge renders where it was planned, inside text
                // this rule never claims.
                let (open, close) = match (&a.shape, &a.count, a.nul_terminated) {
                    (BoxShape::Sized, _, _) => ("Box::from_raw(".to_owned(), ")".to_owned()),
                    // The contract's postcondition: bind the block the
                    // allocator returned and measure IT. The count never
                    // mentions the allocator's arguments, so no other family's
                    // rendering of them can make it stale.
                    (BoxShape::Slice, _, true) => (
                        "{ let __crat_alloc = ".to_owned(),
                        "; Box::from_raw(core::ptr::slice_from_raw_parts_mut(__crat_alloc, \
                         core::ffi::CStr::from_ptr(__crat_alloc).to_bytes().len().wrapping_add(1))) }"
                            .to_owned(),
                    ),
                    (BoxShape::Slice, Some(count), false) => (
                        "Box::from_raw(core::ptr::slice_from_raw_parts_mut(".to_owned(),
                        format!(", ({count}) as usize))"),
                    ),
                    (BoxShape::Slice, None, false) => {
                        unreachable!("a counted slice shape carries its count")
                    }
                };
                let (open, close) = if optional {
                    (format!("Some({open}"), format!("{close})"))
                } else {
                    (open, close)
                };
                expr_edits.push(BoxExprEdit {
                    span: span.shrink_to_lo(),
                    replacement: open,
                    receipt: "allocator-contract-construction",
                });
                expr_edits.push(BoxExprEdit {
                    span: span.shrink_to_hi(),
                    replacement: close,
                    receipt: "allocator-contract-construction-close",
                });
                if let Some(null) = else_null {
                    expr_edits.push(BoxExprEdit {
                        span: *null,
                        replacement: "None".to_owned(),
                        receipt: "allocator-contract-none-arm",
                    });
                }
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
                format!("allocator-contract {}", contract.id),
                format!(
                    "shape={} optional={optional} generations={} moves_in={moved_in} frees={}",
                    match shape {
                        BoxShape::Sized => "sized",
                        BoxShape::Slice => "slice",
                    },
                    creations.len(),
                    frees.len()
                ),
            ];
            for (call, _) in &frees {
                receipts.push(format!(
                    "allocator-contract site={}",
                    super::emitability::EmitabilityFacts::site(tcx, *call)
                ));
            }
            for span in &overwrites {
                receipts.push(format!(
                    "waiver-drop(overwrite) site={}",
                    super::emitability::EmitabilityFacts::site(tcx, *span)
                ));
            }
            for receipt in &receipts {
                out.admitted.push((label.clone(), receipt.clone()));
            }
            out.plans.insert(
                node,
                BoxPlan {
                    shape,
                    optional,
                    expr_edits,
                    delete_statements,
                    receipts,
                    fabricated_extent: false,
                    pointee_override: None,
                    inferred_binding: subject.ty_span.is_none(),
                    overwrite_spans: overwrites.clone(),
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
