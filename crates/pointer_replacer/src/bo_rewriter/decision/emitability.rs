//! **A1 emitability facts.** Static preconditions for emitting a reference,
//! gathered from HIR before any decision is made.
//!
//! # Why this exists
//!
//! S1 decided `Ref` on the BO slot kind alone and let the emitted crate fail
//! the type-check gate. That produced one anonymous whole-crate string with no
//! site and no subject, which is useless as attribution and — worse — made the
//! envelope-demotion counters wrong by construction: a parameter that was
//! decided `Ref` and then killed at the gate is recorded as a *success* by the
//! decision phase.
//!
//! A1 moves those preconditions to where the decision is made, so a subject
//! that cannot be emitted is degraded **with its own site and reason**.
//!
//! # What is modelled at S2a
//!
//! 1. **Raw-pointer-only operations on the parameter** (`p.is_null()`,
//!    `p.offset(..)`, and friends). A `&T` has no such method, so emitting a
//!    reference makes the body ill-typed. This is the g02 class.
//! 2. **In-crate callers.** `plan` rewrites a signature but not its call sites,
//!    so any direct in-crate call makes the crate ill-typed. This is the g06
//!    class, and it is a *temporary* precondition: S3 adds call-site
//!    adaptation, at which point this fact stops forcing a degradation.

use rustc_hash::FxHashMap;
use rustc_hir::{
    Expr, ExprKind, HirId, Mutability, QPath,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::raw_boundary::{
    ForeignCallArgFact, RawMutability, RawTargetType, raw_target_type, symbol_key,
};

/// Methods that exist on raw pointers and not on references.
///
/// Deliberately a small, exact list rather than a heuristic: a false positive
/// here degrades a parameter that could have been emitted (a lost rewrite), and
/// a false negative lets the old anonymous gate failure back in. Both are
/// visible, which is why the list is allowed to grow from evidence rather than
/// from guessing.
const RAW_ONLY_METHODS: &[&str] = &[
    "is_null",
    "offset",
    "wrapping_offset",
    "add",
    "sub",
    "wrapping_add",
    "wrapping_sub",
    "offset_from",
    "read",
    "write",
    "read_volatile",
    "write_volatile",
    "copy_to",
    "copy_from",
    "as_ref",
    "as_mut",
];
/// **How a local `fn` is referred to — S3.6-0.**
///
/// The single `referenced` boolean this replaces was widened deliberately (F1:
/// matching only `Call` missed the callback-table shape), and that widening is
/// exactly what made the adaptable/pinned split unmeasurable: the map kept
/// spans, not kinds, so three populations with three different adaptation
/// stories were indistinguishable.
///
/// **The decision layer still treats all three identically** — any reference
/// degrades `call-site-not-adapted`, unchanged. This records *which*, so the
/// split can be measured before any capability is scoped against it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RefKind {
    /// The path is the callee of a direct call — **adaptable**: every site is
    /// visible and rewritable.
    Call,
    /// The operand of a cast to a fn pointer — **pins** the signature to the
    /// cast's target type.
    FnPtrCast,
    /// Any other path reference: stored in a table, passed as an argument,
    /// returned. **Pins** the signature to whatever consumes it.
    AddrTaken,
}

impl RefKind {
    pub(crate) fn key(self) -> &'static str {
        match self {
            RefKind::Call => "call",
            RefKind::FnPtrCast => "fnptr-cast",
            RefKind::AddrTaken => "addr-taken",
        }
    }

    /// A function is adaptable only if EVERY reference to it is a direct call.
    /// One pinning reference is enough to fix the signature.
    pub(crate) fn is_adaptable(refs: &[(RefKind, Span)]) -> bool {
        !refs.is_empty() && refs.iter().all(|(k, _)| *k == RefKind::Call)
    }
}

/// **What a call site actually supplies at one argument position — S3.6-1.**
///
/// The gate that blocks the adaptable population is a *signature* fact
/// (`referenced`), but adapting a call site is an *argument* question, and no
/// argument fact existed: the `Call` arm bound its arguments to `_`, so the
/// index, the span, the shape and the caller were all discarded at the exact
/// site that could have recorded them.
///
/// **The classification is by outermost operator**, which is what decides the
/// edit. `&mut *p.offset(1)` is an address-of, not arithmetic — the arithmetic
/// is inside the place being borrowed and does not reach the argument's own
/// form.
///
/// # The checked/unchecked distinction this domain has to carry
///
/// Banked rule (2026-08-09): the compiler sees aliasing through **real places**
/// and is **blind through a raw-pointer deref**. [`Self::BareLocal`] and
/// [`Self::AddrOf`] land in the CHECKED region — a mistake there is an
/// `E0499`/`E0502`, i.e. a revert. A bridge that borrows through a raw base
/// lands in the UNCHECKED region, where the same mistake compiles. That is why
/// no shape here constructs such a bridge: the reborrow arm is **parked**.
// No `Ord`: `HirId` has none, and nothing needs it — the census sorts the
// rendered `key()` strings, not the shapes themselves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ArgShape {
    /// A bare path resolving to a local binding. **The dominant shape**, and the
    /// propagation edge: whether it needs an edit depends entirely on whether
    /// that binding converts too, which is what makes conversion joint.
    BareLocal(HirId),
    /// `&mut e` / `&e`, already written. Needs no edit either way — `&mut T`
    /// coerces to `*mut T` today and satisfies `&mut T`/`&T` after.
    ///
    /// **`base` is the borrowed place's ROOT binding, and it is what makes the
    /// within-site overlap gate possible at all.** Overlap is not textual
    /// identity: brotli's
    /// `BrotliDecoderHuffmanTreeGroupInit(s, &mut (*s).literal_hgroup, …)`
    /// passes `s` at one `*mut` position and a place *inside* `*s` at another.
    /// Without the root this arm carries nothing to see that with, and the gate
    /// would let a certain-overlap class through.
    ///
    /// `None` when the operand is not rooted at a local binding (a static, a
    /// temporary). `None` is **not** "no overlap" — the gate must treat an
    /// unknown root conservatively.
    AddrOf {
        mutable: bool,
        base: Option<HirId>,
        /// Did the walk to `base` traverse a **deref**?
        ///
        /// **P2's visibility split turns on this.** `&mut x` on a local is a
        /// real place whatever happens. `&mut (*s).g` is a place *through* `s`
        /// — and §5a measured that the compiler CATCHES overlap when that base
        /// is a reference and is BLIND when it is a raw pointer. So the same
        /// expression is checked or unchecked depending on whether `s` itself
        /// converts, which cannot be asked without knowing a deref happened.
        through_deref: bool,
    },
    /// `&mut e as *mut T` — the cast is the only thing to remove.
    AddrOfCast { mutable: bool, inner: Span },
    /// `q as *mut T` where `q` is a local binding.
    CastOfLocal { binding: HirId, inner: Span },
    /// A nameable expression whose resolved type is a raw pointer: an offset,
    /// field read, call result, array `.as_ptr()`/`.as_mut_ptr()`, or a cast not
    /// covered by the two peel-only arms above.
    ///
    /// The whole argument remains the adapter's subtree. `root` is best-effort
    /// overlap evidence; `None` stays conservative wherever a mutable borrow is
    /// involved.
    RawExpr { root: Option<HirId> },
    /// A null pointer literal. **Blocks**: `&mut T` cannot represent null.
    NullLit,
    /// Any other cast.
    Cast { inner: Span },
    /// Anything else — a call result, an index, a field, arithmetic.
    Other,
}

impl ArgShape {
    pub(crate) fn key(self) -> &'static str {
        match self {
            ArgShape::BareLocal(_) => "bare-local",
            ArgShape::AddrOf { mutable: true, .. } => "addr-of-mut",
            ArgShape::AddrOf { mutable: false, .. } => "addr-of",
            ArgShape::AddrOfCast { mutable: true, .. } => "addr-of-mut-cast",
            ArgShape::AddrOfCast { mutable: false, .. } => "addr-of-cast",
            ArgShape::CastOfLocal { .. } => "cast-of-local",
            ArgShape::RawExpr { .. } => "raw-expr",
            ArgShape::NullLit => "null-lit",
            ArgShape::Cast { .. } => "cast",
            ArgShape::Other => "other",
        }
    }

    /// The **place root** this argument reads or borrows, when it is a local
    /// binding.
    ///
    /// This is the key the within-site overlap gate compares. Two argument
    /// positions at one call site sharing a root **may alias**, and after
    /// conversion that is `E0499` (or `E0502` — demoting one side to shared
    /// does *not* rescue it, measured). A shared root is a MAY-overlap, so
    /// blocking on it costs yield and never soundness.
    ///
    /// Shapes that cannot convert at all return `None` and are irrelevant here:
    /// they block on their own account before overlap is asked about.
    pub(crate) fn place_root(self) -> Option<HirId> {
        match self {
            ArgShape::BareLocal(id) | ArgShape::CastOfLocal { binding: id, .. } => Some(id),
            ArgShape::AddrOf { base, .. } => base,
            ArgShape::RawExpr { root } => root,
            _ => None,
        }
    }
}

/// Walk a place expression down to the local binding it is rooted at.
///
/// `(*s).literal_hgroup` roots at `s`; `v[i].f` roots at `v`; a static or a
/// temporary roots at nothing. Deref is included deliberately — that is the
/// C2Rust shape, and stopping at it would make every `(*p).field` argument look
/// unrelated to `p`.
fn place_root(expr: &Expr<'_>) -> (Option<HirId>, bool) {
    let mut cur = expr;
    let mut through_deref = false;
    loop {
        match &cur.kind {
            ExprKind::Unary(rustc_hir::UnOp::Deref, base) => {
                through_deref = true;
                cur = base;
            }
            ExprKind::Field(base, _)
            | ExprKind::Index(base, _, _)
            | ExprKind::AddrOf(_, _, base)
            | ExprKind::Cast(base, _)
            | ExprKind::DropTemps(base) => cur = base,
            ExprKind::MethodCall(_, receiver, _, _) => cur = receiver,
            _ => return (BodyFacts::resolved_local(cur), through_deref),
        }
    }
}

/// One argument at one call site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Arg {
    /// The callee's **0-based parameter index**, which is `SubjectKind::Param`'s
    /// `hir_index` — the same key, so the join needs no translation.
    pub index: usize,
    pub span: Span,
    pub shape: ArgShape,
    pub source_type: String,
    pub target: Option<super::raw_boundary::RawTargetType>,
    /// Exact variable-local storage under `&mut local` (optionally beneath raw
    /// casts). Projections, dereferences, fields, and temporaries are absent.
    pub direct_storage: Option<(HirId, Span)>,
    pub adapter_operand_span: Span,
    pub adapter_operand_mutability: Option<super::raw_boundary::RawMutability>,
    /// Exact syntactic place identity after peeling address/cast wrappers.
    /// Distinct field projections remain distinct even when `place_root` is
    /// the same aggregate local.
    pub place_identity: Option<String>,
}

/// One direct call to a local `fn`, with everything adaptation needs.
///
/// Grouped **by site** rather than flattened per `(callee, index)` because the
/// duplicate-argument gate is a *within-site* question — "do two pointer
/// parameters of this call receive the same place?" — and a flattened map
/// cannot answer it. The per-index view is a cheap projection of this one;
/// the reverse is not true.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CallSite {
    pub caller: LocalDefId,
    pub span: Span,
    pub args: Vec<Arg>,
}

/// Wave-2's two body positions. Kept beside [`CallSite`] because both are HIR
/// expression facts consumed by the same adapter synthesizer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BodyAdapterContext {
    LocalInitializer,
    AssignmentRhs,
}

impl BodyAdapterContext {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::LocalInitializer => "local-initializer",
            Self::AssignmentRhs => "assignment-rhs",
        }
    }
}

/// One exact scalar-reference adapter candidate in an allowlisted function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BodyAdapterSite {
    pub owner: LocalDefId,
    pub destination: HirId,
    pub rhs_span: Span,
    pub shape: ArgShape,
    pub context: BodyAdapterContext,
    /// Calls/method calls are deliberately not adapted in wave 2. This bit is
    /// carried from the HIR classification rather than rediscovered from text.
    pub side_effecting: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AddressOperand {
    pub node: (LocalDefId, HirId),
    pub span: Span,
    pub target: RawTargetType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AddressObservationFact {
    pub owner: LocalDefId,
    pub span: Span,
    pub op: &'static str,
    pub target_type: String,
    pub operands: Vec<AddressOperand>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReturnSiteFact {
    pub owner: LocalDefId,
    pub span: Span,
    pub root: Option<HirId>,
    pub source_shape: &'static str,
    pub source_type: RawTargetType,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AddressUseClass {
    ValueOnly,
    AccessOnly,
    Both,
    Neither,
}

impl AddressUseClass {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::ValueOnly => "value-only",
            Self::AccessOnly => "access-only",
            Self::Both => "both",
            Self::Neither => "neither",
        }
    }
}

const WAVE2_BODY_FUNCTIONS: &[&str] = &[
    "src::enc::backward_references_hq::BrotliZopfliCreateCommands",
    "src::enc::block_splitter::BrotliSplitBlock",
    "src::enc::block_splitter::CountLiterals",
    "src::json::json_extract_get_array_size",
    "src::json::json_extract_get_object_size",
    "src::json::json_extract_get_string_size",
    "src::libtree::visited_files_contains",
    "src::lodepng::color_tree_add",
];

fn wave2_body_owner(tcx: TyCtxt<'_>, owner: LocalDefId) -> bool {
    WAVE2_BODY_FUNCTIONS.contains(&tcx.def_path_str(owner.to_def_id()).as_str())
}

fn body_side_effecting(expr: &Expr<'_>) -> bool {
    matches!(expr.kind, ExprKind::Call(..) | ExprKind::MethodCall(..))
}

/// Peel `as` casts to reach the underlying operand.
///
/// C2Rust writes null as `0 as *mut T` but also as `0 as libc::c_int as *mut T`,
/// so a single-level test would classify the second as an ordinary cast and let
/// a null through the gate that exists to stop it.
fn peel_casts<'e>(mut expr: &'e Expr<'e>) -> &'e Expr<'e> {
    while let ExprKind::Cast(inner, _) = &expr.kind {
        expr = inner;
    }
    expr
}

fn is_zero_literal(expr: &Expr<'_>) -> bool {
    matches!(
        &peel_casts(expr).kind,
        ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(v, _) if v == 0)
    )
}

/// Classify an argument expression by its **outermost** operator and resolved
/// type. The type check is what keeps `Other` fail-closed: wave 1 admits a
/// complex expression only when rustc says the expression itself is a raw
/// pointer, never because its spelling merely resembles one.
fn classify_arg(tcx: TyCtxt<'_>, expr: &Expr<'_>) -> ArgShape {
    let raw_pointer = matches!(
        tcx.typeck(expr.hir_id.owner.def_id).expr_ty(expr).kind(),
        rustc_middle::ty::TyKind::RawPtr(..)
    );
    match &expr.kind {
        // Casts first: both the null form and the strip-the-cast forms are
        // casts, and testing the operand is the only way to tell them apart.
        ExprKind::Cast(inner, _) => {
            if is_zero_literal(inner) {
                ArgShape::NullLit
            } else if let ExprKind::AddrOf(_, mutability, _) = &peel_casts(expr).kind {
                ArgShape::AddrOfCast {
                    mutable: matches!(mutability, Mutability::Mut),
                    inner: peel_casts(expr).span,
                }
            } else if let Some(binding) = BodyFacts::resolved_local(peel_casts(expr)) {
                ArgShape::CastOfLocal {
                    binding,
                    inner: peel_casts(expr).span,
                }
            } else if raw_pointer {
                ArgShape::RawExpr {
                    root: place_root(expr).0,
                }
            } else {
                ArgShape::Cast { inner: inner.span }
            }
        }
        ExprKind::AddrOf(_, mutability, operand) => {
            let (base, through_deref) = place_root(operand);
            ArgShape::AddrOf {
                mutable: matches!(mutability, Mutability::Mut),
                base,
                through_deref,
            }
        }
        _ => match BodyFacts::resolved_local(expr) {
            Some(binding) => ArgShape::BareLocal(binding),
            // A bare `0` with no cast still cannot become a reference.
            None if is_zero_literal(expr) => ArgShape::NullLit,
            None if raw_pointer => ArgShape::RawExpr {
                root: place_root(expr).0,
            },
            None => ArgShape::Other,
        },
    }
}

fn direct_mutable_storage(expr: &Expr<'_>) -> Option<(HirId, Span)> {
    let peeled = peel_casts(expr);
    let ExprKind::AddrOf(_, Mutability::Mut, storage) = peeled.kind else {
        return None;
    };
    let ExprKind::Path(QPath::Resolved(_, path)) = storage.kind else {
        return None;
    };
    let Res::Local(binding) = path.res else {
        return None;
    };
    Some((binding, storage.span))
}

#[derive(Debug, Default)]
pub(crate) struct EmitabilityFacts {
    /// `callee -> reference spans`. Non-empty means a signature change would
    /// break an unadapted USE — not only a call.
    ///
    /// **F1:** this was `ExprKind::Call` only, which missed the C2Rust
    /// callback-table shape (`descent as unsafe extern "C" fn(..)`): the
    /// function is never *called* directly, so its signature was rewritten
    /// while a fn-item cast still referred to the old type, and the crate died
    /// at the anonymous whole-crate gate — the exact class A1 exists to retire.
    /// Any path reference to a local fn now counts, which subsumes direct
    /// calls, address-taking, and fn-pointer casts uniformly.
    pub referenced: FxHashMap<LocalDefId, Vec<(RefKind, Span)>>,
    /// `(fn, param HirId) -> every raw-only use, in HIR walk order`.
    ///
    /// **A `Vec`, not a first-wins entry, since S3.2′-2.** Attribution still
    /// takes `.first()` — the reported op and site are unchanged, byte for byte.
    /// What the vector adds is the question the slice arm has to ask and a
    /// first-wins map cannot answer: *are ALL of this subject's raw-only uses
    /// arithmetic?*
    ///
    /// The hazard is concrete. A subject carrying both `offset` and `is_null`
    /// records whichever the walk met first. If that is `offset`, a first-wins
    /// reading says "arithmetic, emit a slice" — and `p.is_null()` on `&[T]`
    /// does not compile. The slice arm needs the whole set or it is unsound.
    pub raw_only_uses: FxHashMap<(LocalDefId, HirId), Vec<(String, Span)>>,
    /// **F5:** `(fn, param HirId) -> comparison span`.
    ///
    /// A pointer comparison is a blocking precondition in BOTH directions, and
    /// the second is the dangerous one: `p > limit` on two raw pointers
    /// compares ADDRESSES, while the same expression on two references
    /// compares POINTEES. That version type-checks, passes the gate, and
    /// silently inverts a bounds check — so it must be refused at decision
    /// time, not discovered by a behavioral test that does not exist yet.
    pub ptr_comparisons: FxHashMap<(LocalDefId, HirId), Span>,
    /// Value-observing pointer comparisons, with both operand identities. These
    /// are address sinks only; arithmetic/deref uses never enter this vector.
    pub address_observations: Vec<AddressObservationFact>,
    /// Original raw-pointer return expressions, including explicit `return`
    /// operands and function-body tail expressions.
    pub return_sites: Vec<ReturnSiteFact>,
    /// **S3.6-1** — `callee -> every direct call site, with its arguments`.
    ///
    /// Recorded here rather than derived later, because it is not derivable
    /// later: this is the third time a quantity absent at collection time
    /// proved unrecoverable by post-hoc joining (S3.6-0's `ref_kinds`, the
    /// failed name-keyed `#[no_mangle]` join, and now the argument facts).
    ///
    /// **Only direct calls appear.** A function reached by a fn-pointer cast has
    /// no visible argument list, which is exactly why it is `pinned` and not
    /// this slice's business.
    ///
    /// **The decision layer must not read this at task 0** — the S3.6-0 pattern
    /// that makes zero corpus delta structural rather than lucky.
    pub call_args: FxHashMap<LocalDefId, Vec<CallSite>>,
    /// Resolved arguments to non-body callees. Unlike [`call_args`], every row
    /// carries the exact callee identity and raw target type needed by the
    /// raw-boundary contract gate.
    pub foreign_call_args: Vec<ForeignCallArgFact>,
    /// Item-E wave 2's exact, allowlisted body positions. An empty entry for a
    /// ninth function is the scope control; no downstream name filter exists.
    pub body_adapters: Vec<BodyAdapterSite>,
}

/// Gather A1 facts for the whole crate in one HIR pass per function body.
pub(crate) fn collect(tcx: TyCtxt<'_>, functions: &[LocalDefId]) -> EmitabilityFacts {
    let mut facts = EmitabilityFacts::default();
    let local: Vec<LocalDefId> = functions.to_vec();
    // EVERY body in the crate, not only the functions under consideration:
    // a `static` initializer holding a callback table references functions
    // (F1) and would otherwise never be visited at all.
    for owner in tcx.hir_body_owners() {
        let body = tcx.hir_body_owned_by(owner);
        let tail = (tcx.def_kind(owner) == rustc_hir::def::DefKind::Fn)
            .then(|| match &body.value.kind {
                ExprKind::Block(block, _) => block.expr.map(|expr| expr.hir_id),
                _ => Some(body.value.hir_id),
            })
            .flatten();
        let mut visitor = BodyFacts {
            tcx,
            fn_did: owner,
            locals: &local,
            tail,
            facts: &mut facts,
        };
        visitor.visit_body(body);
    }
    facts
}

/// Note the absent `tcx`: this visitor works entirely on HIR nodes and
/// resolutions. It *did* carry a `TyCtxt` that nothing ever read — dead weight
/// that the module-wide `allow(dead_code)` hid, and that the lint reported the
/// moment the blanket came off.
struct BodyFacts<'a, 'tcx> {
    /// **S3.6-0** — carried solely to read a path expression's PARENT node, so
    /// a reference to a local `fn` can be classified `Call` / `FnPtrCast` /
    /// `AddrTaken`. Nothing else in this visitor consults it.
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    locals: &'a [LocalDefId],
    tail: Option<HirId>,
    facts: &'a mut EmitabilityFacts,
}

impl BodyFacts<'_, '_> {
    /// The `HirId` of the binding a path expression resolves to, if it is a
    /// local. That is how a use is attributed to a specific parameter rather
    /// than to a name that might be shadowed.
    fn resolved_local(expr: &Expr<'_>) -> Option<HirId> {
        let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind else {
            return None;
        };
        match path.res {
            Res::Local(hir_id) => Some(hir_id),
            _ => None,
        }
    }

    fn address_operand(&self, expr: &Expr<'_>) -> Option<AddressOperand> {
        let expr = peel_casts(expr);
        let hir_id = Self::resolved_local(expr)?;
        let target = raw_target_type(self.tcx, self.tcx.typeck(self.fn_did).expr_ty(expr))?;
        Some(AddressOperand {
            node: (self.fn_did, hir_id),
            span: expr.span,
            target,
        })
    }

    fn owned_by_call_argument(&self, expr: &Expr<'_>) -> bool {
        let mut child = expr.hir_id;
        for _ in 0..4 {
            let rustc_hir::Node::Expr(parent) = self.tcx.parent_hir_node(child) else {
                return false;
            };
            match &parent.kind {
                ExprKind::Call(_, args) if args.iter().any(|arg| arg.hir_id == child) => {
                    return true;
                }
                ExprKind::DropTemps(inner) if inner.hir_id == child => child = parent.hir_id,
                _ => return false,
            }
        }
        false
    }

    fn exact_place_identity(expr: &Expr<'_>) -> Option<String> {
        match &expr.kind {
            ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                Res::Local(hir_id) => Some(format!("local:{}", hir_id.local_id.as_u32())),
                _ => None,
            },
            ExprKind::AddrOf(_, _, inner)
            | ExprKind::Cast(inner, _)
            | ExprKind::DropTemps(inner) => Self::exact_place_identity(inner),
            ExprKind::Unary(rustc_hir::UnOp::Deref, inner) => {
                Some(format!("{}/*", Self::exact_place_identity(inner)?))
            }
            ExprKind::Field(base, field) => Some(format!(
                "{}/field:{}",
                Self::exact_place_identity(base)?,
                field.name
            )),
            _ => None,
        }
    }
}

impl<'tcx> Visitor<'tcx> for BodyFacts<'_, 'tcx> {
    fn visit_stmt(&mut self, stmt: &'tcx rustc_hir::Stmt<'tcx>) {
        if wave2_body_owner(self.tcx, self.fn_did)
            && let rustc_hir::StmtKind::Let(local) = stmt.kind
            && matches!(local.pat.kind, rustc_hir::PatKind::Binding(..))
            && let Some(init) = local.init
        {
            self.facts.body_adapters.push(BodyAdapterSite {
                owner: self.fn_did,
                destination: local.pat.hir_id,
                rhs_span: init.span,
                shape: classify_arg(self.tcx, init),
                context: BodyAdapterContext::LocalInitializer,
                side_effecting: body_side_effecting(init),
            });
        }
        rustc_hir::intravisit::walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let explicit_return = matches!(
            self.tcx.parent_hir_node(expr.hir_id),
            rustc_hir::Node::Expr(parent)
                if matches!(parent.kind, ExprKind::Ret(Some(value)) if value.hir_id == expr.hir_id)
        );
        if (self.tail == Some(expr.hir_id) || explicit_return)
            && let Some(source_type) =
                raw_target_type(self.tcx, self.tcx.typeck(self.fn_did).expr_ty(expr))
        {
            let shape = classify_arg(self.tcx, expr);
            self.facts.return_sites.push(ReturnSiteFact {
                owner: self.fn_did,
                span: expr.span,
                root: shape.place_root(),
                source_shape: shape.key(),
                source_type,
            });
        }
        if wave2_body_owner(self.tcx, self.fn_did)
            && let ExprKind::Assign(lhs, rhs, _) = expr.kind
            && let Some(destination) = Self::resolved_local(lhs)
        {
            self.facts.body_adapters.push(BodyAdapterSite {
                owner: self.fn_did,
                destination,
                rhs_span: rhs.span,
                shape: classify_arg(self.tcx, rhs),
                context: BodyAdapterContext::AssignmentRhs,
                side_effecting: body_side_effecting(rhs),
            });
        }
        match &expr.kind {
            // (1) raw-pointer-only method on a local
            ExprKind::MethodCall(segment, receiver, args, _) => {
                let method = segment.ident.name.to_string();
                let receiver_node = Self::resolved_local(receiver).map(|hir| (self.fn_did, hir));
                if matches!(method.as_str(), "addr")
                    && let Some(operand) = self.address_operand(receiver)
                {
                    self.facts
                        .address_observations
                        .push(AddressObservationFact {
                            owner: self.fn_did,
                            span: expr.span,
                            op: "ptr-to-int",
                            target_type: format!(
                                "{:?}",
                                self.tcx.typeck(self.fn_did).expr_ty(expr)
                            ),
                            operands: vec![operand],
                        });
                } else if method == "offset_from"
                    && let [right] = args
                    && let Some(left) = self.address_operand(receiver)
                    && let Some(right) = self.address_operand(right)
                {
                    self.facts
                        .address_observations
                        .push(AddressObservationFact {
                            owner: self.fn_did,
                            span: expr.span,
                            op: "difference",
                            target_type: format!(
                                "{:?}",
                                self.tcx.typeck(self.fn_did).expr_ty(expr)
                            ),
                            operands: vec![left, right],
                        });
                } else if RAW_ONLY_METHODS.contains(&method.as_str())
                    && let Some((_, hir_id)) = receiver_node
                {
                    self.facts
                        .raw_only_uses
                        .entry((self.fn_did, hir_id))
                        .or_default()
                        .push((method, expr.span));
                }
            }
            // (2) ANY reference to a local fn — call, address-taken, or the
            // operand of a fn-pointer cast. F1: matching only `Call` missed the
            // callback-table shape entirely.
            ExprKind::Path(QPath::Resolved(_, path)) => {
                if let Res::Def(rustc_hir::def::DefKind::Fn, def_id) = path.res
                    && let Some(local_did) = def_id.as_local()
                    && self.locals.contains(&local_did)
                {
                    // **S3.6-0** — the KIND, read from the parent node. The
                    // decision layer ignores it (any reference still
                    // degrades); it exists so the adaptable/pinned split is
                    // measurable at all.
                    let kind = match self.tcx.parent_hir_node(expr.hir_id) {
                        rustc_hir::Node::Expr(parent) => match parent.kind {
                            ExprKind::Call(callee, _) if callee.hir_id == expr.hir_id => {
                                RefKind::Call
                            }
                            ExprKind::Cast(..) => RefKind::FnPtrCast,
                            _ => RefKind::AddrTaken,
                        },
                        _ => RefKind::AddrTaken,
                    };
                    self.facts
                        .referenced
                        .entry(local_did)
                        .or_default()
                        .push((kind, expr.span));
                }
            }
            // (5) **S3.6-1** — a DIRECT call to a local fn, with its arguments.
            //
            // Separate from arm (2), which classifies the callee PATH by its
            // parent. That arm answers "is this function referenced, and how";
            // this one answers "what is supplied to it", and only the direct-call
            // shape has an answer at all.
            ExprKind::Call(callee, args) => {
                if let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind
                    && let Res::Def(rustc_hir::def::DefKind::Fn, def_id) = path.res
                {
                    let defining_crate = self.tcx.crate_name(def_id.krate);
                    let ptr_eq = matches!(defining_crate.as_str(), "core" | "std")
                        && self.tcx.def_path_str(def_id).ends_with("::ptr::eq");
                    if ptr_eq
                        && args.len() == 2
                        && let Some(left) = self.address_operand(&args[0])
                        && let Some(right) = self.address_operand(&args[1])
                    {
                        self.facts
                            .address_observations
                            .push(AddressObservationFact {
                                owner: self.fn_did,
                                span: expr.span,
                                op: "ptr-eq",
                                target_type: "bool".to_owned(),
                                operands: vec![left, right],
                            });
                    }
                    if let Some(local_did) = def_id.as_local()
                        && self.locals.contains(&local_did)
                    {
                        let sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();
                        let typeck = self.tcx.typeck(self.fn_did);
                        self.facts
                            .call_args
                            .entry(local_did)
                            .or_default()
                            .push(CallSite {
                                caller: self.fn_did,
                                span: expr.span,
                                args: args
                                    .iter()
                                    .enumerate()
                                    .map(|(index, arg)| {
                                        let target = sig
                                            .inputs()
                                            .get(index)
                                            .copied()
                                            .and_then(|ty| raw_target_type(self.tcx, ty));
                                        let shape = classify_arg(self.tcx, arg);
                                        let adapter_operand_span = match shape {
                                            ArgShape::AddrOfCast { inner, .. }
                                            | ArgShape::CastOfLocal { inner, .. } => inner,
                                            _ => arg.span,
                                        };
                                        let adapter_operand_mutability =
                                            match typeck.expr_ty(peel_casts(arg)).kind() {
                                                rustc_middle::ty::TyKind::RawPtr(_, mutability) => {
                                                    Some(if mutability.is_mut() {
                                                        super::raw_boundary::RawMutability::Mut
                                                    } else {
                                                        super::raw_boundary::RawMutability::Const
                                                    })
                                                }
                                                _ => None,
                                            };
                                        Arg {
                                            index,
                                            span: arg.span,
                                            shape,
                                            source_type: format!("{:?}", typeck.expr_ty(arg)),
                                            target,
                                            direct_storage: direct_mutable_storage(arg),
                                            adapter_operand_span,
                                            adapter_operand_mutability,
                                            place_identity: Self::exact_place_identity(arg),
                                        }
                                    })
                                    .collect(),
                            });
                    } else if !ptr_eq {
                        let sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();
                        let typeck = self.tcx.typeck(self.fn_did);
                        let symbol = symbol_key(self.tcx, def_id, self.locals);
                        for (index, arg) in args.iter().enumerate() {
                            let source_ty = typeck.expr_ty(arg);
                            let target = sig
                                .inputs()
                                .get(index)
                                .copied()
                                .and_then(|ty| raw_target_type(self.tcx, ty))
                                .or_else(|| {
                                    sig.c_variadic
                                        .then(|| raw_target_type(self.tcx, source_ty))
                                        .flatten()
                                });
                            let Some(target) = target else {
                                continue;
                            };
                            let shape = classify_arg(self.tcx, arg);
                            let adapter_operand_span = match shape {
                                ArgShape::AddrOfCast { inner, .. }
                                | ArgShape::CastOfLocal { inner, .. } => inner,
                                _ => arg.span,
                            };
                            let adapter_operand_mutability =
                                match typeck.expr_ty(peel_casts(arg)).kind() {
                                    rustc_middle::ty::TyKind::RawPtr(_, mutability) => {
                                        Some(if mutability.is_mut() {
                                            super::raw_boundary::RawMutability::Mut
                                        } else {
                                            super::raw_boundary::RawMutability::Const
                                        })
                                    }
                                    _ => None,
                                };
                            self.facts.foreign_call_args.push(ForeignCallArgFact {
                                caller: self.fn_did,
                                callee: symbol.clone(),
                                call_span: expr.span,
                                argument_index: index,
                                argument_span: arg.span,
                                root: shape.place_root(),
                                shape: shape.key(),
                                source_type: format!("{source_ty:?}"),
                                target,
                                direct_storage: direct_mutable_storage(arg),
                                adapter_operand_span,
                                adapter_operand_mutability,
                            });
                        }
                    }
                }
            }
            // (4) pointer comparison — F5.
            ExprKind::Binary(op, lhs, rhs) => {
                use rustc_hir::BinOpKind::*;
                if matches!(op.node, Lt | Le | Gt | Ge | Eq | Ne) {
                    let operands = [lhs, rhs]
                        .into_iter()
                        .filter_map(|side| self.address_operand(side))
                        .collect::<Vec<_>>();
                    if operands.len() == 2 {
                        let op = match op.node {
                            Lt => "lt",
                            Le => "le",
                            Gt => "gt",
                            Ge => "ge",
                            Eq => "eq",
                            Ne => "ne",
                            _ => unreachable!(),
                        };
                        self.facts
                            .address_observations
                            .push(AddressObservationFact {
                                owner: self.fn_did,
                                span: expr.span,
                                op,
                                target_type: "bool".to_owned(),
                                operands,
                            });
                    }
                    for side in [lhs, rhs] {
                        if let Some(hir_id) = Self::resolved_local(side) {
                            self.facts
                                .ptr_comparisons
                                .entry((self.fn_did, hir_id))
                                .or_insert(expr.span);
                        }
                    }
                }
            }
            // (3) pointer-to-integer is a terminal value observation; every
            // other cast remains raw-only. Integer-to-pointer never enters the
            // address arm because its source is not a raw-pointer local.
            ExprKind::Cast(inner, _) => {
                let owned_by_call_boundary = self.owned_by_call_argument(expr);
                if !owned_by_call_boundary && let Some(operand) = self.address_operand(inner) {
                    let typeck = self.tcx.typeck(self.fn_did);
                    let pointer_to_integer = matches!(
                        typeck.expr_ty(expr).kind(),
                        rustc_middle::ty::TyKind::Int(_) | rustc_middle::ty::TyKind::Uint(_)
                    );
                    let pointer_to_pointer = matches!(
                        typeck.expr_ty(expr).kind(),
                        rustc_middle::ty::TyKind::RawPtr(..)
                    );
                    if pointer_to_integer || pointer_to_pointer {
                        self.facts
                            .address_observations
                            .push(AddressObservationFact {
                                owner: self.fn_did,
                                span: expr.span,
                                op: if pointer_to_integer {
                                    "ptr-to-int"
                                } else {
                                    "ptr-cast"
                                },
                                target_type: format!("{:?}", typeck.expr_ty(expr)),
                                operands: vec![operand],
                            });
                    } else {
                        self.facts
                            .raw_only_uses
                            .entry(operand.node)
                            .or_default()
                            .push(("as-cast".to_owned(), expr.span));
                    }
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

impl EmitabilityFacts {
    /// Render a span as `file:line:col` so a degradation record can leave the
    /// compiler session. Sites are for humans and for counters, not for lookup.
    pub(crate) fn site(tcx: TyCtxt<'_>, span: Span) -> String {
        tcx.sess.source_map().span_to_diagnostic_string(span)
    }

    pub(crate) fn raw_boundary_argument_paths(
        &self,
    ) -> rustc_hash::FxHashSet<(LocalDefId, HirId, u32, u32)> {
        let mut out = rustc_hash::FxHashSet::default();
        for fact in &self.foreign_call_args {
            if let Some(root) = fact
                .direct_storage
                .map(|(storage, _)| storage)
                .or(fact.root)
            {
                out.insert((
                    fact.caller,
                    root,
                    fact.argument_span.lo().0,
                    fact.argument_span.hi().0,
                ));
            }
        }
        for calls in self.call_args.values() {
            for call in calls {
                for argument in &call.args {
                    if argument.target.is_some()
                        && let Some(root) = argument
                            .direct_storage
                            .map(|(storage, _)| storage)
                            .or_else(|| argument.shape.place_root())
                    {
                        out.insert((
                            call.caller,
                            root,
                            argument.span.lo().0,
                            argument.span.hi().0,
                        ));
                    }
                }
            }
        }
        out
    }

    pub(crate) fn depth2_npo_target(
        &self,
        node: (LocalDefId, HirId),
    ) -> Option<super::raw_boundary::Depth2Target> {
        let mut targets = self
            .foreign_call_args
            .iter()
            .filter_map(|fact| {
                (fact.caller == node.0
                    && fact.direct_storage.map(|(storage, _)| storage) == Some(node.1))
                .then(|| fact.target.depth2.clone())
                .flatten()
            })
            .chain(self.call_args.values().flat_map(|calls| {
                calls.iter().flat_map(|call| {
                    call.args.iter().filter_map(|argument| {
                        (call.caller == node.0
                            && argument.direct_storage.map(|(storage, _)| storage) == Some(node.1))
                        .then(|| argument.target.as_ref()?.depth2.clone())
                        .flatten()
                    })
                })
            }))
            .filter(|target| target.thin);
        let first = targets.next()?;
        targets.all(|target| target == first).then_some(first)
    }

    pub(crate) fn is_value_observation_candidate(&self, node: (LocalDefId, HirId)) -> bool {
        self.address_observations.iter().any(|observation| {
            observation
                .operands
                .iter()
                .any(|operand| operand.node == node)
        })
    }

    pub(crate) fn address_use_class(&self, node: (LocalDefId, HirId)) -> AddressUseClass {
        let value = self.is_value_observation_candidate(node);
        let access = self.raw_only_uses.get(&node).is_some_and(|uses| {
            uses.iter()
                .any(|(op, _)| !matches!(op.as_str(), "is_null" | "addr" | "offset_from"))
        });
        match (value, access) {
            (true, false) => AddressUseClass::ValueOnly,
            (false, true) => AddressUseClass::AccessOnly,
            (true, true) => AddressUseClass::Both,
            (false, false) => AddressUseClass::Neither,
        }
    }
}

#[cfg(test)]
mod address_use_tests {
    use rustc_hir::{CRATE_HIR_ID, def_id::CRATE_DEF_ID};

    use super::*;

    #[test]
    fn addr_n1_value_and_access_is_both_never_value_only() {
        let node = (CRATE_DEF_ID, CRATE_HIR_ID);
        let mut facts = EmitabilityFacts::default();
        facts.address_observations.push(AddressObservationFact {
            owner: CRATE_DEF_ID,
            span: rustc_span::DUMMY_SP,
            op: "ptr-to-int",
            target_type: "usize".to_owned(),
            operands: vec![AddressOperand {
                node,
                span: rustc_span::DUMMY_SP,
                target: RawTargetType {
                    rendered: "*const i32".to_owned(),
                    pointee: "i32".to_owned(),
                    mutability: RawMutability::Const,
                    depth2: None,
                },
            }],
        });
        facts
            .raw_only_uses
            .insert(node, vec![("offset".to_owned(), rustc_span::DUMMY_SP)]);
        assert_eq!(facts.address_use_class(node), AddressUseClass::Both);
    }
}

/// The arithmetic ops a borrowed-slice form can absorb.
///
/// A strict subset of [`RAW_ONLY_METHODS`], and deliberately narrower than the
/// §1(g) op table: only the two the addressable market actually carries. Adding
/// a member is adding a rewrite rule, so the list grows from evidence like its
/// parent does.
pub(crate) const SLICE_ARITHMETIC_OPS: &[&str] = &["offset", "offset_from"];

/// One rewritable use of a slice subject: the span to replace, and the text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct UseEdit {
    pub span: Span,
    pub replacement: String,
    pub bridge_kind: &'static str,
}

/// What a subject's uses permit.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SliceUses {
    pub rewrites: Vec<UseEdit>,
    /// A use that is **not** `*p.offset(e)`.
    ///
    /// Any such use blocks the whole subject. `&[T]` changes the type at every
    /// occurrence, so a rewrite that fixes the uses it recognizes and leaves the
    /// rest is not a partial win — it is an ill-typed crate.
    pub unsupported: Option<Span>,
}

/// Is `rhs` this binding's own pointer arithmetic — the right-hand side of a
/// self-advance?
fn self_advance_rhs(tcx: TyCtxt<'_>, rhs: &Expr<'_>, key: (LocalDefId, HirId)) -> Option<()> {
    let ExprKind::MethodCall(seg, receiver, _, _) = &rhs.kind else {
        return None;
    };
    if !SLICE_ARITHMETIC_OPS.contains(&seg.ident.name.to_string().as_str()) {
        return None;
    }
    let _ = tcx;
    self_advance_lhs(receiver, key).then_some(())
}

/// Does this expression name the binding `key` refers to?
fn self_advance_lhs(expr: &Expr<'_>, key: (LocalDefId, HirId)) -> bool {
    matches!(
        &expr.kind,
        ExprKind::Path(QPath::Resolved(_, path)) if matches!(path.res, Res::Local(id) if id == key.1)
    )
}

/// The index expression's source text, **typed as a `usize`**.
///
/// C2Rust writes `p.offset(i as isize)`; the `as isize` exists only to satisfy
/// `offset`, so stripping it recovers the author's index rather than inventing
/// a conversion.
///
/// # Stripping is not enough, and the corpus said so
///
/// The real idiom is a **double** cast — `p.offset(1 as libc::c_int as isize)` —
/// so stripping the outer cast leaves a `c_int`, and a slice indexed by `i32` is
/// `error[E0277]`. Measured: all 14 decided slices reverted, taking two sibling
/// `Ref` emissions down with them, because revert granularity is per function.
///
/// So the stripped expression's TYPE decides. Already `usize` — the shape
/// g11/g12 pin — renders bare, which is what keeps the ratified golden text
/// untouched rather than bending spec around a defect. Anything else is
/// parenthesised and cast: parenthesised because `i + 1 as usize` parses as
/// `i + (1 as usize)`.
///
/// **S3.2′-3: lifted out of the slice collector unchanged**, so the optional
/// slice twin renders indices by the same rule rather than by a second copy of
/// it. One canonicalizer, the standing rule.
fn index_text(tcx: TyCtxt<'_>, arg: &Expr<'_>) -> Option<String> {
    /// Is this expression already a `usize`?
    ///
    /// Asked of the type checker rather than of the syntax: `i`, `n as usize`
    /// and a `usize`-returning call are all bare-renderable and no syntactic
    /// test recognises the three.
    fn is_usize(tcx: TyCtxt<'_>, expr: &Expr<'_>) -> bool {
        let owner = expr.hir_id.owner.def_id;
        tcx.typeck(owner)
            .expr_ty_adjusted_opt(expr)
            .is_some_and(|t| {
                matches!(
                    t.kind(),
                    rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::Usize)
                )
            })
    }

    /// A non-negative integer LITERAL indexes bare.
    ///
    /// **S3.2′-2b.** `p.offset(1)`'s argument is an `isize` literal, so the
    /// type test below renders it `(1) as usize` — correct, and not what any
    /// human writes or what the ratified golden text says. A literal is
    /// representable as a `usize` when it is non-negative, and a negative one
    /// cannot reach here: the sign verdict gates that class to `SliceCursor`.
    ///
    /// This is a rendering rule, not a typing one, so it lives with the other
    /// rendering rules rather than as a special case at the reslice position —
    /// the same index expression must render the same way in every position.
    fn is_bare_literal(expr: &Expr<'_>) -> bool {
        matches!(&expr.kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(..)))
    }

    let sm = tcx.sess.source_map();
    if let ExprKind::Cast(inner, ty) = &arg.kind
        && let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, p)) = &ty.kind
        && p.segments
            .last()
            .is_some_and(|s| s.ident.name.as_str() == "isize")
    {
        let text = sm.span_to_snippet(inner.span).ok()?;
        return Some(if is_usize(tcx, inner) || is_bare_literal(inner) {
            text
        } else {
            format!("({text}) as usize")
        });
    }
    let text = sm.span_to_snippet(arg.span).ok()?;
    Some(if is_usize(tcx, arg) || is_bare_literal(arg) {
        text
    } else {
        format!("({text}) as usize")
    })
}

/// How many of a binding's uses are **not** the null test.
///
/// The multiplicity half of the idiom rule, needed *before* the collector runs
/// because it decides which accessor the collector substitutes. Counting the
/// same walk twice is the price of that ordering, and it is a cheap HIR pass —
/// the alternative is a collector that rewrites its own output after the fact.
pub(crate) fn non_test_use_count(tcx: TyCtxt<'_>, fn_did: LocalDefId, binding: HirId) -> usize {
    struct V<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        binding: HirId,
        count: &'a mut usize,
    }
    impl<'tcx> Visitor<'tcx> for V<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && let Res::Local(hir_id) = path.res
                && hir_id == self.binding
            {
                let is_null_test = matches!(
                    self.tcx.parent_hir_node(expr.hir_id),
                    rustc_hir::Node::Expr(p)
                        if matches!(
                            &p.kind,
                            ExprKind::MethodCall(seg, receiver, _, _)
                                if receiver.hir_id == expr.hir_id
                                    && seg.ident.name.as_str() == "is_null"
                        )
                );
                if !is_null_test {
                    *self.count += 1;
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
        return 0;
    };
    let mut count = 0;
    let mut v = V {
        tcx,
        binding,
        count: &mut count,
    };
    v.visit_body(tcx.hir_body(body_id));
    count
}

/// The two spellings one optional subject needs, because `unwrap()` and
/// `as_mut()` unwrap to different depths.
///
/// `Option<&T>::unwrap()` yields `&T` — one deref to the pointee.
/// `Option<&mut T>::as_mut().unwrap()` yields `&mut &mut T` — two. So the
/// dereferencing position needs an extra `*` in the second case, while the
/// indexing position needs none in either (indexing auto-derefs). Carrying both
/// spellings is what keeps that asymmetry out of the call sites.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Accessor {
    /// Substituted for the binding at a `*p` position.
    pub deref: String,
    /// The base, for `…[i]`.
    pub index: String,
}

/// **S3.2′-3 — what an OPTIONAL subject's uses permit.**
///
/// Same all-or-nothing contract as [`SliceUses`], and for a stronger reason:
/// `Option<&T>` changes the type at *every* occurrence, including the plain
/// `*p` a reference form left alone. There is no partial optional rewrite.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct OptUses {
    pub rewrites: Vec<UseEdit>,
    /// A use with no image under the wrapper.
    pub unsupported: Option<Span>,
    /// Uses that are not the null test — the multiplicity half of the idiom
    /// rule (micro-plan §9c).
    pub non_test_uses: usize,
}

/// Collect, per binding, the uses an **optional** form must rewrite.
///
/// # The two ratified idioms, and why the choice is not stylistic
///
/// - `Option<&T>` is `Copy`, so `unwrap()` may be spelled at every use.
/// - `Option<&mut T>` is **not**. `unwrap()` moves it — fine exactly once, which
///   is g02's ratified text, and ill-typed twice. More than one use therefore
///   takes `as_mut()`, which is g05's.
///
/// # One substitution, three positions
///
/// The edit replaces the **binding's own path expression**, not the enclosing
/// expression, so a single replacement text serves every dereferencing position:
///
/// | source | replacement of `p` | result |
/// |---|---|---|
/// | `*p` | `p.unwrap()` | `*p.unwrap()` |
/// | `*p = e` | `p.unwrap()` | `*p.unwrap() = e` |
/// | `(*p).f` | `p.unwrap()` | `(*p.unwrap()).f` |
/// | `*p` (mut, multi-use) | `*p.as_mut().unwrap()` | `**p.as_mut().unwrap()` |
///
/// The null test is the one exception: it replaces the whole call, because
/// `is_null` and `is_none` are different names — and `!p.is_null()` collapses to
/// `p.is_some()`, g05's spelling, rather than the correct-but-graceless
/// `!p.is_none()`.
pub(crate) fn collect_opt_uses(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    name_of: &FxHashMap<(LocalDefId, HirId), String>,
    accessor_of: &FxHashMap<(LocalDefId, HirId), Accessor>,
    fat: &rustc_hash::FxHashSet<(LocalDefId, HirId)>,
    raw_boundary_arguments: &rustc_hash::FxHashSet<(LocalDefId, HirId, u32, u32)>,
) -> FxHashMap<(LocalDefId, HirId), OptUses> {
    struct V<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        fn_did: LocalDefId,
        out: &'a mut FxHashMap<(LocalDefId, HirId), OptUses>,
        name_of: &'a FxHashMap<(LocalDefId, HirId), String>,
        accessor_of: &'a FxHashMap<(LocalDefId, HirId), Accessor>,
        fat: &'a rustc_hash::FxHashSet<(LocalDefId, HirId)>,
        raw_boundary_arguments: &'a rustc_hash::FxHashSet<(LocalDefId, HirId, u32, u32)>,
    }
    impl<'tcx> Visitor<'tcx> for V<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && let Res::Local(hir_id) = path.res
                && self.name_of.contains_key(&(self.fn_did, hir_id))
            {
                let key = (self.fn_did, hir_id);
                if self.raw_boundary_arguments.contains(&(
                    self.fn_did,
                    hir_id,
                    expr.span.lo().0,
                    expr.span.hi().0,
                )) {
                    self.out.entry(key).or_default().non_test_uses += 1;
                    intravisit::walk_expr(self, expr);
                    return;
                }
                let classified = self.classify(expr, key);
                let entry = self.out.entry(key).or_default();
                match classified {
                    Some((edit, is_non_test)) => {
                        entry.rewrites.push(edit);
                        entry.non_test_uses += usize::from(is_non_test);
                    }
                    None => {
                        entry.non_test_uses += 1;
                        if entry.unsupported.is_none() {
                            entry.unsupported = Some(expr.span);
                        }
                    }
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    impl V<'_, '_> {
        /// `Some((edit, is_a_non_test_use))`, or `None` for a use with no image.
        fn classify(
            &self,
            use_expr: &Expr<'_>,
            key: (LocalDefId, HirId),
        ) -> Option<(UseEdit, bool)> {
            let name = self.name_of.get(&key)?;
            let accessor = self.accessor_of.get(&key)?;
            let rustc_hir::Node::Expr(p) = self.tcx.parent_hir_node(use_expr.hir_id) else {
                return None;
            };
            match &p.kind {
                ExprKind::MethodCall(seg, receiver, _, _)
                    if receiver.hir_id == use_expr.hir_id
                        && seg.ident.name.as_str() == "is_null" =>
                {
                    if let rustc_hir::Node::Expr(not) = self.tcx.parent_hir_node(p.hir_id)
                        && matches!(not.kind, ExprKind::Unary(rustc_hir::UnOp::Not, _))
                    {
                        return Some((
                            UseEdit {
                                span: not.span,
                                replacement: format!("{name}.is_some()"),
                                bridge_kind: "raw-op-is-none",
                            },
                            false,
                        ));
                    }
                    Some((
                        UseEdit {
                            span: p.span,
                            replacement: format!("{name}.is_none()"),
                            bridge_kind: "raw-op-is-none",
                        },
                        false,
                    ))
                }
                ExprKind::Unary(rustc_hir::UnOp::Deref, _) => Some((
                    UseEdit {
                        span: use_expr.span,
                        replacement: accessor.deref.clone(),
                        bridge_kind: "subject-use",
                    },
                    true,
                )),
                // **The fat twin's arithmetic position.** `*p.offset(e)` on an
                // `Option<&[T]>` is `p.unwrap()[e]` — the -2 rewrite with the
                // wrapper's accessor in front of it, which is why the index is
                // rendered by the SAME `index_text` and not a second copy.
                //
                // Admitted only for subjects fatness licensed: on a thin
                // optional this position has no image, and falling through to
                // `None` is the correct refusal.
                ExprKind::MethodCall(seg, receiver, args, _)
                    if receiver.hir_id == use_expr.hir_id
                        && self.fat.contains(&key)
                        && SLICE_ARITHMETIC_OPS.contains(&seg.ident.name.to_string().as_str()) =>
                {
                    let [arg] = args else { return None };
                    let rustc_hir::Node::Expr(deref) = self.tcx.parent_hir_node(p.hir_id) else {
                        return None;
                    };
                    if !matches!(deref.kind, ExprKind::Unary(rustc_hir::UnOp::Deref, _)) {
                        return None;
                    }
                    // -2's accept-set restoration carries over verbatim: a
                    // BORROW of the deref is a third position, and it is not in
                    // scope here either.
                    if matches!(
                        self.tcx.parent_hir_node(deref.hir_id),
                        rustc_hir::Node::Expr(e) if matches!(e.kind, ExprKind::AddrOf(..))
                    ) {
                        return None;
                    }
                    let index = index_text(self.tcx, arg)?;
                    Some((
                        UseEdit {
                            span: deref.span,
                            replacement: format!("{}[{index}]", accessor.index),
                            bridge_kind: "subject-use",
                        },
                        true,
                    ))
                }
                _ => None,
            }
        }
    }

    let mut out = FxHashMap::default();
    for &fn_did in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
            continue;
        };
        let mut v = V {
            tcx,
            fn_did,
            out: &mut out,
            name_of,
            accessor_of,
            fat,
            raw_boundary_arguments,
        };
        v.visit_body(tcx.hir_body(body_id));
    }
    out
}

/// Collect, per binding, the `*p.offset(e)` uses and whether anything else uses
/// the binding at all.
///
/// **Total over uses, not over recognized uses** — the distinction is the whole
/// soundness argument. The walk visits every path expression resolving to a
/// local and classifies it; a use that does not match the rewritable shape sets
/// `unsupported` rather than being skipped.
pub(crate) fn collect_slice_uses(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    name_of: &FxHashMap<(LocalDefId, HirId), String>,
    mutable_of: &rustc_hash::FxHashSet<(LocalDefId, HirId)>,
    advance_ok: &rustc_hash::FxHashSet<(LocalDefId, HirId)>,
) -> FxHashMap<(LocalDefId, HirId), SliceUses> {
    struct V<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        fn_did: LocalDefId,
        out: &'a mut FxHashMap<(LocalDefId, HirId), SliceUses>,
        name_of: &'a FxHashMap<(LocalDefId, HirId), String>,
        mutable_of: &'a rustc_hash::FxHashSet<(LocalDefId, HirId)>,
        /// Subjects a self-advance may be emitted for: **non-negative sign**
        /// (the negative class is `SliceCursor`'s, S3.2′-5's) **and** a `mut`
        /// binding (`p = …` needs one). Both gates are decided where the facts
        /// live and handed here as one set.
        advance_ok: &'a rustc_hash::FxHashSet<(LocalDefId, HirId)>,
    }
    impl<'tcx> Visitor<'tcx> for V<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && let Res::Local(hir_id) = path.res
            {
                let key = (self.fn_did, hir_id);
                // Classify BEFORE taking the entry: `classify` reads `self`, and
                // holding the map entry across it would be a borrow conflict.
                let classified = self.classify(expr, key);
                let entry = self.out.entry(key).or_default();
                match classified {
                    // **S3.2′-2b — three outcomes, not two.** The self-advance
                    // assignment's TARGET (`p` on the left of `p = p.offset(1)`)
                    // is a use that is in scope and needs NO edit: the binding
                    // keeps its name. Folding it into the reject arm would make
                    // the whole subject unsupported; folding it into the accept
                    // arm would need an edit it does not have.
                    Some(Some(edit)) => entry.rewrites.push(edit),
                    Some(None) => {}
                    None => {
                        if entry.unsupported.is_none() {
                            entry.unsupported = Some(expr.span);
                        }
                    }
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    impl V<'_, '_> {
        /// `*p.offset(e)` — and nothing else — yields an edit.
        fn classify(
            &self,
            use_expr: &Expr<'_>,
            key: (LocalDefId, HirId),
        ) -> Option<Option<UseEdit>> {
            let name = self.name_of.get(&key)?;
            let parent = self.tcx.parent_hir_node(use_expr.hir_id);
            let rustc_hir::Node::Expr(call) = parent else {
                return None;
            };

            // **S3.2′-2b — the PLAIN dereference.** `*p` with no arithmetic
            // under it. On `&[T]` its image is `p[0]`, and it is admitted here
            // because the census showed it never occurs alone: every subject it
            // would unblock also self-advances, which is why the two positions
            // were ratified as one bundle.
            if matches!(call.kind, ExprKind::Unary(rustc_hir::UnOp::Deref, _)) {
                // -2's accept-set restoration, unchanged: a BORROW of the deref
                // is a third position and is still out of scope.
                if matches!(
                    self.tcx.parent_hir_node(call.hir_id),
                    rustc_hir::Node::Expr(e) if matches!(e.kind, ExprKind::AddrOf(..))
                ) {
                    return None;
                }
                return Some(Some(UseEdit {
                    span: call.span,
                    replacement: format!("{name}[0]"),
                    bridge_kind: "subject-use",
                }));
            }

            // **S3.2′-2b — the self-advance TARGET.** `p` on the left of
            // `p = p.offset(1)`. In scope, and it needs no edit: the binding
            // keeps its name. Admitted only when the right-hand side is this
            // same binding's own arithmetic, so an assignment FROM anything
            // else stays unsupported.
            if let ExprKind::Assign(lhs, rhs, _) = &call.kind
                && lhs.hir_id == use_expr.hir_id
            {
                if !self.advance_ok.contains(&key) {
                    return None;
                }
                return self_advance_rhs(self.tcx, rhs, key).map(|_| None);
            }

            let ExprKind::MethodCall(seg, receiver, args, _) = &call.kind else {
                return None;
            };
            if receiver.hir_id != use_expr.hir_id
                || !SLICE_ARITHMETIC_OPS.contains(&seg.ident.name.to_string().as_str())
            {
                return None;
            }
            let [arg] = args else { return None };
            let rustc_hir::Node::Expr(deref) = self.tcx.parent_hir_node(call.hir_id) else {
                return None;
            };

            // **S3.2′-2b — the self-advance SOURCE.** `p.offset(e)` on the right
            // of `p = …`. Its image is the reslice, and the `&mut` form is the
            // naive reborrow — compiler-witnessed on the pinned toolchain, so no
            // `mem::take` is needed. Under the NON-NEGATIVE sign verdict only;
            // the negative class is `SliceCursor`'s, which S3.2′-5 owns.
            if let ExprKind::Assign(lhs, rhs, _) = &deref.kind
                && rhs.hir_id == call.hir_id
                && lhs.hir_id != use_expr.hir_id
                && self_advance_lhs(lhs, key)
                && self.advance_ok.contains(&key)
            {
                let index = index_text(self.tcx, arg)?;
                let amp = if self.mutable_of.contains(&key) {
                    "&mut "
                } else {
                    "&"
                };
                return Some(Some(UseEdit {
                    span: call.span,
                    replacement: format!("{amp}{name}[{index}..]"),
                    bridge_kind: "subject-use",
                }));
            }

            if !matches!(deref.kind, ExprKind::Unary(rustc_hir::UnOp::Deref, _)) {
                return None;
            }
            // **SCOPE RESTORATION.** Amendment 1 authorises exactly two
            // positions — the deref READ and the deref WRITE. A BORROW of the
            // deref is a third, and this classifier accepted it because it
            // tested the deref's shape without testing its context.
            //
            // Measured on the corpus: `lodepng_chunk_data` reads
            // `return &mut *chunk.offset(8) as *mut c_uchar`, and rewriting it
            // gave `error[E0596]: cannot borrow chunk[_] as mutable, as it is
            // behind a & reference`.
            //
            // **Scope is whatever the classifier accepts.** The approved scope
            // and the accept-set are the same object, so the accept-set is
            // witnessed against the scope — positive controls for both
            // authorised positions, a negative control for each known
            // neighbour (borrow-of-deref, rebind, self-advance).
            if matches!(
                self.tcx.parent_hir_node(deref.hir_id),
                rustc_hir::Node::Expr(e) if matches!(e.kind, ExprKind::AddrOf(..))
            ) {
                return None;
            }
            let index = self.index_text(arg)?;
            Some(Some(UseEdit {
                span: deref.span,
                replacement: format!("{name}[{index}]"),
                bridge_kind: "subject-use",
            }))
        }

        /// The index expression's source text, **typed as a `usize`**.
        ///
        /// C2Rust writes `p.offset(i as isize)`; the `as isize` exists only to
        /// satisfy `offset`, so stripping it recovers the author's index rather
        /// than inventing a conversion.
        ///
        /// # Stripping is not enough, and the corpus said so
        ///
        /// The real idiom is a **double** cast — `p.offset(1 as libc::c_int as
        /// isize)` — so stripping the outer cast leaves a `c_int`, and a slice
        /// indexed by `i32` is `error[E0277]`. Measured: all 14 decided slices
        /// reverted, taking two sibling `Ref` emissions down with them, because
        /// revert granularity is per function.
        ///
        /// So the stripped expression's TYPE decides. Already `usize` — the
        /// shape g11/g12 pin — renders bare, which is what keeps the ratified
        /// golden text untouched rather than bending spec around a defect.
        /// Anything else is parenthesised and cast: parenthesised because
        /// `i + 1 as usize` parses as `i + (1 as usize)`.
        fn index_text(&self, arg: &Expr<'_>) -> Option<String> {
            index_text(self.tcx, arg)
        }
    }

    let mut out = FxHashMap::default();
    for &fn_did in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
            continue;
        };
        let mut v = V {
            tcx,
            fn_did,
            out: &mut out,
            name_of,
            mutable_of,
            advance_ok,
        };
        v.visit_body(tcx.hir_body(body_id));
    }
    out
}
