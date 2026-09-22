//! Thin references at multi-element LOCAL callee positions (seat addendum 364,
//! R364-2; adjudicated R365-1/2).
//!
//! [`super::thin_extent`] holds a thin `&T` that reaches a FOREIGN position
//! whose pinned contract consumes more than one element. Its own "not held"
//! list ends at local callees, on the ground that "a local callee's parameter
//! is a subject in its own right" — which is true of the CALLEE's slot and says
//! nothing about the caller's extent. [`super::void_pointee`] holds the
//! callee's `c_void` parameter and says of the other end that the caller then
//! "takes the ordinary raw-boundary bridge, whose pointer carries the caller
//! subject's own full extent". Both statements are true, and together they
//! leave exactly one hole: when the caller's subject is ITSELF thin, its "own
//! full extent" is one element, and a callee that accesses wider walks off it.
//!
//! brotli is the witness in both directions. `Hash14(data: &uint8_t)` bridges
//! into `BrotliUnalignedRead32(p: *const c_void)`, whose body is
//! `*(p as *const uint32_t)` — four bytes through a one-byte claim — and
//! `BrotliStoreMetaBlockHeader(storage: &mut uint8_t)` bridges into
//! `BrotliWriteBits(array: *mut uint8_t)`, which offsets and then calls
//! `BrotliUnalignedWrite64`: an EIGHT-byte WRITE. The class is therefore not a
//! read-extent class, which is why the hold names the ACCESS.
//!
//! **The predicate asks only "does this callee parameter access more than one
//! element", never "how many bytes versus how many".** That is the same shape
//! as both neighbours — `thin_extent` asks whether the contract's extent fits
//! one element, `void_pointee` asks whether the pointee is `c_void` — and it
//! needs no width arithmetic to be sound:
//!
//! - a `c_void` pointee carries no extent at all (R271-1), so the cast the
//!   callee performs to reach its real type is an access of unbounded width by
//!   that rule's own reasoning. The cast target is recorded in the receipt
//!   because it is the useful thing to read, not because the rule needs it;
//! - pointer arithmetic leaves a one-element claim by construction, whatever
//!   the element is.
//!
//! What is deliberately NOT held:
//!
//! - **`RawExpr` arguments.** `f(((*s).string_table.arr).offset(..))` roots at
//!   `s` under [`ArgShape::place_root`], but the pointer passed was READ OUT OF
//!   the referent and carries its own provenance; `s`'s extent does not bound
//!   it. Holding `s` would be holding on the wrong subject. Only shapes in
//!   which the argument DENOTES the subject — a bare binding, or that binding
//!   under casts — are in the class. The corpus sizing separated exactly three
//!   rows this way (one libtree, two lodepng).
//! - **`AddrOf` arguments.** `f(&mut p)` passes the ADDRESS of the subject
//!   binding, so the extent question belongs to the outer pointer, at depth 2.
//! - **`is_null` and the other observing raw-only uses.** They read the address
//!   and access nothing past it.
//! - **Slice-typed callee parameters.** A `&[T]` parameter carries its own
//!   checked extent; how that slice was CONSTRUCTED is the
//!   `FALLBACK_SLICE_EXTENT` waiver, receipted per site and out of scope by the
//!   2026-08-30 ruling (R365-2 keeps these 21 corpus rows a census item, not a
//!   hold).
//! - **Foreign callees.** They are [`super::thin_extent`]'s, decided by the
//!   pinned contract table so the classification stays in one place.

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, Node, def_id::LocalDefId};
use rustc_middle::ty::{Mutability, TyCtxt, TyKind};

use super::{
    Subject, SubjectKind,
    emitability::{ArgShape, EmitabilityFacts, SliceUses},
    void_pointee::{VOID_POINTEE_DEPTH, has_void_pointee},
};

/// Pointer arithmetic leaves a one-element claim by construction.
///
/// `is_null` and the other members of `RAW_ONLY_METHODS` observe the address
/// without accessing past it, so they are deliberately absent.
const EXTENT_LEAVING_OPS: &[&str] = &[
    "offset",
    "wrapping_offset",
    "add",
    "sub",
    "wrapping_add",
    "wrapping_sub",
    "offset_from",
];

/// Why one local callee parameter accesses more than one element.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AccessReason {
    /// The parameter's own pointee is `c_void` and the body casts it away to
    /// the type it actually wants. Carries that cast target, for the receipt.
    VoidPointee { cast_to: String },
    /// The body offsets or indexes the parameter.
    PointerArithmetic { op: String },
    /// The parameter accesses nothing itself and hands the pointer, bare, to
    /// a callee parameter that does (W-C9, fix-2 one call deeper: a thin
    /// caller bridged into the forwarder reads wide through a one-element
    /// claim exactly as it would at the accessing callee). Carries that
    /// parameter's own detail.
    Forwarded { into: String },
}

impl AccessReason {
    fn key(&self) -> String {
        match self {
            Self::VoidPointee { cast_to } => format!("void-pointee-cast-to:{cast_to}"),
            Self::PointerArithmetic { op } => format!("pointer-arithmetic:{op}"),
            Self::Forwarded { into } => format!("forwarded-into:{into}"),
        }
    }
}

/// The typed hold: which callee, which parameter, read or write, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LocalCalleeAccess {
    pub(crate) callee_id: LocalDefId,
    pub(crate) parameter_index: usize,
    pub callee: String,
    pub parameter: String,
    /// `read` or `write`, from the callee parameter's own pointee mutability.
    /// Six of the twenty corpus sites are writes; a class named for reads would
    /// have mis-described them.
    pub access: &'static str,
    pub reason: AccessReason,
}

impl LocalCalleeAccess {
    /// `callee:parameter:access:reason` — the four things R365-1 requires.
    pub(crate) fn detail(&self) -> String {
        format!(
            "{}:{}:{}:{}",
            self.callee,
            self.parameter,
            self.access,
            self.reason.key()
        )
    }
}

/// Does this argument expression DENOTE the subject, so that the pointer handed
/// over is a view of the subject's own referent?
///
/// See the module note: `RawExpr` and `AddrOf` are excluded, and for reasons
/// that differ, so they are matched out explicitly rather than by falling
/// through [`ArgShape::place_root`].
fn subject_denoting_root(shape: ArgShape) -> Option<HirId> {
    match shape {
        ArgShape::BareLocal(id) | ArgShape::CastOfLocal { binding: id, .. } => Some(id),
        _ => None,
    }
}

/// How the callee's body accesses this parameter, if it accesses past one
/// element at all.
fn parameter_access(
    tcx: TyCtxt<'_>,
    param: &Subject,
    facts: &EmitabilityFacts,
    slice_uses: &FxHashMap<(LocalDefId, HirId), SliceUses>,
    parameters: &FxHashMap<(LocalDefId, usize), &Subject>,
    cursor_candidates: &CursorCandidates,
    decided: Option<&DecidedForms>,
    visited: &mut Vec<(LocalDefId, HirId)>,
) -> Option<LocalCalleeAccess> {
    let Node::Pat(pattern) = tcx.hir_node(param.hir_id) else {
        return None;
    };
    // **R365-2 — a slice-shaped callee parameter is out of the class.** Read
    // before anything else, because the arithmetic arm below would otherwise
    // claim exactly these: at decision time the parameter is still raw and its
    // uses are still `*p.offset(e)`, and the whole point of a slice candidate
    // is that every one of those becomes a CHECKED index on a form carrying its
    // own extent. What stays open for them is how the slice was CONSTRUCTED,
    // which is the `FALLBACK_SLICE_EXTENT` waiver, receipted per site and
    // ruled a census item rather than a hold. (W-C9 report 017 sizes the
    // THIN-caller side of this exclusion — `from_ref` into a wide reader —
    // for the seat; it is not moved here.)
    // **R491-7 — a C-STRING walk is not this hold's class.** The callee reads
    // one byte at a time to a NUL, so what it accesses is a string, and the
    // extent of a string is a fact the caller can state — exactly
    // (`strlen + 1`, where the walk provably reaches the NUL or the pointer is
    // handed to a libc string function) or under §77's fallback with its
    // receipt (where the walk can stop early). Both are extents; neither is the
    // one-element claim the hold exists to protect.
    // **R517-11 — and it yields to a cursor CANDIDATE, read in this pass.** A
    // parameter the cursor family can admit keeps its caller's hold: two cursor
    // deliveries are not worth one string extent (wave-5c 046 §3). R505-2 read
    // that off the SETTLED decision, which needed a second pass — and a row
    // lifted by a second pass is decided but never planned, so it does not
    // place and its siblings fall with it (047 §2, measured −3 on libtree). The
    // candidate set carries the same intent from facts that exist before any
    // decision, so the lift happens in the FIRST pass and the planning sees it.
    if let SubjectKind::Param { hir_index } = param.kind
        && !cursor_candidates.contains(&(param.fn_did, hir_index))
        && nul_walk(tcx, param, facts).is_some()
    {
        return None;
    }
    if slice_uses
        .get(&(param.fn_did, param.hir_id))
        .is_some_and(|uses| {
            uses.unsupported.is_none()
                && !uses.rewrites.is_empty()
                && !super::slice_return_evidence::needs_full_base(tcx, param, uses)
        })
    {
        return None;
    }
    let ty = tcx.typeck(param.fn_did).pat_ty(pattern);
    let key = (param.fn_did, param.hir_id);
    let reason = if has_void_pointee(tcx, ty, VOID_POINTEE_DEPTH) {
        // A `c_void` parameter is held on its own account by R271-1; what puts
        // the CALLER in this class is the cast that follows, which is the
        // evidence that the opaque address is accessed at some real width. A
        // `c_void` parameter that is only passed on or compared accesses
        // nothing and is not in scope.
        let cast = facts.address_observations.iter().find(|fact| {
            fact.op == "ptr-cast" && fact.operands.iter().any(|operand| operand.node == key)
        })?;
        AccessReason::VoidPointee {
            cast_to: cast.target_type.clone(),
        }
    } else if let Some((op, _)) = facts.raw_only_uses.get(&key).and_then(|uses| {
        uses.iter()
            .find(|(op, _)| EXTENT_LEAVING_OPS.contains(&op.as_str()))
    }) {
        AccessReason::PointerArithmetic { op: op.clone() }
    } else {
        // No access of its own: the first callee parameter it is handed to,
        // bare, that accesses wide (a cycle accesses nothing).
        if visited.contains(&key) {
            return None;
        }
        visited.push(key);
        let into = facts
            .call_args
            .iter()
            .flat_map(|(callee, sites)| sites.iter().map(move |site| (*callee, site)))
            .filter(|(_, site)| site.caller == param.fn_did)
            .flat_map(|(callee, site)| site.args.iter().map(move |arg| (callee, arg)))
            .filter(|(_, arg)| matches!(arg.shape, ArgShape::BareLocal(binding) if binding == param.hir_id))
            .find_map(|(callee, arg)| {
                let target = parameters.get(&(callee, arg.index))?;
                parameter_access(
                    tcx,
                    target,
                    facts,
                    slice_uses,
                    parameters,
                    cursor_candidates,
                    decided,
                    visited,
                )
            })?;
        AccessReason::Forwarded {
            into: into.detail(),
        }
    };
    let access = match ty.kind() {
        TyKind::RawPtr(_, Mutability::Mut) | TyKind::Ref(_, _, Mutability::Mut) => "write",
        _ => "read",
    };
    Some(LocalCalleeAccess {
        callee_id: param.fn_did,
        parameter_index: match param.kind {
            SubjectKind::Param { hir_index } => hir_index,
            SubjectKind::Local => unreachable!("local callee access is classified on a parameter"),
        },
        callee: tcx.def_path_str(param.fn_did.to_def_id()),
        parameter: param
            .param_name
            .clone()
            .unwrap_or_else(|| "<unnamed>".to_owned()),
        access,
        reason,
    })
}

/// **R491-7 — a local callee that reads a C STRING.**
///
/// `is_float(p)` and `print_colon_delimited_paths(start)` walk their parameter
/// one byte at a time to its NUL. That is an element-wise access, so the hold's
/// "accesses past one element" is true of it — and unlike the wide readers the
/// hold is for, the extent it accesses is a fact the CALLER can state: the
/// string. Which form that takes is the seat's ruling (addendum 491):
///
/// - [`Exact`](NulWalk::Exact) — the walk provably reaches the NUL on every
///   path, or the pointer is handed to a libc string function whose contract
///   requires a terminated string. `strlen(p) + 1` is then evidence: on a
///   UB-free input (§28) the terminator is there, and `strlen` reads exactly
///   the bytes the callee would.
/// - [`Fallback`](NulWalk::Fallback) — the walk can stop before the NUL, so
///   `strlen` at the caller could read bytes the input never reads. The §77
///   fallback extent with its receipt is what that takes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NulWalk {
    Exact,
    Fallback,
}

/// The libc string functions whose contract requires a NUL-terminated argument.
/// A pointer handed to one of these is terminated on a UB-free input, which is
/// what licenses the exact form even when the callee's own loop can exit early.
const NUL_CONTRACT_CALLEES: &[&str] = &[
    "strlen",
    "strchr",
    "strrchr",
    "strcmp",
    "strcasecmp",
    "strncmp",
    "strncasecmp",
    "strcpy",
    "strcat",
    "strstr",
    "strdup",
    "puts",
    "atoi",
    "atol",
    "atof",
    "strtol",
    "strtod",
];

/// Does this parameter's body walk it, byte at a time, to a NUL?
pub(crate) fn nul_walk(
    tcx: TyCtxt<'_>,
    param: &Subject,
    facts: &EmitabilityFacts,
) -> Option<NulWalk> {
    use rustc_hir::intravisit::Visitor;

    let key = (param.fn_did, param.hir_id);
    // Byte-at-a-time: the pointee is one byte wide, and the only arithmetic on
    // it is `offset`/`add` — an INDEXED read (`*p.offset(i)`) is a count
    // question, not a string one.
    let Node::Pat(pattern) = tcx.hir_node(param.hir_id) else {
        return None;
    };
    let ty = tcx.typeck(param.fn_did).pat_ty(pattern);
    let TyKind::RawPtr(pointee, _) = ty.kind() else { return None };
    if !matches!(
        pointee.kind(),
        TyKind::Int(rustc_middle::ty::IntTy::I8) | TyKind::Uint(rustc_middle::ty::UintTy::U8)
    ) {
        return None;
    }
    // A cast of the cursor to a wider type reads more than a byte at it.
    if facts.address_observations.iter().any(|fact| {
        fact.op == "ptr-cast" && fact.operands.iter().any(|operand| operand.node == key)
    }) {
        return None;
    }

    struct Walk<'tcx> {
        tcx: TyCtxt<'tcx>,
        binding: HirId,
        nul_tested: bool,
        early_exit: bool,
        libc_contract: bool,
        indexed: bool,
    }
    /// `*p`, `*p as i32`, `(*p)` — the cursor's own byte, however the C
    /// spelling casts it.
    fn derefs_the_cursor(expr: &rustc_hir::Expr<'_>, binding: HirId) -> bool {
        let mut expr = expr;
        loop {
            match expr.kind {
                rustc_hir::ExprKind::Cast(inner, _) | rustc_hir::ExprKind::DropTemps(inner) => {
                    expr = inner;
                }
                rustc_hir::ExprKind::Unary(rustc_hir::UnOp::Deref, inner) => {
                    return names(inner, binding);
                }
                _ => return false,
            }
        }
    }
    /// `1`, `1 as isize`, `(1)` — a constant step. Anything naming a value is
    /// not.
    fn literal_step(expr: &rustc_hir::Expr<'_>) -> bool {
        let mut expr = expr;
        loop {
            match expr.kind {
                rustc_hir::ExprKind::Cast(inner, _) | rustc_hir::ExprKind::DropTemps(inner) => {
                    expr = inner;
                }
                rustc_hir::ExprKind::Lit(_) => return true,
                _ => return false,
            }
        }
    }
    /// `0`, `0 as c_int`, `'\0'`, `'\0' as i32` — the terminator, in the
    /// spellings C and c2rust use for it.
    fn is_zero(expr: &rustc_hir::Expr<'_>) -> bool {
        let mut expr = expr;
        loop {
            match expr.kind {
                rustc_hir::ExprKind::Cast(inner, _) | rustc_hir::ExprKind::DropTemps(inner) => {
                    expr = inner;
                }
                rustc_hir::ExprKind::Lit(literal) => {
                    return match literal.node {
                        rustc_ast::LitKind::Int(value, _) => value.get() == 0,
                        rustc_ast::LitKind::Char(ch) => ch == '\0',
                        _ => false,
                    };
                }
                _ => return false,
            }
        }
    }
    fn names(expr: &rustc_hir::Expr<'_>, binding: HirId) -> bool {
        struct Names {
            binding: HirId,
            found: bool,
        }
        impl<'tcx> Visitor<'tcx> for Names {
            fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
                if let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = expr.kind
                    && let rustc_hir::def::Res::Local(id) = path.res
                    && id == self.binding
                {
                    self.found = true;
                }
                rustc_hir::intravisit::walk_expr(self, expr);
            }
        }
        let mut visitor = Names {
            binding,
            found: false,
        };
        visitor.visit_expr(expr);
        visitor.found
    }
    impl<'tcx> Visitor<'tcx> for Walk<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            match expr.kind {
                // `while *p != 0` — the loop the string ends. **Both halves
                // are required** (R497-3(a)): a deref of the cursor on one side
                // and a ZERO on the other. Without the zero, `*p1.offset(0) ==
                // *p2.offset(0)` — a byte comparison between two buffers —
                // reads as a string walk, and the extent it licenses scans past
                // whatever the input actually read.
                rustc_hir::ExprKind::Binary(op, left, right)
                    if matches!(op.node, rustc_hir::BinOpKind::Ne | rustc_hir::BinOpKind::Eq)
                        && ((derefs_the_cursor(left, self.binding) && is_zero(right))
                            || (derefs_the_cursor(right, self.binding) && is_zero(left))) =>
                {
                    self.nul_tested = true;
                }
                // `*p.offset(i)` with a non-literal index is a COUNT walk.
                rustc_hir::ExprKind::MethodCall(segment, receiver, [index], _)
                    if EXTENT_LEAVING_OPS.contains(&segment.ident.name.as_str())
                        && names(receiver, self.binding) =>
                {
                    // A CAST of a literal is still a literal step
                    // (`p.offset(1 as isize)`); a cast of a variable is not
                    // (`p.offset(i as isize)`), and that is a count walk.
                    if !literal_step(index) {
                        self.indexed = true;
                    }
                }
                rustc_hir::ExprKind::Call(callee, args) => {
                    let name = match callee.kind {
                        rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => path
                            .segments
                            .last()
                            .map(|segment| segment.ident.name.to_string()),
                        _ => None,
                    };
                    if let Some(name) = name
                        && NUL_CONTRACT_CALLEES.contains(&name.as_str())
                        && args.iter().any(|arg| names(arg, self.binding))
                    {
                        self.libc_contract = true;
                    }
                }
                // A `return` inside the walk can leave it before the NUL.
                rustc_hir::ExprKind::Ret(_) | rustc_hir::ExprKind::Break(..) => {
                    self.early_exit = true;
                }
                _ => {}
            }
            rustc_hir::intravisit::walk_expr(self, expr);
        }
    }

    let body = tcx.hir_body_owned_by(param.fn_did);
    let mut walk = Walk {
        tcx,
        binding: param.hir_id,
        nul_tested: false,
        early_exit: false,
        libc_contract: false,
        indexed: false,
    };
    walk.visit_body(&body);
    let _ = walk.tcx;
    if !walk.nul_tested || walk.indexed {
        return None;
    }
    Some(if walk.libc_contract || !walk.early_exit {
        NulWalk::Exact
    } else {
        NulWalk::Fallback
    })
}

/// **R491-7's caller-side clause (relay 060).** The exact form is licensed by
/// the CALLEE's own walk — or by the caller, when the caller hands the same
/// pointer to a libc string function. `is_bool_str(str, ..)` calls
/// `strcasecmp(str, "true")` before it reaches `is_float(str)`, and
/// `strcasecmp`'s contract requires a terminated string: on a UB-free input
/// (§28) the terminator is there, so the string's own length reads exactly the
/// bytes the program already reads.
///
/// **The same discipline as the callee side.** A libc STRING function, by name,
/// with this very binding as an argument — never a counted call (`memcpy`,
/// `strncpy`), which says nothing about a terminator, and never a comparison
/// against another byte.
pub(crate) fn caller_establishes_nul(tcx: TyCtxt<'_>, subject: &Subject) -> bool {
    use rustc_hir::intravisit::Visitor;

    struct Calls {
        binding: HirId,
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for Calls {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            if let rustc_hir::ExprKind::Call(callee, args) = expr.kind
                && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = callee.kind
                && path.segments.last().is_some_and(|segment| {
                    NUL_CONTRACT_CALLEES.contains(&segment.ident.name.as_str())
                })
                && args.iter().any(|arg| {
                    let mut arg = arg;
                    loop {
                        match arg.kind {
                            rustc_hir::ExprKind::Cast(inner, _)
                            | rustc_hir::ExprKind::DropTemps(inner) => arg = inner,
                            rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
                                return path.res == rustc_hir::def::Res::Local(self.binding);
                            }
                            _ => return false,
                        }
                    }
                })
            {
                self.found = true;
            }
            rustc_hir::intravisit::walk_expr(self, expr);
        }
    }

    if !tcx.hir_body_owners().any(|did| did == subject.fn_did) {
        return false;
    }
    let body = tcx.hir_body_owned_by(subject.fn_did);
    let mut calls = Calls {
        binding: subject.hir_id,
        found: false,
    };
    calls.visit_body(&body);
    calls.found
}

/// **The decisions a second pass may read** (R485-4(b)). Absent on the FIRST
/// pass, where nothing is decided yet. The C-string exemption no longer reads
/// this: it takes the pre-decision [`CursorCandidates`] instead (R517-11), so
/// that lift happens in the first pass and its rows are planned.
#[derive(Debug, Default)]
pub(crate) struct DecidedForms {
    /// Parameters decided `Slice` — a checked extent at the callee.
    pub(crate) slice: rustc_hash::FxHashSet<(LocalDefId, usize)>,
}

/// **Callee parameters the cursor family can admit** (R517-11), keyed by
/// `(callee, parameter index)` and derived in `bo_rewriter::mod` from the facts
/// that exist BEFORE any decision — the BO model's kind for the slot, and the
/// slice-use / offset-sign verdicts the three reasons
/// `cursor_native::is_cursor_reason` admits from. It is a CANDIDATE set, not a
/// delivery: a parameter in it may still fail the family's own plan. That is
/// the conservative direction for this rule, which uses it only to KEEP a hold.
pub(crate) type CursorCandidates = rustc_hash::FxHashSet<(LocalDefId, usize)>;

/// **The candidate predicate itself** (R517-11), pure, so each conjunct answers
/// for itself. `cursor_native::promote` admits a degraded subject on three
/// reasons; `SliceCursorUse` and `SliceUseUnsupported` are both
/// `SliceUses::unsupported`, and `SliceNegOrUnknownOffset` is the offset-sign
/// refusal the caller passes in. Every one of them sits BELOW BO's kind in the
/// ladder, which is why the kind is read first and alone decides a `Raw` slot:
/// such a subject degrades at `kind-raw`, and the family then reaches it only
/// through a DELIVERED base — which a bare C-string walk never has.
pub(crate) fn is_cursor_candidate(
    model_kind: Option<crate::analyses::borrow_ownership::SlotKind>,
    uses: Option<&SliceUses>,
    sign_refuses: bool,
) -> bool {
    if model_kind != Some(crate::analyses::borrow_ownership::SlotKind::Ref) {
        return false;
    }
    uses.is_some_and(|uses| uses.unsupported.is_some()) || sign_refuses
}

/// Caller subjects handed to such a position. A subject in this map may not
/// take a THIN reference form.
pub(crate) fn collect(
    tcx: TyCtxt<'_>,
    subjects: &[Subject],
    facts: &EmitabilityFacts,
    slice_uses: &FxHashMap<(LocalDefId, HirId), SliceUses>,
    cursor_candidates: &CursorCandidates,
    decided: Option<&DecidedForms>,
    fat: Option<&crate::bo_rewriter::fat_facts::FatFacts>,
) -> FxHashMap<(LocalDefId, HirId), LocalCalleeAccess> {
    let mut parameters: FxHashMap<(LocalDefId, usize), &Subject> = FxHashMap::default();
    let mut by_binding: FxHashMap<(LocalDefId, HirId), &Subject> = FxHashMap::default();
    for subject in subjects {
        if let SubjectKind::Param { hir_index } = subject.kind {
            parameters.insert((subject.fn_did, hir_index), subject);
        }
        by_binding.insert((subject.fn_did, subject.hir_id), subject);
    }
    // One classification per callee parameter, reused across its call sites:
    // the body is a property of the callee, not of any one caller.
    let mut classified: FxHashMap<(LocalDefId, usize), Option<LocalCalleeAccess>> =
        FxHashMap::default();
    let mut out = FxHashMap::default();
    for (callee, sites) in &facts.call_args {
        for site in sites {
            for arg in &site.args {
                let Some(root) = subject_denoting_root(arg.shape) else {
                    continue;
                };
                let Some(parameter) = parameters.get(&(*callee, arg.index)) else {
                    continue;
                };
                let access = classified.entry((*callee, arg.index)).or_insert_with(|| {
                    parameter_access(
                        tcx,
                        parameter,
                        facts,
                        slice_uses,
                        &parameters,
                        cursor_candidates,
                        decided,
                        &mut vec![],
                    )
                });
                if let Some(access) = access {
                    // **R485-4(b) — the decided-`Slice` callee, narrowly.** A
                    // parameter this run decided `Slice` carries a checked
                    // extent for its INDEXES. That is not the whole of what
                    // this hold protects, and the first build proved it: a
                    // callee that casts its parameter to a wider type and
                    // writes through it (`*(p as *mut u64) = 7`) is not bounded
                    // by any `[u8]`, and a thin caller filling that slice hands
                    // over one element either way. So the exemption is taken
                    // only where all three hold:
                    //   * the callee parameter is decided `Slice`;
                    //   * its slice USES are element-width and rewritable — the
                    //     conjuncts R365-2 already trusts — and the one thing
                    //     that kept it out of that exemption is
                    //     `needs_full_base`, i.e. it hands its base on rather
                    //     than reading past its own claim;
                    //   * the CALLER's own subject is an array, so its form has
                    //     an extent to fill the slice with.
                    let element_width = slice_uses
                        .get(&(parameter.fn_did, parameter.hir_id))
                        .is_some_and(|uses| {
                            uses.unsupported.is_none() && !uses.rewrites.is_empty()
                        });
                    let caller_is_fat = fat
                        .zip(by_binding.get(&(site.caller, root)))
                        .is_some_and(|(fat, subject)| fat.is_array(subject.fn_did, subject.local));
                    if decided.is_some_and(|decided| decided.slice.contains(&(*callee, arg.index)))
                        && element_width
                        && caller_is_fat
                    {
                        continue;
                    }
                    out.entry((site.caller, root))
                        .or_insert_with(|| access.clone());
                }
            }
        }
    }
    out
}

/// **R485-4(b) — the second pass, as a function.** Re-collects the holds with
/// every parameter the settled table decided `Slice` exempted, and answers
/// `Some` only when that actually removes a hold: the caller re-decides on
/// `Some` and does nothing on `None`, so a run in which no callee parameter
/// became a slice costs one collect and no second ladder.
pub(crate) fn relaxed_by_decisions(
    tcx: TyCtxt<'_>,
    subjects: &[Subject],
    facts: &EmitabilityFacts,
    slice_uses: &FxHashMap<(LocalDefId, HirId), SliceUses>,
    cursor_candidates: &CursorCandidates,
    fat: &crate::bo_rewriter::fat_facts::FatFacts,
    decided: &DecidedForms,
    current: &FxHashMap<(LocalDefId, HirId), LocalCalleeAccess>,
) -> Option<FxHashMap<(LocalDefId, HirId), LocalCalleeAccess>> {
    let relaxed = collect(
        tcx,
        subjects,
        facts,
        slice_uses,
        cursor_candidates,
        Some(decided),
        Some(fat),
    );
    (relaxed.len() < current.len()).then_some(relaxed)
}

#[cfg(test)]
mod decided_slice_tests {
    use super::*;

    /// `caller::p` is held because `local_read` walks past one element; its
    /// callee parameter's slice USES do not exempt it (the walk is
    /// `p.wrapping_add(n)`, not an indexable rewrite), which is what leaves the
    /// hold in place. That is the corpus shape in miniature — the exemption's
    /// three conjuncts fall short at collect time — and the only thing R485-4(b)
    /// adds is the decision.
    const HELD: &str = r#"
#![allow(dead_code, unused_unsafe)]
unsafe fn local_read(p: *const u8, n: usize) -> u8 {
    let end = p.wrapping_add(n);
    *end.wrapping_sub(1)
}
pub unsafe fn caller(p: *const u8, n: usize) -> u8 {
    *p.offset(1) + local_read(p, n)
}
"#;

    /// **Control (ii) — a THIN caller keeps the hold.** This is the line the
    /// first build crossed: `read32(data as *const c_void)` with
    /// `data: *const u8` reads four bytes through a one-element claim, and the
    /// callee's parameter being a slice does not give the CALLER an extent to
    /// fill it with. R364-2's own witnesses pin this, and the corpus rows the
    /// exemption is for are array callers, not thin ones.
    #[test]
    fn w5c_r485_a_thin_caller_keeps_the_hold() {
        const THIN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables)]
pub unsafe fn read32(p: *const core::ffi::c_void) -> u32 { *(p as *const u32) }
pub unsafe fn hash(data: *const u8) -> u32 { read32(data as *const core::ffi::c_void) }
"#;
        let held = ::utils::compilation::run_compiler_on_str(THIN, |tcx| {
            let owners = tcx
                .hir_body_owners()
                .filter(|did| matches!(tcx.def_kind(*did), rustc_hir::def::DefKind::Fn))
                .collect::<Vec<_>>();
            let facts = super::super::emitability::collect(tcx, &owners);
            let table = crate::bo_rewriter::decide_table(tcx).expect("fixture decisions");
            let subjects = table
                .entries
                .iter()
                .map(|(subject, _)| subject.clone())
                .collect::<Vec<_>>();
            let program = crate::bo_rewriter::collect_program(tcx);
            let fat = crate::bo_rewriter::fat_facts::FatFacts::from_program(&program);
            let decided = subjects
                .iter()
                .filter(|subject| subject.label == "read32::p")
                .filter_map(|subject| match subject.kind {
                    SubjectKind::Param { hir_index } => Some((subject.fn_did, hir_index)),
                    SubjectKind::Local => None,
                })
                .collect::<rustc_hash::FxHashSet<_>>();
            assert_eq!(decided.len(), 1, "the reader's parameter resolves");
            collect(
                tcx,
                &subjects,
                &facts,
                &FxHashMap::default(),
                &CursorCandidates::default(),
                Some(&DecidedForms { slice: decided }),
                Some(&fat),
            )
            .into_iter()
            .map(|((owner, _), access)| {
                format!("{}:{}", tcx.item_name(owner.to_def_id()), access.detail())
            })
            .collect::<Vec<_>>()
        })
        .unwrap();
        assert!(
            held.iter().any(|row| row.starts_with("hash:read32:p:")),
            "a one-element source must keep the hold whatever its callee decided: {held:?}"
        );
    }
}

#[cfg(test)]
mod nul_walk_tests {
    use super::*;

    /// libtree's shape: the callee walks to the NUL and hands the pointer to
    /// libc string functions on the way (`strchr`, `puts`), whose contracts
    /// require a terminated string — so a UB-free input is terminated (§28) and
    /// the caller's extent is `strlen + 1`, exactly.
    const LIBC_WALK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe extern "C" { fn strchr(s: *const i8, c: i32) -> *mut i8; fn puts(s: *const i8) -> i32; }
unsafe fn walk(mut start: *const i8) {
    while *start as i32 != 0 {
        let next = strchr(start, ':' as i32);
        if start == next { start = start.offset(1); } else { puts(start); return; }
    }
}
pub unsafe fn caller(runpath: *const i8) { walk(runpath); }
"#;

    /// binn's shape: the walk can stop before the NUL (`else { return 0 }`), so
    /// `strlen` at the caller could read bytes the input never reads — the §77
    /// fallback, receipted, is what that takes.
    const EARLY_EXIT_WALK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe fn is_float(mut p: *const i8) -> i32 {
    while *p as i32 != 0 {
        if *p as i32 >= '0' as i32 && *p as i32 <= '9' as i32 {} else { return 0 }
        p = p.offset(1);
    }
    1
}
pub unsafe fn caller(str: *const i8) -> i32 { is_float(str) }
"#;

    fn walk_of(input: &str, callee: &str) -> Option<NulWalk> {
        ::utils::compilation::run_compiler_on_str(input, |tcx| {
            let owners = tcx
                .hir_body_owners()
                .filter(|did| matches!(tcx.def_kind(*did), rustc_hir::def::DefKind::Fn))
                .collect::<Vec<_>>();
            let facts = super::super::emitability::collect(tcx, &owners);
            let table = crate::bo_rewriter::decide_table(tcx).expect("fixture decisions");
            let subject = table
                .entries
                .iter()
                .map(|(subject, _)| subject)
                .find(|subject| subject.label == callee)
                .unwrap_or_else(|| panic!("{callee}"))
                .clone();
            nul_walk(tcx, &subject, &facts)
        })
        .unwrap()
    }

    /// **The shape** — a NUL walk that hands the pointer to libc string
    /// functions takes the EXACT extent.
    #[test]
    fn w5c_nul_a_libc_string_walk_is_exact() {
        assert_eq!(walk_of(LIBC_WALK, "walk::start"), Some(NulWalk::Exact));
    }

    /// **The other branch** — a walk that can stop before the NUL takes the
    /// ruled fallback, because `strlen` at the caller would read further than
    /// the input does.
    #[test]
    fn w5c_nul_an_early_exit_walk_takes_the_fallback() {
        assert_eq!(
            walk_of(EARLY_EXIT_WALK, "is_float::p"),
            Some(NulWalk::Fallback)
        );
    }

    /// **The hold is lifted for both branches** — the extent differs, the class
    /// does not. This is the rule's effect at the caller, which is what the two
    /// corpus rows wait on.
    #[test]
    fn w5c_nul_the_caller_is_not_held_for_a_string_walk() {
        for (input, callee) in [(LIBC_WALK, "walk"), (EARLY_EXIT_WALK, "is_float")] {
            let held = ::utils::compilation::run_compiler_on_str(input, |tcx| {
                let owners = tcx
                    .hir_body_owners()
                    .filter(|did| matches!(tcx.def_kind(*did), rustc_hir::def::DefKind::Fn))
                    .collect::<Vec<_>>();
                let facts = super::super::emitability::collect(tcx, &owners);
                let table = crate::bo_rewriter::decide_table(tcx).expect("fixture decisions");
                let subjects = table
                    .entries
                    .iter()
                    .map(|(subject, _)| subject.clone())
                    .collect::<Vec<_>>();
                let program = crate::bo_rewriter::collect_program(tcx);
                let fat = crate::bo_rewriter::fat_facts::FatFacts::from_program(&program);
                collect(
                    tcx,
                    &subjects,
                    &facts,
                    &FxHashMap::default(),
                    &CursorCandidates::default(),
                    Some(&DecidedForms::default()),
                    Some(&fat),
                )
                .into_iter()
                .map(|(_, access)| access.detail())
                .collect::<Vec<_>>()
            })
            .unwrap();
            assert!(
                !held.iter().any(|detail| detail.starts_with(callee)),
                "{callee}: a C-string walk must not hold its caller: {held:?}"
            );
        }
    }

    /// **The emitted length**, for the licensed branch: the caller constructs
    /// the slice with `strlen + 1`, not the fallback const.
    #[test]
    fn w5c_nul_the_licensed_branch_emits_strlen_plus_one() {
        let emitted =
            crate::bo_rewriter::emit_tests::ast_emitted_source_of(LIBC_WALK).expect("emission");
        let flat = emitted.split_whitespace().collect::<String>();
        if flat.contains("from_raw_parts") {
            assert!(
                flat.contains("CStr::from_ptr") && flat.contains("wrapping_add(1)"),
                "a licensed C-string extent is `strlen + 1`: {emitted}"
            );
            assert!(
                !flat.contains("FALLBACK_SLICE_EXTENT"),
                "and it is not the fallback: {emitted}"
            );
        }
        assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    }

    /// **Control (R497-3(a), slicecursor 052's defect)** — a callee that
    /// COMPARES two buffers byte for byte has a deref of the cursor on one side
    /// of an `==`, no loop, no NUL and no zero anywhere. The first build read
    /// that as a C-string walk and licensed the exact extent, so the emitted
    /// program scanned for a terminator past a 32-byte array the input only
    /// read at two indices — a new out-of-bounds read on a UB-free input, which
    /// neither §28 (the input never touched those bytes) nor §77 (it waives a
    /// slice's LENGTH, not an unbounded scan that computes one) covers.
    ///
    /// The rule this restores is the one its own doc comment states: the loop
    /// the string ends is `*p != 0`, so the other side of the comparison must
    /// be a ZERO literal.
    #[test]
    fn w5c_nul_a_byte_comparison_is_not_a_nul_test() {
        const COMPARE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe fn is_match(p1: *const u8, p2: *const u8) -> i32 {
    (*p1.offset(0) == *p2.offset(0) && *p1.offset(4) == *p2.offset(4)) as i32
}
pub unsafe fn caller(ip: *const u8, candidate: *const u8) -> i32 { is_match(ip, candidate) }
"#;
        assert_eq!(walk_of(COMPARE, "is_match::p1"), None);
        assert_eq!(walk_of(COMPARE, "is_match::p2"), None);
    }

    /// **Control** — a comparison against a NON-zero literal is not the string's
    /// end either (`*p == b':'` is a delimiter test).
    #[test]
    fn w5c_nul_a_delimiter_comparison_is_not_a_nul_test() {
        const DELIM: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe fn scan(mut p: *const u8) -> u32 {
    let mut n = 0u32;
    while *p as i32 == ':' as i32 { p = p.offset(1); n += 1; }
    n
}
pub unsafe fn caller(q: *const u8) -> u32 { scan(q) }
"#;
        assert_eq!(walk_of(DELIM, "scan::p"), None);
    }

    /// binn's row: the callee's walk can stop early (so the callee alone
    /// licenses only the fallback), but the CALLER hands the same pointer to
    /// `strcasecmp`, whose contract requires a terminated string — so on a
    /// UB-free input (§28) the terminator is there and the exact form is
    /// licensed at THIS caller. Relay 060, the caller-side clause of R491-7.
    const CALLER_LICENCE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe extern "C" { fn strcasecmp(a: *const i8, b: *const i8) -> i32; }
unsafe fn is_float(mut p: *const i8) -> i32 {
    while *p as i32 != 0 {
        if *p as i32 >= '0' as i32 && *p as i32 <= '9' as i32 {} else { return 0 }
        p = p.offset(1);
    }
    1
}
pub unsafe fn is_bool_str(str: *const i8) -> i32 {
    if strcasecmp(str, b"true\0" as *const u8 as *const i8) == 0 { return 1; }
    is_float(str)
}
"#;

    #[test]
    fn w5c_nul_a_callers_own_string_call_licenses_the_exact_form() {
        let licensed = ::utils::compilation::run_compiler_on_str(CALLER_LICENCE, |tcx| {
            let table = crate::bo_rewriter::decide_table(tcx).expect("fixture decisions");
            table
                .entries
                .iter()
                .map(|(subject, _)| subject)
                .find(|subject| subject.label == "is_bool_str::str")
                .map(|subject| caller_establishes_nul(tcx, subject))
                .expect("is_bool_str::str")
        })
        .unwrap();
        assert!(
            licensed,
            "a caller that hands its own pointer to `strcasecmp` establishes the NUL"
        );
    }

    /// **The emitted length under the caller-side licence**: the construction
    /// takes the string's own length, not the fallback const — the same
    /// `core::ffi` spelling as the callee-side branch.
    #[test]
    fn w5c_nul_the_caller_licence_emits_the_string_length() {
        let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(CALLER_LICENCE)
            .expect("emission");
        let flat = emitted.split_whitespace().collect::<String>();
        if flat.contains("from_raw_parts") {
            assert!(
                flat.contains("CStr::from_ptr") && flat.contains("wrapping_add(1)"),
                "the caller's licence emits the string's own length: {emitted}"
            );
        }
        assert!(
            !flat.contains("libc::"),
            "emitted extents use core::ffi, never libc (R497-3): {emitted}"
        );
        assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    }

    /// **Control** — the caller's call is NOT a string function. `memcpy` takes
    /// a count and says nothing about a terminator, so the licence does not
    /// come from it and the row keeps the fallback.
    #[test]
    fn w5c_nul_a_callers_counted_call_licenses_nothing() {
        let input = CALLER_LICENCE
            .replace(
                "unsafe extern \"C\" { fn strcasecmp(a: *const i8, b: *const i8) -> i32; }",
                "unsafe extern \"C\" { fn memcpy(d: *mut i8, s: *const i8, n: usize) -> *mut i8; }",
            )
            .replace(
                "if strcasecmp(str, b\"true\\0\" as *const u8 as *const i8) == 0 { return 1; }",
                "let mut buf: [i8; 4] = [0; 4]; memcpy(buf.as_mut_ptr(), str, 4);",
            );
        assert!(
            input.contains("memcpy(buf.as_mut_ptr(), str, 4)") && !input.contains("strcasecmp"),
            "the control must replace the string call with a counted one:\n{input}"
        );
        let licensed = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
            let table = crate::bo_rewriter::decide_table(tcx).expect("fixture decisions");
            table
                .entries
                .iter()
                .map(|(subject, _)| subject)
                .find(|subject| subject.label == "is_bool_str::str")
                .map(|subject| caller_establishes_nul(tcx, subject))
                .expect("is_bool_str::str")
        })
        .unwrap();
        assert!(!licensed, "a counted call establishes no terminator");
    }

    /// **R517-11 controls — one per conjunct of the candidate predicate.**
    /// libtree's `print_colon_delimited_paths::start` and binn's `is_float::p`
    /// are the SAME source shape — a self-advancing C-string walk — and what
    /// separates them at the corpus is BO's kind: libtree's slot is `Raw` and
    /// decides `kind-raw`, binn's is `Ref` and delivers a cursor (batch 27's
    /// `raw-boundary-subjects.tsv`, both programs). The predicate is read here
    /// on that pair's two shapes.
    #[test]
    fn w5c_r517_the_candidate_predicate_reads_the_kind_first() {
        let unsupported = SliceUses {
            unsupported: Some(rustc_span::DUMMY_SP),
            ..SliceUses::default()
        };
        let supported = SliceUses::default();
        use crate::analyses::borrow_ownership::SlotKind;
        // libtree's shape: a cursor-shaped walk the model calls `Raw`.
        assert!(
            !is_cursor_candidate(Some(SlotKind::Raw), Some(&unsupported), false),
            "a `Raw` slot is no cursor candidate whatever its uses look like"
        );
        assert!(
            !is_cursor_candidate(Some(SlotKind::Raw), Some(&unsupported), true),
            "and the sign refusal does not lift a `Raw` slot either"
        );
        assert!(
            !is_cursor_candidate(Some(SlotKind::Owning), Some(&unsupported), true),
            "nor an `Owning` one"
        );
        assert!(
            !is_cursor_candidate(None, Some(&unsupported), true),
            "an unmodelled slot is not a candidate on absence of evidence"
        );
        // binn's shape: a cursor-shaped walk the model calls `Ref`.
        assert!(
            is_cursor_candidate(Some(SlotKind::Ref), Some(&unsupported), false),
            "an unsupported slice use is `SliceCursorUse`/`SliceUseUnsupported`"
        );
        assert!(
            is_cursor_candidate(Some(SlotKind::Ref), Some(&supported), true),
            "and the sign refusal is `SliceNegOrUnknownOffset`"
        );
        // Neither reason: nothing for the cursor family to admit from.
        assert!(
            !is_cursor_candidate(Some(SlotKind::Ref), Some(&supported), false),
            "a `Ref` slot whose uses are supported and whose sign is fine is not one"
        );
        assert!(
            !is_cursor_candidate(Some(SlotKind::Ref), None, false),
            "and neither is one with no slice uses at all"
        );
    }

    /// **R517-11 — the exemption yields to a cursor CANDIDATE.** binn's shape:
    /// the caller is held on `is_float`, whose parameter the cursor family can
    /// admit. With that candidate fact the hold stays (two cursor deliveries
    /// are not worth one string extent); without it the exemption is the one
    /// R491-7 built. Both readings are taken in the SAME pass — which is the
    /// whole of the change from R505-2, whose reading needed a second one
    /// (047 §2). Restated per R217-2(a) to the property both frames share: what
    /// decides the hold is the candidate set, not when it is consulted.
    #[test]
    fn w5c_nul_the_exemption_yields_to_a_cursor_candidate() {
        let held = |cursor: bool| {
            ::utils::compilation::run_compiler_on_str(EARLY_EXIT_WALK, |tcx| {
                let owners = tcx
                    .hir_body_owners()
                    .filter(|did| matches!(tcx.def_kind(*did), rustc_hir::def::DefKind::Fn))
                    .collect::<Vec<_>>();
                let facts = super::super::emitability::collect(tcx, &owners);
                let table = crate::bo_rewriter::decide_table(tcx).expect("fixture decisions");
                let subjects = table
                    .entries
                    .iter()
                    .map(|(subject, _)| subject.clone())
                    .collect::<Vec<_>>();
                let program = crate::bo_rewriter::collect_program(tcx);
                let fat = crate::bo_rewriter::fat_facts::FatFacts::from_program(&program);
                let mut candidates = CursorCandidates::default();
                if cursor {
                    for subject in &subjects {
                        if subject.label == "is_float::p"
                            && let SubjectKind::Param { hir_index } = subject.kind
                        {
                            candidates.insert((subject.fn_did, hir_index));
                        }
                    }
                    assert_eq!(candidates.len(), 1, "the callee parameter resolves");
                }
                collect(
                    tcx,
                    &subjects,
                    &facts,
                    &FxHashMap::default(),
                    &candidates,
                    None,
                    Some(&fat),
                )
                .into_iter()
                .any(|(_, access)| access.detail().starts_with("is_float:p:"))
            })
            .unwrap()
        };
        assert!(
            held(true),
            "a callee parameter the cursor family can admit keeps its caller's hold"
        );
        assert!(
            !held(false),
            "and one it cannot takes the exemption R491-7 built, in this same pass"
        );
    }

    /// **Control** — an INDEXED walk is not a NUL walk at all: its extent is a
    /// count question, and this rule says nothing about it.
    #[test]
    fn w5c_nul_an_indexed_walk_is_not_a_nul_walk() {
        const INDEXED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe fn read_at(data: *const u8, n: usize) -> u32 {
    let mut i = 0usize; let mut acc = 0u32;
    while i < n { acc = acc.wrapping_add(*data.offset(i as isize) as u32); i += 1; }
    acc
}
pub unsafe fn caller(p: *const u8, n: usize) -> u32 { read_at(p, n) }
"#;
        assert_eq!(walk_of(INDEXED, "read_at::data"), None);
    }

    /// **Control** — a NUL test AND an indexed read. The loop ends at the NUL,
    /// but the body reaches `p[i]` for an `i` the string's own length does not
    /// bound, so this is a count walk wearing a NUL test and the rule declines
    /// it.
    #[test]
    fn w5c_nul_an_indexed_read_under_a_nul_test_is_declined() {
        const MIXED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe fn mixed(p: *const u8, n: usize) -> u32 {
    let mut i = 0usize; let mut acc = 0u32;
    while *p != 0 && i < n { acc = acc.wrapping_add(*p.offset(i as isize) as u32); i += 1; }
    acc
}
pub unsafe fn caller(q: *const u8, n: usize) -> u32 { mixed(q, n) }
"#;
        assert_eq!(walk_of(MIXED, "mixed::p"), None);
    }

    /// **Control** — a walk that reads a WIDER type at the cursor is not a
    /// byte-at-a-time NUL walk, whatever its loop condition says.
    #[test]
    fn w5c_nul_a_wide_read_at_the_cursor_is_not_a_nul_walk() {
        const WIDE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe fn scan(mut p: *const u8) -> u32 {
    let mut acc = 0u32;
    while *p != 0 { acc = acc.wrapping_add(*(p as *const u32)); p = p.offset(1); }
    acc
}
pub unsafe fn caller(q: *const u8) -> u32 { scan(q) }
"#;
        assert_eq!(walk_of(WIDE, "scan::p"), None);
    }
}
