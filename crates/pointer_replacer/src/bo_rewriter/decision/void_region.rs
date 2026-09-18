//! Void buffers viewed as typed regions (wave-6b; seat addendum 400, R400-1).
//!
//! A `c_void` parameter carries no extent (R271-1), so [`super::void_pointee`]
//! holds it. Two program-defined shapes REINTERPRET such a buffer rather than
//! walk it, and both are provable from the callee's own body:
//!
//! - **Accessor chain** — the body is one `return` of a cast chain over the
//!   parameter: `p as *mut T` (region at offset 0), or
//!   `&mut *(Inner(p)).offset(K) as *mut A as *mut T` where `Inner` is itself
//!   an accessor of this shape over the same buffer. The region's byte offset
//!   is `offset(Inner) + K * size_of::<A>()`, a compile-time constant of the
//!   program. brotli's `AddrH40` / `HeadH40` / `TinyHashH40` / `BanksH40`
//!   carve one `extra` allocation this way.
//! - **Width reader** — the body is one `return *(p as *const T)`: a read of
//!   `size_of::<T>()` bytes at offset 0. brotli's `BrotliUnalignedRead32/64`.
//!
//! The parameter becomes a byte slice (`&mut [u8]` / `&[u8]`) over exactly the
//! region the body reaches. A chain's regions are sized by their neighbours
//! (region k ends where region k+1 begins); the LAST region of a chain has no
//! neighbour and takes `FALLBACK_SLICE_EXTENT` elements of its type with the
//! addendum-77 receipt. A width reader's region is exactly its width.
//!
//! **Build 1 keeps the accessor's raw return.** The body reinterprets the
//! region and hands back the raw typed pointer the caller always received
//! (`region.as_mut_ptr().cast::<T>()` after an alignment assertion), so every
//! caller local keeps its prior form and its prior accesses; the native
//! `&mut [T]` return is the next build. A width reader returns
//! `T::from_ne_bytes([p[0], ..])` — a checked read of its own width.
//!
//! Soundness (conditional on a UB-free input, §28): the C program's own typed
//! access through the region proves the region is within the allocation and
//! aligned for `T` wherever it is reached; the caller-side bridge derives each
//! region from the raw buffer pointer at the region's own offset and length, so
//! the regions a caller holds together are disjoint ranges — under Stacked
//! Borrows a later region's retag pops nothing of an earlier region's. The
//! bridged argument is a temporary: no safe view of the buffer outlives the
//! call, so the raw pointer the accessor returns aliases only raw state.
//! Alignment is asserted at runtime, not assumed: a misaligned typed access in
//! the input is its own UB, and the assertion turns it into a panic.
//!
//! A body that is anything but the single return, a chain that reaches the
//! buffer other than through the parameter, a non-constant offset, or a cast
//! through an element that is not plain old data is not in the class and keeps
//! the void hold. The structural match names the parameter exactly once — at
//! the chain's base or as the inner call's only argument — so no second use
//! can hide in a recognised body.

use rustc_hash::FxHashMap;
use rustc_hir::{
    BorrowKind, Expr, ExprKind, HirId, Node, QPath, StmtKind, UnOp,
    def::{DefKind, Res},
    def_id::LocalDefId,
};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::Span;

use super::{
    Subject, SubjectKind,
    declaration::{DeclarationPointees, ResolvedPointee},
    emitability::{SliceUses, UseEdit},
};

pub(crate) type Key = (LocalDefId, HirId);
pub(crate) type Contracts = FxHashMap<Key, Region>;

/// Which of the two reinterpretation shapes the body has.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Shape {
    /// `return <chain>(p)` — a typed pointer into the buffer at a constant
    /// offset; the return stays raw in this build.
    Accessor,
    /// `return *(p as *const T)` — one value of `T` read at offset 0.
    WidthRead,
    /// `*(p as *mut T) = v;` — one value of `T` WRITTEN at offset 0, the
    /// mirror of [`Shape::WidthRead`] (brotli's `BrotliUnalignedWrite32/64`).
    WidthWrite,
    /// A LOCAL `let v = p as *mut u8` over a typed scalar parameter `p: *mut T`:
    /// the `size_of::<T>()` bytes of one scalar, viewed byte by byte (relay
    /// 009 / R416-7; binn `copy_be64::source`). The local is the subject; the
    /// parameter keeps its own form.
    ByteView,
}

impl Shape {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::Accessor => "accessor",
            Self::WidthRead => "width-read",
            Self::WidthWrite => "width-write",
            Self::ByteView => "byte-view",
        }
    }
}

/// One proven region of a void buffer, keyed by the callee parameter that
/// receives it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Region {
    pub(crate) shape: Shape,
    /// Byte offset of the region from the buffer pointer the CALLER holds.
    pub(crate) offset_bytes: u64,
    /// Exact byte length — from the chain's next region or the reader's width.
    /// `None` is the last region of a chain: the caller bridges
    /// `FALLBACK_SLICE_EXTENT * size_of::<T>()` bytes under the receipt.
    pub(crate) len_bytes: Option<u64>,
    /// The element type at the reinterpretation, as the source spells it.
    pub(crate) element: String,
    pub(crate) element_size: u64,
    /// The reinterpretation's own mutability: `*mut T` needs `&mut [u8]`.
    pub(crate) mutable: bool,
    /// The one body rewrite: the whole returned expression.
    pub(crate) uses: Vec<UseEdit>,
    /// The span the rewrite covers; references to sibling accessors inside it
    /// disappear with it (see [`covers`]).
    pub(crate) replaced: Span,
    /// The inner accessor this chain link continues, if any: the body names
    /// that function's signature (`(Inner as unsafe extern "C" fn(*mut c_void)
    /// -> *mut T)(p)`), so the two signatures are one unit (R447-4).
    pub(crate) inner: Option<LocalDefId>,
}

impl Region {
    /// The caller-side byte length text, or `None` for the fallback arm.
    pub(crate) fn len_text(&self) -> Option<String> {
        self.len_bytes.map(|n| n.to_string())
    }

    /// The fallback arm's scaled extent: the ruled element count, in bytes of
    /// this region's element type, spelled with the named const so a
    /// fabricated site stays recognisable in the emitted crate.
    pub(crate) fn fallback_len_text(&self) -> String {
        format!(
            "{}*core::mem::size_of::<{}>()",
            super::seam::FABRICATED_LEN_PATH,
            self.element
        )
    }

    pub(crate) fn detail(&self) -> String {
        format!(
            "{}:offset={}:len={}:element={}",
            self.shape.key(),
            self.offset_bytes,
            self.len_bytes
                .map_or_else(|| "fallback".to_owned(), |n| n.to_string()),
            self.element
        )
    }
}

/// What one body proves about its parameter, before the chain is sized.
struct Chain {
    shape: Shape,
    offset_bytes: u64,
    element: String,
    element_size: u64,
    element_align: u64,
    mutable: bool,
    /// The whole returned expression, or the whole assignment for a writer.
    returned: Span,
    /// A writer's written VALUE, whose bytes the region copy takes.
    written: Option<Span>,
    /// The inner accessor this chain continues, if any.
    inner: Option<LocalDefId>,
    /// The parameter binding.
    param: HirId,
    param_name: String,
}

fn layout_of<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId, ty: Ty<'tcx>) -> Option<(u64, u64)> {
    let env = ty::TypingEnv::post_analysis(tcx, owner);
    let layout = tcx.layout_of(env.as_query_input(ty)).ok()?;
    Some((layout.size.bytes(), layout.align.abi.bytes()))
}

/// Is `ty` plain old data for a typed region: an integer, or a `repr(C)` struct
/// / array of such with no padding? Every bit pattern of the bytes is then a
/// valid `T`, which is what a reinterpretation needs.
fn is_plain_old_data<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId, ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => true,
        TyKind::Array(element, _) => is_plain_old_data(tcx, owner, *element),
        TyKind::Adt(def, args) if def.is_struct() && def.repr().c() => {
            let Some((size, _)) = layout_of(tcx, owner, ty) else { return false };
            let mut sum = 0;
            for field in def.all_fields() {
                let field_ty = field.ty(tcx, args);
                if !is_plain_old_data(tcx, owner, field_ty) {
                    return false;
                }
                let Some((field_size, _)) = layout_of(tcx, owner, field_ty) else {
                    return false;
                };
                sum += field_size;
            }
            sum == size
        }
        _ => false,
    }
}

/// c2rust's constant vocabulary: integer literals under casts, `<<`, `>>`,
/// `+`, `-`, `*`, `&`, `|`, unary minus, and `size_of::<T>()`.
fn eval_const<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId, expr: &Expr<'tcx>) -> Option<i128> {
    use rustc_hir::BinOpKind;
    match &expr.kind {
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(value, _) => i128::try_from(value.get()).ok(),
            _ => None,
        },
        ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) => eval_const(tcx, owner, inner),
        ExprKind::Block(block, _) if block.stmts.is_empty() => eval_const(tcx, owner, block.expr?),
        ExprKind::Unary(UnOp::Neg, inner) => eval_const(tcx, owner, inner).map(|v| -v),
        ExprKind::Binary(op, left, right) => {
            let l = eval_const(tcx, owner, left)?;
            let r = eval_const(tcx, owner, right)?;
            match op.node {
                BinOpKind::Add => l.checked_add(r),
                BinOpKind::Sub => l.checked_sub(r),
                BinOpKind::Mul => l.checked_mul(r),
                BinOpKind::Shl => u32::try_from(r).ok().and_then(|r| l.checked_shl(r)),
                BinOpKind::Shr => u32::try_from(r).ok().and_then(|r| l.checked_shr(r)),
                BinOpKind::BitAnd => Some(l & r),
                BinOpKind::BitOr => Some(l | r),
                _ => None,
            }
        }
        ExprKind::Call(callee, args) if args.is_empty() => {
            let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind else { return None };
            let Res::Def(DefKind::Fn, did) = path.res else { return None };
            if !tcx.def_path_str(did).ends_with("mem::size_of") {
                return None;
            }
            let ty = tcx
                .typeck(owner)
                .node_args(callee.hir_id)
                .first()?
                .as_type()?;
            layout_of(tcx, owner, ty).map(|(size, _)| i128::from(size))
        }
        _ => None,
    }
}

/// The single returned expression of a body that is nothing else.
fn sole_return<'tcx>(body: &'tcx Expr<'tcx>) -> Option<&'tcx Expr<'tcx>> {
    let ExprKind::Block(block, _) = body.kind else { return None };
    match (block.stmts, block.expr) {
        ([stmt], None) => match stmt.kind {
            StmtKind::Semi(expr) | StmtKind::Expr(expr) => match expr.kind {
                ExprKind::Ret(Some(returned)) => Some(returned),
                _ => None,
            },
            _ => None,
        },
        ([], Some(expr)) => match expr.kind {
            ExprKind::Ret(Some(returned)) => Some(returned),
            _ => Some(expr),
        },
        _ => None,
    }
}

/// The single assignment statement of a body that is nothing else:
/// `*(p as *mut T) = v;` and no more. The write mirror of [`sole_return`], and
/// as strict: a body with any other statement is not in the class.
fn sole_assignment<'tcx>(
    body: &'tcx Expr<'tcx>,
) -> Option<(&'tcx Expr<'tcx>, &'tcx Expr<'tcx>, &'tcx Expr<'tcx>)> {
    let ExprKind::Block(block, _) = body.kind else { return None };
    let whole = match (block.stmts, block.expr) {
        ([stmt], None) => match stmt.kind {
            StmtKind::Semi(expr) | StmtKind::Expr(expr) => expr,
            _ => return None,
        },
        ([], Some(expr)) => expr,
        _ => return None,
    };
    let ExprKind::Assign(place, value, _) = whole.kind else { return None };
    Some((whole, place, value))
}

/// Peel casts, returning the operand and the outermost cast's written pointee
/// type text (`*mut uint16_t` → `uint16_t`) with its mutability.
fn peel_casts<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> (&'tcx Expr<'tcx>, Option<(String, bool)>) {
    let mut outermost = None;
    let mut current = expr;
    while let ExprKind::Cast(inner, ty) = current.kind {
        if outermost.is_none()
            && let rustc_hir::TyKind::Ptr(mut_ty) = ty.kind
            && let Ok(text) = tcx.sess.source_map().span_to_snippet(mut_ty.ty.span)
        {
            outermost = Some((text, mut_ty.mutbl.is_mut()));
        }
        current = inner;
    }
    (current, outermost)
}

fn is_param_path(expr: &Expr<'_>, param: HirId) -> bool {
    matches!(&expr.kind, ExprKind::Path(QPath::Resolved(_, path)) if path.res == Res::Local(param))
}

/// A call `A(p)` or `(A as fn(..))(p)` to a local function with the parameter
/// as its only argument.
fn inner_accessor_call<'tcx>(expr: &'tcx Expr<'tcx>, param: HirId) -> Option<LocalDefId> {
    let ExprKind::Call(callee, [argument]) = expr.kind else { return None };
    let (argument, _) = strip_plain_casts(argument);
    if !is_param_path(argument, param) {
        return None;
    }
    let (callee, _) = strip_plain_casts(callee);
    let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind else { return None };
    let Res::Def(DefKind::Fn, did) = path.res else { return None };
    did.as_local()
}

fn strip_plain_casts<'tcx>(expr: &'tcx Expr<'tcx>) -> (&'tcx Expr<'tcx>, usize) {
    let mut current = expr;
    let mut count = 0;
    while let ExprKind::Cast(inner, _) = current.kind {
        current = inner;
        count += 1;
    }
    (current, count)
}

/// What one local proves about itself: a byte view of one scalar parameter.
struct ByteView {
    parameter: HirId,
    /// The scalar type as the parameter spells it, resolved.
    scalar: String,
    /// The extent, ALWAYS exact (R422-7): the view is a reborrow of one
    /// scalar's storage, so a UB-free input never indexes past
    /// `size_of::<T>()` — a read past the scalar was UB in the input (§28).
    /// No range analysis, no fallback receipt, no hold.
    size: u64,
    initializer: HirId,
    initializer_span: Span,
}

/// Count the body's path uses of one local binding.
struct UseCounter {
    local: HirId,
    count: usize,
}

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for UseCounter {
    fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
        if is_param_path(expression, self.local) {
            self.count += 1;
        }
        rustc_hir::intravisit::walk_expr(self, expression);
    }
}

/// Read one unannotated local's byte view: `let v = p as *mut u8` (any run of
/// plain pointer casts, ending at `u8`) where `p` is a parameter of this
/// function typed `*T` for a scalar `T` wider than a byte (a byte-to-byte
/// recast is a string, not a view), and the cast is `p`'s ONLY use in the
/// body — so the view is the only live path to the scalar while it lives,
/// and a safe form of `p` is never used alongside it. `None` is "not in the
/// class"; the ladder's own hold stays.
fn read_byte_view<'tcx>(tcx: TyCtxt<'tcx>, subject: &Subject) -> Option<ByteView> {
    if subject.ptr_depth != 1 || subject.kind != SubjectKind::Local || subject.ty_span.is_some() {
        return None;
    }
    let Node::LetStmt(let_stmt) = tcx.parent_hir_node(subject.hir_id) else { return None };
    if let_stmt.ty.is_some() || let_stmt.pat.hir_id != subject.hir_id {
        return None;
    }
    let initializer = let_stmt.init?;
    if initializer.span.from_expansion() || !matches!(initializer.kind, ExprKind::Cast(..)) {
        return None;
    }
    let typeck = tcx.typeck(subject.fn_did);
    let TyKind::RawPtr(viewed, _) = typeck.expr_ty(initializer).kind() else { return None };
    if *viewed != tcx.types.u8 {
        return None;
    }
    let (base, _) = strip_plain_casts(initializer);
    let ExprKind::Path(QPath::Resolved(_, path)) = &base.kind else { return None };
    let Res::Local(parameter) = path.res else { return None };
    let body = tcx.hir_body_owned_by(subject.fn_did);
    if !body
        .params
        .iter()
        .any(|param| param.pat.hir_id == parameter)
    {
        return None;
    }
    let TyKind::RawPtr(scalar_ty, _) = typeck.expr_ty(base).kind() else { return None };
    if !matches!(
        scalar_ty.kind(),
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)
    ) {
        return None;
    }
    let (size, _) = layout_of(tcx, subject.fn_did, *scalar_ty)?;
    if size <= 1 {
        return None;
    }
    let mut counter = UseCounter {
        local: parameter,
        count: 0,
    };
    rustc_hir::intravisit::Visitor::visit_expr(&mut counter, body.value);
    if counter.count != 1 {
        return None;
    }
    Some(ByteView {
        parameter,
        scalar: super::declaration::pointee_source(tcx, *scalar_ty),
        size,
        initializer: initializer.hir_id,
        initializer_span: initializer.span,
    })
}

/// Read one body's chain. `None` is "not in the class", never a hold on its
/// own — the void hold stays in force.
fn read_chain<'tcx>(tcx: TyCtxt<'tcx>, subject: &Subject) -> Option<Chain> {
    if subject.ptr_depth != 1 || !matches!(subject.kind, SubjectKind::Param { .. }) {
        return None;
    }
    let Node::Pat(pat) = tcx.hir_node(subject.hir_id) else { return None };
    if !super::void_pointee::has_void_pointee(tcx, tcx.typeck(subject.fn_did).pat_ty(pat), 1) {
        return None;
    }
    let param_name = subject.param_name.clone()?;
    let body = tcx.hir_body_owned_by(subject.fn_did).value;
    let typeck = tcx.typeck(subject.fn_did);

    // Width writer: `*(p as *mut T) = v;`, the mirror of the reader below.
    // The written value is any expression that does not mention the buffer —
    // in the corpus it is the function's other parameter — and the whole
    // assignment is replaced, so `p` has no use left outside the region.
    if let Some((whole, place, value)) = sole_assignment(body)
        && !whole.span.from_expansion()
        && let ExprKind::Unary(UnOp::Deref, operand) = place.kind
    {
        let (base, cast) = peel_casts(tcx, operand);
        let (element, mutable) = cast?;
        if !is_param_path(base, subject.hir_id) || !mutable {
            return None;
        }
        let ty = typeck.expr_ty(place);
        if !matches!(
            ty.kind(),
            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)
        ) {
            return None;
        }
        // The written value may not reach the buffer: a value derived from `p`
        // would read the region while the write borrows it.
        let mut counter = UseCounter {
            local: subject.hir_id,
            count: 0,
        };
        rustc_hir::intravisit::Visitor::visit_expr(&mut counter, value);
        if counter.count != 0 {
            return None;
        }
        let (element_size, element_align) = layout_of(tcx, subject.fn_did, ty)?;
        return Some(Chain {
            shape: Shape::WidthWrite,
            offset_bytes: 0,
            element,
            element_size,
            element_align,
            mutable: true,
            returned: whole.span,
            written: Some(value.span),
            inner: None,
            param: subject.hir_id,
            param_name,
        });
    }

    let returned = sole_return(body)?;
    if returned.span.from_expansion() {
        return None;
    }

    // Width reader: `*(p as *const T)`.
    if let ExprKind::Unary(UnOp::Deref, operand) = returned.kind {
        let (base, cast) = peel_casts(tcx, operand);
        let (element, _) = cast?;
        if !is_param_path(base, subject.hir_id) {
            return None;
        }
        let ty = typeck.expr_ty(returned);
        if !matches!(
            ty.kind(),
            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)
        ) {
            return None;
        }
        let (element_size, element_align) = layout_of(tcx, subject.fn_did, ty)?;
        return Some(Chain {
            shape: Shape::WidthRead,
            offset_bytes: 0,
            element,
            element_size,
            element_align,
            mutable: false,
            returned: returned.span,
            written: None,
            inner: None,
            param: subject.hir_id,
            param_name,
        });
    }

    // Accessor: casts over the parameter itself, or over
    // `&mut *(Inner(p)).offset(K)`.
    let (base, cast) = peel_casts(tcx, returned);
    let (element, mutable) = cast?;
    let TyKind::RawPtr(element_ty, _) = typeck.expr_ty(returned).kind() else { return None };
    if !is_plain_old_data(tcx, subject.fn_did, *element_ty) {
        return None;
    }
    let (element_size, element_align) = layout_of(tcx, subject.fn_did, *element_ty)?;
    let mut chain = Chain {
        shape: Shape::Accessor,
        offset_bytes: 0,
        element,
        element_size,
        element_align,
        mutable,
        returned: returned.span,
        written: None,
        inner: None,
        param: subject.hir_id,
        param_name,
    };
    if is_param_path(base, subject.hir_id) {
        return Some(chain);
    }
    let ExprKind::AddrOf(BorrowKind::Ref, _, place) = base.kind else { return None };
    let ExprKind::Unary(UnOp::Deref, pointer) = place.kind else { return None };
    let (receiver, step) = match pointer.kind {
        ExprKind::MethodCall(segment, receiver, [count], _)
            if segment.ident.name.as_str() == "offset" =>
        {
            let count = eval_const(tcx, subject.fn_did, count)?;
            let TyKind::RawPtr(stride_ty, _) = typeck.expr_ty(receiver).kind() else {
                return None;
            };
            let (stride, _) = layout_of(tcx, subject.fn_did, *stride_ty)?;
            (receiver, u64::try_from(count).ok()?.checked_mul(stride)?)
        }
        _ => (pointer, 0),
    };
    let (receiver, _) = strip_plain_casts(receiver);
    chain.inner = Some(inner_accessor_call(receiver, subject.hir_id)?);
    chain.offset_bytes = step;
    Some(chain)
}

/// Resolve every chain of the crate to absolute offsets, size each region by
/// its neighbour, and install the byte-slice declaration for each admitted
/// parameter.
pub(crate) fn collect(
    tcx: TyCtxt<'_>,
    subjects: &[Subject],
    referenced: &FxHashMap<LocalDefId, Vec<(super::emitability::RefKind, Span)>>,
    pointees: &mut DeclarationPointees,
) -> Contracts {
    let mut chains: FxHashMap<LocalDefId, (Key, Chain)> = FxHashMap::default();
    let mut ambiguous: Vec<LocalDefId> = Vec::new();
    for subject in subjects {
        let Some(chain) = read_chain(tcx, subject) else { continue };
        // One void parameter per accessor; a second would make the chain's
        // buffer ambiguous.
        if chains.contains_key(&subject.fn_did) {
            ambiguous.push(subject.fn_did);
            continue;
        }
        chains.insert(subject.fn_did, ((subject.fn_did, subject.hir_id), chain));
    }
    for function in ambiguous {
        chains.remove(&function);
    }
    // Absolute offsets: walk each chain to its root, refusing cycles and
    // links to functions outside the class.
    let mut absolute: FxHashMap<LocalDefId, (u64, LocalDefId)> = FxHashMap::default();
    for &function in chains.keys() {
        let mut offset = 0;
        let mut current = function;
        let mut seen = vec![function];
        let root = loop {
            let Some((_, chain)) = chains.get(&current) else { break None };
            offset += chain.offset_bytes;
            match chain.inner {
                None => break Some(current),
                Some(inner) if seen.contains(&inner) => break None,
                Some(inner) => {
                    seen.push(inner);
                    current = inner;
                }
            }
        };
        if let Some(root) = root {
            absolute.insert(function, (offset, root));
        }
    }
    // Two accessors of one buffer at the same offset would hand a caller two
    // views of one range, and the second mutable retag would invalidate the
    // first (Stacked Borrows). Neither is admitted.
    let same_offset: Vec<LocalDefId> = absolute
        .iter()
        .filter(|(function, (offset, root))| {
            absolute
                .iter()
                .any(|(other, (o, r))| other != *function && r == root && o == offset)
        })
        .map(|(function, _)| *function)
        .collect();
    for function in same_offset {
        absolute.remove(&function);
    }
    // A chain admits only whole. An inner accessor whose outer link is NOT
    // admitted keeps the outer's `(Inner as fn(..))(p)` cast in force, and a
    // fn-pointer cast pins the signature it names (the referenced gate). So a
    // pinning reference from anywhere but an ADMITTED chain's rewrite drops the
    // accessor it names — and dropping it un-covers its own inner call, hence
    // the fixpoint. `covers_sibling` then lifts the ladder's gate for exactly
    // the references this loop found covered.
    loop {
        let pinned: Vec<LocalDefId> = absolute
            .keys()
            .copied()
            .filter(|function| {
                referenced.get(function).is_some_and(|refs| {
                    refs.iter().any(|(kind, span)| {
                        *kind != super::emitability::RefKind::Call
                            && !chains.iter().any(|(outer, (_, chain))| {
                                outer != function
                                    && absolute.contains_key(outer)
                                    && chain.returned.contains(*span)
                            })
                    })
                })
            })
            .collect();
        if pinned.is_empty() {
            break;
        }
        for function in pinned {
            absolute.remove(&function);
        }
    }
    let mut out = Contracts::default();
    for (&function, (key, chain)) in &chains {
        let Some(&(offset_bytes, root)) = absolute.get(&function) else { continue };
        // Alignment of the region's start must be provable from the chain:
        // every offset on the way is a multiple of the element alignment.
        if chain.element_align != 0 && offset_bytes % chain.element_align != 0 {
            continue;
        }
        let len_bytes = match chain.shape {
            // A chain is read from a parameter's body; a byte view is a local's.
            Shape::ByteView => unreachable!("a chain never reads as a byte view"),
            Shape::WidthRead | Shape::WidthWrite => Some(chain.element_size),
            Shape::Accessor => absolute
                .iter()
                .filter(|(other, (off, other_root))| {
                    **other != function && *other_root == root && *off > offset_bytes
                })
                .map(|(_, (off, _))| off - offset_bytes)
                .min(),
        };
        let name = &chain.param_name;
        let element = &chain.element;
        let replacement = match chain.shape {
            Shape::ByteView => unreachable!("a chain never reads as a byte view"),
            // The whole assignment becomes a checked copy of the value's own
            // bytes into the region — same width, same order, no pointer.
            Shape::WidthWrite => {
                let Some(written) = chain.written else { continue };
                let Ok(value) = tcx.sess.source_map().span_to_snippet(written) else {
                    continue;
                };
                format!("{name}.copy_from_slice(&({value}).to_ne_bytes())")
            }
            Shape::WidthRead => {
                let bytes = (0..chain.element_size)
                    .map(|i| format!("{name}[{i}]"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{element}::from_ne_bytes([{bytes}])")
            }
            Shape::Accessor => {
                let (amp, ptr) = if chain.mutable {
                    ("&mut ", "as_mut_ptr")
                } else {
                    ("&", "as_ptr")
                };
                format!(
                    "{{ let __crat_region: {amp}[u8] = {name}; assert!(__crat_region.as_ptr() as usize % core::mem::align_of::<{element}>() == 0, \"void region is misaligned for its typed view\"); __crat_region.{ptr}().cast::<{element}>() }}"
                )
            }
        };
        let region = Region {
            shape: chain.shape,
            offset_bytes,
            len_bytes,
            element: element.clone(),
            element_size: chain.element_size,
            mutable: chain.mutable,
            uses: vec![UseEdit {
                span: chain.returned,
                replacement,
                bridge_kind: "void-region-view",
            }],
            replaced: chain.returned,
            inner: chain.inner,
        };
        let Some(subject) = subjects.iter().find(|s| (s.fn_did, s.hir_id) == *key) else {
            continue;
        };
        let Some(span) = subject.ty_span else { continue };
        let Ok(original_alias) = tcx.sess.source_map().span_to_snippet(span) else { continue };
        let Node::Pat(pat) = tcx.hir_node(subject.hir_id) else { continue };
        pointees.insert(
            *key,
            ResolvedPointee {
                original_alias,
                input_type: super::declaration::pointee_source(
                    tcx,
                    tcx.typeck(subject.fn_did).pat_ty(pat),
                ),
                pointee: "u8".to_owned(),
            },
        );
        out.insert(*key, region);
    }
    // Byte views: the local's uses stay the slice-use walk's own (indexing of
    // a `size_of::<T>()`-byte slice); the contract carries the extent.
    for subject in subjects {
        let Some(view) = read_byte_view(tcx, subject) else { continue };
        out.insert(
            (subject.fn_did, subject.hir_id),
            Region {
                shape: Shape::ByteView,
                inner: None,
                offset_bytes: 0,
                len_bytes: Some(view.size),
                element: "u8".to_owned(),
                element_size: 1,
                mutable: subject.mutable,
                uses: Vec::new(),
                replaced: view.initializer_span,
            },
        );
    }
    out
}

/// The body rewrites, installed over whatever the slice-use walk recorded for
/// the parameter: the returned expression is the parameter's only use. A byte
/// view keeps the walk's rewrites: its uses are ordinary indexing.
pub(crate) fn install(contracts: &Contracts, uses: &mut FxHashMap<Key, SliceUses>) {
    for (key, region) in contracts {
        if region.shape == Shape::ByteView {
            continue;
        }
        uses.insert(
            *key,
            SliceUses {
                rewrites: region.uses.clone(),
                ..Default::default()
            },
        );
    }
}

pub(crate) fn active<'a>(ctx: &super::Ctx<'a, '_>, subject: &Subject) -> Option<&'a Region> {
    use crate::bo_rewriter::additive::FamilyStage;
    (ctx.family_policy
        .enabled(subject.fn_did, FamilyStage::Declaration)
        && ctx
            .family_policy
            .enabled(subject.fn_did, FamilyStage::SliceUse))
    .then(|| ctx.void_region.get(&(subject.fn_did, subject.hir_id)))
    .flatten()
}

/// Is this reference to `referenced` inside another accessor's region rewrite?
/// A reference there (the `(Inner as fn(..))(p)` call of a chain) is deleted
/// with the chain it belongs to, so it does not pin `referenced`'s signature.
pub(crate) fn covers_sibling(contracts: &Contracts, referenced: LocalDefId, span: Span) -> bool {
    contracts
        .iter()
        .any(|((owner, _), region)| *owner != referenced && region.replaced.contains(span))
}

/// Is the subject's decision the slice form a region contract emits under?
/// Exhaustive on purpose: a new disposition must be placed here, not fall
/// through a `matches!`.
fn decided_slice(decision: &super::Decision) -> bool {
    match decision {
        super::Decision::Slice { .. } => true,
        super::Decision::Ref { .. }
        | super::Decision::InferredRef { .. }
        | super::Decision::NestedSlice { .. }
        | super::Decision::Opt { .. }
        | super::Decision::Box(_)
        | super::Decision::Cursor { .. }
        | super::Decision::Degraded(_) => false,
    }
}

/// The region contract of one callee parameter position, if that parameter
/// was decided as a region slice.
pub(crate) fn parameter(
    table: &super::DecisionTable,
    callee: LocalDefId,
    index: usize,
) -> Option<&Region> {
    table.entries.iter().find_map(|(s, d)| {
        (s.fn_did == callee
            && matches!(s.kind, SubjectKind::Param { hir_index } if hir_index == index)
            && decided_slice(d))
        .then(|| table.void_region.get(&(s.fn_did, s.hir_id)))
        .flatten()
    })
}

/// **The licensed byte width of a callee parameter this family has typed**
/// (relay 023 §2, R408-1 evidence for wave-5c's caller lift).
///
/// A caller held `held:local-callee-access-extent` at a LOCAL callee needs a
/// length for its own parameter, and R408-1 licenses a companion only when a
/// count position of the callee parameter's own pinned contract names it.
/// A region contract is exactly such a count, and a stronger one: the width is
/// the callee's own type, not a position whose value must be read. It is
/// returned only when it is EXACT — a width read or write (`size_of::<T>()`)
/// or a chain link sized by its neighbour — never for the fallback arm, whose
/// extent is `FALLBACK_SLICE_EXTENT` and licenses nothing.
///
/// The caller still owes its own root: this says how many bytes the callee
/// accesses, not that the caller may claim them. A THIN caller widened to this
/// width is the refusal R416-5 names, and nothing here relaxes it.
pub(crate) fn licensed_width(
    table: &super::DecisionTable,
    callee: LocalDefId,
    index: usize,
) -> Option<u64> {
    parameter(table, callee, index).and_then(|region| region.len_bytes)
}

/// The caller-side bridge carried by a seam spec.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Bridge {
    pub(crate) offset_bytes: u64,
    /// `None` renders the fallback arm.
    pub(crate) len_text: Option<String>,
    pub(crate) fallback_len_text: String,
    /// The caller's argument is a DELIVERED slice: a width reader takes a
    /// checked prefix of it (`&s[..N]`), no raw pointer in between.
    pub(crate) from_slice: bool,
}

impl Bridge {
    pub(crate) fn of(region: &Region) -> Self {
        Self {
            offset_bytes: region.offset_bytes,
            len_text: region.len_text(),
            fallback_len_text: region.fallback_len_text(),
            from_slice: false,
        }
    }

    pub(crate) fn from_slice(region: &Region) -> Self {
        Self {
            from_slice: true,
            ..Self::of(region)
        }
    }

    /// Is this a width reader's exact-width bridge (never a fallback, never an
    /// accessor region)? The only bridge a computed slice view may feed.
    pub(crate) fn reads_width(&self) -> bool {
        self.offset_bytes == 0 && self.len_text.is_some() && !self.from_slice
    }

    /// The same width read over a slice view supplied by the caller (wave-6s's
    /// computed suffix): a checked prefix of that view.
    pub(crate) fn as_prefix_of_view(&self) -> Self {
        Self {
            from_slice: true,
            ..self.clone()
        }
    }

    /// `&(<slice>)[..N]` — the reader's width as a checked prefix of the
    /// caller's own slice. Safe: no `unsafe` wrapper.
    pub(crate) fn render_slice(&self, text: &str) -> String {
        format!("&({text})[..{}]", self.len_text())
    }

    pub(crate) fn len_text(&self) -> &str {
        self.len_text.as_deref().unwrap_or(&self.fallback_len_text)
    }

    /// The raw byte pointer at the region's offset, from the caller's own
    /// buffer expression.
    pub(crate) fn pointer_text(&self, text: &str, mutable: bool) -> String {
        let pointer = if mutable { "mut" } else { "const" };
        if self.offset_bytes == 0 {
            format!("(({text}) as *{pointer} u8)")
        } else {
            format!("(({text}) as *{pointer} u8).add({})", self.offset_bytes)
        }
    }

    /// `core::slice::from_raw_parts_mut(<pointer>, <len>)`, to be wrapped in
    /// `unsafe` by the caller's context rule.
    pub(crate) fn render(&self, text: &str, mutable: bool) -> String {
        let ctor = if mutable {
            "from_raw_parts_mut"
        } else {
            "from_raw_parts"
        };
        format!(
            "core::slice::{ctor}({}, {})",
            self.pointer_text(text, mutable),
            self.len_text()
        )
    }
}

/// The inbound retention receipt for a region position. The accessor hands
/// its region back to the caller as a raw pointer by design; the width reader
/// retains nothing. Both are receipted, never inferred: the accessor's
/// return-carried alias takes the T2 waiver every return-carried alias takes,
/// the reader is T1.
pub(crate) fn retention(
    region: &Region,
) -> (
    crate::bo_rewriter::bridge_receipt::BridgeRetentionTier,
    Option<String>,
) {
    use crate::bo_rewriter::bridge_receipt::BridgeRetentionTier;
    match region.shape {
        // A byte view is a local's own reborrow; a width read or write calls
        // nothing and keeps nothing.
        Shape::WidthRead | Shape::WidthWrite | Shape::ByteView => (BridgeRetentionTier::T1, None),
        Shape::Accessor => (
            BridgeRetentionTier::T2,
            Some(crate::bo_rewriter::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID.to_owned()),
        ),
    }
}

/// The AST layer's bridge: the rendered template parsed once with a
/// placeholder, and the caller's own argument SUBTREE substituted for it —
/// never re-parsed from text.
pub(crate) fn bridge_ast(
    bridge: &Bridge,
    mutable: bool,
    argument: &rustc_ast::Expr,
    enclosing_unsafe_fn: bool,
) -> Option<rustc_ast::ExprKind> {
    use rustc_ast::mut_visit::MutVisitor;
    const ARG: &str = "__CRAT_VOID_REGION_ARG";
    let rendered = if bridge.from_slice {
        bridge.render_slice(ARG)
    } else {
        crate::bo_rewriter::mechanical_receipt::present_unsafe_text(
            bridge.render(ARG, mutable),
            enclosing_unsafe_fn,
        )
    };
    let mut parsed = crate::bo_rewriter::ast_transform::graft_expr(&rendered).ok()?;

    struct Replace {
        argument: rustc_ast::Expr,
        hits: usize,
    }
    impl MutVisitor for Replace {
        fn visit_expr(&mut self, expr: &mut rustc_ast::Expr) {
            if matches!(
                &expr.kind,
                rustc_ast::ExprKind::Path(None, path)
                    if path.segments.len() == 1
                        && path.segments[0].ident.name == rustc_span::Symbol::intern(ARG)
            ) {
                *expr = self.argument.clone();
                self.hits += 1;
                return;
            }
            rustc_ast::mut_visit::walk_expr(self, expr);
        }
    }

    let mut replace = Replace {
        argument: rustc_ast::Expr {
            id: rustc_ast::DUMMY_NODE_ID,
            kind: argument.kind.clone(),
            span: argument.span,
            attrs: Default::default(),
            tokens: None,
        },
        hits: 0,
    };
    replace.visit_expr(&mut parsed);
    (replace.hits == 1).then_some(parsed.kind)
}

/// Does a region rewrite own this address-view site? The `p as *mut T` cast
/// of a chain root is inside the returned expression the rewrite replaces, so
/// the raw-boundary bridge for it renders no syntax of its own.
pub(crate) fn owns_address(
    table: &super::DecisionTable,
    site: &super::raw_boundary::AddressViewSite,
) -> bool {
    if site.op != "ptr-cast" {
        return false;
    }
    let Some(region) = table.void_region.get(&site.node) else { return false };
    table.entries.iter().any(|(s, d)| {
        (s.fn_did, s.hir_id) == site.node && decided_slice(d) && region.replaced.contains(site.span)
    })
}

/// The byte range a caller-side bridge claims: the exact region, or the
/// fallback arm's `FALLBACK_SLICE_EXTENT` elements.
fn claimed_range(region: &Region) -> (u64, u64) {
    let len = region
        .len_bytes
        .unwrap_or(super::seam::FALLBACK_SLICE_EXTENT as u64 * region.element_size);
    (region.offset_bytes, region.offset_bytes.saturating_add(len))
}

/// Accessor call sites that cannot be bridged: two accessor regions of ONE
/// buffer expression in ONE caller whose claimed ranges overlap. An accessor
/// hands its caller a raw pointer derived from the bridged view, and a later
/// mutable retag of an overlapping range from the same raw root invalidates
/// it (Stacked Borrows); disjoint ranges are what the chain guarantees, and
/// this is the check that the guarantee is not crossed by a second chain or a
/// twin view over the same bytes.
pub(crate) fn overlapping_calls(
    tcx: TyCtxt<'_>,
    facts: &super::emitability::EmitabilityFacts,
    table: &super::DecisionTable,
) -> rustc_hash::FxHashSet<(LocalDefId, Span)> {
    let sm = tcx.sess.source_map();
    // (caller, buffer text) -> [(call span, range)]
    let mut by_buffer: FxHashMap<(LocalDefId, String), Vec<(Span, (u64, u64))>> =
        FxHashMap::default();
    for (callee, sites) in &facts.call_args {
        for site in sites {
            for arg in &site.args {
                let Some(region) = parameter(table, *callee, arg.index) else { continue };
                if region.shape != Shape::Accessor {
                    continue;
                }
                let Ok(text) = sm.span_to_snippet(arg.span) else { continue };
                let text: String = text.chars().filter(|c| !c.is_whitespace()).collect();
                by_buffer
                    .entry((site.caller, text))
                    .or_default()
                    .push((site.span, claimed_range(region)));
            }
        }
    }
    let mut blocked = rustc_hash::FxHashSet::default();
    for ((caller, _), calls) in by_buffer {
        for (i, (span, (lo, hi))) in calls.iter().enumerate() {
            let overlaps = calls
                .iter()
                .enumerate()
                .any(|(j, (_, (other_lo, other_hi)))| i != j && lo < other_hi && other_lo < hi);
            if overlaps {
                blocked.insert((caller, *span));
            }
        }
    }
    blocked
}

// ---------------------------------------------------------------------------
// Build 3 — region receivers: the caller local that receives an accessor's
// raw result becomes a typed slice over the region.
// ---------------------------------------------------------------------------

/// One caller local `let L = A(buffer)` where `A` is an admitted accessor:
/// `L` is declared `&mut [T]` / `&[T]` and the raw result is wrapped with the
/// region's exact element count (the fallback count for a last region).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Receiver {
    pub(crate) node: Key,
    pub(crate) callee: LocalDefId,
    pub(crate) initializer_hir: HirId,
    pub(crate) initializer_span: Span,
    /// The element type as the callee's raw return spells it, resolved.
    pub(crate) element: String,
    pub(crate) mutable: bool,
    /// The element count text: exact, or the named fallback const.
    pub(crate) count_text: String,
    pub(crate) fabricated: bool,
    /// The caller is an `unsafe fn`: no redundant inner `unsafe` block.
    pub(crate) enclosing_unsafe_fn: bool,
    /// A byte view: the scalar parameter viewed, in the same function
    /// (`callee` is then the function itself and carries no dependency).
    pub(crate) parameter: Option<HirId>,
}

pub(crate) type Receivers = FxHashMap<Key, Receiver>;

impl Receiver {
    pub(crate) fn declared_type(&self) -> String {
        format!(
            "&{}[{}]",
            if self.mutable { "mut " } else { "" },
            self.element
        )
    }

    /// The initializer with the adapted call inside: the raw result of the
    /// accessor becomes a slice of exactly the region's elements.
    pub(crate) fn render(&self, adapted_call: &str) -> String {
        let ctor = if self.mutable {
            "from_raw_parts_mut"
        } else {
            "from_raw_parts"
        };
        crate::bo_rewriter::mechanical_receipt::present_unsafe_text(
            format!("core::slice::{ctor}({adapted_call}, {})", self.count_text),
            self.enclosing_unsafe_fn,
        )
    }
}

/// Every local initialised by a direct call to an admitted accessor whose own
/// shape wants a slice. The decision ladder still decides the local (its uses,
/// its sign, its construction); this only names the receiver the veto may
/// admit and the emitter must type.
pub(crate) fn receivers(
    tcx: TyCtxt<'_>,
    subjects: &[Subject],
    constructions: &super::construction::ConstructionFacts,
    contracts: &Contracts,
) -> Receivers {
    use super::construction::{CallResultTarget, Construction};
    let mut out = Receivers::default();
    for subject in subjects {
        if subject.kind != SubjectKind::Local || subject.ty_span.is_some() {
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        if constructions.by_binding.get(&node) != Some(&Construction::CallResult) {
            continue;
        }
        let Some(CallResultTarget::DirectLocal(callee)) =
            constructions.call_result_targets.get(&node).copied()
        else {
            continue;
        };
        let Some(region) = contracts
            .iter()
            .find(|((owner, _), _)| *owner == callee)
            .map(|(_, region)| region)
        else {
            continue;
        };
        if region.shape != Shape::Accessor || (subject.mutable && !region.mutable) {
            continue;
        }
        let (Some(&initializer_hir), Some(&initializer_span)) = (
            constructions.init_hirs.get(&node),
            constructions.init_spans.get(&node),
        ) else {
            continue;
        };
        let initializer = tcx.hir_node(initializer_hir).expect_expr();
        let exact = match initializer.kind {
            ExprKind::Call(function, _) => matches!(function.kind,
                ExprKind::Path(QPath::Resolved(_, path))
                    if matches!(path.res, Res::Def(_, did) if did == callee.to_def_id())),
            _ => false,
        };
        if !exact || initializer.span != initializer_span {
            continue;
        }
        let signature = tcx.fn_sig(callee).skip_binder().skip_binder();
        let TyKind::RawPtr(pointee, _) = signature.output().kind() else { continue };
        let element = super::declaration::pointee_source(tcx, *pointee);
        let (count_text, fabricated) = match region.len_bytes {
            Some(bytes) if region.element_size > 0 && bytes % region.element_size == 0 => {
                ((bytes / region.element_size).to_string(), false)
            }
            Some(_) => continue,
            None => (super::seam::FABRICATED_LEN_PATH.to_owned(), true),
        };
        out.insert(
            node,
            Receiver {
                node,
                callee,
                initializer_hir,
                initializer_span,
                element,
                mutable: subject.mutable,
                count_text,
                fabricated,
                enclosing_unsafe_fn: tcx
                    .fn_sig(subject.fn_did)
                    .skip_binder()
                    .skip_binder()
                    .safety
                    .is_unsafe(),
                parameter: None,
            },
        );
    }
    // Byte views: the local's initializer (the cast of the parameter) is
    // wrapped as a slice of exactly the scalar's bytes.
    for subject in subjects {
        let Some(view) = read_byte_view(tcx, subject) else { continue };
        let node = (subject.fn_did, subject.hir_id);
        if !contracts.contains_key(&node) {
            continue;
        }
        out.insert(
            node,
            Receiver {
                node,
                callee: subject.fn_did,
                initializer_hir: view.initializer,
                initializer_span: view.initializer_span,
                element: "u8".to_owned(),
                mutable: subject.mutable,
                count_text: format!("core::mem::size_of::<{}>()", view.scalar),
                fabricated: false,
                enclosing_unsafe_fn: tcx
                    .fn_sig(subject.fn_did)
                    .skip_binder()
                    .skip_binder()
                    .safety
                    .is_unsafe(),
                parameter: Some(view.parameter),
            },
        );
    }
    out
}

/// The veto's question: is this unannotated local a region receiver whose
/// ladder decision is the slice it wants?
pub(crate) fn receives_region(receivers: &Receivers, node: Key, mutable: bool) -> bool {
    receivers
        .get(&node)
        .is_some_and(|receiver| receiver.mutable == mutable)
}

/// The explicit declaration of every delivered region receiver — the type the
/// custody instrument requires a delivered local to carry — and its receipt.
pub(crate) fn append_receiver_declarations(table: &mut super::DecisionTable) {
    use crate::bo_rewriter::bridge_receipt::{BridgeRetentionTier, SignatureClassId};
    let mut declarations = Vec::new();
    let mut bridges = Vec::new();
    for (subject, decision) in &table.entries {
        let node = (subject.fn_did, subject.hir_id);
        let Some(receiver) = table.void_region_receivers.get(&node) else { continue };
        let admitted = match decision {
            super::Decision::Slice { mutable, .. } => *mutable == receiver.mutable,
            super::Decision::Ref { .. }
            | super::Decision::InferredRef { .. }
            | super::Decision::NestedSlice { .. }
            | super::Decision::Opt { .. }
            | super::Decision::Box(_)
            | super::Decision::Cursor { .. }
            | super::Decision::Degraded(_) => false,
        };
        if !admitted || !source_delivered(table, receiver) {
            continue;
        }
        let Some(name) = subject.param_name.as_deref() else { continue };
        let owner_class = SignatureClassId::of(receiver.callee);
        let emitted_type = receiver.declared_type();
        let binding_prefix = if subject.mut_binding { "mut " } else { "" };
        declarations.push(super::seam::ExplicitDeclarationSite {
            owner_class,
            caller: subject.fn_did,
            node: Some(node),
            span: Some(subject.binding_span),
            category: "local",
            replacement: Some(format!("{binding_prefix}{name}: {emitted_type}")),
            emitted_type: emitted_type.clone(),
            arm: "glue",
        });
        bridges.push(super::seam::ZeroBridgeSite {
            owner_class,
            caller: subject.fn_did,
            span: Some(receiver.initializer_span),
            arm: "c",
            position: format!(
                "region-receiver:type={emitted_type}:count={}:{}",
                receiver.count_text,
                if receiver.fabricated {
                    "len-fabricated"
                } else {
                    "len-elsewhere"
                }
            ),
            bridge_kind: "void-region-receiver",
            expected_form: receiver.declared_form(),
            found_form: "raw",
            argument_kind: if receiver.parameter.is_some() {
                "byte-view-of-scalar"
            } else {
                "return-call-result"
            },
            // A byte view is a reborrow of the parameter's own storage in the
            // same body — nothing is called, nothing can retain it (T1). An
            // accessor's raw result is return-carried (T2, the waiver).
            retention: if receiver.parameter.is_some() {
                BridgeRetentionTier::T1
            } else {
                BridgeRetentionTier::T2
            },
            waiver_id: receiver
                .parameter
                .is_none()
                .then(|| crate::bo_rewriter::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID.to_owned()),
            unsafe_context: None,
        });
    }
    table.seams.explicit_declarations.extend(declarations);
    table.seams.zero_bridges.extend(bridges);
}

impl Receiver {
    pub(crate) fn declared_form(&self) -> &'static str {
        if self.mutable {
            "slice-mut"
        } else {
            "slice-shared"
        }
    }
}

/// The receivers whose local is delivered as the slice and whose class is kept.
pub(crate) fn delivered_receivers<'a>(
    table: &'a super::DecisionTable,
    reverts: &crate::bo_rewriter::ast_transform::RevertSet,
) -> Vec<&'a Receiver> {
    use crate::bo_rewriter::bridge_receipt::SignatureClassId;
    let mut out = table
        .entries
        .iter()
        .filter_map(|(subject, decision)| {
            let node = (subject.fn_did, subject.hir_id);
            let receiver = table.void_region_receivers.get(&node)?;
            let delivered = match decision {
                super::Decision::Slice { mutable, .. } => *mutable == receiver.mutable,
                super::Decision::Ref { .. }
                | super::Decision::InferredRef { .. }
                | super::Decision::NestedSlice { .. }
                | super::Decision::Opt { .. }
                | super::Decision::Box(_)
                | super::Decision::Cursor { .. }
                | super::Decision::Degraded(_) => false,
            };
            (delivered
                && source_delivered(table, receiver)
                && reverts.keeps(SignatureClassId::of(receiver.callee))
                && reverts.keeps(SignatureClassId::of(subject.fn_did))
                && reverts.keeps_subject(subject.fn_did, subject.hir_id))
            .then_some(receiver)
        })
        .collect::<Vec<_>>();
    out.sort_by_key(|receiver| {
        (
            receiver.node.0.local_def_index.as_u32(),
            receiver.node.1.local_id.as_u32(),
        )
    });
    out
}

/// Is this subject a delivered region receiver whose explicit declaration
/// site is planned? The plan then places it by its binding (no type splice of
/// its own) and the AST declaration pass leaves it to the explicit-type pass.
pub(crate) fn typed_receiver(
    table: &super::DecisionTable,
    subject: &Subject,
    decision: &super::Decision,
) -> bool {
    use crate::bo_rewriter::bridge_receipt::SignatureClassId;
    let node = (subject.fn_did, subject.hir_id);
    let Some(receiver) = table.void_region_receivers.get(&node) else { return false };
    let delivered = match decision {
        super::Decision::Slice { mutable, .. } => *mutable == receiver.mutable,
        super::Decision::Ref { .. }
        | super::Decision::InferredRef { .. }
        | super::Decision::NestedSlice { .. }
        | super::Decision::Opt { .. }
        | super::Decision::Box(_)
        | super::Decision::Cursor { .. }
        | super::Decision::Degraded(_) => false,
    };
    delivered
        && source_delivered(table, receiver)
        && table.seams.explicit_declarations.iter().any(|site| {
            site.category == "local"
                && site.node == Some(node)
                && site.owner_class == SignatureClassId::of(receiver.callee)
                && site.emitted_type == receiver.declared_type()
        })
}

/// Is the accessor's own region parameter decided as the byte slice in this
/// table? A receiver over an accessor that fell back to its raw parameter is
/// not emitted: the two must move together. A byte view has no accessor: it
/// is emitted unless it writes through a parameter decided as a SHARED safe
/// form (the seam would bridge `from_ref(p).cast_mut()`, and a write through
/// that is UB).
fn source_delivered(table: &super::DecisionTable, receiver: &Receiver) -> bool {
    match receiver.parameter {
        Some(parameter) => {
            !receiver.mutable
                || table.entries.iter().any(|(s, d)| {
                    s.fn_did == receiver.callee
                        && s.hir_id == parameter
                        && !matches!(
                            super::seam::form_of(d),
                            super::seam::Form::Ref { mutable: false }
                                | super::seam::Form::Opt { mutable: false, .. }
                                | super::seam::Form::Slice { mutable: false }
                        )
                })
        }
        None => table.entries.iter().any(|(s, d)| {
            s.fn_did == receiver.callee
                && table.void_region.contains_key(&(s.fn_did, s.hir_id))
                && decided_slice(d)
        }),
    }
}

/// Every class of a chain that is NOT whole in this table: one link's region
/// is not the byte slice it contracted for (a later family stage withdrew it,
/// or a composed rule decided it otherwise), so the SIBLING links' bodies —
/// which name this link's signature inside
/// `(Inner as unsafe extern "C" fn(*mut c_void) -> *mut T)(p)` — would keep a
/// spelling that no longer exists. [`collect`] admits a chain only whole; this
/// is the same rule read from the finished table, where the withdrawal is
/// visible and a class dependency is not (a withdrawn link has no class for an
/// edge to point at).
pub(crate) fn chain_holds(
    table: &super::DecisionTable,
) -> Vec<crate::bo_rewriter::bridge_receipt::SignatureClassId> {
    use crate::bo_rewriter::bridge_receipt::SignatureClassId;
    let delivered = |owner: LocalDefId| {
        table.entries.iter().any(|(s, d)| {
            s.fn_did == owner
                && table.void_region.contains_key(&(s.fn_did, s.hir_id))
                && decided_slice(d)
        })
    };
    let mut broken: Vec<LocalDefId> = Vec::new();
    for ((owner, _), region) in &table.void_region {
        let Some(inner) = region.inner else { continue };
        if delivered(*owner) != delivered(inner) {
            broken.push(*owner);
            broken.push(inner);
        }
    }
    // A chain is transitive: a broken link at any depth takes every link that
    // reaches it, so the walk repeats until the set stops growing.
    loop {
        let before = broken.len();
        for ((owner, _), region) in &table.void_region {
            let Some(inner) = region.inner else { continue };
            if (broken.contains(owner) || broken.contains(&inner))
                && !(broken.contains(owner) && broken.contains(&inner))
            {
                broken.push(*owner);
                broken.push(inner);
            }
        }
        if broken.len() == before {
            break;
        }
    }
    broken.sort_by_key(|did| did.local_def_index.as_u32());
    broken.dedup();
    broken.into_iter().map(SignatureClassId::of).collect()
}

/// The class dependencies a CHAIN introduces — both ways, so the links are one
/// atomic unit (R447-4; the planner puts a mutually-reaching pair in one
/// dependency SCC, so this adds no cycle to its ordering).
///
/// Measured on brotli at the batch-9 census head: 45 of the 49 `c_void` ↔ byte
/// compile failures are one link of an H4x chain changing its parameter while a
/// sibling link keeps the body that names the OLD signature —
/// `(AddrH40 as unsafe extern "C" fn(*mut c_void) -> *mut u32)(extra)` against
/// an `AddrH40` whose parameter is now `&mut [u8]`. [`collect`] admits a chain
/// only whole, but a LATER withdrawal is not its to see; this is that rule
/// carried to the stage where withdrawals happen.
pub(crate) fn chain_dependencies(
    table: &super::DecisionTable,
) -> Vec<(
    crate::bo_rewriter::bridge_receipt::SignatureClassId,
    crate::bo_rewriter::bridge_receipt::SignatureClassId,
)> {
    use crate::bo_rewriter::bridge_receipt::SignatureClassId;
    table
        .void_region
        .iter()
        .filter_map(|((owner, _), region)| region.inner.map(|inner| (*owner, inner)))
        .flat_map(|(outer, inner)| {
            [
                (SignatureClassId::of(outer), SignatureClassId::of(inner)),
                (SignatureClassId::of(inner), SignatureClassId::of(outer)),
            ]
        })
        .collect()
}

/// The class dependency each delivered region receiver introduces: the
/// caller's class depends on the accessor's, so a withdrawn accessor takes
/// its receivers with it.
pub(crate) fn receiver_dependencies(
    table: &super::DecisionTable,
) -> Vec<(
    crate::bo_rewriter::bridge_receipt::SignatureClassId,
    crate::bo_rewriter::bridge_receipt::SignatureClassId,
)> {
    use crate::bo_rewriter::bridge_receipt::SignatureClassId;
    table
        .entries
        .iter()
        .filter(|(subject, decision)| typed_receiver(table, subject, decision))
        .filter_map(|(subject, _)| {
            let receiver = table
                .void_region_receivers
                .get(&(subject.fn_did, subject.hir_id))?;
            if receiver.parameter.is_some() {
                return None;
            }
            Some((
                SignatureClassId::of(subject.fn_did),
                SignatureClassId::of(receiver.callee),
            ))
        })
        .collect()
}

/// Does an admitted region rewrite of `owner` replace the expression this
/// span lies in? A seam site there (the inner accessor call's own argument,
/// the root cast) renders no syntax of its own: the rewrite replaces the whole
/// returned expression.
pub(crate) fn owns_span(table: &super::DecisionTable, owner: LocalDefId, span: Span) -> bool {
    table.entries.iter().any(|(s, d)| {
        s.fn_did == owner
            && decided_slice(d)
            && table
                .void_region
                .get(&(s.fn_did, s.hir_id))
                .is_some_and(|region| region.replaced.contains(span))
    })
}

/// The veto's question in its decision-shaped form — asked by this lane's own
/// arm and by any constructor-typing refusal that must let a receiver answer
/// first: is this local a region receiver whose ladder decision is its slice?
pub(crate) fn receiver_form_matches(
    receivers: &Receivers,
    node: Key,
    decision: &super::Decision,
) -> bool {
    match decision {
        super::Decision::Slice { mutable, .. } => receives_region(receivers, node, *mutable),
        super::Decision::Ref { .. }
        | super::Decision::InferredRef { .. }
        | super::Decision::NestedSlice { .. }
        | super::Decision::Opt { .. }
        | super::Decision::Box(_)
        | super::Decision::Cursor { .. }
        | super::Decision::Degraded(_) => false,
    }
}
