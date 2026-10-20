//! **wave-6l relay 071 (R697-7): the field-carried allocation length.**
//!
//! A struct's pointer field `P` whose every non-null write is an allocation
//! plus a literal offset, made in a function that also writes an unsigned
//! integer field `C` of the same object, straight-line beside it, so that the
//! allocation's elements past the offset are `C + k`, holds `C + k` elements
//! wherever it is read (brotli's `RingBufferInitBuffer`: `data_ = alloc(2 +
//! buflen + 7)`, `cur_size_ = buflen`, `buffer_ = data_ + 2`, so `buffer_`
//! holds `cur_size_ + 7`). The seam renders that length where a construction's
//! argument is `P` read from an object (receipted `len-field-alloc`), before
//! the fallback.
//!
//! **What refuses a licence** (the relay 071 review's findings in brackets):
//! a write to `P` that is neither null nor such an allocation; a write to `C`
//! in a function that writes `P` only as null, unless it writes `0` (1); a
//! local in the allocation or the length reassigned in its function (2); the
//! allocation stored, or the length written, other than straight-line beside
//! the pointer's write in one block (3, 4); `size_of::<T>()` of a `T` that is
//! not the pointee (5); a whole-object write of the struct or of one that
//! embeds it, or its address handed to a writing callee (`memcpy`,
//! `ptr::write`, a foreign function) (6); a compound write or an escaped
//! `&mut` of either field, including in a closure (7); a signed `C` (10); a
//! negative `k`. Closures and static initializers are scanned.
//!
//! **What refuses a use:** the calling function may write `P` or `C`
//! (directly, through a local, method or indirect call, or a closure), so the
//! field may be reallocated between the read and the construction; the base is
//! not `(*root).f..` (an inner dereference reaches another object) (6); the
//! argument's pointee is not the field's size (5); or the argument is a local
//! not defined only from `P` of one object, whose root is reassigned, borrowed
//! mutably, or which may still hold its null initializer at the call (8).

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, LetStmt, Node, PatKind,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_span::{BytePos, Span, Symbol};

/// One licence: `(*x).pointer` holds `(*x).length + slack` elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Licence {
    pub(crate) strukt: String,
    pub(crate) pointer: String,
    pub(crate) length: String,
    pub(crate) slack: u128,
}

/// Every licence of the program, and the functions that may write a licensed
/// field (directly or through a call).
#[derive(Default)]
pub(crate) struct Licences {
    pub(crate) licences: Vec<Licence>,
    /// `(struct, pointer)` → `(length, slack, element size)`.
    keyed: FxHashMap<(DefId, Symbol), (Symbol, u128, u64)>,
    /// Per licence, the functions that may write its pointer or its length.
    may_write: FxHashMap<(DefId, Symbol), FxHashSet<LocalDefId>>,
}

/// A write to a struct field.
struct Write<'tcx> {
    function: LocalDefId,
    strukt: DefId,
    field: Symbol,
    /// The object's text (`(*rb)`), pairing writes to one object.
    base: String,
    /// `None`: a write whose value is unknown (compound, escaped address,
    /// whole object).
    value: Option<&'tcx Expr<'tcx>>,
    lo: BytePos,
    node: HirId,
}

fn flat(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join("")
}

fn peel<'a, 'tcx>(mut e: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    loop {
        match e.kind {
            ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => e = inner,
            _ => return e,
        }
    }
}

/// `base.field` of a struct (auto-dereferenced), with the struct and the base.
fn field_of<'tcx>(
    typeck: &rustc_middle::ty::TypeckResults<'tcx>,
    e: &'tcx Expr<'tcx>,
) -> Option<(DefId, Symbol, &'tcx Expr<'tcx>)> {
    let mut e = e;
    while let ExprKind::DropTemps(inner) = e.kind {
        e = inner;
    }
    let ExprKind::Field(base, ident) = e.kind else {
        return None;
    };
    let ty = typeck.expr_ty_adjusted(base).peel_refs();
    let TyKind::Adt(adt, _) = ty.kind() else {
        return None;
    };
    adt.is_struct().then_some((adt.did(), ident.name, base))
}

fn is_null(e: &Expr<'_>) -> bool {
    match peel(e).kind {
        ExprKind::Lit(lit) => matches!(lit.node, rustc_ast::LitKind::Int(n, _) if n.get() == 0),
        ExprKind::Call(callee, []) => matches!(
            callee.kind,
            ExprKind::Path(rustc_hir::QPath::Resolved(_, path))
                if path.segments.last().is_some_and(|s| matches!(s.ident.as_str(), "null" | "null_mut"))
        ),
        _ => false,
    }
}

fn local_of(e: &Expr<'_>) -> Option<HirId> {
    match peel(e).kind {
        ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

/// The struct types embedded by value in `ty`, `ty`'s own included.
fn embedded<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, out: &mut Vec<DefId>, depth: u32) {
    if depth > 8 {
        return;
    }
    match ty.kind() {
        TyKind::Adt(adt, args) if adt.is_struct() || adt.is_union() => {
            if out.contains(&adt.did()) {
                return;
            }
            out.push(adt.did());
            for field in adt.all_fields() {
                embedded(tcx, field.ty(tcx, args), out, depth + 1);
            }
        }
        TyKind::Array(inner, _) => embedded(tcx, *inner, out, depth + 1),
        _ => {}
    }
}

/// The writes of one body, the statics it assigns, its locals reassigned, and
/// the calls it makes.
struct Collect<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    function: LocalDefId,
    typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
    writes: &'a mut Vec<Write<'tcx>>,
    ref_mut: FxHashMap<HirId, (DefId, Symbol, String)>,
    statics_written: &'a mut FxHashSet<DefId>,
    calls: &'a mut FxHashMap<LocalDefId, FxHashSet<LocalDefId>>,
    indirect: &'a mut FxHashSet<LocalDefId>,
    address_taken: &'a mut FxHashSet<LocalDefId>,
    reassigned: &'a mut FxHashMap<LocalDefId, FxHashSet<HirId>>,
}

impl<'tcx> Collect<'_, 'tcx> {
    fn text(&self, e: &Expr<'_>) -> String {
        flat(
            &self
                .tcx
                .sess
                .source_map()
                .span_to_snippet(e.span)
                .unwrap_or_default(),
        )
    }

    fn write(
        &mut self,
        strukt: DefId,
        field: Symbol,
        base: String,
        value: Option<&'tcx Expr<'tcx>>,
        lo: BytePos,
        node: HirId,
    ) {
        self.writes.push(Write {
            function: self.function,
            strukt,
            field,
            base,
            value,
            lo,
            node,
        });
    }

    /// Every field of `ty` and of the structs it embeds, written unknown.
    fn whole(&mut self, ty: Ty<'tcx>, node: HirId, lo: BytePos) {
        let mut structs = Vec::new();
        embedded(self.tcx, ty, &mut structs, 0);
        for strukt in structs {
            let fields: Vec<Symbol> = self
                .tcx
                .adt_def(strukt)
                .all_fields()
                .map(|f| f.name)
                .collect();
            for field in fields {
                self.write(strukt, field, "<whole>".to_owned(), None, lo, node);
            }
        }
    }

    fn push(
        &mut self,
        place: &'tcx Expr<'tcx>,
        node: HirId,
        value: Option<&'tcx Expr<'tcx>>,
        assigned: bool,
    ) {
        if let Some((strukt, field, base)) = field_of(self.typeck, place) {
            let base = self.text(base);
            self.write(strukt, field, base, value, place.span.lo(), node);
        } else if let ExprKind::Unary(rustc_hir::UnOp::Deref, inner) = place.kind
            && let Some(binding) = local_of(inner)
            && let Some((strukt, field, base)) = self.ref_mut.get(&binding).cloned()
        {
            self.write(strukt, field, base, value, place.span.lo(), node);
        } else if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = peel(place).kind
            && let Res::Def(DefKind::Static { .. }, did) = path.res
        {
            self.statics_written.insert(did);
        }
        // A write of a whole struct value (`*rb = ..`, `(*s).rb = ..`) rewrites
        // every field it embeds.
        // (A `&mut` of a struct handed to a local callee is the callee's to
        // write, and its writes are seen there.)
        let ty = self.typeck.expr_ty(place);
        if assigned && matches!(ty.kind(), TyKind::Adt(adt, _) if adt.is_struct() || adt.is_union())
        {
            self.whole(ty, node, place.span.lo());
        }
        if let Some(local) = local_of(place) {
            self.reassigned
                .entry(self.function)
                .or_default()
                .insert(local);
        }
    }
}

impl<'tcx> Visitor<'tcx> for Collect<'_, 'tcx> {
    fn visit_local(&mut self, let_: &'tcx LetStmt<'tcx>) {
        if let PatKind::Binding(mode, id, ..) = let_.pat.kind
            && matches!(mode.0, rustc_hir::ByRef::Yes(rustc_hir::Mutability::Mut))
        {
            if let Some(init) = let_.init
                && let Some((strukt, field, base)) = field_of(self.typeck, init)
            {
                let base = self.text(base);
                self.ref_mut.insert(id, (strukt, field, base));
            }
            if let Some(init) = let_.init
                && let Some(local) = local_of(init)
            {
                self.reassigned
                    .entry(self.function)
                    .or_default()
                    .insert(local);
            }
        }
        intravisit::walk_local(self, let_);
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        match e.kind {
            ExprKind::Assign(lhs, rhs, _) => self.push(lhs, e.hir_id, Some(rhs), true),
            ExprKind::AssignOp(_, lhs, _) => self.push(lhs, e.hir_id, None, true),
            ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, place) => {
                self.push(place, e.hir_id, None, false)
            }
            ExprKind::Struct(_, fields, _) => {
                if let TyKind::Adt(adt, _) = self.typeck.expr_ty(e).kind()
                    && adt.is_struct()
                {
                    for field in fields.iter() {
                        self.write(
                            adt.did(),
                            field.ident.name,
                            format!("<literal@{:?}>", e.span.lo()),
                            Some(field.expr),
                            field.span.lo(),
                            e.hir_id,
                        );
                    }
                }
            }
            ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
                // A `ref mut` field binding used other than as `*b = ..` escapes.
                if let Res::Local(id) = path.res
                    && let Some((strukt, field, base)) = self.ref_mut.get(&id).cloned()
                {
                    let assigned = match self.tcx.parent_hir_node(e.hir_id) {
                        Node::Expr(
                            deref @ Expr {
                                kind: ExprKind::Unary(rustc_hir::UnOp::Deref, _),
                                ..
                            },
                        ) => matches!(
                            self.tcx.parent_hir_node(deref.hir_id),
                            Node::Expr(Expr { kind: ExprKind::Assign(lhs, ..), .. })
                                if lhs.hir_id == deref.hir_id
                        ),
                        _ => false,
                    };
                    if !assigned {
                        self.write(strukt, field, base, None, e.span.lo(), e.hir_id);
                    }
                }
                // A function named other than as a callee: its address is taken.
                if let Res::Def(DefKind::Fn | DefKind::AssocFn, did) = path.res
                    && let Some(local) = did.as_local()
                    && !matches!(
                        self.tcx.parent_hir_node(e.hir_id),
                        Node::Expr(Expr { kind: ExprKind::Call(callee, _), .. }) if callee.hir_id == e.hir_id
                    )
                {
                    self.address_taken.insert(local);
                }
            }
            ExprKind::Call(callee, args) => {
                let target = match callee.kind {
                    ExprKind::Path(ref qpath) => {
                        match self.typeck.qpath_res(qpath, callee.hir_id) {
                            Res::Def(DefKind::Fn | DefKind::AssocFn, did) => Some(did),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let local_target = target
                    .filter(|did| !self.tcx.is_foreign_item(*did))
                    .and_then(|did| did.as_local());
                match (target, local_target) {
                    (_, Some(local)) => {
                        self.calls.entry(self.function).or_default().insert(local);
                    }
                    (Some(did), None) => {
                        // A callee outside the program that is handed an
                        // object's address may write it (`memcpy`, `ptr::write`,
                        // a foreign function); `free` and a zeroing `memset`
                        // leave it null / zero.
                        let name = self.tcx.item_name(did);
                        let zeroing = name.as_str() == "memset"
                            && args.get(1).is_some_and(|value| is_null(value));
                        if name.as_str() != "free" && !zeroing {
                            for arg in args {
                                let ty = self.typeck.expr_ty(peel(arg));
                                if let TyKind::RawPtr(pointee, rustc_middle::ty::Mutability::Mut)
                                | TyKind::Ref(_, pointee, rustc_middle::ty::Mutability::Mut) =
                                    ty.kind()
                                {
                                    self.whole(*pointee, e.hir_id, e.span.lo());
                                }
                            }
                        }
                    }
                    (None, None) => {
                        self.indirect.insert(self.function);
                    }
                }
            }
            ExprKind::MethodCall(..) => {
                if let Some(did) = self.typeck.type_dependent_def_id(e.hir_id)
                    && let Some(local) = did.as_local()
                    && matches!(self.tcx.def_kind(did), DefKind::Fn | DefKind::AssocFn)
                {
                    self.calls.entry(self.function).or_default().insert(local);
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }
}

/// A linear form over locals: `constant + Σ coefficient · atom`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Linear {
    constant: i128,
    atoms: Vec<(String, i128)>,
}

impl Linear {
    fn add(mut self, other: Linear, sign: i128) -> Linear {
        self.constant += sign * other.constant;
        for (atom, c) in other.atoms {
            if let Some(slot) = self.atoms.iter_mut().find(|(a, _)| *a == atom) {
                slot.1 += sign * c;
            } else {
                self.atoms.push((atom, sign * c));
            }
        }
        self.atoms.retain(|(_, c)| *c != 0);
        self.atoms.sort();
        self
    }
}

struct Program<'tcx> {
    tcx: TyCtxt<'tcx>,
    writes: Vec<Write<'tcx>>,
    statics_written: FxHashSet<DefId>,
    reassigned: FxHashMap<LocalDefId, FxHashSet<HirId>>,
}

/// The block and statement index holding `node`, if it is (in) a statement.
fn statement_of(tcx: TyCtxt<'_>, node: HirId) -> Option<(HirId, usize)> {
    let mut child = node;
    for (id, parent) in tcx.hir_parent_iter(node) {
        if let Node::Block(block) = parent {
            let index = block.stmts.iter().position(|s| s.hir_id == child)?;
            return Some((id, index));
        }
        child = id;
    }
    None
}

/// The relay 071 review's (3)/(4): `a` and `b` are statements of one block
/// with nothing but straight-line code between them (no call, branch, loop or
/// exit), `a` first when `ordered`.
fn straight(tcx: TyCtxt<'_>, a: HirId, b: HirId, ordered: bool) -> bool {
    let (Some((block_a, index_a)), Some((block_b, index_b))) =
        (statement_of(tcx, a), statement_of(tcx, b))
    else {
        return false;
    };
    if block_a != block_b || (ordered && index_a >= index_b) {
        return false;
    }
    let Node::Block(block) = tcx.hir_node(block_a) else {
        return false;
    };
    let (low, high) = (index_a.min(index_b), index_a.max(index_b));
    struct Flow(bool);
    impl<'tcx> Visitor<'tcx> for Flow {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if matches!(
                e.kind,
                ExprKind::Call(..)
                    | ExprKind::MethodCall(..)
                    | ExprKind::If(..)
                    | ExprKind::Match(..)
                    | ExprKind::Loop(..)
                    | ExprKind::Ret(..)
                    | ExprKind::Break(..)
                    | ExprKind::Continue(..)
                    | ExprKind::Closure(..)
            ) {
                self.0 = true;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut flow = Flow(false);
    for stmt in &block.stmts[low + 1..high] {
        flow.visit_stmt(stmt);
    }
    !flow.0
}

impl<'tcx> Program<'tcx> {
    fn reassigned(&self, function: LocalDefId, local: HirId) -> bool {
        self.reassigned
            .get(&function)
            .is_some_and(|set| set.contains(&local))
    }

    fn linear(&self, function: LocalDefId, e: &'tcx Expr<'tcx>) -> Option<Linear> {
        let e = peel(e);
        match e.kind {
            ExprKind::Lit(lit) => match lit.node {
                rustc_ast::LitKind::Int(n, _) => Some(Linear {
                    constant: i128::try_from(n.get()).ok()?,
                    atoms: Vec::new(),
                }),
                _ => None,
            },
            ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
                // (2) a local reassigned in its function is not one value.
                Res::Local(id) if !self.reassigned(function, id) => Some(Linear {
                    constant: 0,
                    atoms: vec![(format!("{id:?}"), 1)],
                }),
                // A static never assigned is its initializer.
                Res::Def(DefKind::Static { .. }, did) if !self.statics_written.contains(&did) => {
                    let local = did.as_local()?;
                    let body = self.tcx.hir_body_owned_by(local);
                    self.linear(local, body.value)
                }
                _ => None,
            },
            ExprKind::Binary(op, left, right) => {
                let sign = match op.node {
                    rustc_hir::BinOpKind::Add => 1,
                    rustc_hir::BinOpKind::Sub => -1,
                    _ => return None,
                };
                Some(
                    self.linear(function, left)?
                        .add(self.linear(function, right)?, sign),
                )
            }
            ExprKind::MethodCall(segment, receiver, [argument], _) => {
                let sign = match segment.ident.as_str() {
                    "wrapping_add" => 1,
                    "wrapping_sub" => -1,
                    _ => return None,
                };
                Some(
                    self.linear(function, receiver)?
                        .add(self.linear(function, argument)?, sign),
                )
            }
            _ => None,
        }
    }

    /// `n * size_of::<T>()` with `T` of the pointee's size (the review's (5)),
    /// or `n` alone for a one-byte pointee: the element count.
    fn elements(
        &self,
        function: LocalDefId,
        bytes: &'tcx Expr<'tcx>,
        element: u64,
    ) -> Option<&'tcx Expr<'tcx>> {
        let bytes = peel(bytes);
        let typeck = self.tcx.typeck(function);
        let size_of = |e: &Expr<'tcx>| {
            let ExprKind::Call(callee, []) = peel(e).kind else {
                return false;
            };
            let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = callee.kind else {
                return false;
            };
            if !path
                .segments
                .last()
                .is_some_and(|s| s.ident.as_str() == "size_of")
            {
                return false;
            }
            let args = typeck.node_args(callee.hir_id);
            args.types().next().is_some_and(|ty| {
                self.tcx
                    .layout_of(
                        rustc_middle::ty::TypingEnv::fully_monomorphized().as_query_input(ty),
                    )
                    .is_ok_and(|layout| layout.size.bytes() == element)
            })
        };
        match bytes.kind {
            ExprKind::MethodCall(segment, receiver, [argument], _)
                if segment.ident.as_str() == "wrapping_mul" && size_of(argument) =>
            {
                Some(receiver)
            }
            ExprKind::Binary(op, left, right)
                if matches!(op.node, rustc_hir::BinOpKind::Mul) && size_of(right) =>
            {
                Some(left)
            }
            ExprKind::MethodCall(segment, ..) if segment.ident.as_str() == "wrapping_mul" => None,
            ExprKind::Binary(op, ..) if matches!(op.node, rustc_hir::BinOpKind::Mul) => None,
            _ if element == 1 => Some(bytes),
            _ => None,
        }
    }

    /// The byte size an allocation-or-null expression allocates.
    fn allocation(
        &self,
        function: LocalDefId,
        e: &'tcx Expr<'tcx>,
        base: &str,
        at: HirId,
        depth: u32,
    ) -> Option<&'tcx Expr<'tcx>> {
        if depth > 6 {
            return None;
        }
        let e = peel(e);
        match e.kind {
            ExprKind::Call(callee, args) => {
                let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = callee.kind else {
                    return None;
                };
                match path.segments.last()?.ident.as_str() {
                    "malloc" => args.first(),
                    "BrotliAllocate" => args.get(1),
                    _ => None,
                }
            }
            ExprKind::If(_, then, Some(otherwise)) => {
                let tail = |e: &'tcx Expr<'tcx>| match e.kind {
                    ExprKind::Block(block, _) => block.expr,
                    _ => Some(e),
                };
                let (then, otherwise) = (tail(then)?, tail(otherwise)?);
                if is_null(otherwise) {
                    self.allocation(function, then, base, at, depth + 1)
                } else if is_null(then) {
                    self.allocation(function, otherwise, base, at, depth + 1)
                } else {
                    None
                }
            }
            ExprKind::Path(..) => {
                // A local defined once, at its `let`, never reassigned (2).
                let id = local_of(e)?;
                if self.reassigned(function, id) {
                    return None;
                }
                let Node::Pat(pat) = self.tcx.hir_node(id) else {
                    return None;
                };
                let Node::LetStmt(let_) = self.tcx.parent_hir_node(pat.hir_id) else {
                    return None;
                };
                self.allocation(function, let_.init?, base, at, depth + 1)
            }
            ExprKind::Field(..) => {
                // The same object's field, by its write straight-line before
                // here in this block (3).
                let typeck = self.tcx.typeck(function);
                let (strukt, field, field_base) = field_of(typeck, e)?;
                let text = flat(
                    &self
                        .tcx
                        .sess
                        .source_map()
                        .span_to_snippet(field_base.span)
                        .unwrap_or_default(),
                );
                if text != base {
                    return None;
                }
                let at_lo = self.tcx.hir_span(at).lo();
                let last = self
                    .writes
                    .iter()
                    .filter(|w| {
                        w.function == function
                            && w.strukt == strukt
                            && w.field == field
                            && w.base == base
                            && w.lo < at_lo
                    })
                    .max_by_key(|w| w.lo)?;
                if !straight(self.tcx, last.node, at, true) {
                    return None;
                }
                self.allocation(function, last.value?, base, last.node, depth + 1)
            }
            _ => None,
        }
    }

    /// The slack of one non-null pointer write, or `None` if it is not an
    /// allocation plus a literal offset matched by the same object's length.
    fn slack(&self, pointer: &Write<'tcx>, length_field: Symbol, element: u64) -> Option<u128> {
        let value = pointer.value?;
        let (source, offset) = match peel(value).kind {
            ExprKind::MethodCall(segment, receiver, [argument], _)
                if matches!(
                    segment.ident.as_str(),
                    "offset" | "add" | "wrapping_offset" | "wrapping_add"
                ) =>
            {
                (receiver, self.linear(pointer.function, argument)?)
            }
            _ => (value, Linear::default()),
        };
        if !offset.atoms.is_empty() || offset.constant < 0 {
            return None;
        }
        let bytes = self.allocation(pointer.function, source, &pointer.base, pointer.node, 0)?;
        let elements = self.linear(
            pointer.function,
            self.elements(pointer.function, bytes, element)?,
        )?;
        let lengths: Vec<_> = self
            .writes
            .iter()
            .filter(|w| {
                w.function == pointer.function
                    && w.strukt == pointer.strukt
                    && w.field == length_field
                    && w.base == pointer.base
            })
            .collect();
        let [length] = lengths.as_slice() else {
            return None;
        };
        // (4) the length written straight-line beside the pointer.
        if !straight(self.tcx, length.node, pointer.node, false) {
            return None;
        }
        let length = self.linear(pointer.function, length.value?)?;
        let difference = elements.add(length, -1);
        let slack = difference.constant - offset.constant;
        (difference.atoms.is_empty() && slack >= 0).then(|| slack as u128)
    }
}

impl Licences {
    pub(crate) fn infer(tcx: TyCtxt<'_>) -> Self {
        let mut writes = Vec::new();
        let mut statics_written = FxHashSet::default();
        let mut calls: FxHashMap<LocalDefId, FxHashSet<LocalDefId>> = FxHashMap::default();
        let mut indirect = FxHashSet::default();
        let mut address_taken = FxHashSet::default();
        let mut reassigned = FxHashMap::default();
        for owner in tcx.hir_body_owners() {
            // (7) closures are their function's; statics and constants are
            // scanned for their literals.
            let function = match tcx.def_kind(owner) {
                DefKind::Fn | DefKind::AssocFn => owner,
                DefKind::Closure => tcx.typeck_root_def_id(owner.to_def_id()).expect_local(),
                DefKind::Static { .. } | DefKind::Const | DefKind::AssocConst => owner,
                _ => continue,
            };
            let mut collect = Collect {
                tcx,
                function,
                typeck: tcx.typeck(owner),
                writes: &mut writes,
                ref_mut: FxHashMap::default(),
                statics_written: &mut statics_written,
                calls: &mut calls,
                indirect: &mut indirect,
                address_taken: &mut address_taken,
                reassigned: &mut reassigned,
            };
            collect.visit_body(tcx.hir_body_owned_by(owner));
        }
        // An indirect call may reach any function whose address is taken.
        for caller in &indirect {
            calls
                .entry(*caller)
                .or_default()
                .extend(address_taken.iter().copied());
        }
        let program = Program {
            tcx,
            writes,
            statics_written,
            reassigned,
        };
        let mut licences = Licences::default();
        let mut pointers: Vec<(DefId, Symbol)> =
            program.writes.iter().map(|w| (w.strukt, w.field)).collect();
        pointers.sort_by_key(|(d, f)| (tcx.def_path_str(*d), f.to_string()));
        pointers.dedup();
        for (strukt, pointer) in pointers {
            let adt = tcx.adt_def(strukt);
            if !adt.is_struct() {
                continue;
            }
            let fields: Vec<_> = adt.all_fields().collect();
            let Some(pointer_def) = fields.iter().find(|f| f.name == pointer) else {
                continue;
            };
            let TyKind::RawPtr(pointee, _) = tcx.type_of(pointer_def.did).skip_binder().kind()
            else {
                continue;
            };
            let Ok(layout) = tcx.layout_of(
                rustc_middle::ty::TypingEnv::fully_monomorphized().as_query_input(*pointee),
            ) else {
                continue;
            };
            let element = layout.size.bytes();
            if element == 0 {
                continue;
            }
            let pointer_writes: Vec<_> = program
                .writes
                .iter()
                .filter(|w| w.strukt == strukt && w.field == pointer)
                .collect();
            // (10) only an unsigned length.
            for length_def in fields
                .iter()
                .filter(|f| matches!(tcx.type_of(f.did).skip_binder().kind(), TyKind::Uint(_)))
            {
                let length = length_def.name;
                let length_writes: Vec<_> = program
                    .writes
                    .iter()
                    .filter(|w| w.strukt == strukt && w.field == length)
                    .collect();
                // A length write needs a pointer write of the same object in
                // its function; beside only null pointer writes it must be 0
                // (1). One beside an allocation is `slack`'s to check.
                let stray = length_writes.iter().any(|l| {
                    let beside: Vec<_> = pointer_writes
                        .iter()
                        .filter(|p| p.function == l.function && p.base == l.base)
                        .collect();
                    let Some(value) = l.value else {
                        return true;
                    };
                    beside.is_empty()
                        || (beside.iter().all(|p| p.value.is_some_and(is_null)) && !is_null(value))
                });
                if stray {
                    continue;
                }
                let mut slack = None;
                let mut ok = true;
                for write in &pointer_writes {
                    match write.value {
                        None => ok = false,
                        Some(value) if is_null(value) => {}
                        Some(_) => match program.slack(write, length, element) {
                            Some(k) if slack.is_none_or(|s| s == k) => slack = Some(k),
                            _ => ok = false,
                        },
                    }
                }
                if ok
                    && let Some(k) = slack
                    && !licences.keyed.contains_key(&(strukt, pointer))
                {
                    licences.licences.push(Licence {
                        strukt: tcx.item_name(strukt).to_string(),
                        pointer: pointer.to_string(),
                        length: length.to_string(),
                        slack: k,
                    });
                    licences
                        .keyed
                        .insert((strukt, pointer), (length, k, element));
                }
            }
        }
        // Per licence, the functions that write its pointer or its length, and
        // their callers.
        let mut may_write = FxHashMap::default();
        for (&(strukt, pointer), &(length, ..)) in &licences.keyed {
            let mut writers: FxHashSet<LocalDefId> = program
                .writes
                .iter()
                .filter(|w| w.strukt == strukt && (w.field == pointer || w.field == length))
                .map(|w| w.function)
                .collect();
            loop {
                let before = writers.len();
                for (caller, callees) in &calls {
                    if callees.iter().any(|c| writers.contains(c)) {
                        writers.insert(*caller);
                    }
                }
                if writers.len() == before {
                    break;
                }
            }
            may_write.insert((strukt, pointer), writers);
        }
        licences.may_write = may_write;
        licences
    }

    /// The rendered length of the argument at `span` of a call in `caller`
    /// (see [`Self::length_of`]).
    pub(crate) fn length_at(
        &self,
        tcx: TyCtxt<'_>,
        caller: LocalDefId,
        span: Span,
    ) -> Option<String> {
        if self.keyed.is_empty() {
            return None;
        }
        struct Find<'tcx> {
            span: Span,
            found: Option<&'tcx Expr<'tcx>>,
        }
        impl<'tcx> Visitor<'tcx> for Find<'tcx> {
            fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                if self.found.is_none() && e.span == self.span {
                    self.found = Some(e);
                }
                intravisit::walk_expr(self, e);
            }
        }
        let mut find = Find { span, found: None };
        find.visit_body(tcx.hir_body_owned_by(caller));
        self.length_of(tcx, caller, find.found?)
    }

    /// The rendered length of `arg`, an argument of a call in `caller`, when
    /// it is a licensed field read: directly, or through a local defined only
    /// from one object's licensed field (or its null initializer, overwritten
    /// before the call), whose object is `(*root).f..` with `root` not
    /// reassigned, in a function that cannot write the licensed fields.
    pub(crate) fn length_of<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        caller: LocalDefId,
        arg: &'tcx Expr<'tcx>,
    ) -> Option<String> {
        if self.keyed.is_empty() {
            return None;
        }
        let typeck = tcx.typeck(caller);
        let text = |e: &Expr<'_>| {
            flat(
                &tcx.sess
                    .source_map()
                    .span_to_snippet(e.span)
                    .unwrap_or_default(),
            )
        };
        let pointee_size = |ty: Ty<'tcx>| match ty.kind() {
            TyKind::RawPtr(pointee, _) | TyKind::Ref(_, pointee, _) => tcx
                .layout_of(
                    rustc_middle::ty::TypingEnv::fully_monomorphized().as_query_input(*pointee),
                )
                .ok()
                .map(|layout| layout.size.bytes()),
            _ => None,
        };
        // (6) `(*root).f..` or `root.f..`, no inner dereference.
        let root_of = |base: &'tcx Expr<'tcx>| -> Option<HirId> {
            let mut e = base;
            while let ExprKind::Field(inner, _) = e.kind {
                e = inner;
            }
            match e.kind {
                ExprKind::Unary(rustc_hir::UnOp::Deref, inner) => local_of(inner),
                ExprKind::Path(..) => local_of(e),
                _ => None,
            }
        };
        let licensed =
            |e: &'tcx Expr<'tcx>| -> Option<(String, Symbol, u128, HirId, (DefId, Symbol))> {
                let (strukt, field, base) = field_of(typeck, peel(e))?;
                let &(length, slack, element) = self.keyed.get(&(strukt, field))?;
                // (5) the value's pointee is the field's size.
                if pointee_size(typeck.expr_ty(e)) != Some(element) {
                    return None;
                }
                let root = root_of(base)?;
                Some((text(base), length, slack, root, (strukt, field)))
            };
        let render =
            |base: &str, length: Symbol, slack: u128| format!("{base}.{length} as usize + {slack}");
        let may_write = |key: (DefId, Symbol)| {
            self.may_write
                .get(&key)
                .is_some_and(|w| w.contains(&caller))
        };
        let body = tcx.hir_body_owned_by(caller);
        /// Whether `root` is reassigned or borrowed mutably in the body.
        fn written_root(body: &rustc_hir::Body<'_>, root: HirId) -> bool {
            struct Root {
                root: HirId,
                written: bool,
            }
            impl<'tcx> Visitor<'tcx> for Root {
                fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                    match e.kind {
                        ExprKind::Assign(lhs, ..) | ExprKind::AssignOp(_, lhs, _)
                            if local_of(lhs) == Some(self.root) =>
                        {
                            self.written = true
                        }
                        ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, place)
                            if local_of(place) == Some(self.root) =>
                        {
                            self.written = true
                        }
                        _ => {}
                    }
                    intravisit::walk_expr(self, e);
                }
            }
            let mut visitor = Root {
                root,
                written: false,
            };
            visitor.visit_body(body);
            visitor.written
        }
        // A direct read, where the calling function cannot reallocate the
        // field (inside an allocator, between the pointer's write and the
        // length's, the pair is inconsistent).
        if let Some((base, length, slack, root, key)) = licensed(arg) {
            return (!may_write(key) && !written_root(body, root))
                .then(|| render(&base, length, slack));
        }
        let local = local_of(arg)?;
        struct Defs<'tcx> {
            local: HirId,
            let_init: Option<&'tcx Expr<'tcx>>,
            assignments: Vec<&'tcx Expr<'tcx>>,
            unknown: bool,
        }
        impl<'tcx> Visitor<'tcx> for Defs<'tcx> {
            fn visit_local(&mut self, let_: &'tcx LetStmt<'tcx>) {
                if let PatKind::Binding(mode, id, ..) = let_.pat.kind
                    && id == self.local
                {
                    if matches!(mode.0, rustc_hir::ByRef::Yes(_)) {
                        self.unknown = true;
                    }
                    self.let_init = let_.init;
                }
                intravisit::walk_local(self, let_);
            }

            fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                match e.kind {
                    ExprKind::Assign(lhs, _, _) if local_of(lhs) == Some(self.local) => {
                        self.assignments.push(e)
                    }
                    ExprKind::AssignOp(_, lhs, _) if local_of(lhs) == Some(self.local) => {
                        self.unknown = true
                    }
                    ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, place)
                        if local_of(place) == Some(self.local) =>
                    {
                        self.unknown = true
                    }
                    ExprKind::Closure(..) => self.unknown = true,
                    _ => {}
                }
                intravisit::walk_expr(self, e);
            }
        }
        let mut defs = Defs {
            local,
            let_init: None,
            assignments: Vec::new(),
            unknown: false,
        };
        defs.visit_body(body);
        if defs.unknown {
            return None;
        }
        let value_of = |assign: &'tcx Expr<'tcx>| match assign.kind {
            ExprKind::Assign(_, rhs, _) => rhs,
            _ => assign,
        };
        let (found, key) = match (defs.let_init, defs.assignments.as_slice()) {
            // `let p = field;`
            (Some(init), []) => {
                let (base, length, slack, root, key) = licensed(init)?;
                ((base, length, slack, root), key)
            }
            // (8) `let p = null; ..; p = field;` with the assignment
            // straight-line before the call in an enclosing block.
            (Some(init), [assign]) if is_null(init) => {
                let (base, length, slack, root, key) = licensed(value_of(assign))?;
                let (block, _) = statement_of(tcx, assign.hir_id)?;
                if !(assign.span.lo() < arg.span.lo()
                    && tcx.hir_parent_iter(arg.hir_id).any(|(id, _)| id == block))
                {
                    return None;
                }
                ((base, length, slack, root), key)
            }
            _ => return None,
        };
        let (base, length, slack, root) = found;
        // (5) the argument's own pointee is the field's size.
        if pointee_size(typeck.expr_ty(arg)) != self.keyed.get(&key).map(|&(.., element)| element) {
            return None;
        }
        if may_write(key) || written_root(body, root) {
            return None;
        }
        Some(render(&base, length, slack))
    }
}
