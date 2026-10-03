//! **R763-2 (wave-4 build 2) — a pointer field whose element count is a
//! sibling field of the same struct** (`len-field-count`).
//!
//! genann's `(*ann).weight` and ht's `(*table).entries` are fields the §77
//! fallback sized: nothing at the construction states a length, and the
//! sibling that does (`total_weights`, `capacity`) carries no name the
//! sibling-size arm recognises. This module proves the pairing from the
//! program itself: **every write of `F` anywhere in the crate is established
//! by its own block** in one of two forms, and every write of the count field
//! `C` belongs to such a block:
//!   (E1) allocation — `F = calloc(n, size_of::<T>())` / `malloc(n *
//!        size_of::<T>())` (directly, or through a local defined once by that
//!        call), `T` being `F`'s pointee, and `n` the value of `C`: a read of
//!        the same object's `C`, or the same once-defined local written to it;
//!   (E2) offset witness — after the `F` write, the same block computes
//!        `B.F.offset(B.C)` (or `.add`): on a UB-free input (§28) that offset
//!        lies in `F`'s allocation or one past it, so the allocation holds at
//!        least `C` elements from `F`.
//! Whole-struct copies (`memcpy` / `memmove` / `*a = *b`) copy both fields of
//! an object that already satisfies the pairing, and a zeroing (`memset`,
//! `zeroed`) leaves a null `F` beside a zero `C`; neither is a field write
//! here. Taking `&mut` of either field, a compound assignment, a struct
//! literal that sets `F` to anything but null, or any write the two forms do
//! not cover refuses the pair.
//!
//! The length at a construction over `B.F` is then `((B).C) as usize`, read at
//! the construction, `must` on every path — unless the constructing function
//! itself writes `F` or `C` (an establishing sequence may be in flight), which
//! refuses.

use rustc_hir::{
    BinOpKind, Block, Expr, ExprKind, HirId, LetStmt, PatKind, QPath, UnOp,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind};
use rustc_span::Symbol;

/// The proven count field of `F` and the form that established it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FieldCount {
    pub(crate) count: Symbol,
    pub(crate) form: &'static str,
}

impl FieldCount {
    pub(crate) fn receipt(&self, field: Symbol) -> String {
        format!("len-field-count:must:{field}={}:{}", self.count, self.form)
    }
}

fn peel<'a, 'tcx>(mut e: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    loop {
        match e.kind {
            ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) => e = inner,
            _ => return e,
        }
    }
}

fn local_of(e: &Expr<'_>) -> Option<HirId> {
    match peel(e).kind {
        ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

/// The struct behind a field access's base (through `&`, `*const`, `*mut`).
fn struct_of<'tcx>(mut ty: Ty<'tcx>) -> Option<AdtDef<'tcx>> {
    loop {
        match ty.kind() {
            TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => ty = *inner,
            TyKind::Adt(def, _) if def.is_struct() => return Some(*def),
            _ => return None,
        }
    }
}

/// One field place: the struct, the field, the base's source text.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Place {
    adt: rustc_hir::def_id::DefId,
    field: Symbol,
    base: String,
}

struct Ctx<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
}

impl<'tcx> Ctx<'tcx> {
    fn text(&self, e: &Expr<'_>) -> Option<String> {
        self.tcx
            .sess
            .source_map()
            .span_to_snippet(e.span)
            .ok()
            .map(|t| t.split_whitespace().collect::<Vec<_>>().join(" "))
    }

    fn place(&self, e: &Expr<'tcx>) -> Option<Place> {
        let ExprKind::Field(base, ident) = peel(e).kind else { return None };
        let adt = struct_of(self.tcx.typeck(self.owner).expr_ty(base))?;
        Some(Place {
            adt: adt.did(),
            field: ident.name,
            base: self.text(base)?,
        })
    }
}

/// Every write of a field of `adt` in one body, in block order, with the
/// block it is a statement of.
#[derive(Default)]
struct Writes<'tcx> {
    /// (block, statement index, place, right-hand side)
    writes: Vec<(HirId, usize, Place, Option<&'tcx Expr<'tcx>>)>,
    /// fields of `adt` written in a form the two shapes cannot cover
    poisoned: Vec<Symbol>,
}

struct Scan<'a, 'tcx> {
    cx: &'a Ctx<'tcx>,
    adt: rustc_hir::def_id::DefId,
    /// `let ref mut fresh = (*s).f;` bindings, C2Rust's spelling of a field write
    fresh: Vec<(HirId, Place)>,
    out: Writes<'tcx>,
    block: Option<(HirId, usize)>,
}

impl<'tcx> Scan<'_, 'tcx> {
    fn target(&self, lhs: &'tcx Expr<'tcx>) -> Option<Place> {
        if let Some(place) = self.cx.place(lhs) {
            return (place.adt == self.adt).then_some(place);
        }
        // `*fresh = rhs` through a `let ref mut fresh = (*s).f`
        if let ExprKind::Unary(UnOp::Deref, inner) = peel(lhs).kind {
            let id = local_of(inner)?;
            return self
                .fresh
                .iter()
                .find(|(b, _)| *b == id)
                .map(|(_, p)| p.clone());
        }
        None
    }
}

impl<'tcx> Visitor<'tcx> for Scan<'_, 'tcx> {
    fn visit_block(&mut self, b: &'tcx Block<'tcx>) {
        let saved = self.block;
        for (i, s) in b.stmts.iter().enumerate() {
            self.block = Some((b.hir_id, i));
            self.visit_stmt(s);
        }
        if let Some(e) = b.expr {
            self.block = Some((b.hir_id, b.stmts.len()));
            self.visit_expr(e);
        }
        self.block = saved;
    }

    fn visit_local(&mut self, l: &'tcx LetStmt<'tcx>) {
        if let (PatKind::Binding(mode, id, _, _), Some(init)) = (l.pat.kind, l.init)
            && mode.0 == rustc_hir::ByRef::Yes(rustc_hir::Mutability::Mut)
            && let Some(place) = self.cx.place(init)
            && place.adt == self.adt
        {
            self.fresh.push((id, place));
            return;
        }
        intravisit::walk_local(self, l);
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        match e.kind {
            ExprKind::Assign(lhs, rhs, _) => {
                if let Some(place) = self.target(lhs) {
                    if let Some((block, i)) = self.block {
                        self.out.writes.push((block, i, place, Some(rhs)));
                    }
                    self.visit_expr(rhs);
                    return;
                }
            }
            ExprKind::AssignOp(_, lhs, _) => {
                if let Some(place) = self.target(lhs) {
                    self.out.poisoned.push(place.field);
                }
            }
            ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, inner) => {
                if let Some(place) = self.cx.place(inner)
                    && place.adt == self.adt
                {
                    self.out.poisoned.push(place.field);
                }
            }
            ExprKind::Struct(_, fields, _) => {
                if struct_of(self.cx.tcx.typeck(self.cx.owner).expr_ty(e))
                    .is_some_and(|d| d.did() == self.adt)
                {
                    for f in fields.iter() {
                        // Only a zero count beside a null pointer keeps the pair.
                        let zero = self.cx.text(f.expr).is_some_and(|t| {
                            t == "0" || t.starts_with("0 as ") || t.contains("null") || t == "None"
                        });
                        if !zero {
                            self.out.poisoned.push(f.ident.name);
                        }
                    }
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }
}

/// `calloc(n, size_of::<T>())` / `malloc(n * size_of::<T>())` (any operand
/// order, `wrapping_mul` too): the count `n`, when the element is `pointee`.
fn allocation_count<'tcx>(
    cx: &Ctx<'tcx>,
    e: &'tcx Expr<'tcx>,
    pointee: &str,
) -> Option<&'tcx Expr<'tcx>> {
    let ExprKind::Call(callee, args) = peel(e).kind else { return None };
    let name = cx.text(callee)?;
    let name = name.rsplit("::").next()?.to_owned();
    let sized = |e: &Expr<'_>| {
        cx.text(e).is_some_and(|t| {
            let t = t.replace(' ', "");
            t.contains(&format!("size_of::<{}>()", pointee.replace(' ', "")))
        })
    };
    match (name.as_str(), args) {
        ("calloc", [n, size]) if sized(size) => Some(n),
        ("malloc", [size]) => {
            let size = peel(size);
            match size.kind {
                ExprKind::Binary(op, l, r) if op.node == BinOpKind::Mul => {
                    if sized(l) {
                        Some(r)
                    } else if sized(r) {
                        Some(l)
                    } else {
                        None
                    }
                }
                ExprKind::MethodCall(seg, recv, [arg], _)
                    if seg.ident.name.as_str() == "wrapping_mul" =>
                {
                    if sized(recv) {
                        Some(arg)
                    } else if sized(arg) {
                        Some(recv)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The once-defined local's initializer, when the local is never reassigned.
fn single_definition<'tcx>(
    cx: &Ctx<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
    local: HirId,
) -> Option<&'tcx Expr<'tcx>> {
    struct Defs<'tcx> {
        local: HirId,
        init: Option<&'tcx Expr<'tcx>>,
        writes: usize,
    }
    impl<'tcx> Visitor<'tcx> for Defs<'tcx> {
        fn visit_local(&mut self, l: &'tcx LetStmt<'tcx>) {
            if let PatKind::Binding(_, id, _, _) = l.pat.kind
                && id == self.local
            {
                self.init = l.init;
            }
            intravisit::walk_local(self, l);
        }

        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            match e.kind {
                ExprKind::Assign(lhs, ..) | ExprKind::AssignOp(_, lhs, _)
                    if local_of(lhs) == Some(self.local) =>
                {
                    self.writes += 1
                }
                ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, inner)
                    if local_of(inner) == Some(self.local) =>
                {
                    self.writes += 1
                }
                _ => {}
            }
            intravisit::walk_expr(self, e);
        }
    }
    let _ = cx;
    let mut d = Defs {
        local,
        init: None,
        writes: 0,
    };
    d.visit_expr(body.value);
    (d.writes == 0).then_some(d.init).flatten()
}

/// Does the block, after statement `from`, compute `B.F.offset(B.C)` /
/// `.add(B.C)`? Returns `C`.
fn offset_witness<'tcx>(
    cx: &Ctx<'tcx>,
    block: &'tcx Block<'tcx>,
    from: usize,
    f: &Place,
) -> Option<Symbol> {
    struct Find<'a, 'tcx> {
        cx: &'a Ctx<'tcx>,
        f: &'a Place,
        found: Option<Symbol>,
    }
    impl<'tcx> Visitor<'tcx> for Find<'_, 'tcx> {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if let ExprKind::MethodCall(seg, recv, [arg], _) = e.kind
                && matches!(seg.ident.name.as_str(), "offset" | "add")
                && self.cx.place(recv).as_ref() == Some(self.f)
                && let Some(count) = self.cx.place(arg)
                && count.adt == self.f.adt
                && count.base == self.f.base
            {
                self.found = Some(count.field);
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut find = Find { cx, f, found: None };
    for s in block.stmts.iter().skip(from + 1) {
        find.visit_stmt(s);
        if find.found.is_some() {
            return find.found;
        }
    }
    if let Some(e) = block.expr {
        find.visit_expr(e);
    }
    find.found
}

fn block_of<'tcx>(tcx: TyCtxt<'tcx>, id: HirId) -> Option<&'tcx Block<'tcx>> {
    match tcx.hir_node(id) {
        rustc_hir::Node::Block(b) => Some(b),
        _ => None,
    }
}

/// **The proof.** The count field of `adt.field`, or `None`.
pub(crate) fn proven_count(
    tcx: TyCtxt<'_>,
    adt: rustc_hir::def_id::DefId,
    field: Symbol,
) -> Option<FieldCount> {
    let def = tcx.adt_def(adt);
    if !def.is_struct() {
        return None;
    }
    let variant = def.non_enum_variant();
    let f = variant.fields.iter().find(|x| x.name == field)?;
    let fty = tcx.type_of(f.did).instantiate_identity();
    let TyKind::RawPtr(pointee, _) = fty.kind() else { return None };
    let pointee = pointee.to_string();
    let is_count = |name: Symbol| {
        variant
            .fields
            .iter()
            .any(|x| x.name == name && tcx.type_of(x.did).instantiate_identity().is_integral())
    };

    let mut paired: Option<FieldCount> = None;
    // (block, count field) pairs whose count writes are covered
    let mut covered: Vec<(LocalDefId, HirId, Symbol)> = Vec::new();
    let mut count_writes: Vec<(LocalDefId, HirId, usize, Symbol)> = Vec::new();

    for owner in tcx.hir_body_owners() {
        if !matches!(
            tcx.def_kind(owner),
            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
        ) {
            continue;
        }
        let Some(body) = tcx.hir_maybe_body_owned_by(owner) else { continue };
        let cx = Ctx { tcx, owner };
        let mut scan = Scan {
            cx: &cx,
            adt,
            fresh: Vec::new(),
            out: Writes::default(),
            block: None,
        };
        scan.visit_expr(body.value);
        if scan.out.poisoned.contains(&field) {
            return None;
        }
        for (block, i, place, rhs) in &scan.out.writes {
            if place.field == field {
                let rhs = (*rhs)?;
                let block_ref = block_of(tcx, *block)?;
                // (E1) the allocation, directly or through a once-defined local
                let allocation = allocation_count(&cx, rhs, &pointee).or_else(|| {
                    local_of(rhs)
                        .and_then(|l| single_definition(&cx, body, l))
                        .and_then(|init| allocation_count(&cx, init, &pointee))
                });
                let established = if let Some(n) = allocation {
                    if let Some(count) = cx
                        .place(n)
                        .filter(|c| c.adt == adt && c.base == place.base && is_count(c.field))
                    {
                        // n reads the same object's count
                        Some(FieldCount {
                            count: count.field,
                            form: "alloc",
                        })
                    } else if let Some(v) = local_of(n) {
                        // n is a local written to the count in the same block
                        scan.out
                            .writes
                            .iter()
                            .find(|(b, _, p, r)| {
                                b == block
                                    && p.base == place.base
                                    && is_count(p.field)
                                    && r.and_then(local_of) == Some(v)
                            })
                            .filter(|_| single_definition(&cx, body, v).is_some())
                            .map(|(_, _, p, _)| FieldCount {
                                count: p.field,
                                form: "alloc",
                            })
                    } else {
                        None
                    }
                } else {
                    // (E2) the offset witness
                    offset_witness(&cx, block_ref, *i, place)
                        .filter(|c| is_count(*c))
                        .map(|c| FieldCount {
                            count: c,
                            form: "offset",
                        })
                };
                let established = established?;
                match &paired {
                    Some(p) if p.count != established.count => return None,
                    _ => {}
                }
                covered.push((owner, *block, established.count));
                if paired.as_ref().map(|p| p.form) != Some("alloc") {
                    paired = Some(established);
                }
            } else {
                count_writes.push((owner, *block, *i, place.field));
            }
        }
        if let Some(p) = &paired
            && scan.out.poisoned.contains(&p.count)
        {
            return None;
        }
    }
    let paired = paired?;
    // Every write of the count field sits in a block that establishes F.
    if count_writes
        .iter()
        .filter(|(_, _, _, c)| *c == paired.count)
        .any(|(o, b, _, c)| {
            !covered
                .iter()
                .any(|(o2, b2, c2)| o2 == o && b2 == b && c2 == c)
        })
    {
        return None;
    }
    Some(paired)
}

/// Does `owner` write `adt.field` or `adt.count` itself (an establishing
/// sequence may be in flight at a construction there)?
pub(crate) fn writes_either(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    adt: rustc_hir::def_id::DefId,
    field: Symbol,
    count: Symbol,
) -> bool {
    let Some(body) = tcx.hir_maybe_body_owned_by(owner) else { return true };
    let cx = Ctx { tcx, owner };
    let mut scan = Scan {
        cx: &cx,
        adt,
        fresh: Vec::new(),
        out: Writes::default(),
        block: None,
    };
    scan.visit_expr(body.value);
    scan.out
        .writes
        .iter()
        .any(|(_, _, p, _)| p.field == field || p.field == count)
        || scan.out.poisoned.iter().any(|f| *f == field || *f == count)
}

/// **The construction side.** For a base expression `B.F` in `owner`: the
/// length text `((B).C) as usize` and the receipt, when the pair is proven.
pub(crate) fn length_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    base: &'tcx Expr<'tcx>,
    count_only: bool,
) -> Option<(String, String)> {
    let cx = Ctx { tcx, owner };
    let place = cx.place(base)?;
    // The base object is read twice; it must be free of effects.
    if place.base.contains('(') && !place.base.starts_with("(*") || place.base.contains('{') {
        return None;
    }
    let proven = proven_count(tcx, place.adt, place.field)?;
    if writes_either(tcx, owner, place.adt, place.field, proven.count) {
        return None;
    }
    let count = format!("{}.{}", place.base, proven.count);
    Some((
        if count_only {
            count
        } else {
            format!("({count}) as usize")
        },
        proven.receipt(place.field),
    ))
}

/// The seam's side: the argument at `span` in `owner`'s body (casts peeled),
/// its count text (the glue casts it) and the receipt.
pub(crate) fn length_at_span(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    span: rustc_span::Span,
) -> Option<(String, String)> {
    struct At<'tcx> {
        span: rustc_span::Span,
        found: Option<&'tcx Expr<'tcx>>,
    }
    impl<'tcx> Visitor<'tcx> for At<'tcx> {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if self.found.is_none() && e.span == self.span {
                self.found = Some(e);
                return;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let body = tcx.hir_maybe_body_owned_by(owner)?;
    let mut at = At { span, found: None };
    at.visit_expr(body.value);
    length_at(tcx, owner, peel(at.found?), true)
}
