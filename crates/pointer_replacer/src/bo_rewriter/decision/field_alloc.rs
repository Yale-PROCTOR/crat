//! **wave-6l relay 071 (R697-7): the field-carried allocation length.**
//!
//! A struct's pointer field `P` whose every non-null write is an allocation
//! plus a literal offset, made in a function that also writes an integer field
//! `C` of the same object so that the allocation's elements past the offset
//! are `C + k`, holds `C + k` elements wherever it is read (brotli's
//! `RingBufferInitBuffer`: `data_ = alloc(2 + buflen + 7)`, `cur_size_ =
//! buflen`, `buffer_ = data_ + 2`, so `buffer_` holds `cur_size_ + 7`). The
//! seam renders that length where a construction's argument is `P` read from
//! an object (receipted `len-field-alloc`), before the fallback.
//!
//! **What refuses a licence:** any write to `P` that is neither null nor such
//! an allocation; a write to `C` in a function that does not write `P` (a
//! stray length); a compound write or an escaped `&mut` of either field; a
//! struct literal with a non-null `P`; an offset past the allocation (a
//! negative `k`).
//!
//! **What refuses a use:** the calling function may write `P` or `C`
//! (directly or through a call), so the field may be reallocated between the
//! read and the construction; or the argument is a local not defined only from
//! `P` of one object (or null), the object's root is reassigned, or the local
//! is borrowed mutably.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, LetStmt, Node, PatKind,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};
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
    keyed: FxHashMap<(DefId, Symbol), (Symbol, u128)>,
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
    /// `None`: a write whose value is unknown (compound, escaped address).
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

/// The writes of one body, the statics it assigns, and the local functions it
/// calls.
struct Collect<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    function: LocalDefId,
    typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
    writes: &'a mut Vec<Write<'tcx>>,
    ref_mut: FxHashMap<HirId, (DefId, Symbol, String)>,
    statics_written: &'a mut FxHashSet<DefId>,
    calls: &'a mut FxHashMap<LocalDefId, FxHashSet<LocalDefId>>,
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

    fn push(&mut self, place: &'tcx Expr<'tcx>, node: HirId, value: Option<&'tcx Expr<'tcx>>) {
        if let Some((strukt, field, base)) = field_of(self.typeck, place) {
            let base = self.text(base);
            self.writes.push(Write {
                function: self.function,
                strukt,
                field,
                base,
                value,
                lo: place.span.lo(),
                node,
            });
        } else if let ExprKind::Unary(rustc_hir::UnOp::Deref, inner) = place.kind
            && let Some(binding) = local_of(inner)
            && let Some((strukt, field, base)) = self.ref_mut.get(&binding).cloned()
        {
            self.writes.push(Write {
                function: self.function,
                strukt,
                field,
                base,
                value,
                lo: place.span.lo(),
                node,
            });
        } else if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = peel(place).kind
            && let Res::Def(DefKind::Static { .. }, did) = path.res
        {
            self.statics_written.insert(did);
        }
    }
}

impl<'tcx> Visitor<'tcx> for Collect<'_, 'tcx> {
    fn visit_local(&mut self, let_: &'tcx LetStmt<'tcx>) {
        if let PatKind::Binding(mode, id, ..) = let_.pat.kind
            && matches!(mode.0, rustc_hir::ByRef::Yes(rustc_hir::Mutability::Mut))
            && let Some(init) = let_.init
            && let Some((strukt, field, base)) = field_of(self.typeck, init)
        {
            let base = self.text(base);
            self.ref_mut.insert(id, (strukt, field, base));
        }
        intravisit::walk_local(self, let_);
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        match e.kind {
            ExprKind::Assign(lhs, rhs, _) => self.push(lhs, e.hir_id, Some(rhs)),
            ExprKind::AssignOp(_, lhs, _) => self.push(lhs, e.hir_id, None),
            ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, place) => {
                self.push(place, e.hir_id, None)
            }
            ExprKind::Struct(_, fields, _) => {
                if let TyKind::Adt(adt, _) = self.typeck.expr_ty(e).kind()
                    && adt.is_struct()
                {
                    for field in fields.iter() {
                        self.writes.push(Write {
                            function: self.function,
                            strukt: adt.did(),
                            field: field.ident.name,
                            base: format!("<literal@{:?}>", e.span.lo()),
                            value: Some(field.expr),
                            lo: field.span.lo(),
                            node: e.hir_id,
                        });
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
                        self.writes.push(Write {
                            function: self.function,
                            strukt,
                            field,
                            base,
                            value: None,
                            lo: e.span.lo(),
                            node: e.hir_id,
                        });
                    }
                }
            }
            ExprKind::Call(callee, _) => {
                if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = callee.kind
                    && let Res::Def(DefKind::Fn, did) = path.res
                    && let Some(local) = did.as_local()
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
}

impl<'tcx> Program<'tcx> {
    fn linear(&self, e: &'tcx Expr<'tcx>) -> Option<Linear> {
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
                Res::Local(id) => Some(Linear {
                    constant: 0,
                    atoms: vec![(format!("{id:?}"), 1)],
                }),
                // A static never assigned is its initializer.
                Res::Def(DefKind::Static { .. }, did) if !self.statics_written.contains(&did) => {
                    let local = did.as_local()?;
                    let body = self.tcx.hir_body_owned_by(local);
                    self.linear(body.value)
                }
                _ => None,
            },
            ExprKind::Binary(op, left, right) => {
                let sign = match op.node {
                    rustc_hir::BinOpKind::Add => 1,
                    rustc_hir::BinOpKind::Sub => -1,
                    _ => return None,
                };
                Some(self.linear(left)?.add(self.linear(right)?, sign))
            }
            ExprKind::MethodCall(segment, receiver, [argument], _) => {
                let sign = match segment.ident.as_str() {
                    "wrapping_add" => 1,
                    "wrapping_sub" => -1,
                    _ => return None,
                };
                Some(self.linear(receiver)?.add(self.linear(argument)?, sign))
            }
            _ => None,
        }
    }

    /// `n * size_of::<T>()` (or `n` alone for a one-byte `T`): the element count.
    fn elements(&self, bytes: &'tcx Expr<'tcx>, element: u64) -> Option<&'tcx Expr<'tcx>> {
        let bytes = peel(bytes);
        let size_of = |e: &Expr<'_>| {
            matches!(peel(e).kind, ExprKind::Call(callee, [])
                if matches!(callee.kind, ExprKind::Path(rustc_hir::QPath::Resolved(_, path))
                    if path.segments.last().is_some_and(|s| s.ident.as_str() == "size_of")))
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
        before: BytePos,
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
                    self.allocation(function, then, base, before, depth + 1)
                } else if is_null(then) {
                    self.allocation(function, otherwise, base, before, depth + 1)
                } else {
                    None
                }
            }
            ExprKind::Path(..) => {
                // A local defined once, at its `let`.
                let id = local_of(e)?;
                let Node::Pat(pat) = self.tcx.hir_node(id) else {
                    return None;
                };
                let Node::LetStmt(let_) = self.tcx.parent_hir_node(pat.hir_id) else {
                    return None;
                };
                self.allocation(function, let_.init?, base, before, depth + 1)
            }
            ExprKind::Field(..) => {
                // The same object's field, by its last write before here in
                // this function.
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
                let last = self
                    .writes
                    .iter()
                    .filter(|w| {
                        w.function == function
                            && w.strukt == strukt
                            && w.field == field
                            && w.base == base
                            && w.lo < before
                    })
                    .max_by_key(|w| w.lo)?;
                self.allocation(function, last.value?, base, last.lo, depth + 1)
            }
            _ => None,
        }
    }

    /// One write's enclosing block is an ancestor of the other's node.
    fn encloses(&self, outer: HirId, inner: HirId) -> bool {
        let Some(block) = self
            .tcx
            .hir_parent_iter(outer)
            .find(|(_, node)| matches!(node, Node::Block(_)))
            .map(|(id, _)| id)
        else {
            return false;
        };
        self.tcx.hir_parent_iter(inner).any(|(id, _)| id == block)
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
                (receiver, self.linear(argument)?)
            }
            _ => (value, Linear::default()),
        };
        if !offset.atoms.is_empty() || offset.constant < 0 {
            return None;
        }
        let bytes = self.allocation(pointer.function, source, &pointer.base, pointer.lo, 0)?;
        let elements = self.linear(self.elements(bytes, element)?)?;
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
        if !self.encloses(length.node, pointer.node) && !self.encloses(pointer.node, length.node) {
            return None;
        }
        let length = self.linear(length.value?)?;
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
        for owner in tcx.hir_body_owners() {
            if !matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn) {
                continue;
            }
            let mut collect = Collect {
                tcx,
                function: owner,
                typeck: tcx.typeck(owner),
                writes: &mut writes,
                ref_mut: FxHashMap::default(),
                statics_written: &mut statics_written,
                calls: &mut calls,
            };
            collect.visit_body(tcx.hir_body_owned_by(owner));
        }
        let program = Program {
            tcx,
            writes,
            statics_written,
        };
        let mut licences = Licences::default();
        let mut pointers: Vec<(DefId, Symbol)> =
            program.writes.iter().map(|w| (w.strukt, w.field)).collect();
        pointers.sort_by_key(|(d, f)| (tcx.def_path_str(*d), f.to_string()));
        pointers.dedup();
        for (strukt, pointer) in pointers {
            let adt = tcx.adt_def(strukt);
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
            for length_def in fields.iter().filter(|f| {
                matches!(
                    tcx.type_of(f.did).skip_binder().kind(),
                    TyKind::Uint(_) | TyKind::Int(_)
                )
            }) {
                let length = length_def.name;
                let length_writes: Vec<_> = program
                    .writes
                    .iter()
                    .filter(|w| w.strukt == strukt && w.field == length)
                    .collect();
                // A stray or unknown length write refuses it.
                if length_writes.iter().any(|l| {
                    l.value.is_none()
                        || !pointer_writes
                            .iter()
                            .any(|p| p.function == l.function && p.base == l.base)
                }) {
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
                if ok && let Some(k) = slack {
                    licences.licences.push(Licence {
                        strukt: tcx.item_name(strukt).to_string(),
                        pointer: pointer.to_string(),
                        length: length.to_string(),
                        slack: k,
                    });
                    licences.keyed.insert((strukt, pointer), (length, k));
                }
            }
        }
        // Per licence, the functions that write its pointer or its length, and
        // their callers.
        let mut may_write = FxHashMap::default();
        for (&(strukt, pointer), &(length, _)) in &licences.keyed {
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
    /// from one object's licensed field (or null), whose object root is not
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
        let licensed = |e: &'tcx Expr<'tcx>| -> Option<(String, Symbol, u128, &'tcx Expr<'tcx>, (DefId, Symbol))> {
            let (strukt, field, base) = field_of(typeck, peel(e))?;
            let (length, slack) = self.keyed.get(&(strukt, field))?;
            Some((text(base), *length, *slack, base, (strukt, field)))
        };
        let render =
            |base: &str, length: Symbol, slack: u128| format!("{base}.{length} as usize + {slack}");
        let may_write = |key: (DefId, Symbol)| {
            self.may_write
                .get(&key)
                .is_some_and(|w| w.contains(&caller))
        };
        // A direct read, where the calling function cannot reallocate the
        // field (inside an allocator, between the pointer's write and the
        // length's, the pair is inconsistent).
        if let Some((base, length, slack, _, key)) = licensed(arg) {
            return (!may_write(key)).then(|| render(&base, length, slack));
        }
        let local = local_of(arg)?;
        struct Defs<'tcx> {
            local: HirId,
            root: Option<HirId>,
            values: Vec<&'tcx Expr<'tcx>>,
            unknown: bool,
            root_written: bool,
        }
        impl<'tcx> Visitor<'tcx> for Defs<'tcx> {
            fn visit_local(&mut self, let_: &'tcx LetStmt<'tcx>) {
                if let PatKind::Binding(mode, id, ..) = let_.pat.kind
                    && id == self.local
                {
                    if matches!(mode.0, rustc_hir::ByRef::Yes(_)) {
                        self.unknown = true;
                    }
                    if let Some(init) = let_.init {
                        self.values.push(init);
                    }
                }
                intravisit::walk_local(self, let_);
            }

            fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                match e.kind {
                    ExprKind::Assign(lhs, rhs, _) => {
                        if local_of(lhs) == Some(self.local) {
                            self.values.push(rhs);
                        }
                        if self.root.is_some() && local_of(lhs) == self.root {
                            self.root_written = true;
                        }
                    }
                    ExprKind::AssignOp(_, lhs, _) => {
                        if local_of(lhs) == Some(self.local) {
                            self.unknown = true;
                        }
                        if self.root.is_some() && local_of(lhs) == self.root {
                            self.root_written = true;
                        }
                    }
                    ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, place) => {
                        if local_of(place) == Some(self.local) {
                            self.unknown = true;
                        }
                        if self.root.is_some() && local_of(place) == self.root {
                            self.root_written = true;
                        }
                    }
                    ExprKind::Closure(..) => self.unknown = true,
                    _ => {}
                }
                intravisit::walk_expr(self, e);
            }
        }
        let body = tcx.hir_body_owned_by(caller);
        let mut defs = Defs {
            local,
            root: None,
            values: Vec::new(),
            unknown: false,
            root_written: false,
        };
        defs.visit_body(body);
        if defs.unknown {
            return None;
        }
        let mut found: Option<(String, Symbol, u128, &'tcx Expr<'tcx>, (DefId, Symbol))> = None;
        for value in &defs.values {
            if is_null(value) {
                continue;
            }
            let this = licensed(value)?;
            match &found {
                Some((base, ..)) if *base != this.0 => return None,
                _ => found = Some(this),
            }
        }
        let (base, length, slack, base_expr, key) = found?;
        // The calling function may not reallocate this field.
        if may_write(key) {
            return None;
        }
        // The object's root binding is not reassigned in this function.
        let mut root = base_expr;
        loop {
            match root.kind {
                ExprKind::Field(inner, _)
                | ExprKind::Unary(rustc_hir::UnOp::Deref, inner)
                | ExprKind::DropTemps(inner)
                | ExprKind::Cast(inner, _) => root = inner,
                _ => break,
            }
        }
        let mut roots = Defs {
            local: HirId::INVALID,
            root: Some(local_of(root)?),
            values: Vec::new(),
            unknown: false,
            root_written: false,
        };
        roots.visit_body(body);
        if roots.root_written {
            return None;
        }
        Some(render(&base, length, slack))
    }
}
