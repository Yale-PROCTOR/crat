//! **P11 (R936-1, the USER with the advisor, 10-09) — aliasing through a global
//! variable or an integer is outside the claim.** A pointer whose provenance
//! passes through a global (a pointer value stored in or read from a `static`,
//! or a pointer to a `static`'s storage) or through an integer (an
//! integer-to-pointer cast, a round trip included) is assumed not to designate
//! an object that another pointer argument of the same call also designates.
//! The pair certificates take the premise as their LAST arm, after every
//! structural certificate has failed, so every pair that rests on it carries
//! its own receipt (`pair-disjoint:premise=global-or-integer-provenance:<kind>`)
//! and is counted (`<p>.raw-boundary-pair-premise.tsv`).
//!
//! [`provenance`] answers from the text, on every path it shows: casts and
//! pointer arithmetic, a local through ALL of its definitions (none of them its
//! entry value, its address never taken), every branch of a conditional, the
//! returned values of a local getter, a pointer value read out of a static's
//! storage (directly, or through a pointer to that storage), the address of a
//! place in a static's storage. A pointer loaded from an object a global's
//! VALUE or an integer designates is NOT (it was never in a static: 149f's
//! core stays in scope). Anything else is no premise, so the pair stays with
//! the rules that hold it (the conservative side).

use rustc_hir::{
    Expr, ExprKind, HirId, PatKind, QPath, UnOp,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TypeckResults};

/// What the premise rests on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Provenance {
    /// A pointer value stored in, or read out of, a `static`.
    GlobalValue(DefId),
    /// A pointer to a `static`'s own storage.
    GlobalStorage(DefId),
    /// A pointer made from a (non-literal) integer.
    Integer,
}

/// The receipt's root kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ProvenanceKind {
    GlobalValue,
    GlobalStorage,
    Integer,
}

impl Provenance {
    pub(crate) fn kind(self) -> ProvenanceKind {
        match self {
            Self::GlobalValue(_) => ProvenanceKind::GlobalValue,
            Self::GlobalStorage(_) => ProvenanceKind::GlobalStorage,
            Self::Integer => ProvenanceKind::Integer,
        }
    }
}

impl ProvenanceKind {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::GlobalValue => "global-value",
            Self::GlobalStorage => "global-storage",
            Self::Integer => "integer",
        }
    }
}

/// The premise for a pair, if one side's provenance passes through a global or
/// an integer. Never for one global at both positions (its value or its
/// storage: `st.pos` may point into `st.buf`), nor for two integers:
/// the premise is about ANOTHER argument's object, and those may visibly be
/// the same.
pub(crate) fn premise(
    left: Option<Provenance>,
    right: Option<Provenance>,
) -> Option<ProvenanceKind> {
    match (left, right) {
        (Some(a), Some(b)) => {
            let same = match (a, b) {
                (Provenance::Integer, Provenance::Integer) => true,
                (
                    Provenance::GlobalValue(x) | Provenance::GlobalStorage(x),
                    Provenance::GlobalValue(y) | Provenance::GlobalStorage(y),
                ) => x == y,
                _ => false,
            };
            (!same).then_some(a.kind())
        }
        (Some(a), None) | (None, Some(a)) => Some(a.kind()),
        (None, None) => None,
    }
}

/// The provenance of pointer argument `expr` of a call in `caller`, when it
/// passes through a global or an integer on every path the text shows.
pub(crate) fn provenance<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    expr: &'tcx Expr<'tcx>,
) -> Option<Provenance> {
    let mut walk = Walk {
        tcx,
        stack: Vec::new(),
        depth: 0,
    };
    match walk.value(caller, tcx.typeck(caller), expr) {
        Tri::Yes(provenance) => Some(provenance),
        Tri::No | Tri::Neutral => None,
    }
}

/// A walk's answer: `Neutral` is a local met again on its own path (it adds
/// no definition of its own to an "every definition" question).
#[derive(Clone, Copy)]
enum Tri {
    Yes(Provenance),
    No,
    Neutral,
}

/// Every path's answer, and they agree: two paths through different globals
/// (or a global and an integer) name no one root the same-object refusal can
/// check, so they are no premise (the round-3 review's M2).
fn all(items: impl IntoIterator<Item = Tri>) -> Tri {
    let mut out = Tri::Neutral;
    for item in items {
        match (item, out) {
            (Tri::No, _) => return Tri::No,
            (Tri::Yes(provenance), Tri::Neutral) => out = Tri::Yes(provenance),
            (Tri::Yes(provenance), Tri::Yes(seen)) if provenance != seen => return Tri::No,
            _ => {}
        }
    }
    out
}

struct Walk<'tcx> {
    tcx: TyCtxt<'tcx>,
    stack: Vec<HirId>,
    depth: usize,
}

impl<'tcx> Walk<'tcx> {
    fn value(
        &mut self,
        owner: LocalDefId,
        typeck: &'tcx TypeckResults<'tcx>,
        expr: &'tcx Expr<'tcx>,
    ) -> Tri {
        match expr.kind {
            ExprKind::Cast(inner, _) => {
                if typeck.expr_ty(inner).is_integral() {
                    // A literal (`0 as *mut T`, a sentinel) addresses no object.
                    return if is_integer_literal(inner) {
                        Tri::No
                    } else {
                        Tri::Yes(Provenance::Integer)
                    };
                }
                self.value(owner, typeck, inner)
            }
            ExprKind::DropTemps(inner) => self.value(owner, typeck, inner),
            ExprKind::MethodCall(segment, receiver, _, _) => match segment.ident.name.as_str() {
                "offset" | "add" | "sub" | "wrapping_offset" | "wrapping_add" | "wrapping_sub"
                | "byte_offset" | "byte_add" | "byte_sub" | "cast" | "cast_mut" | "cast_const"
                    if typeck.expr_ty(receiver).is_raw_ptr() =>
                {
                    self.value(owner, typeck, receiver)
                }
                "as_ptr" | "as_mut_ptr" => self.storage(owner, typeck, receiver),
                _ => Tri::No,
            },
            ExprKind::AddrOf(_, _, place) => self.storage(owner, typeck, place),
            ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
                Res::Def(DefKind::Static { .. }, def) if typeck.expr_ty(expr).is_raw_ptr() => {
                    Tri::Yes(Provenance::GlobalValue(def))
                }
                Res::Local(binding) => self.local(owner, typeck, binding),
                _ => Tri::No,
            },
            ExprKind::Field(..) | ExprKind::Index(..) | ExprKind::Unary(UnOp::Deref, _) => {
                self.loaded(owner, typeck, expr)
            }
            ExprKind::If(_, then, Some(other)) => {
                let then = self.value(owner, typeck, then);
                let other = self.value(owner, typeck, other);
                all([then, other])
            }
            ExprKind::Match(_, arms, _) => {
                let answers: Vec<Tri> = arms
                    .iter()
                    .map(|arm| self.value(owner, typeck, arm.body))
                    .collect();
                all(answers)
            }
            // A labelled block's value may leave by a `break` the tail does
            // not show (the round-3 review's L1).
            ExprKind::Block(block, None) => block
                .expr
                .map_or(Tri::No, |tail| self.value(owner, typeck, tail)),
            ExprKind::Call(callee, _) => self.returned(callee),
            _ => Tri::No,
        }
    }

    /// The object a place names, reached through a global or an integer.
    fn storage(
        &mut self,
        owner: LocalDefId,
        typeck: &'tcx TypeckResults<'tcx>,
        place: &'tcx Expr<'tcx>,
    ) -> Tri {
        match place.kind {
            ExprKind::Field(base, _) | ExprKind::Index(base, _, _) | ExprKind::DropTemps(base) => {
                self.storage(owner, typeck, base)
            }
            ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
                Res::Def(DefKind::Static { .. }, def) => Tri::Yes(Provenance::GlobalStorage(def)),
                _ => Tri::No,
            },
            ExprKind::Unary(UnOp::Deref, pointer) => self.value(owner, typeck, pointer),
            _ => Tri::No,
        }
    }

    /// A pointer value read out of a place: out of a static's storage, or out
    /// of an object a global or an integer designates.
    fn loaded(
        &mut self,
        owner: LocalDefId,
        typeck: &'tcx TypeckResults<'tcx>,
        place: &'tcx Expr<'tcx>,
    ) -> Tri {
        match place.kind {
            ExprKind::Field(base, _) | ExprKind::Index(base, _, _) | ExprKind::DropTemps(base) => {
                self.loaded(owner, typeck, base)
            }
            ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
                Res::Def(DefKind::Static { .. }, def) => Tri::Yes(Provenance::GlobalValue(def)),
                _ => Tri::No,
            },
            // Only a value read out of a STATIC's storage is P11's (R936-1: "a
            // pointer value stored in or read from a static"). A pointer loaded
            // from an object a global's VALUE or an integer designates was never
            // in a static: `(*CTX).data` is 149f's in-scope core (relay 197 item
            // 3), so no premise (round-3 review H1).
            ExprKind::Unary(UnOp::Deref, pointer) => match self.value(owner, typeck, pointer) {
                Tri::Yes(Provenance::GlobalStorage(def)) => Tri::Yes(Provenance::GlobalValue(def)),
                _ => Tri::No,
            },
            _ => Tri::No,
        }
    }

    /// A local: every one of its definitions, never its entry value, its
    /// address never taken (a store through that address is a definition the
    /// text does not show).
    fn local(
        &mut self,
        owner: LocalDefId,
        typeck: &'tcx TypeckResults<'tcx>,
        binding: HirId,
    ) -> Tri {
        if self.stack.contains(&binding) {
            return Tri::Neutral;
        }
        if self.stack.len() >= 16 {
            return Tri::No;
        }
        let Some(body) = self.tcx.hir_maybe_body_owned_by(owner) else {
            return Tri::No;
        };
        let is_param = body
            .params
            .iter()
            .any(|param| matches!(param.pat.kind, PatKind::Binding(_, id, ..) if id == binding));
        let (definitions, addressed, plain_let) = definitions(body, binding);
        // A binding a pattern destructures, a `match` arm binds, or a `let`
        // without an initializer introduces holds a value the text does not
        // give here (the round-3 review's L1).
        if is_param || addressed || !plain_let || definitions.is_empty() {
            return Tri::No;
        }
        self.stack.push(binding);
        let answers: Vec<Tri> = definitions
            .into_iter()
            .map(|value| self.value(owner, typeck, value))
            .collect();
        self.stack.pop();
        all(answers)
    }

    /// The values a local getter returns.
    fn returned(&mut self, callee: &'tcx Expr<'tcx>) -> Tri {
        let ExprKind::Path(QPath::Resolved(None, path)) = callee.kind else {
            return Tri::No;
        };
        let Res::Def(DefKind::Fn, def) = path.res else {
            return Tri::No;
        };
        let Some(function) = def.as_local() else {
            return Tri::No;
        };
        if self.depth >= 4 {
            return Tri::No;
        }
        let Some(body) = self.tcx.hir_maybe_body_owned_by(function) else {
            return Tri::No;
        };
        struct Returns<'tcx>(Vec<&'tcx Expr<'tcx>>);
        impl<'tcx> Visitor<'tcx> for Returns<'tcx> {
            fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
                if let ExprKind::Ret(Some(value)) = expr.kind {
                    self.0.push(value);
                }
                if !matches!(expr.kind, ExprKind::Closure(..)) {
                    intravisit::walk_expr(self, expr);
                }
            }
        }
        let mut returns = Returns(Vec::new());
        returns.visit_expr(body.value);
        if let ExprKind::Block(block, _) = body.value.kind
            && let Some(tail) = block.expr
        {
            returns.0.push(tail);
        }
        if returns.0.is_empty() {
            return Tri::No;
        }
        let typeck = self.tcx.typeck(function);
        let stack = std::mem::take(&mut self.stack);
        self.depth += 1;
        let answers: Vec<Tri> = returns
            .0
            .into_iter()
            .map(|value| self.value(function, typeck, value))
            .collect();
        self.depth -= 1;
        self.stack = stack;
        match all(answers) {
            Tri::Neutral => Tri::No,
            other => other,
        }
    }
}

/// Every value `body` stores into `binding` (its `let` initializer, its
/// assignments), whether its address is taken anywhere, and whether a plain
/// `let` with an initializer introduces it.
fn definitions<'tcx>(
    body: &'tcx rustc_hir::Body<'tcx>,
    binding: HirId,
) -> (Vec<&'tcx Expr<'tcx>>, bool, bool) {
    struct Defs<'tcx> {
        binding: HirId,
        found: Vec<&'tcx Expr<'tcx>>,
        addressed: bool,
        plain_let: bool,
    }
    impl<'tcx> Visitor<'tcx> for Defs<'tcx> {
        fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
            if let PatKind::Binding(_, id, _, None) = local.pat.kind
                && id == self.binding
                && let Some(init) = local.init
            {
                self.found.push(init);
                self.plain_let = true;
            }
            intravisit::walk_local(self, local);
        }

        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            let names = |e: &Expr<'_>| {
                matches!(e.kind, ExprKind::Path(QPath::Resolved(None, path))
                    if path.res == Res::Local(self.binding))
            };
            match expr.kind {
                ExprKind::Assign(lhs, rhs, _) if names(lhs) => self.found.push(rhs),
                ExprKind::AddrOf(_, _, place) if names(place) => self.addressed = true,
                // A closure may write the binding where the text does not show.
                ExprKind::Closure(..) => self.addressed = true,
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut defs = Defs {
        binding,
        found: Vec::new(),
        addressed: false,
        plain_let: false,
    };
    defs.visit_body(body);
    (defs.found, defs.addressed, defs.plain_let)
}

/// An integer literal under casts and negation.
fn is_integer_literal(mut expr: &Expr<'_>) -> bool {
    loop {
        match expr.kind {
            ExprKind::Cast(inner, _)
            | ExprKind::DropTemps(inner)
            | ExprKind::Unary(UnOp::Neg, inner) => expr = inner,
            ExprKind::Lit(_) => return true,
            _ => return false,
        }
    }
}

/// R939-1: a binding or a static a pointer argument's value flows from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FlowRoot {
    Local(HirId),
    Static(DefId),
    /// The walk could not see every store (its bound was reached, or an address
    /// a store may go through is taken): related to everything, so the premise
    /// is refused (the round-6 review's MED-1 / MED-2: fail closed).
    Unbounded,
}

/// **R939-1 (the seat) — what the caller's text relates.** The bindings and
/// statics whose values flow into pointer argument `expr` of a call in
/// `caller`: through copies, casts, pointer and integer arithmetic, places and
/// their bases, aggregate literals, every store into a local or a place inside
/// it, every value the caller stores into a static it reads, every branch, a
/// call's arguments; `seed` (the argument's own P11 provenance) starts the
/// walk at the static a getter reads (the round-6 review's MED-3).
/// Over-approximate on purpose: two arguments whose sets meet are related by
/// the text and the P11 premise is not asked (a refusal is a hold); an address
/// that may carry a hidden store, or the walk's bound, is `Unbounded`.
pub(crate) fn flow_roots<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    expr: &'tcx Expr<'tcx>,
    seed: Option<Provenance>,
) -> Vec<FlowRoot> {
    let Some(body) = tcx.hir_maybe_body_owned_by(caller) else {
        return vec![FlowRoot::Unbounded];
    };
    let mut roots: Vec<FlowRoot> = Vec::new();
    let mut work: Vec<&'tcx Expr<'tcx>> = vec![expr];
    let mut add_static =
        |def: DefId, roots: &mut Vec<FlowRoot>, work: &mut Vec<&'tcx Expr<'tcx>>| {
            let root = FlowRoot::Static(def);
            if !roots.contains(&root) {
                roots.push(root);
                let (stores, addressed) = stores_into_static(body, def);
                if addressed {
                    roots.push(FlowRoot::Unbounded);
                }
                work.extend(stores);
            }
        };
    if let Some(Provenance::GlobalValue(def) | Provenance::GlobalStorage(def)) = seed {
        add_static(def, &mut roots, &mut work);
    }
    let mut steps = 0usize;
    while let Some(expr) = work.pop() {
        steps += 1;
        if steps > 512 {
            roots.push(FlowRoot::Unbounded);
            break;
        }
        match expr.kind {
            ExprKind::Cast(inner, _)
            | ExprKind::DropTemps(inner)
            | ExprKind::AddrOf(_, _, inner)
            | ExprKind::Field(inner, _)
            | ExprKind::Unary(_, inner)
            | ExprKind::Repeat(inner, _) => work.push(inner),
            ExprKind::Index(base, index, _) | ExprKind::Binary(_, base, index) => {
                work.push(base);
                work.push(index);
            }
            ExprKind::MethodCall(_, receiver, arguments, _) => {
                work.push(receiver);
                work.extend(arguments.iter());
            }
            ExprKind::Call(_, arguments)
            | ExprKind::Array(arguments)
            | ExprKind::Tup(arguments) => work.extend(arguments.iter()),
            ExprKind::Struct(_, fields, tail) => {
                work.extend(fields.iter().map(|field| field.expr));
                if let rustc_hir::StructTailExpr::Base(base) = tail {
                    work.push(base);
                }
            }
            ExprKind::If(_, then, other) => {
                work.push(then);
                work.extend(other);
            }
            ExprKind::Match(_, arms, _) => work.extend(arms.iter().map(|arm| arm.body)),
            ExprKind::Block(block, _) => work.extend(block.expr),
            ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
                Res::Local(binding) => {
                    let root = FlowRoot::Local(binding);
                    if !roots.contains(&root) {
                        roots.push(root);
                        let (stores, addressed) = stores_into_local(body, binding);
                        if addressed {
                            roots.push(FlowRoot::Unbounded);
                        }
                        work.extend(stores);
                    }
                }
                Res::Def(DefKind::Static { .. }, def) => add_static(def, &mut roots, &mut work),
                _ => {}
            },
            _ => {}
        }
    }
    roots
}

/// Do two arguments' flow roots meet (R939-1)? `Unbounded` meets everything.
pub(crate) fn shown_related(left: &[FlowRoot], right: &[FlowRoot]) -> bool {
    left.contains(&FlowRoot::Unbounded)
        || right.contains(&FlowRoot::Unbounded)
        || left.iter().any(|root| right.contains(root))
}

/// Every value `body` stores into static `def` or a place inside it, and
/// whether the body takes a MUTABLE address of it (a store may go through it
/// where the text does not tie it to `def`; `S.as_ptr()` is the storage P11
/// itself names).
fn stores_into_static<'tcx>(
    body: &'tcx rustc_hir::Body<'tcx>,
    def: DefId,
) -> (Vec<&'tcx Expr<'tcx>>, bool) {
    stores_into(
        body,
        true,
        |res| matches!(res, Res::Def(DefKind::Static { .. }, d) if d == def),
    )
}

/// Every value `body` stores into local `binding` or a place inside it (its
/// `let` initializer, `x = v`, `x.f = v`, `x[i] = v`, `x += v`), and whether
/// the body takes any address of it or holds a closure.
fn stores_into_local<'tcx>(
    body: &'tcx rustc_hir::Body<'tcx>,
    binding: HirId,
) -> (Vec<&'tcx Expr<'tcx>>, bool) {
    struct Lets<'tcx> {
        binding: HirId,
        found: Vec<&'tcx Expr<'tcx>>,
    }
    impl<'tcx> Visitor<'tcx> for Lets<'tcx> {
        fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
            let mut binds = false;
            local.pat.walk_always(|pat| {
                if let PatKind::Binding(_, id, ..) = pat.kind
                    && id == self.binding
                {
                    binds = true;
                }
            });
            if binds && let Some(init) = local.init {
                self.found.push(init);
            }
            intravisit::walk_local(self, local);
        }
    }
    let (mut stores, addressed) = stores_into(body, false, |res| res == Res::Local(binding));
    let mut lets = Lets {
        binding,
        found: Vec::new(),
    };
    lets.visit_body(body);
    stores.extend(lets.found);
    (stores, addressed)
}

/// Stores into places whose root `names` accepts, and whether such a place's
/// address is taken (any address, or only a mutable one) or a closure exists.
fn stores_into<'tcx>(
    body: &'tcx rustc_hir::Body<'tcx>,
    mutable_only: bool,
    names: impl Fn(Res) -> bool,
) -> (Vec<&'tcx Expr<'tcx>>, bool) {
    fn root_res(mut place: &Expr<'_>) -> Option<Res> {
        loop {
            match place.kind {
                ExprKind::Field(base, _)
                | ExprKind::Index(base, _, _)
                | ExprKind::DropTemps(base) => place = base,
                ExprKind::Path(QPath::Resolved(None, path)) => return Some(path.res),
                _ => return None,
            }
        }
    }
    struct Stores<'tcx, F> {
        names: F,
        mutable_only: bool,
        found: Vec<&'tcx Expr<'tcx>>,
        addressed: bool,
    }
    impl<'tcx, F: Fn(Res) -> bool> Visitor<'tcx> for Stores<'tcx, F> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            let named = |e: &Expr<'_>| root_res(e).is_some_and(|res| (self.names)(res));
            match expr.kind {
                ExprKind::Assign(lhs, rhs, _) | ExprKind::AssignOp(_, lhs, rhs) if named(lhs) => {
                    self.found.push(rhs)
                }
                ExprKind::AddrOf(_, mutability, place)
                    if named(place)
                        && (!self.mutable_only || mutability == rustc_hir::Mutability::Mut) =>
                {
                    self.addressed = true
                }
                ExprKind::MethodCall(segment, receiver, _, _)
                    if (segment.ident.name.as_str() == "as_mut_ptr"
                        || (!self.mutable_only && segment.ident.name.as_str() == "as_ptr"))
                        && named(receiver) =>
                {
                    self.addressed = true
                }
                ExprKind::Closure(..) => self.addressed = true,
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut stores = Stores {
        names,
        mutable_only,
        found: Vec::new(),
        addressed: false,
    };
    stores.visit_body(body);
    (stores.found, stores.addressed)
}
