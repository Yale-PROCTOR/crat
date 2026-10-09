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
//! returned values of a local getter, a place in a static's storage or reached
//! through such a pointer. Anything else is no premise, so the pair stays with
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
/// an integer. Never for one global at both positions, nor for two integers:
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
                (Provenance::GlobalValue(x), Provenance::GlobalValue(y))
                | (Provenance::GlobalStorage(x), Provenance::GlobalStorage(y)) => x == y,
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

fn all(items: impl IntoIterator<Item = Tri>) -> Tri {
    let mut out = Tri::Neutral;
    for item in items {
        match item {
            Tri::No => return Tri::No,
            Tri::Yes(provenance) => {
                if matches!(out, Tri::Neutral) {
                    out = Tri::Yes(provenance);
                }
            }
            Tri::Neutral => {}
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
            ExprKind::Block(block, _) => block
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
            ExprKind::Unary(UnOp::Deref, pointer) => match self.value(owner, typeck, pointer) {
                Tri::Yes(Provenance::GlobalStorage(def)) => Tri::Yes(Provenance::GlobalValue(def)),
                other => other,
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
        let (definitions, addressed) = definitions(body, binding);
        if is_param || addressed || definitions.is_empty() {
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
/// assignments), and whether its address is taken anywhere.
fn definitions<'tcx>(
    body: &'tcx rustc_hir::Body<'tcx>,
    binding: HirId,
) -> (Vec<&'tcx Expr<'tcx>>, bool) {
    struct Defs<'tcx> {
        binding: HirId,
        found: Vec<&'tcx Expr<'tcx>>,
        addressed: bool,
    }
    impl<'tcx> Visitor<'tcx> for Defs<'tcx> {
        fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
            if let PatKind::Binding(_, id, _, _) = local.pat.kind
                && id == self.binding
                && let Some(init) = local.init
            {
                self.found.push(init);
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
    };
    defs.visit_body(body);
    (defs.found, defs.addressed)
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
