//! **R699-2 / R707 / R923-1 — the extent a function's own loop proves**
//! (wave-4 build 1, `len-callee-bound`, narrowed by relay 112).
//!
//! A slice built over a raw pointer needs a length. Where no companion,
//! contract, array or region names one, the §77 fallback (`1024`) is used. This
//! module reads the length from the body that USES the pointer instead, but
//! only from an **arithmetic-free shape** (R923-1): the pointer is read or
//! written at the counter of a loop
//!
//! ```text
//! while i < X { …; *p.offset(i as isize) …; i += 1 }
//! ```
//!
//! whose limit `X` is a literal or one of the function's own integer
//! parameters, never written; or it is passed UNCHANGED to a local callee whose
//! own bound is instantiated with a literal or a never-written parameter. The
//! bound is the `max` of such terms, each a constant or one parameter (no
//! coefficient, no `±`): the C program computes no part of it, so no cast,
//! wrap or overflow of the C program can make it smaller than the index.
//!
//! Everything else — a literal or parameter index outside a loop, any `+`,
//! `-`, `*`, shift, method or cast on a limit or an argument, a loop with a
//! branch, `break`, `continue`, `return`, closure or nested loop in its body,
//! `<=`, a second conjunct, a counter written twice, a pointer passed at an
//! offset or by address, a closure anywhere in the body — gives no bound, and
//! the fallback stays with its receipt.
//!
//! **Only `may` (R707-1, R923-1).** Every access the body makes is below the
//! bound, so the slice never panics where the C program reads; the allocation
//! has the bound's elements on every path that runs the loop to its limit
//! (§28: a UB-free input stays inside its allocation). On a path that leaves
//! before that (a call that exits, a limit the counter starts above), the
//! length is a §77-class claim, never larger than what the loop could read.
//! The receipt is `len-callee-bound:may:<expr>`.
//!
//! The rendering evaluates in `i128` and clamps at zero:
//! `((<expr>).max(0)) as usize`.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    BinOpKind, Expr, ExprKind, HirId, LoopSource, PatKind, QPath, StmtKind, UnOp,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{
    Ty, TyCtxt,
    adjustment::{Adjust, AutoBorrow, AutoBorrowMutability},
};

/// One term of the bound: a constant, or parameter `index` itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Term {
    Constant(i128),
    Parameter(usize),
}

impl Term {
    /// An `i128` expression usable as a method receiver.
    fn render(self, argument: &dyn Fn(usize) -> String) -> String {
        match self {
            Term::Constant(k) => format!("{k}i128"),
            Term::Parameter(p) => format!("(({}) as i128)", argument(p)),
        }
    }

    fn display(self, names: &[String]) -> String {
        match self {
            Term::Constant(k) => k.to_string(),
            Term::Parameter(p) => names.get(p).cloned().unwrap_or_else(|| format!("arg{p}")),
        }
    }
}

/// The bound: the `max` of its terms (at most one constant, sorted, distinct).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Bound {
    pub(crate) terms: Vec<Term>,
}

impl Bound {
    /// The clamped count, an `i128`, with parameter `i` spelled
    /// `argument(i)` — for the glue, which casts a length `(len) as usize`
    /// itself.
    pub(crate) fn render_count(&self, argument: &dyn Fn(usize) -> String) -> String {
        if let Some(k) = self.constant() {
            return k.to_string();
        }
        let mut terms = self.terms.iter().map(|t| t.render(argument));
        let first = terms.next().unwrap_or_else(|| "0i128".to_owned());
        let max = terms.fold(first, |acc, t| format!("{acc}.max({t})"));
        format!("{max}.max(0)")
    }

    /// The length expression, a `usize`, for a site that uses it verbatim.
    pub(crate) fn render(&self, argument: &dyn Fn(usize) -> String) -> String {
        match self.constant() {
            // A bare literal, so a consumer that reads a constant length
            // (`cursor::delivered::provider_minimum`) reads this one.
            Some(k) => k.to_string(),
            None => format!("({} as usize)", self.render_count(argument)),
        }
    }

    /// The bound when it is one non-negative constant.
    fn constant(&self) -> Option<i128> {
        match self.terms.as_slice() {
            [Term::Constant(k)] if *k >= 0 => Some(*k),
            _ => None,
        }
    }

    /// `len-callee-bound:may:<expr>`, the expression in the bounded function's
    /// own parameter names.
    pub(crate) fn receipt(&self, names: &[String]) -> String {
        let expr = if self.terms.len() == 1 {
            self.terms[0].display(names)
        } else {
            format!(
                "max({})",
                self.terms
                    .iter()
                    .map(|t| t.display(names))
                    .collect::<Vec<_>>()
                    .join(",")
            )
        };
        format!("len-callee-bound:may:{expr}")
    }

    /// The max of both: the larger constant, every parameter once.
    fn join(&mut self, other: Bound) {
        for t in other.terms {
            let known = self
                .terms
                .iter()
                .position(|k| matches!(k, Term::Constant(_)));
            match (t, known) {
                (Term::Constant(new), Some(at)) => {
                    if let Term::Constant(k) = &mut self.terms[at] {
                        *k = (*k).max(new);
                    }
                }
                _ if self.terms.contains(&t) => {}
                _ => self.terms.push(t),
            }
        }
        self.terms.sort();
    }
}

/// The parameter names of `f`, in order (`arg<i>` where a pattern has none).
pub(crate) fn parameter_names(tcx: TyCtxt<'_>, f: LocalDefId) -> Vec<String> {
    let Some(body) = tcx.hir_maybe_body_owned_by(f) else { return Vec::new() };
    body.params
        .iter()
        .enumerate()
        .map(|(i, p)| match p.pat.kind {
            PatKind::Binding(_, _, ident, None) => ident.name.to_string(),
            _ => format!("arg{i}"),
        })
        .collect()
}

/// The bound on parameter `index` of `f`.
pub(crate) fn of_parameter(tcx: TyCtxt<'_>, f: LocalDefId, index: usize) -> Option<Bound> {
    let body = tcx.hir_maybe_body_owned_by(f)?;
    let PatKind::Binding(_, id, _, None) = body.params.get(index)?.pat.kind else {
        return None;
    };
    Analysis::new(tcx).bound(f, id)
}

/// The bound on a pointer LOCAL of `f`, assigned only at its `let`.
pub(crate) fn of_local(tcx: TyCtxt<'_>, f: LocalDefId, local: HirId) -> Option<Bound> {
    Analysis::new(tcx).bound(f, local)
}

/// An argument copied into a length is a plain name or a decimal literal
/// (R923-1): its text then has the parameter's own type and value — Rust has
/// no implicit integer conversion — and evaluating it again reads the same
/// value and does nothing else.
pub(crate) fn pure_argument_text(text: &str) -> bool {
    let text = text.trim();
    let name = text
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && text.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    let digits = text
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(text.len());
    let literal = digits > 0
        && matches!(
            &text[digits..],
            "" | "u8"
                | "u16"
                | "u32"
                | "u64"
                | "u128"
                | "usize"
                | "i8"
                | "i16"
                | "i32"
                | "i64"
                | "i128"
                | "isize"
        );
    name || literal
}

/// Every argument of the call is free of assignments, blocks and calls (the
/// pointer-arithmetic methods excepted), so no argument's evaluation can
/// change a value the duplicated length reads.
fn effect_free_text(text: &str) -> bool {
    if text.contains('{') {
        return false;
    }
    let chars = text.chars().collect::<Vec<_>>();
    for (i, c) in chars.iter().enumerate() {
        match c {
            '=' => {
                let before = i.checked_sub(1).map(|j| chars[j]);
                if !matches!(before, Some('=' | '!' | '<' | '>')) && chars.get(i + 1) != Some(&'=')
                {
                    return false;
                }
            }
            '(' => {
                // `(f)()` / `t[k]()` call through a parenthesized or indexed
                // callee.
                if matches!(
                    chars[..i].iter().rev().find(|c| !c.is_whitespace()),
                    Some(')' | ']')
                ) {
                    return false;
                }
                let name = chars[..i]
                    .iter()
                    .rev()
                    .skip_while(|c| c.is_whitespace())
                    .take_while(|c| c.is_alphanumeric() || **c == '_')
                    .collect::<String>()
                    .chars()
                    .rev()
                    .collect::<String>();
                if name.is_empty() {
                    continue;
                }
                // A method, and one of the pointer methods that read nothing
                // but their operands.
                let method = chars[..i]
                    .iter()
                    .rev()
                    .skip_while(|c| c.is_whitespace())
                    .skip_while(|c| c.is_alphanumeric() || **c == '_')
                    .find(|c| !c.is_whitespace())
                    == Some(&'.');
                if !method
                    || !matches!(
                        name.as_str(),
                        "offset" | "add" | "wrapping_offset" | "is_null" | "as_ptr" | "as_mut_ptr"
                    )
                {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

/// The receipt keys, interned once each (a few hundred distinct strings per
/// program) so [`super::seam::LenEvidence`] stays `Copy`.
fn intern(key: String) -> &'static str {
    use std::sync::{Mutex, OnceLock};
    static KEYS: OnceLock<Mutex<FxHashSet<&'static str>>> = OnceLock::new();
    let mut keys = KEYS
        .get_or_init(|| Mutex::new(FxHashSet::default()))
        .lock()
        .expect("callee-bound receipt interner");
    if let Some(known) = keys.get(key.as_str()) {
        return known;
    }
    let leaked: &'static str = Box::leak(key.into_boxed_str());
    keys.insert(leaked);
    leaked
}

/// **The seam's raw-argument arm.** The length text for parameter `index` of
/// `callee` at one call, instantiated with that call's own arguments, and its
/// receipt key — or `None`, and the arm keeps its fallback.
pub(crate) fn at_call_site(
    tcx: TyCtxt<'_>,
    callee: LocalDefId,
    index: usize,
    args: &[super::emitability::Arg],
    sm: &rustc_span::source_map::SourceMap,
) -> Option<(String, &'static str)> {
    let bound = of_parameter(tcx, callee, index)?;
    let texts = args
        .iter()
        .map(|a| Some((a.index, sm.span_to_snippet(a.span).ok()?)))
        .collect::<Option<FxHashMap<_, _>>>()?;
    if !texts.values().all(|t| effect_free_text(t)) {
        return None;
    }
    let needed = bound.terms.iter().filter_map(|t| match t {
        Term::Parameter(p) => Some(*p),
        Term::Constant(_) => None,
    });
    for i in needed {
        if !texts.get(&i).is_some_and(|t| pure_argument_text(t)) {
            return None;
        }
    }
    let text = bound.render_count(&|i| texts[&i].trim().to_owned());
    Some((text, intern(bound.receipt(&parameter_names(tcx, callee)))))
}

/// **The exposure wrapper and the declaration planner.** The length text for a
/// target of `f` in `f`'s own parameter names (the wrapper's formals carry the
/// same names, and a bounded parameter is never written in the body, so the
/// value at the construction is the entry value), and its receipt.
pub(crate) fn in_own_parameters(
    tcx: TyCtxt<'_>,
    f: LocalDefId,
    bound: &Bound,
    count: bool,
) -> Option<(String, String)> {
    let names = parameter_names(tcx, f);
    if bound.terms.iter().any(|t| match t {
        Term::Parameter(p) => names.get(*p).is_none_or(|n| n.starts_with("arg")),
        Term::Constant(_) => false,
    }) {
        return None;
    }
    let argument = |i: usize| names[i].clone();
    let text = if count {
        bound.render_count(&argument)
    } else {
        bound.render(&argument)
    };
    Some((text, bound.receipt(&names)))
}

struct Analysis<'tcx> {
    tcx: TyCtxt<'tcx>,
    memo: FxHashMap<(LocalDefId, HirId), Option<Bound>>,
    active: FxHashSet<(LocalDefId, HirId)>,
}

impl<'tcx> Analysis<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Analysis {
            tcx,
            memo: FxHashMap::default(),
            active: FxHashSet::default(),
        }
    }

    fn bound(&mut self, f: LocalDefId, target: HirId) -> Option<Bound> {
        if let Some(known) = self.memo.get(&(f, target)) {
            return known.clone();
        }
        // A recursive SCC refuses.
        if !self.active.insert((f, target)) {
            return None;
        }
        let result = self.compute(f, target);
        self.active.remove(&(f, target));
        self.memo.insert((f, target), result.clone());
        result
    }

    fn compute(&mut self, f: LocalDefId, target: HirId) -> Option<Bound> {
        let tcx = self.tcx;
        let body = tcx.hir_maybe_body_owned_by(f)?;
        let params = body
            .params
            .iter()
            .map(|p| match p.pat.kind {
                PatKind::Binding(_, id, _, None) => Some(id),
                _ => None,
            })
            .collect::<Vec<_>>();
        let mut writes = Writes::new_typeck(tcx.typeck(f));
        writes.visit_expr(body.value);
        // A closure, a `ref mut` binding or inline assembly writes locals this
        // census does not see (relay 112, R3-3).
        if writes.opaque {
            return None;
        }
        // The pointer itself is never re-pointed.
        if writes.written.contains(&target) || writes.borrowed.contains(&target) {
            return None;
        }
        // A local target is bound once, at its `let`.
        if !params.contains(&Some(target)) && writes.lets.get(&target) != Some(&1) {
            return None;
        }
        let mut walker = Walk {
            a: self,
            f,
            target,
            params: &params,
            writes: &writes,
            loops: Vec::new(),
            bound: None,
            refused: false,
        };
        walker.visit_expr(body.value);
        if walker.refused {
            return None;
        }
        // A pointer read nowhere proves no length (R923-1: no constant of the
        // module's own making).
        walker.bound
    }
}

#[derive(Default)]
struct Writes<'tcx> {
    typeck: Option<&'tcx rustc_middle::ty::TypeckResults<'tcx>>,
    /// Locals assigned (`=`, `op=`) anywhere, with the assignment expression.
    written: FxHashSet<HirId>,
    assignments: Vec<(HirId, HirId)>,
    /// Locals whose address is taken mutably, explicitly or by an autoref.
    borrowed: FxHashSet<HirId>,
    /// `let` bindings per local.
    lets: FxHashMap<HirId, usize>,
    /// A closure, a `ref mut` binding or inline assembly anywhere in the body.
    opaque: bool,
}

impl<'tcx> Writes<'tcx> {
    fn new_typeck(typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>) -> Self {
        Writes {
            typeck: Some(typeck),
            ..Writes::default()
        }
    }
}

fn local_of(e: &Expr<'_>) -> Option<HirId> {
    match e.kind {
        ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

fn peel_parens<'a, 'tcx>(mut e: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    while let ExprKind::DropTemps(inner) = e.kind {
        e = inner;
    }
    e
}

impl<'tcx> Visitor<'tcx> for Writes<'tcx> {
    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        match e.kind {
            ExprKind::Assign(lhs, ..) | ExprKind::AssignOp(_, lhs, _) => {
                if let Some(id) = local_of(peel_parens(lhs)) {
                    self.written.insert(id);
                    self.assignments.push((id, e.hir_id));
                }
            }
            ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, inner) => {
                if let Some(id) = local_of(peel_parens(inner)) {
                    self.borrowed.insert(id);
                }
            }
            ExprKind::Closure(..) | ExprKind::InlineAsm(..) => self.opaque = true,
            ExprKind::Path(..) => {
                // A `&mut self` method on a local (`n.add_assign(1)`) borrows
                // it through its autoref.
                if let Some(id) = local_of(e)
                    && let Some(typeck) = self.typeck
                    && typeck.expr_adjustments(e).iter().any(|a| {
                        matches!(
                            a.kind,
                            Adjust::Borrow(
                                AutoBorrow::Ref(AutoBorrowMutability::Mut { .. })
                                    | AutoBorrow::RawPtr(rustc_hir::Mutability::Mut)
                            )
                        )
                    })
                {
                    self.borrowed.insert(id);
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }

    fn visit_pat(&mut self, p: &'tcx rustc_hir::Pat<'tcx>) {
        if let PatKind::Binding(mode, ..) = p.kind
            && matches!(mode.0, rustc_hir::ByRef::Yes(rustc_hir::Mutability::Mut))
        {
            self.opaque = true;
        }
        intravisit::walk_pat(self, p);
    }

    fn visit_local(&mut self, l: &'tcx rustc_hir::LetStmt<'tcx>) {
        if let PatKind::Binding(_, id, _, _) = l.pat.kind {
            *self.lets.entry(id).or_insert(0) += 1;
        }
        intravisit::walk_local(self, l);
    }
}

/// One enclosing `while` loop: its body block, the conjuncts of its condition
/// and whether the body is straight.
struct LoopFrame<'tcx> {
    body: &'tcx rustc_hir::Block<'tcx>,
    conjuncts: Vec<&'tcx Expr<'tcx>>,
    straight: bool,
}

/// No branch, loop, `break`, `continue`, `return`, short-circuit, closure or
/// `let` expression anywhere in `body`: every statement runs on every
/// iteration, in order (relay 107 F4b, relay 112 R3-5).
fn straight_block(body: &rustc_hir::Block<'_>) -> bool {
    struct V(bool);
    impl<'v> Visitor<'v> for V {
        fn visit_expr(&mut self, e: &'v Expr<'v>) {
            if matches!(
                e.kind,
                ExprKind::If(..)
                    | ExprKind::Match(..)
                    | ExprKind::Loop(..)
                    | ExprKind::Break(..)
                    | ExprKind::Continue(..)
                    | ExprKind::Ret(..)
                    | ExprKind::Closure(..)
                    | ExprKind::Let(..)
                    | ExprKind::InlineAsm(..)
                    | ExprKind::Yield(..)
                    | ExprKind::Become(..)
            ) || matches!(e.kind, ExprKind::Binary(op, ..) if matches!(op.node, BinOpKind::And | BinOpKind::Or))
            {
                self.0 = false;
            }
            intravisit::walk_expr(self, e)
        }
    }
    let mut v = V(true);
    v.visit_block(body);
    v.0
}

struct Walk<'a, 'b, 'tcx> {
    a: &'a mut Analysis<'tcx>,
    f: LocalDefId,
    target: HirId,
    params: &'b [Option<HirId>],
    writes: &'b Writes<'tcx>,
    loops: Vec<LoopFrame<'tcx>>,
    bound: Option<Bound>,
    refused: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Sign {
    Signed,
    Unsigned,
}

fn int_info<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(u64, Sign)> {
    if !ty.is_integral() {
        return None;
    }
    let (size, signed) = ty.int_size_and_signed(tcx);
    Some((
        size.bits(),
        if signed { Sign::Signed } else { Sign::Unsigned },
    ))
}

/// `to` holds every value of `from` exactly.
fn value_preserving(from: (u64, Sign), to: (u64, Sign)) -> bool {
    match (from.1, to.1) {
        (Sign::Signed, Sign::Signed) | (Sign::Unsigned, Sign::Unsigned) => to.0 >= from.0,
        (Sign::Unsigned, Sign::Signed) => to.0 > from.0,
        (Sign::Signed, Sign::Unsigned) => false,
    }
}

fn literal(e: &Expr<'_>) -> Option<i128> {
    match e.kind {
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(value, _) => i128::try_from(value.get()).ok(),
            _ => None,
        },
        _ => None,
    }
}

fn offset_call<'tcx>(e: &'tcx Expr<'tcx>) -> Option<(&'tcx Expr<'tcx>, &'tcx Expr<'tcx>)> {
    match e.kind {
        ExprKind::MethodCall(segment, receiver, [arg], _)
            if matches!(segment.ident.name.as_str(), "offset" | "add") =>
        {
            Some((receiver, arg))
        }
        _ => None,
    }
}

impl<'tcx> Walk<'_, '_, 'tcx> {
    fn is_target(&self, e: &Expr<'_>) -> bool {
        local_of(peel_parens(e)) == Some(self.target)
    }

    fn refuse(&mut self) {
        self.refused = true;
    }

    fn add(&mut self, b: Bound) {
        match &mut self.bound {
            Some(known) => known.join(b),
            None => self.bound = Some(b),
        }
    }

    fn typeck(&self) -> &'tcx rustc_middle::ty::TypeckResults<'tcx> {
        self.a.tcx.typeck(self.f)
    }

    /// A parameter of `f` usable in a bound: integer-typed and never written
    /// or borrowed mutably.
    fn bound_param(&self, id: HirId) -> Option<usize> {
        let index = self.params.iter().position(|p| *p == Some(id))?;
        if self.writes.written.contains(&id) || self.writes.borrowed.contains(&id) {
            return None;
        }
        int_info(self.a.tcx, self.typeck().node_type(id))?;
        Some(index)
    }

    /// A limit or an argument as a term: a non-negative literal, a literal
    /// under casts it fits through unchanged, or a bound parameter — with no
    /// operator and no other cast (R923-1).
    fn term(&self, e: &'tcx Expr<'tcx>) -> Option<Term> {
        let e = peel_parens(e);
        if let Some(k) = literal(e) {
            return Some(Term::Constant(k));
        }
        match e.kind {
            ExprKind::Path(..) => self.bound_param(local_of(e)?).map(Term::Parameter),
            ExprKind::Cast(inner, _) => {
                let Term::Constant(k) = self.term(inner)? else { return None };
                let ty = self.typeck().expr_ty(e);
                let (bits, sign) = int_info(self.a.tcx, ty)?;
                let max = match sign {
                    Sign::Signed => (1i128 << (bits - 1)) - 1,
                    Sign::Unsigned if bits >= 127 => i128::MAX,
                    Sign::Unsigned => (1i128 << bits) - 1,
                };
                (k <= max).then_some(Term::Constant(k))
            }
            _ => None,
        }
    }

    /// The loop counter an index names: `i`, or `i` under value-preserving
    /// widening casts (`i as isize`), and nothing else.
    fn counter(&self, idx: &'tcx Expr<'tcx>) -> Option<HirId> {
        let idx = peel_parens(idx);
        match idx.kind {
            ExprKind::Cast(inner, _) => {
                let from = int_info(self.a.tcx, self.typeck().expr_ty(inner))?;
                let to = int_info(self.a.tcx, self.typeck().expr_ty(idx))?;
                value_preserving(from, to).then(|| self.counter(inner))?
            }
            _ => local_of(idx),
        }
    }

    /// `i < X` from the innermost enclosing loop, which must be a straight
    /// `while i < X` whose body writes `i` once, as its last statement, by
    /// one; `at` is a statement before that write.
    fn loop_bound(&self, i: HirId, at: HirId) -> Option<Term> {
        let tcx = self.a.tcx;
        if self.writes.borrowed.contains(&i) {
            return None;
        }
        let frame = self.loops.last()?;
        if !frame.straight {
            return None;
        }
        // One conjunct, `i < X` or `X > i`, `i` bare.
        let [cond] = frame.conjuncts.as_slice() else { return None };
        let ExprKind::Binary(op, l, r) = peel_parens(cond).kind else { return None };
        let (var, x) = match op.node {
            BinOpKind::Lt => (l, r),
            BinOpKind::Gt => (r, l),
            _ => return None,
        };
        if local_of(peel_parens(var)) != Some(i) {
            return None;
        }
        let bound = self.term(x)?;
        // The counter's one write in the body: its last statement or its
        // tail, `i += 1` or `i = i + 1`.
        let inside = self
            .writes
            .assignments
            .iter()
            .filter(|(var, a)| {
                *var == i && tcx.hir_parent_id_iter(*a).any(|p| p == frame.body.hir_id)
            })
            .map(|(_, a)| *a)
            .collect::<Vec<_>>();
        let [write] = inside.as_slice() else { return None };
        let last = match frame.body.expr {
            Some(tail) => tail.hir_id == *write,
            None => frame.body.stmts.last().is_some_and(
                |s| matches!(s.kind, StmtKind::Semi(e) | StmtKind::Expr(e) if e.hir_id == *write),
            ),
        };
        if !last || !Self::steps_by_one(tcx.hir_node(*write), i) {
            return None;
        }
        // `at` lies in a statement of the body other than the write.
        let in_statement = frame.body.stmts.iter().any(|s| {
            !matches!(s.kind, StmtKind::Semi(e) | StmtKind::Expr(e) if e.hir_id == *write)
                && tcx.hir_parent_id_iter(at).any(|p| p == s.hir_id)
        });
        in_statement.then_some(bound)
    }

    /// `i += 1` or `i = i + 1`, the `1` a bare literal.
    fn steps_by_one(node: rustc_hir::Node<'_>, i: HirId) -> bool {
        let rustc_hir::Node::Expr(e) = node else { return false };
        let one = |e: &Expr<'_>| literal(peel_parens(e)) == Some(1);
        match e.kind {
            ExprKind::AssignOp(op, lhs, rhs) => {
                op.node == rustc_hir::AssignOpKind::AddAssign
                    && local_of(peel_parens(lhs)) == Some(i)
                    && one(rhs)
            }
            ExprKind::Assign(lhs, rhs, _) if local_of(peel_parens(lhs)) == Some(i) => {
                matches!(peel_parens(rhs).kind, ExprKind::Binary(op, l, r)
                    if op.node == BinOpKind::Add && local_of(peel_parens(l)) == Some(i) && one(r))
            }
            _ => false,
        }
    }

    /// `*p.offset(idx)` / `*p.add(idx)`: the index must be a loop counter.
    fn access(&mut self, idx: &'tcx Expr<'tcx>, at: HirId) {
        match self.counter(idx).and_then(|i| self.loop_bound(i, at)) {
            Some(term) => self.add(Bound { terms: vec![term] }),
            None => self.refuse(),
        }
    }

    /// The pointer passed unchanged to `callee` at position `j`.
    fn compose(&mut self, callee: &'tcx Expr<'tcx>, args: &'tcx [Expr<'tcx>], j: usize) {
        let tcx = self.a.tcx;
        let ExprKind::Path(QPath::Resolved(None, path)) = callee.kind else {
            return self.refuse();
        };
        let Res::Def(DefKind::Fn, def) = path.res else { return self.refuse() };
        let Some(local) = def.as_local() else { return self.refuse() };
        let Some(callee_body) = tcx.hir_maybe_body_owned_by(local) else {
            return self.refuse();
        };
        let Some(PatKind::Binding(_, param, _, None)) =
            callee_body.params.get(j).map(|p| p.pat.kind)
        else {
            return self.refuse();
        };
        let Some(inner) = self.a.bound(local, param) else { return self.refuse() };
        // Instantiate the callee's parameters with this call's arguments.
        let mut terms = Vec::new();
        for t in &inner.terms {
            terms.push(match *t {
                Term::Constant(k) => Term::Constant(k),
                Term::Parameter(p) => {
                    let Some(term) = args.get(p).and_then(|arg| self.term(arg)) else {
                        return self.refuse();
                    };
                    term
                }
            });
        }
        let mut bound = Bound { terms: Vec::new() };
        bound.join(Bound { terms });
        self.add(bound);
    }
}

impl<'tcx> Visitor<'tcx> for Walk<'_, '_, 'tcx> {
    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if self.refused {
            return;
        }
        match e.kind {
            ExprKind::Loop(block, _, source, _) => {
                if source == LoopSource::While
                    && let Some(tail) = block.expr
                    && let ExprKind::If(cond, then, _) = tail.kind
                    && let ExprKind::Block(body, _) = then.kind
                {
                    let mut conjuncts = Vec::new();
                    let mut stack = vec![peel_parens(cond)];
                    while let Some(c) = stack.pop() {
                        match c.kind {
                            ExprKind::Binary(op, l, r) if op.node == BinOpKind::And => {
                                stack.push(peel_parens(l));
                                stack.push(peel_parens(r));
                            }
                            _ => conjuncts.push(c),
                        }
                    }
                    self.visit_expr(cond);
                    self.loops.push(LoopFrame {
                        body,
                        conjuncts,
                        straight: straight_block(body),
                    });
                    self.visit_block(body);
                    self.loops.pop();
                    return;
                }
                self.loops.push(LoopFrame {
                    body: block,
                    conjuncts: Vec::new(),
                    straight: false,
                });
                intravisit::walk_expr(self, e);
                self.loops.pop();
                return;
            }
            // An address formed from the pointee (`&*p`, `&raw const *p`,
            // `&mut *p.offset(i)`) escapes; it is no access (relay 112, R3-4).
            ExprKind::AddrOf(_, _, inner) => {
                if let ExprKind::Unary(UnOp::Deref, place) = peel_parens(inner).kind
                    && (self.is_target(place)
                        || offset_call(peel_parens(place)).is_some_and(|(r, _)| self.is_target(r)))
                {
                    return self.refuse();
                }
            }
            ExprKind::Unary(UnOp::Deref, inner) => {
                if let Some((receiver, idx)) = offset_call(peel_parens(inner))
                    && self.is_target(receiver)
                {
                    self.visit_expr(idx);
                    return self.access(idx, e.hir_id);
                }
                // `*p` reads a literal index (R923-1: no constant of the
                // module's own making); it falls to the bare path below.
            }
            ExprKind::Call(callee, args) => {
                self.visit_expr(callee);
                for (j, arg) in args.iter().enumerate() {
                    if self.is_target(arg) {
                        self.compose(callee, args, j);
                    } else {
                        self.visit_expr(arg);
                    }
                }
                return;
            }
            ExprKind::MethodCall(segment, receiver, args, _)
                if self.is_target(receiver)
                    && matches!(segment.ident.name.as_str(), "is_null" | "offset_from") =>
            {
                for arg in args {
                    if !self.is_target(arg) {
                        self.visit_expr(arg);
                    }
                }
                return;
            }
            ExprKind::MethodCall(segment, receiver, [arg], _)
                if segment.ident.name.as_str() == "offset_from" && self.is_target(arg) =>
            {
                self.visit_expr(receiver);
                return;
            }
            ExprKind::Path(..) if self.is_target(e) => return self.refuse(),
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }
}
