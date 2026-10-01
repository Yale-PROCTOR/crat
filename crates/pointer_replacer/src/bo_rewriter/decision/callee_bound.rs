//! **R699-2 / R707 / R717-1 — the extent a function's own accesses prove**
//! (wave-4 build 1, `len-callee-bound`).
//!
//! A slice built over a raw pointer needs a length. Where no companion,
//! contract, array or region names one, the §77 fallback (`1024`) is used. This
//! module reads the length from the body that USES the pointer instead: every
//! element the body touches is at an index the body itself bounds, so the
//! maximum index plus one is a length the allocation has wherever that access
//! runs (§28: a UB-free input stays inside its allocation).
//!
//! The bound is a [`Bound`]: the `max` of linear expressions in the function's
//! own integer parameters — a constant `k`, `p`, `p ± k`, `p − q`. Three forms
//! of index produce one:
//!   (a) a literal `c` (`*p`, `*p.offset(c)`) → `c + 1`;
//!   (b) the variable `i` of an enclosing `while i < X` (`<= X` → `X + 1`),
//!       optionally `i ± v` for a constant or parameter `v`, where `X` is itself
//!       such an expression and `i` is written only after the access, at the
//!       loop body's own top level → `X (± v)`;
//!   (c) the pointer (or `p.offset(e)`, `&*p.offset(e)`) passed to a LOCAL
//!       callee whose own bound for that parameter is instantiated with the
//!       call's arguments → that bound (`+ e`).
//! Anything else — an index read from memory, a bound on a local or a global,
//! the pointer stored, cast, reassigned, compared or handed to a foreign
//! function, a recursive callee — gives no bound, and the fallback stays.
//!
//! **Must and may (R707-1).** A bound is `must` when every access runs on every
//! call: the body has no branch, loop, early return or short-circuit, so the
//! allocation has the bound's elements at the construction (R677-6's meaning).
//! Every other bound is `may`: every access the body makes is below it (so the
//! slice never panics where the C program reads), and the allocation has the
//! bound's elements on every path that performs the maximal access; on a path
//! that returns before reading, the length is a §77-class claim — never larger
//! than what the body could read. The receipt carries the tag
//! (`len-callee-bound:<must|may>:<expr>`) so the two are counted apart.
//!
//! **Soundness of the arithmetic.** The bound must over-approximate the index,
//! so every step that could make the rendered value SMALLER than the real one
//! refuses: subtraction or a negative coefficient on an unsigned operand (it
//! wraps), a cast that can increase a value (signed → unsigned, signed
//! narrowing) on the bound side, a cast that can shrink the loop variable on
//! the index side. The rendering evaluates in `i128` and clamps at zero:
//! `((<expr>).max(0)) as usize`.

use std::collections::BTreeMap;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    BinOpKind, Expr, ExprKind, HirId, LoopSource, Node, PatKind, QPath, StmtKind, UnOp,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{Ty, TyCtxt};

/// One linear term set: `k + Σ c·param`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Lin {
    pub(crate) k: i128,
    /// parameter index → coefficient (never zero).
    pub(crate) terms: BTreeMap<usize, i128>,
}

impl Lin {
    fn constant(k: i128) -> Self {
        Lin {
            k,
            terms: BTreeMap::new(),
        }
    }

    fn param(index: usize) -> Self {
        Lin {
            k: 0,
            terms: BTreeMap::from([(index, 1)]),
        }
    }

    fn plus(&self, other: &Lin, sign: i128) -> Lin {
        let mut out = self.clone();
        out.k += sign * other.k;
        for (p, c) in &other.terms {
            let v = out.terms.entry(*p).or_insert(0);
            *v += sign * c;
        }
        out.terms.retain(|_, c| *c != 0);
        out
    }

    /// An `i128` expression usable as a method receiver: `3i128`,
    /// `((n) as i128)`, or a parenthesised sum.
    fn render(&self, argument: &dyn Fn(usize) -> String) -> String {
        let mut parts = Vec::new();
        for (p, c) in &self.terms {
            let a = format!("(({}) as i128)", argument(*p));
            parts.push(match c {
                1 => a,
                -1 => format!("-{a}"),
                c => format!("{c} * {a}"),
            });
        }
        if parts.is_empty() {
            return if self.k < 0 {
                format!("({}i128)", self.k)
            } else {
                format!("{}i128", self.k)
            };
        }
        if self.k != 0 {
            parts.push(format!("{}i128", self.k));
        }
        if parts.len() == 1 && !parts[0].starts_with('-') {
            return parts.remove(0);
        }
        format!("({})", parts.join(" + ").replace("+ -", "- "))
    }

    fn display(&self, names: &[String]) -> String {
        let mut parts = Vec::new();
        for (p, c) in &self.terms {
            let n = names.get(*p).cloned().unwrap_or_else(|| format!("arg{p}"));
            parts.push(match c {
                1 => n,
                -1 => format!("-{n}"),
                c => format!("{c}*{n}"),
            });
        }
        if self.k != 0 || parts.is_empty() {
            parts.push(self.k.to_string());
        }
        parts.join("+").replace("+-", "-")
    }
}

/// The bound: the `max` of its terms, tagged must or may.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Bound {
    pub(crate) terms: Vec<Lin>,
    pub(crate) must: bool,
}

impl Bound {
    fn tag(&self) -> &'static str {
        if self.must { "must" } else { "may" }
    }

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
            [only] if only.terms.is_empty() && only.k >= 0 => Some(only.k),
            _ => None,
        }
    }

    /// `len-callee-bound:<must|may>:<expr>`, the expression in the bounded
    /// function's own parameter names.
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
        format!("len-callee-bound:{}:{expr}", self.tag())
    }

    /// The max of both. Terms over the same parameters differ only in their
    /// constant, so the larger one dominates and the other is dropped (`max(1,
    /// 4)` is `4`; `max(n, n + 1)` is `n + 1`).
    fn join(&mut self, other: Bound) {
        self.must &= other.must;
        for t in other.terms {
            match self.terms.iter_mut().find(|known| known.terms == t.terms) {
                Some(known) => known.k = known.k.max(t.k),
                None => self.terms.push(t),
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

/// A call-site argument is admitted as an instantiation only when it is free
/// of calls, assignments and blocks — it is duplicated into the length.
pub(crate) fn pure_argument_text(text: &str) -> bool {
    // No block, index, address-of or assignment.
    if text.contains('{') || text.contains('[') || text.contains('&') {
        return false;
    }
    let chars = text.chars().collect::<Vec<_>>();
    for (i, c) in chars.iter().enumerate() {
        let prev = chars[..i]
            .iter()
            .rev()
            .find(|c| !c.is_whitespace())
            .copied();
        let word = |c: Option<char>| c.is_some_and(|c| c.is_alphanumeric() || c == '_');
        match c {
            '=' => {
                let before = i.checked_sub(1).map(|j| chars[j]);
                if !matches!(before, Some('=' | '!' | '<' | '>')) && chars.get(i + 1) != Some(&'=')
                {
                    return false;
                }
            }
            // A call — except the integer `wrapping_*` methods, which read
            // nothing but their operands.
            '(' if word(prev) || prev == Some('>') => {
                let name = chars[..i]
                    .iter()
                    .rev()
                    .skip_while(|c| c.is_whitespace())
                    .take_while(|c| c.is_alphanumeric() || **c == '_')
                    .collect::<String>()
                    .chars()
                    .rev()
                    .collect::<String>();
                if !matches!(
                    name.as_str(),
                    "wrapping_add" | "wrapping_sub" | "wrapping_mul"
                ) {
                    return false;
                }
            }
            // A dereference reads memory another argument's call may write.
            '*' if !(word(prev) || prev == Some(')')) => return false,
            _ => {}
        }
    }
    true
}

/// Every argument of the call is free of assignments, blocks and calls (the
/// pointer-arithmetic and integer methods excepted), so no argument's
/// evaluation can change a value the duplicated length reads.
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
                let name = chars[..i]
                    .iter()
                    .rev()
                    .skip_while(|c| c.is_whitespace())
                    .take_while(|c| c.is_alphanumeric() || **c == '_')
                    .collect::<String>()
                    .chars()
                    .rev()
                    .collect::<String>();
                if !name.is_empty()
                    && !matches!(
                        name.as_str(),
                        "offset"
                            | "add"
                            | "wrapping_offset"
                            | "wrapping_add"
                            | "wrapping_sub"
                            | "wrapping_mul"
                            | "is_null"
                            | "as_ptr"
                            | "as_mut_ptr"
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
    let needed = bound
        .terms
        .iter()
        .flat_map(|t| t.terms.keys().copied())
        .collect::<FxHashSet<_>>();
    if !needed
        .iter()
        .all(|i| texts.get(i).is_some_and(|t| pure_argument_text(t)))
    {
        return None;
    }
    let text = bound.render_count(&|i| texts[&i].clone());
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
    let needed = bound
        .terms
        .iter()
        .flat_map(|t| t.terms.keys().copied())
        .collect::<FxHashSet<_>>();
    if needed
        .iter()
        .any(|i| names.get(*i).is_none_or(|n| n.starts_with("arg")))
    {
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
        // A recursive SCC refuses (build 1).
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
        let mut writes = Writes::default();
        writes.visit_expr(body.value);
        // The pointer itself is never re-pointed (a walker is build 2's).
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
            straight: true,
        };
        walker.visit_expr(body.value);
        if walker.refused {
            return None;
        }
        let straight = walker.straight;
        // A pointer the body never reads or passes on is read at no index:
        // its extent is 0, on every path.
        let mut bound = walker.bound.unwrap_or(Bound {
            terms: vec![Lin::constant(0)],
            must: true,
        });
        bound.must &= straight;
        Some(bound)
    }
}

#[derive(Default)]
struct Writes {
    /// Locals assigned (`=`, `op=`) anywhere, with the assignment expression.
    written: FxHashSet<HirId>,
    assignments: Vec<(HirId, HirId)>,
    /// Locals whose address is taken mutably.
    borrowed: FxHashSet<HirId>,
    /// `let` bindings per local.
    lets: FxHashMap<HirId, usize>,
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

impl<'tcx> Visitor<'tcx> for Writes {
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
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }

    fn visit_local(&mut self, l: &'tcx rustc_hir::LetStmt<'tcx>) {
        if let PatKind::Binding(_, id, _, _) = l.pat.kind {
            *self.lets.entry(id).or_insert(0) += 1;
        }
        intravisit::walk_local(self, l);
    }
}

/// One enclosing `while` loop: its own expression, its body block and the
/// conjuncts of its condition.
struct LoopFrame<'tcx> {
    body: &'tcx rustc_hir::Block<'tcx>,
    conjuncts: Vec<&'tcx Expr<'tcx>>,
}

struct Walk<'a, 'b, 'tcx> {
    a: &'a mut Analysis<'tcx>,
    f: LocalDefId,
    target: HirId,
    params: &'b [Option<HirId>],
    writes: &'b Writes,
    loops: Vec<LoopFrame<'tcx>>,
    bound: Option<Bound>,
    refused: bool,
    /// No branch, loop, early return or short-circuit seen anywhere.
    straight: bool,
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

fn literal(e: &Expr<'_>) -> Option<i128> {
    match e.kind {
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(value, _) => i128::try_from(value.get()).ok(),
            _ => None,
        },
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

    /// A parameter of `f` usable in a bound: integer-typed and never written.
    fn bound_param(&self, id: HirId) -> Option<usize> {
        let index = self.params.iter().position(|p| *p == Some(id))?;
        if self.writes.written.contains(&id) || self.writes.borrowed.contains(&id) {
            return None;
        }
        int_info(self.a.tcx, self.typeck().node_type(id))?;
        Some(index)
    }

    /// A VALUE as a linear expression in `f`'s parameters, over-approximating
    /// it from neither side: only exact steps are admitted (constants,
    /// parameters, value-preserving casts, signed `±`, unsigned `+`).
    fn value(&self, e: &'tcx Expr<'tcx>) -> Option<Lin> {
        let e = peel_parens(e);
        if let Some(k) = literal(e) {
            return Some(Lin::constant(k));
        }
        match e.kind {
            ExprKind::Path(..) => self.bound_param(local_of(e)?).map(Lin::param),
            ExprKind::Cast(inner, _) => {
                let from = int_info(self.a.tcx, self.typeck().expr_ty(inner))?;
                let to = int_info(self.a.tcx, self.typeck().expr_ty(e))?;
                value_preserving(from, to).then(|| self.value(inner))?
            }
            ExprKind::Binary(op, l, r) => {
                let sign = int_info(self.a.tcx, self.typeck().expr_ty(e))?.1;
                match op.node {
                    BinOpKind::Add => Some(self.value(l)?.plus(&self.value(r)?, 1)),
                    BinOpKind::Sub if sign == Sign::Signed => {
                        Some(self.value(l)?.plus(&self.value(r)?, -1))
                    }
                    _ => None,
                }
            }
            ExprKind::MethodCall(segment, receiver, [arg], _)
                if segment.ident.name.as_str() == "wrapping_add" =>
            {
                Some(self.value(receiver)?.plus(&self.value(arg)?, 1))
            }
            _ => None,
        }
    }

    /// An upper bound on a LOOP-BOUND expression `X`: over-approximation is
    /// sound here, so casts that can only shrink the value are admitted.
    fn upper(&self, e: &'tcx Expr<'tcx>) -> Option<Lin> {
        let e = peel_parens(e);
        if let ExprKind::Cast(inner, _) = e.kind {
            let from = int_info(self.a.tcx, self.typeck().expr_ty(inner))?;
            let to = int_info(self.a.tcx, self.typeck().expr_ty(e))?;
            return never_increases(from, to).then(|| self.upper(inner))?;
        }
        self.value(e)
    }

    /// `ub(idx)`: a linear expression `L` with `idx < L` at the access.
    fn index_bound(&self, idx: &'tcx Expr<'tcx>, at: HirId) -> Option<Lin> {
        let idx = peel_parens(idx);
        if let Some(k) = literal(idx) {
            return Some(Lin::constant(k + 1));
        }
        match idx.kind {
            ExprKind::Cast(inner, _) => {
                let from = int_info(self.a.tcx, self.typeck().expr_ty(inner))?;
                let to = int_info(self.a.tcx, self.typeck().expr_ty(idx))?;
                // The index the access uses is the cast value; it equals the
                // inner value whenever that is in range of the target, which a
                // pointer offset of a real allocation always is.
                (from.0 <= to.0 || from.1 == Sign::Unsigned && from.0 <= to.0 + 1)
                    .then(|| self.index_bound(inner, at))?
            }
            ExprKind::Path(..) => {
                let id = local_of(idx)?;
                if let Some(p) = self.bound_param(id) {
                    return Some(Lin::param(p).plus(&Lin::constant(1), 1));
                }
                self.loop_bound(id, at)
            }
            ExprKind::Binary(op, l, r) => {
                let sign = int_info(self.a.tcx, self.typeck().expr_ty(idx))?.1;
                match op.node {
                    BinOpKind::Add => {
                        if let Some(v) = self.value(r) {
                            Some(self.index_bound(l, at)?.plus(&v, 1))
                        } else {
                            Some(self.index_bound(r, at)?.plus(&self.value(l)?, 1))
                        }
                    }
                    BinOpKind::Sub if sign == Sign::Signed => {
                        Some(self.index_bound(l, at)?.plus(&self.value(r)?, -1))
                    }
                    _ => None,
                }
            }
            ExprKind::MethodCall(segment, receiver, [arg], _)
                if segment.ident.name.as_str() == "wrapping_add" =>
            {
                Some(self.index_bound(receiver, at)?.plus(&self.value(arg)?, 1))
            }
            _ => None,
        }
    }

    /// `i < X` from the innermost enclosing `while` whose condition bounds `i`,
    /// valid at `at` only when `i` is written in that loop nowhere but at the
    /// loop body's top level, AFTER the statement that contains `at`.
    fn loop_bound(&self, i: HirId, at: HirId) -> Option<Lin> {
        let tcx = self.a.tcx;
        // A counter whose address is taken may be written through it.
        if self.writes.borrowed.contains(&i) {
            return None;
        }
        for frame in self.loops.iter().rev() {
            let mut found = None;
            for c in &frame.conjuncts {
                let ExprKind::Binary(op, l, r) = peel_parens(c).kind else { continue };
                let (var, x, inclusive) = match op.node {
                    BinOpKind::Lt => (l, r, false),
                    BinOpKind::Le => (l, r, true),
                    BinOpKind::Gt => (r, l, false),
                    BinOpKind::Ge => (r, l, true),
                    _ => continue,
                };
                if !self.is_counter(var, i) {
                    continue;
                }
                let Some(x) = self.upper(x) else { continue };
                found = Some(if inclusive {
                    x.plus(&Lin::constant(1), 1)
                } else {
                    x
                });
                break;
            }
            let Some(bound) = found else { continue };
            // Position of the top-level statement containing `at`.
            let contains = |stmt: &rustc_hir::Stmt<'_>, id: HirId| {
                tcx.hir_parent_id_iter(id).any(|p| p == stmt.hir_id)
            };
            let at_position = frame.body.stmts.iter().position(|s| contains(s, at));
            for (var, assignment) in &self.writes.assignments {
                if *var != i {
                    continue;
                }
                let inside = tcx
                    .hir_parent_id_iter(*assignment)
                    .any(|p| p == frame.body.hir_id);
                if !inside {
                    continue;
                }
                // Admitted only as a top-level statement after `at`'s, or as
                // the body's own tail (`{ …; i += 1 }`), which runs after every
                // statement — provided `at` is in a statement.
                let position = frame.body.stmts.iter().position(|s| {
                    matches!(s.kind, StmtKind::Semi(e) | StmtKind::Expr(e) if e.hir_id == *assignment)
                });
                let is_tail = frame
                    .body
                    .expr
                    .is_some_and(|tail| tail.hir_id == *assignment);
                match (position, at_position) {
                    (Some(w), Some(a)) if w > a => {}
                    (None, Some(_)) if is_tail => {}
                    _ => return None,
                }
            }
            return Some(bound);
        }
        None
    }

    /// `var` is the counter `i` itself, or `i` under a value-preserving cast.
    fn is_counter(&self, var: &'tcx Expr<'tcx>, i: HirId) -> bool {
        let var = peel_parens(var);
        match var.kind {
            ExprKind::Cast(inner, _) => {
                let from = int_info(self.a.tcx, self.typeck().expr_ty(inner));
                let to = int_info(self.a.tcx, self.typeck().expr_ty(var));
                matches!((from, to), (Some(f), Some(t)) if value_preserving(f, t))
                    && self.is_counter(inner, i)
            }
            _ => local_of(var) == Some(i),
        }
    }

    fn access(&mut self, idx: Option<&'tcx Expr<'tcx>>, at: HirId) {
        let lin = match idx {
            None => Some(Lin::constant(1)),
            Some(idx) => self.index_bound(idx, at),
        };
        match lin {
            Some(lin) => {
                let must = lin.terms.is_empty() && self.loops.is_empty();
                self.add(Bound {
                    terms: vec![lin],
                    must,
                })
            }
            None => self.refuse(),
        }
    }

    /// The pointer (at offset `offset`) passed to `callee` at position `j`.
    fn compose(
        &mut self,
        call: &'tcx Expr<'tcx>,
        callee: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
        j: usize,
        offset: Option<&'tcx Expr<'tcx>>,
    ) {
        let tcx = self.a.tcx;
        let ExprKind::Path(QPath::Resolved(None, path)) = callee.kind else {
            return self.refuse();
        };
        let Res::Def(DefKind::Fn, def) = path.res else { return self.refuse() };
        let Some(local) = def.as_local() else { return self.refuse() };
        if tcx.hir_node_by_def_id(local).body_id().is_none() {
            return self.refuse();
        }
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
            let mut lin = Lin::constant(t.k);
            for (p, c) in &t.terms {
                let Some(arg) = args.get(*p) else { return self.refuse() };
                let Some(v) = self.value(arg) else { return self.refuse() };
                // A negative coefficient subtracts: exact only when the
                // argument's type is signed (an unsigned one wraps).
                if *c < 0
                    && int_info(tcx, self.typeck().expr_ty(arg)).map(|i| i.1) != Some(Sign::Signed)
                {
                    return self.refuse();
                }
                for _ in 0..c.unsigned_abs() {
                    lin = lin.plus(&v, c.signum());
                }
            }
            if let Some(o) = offset {
                let Some(o) = self.index_bound(o, call.hir_id) else { return self.refuse() };
                // `p.offset(o)` with `o < O`: elements up to `o + bound - 1`.
                lin = lin.plus(&o, 1).plus(&Lin::constant(1), -1);
            }
            terms.push(lin);
        }
        let must = inner.must && self.loops.is_empty();
        self.add(Bound { terms, must });
    }
}

/// `to` holds every value of `from` exactly.
fn value_preserving(from: (u64, Sign), to: (u64, Sign)) -> bool {
    match (from.1, to.1) {
        (Sign::Signed, Sign::Signed) | (Sign::Unsigned, Sign::Unsigned) => to.0 >= from.0,
        (Sign::Unsigned, Sign::Signed) => to.0 > from.0,
        (Sign::Signed, Sign::Unsigned) => false,
    }
}

/// Casting can only keep or DECREASE the value (as a bound, over-approximated
/// by the uncast operand): any unsigned source, or a widening signed one.
fn never_increases(from: (u64, Sign), to: (u64, Sign)) -> bool {
    match (from.1, to.1) {
        (Sign::Unsigned, _) => true,
        (Sign::Signed, Sign::Signed) => to.0 >= from.0,
        (Sign::Signed, Sign::Unsigned) => false,
    }
}

fn offset_call<'tcx>(e: &'tcx Expr<'tcx>) -> Option<(&'tcx Expr<'tcx>, &'tcx Expr<'tcx>)> {
    match e.kind {
        ExprKind::MethodCall(segment, receiver, [arg], _)
            if matches!(
                segment.ident.name.as_str(),
                "offset" | "add" | "wrapping_offset" | "wrapping_add"
            ) =>
        {
            Some((receiver, arg))
        }
        _ => None,
    }
}

impl<'tcx> Visitor<'tcx> for Walk<'_, '_, 'tcx> {
    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if self.refused {
            return;
        }
        match e.kind {
            ExprKind::Loop(block, _, source, _) => {
                self.straight = false;
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
                    self.loops.push(LoopFrame { body, conjuncts });
                    self.visit_block(body);
                    self.loops.pop();
                    return;
                }
                self.loops.push(LoopFrame {
                    body: block,
                    conjuncts: Vec::new(),
                });
                intravisit::walk_expr(self, e);
                self.loops.pop();
                return;
            }
            ExprKind::If(..)
            | ExprKind::Match(..)
            | ExprKind::Break(..)
            | ExprKind::Continue(..)
            | ExprKind::Closure(..) => self.straight = false,
            ExprKind::Binary(op, ..) if matches!(op.node, BinOpKind::And | BinOpKind::Or) => {
                self.straight = false
            }
            ExprKind::Ret(..) => {
                // A tail `return` keeps the body straight; R677-6 admits it.
                let mut parents = self.a.tcx.hir_parent_iter(e.hir_id);
                let first = parents.next().map(|(_, n)| n);
                let second = parents.next().map(|(_, n)| n);
                // `{ …; return x; }` or `{ …; return x }`, as the block's end.
                let tail = matches!(first, Some(Node::Block(b)) if b.expr.is_some_and(|x| x.hir_id == e.hir_id))
                    || matches!(second, Some(Node::Block(b))
                        if b.expr.is_none()
                            && b.stmts.last().is_some_and(|s| matches!(s.kind, StmtKind::Semi(x) if x.hir_id == e.hir_id)));
                if !tail {
                    self.straight = false;
                }
            }
            ExprKind::Unary(UnOp::Deref, inner) => {
                if self.is_target(inner) {
                    return self.access(None, e.hir_id);
                }
                if let Some((receiver, idx)) = offset_call(peel_parens(inner))
                    && self.is_target(receiver)
                {
                    self.visit_expr(idx);
                    return self.access(Some(idx), e.hir_id);
                }
            }
            ExprKind::Call(callee, args) => {
                self.visit_expr(callee);
                for (j, arg) in args.iter().enumerate() {
                    let a = peel_parens(arg);
                    if self.is_target(a) {
                        self.compose(e, callee, args, j, None);
                        continue;
                    }
                    let derived = match a.kind {
                        ExprKind::AddrOf(_, _, inner) => match peel_parens(inner).kind {
                            ExprKind::Unary(UnOp::Deref, place) => offset_call(peel_parens(place)),
                            _ => None,
                        },
                        _ => offset_call(a),
                    };
                    if let Some((receiver, idx)) = derived
                        && self.is_target(receiver)
                    {
                        self.visit_expr(idx);
                        self.compose(e, callee, args, j, Some(idx));
                        continue;
                    }
                    self.visit_expr(arg);
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
