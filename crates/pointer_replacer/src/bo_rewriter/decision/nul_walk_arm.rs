//! **wave-6l relay 077 (R776-4, STOP 2) — the NUL-walk extent.**
//!
//! A raw C string handed to a byte-pointer callee parameter that the seam
//! would build with the fallback extent takes `strlen + 1` where one of two
//! arms proves the bytes up to and including the NUL are initialized and
//! terminated at the call, and that every read the input makes through the
//! argument lies in them:
//!
//! - **(A) `contract`** — the callee (or a callee it forwards the parameter to,
//!   on every path) hands it to a string-contract position (`strlen`,
//!   `strcmp`, a `%s` of `printf`, …) on EVERY path through it, and uses it
//!   nowhere else. C requires a string there, so on a UB-free input (§28) the
//!   argument IS a terminated, initialized string at the call; the callee
//!   reads nothing past its NUL.
//! - **(B) provenance** — the BASE is a C string by construction:
//!   - `argv` — an element of `main_0`'s command-line `argv`;
//!   - `literal` — a string literal with one NUL, at its end (directly, or a
//!     local bound once to one or to a choice among them);
//!   - `strdup` — a local bound once to `strdup(..)`, null-tested before the
//!     call;
//!
//!   - `getenv` — a local bound once to `getenv(..)`, null-tested;
//!   - `sscanf` — a `%s` / `%[` destination of an `sscanf` whose return value
//!     the call is dominated by a test of, covering that conversion;
//!
//!   and the callee's reads stop at or before the NUL (the bounded test
//!   below): string reads, null tests, copies, forwards to such callees, a
//!   cursor walk R491-7 proves, or an indexed walk that steps only past a
//!   tested non-NUL byte. Even an exactly-sized allocation (`argv`, `strdup`)
//!   may have been shortened by the program, and a callee that writes
//!   through the pointer (`strcpy`'s destination) is not bounded by its NUL.
//!
//! Everything else keeps the fallback and its receipt. The receipt names the
//! arm and the provenance: `nul-walk:<arm>:<provenance>`.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    BinOpKind, Expr, ExprKind, HirId, Node, PatKind, QPath, UnOp,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::emitability::EmitabilityFacts;

/// One licensed construction: the arm and the base's provenance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Site {
    pub arm: &'static str,
    pub provenance: String,
}

impl Site {
    pub(crate) fn receipt(&self) -> String {
        format!("nul-walk:{}:{}", self.arm, self.provenance)
    }
}

/// String-reading positions of the C library: `(name, argument, terminated)`.
/// `terminated` = C requires a string there (a NUL-terminated array); the
/// counted comparisons read at most `n` and stop at the NUL, so they read
/// nothing past it, but do not require one.
const STRING_READS: &[(&str, usize, bool)] = &[
    ("strlen", 0, true),
    ("strcmp", 0, true),
    ("strcmp", 1, true),
    ("strcasecmp", 0, true),
    ("strcasecmp", 1, true),
    ("strcpy", 1, true),
    ("strcat", 1, true),
    ("strchr", 0, true),
    ("strrchr", 0, true),
    ("strstr", 0, true),
    ("strstr", 1, true),
    ("strdup", 0, true),
    ("strspn", 0, true),
    ("strspn", 1, true),
    ("strcspn", 0, true),
    ("strcspn", 1, true),
    ("strpbrk", 0, true),
    ("strpbrk", 1, true),
    ("puts", 0, true),
    ("fputs", 0, true),
    ("atoi", 0, true),
    ("atol", 0, true),
    ("atof", 0, true),
    ("strtol", 0, true),
    ("strtoul", 0, true),
    ("strtod", 0, true),
    ("fopen", 0, true),
    ("sscanf", 0, true),
    ("getenv", 0, true),
    ("strncmp", 0, false),
    ("strncmp", 1, false),
    ("strncasecmp", 0, false),
    ("strncasecmp", 1, false),
    ("strncpy", 1, false),
];

/// The `printf` family: the format's argument index.
const PRINTF_FORMAT: &[(&str, usize)] = &[
    ("printf", 0),
    ("fprintf", 1),
    ("sprintf", 1),
    ("snprintf", 2),
];

/// Every licensed `(caller, argument span)` of the program.
pub(crate) fn sites(
    tcx: TyCtxt<'_>,
    facts: &EmitabilityFacts,
) -> FxHashMap<(LocalDefId, Span), Site> {
    let mut classes = Classes::default();
    let mut out = FxHashMap::default();
    for (callee, calls) in &facts.call_args {
        if tcx.hir_node_by_def_id(*callee).body_id().is_none() {
            continue;
        }
        for call in calls {
            for arg in &call.args {
                let Some(class) = classes.of(tcx, facts, *callee, arg.index) else {
                    continue;
                };
                let Some(expr) = argument_expr(tcx, call.caller, arg.span) else {
                    continue;
                };
                if !byte_pointer(tcx.typeck(call.caller).expr_ty(expr)) {
                    continue;
                }
                let site = if class.reaches {
                    Some(Site {
                        arm: "A",
                        provenance: "contract".to_owned(),
                    })
                } else {
                    // The callee's reads must stop at or before the NUL for
                    // every provenance: an `argv` or `strdup` string the
                    // program shortened, or a callee that writes through it
                    // (`strcpy`'s destination), runs past `strlen + 1`.
                    provenance(tcx, call.caller, expr)
                        .filter(|_| class.bounded)
                        .map(|provenance| Site {
                            arm: "B",
                            provenance,
                        })
                };
                if let Some(site) = site {
                    out.insert((call.caller, arg.span), site);
                }
            }
        }
    }
    out
}

fn byte_pointer(ty: rustc_middle::ty::Ty<'_>) -> bool {
    let (TyKind::RawPtr(pointee, _) | TyKind::Ref(_, pointee, _)) = ty.kind() else {
        return false;
    };
    matches!(
        pointee.kind(),
        TyKind::Int(rustc_middle::ty::IntTy::I8) | TyKind::Uint(rustc_middle::ty::UintTy::U8)
    )
}

fn peel<'a, 'tcx>(mut e: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) = e.kind {
        e = inner;
    }
    e
}

fn local_of(e: &Expr<'_>) -> Option<HirId> {
    match peel(e).kind {
        ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

/// The name a call's callee spells, when it is a plain path.
fn callee_name(callee: &Expr<'_>) -> Option<String> {
    match callee.kind {
        ExprKind::Path(QPath::Resolved(_, path)) => {
            path.segments.last().map(|s| s.ident.name.to_string())
        }
        _ => None,
    }
}

/// The local `fn` a call's callee names, when it has a body.
fn local_callee(tcx: TyCtxt<'_>, callee: &Expr<'_>) -> Option<LocalDefId> {
    let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind else {
        return None;
    };
    let Res::Def(DefKind::Fn, def) = path.res else {
        return None;
    };
    let local = def.as_local()?;
    tcx.hir_node_by_def_id(local).body_id().map(|_| local)
}

/// The argument expression at `span` in `caller`'s body.
fn argument_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    span: Span,
) -> Option<&'tcx Expr<'tcx>> {
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
    find.found
}

// ---- the callee: bounded / reaches ----

#[derive(Clone, Copy, Debug, Default)]
struct Class {
    /// Every read through the parameter stops at or before its NUL.
    bounded: bool,
    /// ...and a string-contract position reads it on every path.
    reaches: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Index {
    Zero,
    Literal,
    Local(HirId),
    Other,
}

#[derive(Default)]
struct Classes {
    done: FxHashMap<(LocalDefId, usize), Class>,
    open: FxHashSet<(LocalDefId, usize)>,
}

enum Use {
    /// A string-contract or counted string read; `terminated` = C requires a
    /// string there; `every` = it runs on every path through the callee.
    Read { terminated: bool, every: bool },
    /// Handed to a local callee's parameter.
    Forward {
        callee: LocalDefId,
        index: usize,
        every: bool,
    },
    /// A null test, or a copy into a local of the set.
    Neutral,
    /// `*p` / `*p.offset(index)` (`write` = the target of an assignment).
    Deref { index: Index, write: bool },
    /// `p = p.offset(literal)`: a cursor step.
    Step,
    /// Anything else: not provably bounded.
    Other,
}

impl Classes {
    fn of(
        &mut self,
        tcx: TyCtxt<'_>,
        facts: &EmitabilityFacts,
        callee: LocalDefId,
        index: usize,
    ) -> Option<Class> {
        let key = (callee, index);
        if let Some(class) = self.done.get(&key) {
            return Some(*class);
        }
        if !self.open.insert(key) {
            // A cycle (`snocString` forwards to itself): it adds no read.
            return Some(Class {
                bounded: true,
                reaches: false,
            });
        }
        let class = self.compute(tcx, facts, callee, index);
        self.open.remove(&key);
        if let Some(class) = class {
            self.done.insert(key, class);
        }
        class
    }

    fn compute(
        &mut self,
        tcx: TyCtxt<'_>,
        facts: &EmitabilityFacts,
        callee: LocalDefId,
        index: usize,
    ) -> Option<Class> {
        let body = tcx.hir_body_owned_by(callee);
        let param = body.params.get(index)?;
        let PatKind::Binding(_, binding, _, None) = param.pat.kind else {
            return None;
        };
        if !byte_pointer(tcx.typeck(callee).pat_ty(param.pat)) {
            return None;
        }
        // The parameter and its copies (`let q = p`, under casts).
        let mut set: FxHashSet<HirId> = FxHashSet::default();
        set.insert(binding);
        let copies = super::thin_extent::copy_edges_in(tcx, callee);
        loop {
            let before = set.len();
            for (copy, source) in &copies {
                if set.contains(source) {
                    set.insert(*copy);
                }
            }
            if set.len() == before {
                break;
            }
        }
        let uses = uses(tcx, callee, &set);
        // R491-7's cursor walk (`while *p != 0 { p = p.offset(1) }`) proves
        // its byte-at-a-time reads stop at the NUL; asked only when needed.
        let cursor = || {
            let subject = super::Subject {
                fn_did: callee,
                local: rustc_middle::mir::Local::from_usize(index + 1),
                hir_id: binding,
                param_name: None,
                kind: super::SubjectKind::Param { hir_index: index },
                ptr_depth: 1,
                label: String::new(),
                ty_span: None,
                binding_span: param.pat.span,
                pointee_span: None,
                decl_shape: super::DeclShape::RawPtr,
                mutable: false,
                freed_at: None,
                len_recovered: false,
                null_init: false,
                mut_binding: false,
                ctor: None,
            };
            super::local_callee_extent::nul_walk(tcx, &subject, facts).is_some()
        };
        let mut class = Class {
            bounded: true,
            reaches: false,
        };
        let mut walk_indexes: FxHashSet<HirId> = FxHashSet::default();
        let mut cursor_uses = false;
        for u in uses {
            match u {
                Use::Deref { write: true, .. } => class.bounded = false,
                Use::Deref {
                    index: Index::Zero, ..
                } => {}
                Use::Deref {
                    index: Index::Local(i),
                    ..
                } => {
                    walk_indexes.insert(i);
                }
                Use::Deref {
                    index: Index::Literal,
                    ..
                }
                | Use::Step => cursor_uses = true,
                Use::Deref {
                    index: Index::Other,
                    ..
                } => class.bounded = false,
                Use::Read { terminated, every } => class.reaches |= terminated && every,
                Use::Forward {
                    callee: next,
                    index: at,
                    every,
                } => match self.of(tcx, facts, next, at) {
                    Some(inner) => {
                        class.bounded &= inner.bounded;
                        class.reaches |= every && inner.reaches;
                    }
                    None => class.bounded = false,
                },
                Use::Neutral => {}
                Use::Other => class.bounded = false,
            }
        }
        if class.bounded && cursor_uses && !cursor() {
            class.bounded = false;
        }
        if class.bounded
            && !walk_indexes
                .iter()
                .all(|i| indexed_walk(tcx, callee, &set, *i))
        {
            class.bounded = false;
        }
        class.reaches &= class.bounded;
        Some(class)
    }
}

/// Every use of a local of `set` in `callee`'s body, classified.
fn uses(tcx: TyCtxt<'_>, callee: LocalDefId, set: &FxHashSet<HirId>) -> Vec<Use> {
    struct Paths<'a> {
        set: &'a FxHashSet<HirId>,
        found: Vec<HirId>,
    }
    impl<'tcx> Visitor<'tcx> for Paths<'_> {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = e.kind
                && let Res::Local(id) = path.res
                && self.set.contains(&id)
            {
                self.found.push(e.hir_id);
            }
            intravisit::walk_expr(self, e);
        }
    }
    let body = tcx.hir_body_owned_by(callee);
    let mut paths = Paths {
        set,
        found: Vec::new(),
    };
    paths.visit_body(body);
    paths
        .found
        .into_iter()
        .map(|id| classify(tcx, callee, set, id))
        .collect()
}

fn classify(tcx: TyCtxt<'_>, callee: LocalDefId, set: &FxHashSet<HirId>, at: HirId) -> Use {
    // Up through the casts the C spelling puts around the pointer.
    let mut child = at;
    let mut parent = tcx.parent_hir_node(child);
    while let Node::Expr(Expr {
        kind: ExprKind::Cast(..) | ExprKind::DropTemps(..),
        hir_id,
        ..
    }) = parent
    {
        child = *hir_id;
        parent = tcx.parent_hir_node(child);
    }
    match parent {
        // `*p`: element 0.
        Node::Expr(
            e @ Expr {
                kind: ExprKind::Unary(UnOp::Deref, _),
                ..
            },
        ) => Use::Deref {
            index: Index::Zero,
            write: assigned(tcx, e.hir_id),
        },
        // `*p.offset(i)`, or the cursor step `p = p.offset(1)`.
        Node::Expr(
            e @ Expr {
                kind: ExprKind::MethodCall(segment, receiver, [step], _),
                ..
            },
        ) if receiver.hir_id == child
            && matches!(segment.ident.name.as_str(), "offset" | "add") =>
        {
            let index = match peel(step).kind {
                ExprKind::Lit(lit) => match lit.node {
                    rustc_ast::LitKind::Int(v, _) if v.get() == 0 => Index::Zero,
                    rustc_ast::LitKind::Int(..) => Index::Literal,
                    _ => Index::Other,
                },
                _ => local_of(step).map_or(Index::Other, Index::Local),
            };
            match tcx.parent_hir_node(e.hir_id) {
                Node::Expr(
                    d @ Expr {
                        kind: ExprKind::Unary(UnOp::Deref, _),
                        ..
                    },
                ) => Use::Deref {
                    index,
                    write: assigned(tcx, d.hir_id),
                },
                Node::Expr(Expr {
                    kind: ExprKind::Assign(left, right, _),
                    ..
                }) if right.hir_id == e.hir_id
                    && index == Index::Literal
                    && local_of(left).is_some_and(|l| set.contains(&l)) =>
                {
                    Use::Step
                }
                _ => Use::Other,
            }
        }
        Node::Expr(e) => match e.kind {
            ExprKind::Call(function, args) => {
                let Some(position) = args.iter().position(|a| a.hir_id == child) else {
                    return Use::Other;
                };
                let every = every_path(tcx, callee, e.hir_id);
                if let Some(next) = local_callee(tcx, function) {
                    return Use::Forward {
                        callee: next,
                        index: position,
                        every,
                    };
                }
                let Some(name) = callee_name(function) else {
                    return Use::Other;
                };
                if let Some((_, _, terminated)) = STRING_READS
                    .iter()
                    .find(|(n, i, _)| *n == name.as_str() && *i == position)
                {
                    return Use::Read {
                        terminated: *terminated,
                        every,
                    };
                }
                if let Some((_, format_at)) =
                    PRINTF_FORMAT.iter().find(|(n, _)| *n == name.as_str())
                    && position > *format_at
                    && let Some(format) = args.get(*format_at).and_then(|f| byte_string(f))
                    && plain_s_conversion(&format, position - *format_at - 1)
                {
                    return Use::Read {
                        terminated: true,
                        every,
                    };
                }
                Use::Other
            }
            ExprKind::MethodCall(segment, receiver, [], _)
                if receiver.hir_id == child && segment.ident.name.as_str() == "is_null" =>
            {
                Use::Neutral
            }
            // A copy into the set (`q = p`): its uses are the set's.
            ExprKind::Assign(left, right, _)
                if right.hir_id == child && local_of(left).is_some_and(|l| set.contains(&l)) =>
            {
                Use::Neutral
            }
            _ => Use::Other,
        },
        Node::LetStmt(local)
            if local.init.is_some_and(|i| i.hir_id == child)
                && matches!(local.pat.kind, PatKind::Binding(_, id, _, None) if set.contains(&id)) =>
        {
            Use::Neutral
        }
        _ => Use::Other,
    }
}

/// Is the place at `place` written (`*p = ..`, `*p += ..`) or borrowed?
fn assigned(tcx: TyCtxt<'_>, place: HirId) -> bool {
    match tcx.parent_hir_node(place) {
        Node::Expr(Expr {
            kind: ExprKind::Assign(left, _, _) | ExprKind::AssignOp(_, left, _),
            ..
        }) => left.hir_id == place,
        Node::Expr(Expr {
            kind: ExprKind::AddrOf(..),
            ..
        }) => true,
        _ => false,
    }
}

/// **An indexed walk to the NUL** (brotli `ParseInt`): `i` starts at `0`, is
/// changed only by `i += 1`, and every `i += 1` is preceded in its block by a
/// statement that leaves when `s[i]` is the NUL (`if *s.offset(i) == 0 {
/// break }`, or through `let c = *s.offset(i)`). Every read `s[i]` is then at
/// or before the NUL: either the loop stopped on it, or every byte before it
/// was not one.
fn indexed_walk(tcx: TyCtxt<'_>, function: LocalDefId, set: &FxHashSet<HirId>, i: HirId) -> bool {
    struct Defs<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        set: &'a FxHashSet<HirId>,
        i: HirId,
        ok: bool,
        increments: usize,
    }
    fn zero(e: &Expr<'_>) -> bool {
        matches!(peel(e).kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(v, _) if v.get() == 0))
    }
    fn one(e: &Expr<'_>) -> bool {
        matches!(peel(e).kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(v, _) if v.get() == 1))
    }
    impl<'tcx> Visitor<'tcx> for Defs<'_, 'tcx> {
        fn visit_local(&mut self, l: &'tcx rustc_hir::LetStmt<'tcx>) {
            if let PatKind::Binding(_, id, _, None) = l.pat.kind
                && id == self.i
                && !l.init.is_some_and(zero)
            {
                self.ok = false;
            }
            intravisit::walk_local(self, l);
        }

        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            match e.kind {
                ExprKind::Assign(left, right, _) if local_of(left) == Some(self.i) => {
                    if !zero(right) {
                        self.ok = false;
                    }
                }
                ExprKind::AssignOp(op, left, right) if local_of(left) == Some(self.i) => {
                    if op.node != rustc_hir::AssignOpKind::AddAssign
                        || !one(right)
                        || !tested_before(self.tcx, self.set, self.i, e.hir_id)
                    {
                        self.ok = false;
                    }
                    self.increments += 1;
                }
                ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, inner)
                    if local_of(inner) == Some(self.i) =>
                {
                    self.ok = false;
                }
                _ => {}
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut defs = Defs {
        tcx,
        set,
        i,
        ok: true,
        increments: 0,
    };
    defs.visit_body(tcx.hir_body_owned_by(function));
    defs.ok
}

/// The statement holding `increment` is preceded, in its block, by `if R == 0
/// { break | return .. }` where `R` reads `s[i]`.
fn tested_before(tcx: TyCtxt<'_>, set: &FxHashSet<HirId>, i: HirId, increment: HirId) -> bool {
    let mut child = increment;
    for (_, node) in tcx.hir_parent_iter(increment) {
        if let Node::Block(block) = node {
            for stmt in block.stmts {
                let holds = stmt.hir_id == child
                    || matches!(stmt.kind, rustc_hir::StmtKind::Expr(e) | rustc_hir::StmtKind::Semi(e) if e.hir_id == child);
                if holds {
                    return false;
                }
                if let rustc_hir::StmtKind::Expr(e) | rustc_hir::StmtKind::Semi(e) = stmt.kind
                    && let ExprKind::If(condition, then, None) = e.kind
                    && leaves(then)
                    && let ExprKind::Binary(op, left, right) = peel(condition).kind
                    && op.node == BinOpKind::Eq
                    && ((reads_s_at_i(tcx, set, i, left) && is_zero_lit(right))
                        || (reads_s_at_i(tcx, set, i, right) && is_zero_lit(left)))
                {
                    return true;
                }
            }
            return false;
        }
        if let Node::Stmt(stmt) = node {
            child = stmt.hir_id;
        }
    }
    false
}

fn is_zero_lit(e: &Expr<'_>) -> bool {
    match peel(e).kind {
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(v, _) => v.get() == 0,
            rustc_ast::LitKind::Char(c) => c == '\0',
            _ => false,
        },
        _ => false,
    }
}

fn leaves(e: &Expr<'_>) -> bool {
    match e.kind {
        ExprKind::Ret(_) | ExprKind::Break(..) => true,
        ExprKind::Block(block, _) => {
            block.expr.is_some_and(leaves)
                || block.stmts.last().is_some_and(|s| {
                    matches!(s.kind, rustc_hir::StmtKind::Expr(e) | rustc_hir::StmtKind::Semi(e) if leaves(e))
                })
        }
        _ => false,
    }
}

/// `*s.offset(i)`, or a local bound once to it (`let c = *s.offset(i)`).
fn reads_s_at_i(tcx: TyCtxt<'_>, set: &FxHashSet<HirId>, i: HirId, e: &Expr<'_>) -> bool {
    let e = peel(e);
    if let ExprKind::Unary(UnOp::Deref, inner) = e.kind
        && let ExprKind::MethodCall(segment, receiver, [step], _) = peel(inner).kind
        && matches!(segment.ident.name.as_str(), "offset" | "add")
        && local_of(receiver).is_some_and(|r| set.contains(&r))
        && local_of(step) == Some(i)
    {
        return true;
    }
    let Some(local) = local_of(e) else {
        return false;
    };
    let owner = tcx.hir_get_parent_item(local);
    single_definition(tcx, owner.def_id, local).is_some_and(|init| {
        !matches!(peel(init).kind, ExprKind::Path(..)) && reads_s_at_i(tcx, set, i, init)
    })
}

/// The bytes of a `b"..."` literal under casts.
fn byte_string(e: &Expr<'_>) -> Option<Vec<u8>> {
    match peel(e).kind {
        ExprKind::Lit(lit) => match &lit.node {
            rustc_ast::LitKind::ByteStr(bytes, _) => Some(bytes.to_vec()),
            _ => None,
        },
        _ => None,
    }
}

/// Is the `n`-th conversion of `format` a `%s` with no precision (a string
/// read to its NUL)? Any `*` width or precision consumes an argument, which
/// this does not model: refused.
fn plain_s_conversion(format: &[u8], n: usize) -> bool {
    let mut i = 0;
    let mut seen = 0;
    while i < format.len() {
        if format[i] != b'%' {
            i += 1;
            continue;
        }
        i += 1;
        if format.get(i) == Some(&b'%') {
            i += 1;
            continue;
        }
        let start = i;
        while i < format.len() && b"-+ #0123456789.lhzjtLq*".contains(&format[i]) {
            i += 1;
        }
        let spec = &format[start..i];
        let Some(&conversion) = format.get(i) else {
            return false;
        };
        i += 1;
        if spec.contains(&b'*') {
            return false;
        }
        if seen == n {
            return conversion == b's' && !spec.contains(&b'.');
        }
        seen += 1;
    }
    false
}

/// Does `at` run on every path through `function`'s body: no enclosing branch
/// arm, loop body, closure or short-circuit operand, and no `return`, `break`
/// or `continue` in a statement before it?
fn every_path(tcx: TyCtxt<'_>, function: LocalDefId, at: HirId) -> bool {
    let body_value = tcx.hir_body_owned_by(function).value.hir_id;
    let mut child = at;
    for (id, node) in tcx.hir_parent_iter(at) {
        match node {
            Node::Expr(e) => match e.kind {
                ExprKind::If(condition, _, _) if condition.hir_id != child => return false,
                ExprKind::Match(scrutinee, _, _) if scrutinee.hir_id != child => return false,
                ExprKind::Binary(op, left, _)
                    if matches!(op.node, BinOpKind::And | BinOpKind::Or)
                        && left.hir_id != child =>
                {
                    return false;
                }
                ExprKind::Loop(..) | ExprKind::Closure(..) => return false,
                ExprKind::Block(block, _) => {
                    if !preceding_exit_free(block, child) {
                        return false;
                    }
                }
                _ => {}
            },
            Node::Block(block) => {
                if !preceding_exit_free(block, child) {
                    return false;
                }
            }
            Node::Stmt(_) | Node::LetStmt(_) => {}
            _ => return id == body_value || matches!(node, Node::Item(_) | Node::ImplItem(_)),
        }
        if id == body_value {
            return true;
        }
        child = id;
    }
    false
}

/// No statement of `block` before the one holding `child` can leave it.
fn preceding_exit_free(block: &rustc_hir::Block<'_>, child: HirId) -> bool {
    struct Exits(bool);
    impl<'tcx> Visitor<'tcx> for Exits {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if matches!(
                e.kind,
                ExprKind::Ret(_) | ExprKind::Break(..) | ExprKind::Continue(_)
            ) {
                self.0 = true;
            }
            intravisit::walk_expr(self, e);
        }
    }
    for stmt in block.stmts {
        if stmt.hir_id == child
            || matches!(stmt.kind, rustc_hir::StmtKind::Expr(e) | rustc_hir::StmtKind::Semi(e) if e.hir_id == child)
            || matches!(stmt.kind, rustc_hir::StmtKind::Let(l) if l.hir_id == child)
        {
            return true;
        }
        let mut exits = Exits(false);
        exits.visit_stmt(stmt);
        if exits.0 {
            return false;
        }
    }
    true
}

// ---- the base: provenance ----

fn provenance(tcx: TyCtxt<'_>, caller: LocalDefId, arg: &Expr<'_>) -> Option<String> {
    let e = peel(arg);
    if let Some(p) = direct(tcx, caller, e) {
        return Some(p.to_owned());
    }
    let local = local_of(e)?;
    let init = single_definition(tcx, caller, local)?;
    if let Some(p) = direct(tcx, caller, peel(init)) {
        return Some(p.to_owned());
    }
    if let ExprKind::Call(function, _) = peel(init).kind
        && let Some(name) = callee_name(function)
        && matches!(name.as_str(), "strdup" | "getenv")
        && null_tested_before(tcx, local, arg.hir_id)
    {
        return Some(name);
    }
    sscanf_checked(tcx, caller, local, arg.hir_id).map(|test| format!("sscanf({test})"))
}

/// `*argv.offset(k)` of `main_0`'s `argv`, or a string literal (or a choice
/// among literals).
fn direct(tcx: TyCtxt<'_>, caller: LocalDefId, e: &Expr<'_>) -> Option<&'static str> {
    if literal_like(e) {
        return Some("literal");
    }
    let ExprKind::Unary(UnOp::Deref, inner) = e.kind else {
        return None;
    };
    let ExprKind::MethodCall(segment, receiver, [_], _) = peel(inner).kind else {
        return None;
    };
    if !matches!(segment.ident.name.as_str(), "offset" | "add") {
        return None;
    }
    let argv = local_of(receiver)?;
    (tcx.item_name(caller.to_def_id()).as_str() == "main_0"
        && tcx
            .hir_body_owned_by(caller)
            .params
            .get(1)
            .is_some_and(|p| p.pat.hir_id == argv))
    .then_some("argv")
}

/// A byte-string literal with exactly one NUL, at its end; or an `if` /
/// `match` / block whose every arm is one.
fn literal_like(e: &Expr<'_>) -> bool {
    let e = peel(e);
    match e.kind {
        ExprKind::Lit(_) => byte_string(e).is_some_and(|bytes| {
            bytes.last() == Some(&0) && bytes.iter().filter(|b| **b == 0).count() == 1
        }),
        ExprKind::If(_, then, Some(otherwise)) => literal_like(then) && literal_like(otherwise),
        ExprKind::Block(block, _) => block.stmts.is_empty() && block.expr.is_some_and(literal_like),
        ExprKind::Match(_, arms, _) => {
            !arms.is_empty() && arms.iter().all(|arm| literal_like(arm.body))
        }
        _ => false,
    }
}

/// The one definition of a local never assigned, never borrowed mutably:
/// its `let` initializer.
fn single_definition<'tcx>(
    tcx: TyCtxt<'tcx>,
    function: LocalDefId,
    local: HirId,
) -> Option<&'tcx Expr<'tcx>> {
    struct Defs<'tcx> {
        local: HirId,
        init: Option<&'tcx Expr<'tcx>>,
        other: bool,
    }
    impl<'tcx> Visitor<'tcx> for Defs<'tcx> {
        fn visit_local(&mut self, l: &'tcx rustc_hir::LetStmt<'tcx>) {
            if let PatKind::Binding(_, id, _, None) = l.pat.kind
                && id == self.local
            {
                self.init = l.init;
            }
            intravisit::walk_local(self, l);
        }

        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            match e.kind {
                ExprKind::Assign(left, _, _) | ExprKind::AssignOp(_, left, _)
                    if local_of(left) == Some(self.local) =>
                {
                    self.other = true;
                }
                ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, inner)
                    if local_of(inner) == Some(self.local) =>
                {
                    self.other = true;
                }
                _ => {}
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut defs = Defs {
        local,
        init: None,
        other: false,
    };
    defs.visit_body(tcx.hir_body_owned_by(function));
    if defs.other { None } else { defs.init }
}

fn is_null_test_of(e: &Expr<'_>, local: HirId) -> bool {
    matches!(peel(e).kind, ExprKind::MethodCall(segment, receiver, [], _)
        if segment.ident.name.as_str() == "is_null" && local_of(receiver) == Some(local))
}

/// The call is reached only where `local` is not null: inside the `then` of
/// `if !local.is_null()`, the `else` of `if local.is_null()`, or after an
/// `if local.is_null() { return .. }` in an enclosing block.
fn null_tested_before(tcx: TyCtxt<'_>, local: HirId, at: HirId) -> bool {
    let mut child = at;
    for (id, node) in tcx.hir_parent_iter(at) {
        match node {
            Node::Expr(Expr {
                kind: ExprKind::If(condition, then, otherwise),
                ..
            }) => {
                if then.hir_id == child
                    && let ExprKind::Unary(UnOp::Not, inner) = peel(condition).kind
                    && is_null_test_of(inner, local)
                {
                    return true;
                }
                if otherwise.is_some_and(|o| o.hir_id == child) && is_null_test_of(condition, local)
                {
                    return true;
                }
            }
            Node::Block(block) => {
                for stmt in block.stmts {
                    if stmt.hir_id == child {
                        break;
                    }
                    if let rustc_hir::StmtKind::Expr(e) | rustc_hir::StmtKind::Semi(e) = stmt.kind
                        && let ExprKind::If(condition, then, None) = e.kind
                        && is_null_test_of(condition, local)
                        && diverges(then)
                    {
                        return true;
                    }
                }
            }
            _ => {}
        }
        child = id;
    }
    false
}

fn diverges(e: &Expr<'_>) -> bool {
    match e.kind {
        ExprKind::Ret(_) => true,
        ExprKind::Block(block, _) => {
            block.expr.is_some_and(diverges)
                || block.stmts.last().is_some_and(|s| {
                    matches!(s.kind, rustc_hir::StmtKind::Expr(e) | rustc_hir::StmtKind::Semi(e) if diverges(e))
                })
        }
        _ => false,
    }
}

/// `local` is a `%s` / `%[` destination of an `sscanf` whose return value the
/// call is dominated by a test of (`== k`, `>= k`, `> k-1` with `k` covering
/// that conversion): the test's spelling, for the receipt.
fn sscanf_checked(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    local: HirId,
    at: HirId,
) -> Option<String> {
    let mut child = at;
    for (id, node) in tcx.hir_parent_iter(at) {
        if let Node::Expr(Expr {
            kind: ExprKind::If(condition, then, _),
            ..
        }) = node
            && then.hir_id == child
            && let ExprKind::Binary(op, left, right) = peel(condition).kind
            && let ExprKind::Call(function_expr, args) = peel(left).kind
            && callee_name(function_expr).as_deref() == Some("sscanf")
            && let Some(k) = int_literal(right)
            && let Some(format) = args.get(1).and_then(|f| byte_string(f))
            && let Some(position) = args.iter().skip(2).position(|a| local_of(a) == Some(local))
            && string_conversion(&format, position)
        {
            let needed = position as u128 + 1;
            let covers = match op.node {
                BinOpKind::Eq | BinOpKind::Ge => k >= needed,
                BinOpKind::Gt => k + 1 >= needed,
                _ => false,
            };
            if covers {
                let op = match op.node {
                    BinOpKind::Eq => "==",
                    BinOpKind::Ge => ">=",
                    _ => ">",
                };
                return Some(format!("{op}{k}"));
            }
        }
        child = id;
    }
    let _ = function;
    None
}

fn int_literal(e: &Expr<'_>) -> Option<u128> {
    match peel(e).kind {
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(value, _) => Some(value.get()),
            _ => None,
        },
        _ => None,
    }
}

/// Is the `n`-th conversion of a scanf `format` a `%s` or `%[` (which writes a
/// terminated string)? Suppressed (`%*`) conversions take no argument.
fn string_conversion(format: &[u8], n: usize) -> bool {
    let mut i = 0;
    let mut seen = 0;
    while i < format.len() {
        if format[i] != b'%' {
            i += 1;
            continue;
        }
        i += 1;
        if format.get(i) == Some(&b'%') {
            i += 1;
            continue;
        }
        let suppressed = format.get(i) == Some(&b'*');
        while i < format.len() && b"*0123456789lhzjtLqm".contains(&format[i]) {
            i += 1;
        }
        let Some(&conversion) = format.get(i) else {
            return false;
        };
        if conversion == b'[' {
            // Skip the set: `[]...]` / `[^]...]` keep a leading `]`.
            i += 1;
            if format.get(i) == Some(&b'^') {
                i += 1;
            }
            if format.get(i) == Some(&b']') {
                i += 1;
            }
            while i < format.len() && format[i] != b']' {
                i += 1;
            }
        }
        i += 1;
        if suppressed {
            continue;
        }
        if seen == n {
            return matches!(conversion, b's' | b'[');
        }
        seen += 1;
    }
    false
}
