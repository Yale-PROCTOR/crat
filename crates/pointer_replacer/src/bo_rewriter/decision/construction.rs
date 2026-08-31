//! **S3.2′-0 measurement — where a pointer subject's value comes from.**
//!
//! Two questions ride on the construction site, and both were recorded as
//! unmeasurable when the slice addendum was written:
//!
//! - **`Box<T>` vs `Box<[T]>`** — the allocation-size expression is the
//!   discriminator. `malloc(4)` behind a `*mut i32` is one element;
//!   `calloc(k, 4)` is `k`. Under user ruling U-2 condition (b) this is
//!   load-bearing rather than latent: owning fat forms take a *recovered*
//!   length or degrade, because there the length **is** the allocation
//!   parameter — approximating it changes what is allocated, not merely what
//!   is claimed.
//! - **`approx-len` incidence** — the large-length approximation applies where
//!   fatness says array, BO says safe, and no length is recoverable. Forecasting
//!   that set *before* anything is emitted is what U-2 condition (a) requires
//!   and what queue entry **A7**'s sizing depends on.
//!
//! # Measurement only
//!
//! Nothing in `decide_one` reads this. It is collected beside the decision, not
//! inside it, so adding it cannot move a single corpus number — which is the
//! property that lets it ride an ordinary sweep instead of needing its own
//! pre-registration.
//!
//! # Why the recognizer is syntactic, and what that costs
//!
//! It reads HIR initializers, so it sees what the source literally says. A
//! pointer whose length is established somewhere other than its own
//! initializer — the dominant parameter case, where the length arrives as a
//! sibling argument — is reported as **having no local construction site**,
//! not as unrecoverable. Those are different claims and the table keeps them
//! apart: the first is a statement about this analysis's scope, the second
//! would be a statement about the program.

use rustc_hash::FxHashMap;
use rustc_hir::{
    HirId,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;

/// How a pointer binding got its value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Construction {
    /// `arr.as_mut_ptr()` / `as_ptr()` — the length is the array's, statically.
    ArrayDecay,
    /// An allocator call. `count` is `Some` only for the two-argument form
    /// (`calloc`), where the element count is a separate argument and is
    /// therefore recoverable without interpreting the size expression.
    Alloc {
        callee: String,
        size: String,
        count: Option<String>,
    },
    /// Assigned from another pointer binding — the length question defers to
    /// the source, and this analysis does not chase it.
    CopyOf,
    /// A null (or integer) literal, after the `as *mut T` cast is peeled.
    NullLit,
    /// `&x` / `&mut x` — a borrow of a single place.
    AddrOf,
    /// `&arr[i]` — an interior pointer; length is the array's minus the index.
    IndexAddr,
    /// `(*s).field` or `*p` — the length lives with the source place.
    PlaceRead,
    /// A call to something that is not a known allocator — the length, if any,
    /// belongs to the callee's contract and is not visible here.
    CallResult,
    /// A `let` with an initializer the recognizer does not classify.
    Other,
}

impl Construction {
    /// The length-recoverability class, as the forecast table reports it.
    pub(crate) fn len_class(&self) -> &'static str {
        match self {
            Construction::ArrayDecay => "array-len",
            // Two-argument form: the count is its own argument.
            Construction::Alloc { count: Some(_), .. } => "alloc-count",
            Construction::Alloc { size, .. } => {
                if size.chars().all(|c| c.is_ascii_digit()) {
                    "alloc-size-literal"
                } else if size.contains("size_of") {
                    "alloc-size-sizeof"
                } else {
                    "alloc-size-dynamic"
                }
            }
            Construction::CopyOf => "copy",
            Construction::NullLit => "null-lit",
            Construction::AddrOf => "addr-of-one",
            Construction::IndexAddr => "interior-index",
            Construction::PlaceRead => "place-read",
            Construction::CallResult => "call-result",
            Construction::Other => "other",
        }
    }

    pub(crate) fn key(&self) -> &'static str {
        match self {
            Construction::ArrayDecay => "array-decay",
            Construction::Alloc { .. } => "alloc",
            Construction::CopyOf => "copy",
            Construction::NullLit => "null-lit",
            Construction::AddrOf => "addr-of",
            Construction::IndexAddr => "index-addr",
            Construction::PlaceRead => "place-read",
            Construction::CallResult => "call-result",
            Construction::Other => "other",
        }
    }
}

#[derive(Default)]
pub(crate) struct ConstructionFacts {
    pub by_binding: FxHashMap<(LocalDefId, HirId), Construction>,
    pub init_spans: FxHashMap<(LocalDefId, HirId), rustc_span::Span>,
    pub statement_spans: FxHashMap<(LocalDefId, HirId), rustc_span::Span>,
    pub first_stores: FxHashMap<(LocalDefId, HirId), Vec<FirstStore>>,
    pub deallocator_calls: FxHashMap<(LocalDefId, HirId), Vec<rustc_span::Span>>,
    pub zero_memsets: FxHashMap<(LocalDefId, HirId), Vec<ZeroMemset>>,
    pub owner_overwrites: FxHashMap<(LocalDefId, HirId), Vec<OwnerOverwrite>>,
    pub realloc_calls: FxHashMap<(LocalDefId, HirId), Vec<rustc_span::Span>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FirstStore {
    pub statement_span: rustc_span::Span,
    pub value_span: rustc_span::Span,
    pub value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ZeroMemset {
    pub statement_span: rustc_span::Span,
    pub call_span: rustc_span::Span,
    pub bytes: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OwnerOverwrite {
    pub statement_span: rustc_span::Span,
    pub value_span: rustc_span::Span,
    pub construction: Construction,
}

const ALLOCATORS: &[&str] = &[
    "malloc", "calloc", "realloc", "xmalloc", "xcalloc", "strdup",
];

pub(crate) fn collect(tcx: TyCtxt<'_>, fns: &[LocalDefId]) -> ConstructionFacts {
    let mut facts = ConstructionFacts::default();
    for &fn_did in fns {
        let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
            continue;
        };
        let mut v = Collector {
            tcx,
            fn_did,
            facts: &mut facts,
        };
        v.visit_body(tcx.hir_body(body_id));
    }
    facts
}

struct Collector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    facts: &'a mut ConstructionFacts,
}

impl Collector<'_, '_> {
    fn snippet(&self, span: rustc_span::Span) -> String {
        self.tcx
            .sess
            .source_map()
            .span_to_snippet(span)
            .unwrap_or_else(|_| "<unrenderable>".to_owned())
            // TSV is the wire here; a tab or newline inside a snippet would
            // silently shift every later column.
            .replace(['\t', '\n', '\r'], " ")
    }

    /// Strip the `as *mut T` C2Rust puts on every allocator result.
    fn peel<'h>(mut e: &'h rustc_hir::Expr<'h>) -> &'h rustc_hir::Expr<'h> {
        while let rustc_hir::ExprKind::Cast(inner, _) = &e.kind {
            e = inner;
        }
        e
    }

    fn classify(&self, init: &rustc_hir::Expr<'_>) -> Construction {
        let e = Self::peel(init);
        match &e.kind {
            rustc_hir::ExprKind::Call(callee, args) => {
                let name = match &callee.kind {
                    rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, p)) => p
                        .segments
                        .last()
                        .map(|s| s.ident.name.to_string())
                        .unwrap_or_default(),
                    _ => String::new(),
                };
                if ALLOCATORS.contains(&name.as_str()) {
                    // Keyed on the CALLEE, never on arity. `calloc(count, size)`
                    // and `realloc(ptr, size)` both take two arguments, and an
                    // arity test reads `realloc`'s POINTER as an element count —
                    // measured on the first de-risk run, where every `realloc`
                    // in libtree came back `alloc-count` with `(*v).p` as its
                    // "count".
                    let (count, size) = match (name.as_str(), args.len()) {
                        ("calloc" | "xcalloc", 2) => {
                            (Some(self.snippet(args[0].span)), self.snippet(args[1].span))
                        }
                        ("realloc", 2) => (None, self.snippet(args[1].span)),
                        _ => (
                            None,
                            args.first()
                                .map(|a| self.snippet(a.span))
                                .unwrap_or_default(),
                        ),
                    };
                    Construction::Alloc {
                        callee: name,
                        size,
                        count,
                    }
                } else {
                    Construction::CallResult
                }
            }
            rustc_hir::ExprKind::MethodCall(seg, ..) => {
                let m = seg.ident.name.to_string();
                if m == "as_mut_ptr" || m == "as_ptr" {
                    Construction::ArrayDecay
                } else {
                    Construction::Other
                }
            }
            rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, p)) => {
                if matches!(p.res, rustc_hir::def::Res::Local(_)) {
                    Construction::CopyOf
                } else {
                    Construction::Other
                }
            }
            // The shapes below were an undifferentiated `Other` on the first
            // de-risk — 106 of 205 bindings, which forecasts nothing. Split
            // because each has a *different* length story, and the whole point
            // of this table is to predict where the approximation fires.
            //
            // A null literal reaches here because `peel` strips the
            // `0 as *mut T` cast C2Rust emits.
            rustc_hir::ExprKind::Lit(_) => Construction::NullLit,
            // `&mut x` / `&x` — length 1 unless the operand is an index or a
            // whole array, which `Index` below catches separately.
            rustc_hir::ExprKind::AddrOf(..) => Construction::AddrOf,
            // `&arr[i] as *mut T` — the C idiom for interior pointers. The
            // length is the array's *minus the offset*, so it is recoverable
            // only with the index, and this records that it is an index case
            // rather than pretending it is a plain decay.
            rustc_hir::ExprKind::Index(..) => Construction::IndexAddr,
            // `(*s).field` and `*p` — the length lives with the source place,
            // which this analysis does not chase.
            rustc_hir::ExprKind::Field(..)
            | rustc_hir::ExprKind::Unary(rustc_hir::UnOp::Deref, _) => Construction::PlaceRead,
            _ => Construction::Other,
        }
    }
}

impl<'tcx> Visitor<'tcx> for Collector<'_, 'tcx> {
    fn visit_stmt(&mut self, stmt: &'tcx rustc_hir::Stmt<'tcx>) {
        if let rustc_hir::StmtKind::Let(local) = stmt.kind
            && matches!(local.pat.kind, rustc_hir::PatKind::Binding(..))
            && let Some(init) = local.init
        {
            let c = self.classify(init);
            self.facts
                .by_binding
                .insert((self.fn_did, local.pat.hir_id), c);
            self.facts
                .init_spans
                .insert((self.fn_did, local.pat.hir_id), init.span);
            self.facts
                .statement_spans
                .insert((self.fn_did, local.pat.hir_id), stmt.span);
        }
        let expression = match stmt.kind {
            rustc_hir::StmtKind::Semi(expression) | rustc_hir::StmtKind::Expr(expression) => {
                Some(expression)
            }
            _ => None,
        };
        if let Some(expression) = expression
            && let rustc_hir::ExprKind::Assign(lhs, rhs, _) = expression.kind
            && let rustc_hir::ExprKind::Unary(rustc_hir::UnOp::Deref, base) = lhs.kind
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = base.kind
            && let rustc_hir::def::Res::Local(binding) = path.res
            && matches!(Self::peel(rhs).kind, rustc_hir::ExprKind::Lit(_))
        {
            let value = self.snippet(rhs.span);
            self.facts
                .first_stores
                .entry((self.fn_did, binding))
                .or_default()
                .push(FirstStore {
                    statement_span: stmt.span,
                    value_span: rhs.span,
                    value,
                });
        }
        if let Some(expression) = expression
            && let rustc_hir::ExprKind::Assign(lhs, rhs, _) = expression.kind
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, lhs_path)) = lhs.kind
            && let rustc_hir::def::Res::Local(binding) = lhs_path.res
        {
            let construction = self.classify(rhs);
            if matches!(construction, Construction::Alloc { .. }) {
                self.facts
                    .owner_overwrites
                    .entry((self.fn_did, binding))
                    .or_default()
                    .push(OwnerOverwrite {
                        statement_span: stmt.span,
                        value_span: rhs.span,
                        construction,
                    });
            }
        }
        let memset_expression = expression.map(|expression| match expression.kind {
            rustc_hir::ExprKind::Assign(_, rhs, _) => Self::peel(rhs),
            _ => expression,
        });
        if let Some(memset_expression) = memset_expression
            && let rustc_hir::ExprKind::Call(callee, args) = memset_expression.kind
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = callee.kind
            && path
                .segments
                .last()
                .is_some_and(|segment| segment.ident.name.as_str() == "memset")
            && let [pointer, value, bytes] = args
            && self.snippet(Self::peel(value).span).trim() == "0"
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, argument_path)) =
                Self::peel(pointer).kind
            && let rustc_hir::def::Res::Local(binding) = argument_path.res
        {
            let bytes = self.snippet(bytes.span);
            self.facts
                .zero_memsets
                .entry((self.fn_did, binding))
                .or_default()
                .push(ZeroMemset {
                    statement_span: stmt.span,
                    call_span: memset_expression.span,
                    bytes,
                });
        }
        intravisit::walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expression: &'tcx rustc_hir::Expr<'tcx>) {
        if let rustc_hir::ExprKind::Call(callee, args) = expression.kind
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = callee.kind
            && path
                .segments
                .last()
                .is_some_and(|segment| matches!(segment.ident.name.as_str(), "free" | "realloc"))
            && let Some(argument) = args.first()
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, argument_path)) =
                Self::peel(argument).kind
            && let rustc_hir::def::Res::Local(binding) = argument_path.res
        {
            let callee_name = path
                .segments
                .last()
                .expect("matched callee segment")
                .ident
                .name;
            self.facts
                .deallocator_calls
                .entry((self.fn_did, binding))
                .or_default()
                .push(expression.span);
            if callee_name.as_str() == "realloc" {
                self.facts
                    .realloc_calls
                    .entry((self.fn_did, binding))
                    .or_default()
                    .push(expression.span);
            }
        }
        intravisit::walk_expr(self, expression);
    }
}
