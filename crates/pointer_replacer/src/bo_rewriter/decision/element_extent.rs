//! **R674-9 — the extent a local callee's own accesses prove.**
//!
//! C2Rust spells `&a[k]` as `&*a.offset(k)`. To the seam's `(Slice, Ref)` glue
//! that argument is one element, and R622-1 refuses it into a formal the callee
//! reads past element 0 (lodepng's `lodepng_read32bitInt(&*in_0.offset(16))`,
//! which at batch 51 rendered `from_ref` and panicked on `buffer[1]`). The
//! address is of an element of the raw pointer under the `&*`, so the raw-caller
//! arm can take that pointer instead, with an extent it can prove.
//!
//! [`constant_access_extent`] is one such proof, read from the callee's body:
//! the parameter is only ever dereferenced at element `c` for literal `c`
//! (`*p`, `*p.offset(c)`, `*p.add(c)`), and the body has no branch, loop or
//! early return, so every access runs on every call. On a UB-free input (§28)
//! the caller's pointer then covers elements `0..=max c`, and a slice of
//! `max c + 1` elements is exactly what the callee reads. Any other use of the
//! parameter (passed on, stored, cast, offset by a non-literal, reassigned)
//! gives no extent.

use rustc_hir::{
    BinOpKind, Expr, ExprKind, HirId, PatKind, QPath, StmtKind, UnOp,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;

/// The number of elements of parameter `index` that `callee`'s body reads or
/// writes on every call, when its accesses are all at literal offsets.
pub(crate) fn constant_access_extent(
    tcx: TyCtxt<'_>,
    callee: LocalDefId,
    index: usize,
) -> Option<u64> {
    let body = tcx.hir_maybe_body_owned_by(callee)?;
    let PatKind::Binding(_, parameter, _, _) = body.params.get(index)?.pat.kind else {
        return None;
    };
    let mut accesses = Accesses {
        parameter,
        max: None,
        refused: false,
    };
    // A `return` is admitted only as the body's last statement or its tail:
    // anything after an earlier one would not run on every call.
    match body.value.kind {
        ExprKind::Block(block, _) => {
            let last = block.stmts.len().checked_sub(1);
            for (at, statement) in block.stmts.iter().enumerate() {
                match statement.kind {
                    StmtKind::Semi(Expr {
                        kind: ExprKind::Ret(Some(value)),
                        ..
                    }) if Some(at) == last && block.expr.is_none() => accesses.visit_expr(value),
                    _ => accesses.visit_stmt(statement),
                }
            }
            match block.expr {
                Some(Expr {
                    kind: ExprKind::Ret(Some(value)),
                    ..
                }) => accesses.visit_expr(value),
                Some(tail) => accesses.visit_expr(tail),
                None => {}
            }
        }
        _ => accesses.visit_expr(body.value),
    }
    if accesses.refused {
        return None;
    }
    accesses.max.map(|max| max + 1)
}

struct Accesses {
    parameter: HirId,
    max: Option<u64>,
    refused: bool,
}

impl Accesses {
    fn is_parameter(&self, e: &Expr<'_>) -> bool {
        matches!(
            e.kind,
            ExprKind::Path(QPath::Resolved(None, path)) if path.res == Res::Local(self.parameter)
        )
    }
}

/// A non-negative integer literal under casts (`3 as libc::c_int as isize`).
fn literal(mut e: &Expr<'_>) -> Option<u64> {
    while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) = e.kind {
        e = inner;
    }
    match e.kind {
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(value, _) => u64::try_from(value.get()).ok(),
            _ => None,
        },
        _ => None,
    }
}

impl<'tcx> Visitor<'tcx> for Accesses {
    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if self.refused {
            return;
        }
        match e.kind {
            // Control flow: an access under it may not run on every call.
            ExprKind::If(..)
            | ExprKind::Match(..)
            | ExprKind::Loop(..)
            | ExprKind::Closure(..)
            | ExprKind::Break(..)
            | ExprKind::Continue(..)
            | ExprKind::Ret(..)
            | ExprKind::Let(..)
            | ExprKind::Yield(..) => {
                self.refused = true;
                return;
            }
            ExprKind::Binary(op, ..) if matches!(op.node, BinOpKind::And | BinOpKind::Or) => {
                self.refused = true;
                return;
            }
            ExprKind::Unary(UnOp::Deref, place) => {
                if self.is_parameter(place) {
                    self.max = self.max.max(Some(0));
                    return;
                }
                if let ExprKind::MethodCall(segment, receiver, [offset], _) = place.kind
                    && matches!(
                        segment.ident.name.as_str(),
                        "offset" | "add" | "wrapping_offset" | "wrapping_add"
                    )
                    && self.is_parameter(receiver)
                {
                    match literal(offset) {
                        Some(at) => self.max = self.max.max(Some(at)),
                        None => self.refused = true,
                    }
                    return;
                }
            }
            // Any other use of the parameter: passed on, stored, cast,
            // compared, reassigned.
            _ if self.is_parameter(e) => {
                self.refused = true;
                return;
            }
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }
}
