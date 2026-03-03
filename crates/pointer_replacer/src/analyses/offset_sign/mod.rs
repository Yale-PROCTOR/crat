use std::collections::VecDeque;

/// Pointer-offset sign analysis.
///
/// Determines, for each pointer-typed local variable in each function, whether
/// any `.offset()` call on that pointer uses a potentially-negative argument.
///
/// - `needs_cursor() == false` → the pointer is only ever offset by non-negative
///   values; a plain `Slice`/`SliceRef` is sufficient.
/// - `needs_cursor() == true`  → the pointer may be offset negatively; a
///   `SliceCursor`/`SliceCursorRef` is required.
use rustc_ast::LitKind;
use rustc_hash::FxHashMap;
use rustc_hir::{
    self as hir, AssignOpKind, BinOpKind, ExprKind, HirId, QPath, UnOp,
    def::Res,
    intravisit::{Visitor, walk_expr},
};
use rustc_middle::ty;
use rustc_span::def_id::LocalDefId;

use crate::utils::rustc::RustProgram;

/// 7-element sign lattice:
///
///               ⊤
///            /  |  \
///         NonNeg | NonPos
///          / \   |   / \
///        Pos  Zero  Neg
///               |
///               ⊥
/// - Slice:              `{ Bottom, Zero, Pos, NonNeg }`
/// - SliceCursor: `{ Neg, NonPos, Top }`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sign {
    Bottom, // ⊥ — no information yet
    Neg,    // definitely < 0
    NonPos, // definitely ≤ 0
    Zero,   // definitely = 0
    NonNeg, // definitely ≥ 0
    Pos,    // definitely > 0
    Top,    // unknown / may be anything
}

impl Sign {
    pub fn join(self, other: Sign) -> Sign {
        use Sign::*;
        match (self, other) {
            (x, Bottom) | (Bottom, x) => x,
            (_, Top) | (Top, _) => Top,
            (x, y) if x == y => x,
            (Neg, NonPos) | (NonPos, Neg) => NonPos,
            (Neg, Zero) | (Zero, Neg) => NonPos,
            (Neg, NonNeg) | (NonNeg, Neg) => Top,
            (Neg, Pos) | (Pos, Neg) => Top,
            (NonPos, Zero) | (Zero, NonPos) => NonPos,
            (NonPos, NonNeg) | (NonNeg, NonPos) => Top,
            (NonPos, Pos) | (Pos, NonPos) => Top,
            (Zero, NonNeg) | (NonNeg, Zero) => NonNeg,
            (Zero, Pos) | (Pos, Zero) => NonNeg,
            (NonNeg, Pos) | (Pos, NonNeg) => NonNeg,
            _ => Top,
        }
    }

    pub fn negate(self) -> Sign {
        match self {
            Sign::Bottom => Sign::Bottom,
            Sign::Neg => Sign::Pos,
            Sign::NonPos => Sign::NonNeg,
            Sign::Zero => Sign::Zero,
            Sign::NonNeg => Sign::NonPos,
            Sign::Pos => Sign::Neg,
            Sign::Top => Sign::Top,
        }
    }

    /// Returns `true` if this sign can include negative values (needs a SliceCursor).
    pub fn needs_cursor(self) -> bool {
        matches!(self, Sign::Neg | Sign::NonPos | Sign::Top)
    }

    fn of_u128(v: u128) -> Sign {
        if v == 0 { Sign::Zero } else { Sign::Pos }
    }
}

fn sign_add(a: Sign, b: Sign) -> Sign {
    use Sign::*;
    match (a, b) {
        (Bottom, _) | (_, Bottom) => Bottom,
        (Top, _) | (_, Top) => Top,
        (Pos, Pos) => Pos,
        (NonNeg, NonNeg) => NonNeg,
        (Pos, NonNeg) | (NonNeg, Pos) => Pos,
        (Zero, x) | (x, Zero) => x,
        (Neg, Neg) => Neg,
        (NonPos, NonPos) => NonPos,
        (Neg, NonPos) | (NonPos, Neg) => Neg,
        _ => Top,
    }
}

fn sign_mul(a: Sign, b: Sign) -> Sign {
    use Sign::*;
    match (a, b) {
        (Bottom, _) | (_, Bottom) => Bottom,
        (Zero, _) | (_, Zero) => Zero,
        (Top, _) | (_, Top) => Top,
        (Pos, Pos) => Pos,
        (Neg, Neg) => Pos,
        (NonNeg, NonNeg) => NonNeg,
        (NonPos, NonPos) => NonNeg,
        (Pos, NonNeg) | (NonNeg, Pos) => NonNeg,
        (Neg, NonPos) | (NonPos, Neg) => NonNeg,
        (Neg, Pos) | (Pos, Neg) => Neg,
        (Neg, NonNeg) | (NonNeg, Neg) => NonPos,
        (Pos, NonPos) | (NonPos, Pos) => NonPos,
        _ => Top,
    }
}

// Analysis output
#[derive(Debug, Default)]
pub struct OffsetSignResult {
    pub access_signs: FxHashMap<LocalDefId, FxHashMap<HirId, Sign>>,
}

// Entry point
pub fn offset_sign_analysis(rust_program: &RustProgram<'_>) -> OffsetSignResult {
    let mut result = OffsetSignResult::default();
    for &did in &rust_program.functions {
        let body = rust_program.tcx.hir_body_owned_by(did);
        let typeck = rust_program.tcx.typeck(did);

        // compute sign of each integer variable (flow-insensitive fixpoint).
        let var_signs = integer_var_signs(body, typeck);

        // collect pointer offset access signs using Phase 1 results.
        let mut collector = PtrOffsetCollector {
            typeck,
            var_signs: &var_signs,
            ptr_access_signs: FxHashMap::default(),
            ptr_copy_neighbors: FxHashMap::default(),
        };
        collector.visit_body(body);
        collector.propagate_copy_signs();

        if !collector.ptr_access_signs.is_empty() {
            result.access_signs.insert(did, collector.ptr_access_signs);
        }
    }
    result
}

// integer variable sign analysis
struct BindingCollector<'tcx> {
    bindings: Vec<(HirId, &'tcx hir::Expr<'tcx>)>,
}

impl<'tcx> Visitor<'tcx> for BindingCollector<'tcx> {
    fn visit_local(&mut self, local: &'tcx hir::LetStmt<'tcx>) {
        if let hir::PatKind::Binding(_, hir_id, _, _) = local.pat.kind
            && let Some(init) = local.init
        {
            self.bindings.push((hir_id, init));
        }
        hir::intravisit::walk_local(self, local);
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        if let ExprKind::Assign(lhs, rhs, _) = ex.kind
            && let ExprKind::Path(QPath::Resolved(_, path)) = lhs.kind
            && let Res::Local(hir_id) = path.res
        {
            self.bindings.push((hir_id, rhs));
        }
        // i += rhs: treat rhs as an additional binding for i.
        // The fixpoint join of { let i = 0 (Zero), rhs (Pos) } gives NonNeg,
        // correctly capturing the common C2Rust while-loop counter pattern.
        if let ExprKind::AssignOp(op, lhs, rhs) = ex.kind
            && matches!(
                op.node,
                AssignOpKind::AddAssign | AssignOpKind::SubAssign | AssignOpKind::MulAssign
            )
            && let ExprKind::Path(QPath::Resolved(_, path)) = lhs.kind
            && let Res::Local(hir_id) = path.res
        {
            self.bindings.push((hir_id, rhs));
        }
        walk_expr(self, ex);
    }
}

fn integer_var_signs<'tcx>(
    body: &'tcx hir::Body<'tcx>,
    typeck: &'tcx ty::TypeckResults<'tcx>,
) -> FxHashMap<HirId, Sign> {
    let mut bc = BindingCollector {
        bindings: Vec::new(),
    };
    bc.visit_body(body);
    let bindings = bc.bindings;

    let mut var_signs: FxHashMap<HirId, Sign> = FxHashMap::default();
    loop {
        let mut changed = false;
        for (hir_id, rhs) in &bindings {
            let new_sign = sign_of_expr(rhs, typeck, &var_signs);
            let old_sign = var_signs.get(hir_id).copied().unwrap_or(Sign::Bottom);
            let joined = old_sign.join(new_sign);
            if joined != old_sign {
                var_signs.insert(*hir_id, joined);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    var_signs
}

// pointer offset sign collection
struct PtrOffsetCollector<'tcx, 'a> {
    typeck: &'a ty::TypeckResults<'tcx>,
    var_signs: &'a FxHashMap<HirId, Sign>,
    ptr_access_signs: FxHashMap<HirId, Sign>,
    ptr_copy_neighbors: FxHashMap<HirId, Vec<HirId>>,
}

impl<'tcx> Visitor<'tcx> for PtrOffsetCollector<'tcx, '_> {
    fn visit_local(&mut self, local: &'tcx hir::LetStmt<'tcx>) {
        if let hir::PatKind::Binding(_, lhs_hir_id, _, _) = local.pat.kind
            && self.is_raw_ptr_local(lhs_hir_id)
            && let Some(init) = local.init
            && let Some(rhs_hir_id) = root_local(init)
            && self.is_raw_ptr_local(rhs_hir_id)
        {
            self.record_copy(lhs_hir_id, rhs_hir_id);
        }
        hir::intravisit::walk_local(self, local);
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        if let ExprKind::Assign(lhs, rhs, _) = ex.kind
            && let ExprKind::Path(QPath::Resolved(_, path)) = lhs.kind
            && let Res::Local(lhs_hir_id) = path.res
            && self.is_raw_ptr_local(lhs_hir_id)
            && let Some(rhs_hir_id) = root_local(rhs)
            && self.is_raw_ptr_local(rhs_hir_id)
        {
            self.record_copy(lhs_hir_id, rhs_hir_id);
        }

        if let ExprKind::MethodCall(seg, receiver, args, _) = ex.kind
            && matches!(
                seg.ident.as_str(),
                "offset" | "wrapping_offset" | "byte_offset" | "wrapping_byte_offset"
            )
            && let Some(base_hir_id) = root_local(receiver)
            && let [offset_arg] = args
        {
            let sign = sign_of_expr(offset_arg, self.typeck, self.var_signs);
            self.ptr_access_signs
                .entry(base_hir_id)
                .and_modify(|s| *s = s.join(sign))
                .or_insert(sign);
        }
        walk_expr(self, ex);
    }
}

impl<'tcx> PtrOffsetCollector<'tcx, '_> {
    fn is_raw_ptr_local(&self, hir_id: HirId) -> bool {
        self.typeck.node_type(hir_id).is_raw_ptr()
    }

    fn record_copy(&mut self, lhs_hir_id: HirId, rhs_hir_id: HirId) {
        self.ptr_copy_neighbors
            .entry(lhs_hir_id)
            .or_default()
            .push(rhs_hir_id);
    }

    fn propagate_copy_signs(&mut self) {
        if self.ptr_access_signs.is_empty() || self.ptr_copy_neighbors.is_empty() {
            return;
        }

        let mut worklist: VecDeque<HirId> = self.ptr_access_signs.keys().copied().collect();
        while let Some(curr) = worklist.pop_front() {
            let Some(curr_sign) = self.ptr_access_signs.get(&curr).copied() else {
                continue;
            };
            let Some(neighbors) = self.ptr_copy_neighbors.get(&curr) else {
                continue;
            };

            for &next in neighbors {
                let old_sign = self
                    .ptr_access_signs
                    .get(&next)
                    .copied()
                    .unwrap_or(Sign::Bottom);
                let joined = old_sign.join(curr_sign);
                if joined != old_sign {
                    self.ptr_access_signs.insert(next, joined);
                    worklist.push_back(next);
                }
            }
        }
    }
}

/// Unwrap through casts, parens, unary ops, address-of to find the root local variable's HirId
fn root_local(expr: &hir::Expr<'_>) -> Option<HirId> {
    let expr = unwrap_drop_temps(expr);
    match expr.kind {
        ExprKind::Path(QPath::Resolved(_, path)) => {
            let Res::Local(hir_id) = path.res else { return None };
            Some(hir_id)
        }
        ExprKind::Cast(inner, _)
        | ExprKind::Type(inner, _)
        | ExprKind::Unary(_, inner)
        | ExprKind::AddrOf(_, _, inner) => root_local(inner),
        ExprKind::Field(inner, _) => {
            let inner = unwrap_drop_temps(inner);
            if matches!(inner.kind, ExprKind::Unary(UnOp::Deref, _)) {
                None
            } else {
                root_local(inner)
            }
        }
        ExprKind::Index(inner, _, _) => root_local(inner),
        _ => None,
    }
}

// sign_of_expr
fn sign_of_expr<'tcx>(
    expr: &'tcx hir::Expr<'tcx>,
    typeck: &ty::TypeckResults<'tcx>,
    var_signs: &FxHashMap<HirId, Sign>,
) -> Sign {
    let expr = unwrap_drop_temps(expr);
    match expr.kind {
        ExprKind::Lit(lit) => match lit.node {
            LitKind::Int(v, _) => Sign::of_u128(v.get()),
            _ => Sign::Top,
        },
        ExprKind::Unary(UnOp::Neg, inner) => sign_of_expr(inner, typeck, var_signs).negate(),
        ExprKind::Cast(inner, _) => {
            let ty = typeck.expr_ty(expr);
            if is_unsigned_int(ty) {
                Sign::NonNeg
            } else {
                sign_of_expr(inner, typeck, var_signs)
            }
        }
        ExprKind::Path(QPath::Resolved(_, path)) => {
            if let Res::Local(hir_id) = path.res {
                var_signs
                    .get(&hir_id)
                    .copied()
                    .unwrap_or_else(|| type_based_sign(typeck.expr_ty(expr)))
            } else {
                type_based_sign(typeck.expr_ty(expr))
            }
        }
        ExprKind::Binary(op, lhs, rhs) => {
            let sl = sign_of_expr(lhs, typeck, var_signs);
            let sr = sign_of_expr(rhs, typeck, var_signs);
            match op.node {
                BinOpKind::Add => sign_add(sl, sr),
                BinOpKind::Sub => sign_add(sl, sr.negate()),
                BinOpKind::Mul => sign_mul(sl, sr),
                _ => type_based_sign(typeck.expr_ty(expr)),
            }
        }
        ExprKind::Block(block, _) => {
            if let Some(tail) = block.expr {
                sign_of_expr(tail, typeck, var_signs)
            } else {
                Sign::Top
            }
        }
        ExprKind::If(_, then_expr, Some(else_expr)) => {
            let s1 = block_tail_sign(then_expr, typeck, var_signs);
            let s2 = block_tail_sign(else_expr, typeck, var_signs);
            s1.join(s2)
        }
        _ => type_based_sign(typeck.expr_ty(expr)),
    }
}

fn block_tail_sign<'tcx>(
    expr: &'tcx hir::Expr<'tcx>,
    typeck: &ty::TypeckResults<'tcx>,
    var_signs: &FxHashMap<HirId, Sign>,
) -> Sign {
    if let ExprKind::Block(b, _) = expr.kind
        && let Some(e) = b.expr
    {
        sign_of_expr(e, typeck, var_signs)
    } else {
        sign_of_expr(expr, typeck, var_signs)
    }
}

fn type_based_sign(ty: ty::Ty<'_>) -> Sign {
    if is_unsigned_int(ty) {
        Sign::NonNeg
    } else {
        Sign::Top
    }
}

fn is_unsigned_int(ty: ty::Ty<'_>) -> bool {
    matches!(ty.kind(), ty::TyKind::Uint(_))
}

fn unwrap_drop_temps<'tcx>(expr: &'tcx hir::Expr<'tcx>) -> &'tcx hir::Expr<'tcx> {
    match expr.kind {
        ExprKind::DropTemps(inner) => unwrap_drop_temps(inner),
        _ => expr,
    }
}
