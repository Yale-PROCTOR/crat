//! **R1313-2 (relay main/371 step 2; main 254 §1 (b), §5) — the cast-offset need.**
//!
//! An `offset` applied to a pointer cast of the subject —
//! `*(addr as *mut c_uchar).offset(SPX_OFFSET_CHAIN_ADDR as isize) = v` — is the subject's own
//! arithmetic, in the cast target's unit. The facts walk records it among the subject's raw-only uses,
//! so the slice need follows exactly as for `addr.offset(e)`, with `fatness = arr` the licence. One
//! range is not arithmetic past the referent: a constant one inside `size_of::<T>()` (P01's
//! `SPX_set_layer_addr` writes byte 3 of a `u32`), which keeps the thin form.
//!
//! **The byte view (R1313-2).** On a slice subject the use renders through bytemuck:
//! `bytemuck::cast_slice_mut::<u32, u8>(addr)[K]` for a written place, `cast_slice` for a read, and
//! the checked suffix `&mut bytemuck::cast_slice_mut::<u32, u8>(addr)[K..]` for a computed argument.
//! The suffix is what closes A5's collision: the argument is a slice, so the callee class's slice
//! formal takes it bare. Admitted for `u32` → `u8` only: alignment 1 and the size divides, so the cast
//! never fails; the reverse is fallible and refused. An identity cast (the same pointee) is the plain
//! index. Every other retyping stays an unsupported use, and the subject is held.

use rustc_hir::{
    Expr, ExprKind, HirId, Node, QPath,
    def::{DefKind, Res},
    def_id::LocalDefId,
};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, UintTy};

/// The arithmetic methods a cast receiver carries into the subject's own raw-only uses.
const CAST_ARITHMETIC: &[&str] = &[
    "offset",
    "wrapping_offset",
    "add",
    "sub",
    "wrapping_add",
    "wrapping_sub",
];

/// How a cast-offset use renders on a slice subject.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ByteView {
    /// The cast keeps the pointee (`*const u8 as *mut u8`): the slice's own index.
    Identity,
    /// `u32` → `u8` (R1313-2).
    U32Bytes,
}

impl ByteView {
    /// The slice expression the index applies to.
    pub(crate) fn base(self, name: &str, mutable: bool) -> String {
        match self {
            ByteView::Identity => format!("({name})"),
            ByteView::U32Bytes => format!(
                "bytemuck::cast_slice{}::<u32, u8>({name})",
                if mutable { "_mut" } else { "" }
            ),
        }
    }

    pub(crate) fn key(self) -> &'static str {
        match self {
            ByteView::Identity => "identity",
            ByteView::U32Bytes => "u32-bytes",
        }
    }
}

/// `receiver` is a pointer-to-pointer cast chain over a local: the local, its pointee and the
/// outermost cast's pointee.
fn cast_of_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    receiver: &Expr<'tcx>,
) -> Option<(HirId, Ty<'tcx>, Ty<'tcx>)> {
    if !matches!(receiver.kind, ExprKind::Cast(..)) {
        return None;
    }
    let typeck = tcx.typeck(owner);
    let TyKind::RawPtr(target, _) = *typeck.expr_ty(receiver).kind() else {
        return None;
    };
    let mut inner = receiver;
    while let ExprKind::Cast(operand, _) = inner.kind {
        if !typeck.expr_ty(operand).is_raw_ptr() {
            return None;
        }
        inner = operand;
    }
    let ExprKind::Path(QPath::Resolved(_, path)) = &inner.kind else {
        return None;
    };
    let Res::Local(local) = path.res else {
        return None;
    };
    let TyKind::RawPtr(source, _) = *typeck.expr_ty(inner).kind() else {
        return None;
    };
    Some((local, source, target))
}

/// The facts walk's question: is `receiver.method(args)` a local's arithmetic through its cast, and
/// does it leave the local's own pointee? Returns the local when it does.
pub(crate) fn arithmetic_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    method: &str,
    receiver: &Expr<'tcx>,
    args: &[Expr<'tcx>],
) -> Option<HirId> {
    if !CAST_ARITHMETIC.contains(&method) {
        return None;
    }
    let (local, source, target) = cast_of_local(tcx, owner, receiver)?;
    let [delta] = args else { return None };
    (!inside_referent(tcx, owner, method, delta, source, target)).then_some(local)
}

/// A constant range `[k, k + 1)` in the cast target's unit that lies inside `size_of::<source>()`.
fn inside_referent<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    method: &str,
    delta: &Expr<'tcx>,
    source: Ty<'tcx>,
    target: Ty<'tcx>,
) -> bool {
    let Some(k) = eval_const(tcx, delta) else {
        return false;
    };
    let k = if matches!(method, "sub" | "wrapping_sub") {
        -k
    } else {
        k
    };
    let (Some(source), Some(target)) = (size_of(tcx, owner, source), size_of(tcx, owner, target))
    else {
        return false;
    };
    k >= 0 && (k + 1) * target <= source
}

fn size_of<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId, ty: Ty<'tcx>) -> Option<i128> {
    let env = ty::TypingEnv::post_analysis(tcx, owner);
    tcx.layout_of(env.as_query_input(ty))
        .ok()
        .map(|layout| i128::from(layout.size.bytes()))
}

/// C2Rust's constant offsets: integer literals under casts, a path to a `const` item (its own
/// initializer), unary minus, `+`, `-` and `*`.
fn eval_const<'tcx>(tcx: TyCtxt<'tcx>, expr: &Expr<'tcx>) -> Option<i128> {
    use rustc_hir::BinOpKind;
    match &expr.kind {
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(value, _) => i128::try_from(value.get()).ok(),
            _ => None,
        },
        ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) => eval_const(tcx, inner),
        ExprKind::Unary(rustc_hir::UnOp::Neg, inner) => eval_const(tcx, inner).map(|v| -v),
        ExprKind::Binary(op, left, right) => {
            let (left, right) = (eval_const(tcx, left)?, eval_const(tcx, right)?);
            match op.node {
                BinOpKind::Add => left.checked_add(right),
                BinOpKind::Sub => left.checked_sub(right),
                BinOpKind::Mul => left.checked_mul(right),
                _ => None,
            }
        }
        ExprKind::Path(QPath::Resolved(_, path)) => {
            let Res::Def(DefKind::Const, did) = path.res else {
                return None;
            };
            eval_const(tcx, tcx.hir_body_owned_by(did.as_local()?).value)
        }
        _ => None,
    }
}

/// The admitted views: the identity, and `u32` → `u8`.
fn byte_view<'tcx>(source: Ty<'tcx>, target: Ty<'tcx>) -> Option<ByteView> {
    if source == target {
        return Some(ByteView::Identity);
    }
    match (source.kind(), target.kind()) {
        (TyKind::Uint(UintTy::U32), TyKind::Uint(UintTy::U8)) => Some(ByteView::U32Bytes),
        _ => None,
    }
}

/// One cast-offset spine above a path `use_expr` of a slice subject: `(x as *mut U).offset(e)`.
pub(crate) struct Spine<'tcx> {
    /// The outermost cast, the receiver of the offset.
    pub(crate) cast: &'tcx Expr<'tcx>,
    /// The `offset` call.
    pub(crate) call: &'tcx Expr<'tcx>,
    pub(crate) delta: &'tcx Expr<'tcx>,
    pub(crate) view: ByteView,
    /// The cast target's size: the unit of the offset.
    pub(crate) unit_bytes: Option<i128>,
}

/// The spine above `use_expr`, when its view is admitted.
pub(crate) fn spine<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    use_expr: &'tcx Expr<'tcx>,
) -> Option<Spine<'tcx>> {
    let mut cast = use_expr;
    while let Node::Expr(parent) = tcx.parent_hir_node(cast.hir_id)
        && let ExprKind::Cast(inner, _) = parent.kind
        && inner.hir_id == cast.hir_id
    {
        cast = parent;
    }
    if cast.hir_id == use_expr.hir_id {
        return None;
    }
    let Node::Expr(call) = tcx.parent_hir_node(cast.hir_id) else {
        return None;
    };
    let ExprKind::MethodCall(segment, receiver, [delta], _) = call.kind else {
        return None;
    };
    if receiver.hir_id != cast.hir_id || segment.ident.name.as_str() != "offset" {
        return None;
    }
    let typeck = tcx.typeck(owner);
    let callee = typeck.type_dependent_def_id(call.hir_id)?;
    if tcx.crate_name(callee.krate).as_str() != "core" {
        return None;
    }
    let (_, source, target) = cast_of_local(tcx, owner, cast)?;
    Some(Spine {
        cast,
        call,
        delta,
        view: byte_view(source, target)?,
        unit_bytes: size_of(tcx, owner, target),
    })
}

/// The index never moves backwards: a constant that evaluates non-negative (`SPX_OFFSET_TREE as
/// isize`), or wave-6s's forward delta.
pub(crate) fn forward<'tcx>(tcx: TyCtxt<'tcx>, delta: &'tcx Expr<'tcx>) -> bool {
    match eval_const(tcx, delta) {
        Some(k) => k >= 0,
        None => super::slice_forms::forward_delta(tcx, delta),
    }
}

/// **The byte-view receipt** (relay 371 step 2): one row per cast-offset site of a subject the table
/// decides `Slice`, with the view, the use (`place` / `suffix`), the constant offset in the view's
/// unit (`-` when it is not a constant), the unit, and the subject's largest constant offset with the
/// bytes it needs (`(largest + 1) * unit`). The extent each caller supplies is the C arm's own
/// receipt (evidence, or §77's where fabricated); whether the subject delivered is `subjects.tsv`'s
/// outcome.
pub(crate) fn receipts_tsv(tcx: TyCtxt<'_>, table: &super::DecisionTable) -> String {
    use rustc_hir::intravisit::{self, Visitor};
    struct Sites<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        local: HirId,
        out: &'a mut Vec<(
            String,
            &'static str,
            &'static str,
            Option<i128>,
            Option<i128>,
        )>,
    }
    impl<'tcx> Visitor<'tcx> for Sites<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && path.res == Res::Local(self.local)
                && let Some(spine) = spine(self.tcx, self.owner, expr)
            {
                let place = matches!(
                    self.tcx.parent_hir_node(spine.call.hir_id),
                    Node::Expr(deref) if matches!(deref.kind, ExprKind::Unary(rustc_hir::UnOp::Deref, _))
                        && !matches!(
                            self.tcx.parent_hir_node(deref.hir_id),
                            Node::Expr(parent) if matches!(parent.kind, ExprKind::AddrOf(..))
                        )
                );
                self.out.push((
                    super::emitability::EmitabilityFacts::site(self.tcx, spine.call.span),
                    spine.view.key(),
                    if place { "place" } else { "suffix" },
                    eval_const(self.tcx, spine.delta),
                    spine.unit_bytes,
                ));
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let show = |value: Option<i128>| value.map_or_else(|| "-".to_owned(), |v| v.to_string());
    let mut rows = Vec::new();
    for (subject, decision) in &table.entries {
        match decision {
            super::Decision::Slice { .. } => {}
            super::Decision::Ref { .. }
            | super::Decision::InferredRef { .. }
            | super::Decision::NestedSlice { .. }
            | super::Decision::Opt { .. }
            | super::Decision::Box(_)
            | super::Decision::Cursor { .. }
            | super::Decision::Degraded(_) => continue,
        }
        let Some(body) = tcx.hir_node_by_def_id(subject.fn_did).body_id() else {
            continue;
        };
        let mut sites = Vec::new();
        Sites {
            tcx,
            owner: subject.fn_did,
            local: subject.hir_id,
            out: &mut sites,
        }
        .visit_body(tcx.hir_body(body));
        if sites.is_empty() {
            continue;
        }
        let largest = sites
            .iter()
            .map(|(_, _, _, offset, _)| *offset)
            .collect::<Option<Vec<_>>>()
            .and_then(|offsets| offsets.into_iter().max());
        let key = subject.identity_key(&tcx.def_path_str(subject.fn_did.to_def_id()));
        for (site, view, kind, offset, unit) in &sites {
            let needed = largest
                .zip(*unit)
                .map(|(largest, unit)| (largest + 1) * unit);
            rows.push(format!(
                "{key}\t{}\t{site}\t{view}\t{kind}\t{}\t{}\t{}\t{}\n",
                subject.label.replace(['\t', '\r', '\n'], " "),
                show(*offset),
                show(*unit),
                show(largest),
                show(needed),
            ));
        }
    }
    rows.sort();
    let mut out = String::from(
        "subject_key\tlabel\tsite\tview\tuse\toffset\tunit_bytes\tlargest_offset\tbytes_needed\n",
    );
    out.extend(rows);
    out
}
