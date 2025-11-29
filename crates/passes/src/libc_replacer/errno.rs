use etrace::some_or;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def::{DefKind, Res},
    *,
};
use rustc_middle::{hir::nested_filter, mir, mir::Location, ty::TyCtxt};
use rustc_span::Symbol;

use crate::rustc_hir::intravisit::Visitor as _;

#[derive(Debug)]
pub struct ErrnoCalls {
    pub checks: FxHashMap<HirId, ErrnoCheck>,
    pub sources: FxHashSet<ForeignCall>,
    pub assigns: FxHashSet<HirId>,
}

pub fn find_errno_calls(tcx: TyCtxt<'_>) -> ErrnoCalls {
    let hir_to_thir = utils::ir::map_hir_to_thir(tcx);

    let mut checks = FxHashMap::default();
    let mut sources = FxHashSet::default();
    let mut assigns = FxHashSet::default();
    for def_id in tcx.hir_body_owners() {
        if tcx.def_kind(def_id) != DefKind::Fn {
            continue;
        }
        if tcx.item_name(def_id.to_def_id()).as_str() == "main" {
            continue;
        }
        if tcx.def_path_str(def_id).contains("c_lib::") {
            continue;
        }
        let body = tcx.hir_body_owned_by(def_id);
        let mut visitor = HirVisitor {
            tcx,
            ctx: HirCtx::default(),
        };
        visitor.visit_body(body);
        assigns.extend(visitor.ctx.errno_assignment_calls);

        let thir_to_mir = utils::ir::map_thir_to_mir(def_id, false, tcx);
        let foreign_calls: FxHashMap<_, _> = visitor
            .ctx
            .foreign_calls
            .into_iter()
            .filter_map(|call| {
                let loc = hir_id_to_location(call.hir_id, &hir_to_thir, &thir_to_mir)?;
                Some((loc.block, call))
            })
            .collect();

        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        let dominators = body.basic_blocks.dominators();

        for cmp in &visitor.ctx.errno_comparisons {
            let operand = tcx.hir_expect_expr(cmp.operand);
            let operand = some_or!(eval_to_int(operand, tcx), continue);
            let error_code = some_or!(ErrorCode::try_from_int(operand), continue);

            let call_loc = some_or!(
                hir_id_to_location(cmp.errno_call, &hir_to_thir, &thir_to_mir),
                continue
            );
            let mut block = call_loc.block;
            let source = loop {
                let idom = some_or!(dominators.immediate_dominator(block), break None);
                if let Some(call) = foreign_calls.get(&idom) {
                    break Some(call);
                }
                block = idom;
            };
            let call = some_or!(source, continue);
            let check = ErrnoCheck {
                source: *call,
                code: error_code,
                equals: cmp.equals,
            };
            checks.insert(cmp.hir_id, check);
            sources.insert(*call);
        }
    }

    ErrnoCalls {
        checks,
        sources,
        assigns,
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ErrnoCheck {
    pub source: ForeignCall,
    pub code: ErrorCode,
    pub equals: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorCode {
    /// 0
    None,
    /// 33
    Edom,
    /// 34
    Erange,
}

impl ErrorCode {
    fn try_from_int(operand: i32) -> Option<Self> {
        match operand {
            0 => Some(ErrorCode::None),
            33 => Some(ErrorCode::Edom),
            34 => Some(ErrorCode::Erange),
            _ => None,
        }
    }
}

fn hir_id_to_location(
    hir_id: HirId,
    hir_to_thir: &utils::ir::HirToThir,
    thir_to_mir: &utils::ir::ThirToMir,
) -> Option<Location> {
    let expr_id = hir_to_thir.exprs.get(&hir_id)?;
    let locs = thir_to_mir.expr_to_locs.get(expr_id)?;
    locs.first().copied()
}

fn eval_to_int(expr: &Expr<'_>, tcx: TyCtxt<'_>) -> Option<i32> {
    match &expr.kind {
        ExprKind::Lit(lit) => match &lit.node {
            rustc_ast::LitKind::Int(value, _) => Some(value.0 as i32),
            _ => None,
        },
        ExprKind::Path(QPath::Resolved(_, path)) => {
            if let Res::Def(DefKind::Const, def_id) = path.res
                && let Ok(v) = tcx.const_eval_poly(def_id)
                && let mir::ConstValue::Scalar(scalar) = v
                && let mir::interpret::Scalar::Int(int) = scalar
            {
                Some(int.to_int(int.size()) as i32)
            } else {
                None
            }
        }
        ExprKind::Cast(e, _) => eval_to_int(e, tcx),
        ExprKind::DropTemps(e) => eval_to_int(e, tcx),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy)]
struct ErrnoComparison {
    hir_id: HirId,
    errno_call: HirId,
    operand: HirId,
    equals: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ForeignCall {
    pub hir_id: HirId,
    pub name: Symbol,
    pub destination: Option<HirId>,
}

#[derive(Default)]
struct HirCtx {
    errno_assignment_calls: FxHashSet<HirId>,
    errno_comparisons: Vec<ErrnoComparison>,
    foreign_calls: Vec<ForeignCall>,
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ctx: HirCtx,
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
        intravisit::walk_expr(self, expr);

        match expr.kind {
            ExprKind::Assign(lhs, _, _) => {
                if self.errno_call_hir_id(lhs).is_some() {
                    self.ctx.errno_assignment_calls.insert(expr.hir_id);
                }
            }
            ExprKind::Binary(op, lhs, rhs) if matches!(op.node, BinOpKind::Eq | BinOpKind::Ne) => {
                let equals = matches!(op.node, BinOpKind::Eq);
                if let Some(hir_id) = self.errno_call_hir_id(lhs) {
                    let cmp = ErrnoComparison {
                        hir_id: expr.hir_id,
                        errno_call: hir_id,
                        operand: rhs.hir_id,
                        equals,
                    };
                    self.ctx.errno_comparisons.push(cmp);
                } else if let Some(hir_id) = self.errno_call_hir_id(rhs) {
                    let cmp = ErrnoComparison {
                        hir_id: expr.hir_id,
                        errno_call: hir_id,
                        operand: lhs.hir_id,
                        equals,
                    };
                    self.ctx.errno_comparisons.push(cmp);
                }
            }
            ExprKind::Call(callee, _) => {
                if let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind
                    && let Res::Def(DefKind::Fn, def_id) = path.res
                    && let Some(local_def_id) = def_id.as_local()
                    && matches!(
                        self.tcx.hir_node_by_def_id(local_def_id),
                        Node::ForeignItem(_)
                    )
                    && let name = self.tcx.item_name(def_id)
                    && name.as_str() != "__errno_location"
                {
                    let call = ForeignCall {
                        hir_id: expr.hir_id,
                        name,
                        destination: self.return_value_destination(expr),
                    };
                    self.ctx.foreign_calls.push(call);
                }
            }
            _ => {}
        }
    }
}

impl HirVisitor<'_> {
    fn foreign_function_name(&self, expr: &Expr<'_>) -> Option<Symbol> {
        if let ExprKind::Path(QPath::Resolved(_, path)) = utils::hir::unwrap_drop_temps(expr).kind
            && let Res::Def(DefKind::Fn, def_id) = path.res
            && let Some(local_def_id) = def_id.as_local()
            && matches!(
                self.tcx.hir_node_by_def_id(local_def_id),
                Node::ForeignItem(_)
            )
        {
            let name = self.tcx.item_name(def_id);
            Some(name)
        } else {
            None
        }
    }

    fn errno_call_hir_id(&self, expr: &Expr<'_>) -> Option<HirId> {
        if let ExprKind::Unary(UnOp::Deref, e) = utils::hir::unwrap_drop_temps(expr).kind
            && let call = utils::hir::unwrap_drop_temps(e)
            && let ExprKind::Call(func, _) = call.kind
            && let Some(name) = self.foreign_function_name(func)
            && name.as_str() == "__errno_location"
        {
            Some(call.hir_id)
        } else {
            None
        }
    }

    fn return_value_destination(&self, expr: &Expr<'_>) -> Option<HirId> {
        let mut curr_id = expr.hir_id;
        for (parent_id, parent_node) in self.tcx.hir_parent_iter(expr.hir_id) {
            match parent_node {
                Node::Expr(parent_expr) => match parent_expr.kind {
                    ExprKind::DropTemps(_) => {}
                    ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == curr_id => {
                        if let ExprKind::Path(QPath::Resolved(_, path)) =
                            utils::hir::unwrap_drop_temps(lhs).kind
                            && let Res::Local(hir_id) = path.res
                        {
                            return Some(hir_id);
                        }
                        break;
                    }
                    _ => break,
                },
                Node::LetStmt(let_stmt) => {
                    if let Some(init) = let_stmt.init
                        && init.hir_id == curr_id
                        && let PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                    {
                        return Some(hir_id);
                    }
                    break;
                }
                _ => break,
            }
            curr_id = parent_id;
        }
        None
    }
}
