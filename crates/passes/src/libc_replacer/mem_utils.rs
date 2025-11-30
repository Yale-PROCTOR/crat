use rustc_ast::*;
use rustc_ast_pretty::pprust;
use rustc_hir::def_id::LocalDefId;
use rustc_span::{Symbol, sym};
use utils::ast::unwrap_cast_and_paren;

impl<'tcx> super::TransformVisitor<'tcx> {
    pub fn transform_memcpy(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr> {
        let (array1, ty1) = utils::ir::array_of_as_ptr(s1, &self.ast_to_hir, self.tcx)?;
        let (array2, ty2) = utils::ir::array_of_as_ptr(s2, &self.ast_to_hir, self.tcx)?;
        let hir_n = self.ast_to_hir.get_expr(n.id, self.tcx)?;
        if ty1 == ty2
            && let Some(len_expr) = self.get_len_from_size(n, ty1, hir_n.hir_id.owner.def_id)
        {
            Some(utils::expr!(
                "({0}[..({2}) as usize]).copy_from_slice(&{1}[..({2}) as usize])",
                pprust::expr_to_string(array1),
                pprust::expr_to_string(array2),
                pprust::expr_to_string(&len_expr)
            ))
        } else if ty1.is_numeric() && ty2.is_numeric() {
            self.bytemuck = true;
            let array1 = pprust::expr_to_string(array1);
            let array1 = if ty1 == self.tcx.types.u8 {
                format!("({array1})")
            } else {
                format!("bytemuck::cast_slice_mut::<_, u8>(&mut ({array1}))")
            };
            let array2 = pprust::expr_to_string(array2);
            let array2 = if ty2 == self.tcx.types.u8 {
                format!("({array2})")
            } else {
                format!("bytemuck::cast_slice(&({array2}))")
            };
            let n = pprust::expr_to_string(n);
            Some(utils::expr!(
                "{array1}[..({n}) as usize].copy_from_slice(&{array2}[..({n}) as usize])",
            ))
        } else {
            None
        }
    }

    pub fn transform_memset(&mut self, s: &Expr, c: &Expr, n: &Expr) -> Option<Expr> {
        let (array, ty) = utils::ir::array_of_as_ptr(s, &self.ast_to_hir, self.tcx)?;
        let array = pprust::expr_to_string(array);
        let c = pprust::expr_to_string(c);
        let n = pprust::expr_to_string(n);
        if ty == self.tcx.types.u8 || ty == self.tcx.types.i8 {
            Some(utils::expr!(
                "({array})[..({n}) as usize].fill(({c}) as {ty})"
            ))
        } else if ty.is_numeric() {
            self.bytemuck = true;
            Some(utils::expr!(
                "bytemuck::cast_slice_mut::<_, u8>(&mut ({array}))[..({n}) as usize].fill(({c}) as u8)"
            ))
        } else {
            None
        }
    }

    fn get_len_from_size(
        &self,
        size_expr: &Expr,
        ty: rustc_middle::ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Option<Expr> {
        if let ExprKind::MethodCall(call) = &unwrap_cast_and_paren(size_expr).kind
            && call.seg.ident.name == sym::wrapping_mul
            && call.args.len() == 1
        {
            for (operand_1, operand_2) in [
                (&*call.receiver, &*call.args[0]),
                (&*call.args[0], &*call.receiver),
            ] {
                if let ExprKind::Call(func, args) = &unwrap_cast_and_paren(operand_1).kind
                    && let ExprKind::Path(_, call_path) = &func.kind
                    && let Some(func_name) = get_fn_name_from_expr(func)
                    && func_name == sym::size_of
                    && args.is_empty()
                    && let Some(last_seg) = call_path.segments.last()
                    && let Some(box GenericArgs::AngleBracketed(AngleBracketedArgs {
                        args, ..
                    })) = &last_seg.args
                    && let Some(AngleBracketedArg::Arg(GenericArg::Type(box ty_generic))) =
                        args.first()
                    && let Some(ty_generic) = self.ast_to_hir.get_ty(ty_generic.id, self.tcx)
                {
                    let typeck = self.tcx.typeck(ty_generic.hir_id.owner);
                    let ty_generic = typeck.node_type(ty_generic.hir_id);
                    if utils::ir::ty_size(ty_generic, def_id, self.tcx)
                        == utils::ir::ty_size(ty, def_id, self.tcx)
                    {
                        return Some(operand_2.clone());
                    }
                }
            }
        }
        None
    }
}

fn get_fn_name_from_expr(expr: &Expr) -> Option<Symbol> {
    if let ExprKind::Path(_, path) = &expr.kind
        && let Some(segment) = path.segments.last()
    {
        Some(segment.ident.name)
    } else {
        None
    }
}
