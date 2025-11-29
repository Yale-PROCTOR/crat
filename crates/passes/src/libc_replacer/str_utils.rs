use rustc_ast::*;
use rustc_ast_pretty::pprust;

impl super::TransformVisitor<'_> {
    pub fn transform_strlen(&mut self, s: &Expr) -> Expr {
        if let Some((array, ty)) = utils::ir::array_of_as_ptr(s, &self.ast_to_hir, self.tcx) {
            if ty == self.tcx.types.u8 {
                let array = pprust::expr_to_string(array);
                return utils::expr!(
                    "std::ffi::CStr::from_bytes_until_nul(&({array})).unwrap().count_bytes()"
                );
            } else if ty == self.tcx.types.i8 {
                let array = pprust::expr_to_string(array);
                self.bytemuck = true;
                return utils::expr!(
                    "std::ffi::CStr::from_bytes_until_nul(bytemuck::cast_slice(&({array}))).unwrap().count_bytes()"
                );
            }
        }

        let s_str = pprust::expr_to_string(s);
        utils::expr!("std::ffi::CStr::from_ptr(({s_str}) as _).count_bytes()")
    }

    pub fn transform_strncpy(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr> {
        let n_str = pprust::expr_to_string(n);
        if let Some((array1, ty1)) = utils::ir::array_of_as_ptr(s1, &self.ast_to_hir, self.tcx)
            && let Some((array2, ty2)) = utils::ir::array_of_as_ptr(s2, &self.ast_to_hir, self.tcx)
        {
            if (ty1 == self.tcx.types.u8 && ty2 == self.tcx.types.u8)
                || (ty1 == self.tcx.types.i8 && ty2 == self.tcx.types.i8)
            {
                let array1 = pprust::expr_to_string(array1);
                let array2 = pprust::expr_to_string(array2);
                return Some(utils::expr!(
                    "({array1})[..({n_str})].copy_from_slice(&({array2})[..({n_str})])"
                ));
            } else if ty1 == self.tcx.types.u8 || ty1 == self.tcx.types.i8 {
                self.bytemuck = true;
                let array1 = pprust::expr_to_string(array1);
                let array2 = pprust::expr_to_string(array2);
                return Some(utils::expr!(
                    "({array1})[..({n_str})].copy_from_slice(bytemuck::cast_slice(&({array2})[..({n_str})]))"
                ));
            }
        }
        None
    }

    pub fn transform_strcspn(&mut self, s1: &Expr, s2: &Expr) -> Option<Expr> {
        if let Some((array1, ty1)) = utils::ir::array_of_as_ptr(s1, &self.ast_to_hir, self.tcx)
            && let Some((array2, ty2)) = utils::ir::array_of_as_ptr(s2, &self.ast_to_hir, self.tcx)
        {
            let array1 = pprust::expr_to_string(array1);
            let array1 = if ty1 == self.tcx.types.u8 {
                Some(format!("&({array1})"))
            } else if ty1 == self.tcx.types.i8 {
                self.bytemuck = true;
                Some(format!("bytemuck::cast_slice(&({array1}))"))
            } else {
                None
            };
            let array2 = pprust::expr_to_string(array2);
            let array2 = if ty2 == self.tcx.types.u8 {
                Some(format!("&({array2})"))
            } else if ty2 == self.tcx.types.i8 {
                self.bytemuck = true;
                Some(format!("bytemuck::cast_slice(&({array2}))"))
            } else {
                None
            };
            if let Some(array1) = array1
                && let Some(array2) = array2
            {
                return Some(utils::expr!(
                    "std::ffi::CStr::from_bytes_until_nul({array1}).unwrap().to_bytes().iter().take_while(
                        |c| !std::ffi::CStr::from_bytes_until_nul({array2}).unwrap().to_bytes().contains(c)
                    ).count()"
                ));
            }
        }
        None
    }
}
