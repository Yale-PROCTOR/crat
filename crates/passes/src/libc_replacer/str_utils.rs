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
}
