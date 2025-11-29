use rustc_ast::*;

use super::{
    stream_ty::*,
    transform::LibItem,
    visitor::{IndicatorCheck, TransformVisitor},
};

impl TransformVisitor<'_, '_, '_> {
    #[inline]
    pub(super) fn transform_fflush<S: StreamExpr>(
        &self,
        stream: &S,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream_str = stream.borrow_for(StreamTrait::Write);
        self.lib_items.borrow_mut().insert(LibItem::Fflush);
        self.update_error_no_eof(ic, format!("crate::c_lib::rs_fflush({stream_str})"), stream)
    }
}

pub(super) static FFLUSH: &str = r#"
#[inline]
pub(crate) fn rs_fflush<W: std::io::Write>(mut stream: W) -> (i32, i32) {
    match stream.flush() {
        Ok(_) => (0, 0),
        Err(_) => (-1, 1),
    }
}
"#;
