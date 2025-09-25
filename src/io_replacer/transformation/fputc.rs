use rustc_ast::*;
use rustc_ast_pretty::pprust;

use super::{
    stream_ty::*,
    transform::LibItem,
    visitor::{IndicatorCheck, TransformVisitor},
};

impl TransformVisitor<'_, '_, '_> {
    #[inline]
    pub(super) fn transform_fputc<S: StreamExpr>(
        &self,
        stream: &S,
        c: &Expr,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream_str = stream.borrow_for(StreamTrait::Write);
        let c = pprust::expr_to_string(c);
        self.lib_items.borrow_mut().push(LibItem::Fputc);
        self.update_error_no_eof(
            ic,
            format!("crate::stdio::rs_fputc({c}, {stream_str})"),
            stream,
        )
    }

    #[inline]
    pub(super) fn transform_fputwc<S: StreamExpr>(
        &self,
        stream: &S,
        c: &Expr,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream_str = stream.borrow_for(StreamTrait::Write);
        let c = pprust::expr_to_string(c);
        self.lib_items.borrow_mut().push(LibItem::Fputwc);
        self.update_error_no_eof(
            ic,
            format!("crate::stdio::rs_fputwc({c}, {stream_str})"),
            stream,
        )
    }
}

pub(super) static FPUTC: &str = r#"
#[inline]
pub(crate) fn rs_fputc<W: std::io::Write>(c: i32, mut stream: W) -> (i32, i32) {
    let c = c as u8;
    match stream.write_all(&[c]) {
        Ok(_) => (c as i32, 0),
        Err(_) => (libc::EOF, 1),
    }
}
"#;

pub(super) static FWPUTC: &str = r#"
pub(crate) fn rs_fputwc<W: std::io::Write>(c: i32, mut stream: W) -> (i32, i32) {
    match write!(stream, "{}", std::char::from_u32(c as _).unwrap()) {
        Ok(_) => (c, 0),
        Err(_) => (libc::EOF, 1),
    }
}
"#;
