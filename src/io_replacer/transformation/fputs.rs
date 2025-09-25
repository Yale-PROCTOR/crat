use rustc_ast::*;
use rustc_ast_pretty::pprust;

use super::{
    stream_ty::*,
    transform::LibItem,
    visitor::{IndicatorCheck, TransformVisitor},
};

impl TransformVisitor<'_, '_, '_> {
    #[inline]
    pub(super) fn transform_fputs<S: StreamExpr>(
        &self,
        stream: &S,
        s: &Expr,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream_str = stream.borrow_for(StreamTrait::Write);
        let s = pprust::expr_to_string(s);
        self.lib_items.borrow_mut().push(LibItem::Fputs);
        self.update_error_no_eof(
            ic,
            format!("crate::stdio::rs_fputs({s}, {stream_str})"),
            stream,
        )
    }

    #[inline]
    pub(super) fn transform_puts(&self, s: &Expr, ic: IndicatorCheck<'_>) -> Expr {
        let s = pprust::expr_to_string(s);
        self.lib_items.borrow_mut().push(LibItem::Puts);
        self.update_error_no_eof(
            ic,
            format!("crate::stdio::rs_puts({s})"),
            &StdExpr::stdout(),
        )
    }

    #[inline]
    pub(super) fn transform_perror(&self, s: &Expr) -> Expr {
        let s = pprust::expr_to_string(s);
        self.lib_items.borrow_mut().push(LibItem::Perror);
        expr!("crate::stdio::rs_perror({})", s)
    }
}

pub(super) static FPUTS: &str = r#"
#[inline]
pub(crate) unsafe fn rs_fputs<W: std::io::Write>(s: *const i8, mut stream: W) -> (i32, i32) {
    match stream.write_all(std::ffi::CStr::from_ptr(s as _).to_bytes()) {
        Ok(_) => (0, 0),
        Err(_) => (libc::EOF, 1),
    }
}
"#;

pub(super) static PUTS: &str = r#"
#[inline]
pub(crate) unsafe fn rs_puts(s: *const i8) -> (i32, i32) {
    use std::io::Write as _;
    let mut stream = std::io::stdout();
    match stream
        .write_all(std::ffi::CStr::from_ptr(s as _).to_bytes())
        .and_then(|_| stream.write_all(b"\n"))
    {
        Ok(_) => (0, 0),
        Err(_) => (libc::EOF, 1),
    }
}
"#;

pub(super) static PERROR: &str = r#"
#[inline]
pub(crate) unsafe fn rs_perror(s: *const i8) {
    use std::io::Write as _;
    let mut stream = std::io::stderr();
    let _ = if s.is_null() || *s == 0 {
        writeln!(stream)
    } else {
        let s = std::ffi::CStr::from_ptr(s as _);
        if let Ok(s) = s.to_str() {
            writeln!(stream, "{s}: ")
        } else {
            stream
                .write_all(s.to_bytes())
                .and_then(|_| writeln!(stream, ": "))
        }
    };
}
"#;
