use rustc_ast::*;
use rustc_ast_pretty::pprust;
use utils::expr;

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
        let s_str = pprust::expr_to_string(s);
        self.lib_items.borrow_mut().insert(LibItem::Fputs);

        if let Some((array, signed)) = self.byte_array_of_as_mut_ptr(s) {
            let array = pprust::expr_to_string(array);
            self.bytemuck.set(true);
            let e = if signed {
                format!(
                    "crate::stdio::rs_fputs(
                        std::ffi::CStr::from_bytes_until_nul(
                            bytemuck::cast_slice(&({array}))
                        ).unwrap(),
                        {stream_str},
                    )"
                )
            } else {
                format!(
                    "crate::stdio::rs_fputs(
                        std::ffi::CStr::from_bytes_until_nul(&({array})).unwrap(),
                        {stream_str},
                    )"
                )
            };
            return self.update_error_no_eof(ic, e, stream);
        }

        self.update_error_no_eof(
            ic,
            format!(
                "crate::stdio::rs_fputs(std::ffi::CStr::from_ptr(({s_str}) as _), {stream_str})"
            ),
            stream,
        )
    }

    #[inline]
    pub(super) fn transform_puts(&self, s: &Expr, ic: IndicatorCheck<'_>) -> Expr {
        let s_str = pprust::expr_to_string(s);
        self.lib_items.borrow_mut().insert(LibItem::Puts);

        if let Some((array, signed)) = self.byte_array_of_as_mut_ptr(s) {
            let array = pprust::expr_to_string(array);
            self.bytemuck.set(true);
            let e = if signed {
                format!(
                    "crate::stdio::rs_puts(
                        std::ffi::CStr::from_bytes_until_nul(
                            bytemuck::cast_slice(&({array}))
                        ).unwrap(),
                    )"
                )
            } else {
                format!(
                    "crate::stdio::rs_puts(
                        std::ffi::CStr::from_bytes_until_nul(&({array})).unwrap(),
                    )"
                )
            };
            return self.update_error_no_eof(ic, e, &StdExpr::stdout());
        }

        self.update_error_no_eof(
            ic,
            format!("crate::stdio::rs_puts(std::ffi::CStr::from_ptr(({s_str}) as _))"),
            &StdExpr::stdout(),
        )
    }

    #[inline]
    pub(super) fn transform_perror(&self, s: &Expr) -> Expr {
        let s = pprust::expr_to_string(s);
        self.lib_items.borrow_mut().insert(LibItem::Perror);
        expr!("crate::stdio::rs_perror({})", s)
    }
}

pub(super) static FPUTS: &str = r#"
#[inline]
pub(crate) fn rs_fputs<W: std::io::Write>(s: &std::ffi::CStr, mut stream: W) -> (i32, i32) {
    match stream.write_all(s.to_bytes()) {
        Ok(_) => (0, 0),
        Err(_) => (-1, 1),
    }
}
"#;

pub(super) static FPUTS_UNCHECKED: &str = r#"
#[inline]
pub(crate) unsafe fn rs_fputs_unchecked<W: std::io::Write>(s: *const i8, mut stream: W) -> (i32, i32) {
    match stream.write_all(std::ffi::CStr::from_ptr(s as _).to_bytes()) {
        Ok(_) => (0, 0),
        Err(_) => (-1, 1),
    }
}
"#;

pub(super) static PUTS: &str = r#"
#[inline]
pub(crate) fn rs_puts(s: &std::ffi::CStr) -> (i32, i32) {
    use std::io::Write as _;
    let mut stream = std::io::stdout();
    match stream
        .write_all(s.to_bytes())
        .and_then(|_| stream.write_all(b"\n"))
    {
        Ok(_) => (0, 0),
        Err(_) => (-1, 1),
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
