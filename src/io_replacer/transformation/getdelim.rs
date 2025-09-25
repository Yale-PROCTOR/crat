use rustc_ast::*;
use rustc_ast_pretty::pprust;

use super::{
    stream_ty::*,
    transform::LibItem,
    visitor::{IndicatorCheck, TransformVisitor},
};

impl TransformVisitor<'_, '_, '_> {
    #[inline]
    pub(super) fn transform_getdelim<S: StreamExpr>(
        &self,
        stream: &S,
        lineptr: &Expr,
        n: &Expr,
        delimiter: &Expr,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream_str = stream.borrow_for(StreamTrait::BufRead);
        let lineptr = pprust::expr_to_string(lineptr);
        let n = pprust::expr_to_string(n);
        let delimiter = pprust::expr_to_string(delimiter);
        let err_eof_args = self.err_eof_args(ic);
        self.lib_items.borrow_mut().push(LibItem::Getdelim);
        expr!(
            "crate::stdio::rs_getdelim({lineptr}, {n}, {delimiter}, {stream_str}, {err_eof_args})"
        )
    }

    #[inline]
    pub(super) fn transform_getline<S: StreamExpr>(
        &self,
        stream: &S,
        lineptr: &Expr,
        n: &Expr,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream_str = stream.borrow_for(StreamTrait::BufRead);
        let lineptr = pprust::expr_to_string(lineptr);
        let n = pprust::expr_to_string(n);
        let err_eof_args = self.err_eof_args(ic);
        self.lib_items.borrow_mut().push(LibItem::Getdelim);
        self.lib_items.borrow_mut().push(LibItem::Getline);
        expr!("crate::stdio::rs_getline({lineptr}, {n}, {stream_str}, {err_eof_args})")
    }
}

pub(super) static GETDELIM: &str = r#"
pub(crate) unsafe fn rs_getdelim<R: std::io::BufRead>(
    lineptr: *mut *mut i8,
    n: *mut u64,
    delimiter: i32,
    mut stream: R,
    err: Option<&mut i32>,
    eof: Option<&mut i32>,
) -> i64 {
    let mut buf = Vec::new();
    match stream.read_until(delimiter as _, &mut buf) {
        Ok(_) => {
            let len = buf.len();
            if len == 0 {
                return -1;
            }
            buf.push(0);
            if (*lineptr).is_null() {
                *lineptr = libc::malloc(buf.len() as _) as _;
                *n = buf.len() as _;
            } else if buf.len() > *n as _ {
                *lineptr = libc::realloc(*lineptr as _, buf.len() as _) as _;
                *n = buf.len() as _;
            }
            let ptr: &mut [u8] = std::slice::from_raw_parts_mut(*lineptr as _, buf.len());
            ptr.copy_from_slice(&buf);
            len as _
        }
        Err(e) => {
            if e.kind() == std::io::ErrorKind::UnexpectedEof {
                if let Some(eof) = eof {
                    *eof = 1;
                }
            } else if let Some(err) = err {
                *err = 1;
            }
            -1
        }
    }
}
"#;

pub(super) const GETLINE: &str = r#"
#[inline]
pub(crate) unsafe fn rs_getline<R: std::io::BufRead>(
    lineptr: *mut *mut i8,
    n: *mut u64,
    stream: R,
    err: Option<&mut i32>,
    eof: Option<&mut i32>,
) -> i64 {
    rs_getdelim(lineptr, n, b'\n' as _, stream, err, eof)
}
"#;
