use rustc_ast::*;
use rustc_ast_pretty::pprust;

use super::{
    stream_ty::*,
    transform::LibItem,
    visitor::{IndicatorCheck, TransformVisitor},
};

impl TransformVisitor<'_, '_, '_> {
    #[inline]
    pub(super) fn transform_fwrite<S: StreamExpr>(
        &self,
        stream: &S,
        ptr: &Expr,
        size: &Expr,
        nitems: &Expr,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream_str = stream.borrow_for(StreamTrait::Write);
        let ptr = pprust::expr_to_string(ptr);
        let size = pprust::expr_to_string(size);
        let nitems = pprust::expr_to_string(nitems);
        self.lib_items.borrow_mut().push(LibItem::Fwrite);
        self.update_error_no_eof(
            ic,
            format!("crate::stdio::rs_fwrite({ptr}, {size}, {nitems}, {stream_str})"),
            stream,
        )
    }
}

pub(super) static FWRITE: &str = r#"
pub(crate) unsafe fn rs_fwrite<W: std::io::Write>(
    ptr: *const libc::c_void,
    size: u64,
    nitems: u64,
    mut stream: W,
) -> (u64, i32) {
    let mut buf: &[u8] = std::slice::from_raw_parts(ptr as _, (size * nitems) as usize);
    let mut i = 0;
    while !buf.is_empty() {
        match stream.write(buf) {
            Ok(0) => {
                return (i / size, 1);
            }
            Ok(n) => {
                buf = &buf[n..];
                i += n as u64;
            }
            Err(e) => {
                if e.kind() != std::io::ErrorKind::Interrupted {
                    return (i / size, 1);
                }
            }
        }
    }
    (i / size, 0)
}
"#;
