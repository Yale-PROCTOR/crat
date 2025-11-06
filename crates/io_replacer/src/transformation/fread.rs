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
    pub(super) fn transform_fread<S: StreamExpr>(
        &self,
        stream: &S,
        ptr: &Expr,
        size: &Expr,
        nitems: &Expr,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream_str = stream.borrow_for(StreamTrait::Read);
        let ptr = pprust::expr_to_string(ptr);
        let size = pprust::expr_to_string(size);
        let nitems = pprust::expr_to_string(nitems);
        let err_eof_args = self.err_eof_args(ic);
        self.lib_items.borrow_mut().insert(LibItem::Fread);
        expr!("crate::stdio::rs_fread({ptr}, {size}, {nitems}, {stream_str}, {err_eof_args})")
    }
}

pub(super) static FREAD: &str = r#"
pub(crate) unsafe fn rs_fread<R: std::io::Read>(
    ptr: *mut libc::c_void,
    size: u64,
    nitems: u64,
    mut stream: R,
    err: Option<&mut i32>,
    eof: Option<&mut i32>,
) -> u64 {
    let mut buf: &mut [u8] = std::slice::from_raw_parts_mut(ptr as _, (size * nitems) as usize);
    let mut i = 0;
    while !buf.is_empty() {
        match stream.read(buf) {
            Ok(0) => {
                if let Some(eof) = eof {
                    *eof = 1;
                }
                break;
            }
            Ok(n) => {
                buf = &mut buf[n..];
                i += n as u64;
            }
            Err(e) => match e.kind() {
                std::io::ErrorKind::Interrupted => {}
                std::io::ErrorKind::UnexpectedEof => {
                    if let Some(eof) = eof {
                        *eof = 1;
                    }
                    break;
                }
                _ => {
                    if let Some(err) = err {
                        *err = 1;
                    }
                    break;
                }
            },
        }
    }
    i / size
}
"#;
