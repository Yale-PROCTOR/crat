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
        let ptr_str = pprust::expr_to_string(ptr);
        let size = pprust::expr_to_string(size);
        let nitems = pprust::expr_to_string(nitems);
        self.lib_items.borrow_mut().insert(LibItem::Fwrite);

        if let Some((array, ty)) = self.array_of_as_ptr(ptr) {
            if ty == self.tcx.types.i8 {
                let array = pprust::expr_to_string(array);
                self.bytemuck.set(true);
                let code = format!(
                    "
    {{
        let ___size = {size};
        crate::c_lib::rs_fwrite(
            bytemuck::cast_slice(&({array})[..(___size * ({nitems})) as usize]),
            ___size,
            {stream_str}
        )
    }}"
                );
                return self.update_error_no_eof(ic, code, stream);
            } else if ty == self.tcx.types.u8 {
                let array = pprust::expr_to_string(array);
                let code = format!(
                    "
    {{
        let ___size = {size};
        crate::c_lib::rs_fwrite(
            &({array})[..(___size * ({nitems})) as usize],
            ___size,
            {stream_str}
        )
    }}"
                );
                return self.update_error_no_eof(ic, code, stream);
            }
        }

        self.update_error_no_eof(
            ic,
            format!(
                "
    {{
        let ___size = {size};
        crate::c_lib::rs_fwrite(
            std::slice::from_raw_parts(({ptr_str}) as _, (___size * ({nitems})) as usize),
            ___size,
            {stream_str}
        )
    }}"
            ),
            stream,
        )
    }
}

pub(super) static FWRITE: &str = r#"
pub(crate) fn rs_fwrite<W: std::io::Write>(
    mut buf: &[u8],
    size: u64,
    mut stream: W,
) -> (u64, i32) {
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

pub(super) static FWRITE_UNCHECKED: &str = r#"
pub(crate) unsafe fn rs_fwrite_unchecked<W: std::io::Write>(
    ptr: *const std::ffi::c_void,
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
