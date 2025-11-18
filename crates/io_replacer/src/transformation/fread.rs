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
        let ptr_str = pprust::expr_to_string(ptr);
        let size = pprust::expr_to_string(size);
        let nitems = pprust::expr_to_string(nitems);
        let err_eof_args = self.err_eof_args(ic);
        self.lib_items.borrow_mut().insert(LibItem::Fread);

        if let Some((array, signed)) = self.byte_array_of_as_mut_ptr(ptr) {
            let array = pprust::expr_to_string(array);
            if signed {
                self.bytemuck.set(true);
                return expr!(
                    "
    {{
        let ___size = {size};
        crate::stdio::rs_fread(
            bytemuck::cast_slice_mut(&mut ({array})[..(___size * ({nitems})) as usize]),
            ___size as _,
            {stream_str},
            {err_eof_args},
        )
    }}"
                );
            } else {
                return expr!(
                    "
    {{
        let ___size = {size};
        crate::stdio::rs_fread(
            &mut ({array})[..(___size * ({nitems})) as usize],
            ___size as _,
            {stream_str},
            {err_eof_args},
        )
    }}"
                );
            }
        }

        expr!(
            "
    {{
        let ___size = {size};
        crate::stdio::rs_fread(
            std::slice::from_raw_parts_mut(({ptr_str}) as _, (___size * ({nitems})) as usize),
            ___size as _,
            {stream_str},
            {err_eof_args},
        )
    }}"
        )
    }
}

pub(super) static FREAD: &str = r#"
pub(crate) fn rs_fread<R: std::io::Read>(
    mut buf: &mut [u8],
    size: u64,
    mut stream: R,
    err: Option<&mut i32>,
    eof: Option<&mut i32>,
) -> u64 {
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
