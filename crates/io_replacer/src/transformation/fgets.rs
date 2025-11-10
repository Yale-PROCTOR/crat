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
    pub(super) fn transform_fgets<S: StreamExpr>(
        &self,
        stream: &S,
        s: &Expr,
        n: &Expr,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream_str = stream.borrow_for(StreamTrait::BufRead);
        let s_str = pprust::expr_to_string(s);
        let n_str = pprust::expr_to_string(n);
        let err_eof_args = self.err_eof_args(ic);
        self.lib_items.borrow_mut().insert(LibItem::Fgets);

        if let Some(array) = self.i8_array_of_as_mut_ptr(s) {
            let array = pprust::expr_to_string(array);
            return expr!(
                "crate::stdio::rs_fgets(
                    &mut ({array})[..({n_str}) as usize],
                    {stream_str},
                    {err_eof_args},
                )"
            );
        }

        expr!(
            "crate::stdio::rs_fgets(
                std::slice::from_raw_parts_mut(({s_str}) as _, ({n_str}) as _),
                {stream_str},
                {err_eof_args},
            )"
        )
    }
}

pub(super) static FGETS: &str = r#"
pub(crate) fn rs_fgets<R: std::io::BufRead>(
    s: &mut [i8],
    mut stream: R,
    err: Option<&mut i32>,
    eof: Option<&mut i32>,
) -> *mut i8 {
    let mut pos = 0;
    while pos < s.len() - 1 {
        let available = match stream.fill_buf() {
            Ok(buf) => buf,
            Err(e) => {
                if e.kind() == std::io::ErrorKind::UnexpectedEof {
                    if let Some(eof) = eof {
                        *eof = 1;
                    }
                } else if let Some(err) = err {
                    *err = 1;
                }
                return std::ptr::null_mut();
            }
        };
        if available.is_empty() {
            break;
        }
        s[pos] = available[0] as i8;
        stream.consume(1);
        pos += 1;
        if s[pos - 1] == b'\n' as i8 {
            break;
        }
    }
    if pos == 0 {
        std::ptr::null_mut()
    } else {
        s[pos] = 0;
        s.as_mut_ptr()
    }
}
"#;
