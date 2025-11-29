use rustc_ast::*;
use utils::expr;

use super::{
    stream_ty::*,
    transform::LibItem,
    visitor::{IndicatorCheck, TransformVisitor},
};

impl TransformVisitor<'_, '_, '_> {
    #[inline]
    pub(super) fn transform_fgetc<S: StreamExpr>(
        &self,
        stream: &S,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream_str = stream.borrow_for(StreamTrait::Read);
        let err_eof_args = self.err_eof_args(ic);
        self.lib_items.borrow_mut().insert(LibItem::Fgetc);
        expr!("crate::c_lib::rs_fgetc({stream_str}, {err_eof_args})")
    }
}

pub(super) static FGETC: &str = r#"
#[inline]
pub(crate) fn rs_fgetc<R: std::io::Read>(
    mut stream: R,
    err: Option<&mut i32>,
    eof: Option<&mut i32>,
) -> i32 {
    let mut buf = [0];
    match stream.read_exact(&mut buf) {
        Ok(_) => buf[0] as i32,
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
