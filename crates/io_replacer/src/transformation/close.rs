use rustc_ast::*;
use rustc_ast_pretty::pprust;
use utils::expr;

use super::{stream_ty::StreamType, transform::LibItem, visitor::TransformVisitor};

impl TransformVisitor<'_, '_, '_> {
    #[inline]
    pub(super) fn transform_fclose(
        &self,
        stream: &Expr,
        ty: StreamType<'_>,
        is_non_local: bool,
    ) -> Expr {
        let stream = take_stream(stream, ty, is_non_local);
        let v = if ty.can_flush() {
            "std::io::Write::flush(&mut __x).map_or(-1, |_| 0)"
        } else {
            "0"
        };
        expr!(
            "{{
    let mut __x = {};
    let __v = {};
    drop(__x);
    __v
}}",
            stream,
            v,
        )
    }

    #[inline]
    pub(super) fn transform_pclose(
        &self,
        stream: &Expr,
        ty: StreamType<'_>,
        is_non_local: bool,
    ) -> Expr {
        let stream = take_stream(stream, ty, is_non_local);
        self.lib_items.borrow_mut().insert(LibItem::Close);
        expr!(
            "{{
    let mut __x = {};
    let __v = crate::stdio::Close::close(&mut __x);
    drop(__x);
    __v
}}",
            stream,
        )
    }
}

fn take_stream(stream_expr: &Expr, ty: StreamType<'_>, is_non_local: bool) -> String {
    let stream = pprust::expr_to_string(stream_expr);
    match ty {
        StreamType::Ref(_) | StreamType::Ptr(_) => panic!(),
        StreamType::Option(_) => {
            if is_non_local || matches!(stream_expr.kind, ExprKind::Index(_, _, _)) {
                format!("({stream}).take().unwrap()")
            } else {
                format!("({stream}).unwrap()")
            }
        }
        StreamType::ManuallyDrop(StreamType::Option(_)) => {
            format!("std::mem::ManuallyDrop::take(&mut ({stream})).take().unwrap()")
        }
        StreamType::ManuallyDrop(_) => {
            format!("std::mem::ManuallyDrop::take(&mut ({stream}))")
        }
        _ => stream,
    }
}

pub(super) const CLOSE: &str = r#"
pub trait Close {
    fn close(&mut self) -> i32;
}
impl Close for std::fs::File {
    fn close(&mut self) -> i32 {
        0
    }
}
impl Close for std::io::Stdin {
    fn close(&mut self) -> i32 {
        0
    }
}
impl Close for std::io::Stdout {
    fn close(&mut self) -> i32 {
        0
    }
}
impl Close for std::io::Stderr {
    fn close(&mut self) -> i32 {
        0
    }
}
impl<T: Close> Close for std::io::BufReader<T> {
    fn close(&mut self) -> i32 {
        self.get_mut().close()
    }
}
impl<T: Close + std::io::Write> Close for std::io::BufWriter<T> {
    fn close(&mut self) -> i32 {
        self.get_mut().close()
    }
}
impl<T: Close + ?Sized> Close for Box<T> {
    fn close(&mut self) -> i32 {
        self.as_mut().close()
    }
}
"#;
