use rustc_ast::*;
use rustc_ast_pretty::pprust;
use utils::expr;

use super::{likely_lit::LikelyLit, stream_ty::*, transform::LibItem, visitor::TransformVisitor};

impl TransformVisitor<'_, '_, '_> {
    #[inline]
    pub(super) fn transform_fseek<S: StreamExpr>(
        &self,
        stream: &S,
        off: &Expr,
        whence: &Expr,
    ) -> Expr {
        let stream = stream.borrow_for(StreamTrait::Seek);
        let off = pprust::expr_to_string(off);
        let whence = LikelyLit::from_expr(whence);
        match whence {
            LikelyLit::Lit(lit) => {
                let v = match lit.as_str() {
                    "0" => "Start",
                    "1" => "Current",
                    "2" => "End",
                    lit => panic!("{}", lit),
                };
                self.lib_items.borrow_mut().push(LibItem::Seek);
                expr!(
                    "crate::stdio::rs_seek({}, std::io::SeekFrom::{}(({}) as _))",
                    stream,
                    v,
                    off
                )
            }
            LikelyLit::If(_, _, _) => todo!(),
            LikelyLit::Path(path, _) => {
                self.lib_items.borrow_mut().push(LibItem::Fseek);
                expr!("crate::stdio::rs_fseek({}, {}, {})", stream, off, path)
            }
            LikelyLit::Other(_) => todo!(),
        }
    }

    #[inline]
    pub(super) fn transform_ftell<S: StreamExpr>(&self, stream: &S) -> Expr {
        let stream = stream.borrow_for(StreamTrait::Seek);
        self.lib_items.borrow_mut().push(LibItem::Ftell);
        expr!("crate::stdio::rs_ftell({})", stream)
    }

    #[inline]
    pub(super) fn transform_rewind<S: StreamExpr>(&self, stream: &S) -> Expr {
        let stream = stream.borrow_for(StreamTrait::Seek);
        self.lib_items.borrow_mut().push(LibItem::Rewind);
        expr!("crate::stdio::rs_rewind({})", stream)
    }
}

pub(super) static SEEK: &str = r#"
#[inline]
pub(crate) fn rs_seek<S: std::io::Seek>(mut stream: S, seek_from: std::io::SeekFrom) -> i32 {
    stream.seek(seek_from).map_or(-1, |_| 0)
}
"#;

pub(super) static FSEEK: &str = r#"
#[inline]
pub(crate) fn rs_fseek<S: std::io::Seek>(mut stream: S, offset: i64, whence: i32) -> i32 {
    let seek_from = match whence {
        0 => std::io::SeekFrom::Start(offset as _),
        1 => std::io::SeekFrom::Current(offset),
        2 => std::io::SeekFrom::End(offset),
        _ => panic!(),
    };
    stream.seek(seek_from).map_or(-1, |_| 0)
}
"#;

pub(super) static FTELL: &str = r#"
#[inline]
pub(crate) fn rs_ftell<S: std::io::Seek>(mut stream: S) -> i64 {
    stream.stream_position().map_or(-1, |pos| pos as i64)
}
"#;

pub(super) static REWIND: &str = r#"
#[inline]
pub(crate) fn rs_rewind<S: std::io::Seek>(mut stream: S) {
    let _ = stream.rewind();
}
"#;
