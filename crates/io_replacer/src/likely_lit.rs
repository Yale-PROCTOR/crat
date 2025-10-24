use rustc_ast::*;
use rustc_span::{Span, Symbol};

#[derive(Debug)]
pub(super) enum LikelyLit<'a> {
    Lit(Symbol),
    If(&'a Expr, Box<LikelyLit<'a>>, Box<LikelyLit<'a>>),
    Path(Symbol, Span),
    #[allow(dead_code)]
    Other(&'a Expr),
}

impl<'a> LikelyLit<'a> {
    pub(super) fn from_expr(expr: &'a Expr) -> Self {
        match &expr.kind {
            ExprKind::MethodCall(box MethodCall { receiver: e, .. }) | ExprKind::Cast(e, _) => {
                Self::from_expr(e)
            }
            ExprKind::Lit(lit) => LikelyLit::Lit(lit.symbol),
            ExprKind::If(c, t, Some(f)) => {
                let [t] = &t.stmts[..] else { panic!() };
                let StmtKind::Expr(t) = &t.kind else { panic!() };
                let t = Self::from_expr(t);
                let f = Self::from_expr(f);
                LikelyLit::If(c, Box::new(t), Box::new(f))
            }
            ExprKind::Call(callee, args) => {
                if let ExprKind::Path(_, path) = &callee.kind {
                    let callee = path.segments.last().unwrap().ident.name.as_str();
                    match callee {
                        "dcgettext" => Self::from_expr(&args[1]),
                        "transmute" => Self::from_expr(&args[0]),
                        _ => LikelyLit::Other(expr),
                    }
                } else {
                    LikelyLit::Other(expr)
                }
            }
            ExprKind::Paren(e) => Self::from_expr(e),
            ExprKind::Unary(UnOp::Deref, e) => Self::from_expr(e),
            ExprKind::AddrOf(_, _, e) => Self::from_expr(e),
            ExprKind::Path(_, path) => {
                let symbol = path.segments.last().unwrap().ident.name;
                LikelyLit::Path(symbol, path.span)
            }
            ExprKind::Block(block, _) => {
                let [.., stmt] = &block.stmts[..] else { return LikelyLit::Other(expr) };
                let StmtKind::Expr(expr) = &stmt.kind else { return LikelyLit::Other(expr) };
                Self::from_expr(expr)
            }
            _ => LikelyLit::Other(expr),
        }
    }
}
