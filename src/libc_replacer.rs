use rustc_ast::{
    ast::*,
    mut_visit::{self, MutVisitor},
};
use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;

use crate::ast_util;

pub fn run(tcx: TyCtxt<'_>) {
    ast_util::transform_ast(
        |krate| {
            let mut visitor = TransformVisitor::default();
            visitor.visit_crate(krate);
            visitor.updated
        },
        tcx,
    )
    .apply();
}

#[derive(Default)]
struct TransformVisitor {
    updated: bool,
}

impl MutVisitor for TransformVisitor {
    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        if let ExprKind::Call(func, args) = &expr.kind
            && let ExprKind::Path(None, path) = &func.kind
            && let [seg] = path.segments.as_slice()
        {
            match seg.ident.as_str() {
                "tolower" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = self.expr_to_parenthesized_string(arg);
                    self.replace_expr(
                        expr,
                        expr!("(({arg} as u8 as char).to_ascii_lowercase() as i32)"),
                    );
                }
                "toupper" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = self.expr_to_parenthesized_string(arg);
                    self.replace_expr(
                        expr,
                        expr!("(({arg} as u8 as char).to_ascii_uppercase() as i32)"),
                    );
                }
                "exp" | "expf" | "expl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = self.expr_to_parenthesized_string(arg);
                    self.replace_expr(expr, expr!("{arg}.exp()"));
                }
                "fabs" | "fabsf" | "fabsl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = self.expr_to_parenthesized_string(arg);
                    self.replace_expr(expr, expr!("{arg}.abs()"));
                }
                "floor" | "floorf" | "floorl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = self.expr_to_parenthesized_string(arg);
                    self.replace_expr(expr, expr!("{arg}.floor()"));
                }
                "fmod" | "fmodf" | "fmodl" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    let arg1 = self.expr_to_parenthesized_string(arg1);
                    let arg2 = self.expr_to_parenthesized_string(arg2);
                    self.replace_expr(expr, expr!("({arg1} % {arg2})"));
                }
                "pow" | "powf" | "powl" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    let arg1 = self.expr_to_parenthesized_string(arg1);
                    let arg2 = self.expr_to_string(arg2);
                    self.replace_expr(expr, expr!("{arg1}.powf({arg2})"));
                }
                "sqrt" | "sqrtf" | "sqrtl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = self.expr_to_parenthesized_string(arg);
                    self.replace_expr(expr, expr!("{arg}.sqrt()"));
                }
                "div" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    let arg1 = self.expr_to_string(arg1);
                    let arg2 = self.expr_to_string(arg2);
                    self.replace_expr(
                        expr,
                        expr!(
                            "{{
                            let lhs = {arg1};
                            let rhs = {arg2};
                            div_t {{ quot: lhs / rhs, rem: lhs % rhs }}
                        }}"
                        ),
                    );
                }
                "abort" => {
                    self.replace_expr(expr, expr!("std::process::abort()"));
                }
                _ => {}
            }
        }

        if let ExprKind::Binary(op, lhs, rhs) = &expr.kind
            && op.node == BinOpKind::BitAnd
            && let ExprKind::Cast(lhs, _) = &lhs.kind
            && let ExprKind::Unary(UnOp::Deref, box lhs) = &lhs.kind
            && let ExprKind::MethodCall(box MethodCall {
                seg,
                receiver,
                args,
                ..
            }) = &lhs.kind
            && seg.ident.as_str() == "offset"
            && let ExprKind::Paren(receiver) = &receiver.kind
            && let ExprKind::Unary(UnOp::Deref, box receiver) = &receiver.kind
            && let ExprKind::Call(func, _) = &receiver.kind
            && let ExprKind::Path(None, path) = &func.kind
            && let [seg] = path.segments.as_slice()
            && seg.ident.as_str() == "__ctype_b_loc"
            && let [arg] = args.as_slice()
            && let ExprKind::Path(None, path) = &unwrap_cast(rhs).kind
            && let [flag] = path.segments.as_slice()
        {
            let arg = self.expr_to_parenthesized_string(unwrap_cast(arg));
            match flag.ident.as_str() {
                "_ISalnum" => {
                    self.replace_expr(
                        expr,
                        expr!("(({arg} as u8 as char).is_alphanumeric() as i32)"),
                    );
                }
                "_ISalpha" => {
                    self.replace_expr(
                        expr,
                        expr!("(({arg} as u8 as char).is_alphabetic() as i32)"),
                    );
                }
                "_ISlower" => {
                    self.replace_expr(expr, expr!("(({arg} as u8 as char).is_lowercase() as i32)"));
                }
                "_ISupper" => {
                    self.replace_expr(expr, expr!("(({arg} as u8 as char).is_uppercase() as i32)"));
                }
                "_ISdigit" => {
                    self.replace_expr(
                        expr,
                        expr!("(({arg} as u8 as char).is_ascii_digit() as i32)"),
                    );
                }
                "_ISxdigit" => {
                    self.replace_expr(
                        expr,
                        expr!("(({arg} as u8 as char).is_ascii_hexdigit() as i32)"),
                    );
                }
                "_IScntrl" => {
                    self.replace_expr(
                        expr,
                        expr!("(({arg} as u8 as char).is_ascii_control() as i32)"),
                    );
                }
                "_ISgraph" => {
                    self.replace_expr(
                        expr,
                        expr!("(({arg} as u8 as char).is_ascii_graphic() as i32)"),
                    );
                }
                "_ISspace" => {
                    self.replace_expr(
                        expr,
                        expr!("(({arg} as u8 as char).is_ascii_whitespace() as i32)"),
                    );
                }
                "_ISblank" => {
                    self.replace_expr(
                        expr,
                        expr!("matches!({arg} as u8 as char, ' ' | '\\t') as i32"),
                    );
                }
                "_ISprint" => {
                    self.replace_expr(
                        expr,
                        expr!("((({arg} as u8 as char).is_ascii() && !({arg} as u8 as char).is_ascii_control()) as i32)"),
                    );
                }
                "_ISpunct" => {
                    self.replace_expr(
                        expr,
                        expr!("((({arg} as u8 as char).is_ascii_punctuation()) as i32)"),
                    );
                }
                _ => {}
            }
        }
    }
}

impl TransformVisitor {
    fn replace_expr(&mut self, expr: &mut Expr, new: Expr) {
        *expr = new;
        self.updated = true;
    }

    fn expr_to_string(&self, expr: &Expr) -> String {
        pprust::expr_to_string(expr)
    }

    fn expr_to_parenthesized_string(&self, expr: &Expr) -> String {
        let s = self.expr_to_string(expr);
        if need_paren(expr) {
            format!("({s})")
        } else {
            s
        }
    }
}

#[inline]
fn need_paren(expr: &Expr) -> bool {
    !matches!(
        expr.kind,
        ExprKind::Array(..)
            | ExprKind::Call(..)
            | ExprKind::MethodCall(..)
            | ExprKind::Tup(..)
            | ExprKind::Lit(..)
            | ExprKind::Field(..)
            | ExprKind::Index(..)
            | ExprKind::Path(..)
            | ExprKind::Struct(..)
            | ExprKind::Repeat(..)
            | ExprKind::Paren(..)
            | ExprKind::FormatArgs(..)
    )
}

fn unwrap_cast(expr: &Expr) -> &Expr {
    if let ExprKind::Cast(inner, _) = &expr.kind {
        unwrap_cast(inner)
    } else {
        expr
    }
}
