use rustc_ast::{
    mut_visit::{self, MutVisitor},
    ptr::P,
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::HirId;
use rustc_middle::ty::TyCtxt;
use thin_vec::ThinVec;
use utils::expr;

use crate::libc_replacer::errno::ErrorCode;

mod errno;
mod strto;

#[derive(Debug)]
pub struct TransformationResult {
    pub code: String,
    pub bytemuck: bool,
    pub num_traits: bool,
}

pub fn replace_libc(tcx: TyCtxt<'_>) -> TransformationResult {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let errno_calls = errno::find_errno_calls(tcx);
    let source_nums = errno_calls
        .sources
        .iter()
        .filter(|call| {
            let name = call.name.as_str();
            name == "strtod" || name == "strtol" || name == "strtoul"
        })
        .enumerate()
        .map(|(i, call)| (call.hir_id, i))
        .collect();

    let mut visitor = TransformVisitor {
        tcx,
        ast_to_hir,
        errno_calls,
        source_nums,
        lib_items: FxHashSet::default(),
        bytemuck: false,
        num_traits: false,
    };
    visitor.visit_crate(&mut krate);

    let lib_items = krate.items.iter_mut().find_map(|item| {
        if let ItemKind::Mod(_, ident, ModKind::Loaded(items, _, _, _)) = &mut item.kind
            && ident.name.as_str() == "c_lib"
        {
            Some(items)
        } else {
            None
        }
    });
    if let Some(lib_items) = lib_items {
        let items: FxHashSet<_> = lib_items
            .iter()
            .filter_map(|item| {
                if let ItemKind::Fn(f) = &item.kind {
                    Some(f.ident.name.as_str().to_string())
                } else {
                    None
                }
            })
            .collect();
        for item in visitor.lib_items {
            if !items.contains(item.as_str()) {
                let item = utils::item!("{}", item.get_impl());
                lib_items.push(P(item));
            }
        }
    } else {
        let mut code = "mod c_lib {".to_string();
        for item in visitor.lib_items {
            code.push_str(item.get_impl());
        }
        code.push('}');
        krate.items.push(P(utils::item!("{}", code)));
    }

    let code = pprust::crate_to_string_for_macros(&krate);
    TransformationResult {
        code,
        bytemuck: visitor.bytemuck,
        num_traits: visitor.num_traits,
    }
}

struct TransformVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: utils::ir::AstToHir,
    errno_calls: errno::ErrnoCalls,
    source_nums: FxHashMap<HirId, usize>,
    lib_items: FxHashSet<LibItem>,
    bytemuck: bool,
    num_traits: bool,
}

impl MutVisitor for TransformVisitor<'_> {
    fn flat_map_stmt(&mut self, stmt: Stmt) -> smallvec::SmallVec<[Stmt; 1]> {
        let mut stmts = mut_visit::walk_flat_map_stmt(self, stmt);
        stmts.retain(|stmt| {
            if let StmtKind::Semi(expr) = &stmt.kind
                && let Some(hir_id) = self.ast_to_hir.local_map.get(&expr.id)
                && self.errno_calls.assigns.contains(hir_id)
            {
                false
            } else {
                true
            }
        });
        stmts
    }

    fn visit_item(&mut self, item: &mut Item) {
        mut_visit::walk_item(self, item);

        if let ItemKind::Fn(f) = &mut item.kind
            && let Some(body) = &mut f.body
            && let Some(local_def_id) = self.ast_to_hir.global_map.get(&item.id)
            && let nums = self
                .source_nums
                .iter()
                .filter(|(hir_id, _)| hir_id.owner.def_id == *local_def_id)
                .collect::<Vec<_>>()
            && !nums.is_empty()
        {
            let mut stmts: ThinVec<_> = nums
                .into_iter()
                .map(|(_, num)| utils::stmt!("let mut error{num} = false;"))
                .collect();
            stmts.append(&mut body.stmts);
            body.stmts = stmts;
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        if let ExprKind::Binary(_, _, _) = &expr.kind
            && let Some(hir_id) = self.ast_to_hir.local_map.get(&expr.id)
            && let Some(check) = self.errno_calls.checks.get(hir_id)
        {
            match check.source.name.as_str() {
                "pow" | "powf" | "powl" => {
                    if let Some(res) = check.source.destination {
                        let res = self.tcx.hir_name(res);
                        match (check.code, check.equals) {
                            (ErrorCode::None, true) => {
                                *expr = expr!("(!{res}.is_nan() && !{res}.is_infinite())");
                            }
                            (ErrorCode::None, false) => {
                                *expr = expr!("({res}.is_nan() || {res}.is_infinite())");
                            }
                            (ErrorCode::Edom, true) => {
                                *expr = expr!("{res}.is_nan()");
                            }
                            (ErrorCode::Edom, false) => {
                                *expr = expr!("!{res}.is_nan()");
                            }
                            (ErrorCode::Erange, true) => {
                                *expr = expr!("{res}.is_infinite()");
                            }
                            (ErrorCode::Erange, false) => {
                                *expr = expr!("!{res}.is_infinite()");
                            }
                        }
                    }
                }
                "strtod" | "strtol" | "strtoul" => {
                    let num = self.source_nums[&check.source.hir_id];
                    match (check.code, check.equals) {
                        (ErrorCode::None, true) | (ErrorCode::Erange, false) => {
                            *expr = expr!("!error{num}");
                        }
                        (ErrorCode::None, false) | (ErrorCode::Erange, true) => {
                            *expr = expr!("error{num}");
                        }
                        (ErrorCode::Edom, true) => {
                            *expr = expr!("false");
                        }
                        (ErrorCode::Edom, false) => {
                            *expr = expr!("true");
                        }
                    }
                }
                _ => {}
            }
        } else if let ExprKind::Call(func, args) = &expr.kind
            && let ExprKind::Path(None, path) = &func.kind
            && let [seg] = path.segments.as_slice()
        {
            match seg.ident.as_str() {
                "tolower" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = expr_to_parenthesized_string(arg);
                    *expr = expr!("(({arg} as u8 as char).to_ascii_lowercase() as i32)");
                }
                "toupper" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = expr_to_parenthesized_string(arg);
                    *expr = expr!("(({arg} as u8 as char).to_ascii_uppercase() as i32)");
                }
                "exp" | "expf" | "expl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = expr_to_parenthesized_string(arg);
                    *expr = expr!("{arg}.exp()");
                }
                "fabs" | "fabsf" | "fabsl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = expr_to_parenthesized_string(arg);
                    *expr = expr!("{arg}.abs()");
                }
                "floor" | "floorf" | "floorl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = expr_to_parenthesized_string(arg);
                    *expr = expr!("{arg}.floor()");
                }
                "fmod" | "fmodf" | "fmodl" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    let arg1 = expr_to_parenthesized_string(arg1);
                    let arg2 = expr_to_parenthesized_string(arg2);
                    *expr = expr!("({arg1} % {arg2})");
                }
                "pow" | "powf" | "powl" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    let arg1 = expr_to_parenthesized_string(arg1);
                    let arg2 = pprust::expr_to_string(arg2);
                    *expr = expr!("{arg1}.powf({arg2})");
                }
                "sqrt" | "sqrtf" | "sqrtl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = expr_to_parenthesized_string(arg);
                    *expr = expr!("{arg}.sqrt()");
                }
                "div" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    let arg1 = pprust::expr_to_string(arg1);
                    let arg2 = pprust::expr_to_string(arg2);
                    *expr = expr!(
                        "{{
                            let lhs = {arg1};
                            let rhs = {arg2};
                            div_t {{ quot: lhs / rhs, rem: lhs % rhs }}
                        }}"
                    );
                }
                "abort" => {
                    *expr = expr!("std::process::abort()");
                }
                "strtod" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    let num = self
                        .ast_to_hir
                        .local_map
                        .get(&expr.id)
                        .and_then(|hir_id| self.source_nums.get(hir_id));
                    *expr = self.transform_strtod(arg1, arg2, num.copied());
                }
                "strtol" => {
                    let [arg1, arg2, arg3] = args.as_slice() else { panic!() };
                    let num = self
                        .ast_to_hir
                        .local_map
                        .get(&expr.id)
                        .and_then(|hir_id| self.source_nums.get(hir_id));
                    *expr = self.transform_strtol(arg1, arg2, arg3, num.copied());
                }
                "strtoul" => {
                    let [arg1, arg2, arg3] = args.as_slice() else { panic!() };
                    let num = self
                        .ast_to_hir
                        .local_map
                        .get(&expr.id)
                        .and_then(|hir_id| self.source_nums.get(hir_id));
                    *expr = self.transform_strtoul(arg1, arg2, arg3, num.copied());
                }
                _ => {}
            }
        } else if let ExprKind::Binary(op, lhs, rhs) = &expr.kind
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
            let arg = expr_to_parenthesized_string(unwrap_cast(arg));
            match flag.ident.as_str() {
                "_ISalnum" => {
                    *expr = expr!("(({arg} as u8 as char).is_alphanumeric() as i32)");
                }
                "_ISalpha" => {
                    *expr = expr!("(({arg} as u8 as char).is_alphabetic() as i32)");
                }
                "_ISlower" => {
                    *expr = expr!("(({arg} as u8 as char).is_lowercase() as i32)");
                }
                "_ISupper" => {
                    *expr = expr!("(({arg} as u8 as char).is_uppercase() as i32)");
                }
                "_ISdigit" => {
                    *expr = expr!("(({arg} as u8 as char).is_ascii_digit() as i32)");
                }
                "_ISxdigit" => {
                    *expr = expr!("(({arg} as u8 as char).is_ascii_hexdigit() as i32)");
                }
                "_IScntrl" => {
                    *expr = expr!("(({arg} as u8 as char).is_ascii_control() as i32)");
                }
                "_ISgraph" => {
                    *expr = expr!("(({arg} as u8 as char).is_ascii_graphic() as i32)");
                }
                "_ISspace" => {
                    *expr = expr!("(({arg} as u8 as char).is_whitespace() as i32)");
                }
                "_ISblank" => {
                    *expr = expr!("matches!({arg} as u8 as char, ' ' | '\\t') as i32");
                }
                "_ISprint" => {
                    *expr = expr!(
                        "((({arg} as u8 as char).is_ascii() && !({arg} as u8 as char).is_ascii_control()) as i32)"
                    );
                }
                "_ISpunct" => {
                    *expr = expr!("((({arg} as u8 as char).is_ascii_punctuation()) as i32)");
                }
                _ => {}
            }
        }
    }
}

fn expr_to_parenthesized_string(expr: &Expr) -> String {
    let s = pprust::expr_to_string(expr);
    if need_paren(expr) {
        format!("({s})")
    } else {
        s
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum LibItem {
    Strtod,
    Strtol,
    Strtoul,
    Peek,
    ParseFloat,
    ParseInteger,
}

impl LibItem {
    fn as_str(self) -> &'static str {
        match self {
            LibItem::Strtod => "strtod",
            LibItem::Strtol => "strtol",
            LibItem::Strtoul => "strtoul",
            LibItem::Peek => "peek",
            LibItem::ParseFloat => "parse_float",
            LibItem::ParseInteger => "parse_integer",
        }
    }

    fn get_impl(self) -> &'static str {
        match self {
            LibItem::Strtod => strto::STRTOD,
            LibItem::Strtol => strto::STRTOL,
            LibItem::Strtoul => strto::STRTOUL,
            LibItem::Peek => utils::c_lib::PEEK,
            LibItem::ParseFloat => utils::c_lib::PARSE_FLOAT,
            LibItem::ParseInteger => utils::c_lib::PARSE_INTEGER,
        }
    }
}
