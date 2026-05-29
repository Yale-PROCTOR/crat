use rustc_ast::{
    mut_visit::{self, MutVisitor},
    ptr::P,
    visit::{self, Visitor},
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::HirId;
use rustc_middle::ty::{TyCtxt, TyKind};
use thin_vec::ThinVec;
use utils::{
    ast::unwrap_paren,
    bytemuck::{BytemuckDerivePlan, BytemuckDeriveVisitor, BytemuckTypeClassifier},
    expr,
};

use crate::libc_replacer::errno::ErrorCode;

mod errno;
mod mem_utils;
mod stdio_string;
mod str_utils;
mod strto;
#[cfg(test)]
mod tests;

#[derive(Debug)]
pub struct TransformationResult {
    pub code: String,
    pub bytemuck: bool,
    pub bytemuck_derive: bool,
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
        parsing_fns: FxHashMap::default(),
        bytemuck: false,
        bytemuck_derives: BytemuckDerivePlan::default(),
        bytemuck_classifier: BytemuckTypeClassifier::new(tcx),
        num_traits: false,
        current_fn_has_raw_deref: false,
    };
    visitor.visit_crate(&mut krate);
    let bytemuck_derive = !visitor.bytemuck_derives.is_empty();
    if bytemuck_derive {
        let mut derive_visitor =
            BytemuckDeriveVisitor::new(tcx, &visitor.ast_to_hir, visitor.bytemuck_derives.clone());
        derive_visitor.visit_crate(&mut krate);
    }

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
                } else if let ItemKind::Struct(ident, ..) = &item.kind {
                    Some(ident.name.as_str().to_string())
                } else {
                    None
                }
            })
            .collect();
        for (name, code) in visitor.parsing_fns {
            if !items.contains(name.as_str()) {
                push_c_lib_items(lib_items, &code);
            }
        }
        for item in visitor.lib_items {
            if !items.contains(item.as_str()) {
                push_c_lib_items(lib_items, item.get_impl());
            }
        }
    } else {
        let mut code = "mod c_lib {".to_string();
        for (_, item) in visitor.parsing_fns {
            code.push_str(&item);
        }
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
        bytemuck_derive,
        num_traits: visitor.num_traits,
    }
}

fn push_c_lib_items(items: &mut ThinVec<P<Item>>, code: &str) {
    let item = utils::item!("mod __crat_tmp {{ {code} }}");
    let ItemKind::Mod(_, _, ModKind::Loaded(mut new_items, _, _, _)) = item.kind else {
        unreachable!()
    };
    items.append(&mut new_items);
}

struct TransformVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: utils::ir::AstToHir,
    errno_calls: errno::ErrnoCalls,
    source_nums: FxHashMap<HirId, usize>,
    lib_items: FxHashSet<LibItem>,
    parsing_fns: FxHashMap<String, String>,
    bytemuck: bool,
    bytemuck_derives: BytemuckDerivePlan,
    bytemuck_classifier: BytemuckTypeClassifier<'tcx>,
    num_traits: bool,
    current_fn_has_raw_deref: bool,
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
            } else if let StmtKind::Semi(expr) = &stmt.kind
                && let ExprKind::Call(callee, _) = &unwrap_paren(expr).kind
                && let ExprKind::Path(_, path) = &unwrap_paren(callee).kind
                && path.segments.last().unwrap().ident.as_str() == "setlocale"
            {
                false
            } else {
                true
            }
        });
        stmts
    }

    fn visit_item(&mut self, item: &mut Item) {
        let old_current_fn_has_raw_deref = self.current_fn_has_raw_deref;
        if let ItemKind::Fn(f) = &item.kind
            && let Some(body) = &f.body
        {
            self.current_fn_has_raw_deref = fn_body_has_raw_deref(body, &self.ast_to_hir, self.tcx);
        }

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

        self.current_fn_has_raw_deref = old_current_fn_has_raw_deref;
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
                "sin" | "sinf" | "sinl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = expr_to_parenthesized_string(arg);
                    *expr = expr!("{arg}.sin()");
                }
                "cos" | "cosf" | "cosl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = expr_to_parenthesized_string(arg);
                    *expr = expr!("{arg}.cos()");
                }
                "fabs" | "fabsf" | "fabsl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = expr_to_parenthesized_string(arg);
                    *expr = expr!("{arg}.abs()");
                }
                "abs" | "labs" | "llabs" => {
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
                "atan2" | "atan2f" | "atan2l" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    let arg1 = expr_to_parenthesized_string(arg1);
                    let arg2 = pprust::expr_to_string(arg2);
                    *expr = expr!("{arg1}.atan2({arg2})");
                }
                "sqrt" | "sqrtf" | "sqrtl" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = expr_to_parenthesized_string(arg);
                    *expr = expr!("{arg}.sqrt()");
                }
                "difftime" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    let arg1 = expr_to_parenthesized_string(arg1);
                    let arg2 = expr_to_parenthesized_string(arg2);
                    *expr = expr!("({arg1} as f64 - {arg2} as f64)");
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
                "exit" => {
                    let [arg] = args.as_slice() else { panic!() };
                    let arg = pprust::expr_to_string(arg);
                    *expr = expr!("std::process::exit(({arg}) as i32)");
                }
                "time" => {
                    let [arg] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_time(expr.id, arg) {
                        *expr = e;
                    }
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
                "atof" => {
                    let [arg] = args.as_slice() else { panic!() };
                    *expr = self.transform_atof(arg);
                }
                "atoi" => {
                    let [arg] = args.as_slice() else { panic!() };
                    *expr = self.transform_atoi(arg);
                }
                "strlen" => {
                    let [arg] = args.as_slice() else { panic!() };
                    *expr = self.transform_strlen(arg);
                }
                "strcmp" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_strcmp(arg1, arg2) {
                        *expr = e;
                    }
                }
                "strncmp" => {
                    let [arg1, arg2, arg3] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_strncmp(arg1, arg2, arg3) {
                        *expr = e;
                    }
                }
                "strcpy" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_strcpy(arg1, arg2) {
                        *expr = e;
                    }
                }
                "strncpy" => {
                    if let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx)
                        && let rustc_hir::Node::Stmt(stmt) =
                            self.tcx.parent_hir_node(hir_expr.hir_id)
                        && matches!(stmt.kind, rustc_hir::StmtKind::Semi(_))
                        && let [arg1, arg2, arg3] = args.as_slice()
                        && let Some(e) = self.transform_strncpy(arg1, arg2, arg3)
                    {
                        *expr = e;
                    }
                }
                "strcat" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_strcat(arg1, arg2) {
                        *expr = e;
                    }
                }
                "strncat" => {
                    let [arg1, arg2, arg3] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_strncat(arg1, arg2, arg3) {
                        *expr = e;
                    }
                }
                "strchr" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_strchr(arg1, arg2) {
                        *expr = e;
                    }
                }
                "strrchr" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_strrchr(arg1, arg2) {
                        *expr = e;
                    }
                }
                "strstr" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_strstr(arg1, arg2) {
                        *expr = e;
                    }
                }
                "strcspn" => {
                    let [arg1, arg2] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_strcspn(arg1, arg2) {
                        *expr = e;
                    }
                }
                "sprintf" => {
                    if args.len() >= 2
                        && let Some(e) = self.transform_sprintf(&args[0], &args[1], &args[2..])
                    {
                        *expr = e;
                    }
                }
                "snprintf" => {
                    if args.len() >= 3
                        && let Some(e) =
                            self.transform_snprintf(&args[0], &args[1], &args[2], &args[3..])
                    {
                        *expr = e;
                    }
                }
                "sscanf" => {
                    if args.len() >= 2
                        && let Some(e) = self.transform_sscanf(&args[0], &args[1], &args[2..])
                    {
                        *expr = e;
                    }
                }
                "memcpy" => {
                    let [arg1, arg2, arg3] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_memcpy(arg1, arg2, arg3) {
                        *expr = e;
                    }
                }
                "memmove" => {
                    let [arg1, arg2, arg3] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_memmove(arg1, arg2, arg3) {
                        *expr = e;
                    }
                }
                "memcmp" => {
                    let [arg1, arg2, arg3] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_memcmp(arg1, arg2, arg3) {
                        *expr = e;
                    }
                }
                "memchr" => {
                    let [arg1, arg2, arg3] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_memchr(arg1, arg2, arg3) {
                        *expr = e;
                    }
                }
                "memset" => {
                    let [arg1, arg2, arg3] = args.as_slice() else { panic!() };
                    if let Some(e) = self.transform_memset(arg1, arg2, arg3) {
                        *expr = e;
                    }
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
                    *expr = expr!("(({arg} as u8 as char).is_ascii_alphanumeric() as i32)");
                }
                "_ISalpha" => {
                    *expr = expr!("(({arg} as u8 as char).is_ascii_alphabetic() as i32)");
                }
                "_ISlower" => {
                    *expr = expr!("(({arg} as u8 as char).is_ascii_lowercase() as i32)");
                }
                "_ISupper" => {
                    *expr = expr!("(({arg} as u8 as char).is_ascii_uppercase() as i32)");
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
                    *expr = expr!(
                        "(matches!({arg} as u8, b' ' | b'\\t' | b'\\n' | b'\\r' | 0x0b | 0x0c) as i32)"
                    );
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

fn fn_body_has_raw_deref(body: &Block, ast_to_hir: &utils::ir::AstToHir, tcx: TyCtxt<'_>) -> bool {
    struct Finder<'a, 'tcx> {
        ast_to_hir: &'a utils::ir::AstToHir,
        tcx: TyCtxt<'tcx>,
        found: bool,
    }

    impl<'ast> Visitor<'ast> for Finder<'_, '_> {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            if self.found {
                return;
            }
            if let ExprKind::Unary(UnOp::Deref, inner) = &expr.kind
                && let Some(hir_expr) = self.ast_to_hir.get_expr(inner.id, self.tcx)
            {
                let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                if matches!(typeck.expr_ty(hir_expr).kind(), TyKind::RawPtr(..)) {
                    self.found = true;
                    return;
                }
            }
            visit::walk_expr(self, expr);
        }
    }

    let mut finder = Finder {
        ast_to_hir,
        tcx,
        found: false,
    };
    finder.visit_block(body);
    finder.found
}

impl TransformVisitor<'_> {
    fn transform_time(&self, call_id: NodeId, timer: &Expr) -> Option<Expr> {
        let hir_expr = self.ast_to_hir.get_expr(call_id, self.tcx)?;
        let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
        let ty = utils::ir::mir_ty_to_string(typeck.expr_ty(hir_expr), self.tcx);
        let current_time = format!(
            "std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs() as {ty}"
        );

        match &utils::ast::unwrap_cast_and_paren(timer).kind {
            ExprKind::Call(func, args) if args.is_empty() => {
                if let ExprKind::Path(_, path) = &func.kind
                    && path
                        .segments
                        .last()
                        .is_some_and(|seg| seg.ident.as_str() == "null_mut")
                {
                    Some(expr!("{current_time}"))
                } else {
                    None
                }
            }
            ExprKind::AddrOf(BorrowKind::Raw | BorrowKind::Ref, Mutability::Mut, place) => {
                let place = pprust::expr_to_string(place);
                Some(expr!(
                    "{{ let ___time = {current_time}; {place} = ___time; ___time }}"
                ))
            }
            _ => None,
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
    Atof,
    Atoi,
    Peek,
    IsEof,
    ParseDecimal,
    ParseF64,
    ParseFloat,
    ParseInteger,
    Xu8,
    Xu16,
    Xu32,
    Xu64,
    Gf64,
    Strcmp,
    Strncmp,
    Strcpy,
    Strcat,
    Strncat,
    Strchr,
    Strrchr,
    Strstr,
    Memcmp,
    Memchr,
}

impl LibItem {
    fn as_str(self) -> &'static str {
        match self {
            LibItem::Strtod => "strtod",
            LibItem::Strtol => "strtol",
            LibItem::Strtoul => "strtoul",
            LibItem::Atof => "atof",
            LibItem::Atoi => "atoi",
            LibItem::Peek => "peek",
            LibItem::IsEof => "is_eof",
            LibItem::ParseDecimal => "parse_decimal",
            LibItem::ParseF64 => "parse_f64",
            LibItem::ParseFloat => "parse_float",
            LibItem::ParseInteger => "parse_integer",
            LibItem::Xu8 => "Xu8",
            LibItem::Xu16 => "Xu16",
            LibItem::Xu32 => "Xu32",
            LibItem::Xu64 => "Xu64",
            LibItem::Gf64 => "Gf64",
            LibItem::Strcmp => "strcmp",
            LibItem::Strncmp => "strncmp",
            LibItem::Strcpy => "strcpy",
            LibItem::Strcat => "strcat",
            LibItem::Strncat => "strncat",
            LibItem::Strchr => "strchr",
            LibItem::Strrchr => "strrchr",
            LibItem::Strstr => "strstr",
            LibItem::Memcmp => "memcmp",
            LibItem::Memchr => "memchr",
        }
    }

    fn get_impl(self) -> &'static str {
        match self {
            LibItem::Strtod => strto::STRTOD,
            LibItem::Strtol => strto::STRTOL,
            LibItem::Strtoul => strto::STRTOUL,
            LibItem::Atof => strto::ATOF,
            LibItem::Atoi => strto::ATOI,
            LibItem::Peek => utils::c_lib::PEEK,
            LibItem::IsEof => utils::c_lib::IS_EOF,
            LibItem::ParseDecimal => utils::c_lib::PARSE_DECIMAL,
            LibItem::ParseF64 => utils::c_lib::PARSE_F64,
            LibItem::ParseFloat => utils::c_lib::PARSE_FLOAT,
            LibItem::ParseInteger => utils::c_lib::PARSE_INTEGER,
            LibItem::Xu8 => utils::c_lib::XU8,
            LibItem::Xu16 => utils::c_lib::XU16,
            LibItem::Xu32 => utils::c_lib::XU32,
            LibItem::Xu64 => utils::c_lib::XU64,
            LibItem::Gf64 => utils::c_lib::GF64,
            LibItem::Strcmp => str_utils::STRCMP,
            LibItem::Strncmp => str_utils::STRNCMP,
            LibItem::Strcpy => str_utils::STRCPY,
            LibItem::Strcat => str_utils::STRCAT,
            LibItem::Strncat => str_utils::STRNCAT,
            LibItem::Strchr => str_utils::STRCHR,
            LibItem::Strrchr => str_utils::STRRCHR,
            LibItem::Strstr => str_utils::STRSTR,
            LibItem::Memcmp => mem_utils::MEMCMP,
            LibItem::Memchr => mem_utils::MEMCHR,
        }
    }
}
