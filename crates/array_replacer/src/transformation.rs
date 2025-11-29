use std::cell::Cell;

use etrace::some_or;
use rustc_ast::{mut_visit::MutVisitor as _, *};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashSet;
use rustc_hir::{self as hir, def::DefKind, def_id::LocalDefId};
use rustc_middle::ty::{TyCtxt, TyKind, TypingEnv};
use rustc_span::sym;
use utils::ast::{unwrap_cast_and_paren, unwrap_cast_then_as_ptr};

pub fn replace_array(tcx: TyCtxt<'_>) -> (String, bool) {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let mut statics = FxHashSet::default();
    for def_id in tcx.hir_body_owners() {
        if matches!(tcx.def_kind(def_id), DefKind::Static { .. }) {
            statics.insert(def_id);
        }
    }

    let mut visitor = AstVisitor {
        tcx,
        ast_to_hir,
        bytemuck: Cell::new(false),
    };
    visitor.visit_crate(&mut krate);

    (
        pprust::crate_to_string_for_macros(&krate),
        visitor.bytemuck.get(),
    )
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: utils::ir::AstToHir,
    pub bytemuck: Cell<bool>,
}

impl mut_visit::MutVisitor for AstVisitor<'_> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        let hir_expr = some_or!(self.ast_to_hir.get_expr(expr.id, self.tcx), return);
        match &mut expr.kind {
            ExprKind::Call(func, args) => {
                let func_name = some_or!(get_fn_name_from_expr(&**func), return);
                match func_name.as_str() {
                    "memcpy" => {
                        let dest_expr = some_or!(unwrap_cast_then_as_ptr(&args[0]), return);
                        let src_expr = some_or!(unwrap_cast_then_as_ptr(&args[1]), return);

                        let dest_hir_expr =
                            some_or!(self.ast_to_hir.get_expr(dest_expr.id, self.tcx), return);
                        let src_hir_expr =
                            some_or!(self.ast_to_hir.get_expr(src_expr.id, self.tcx), return);

                        let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                        let mut dest_ty = typeck.expr_ty(dest_hir_expr);
                        let mut src_ty = typeck.expr_ty(src_hir_expr);
                        let mut is_dest_ref = false;
                        let mut is_src_ref = false;
                        while let TyKind::Ref(_, _dest_ty, _) = dest_ty.kind() {
                            is_dest_ref = true;
                            dest_ty = _dest_ty.clone();
                        }
                        while let TyKind::Ref(_, _src_ty, _) = src_ty.kind() {
                            is_src_ref = true;
                            src_ty = _src_ty.clone();
                        }
                        // check if the first and second arguments are slices
                        if let TyKind::Slice(dest_inner_ty) | TyKind::Array(dest_inner_ty, _) =
                            dest_ty.kind()
                            && let TyKind::Slice(src_inner_ty) | TyKind::Array(src_inner_ty, _) =
                                src_ty.kind()
                        {
                            let size_expr = &args[2];
                            if dest_inner_ty == src_inner_ty
                                && let Some(len_expr) = self.get_len_from_size(
                                    size_expr,
                                    dest_inner_ty.clone(),
                                    hir_expr.hir_id.owner.def_id,
                                )
                            {
                                // replace memcpy with slice copy
                                *expr = utils::expr!(
                                    "({0}[..({2}) as usize]).copy_from_slice(&{1}[..({2}) as usize])",
                                    pprust::expr_to_string(dest_expr),
                                    pprust::expr_to_string(src_expr),
                                    pprust::expr_to_string(&len_expr)
                                )
                            } else {
                                // could not determine length, use size_expr directly
                                self.bytemuck.set(true);
                                *expr = utils::expr!(
                                    "(bytemuck::cast_slice_mut::<_, u8>({3}{0})[..({2}) as usize]).copy_from_slice(&bytemuck::cast_slice({4}{1})[..({2}) as usize])",
                                    pprust::expr_to_string(dest_expr),
                                    pprust::expr_to_string(src_expr),
                                    pprust::expr_to_string(&size_expr),
                                    if is_dest_ref { "" } else { "&mut " },
                                    if is_src_ref { "" } else { "&" }
                                )
                            }
                        }
                    }
                    "memset" => {
                        let dest_expr = some_or!(unwrap_cast_then_as_ptr(&args[0]), return);
                        let src_expr = unwrap_cast_and_paren(&args[1]);

                        let dest_hir_expr =
                            some_or!(self.ast_to_hir.get_expr(dest_expr.id, self.tcx), return);

                        let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                        let mut dest_ty = typeck.expr_ty(dest_hir_expr);
                        let mut is_dest_ref = false;
                        while let TyKind::Ref(_, _dest_ty, _) = dest_ty.kind() {
                            is_dest_ref = true;
                            dest_ty = _dest_ty.clone();
                        }
                        // check if the first argument is a slice / array
                        if let TyKind::Slice(_) | TyKind::Array(_, _) = dest_ty.kind() {
                            let size_expr = &args[2];
                            // could not determine length, use size_expr directly
                            self.bytemuck.set(true);
                            *expr = utils::expr!(
                                "(bytemuck::cast_slice_mut::<_, u8>({3}{0})[..({2}) as usize]).fill({1} as u8)",
                                pprust::expr_to_string(dest_expr),
                                pprust::expr_to_string(src_expr),
                                pprust::expr_to_string(&size_expr),
                                if is_dest_ref { "" } else { "&mut " },
                            )
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

impl<'tcx> AstVisitor<'tcx> {
    fn get_len_from_size(
        &self,
        size_expr: &Expr,
        ty: rustc_middle::ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Option<Expr> {
        if let ExprKind::MethodCall(call) = &unwrap_cast_and_paren(size_expr).kind
            && call.seg.ident.name == sym::wrapping_mul
            && call.args.len() == 1
        {
            for (operand_1, operand_2) in [
                (&*call.receiver, &*call.args[0]),
                (&*call.args[0], &*call.receiver),
            ] {
                if let ExprKind::Call(func, args) = &unwrap_cast_and_paren(operand_1).kind
                    && let ExprKind::Path(_, call_path) = &func.kind
                    && let Some(func_name) = get_fn_name_from_expr(&**func)
                    && func_name == "size_of"
                    && args.len() == 0
                    && let Some(last_seg) = call_path.segments.last()
                    && let Some(box GenericArgs::AngleBracketed(AngleBracketedArgs {
                        args, ..
                    })) = &last_seg.args
                    && let Some(AngleBracketedArg::Arg(GenericArg::Type(box ty_generic))) =
                        args.first()
                    && let Some(ty_generic) = self.ast_to_hir.get_ty(ty_generic.id, self.tcx)
                {
                    let typeck = self.tcx.typeck(ty_generic.hir_id.owner);
                    let ty_generic = typeck.node_type(ty_generic.hir_id);
                    if self.ty_size(ty_generic.clone(), def_id) == self.ty_size(ty.clone(), def_id)
                    {
                        return Some(operand_2.clone());
                    }
                }
            }
        }
        None
    }

    fn ty_size(&self, ty: rustc_middle::ty::Ty<'tcx>, def_id: LocalDefId) -> u64 {
        let typing_env = TypingEnv::post_analysis(self.tcx, def_id);
        let layout = self.tcx.layout_of(typing_env.as_query_input(ty)).unwrap();
        layout.size.bytes()
    }
}

fn get_fn_name_from_expr(expr: &Expr) -> Option<String> {
    if let ExprKind::Path(_, path) = &expr.kind {
        if let Some(segment) = path.segments.last() {
            return Some(segment.ident.name.to_string());
        }
    }
    None
}

// fn get_def_id_from_hir_expr(expr: &hir::Expr<'_>) -> Option<LocalDefId> {
//     if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = &expr.kind
//         && let Res::Def(DefKind::Fn { .. }, def_id) = path.res
//         && let Some(def_id) = def_id.as_local()
//     {
//         Some(def_id)
//     } else {
//         None
//     }
// }

// fn get_fn_name_from_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> String {
//     let func_name = tcx.def_path_str(def_id);
//     func_name
//         .rsplit("::")
//         .next()
//         .unwrap_or(func_name.as_str())
//         .to_string()
// }

// fn unwrap_cast_then_as_ptr(expr: &Expr) -> Option<&Expr> {
//     match &expr.kind {
//         ExprKind::MethodCall(call)
//             if matches!(call.seg.ident.name.as_str(), "as_ptr" | "as_mut_ptr") =>
//         {
//             Some(&call.receiver)
//         }
//         ExprKind::Cast(e, _) | ExprKind::Paren(e) => unwrap_cast_and_as_ptr(e),
//         _ => None,
//     }
// }

#[cfg(test)]
mod tests {
    fn run_test(code: &str, includes: &[&str], excludes: &[&str]) {
        let (s, _) = utils::compilation::run_compiler_on_str(code, super::replace_array).unwrap();
        println!("{}", s);
        utils::compilation::run_compiler_on_str(&s, utils::type_check).expect(&s);
        for include in includes {
            assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
        }
        for exclude in excludes {
            assert!(
                !s.contains(exclude),
                "Expected not to find `{exclude}` in:\n{s}"
            );
        }
    }

    #[test]
    fn test_memcpy() {
        let code = r#"
use libc;
extern "C" {
            fn memcpy(_: *mut libc::c_void, _: *const libc::c_void,
            _: libc::c_ulong)
            -> *mut libc::c_void;
        }
pub unsafe extern "C" fn merge_sort(mut a: &mut [usize], mut b: &mut [usize], mut size: libc::c_int) {
    memcpy((b).as_mut_ptr() as *mut _, (a).as_ptr() as *const _,
        (::std::mem::size_of::<usize>() as
                    libc::c_ulong).wrapping_mul(size as libc::c_ulong));
}
"#;
        run_test(code, &[], &["memcpy"]);
    }

    #[test]
    fn test_memset() {
        let code = r#"
use libc;
extern "C" {
    fn memset(_: *mut libc::c_void, _: libc::c_int,
    _: libc::c_ulong)
    -> *mut libc::c_void;
}
unsafe fn main_0() {
    let mut source: [libc::c_char; 100] = [0; 100];
    memset(
        (source).as_mut_ptr() as *mut _,
        'A' as i32,
        (100 as libc::c_int - 1 as libc::c_int) as libc::c_ulong,
    );
}
"#;
        run_test(code, &[], &[]);
    }
}
