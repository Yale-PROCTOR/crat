use rustc_ast::*;
use rustc_ast_pretty::pprust;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty;
use rustc_span::{Symbol, sym};
use utils::{ast::unwrap_cast_and_paren, bytemuck::BytemuckRequirement};

use crate::libc_replacer::LibItem;

impl<'tcx> super::TransformVisitor<'tcx> {
    pub fn transform_memcpy(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr> {
        let ptr1 = self.array_of_ptr_or_offset(s1)?;
        if let Some(ptr2) = self.array_of_ptr_or_offset(s2) {
            let hir_n = self.ast_to_hir.get_expr(n.id, self.tcx)?;
            if ptr1.ty == ptr2.ty
                && let Some(len_expr) =
                    self.get_len_from_size(n, ptr1.ty, hir_n.hir_id.owner.def_id)
            {
                if self.current_fn_has_raw_deref && (!ptr1.is_plain() || !ptr2.is_plain()) {
                    return None;
                }
                let array1 = ptr1.slice(true);
                let array2 = ptr2.slice(false);
                let len = pprust::expr_to_string(&len_expr);
                if ptr1.same_array(&ptr2) {
                    return Some(utils::expr!(
                        "{{ let ___tmp = ({array2})[..({len}) as usize].to_vec(); ({array1})[..({len}) as usize].copy_from_slice(&___tmp); }}"
                    ));
                } else {
                    return Some(utils::expr!(
                        "({array1})[..({len}) as usize].copy_from_slice(&({array2})[..({len}) as usize])"
                    ));
                }
            } else if is_numeric_or_numeric_array(ptr1.ty) && is_numeric_or_numeric_array(ptr2.ty) {
                if self.current_fn_has_raw_deref
                    && (!ptr1.is_plain()
                        || !ptr2.is_plain()
                        || !ptr1.ty.is_numeric()
                        || !ptr2.ty.is_numeric())
                {
                    return None;
                }
                self.bytemuck = true;
                let array1 = if ptr1.ty == self.tcx.types.u8 {
                    ptr1.slice(true)
                } else {
                    ptr1.byte_slice(true)
                };
                let array2 = if ptr2.ty == self.tcx.types.u8 {
                    ptr2.slice(false)
                } else {
                    ptr2.byte_slice(false)
                };
                let n = pprust::expr_to_string(n);
                if ptr1.same_array(&ptr2) {
                    return Some(utils::expr!(
                        "{{ let ___tmp = ({array2})[..({n}) as usize].to_vec(); ({array1})[..({n}) as usize].copy_from_slice(&___tmp); }}"
                    ));
                } else {
                    return Some(utils::expr!(
                        "({array1})[..({n}) as usize].copy_from_slice(&({array2})[..({n}) as usize])",
                    ));
                }
            }
        }

        self.transform_memcpy_object_to_bytes(&ptr1, s2, n)
    }

    pub fn transform_memmove(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr> {
        if self.current_fn_has_raw_deref {
            return None;
        }

        let ptr1 = self.array_of_ptr_or_offset(s1)?;
        let ptr2 = self.array_of_ptr_or_offset(s2)?;
        let hir_n = self.ast_to_hir.get_expr(n.id, self.tcx)?;
        if ptr1.ty == ptr2.ty
            && ptr1.ty.is_numeric()
            && let Some(len_expr) = self.get_len_from_size(n, ptr1.ty, hir_n.hir_id.owner.def_id)
        {
            Some(utils::expr!(
                "{{ let ___tmp = ({0})[..({2}) as usize].to_vec(); ({1})[..({2}) as usize].copy_from_slice(&___tmp); }}",
                ptr2.slice(false),
                ptr1.slice(true),
                pprust::expr_to_string(&len_expr)
            ))
        } else if is_numeric_or_numeric_array(ptr1.ty) && is_numeric_or_numeric_array(ptr2.ty) {
            self.bytemuck = true;
            let array1 = if ptr1.ty == self.tcx.types.u8 {
                ptr1.slice(true)
            } else {
                ptr1.byte_slice(true)
            };
            let array2 = if ptr2.ty == self.tcx.types.u8 {
                ptr2.slice(false)
            } else {
                ptr2.byte_slice(false)
            };
            let n = pprust::expr_to_string(n);
            Some(utils::expr!(
                "{{ let ___tmp = ({array2})[..({n}) as usize].to_vec(); ({array1})[..({n}) as usize].copy_from_slice(&___tmp); }}"
            ))
        } else {
            None
        }
    }

    pub fn transform_memset(&mut self, s: &Expr, c: &Expr, n: &Expr) -> Option<Expr> {
        let ptr = self.array_of_ptr_or_offset(s)?;
        if self.current_fn_has_raw_deref
            && (!ptr.is_plain() || (!ptr.ty.is_numeric() && !is_i8_or_u8(ptr.ty, self.tcx)))
        {
            return None;
        }
        let c = pprust::expr_to_string(c);
        let n = pprust::expr_to_string(n);
        if ptr.ty == self.tcx.types.u8 || ptr.ty == self.tcx.types.i8 {
            let array = ptr.slice(true);
            Some(utils::expr!(
                "{array}[..({n}) as usize].fill(({c}) as {0})",
                ptr.ty
            ))
        } else if is_numeric_or_numeric_array(ptr.ty) {
            self.bytemuck = true;
            let array = ptr.byte_slice(true);
            Some(utils::expr!("{array}[..({n}) as usize].fill(({c}) as u8)"))
        } else {
            None
        }
    }

    pub fn transform_memcmp(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr> {
        let s1 = self.c_byte_slice(s1)?;
        let s2 = self.c_byte_slice(s2)?;
        let n = pprust::expr_to_string(n);
        self.lib_items.insert(LibItem::Memcmp);
        Some(utils::expr!(
            "crate::c_lib::memcmp({s1}, {s2}, ({n}) as usize)"
        ))
    }

    pub fn transform_memchr(&mut self, s: &Expr, c: &Expr, n: &Expr) -> Option<Expr> {
        let s = self.c_byte_slice(s)?;
        let c = pprust::expr_to_string(c);
        let n = pprust::expr_to_string(n);
        self.lib_items.insert(LibItem::Memchr);
        Some(utils::expr!(
            "crate::c_lib::memchr({s}, ({c}) as u8, ({n}) as usize)"
        ))
    }

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
                    && let Some(func_name) = get_fn_name_from_expr(func)
                    && func_name == sym::size_of
                    && args.is_empty()
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
                    if utils::ir::ty_size(ty_generic, def_id, self.tcx)
                        == utils::ir::ty_size(ty, def_id, self.tcx)
                    {
                        return Some(operand_2.clone());
                    }
                }
            }
        }
        None
    }

    fn transform_memcpy_object_to_bytes(
        &mut self,
        dst: &ArrayPtr<'_, 'tcx>,
        src: &Expr,
        n: &Expr,
    ) -> Option<Expr> {
        if self.current_fn_has_raw_deref || !is_i8_or_u8(dst.ty, self.tcx) {
            return None;
        }
        let pointee = addr_of_pointee(src)?;
        let hir_pointee = self.ast_to_hir.get_expr(pointee.id, self.tcx)?;
        let typeck = self.tcx.typeck(hir_pointee.hir_id.owner);
        let pointee_ty = typeck.expr_ty(hir_pointee);
        if !self.size_matches_type(n, pointee_ty, hir_pointee.hir_id.owner.def_id) {
            return None;
        }

        match pointee_ty.kind() {
            ty::TyKind::Int(_) | ty::TyKind::Uint(_) | ty::TyKind::Float(_) => {}
            ty::TyKind::Adt(adt, _) if adt.is_struct() => {
                if !self.bytemuck_derives.require_type(
                    self.tcx,
                    &mut self.bytemuck_classifier,
                    pointee_ty,
                    BytemuckRequirement::NoUninit,
                ) {
                    return None;
                }
            }
            _ => return None,
        }

        self.bytemuck = true;
        let dst = if dst.ty == self.tcx.types.u8 {
            dst.slice(true)
        } else {
            dst.byte_slice(true)
        };
        let src = pprust::expr_to_string(pointee);
        Some(utils::expr!(
            "{{ let ___src = bytemuck::bytes_of(&({src})); ({dst})[..___src.len()].copy_from_slice(___src); }}"
        ))
    }

    fn size_matches_type(
        &self,
        size_expr: &Expr,
        ty: rustc_middle::ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> bool {
        if let ExprKind::Call(func, args) = &unwrap_cast_and_paren(size_expr).kind
            && let ExprKind::Path(_, call_path) = &func.kind
            && let Some(func_name) = get_fn_name_from_expr(func)
            && func_name == sym::size_of
            && args.is_empty()
            && let Some(last_seg) = call_path.segments.last()
            && let Some(box GenericArgs::AngleBracketed(AngleBracketedArgs { args, .. })) =
                &last_seg.args
            && let Some(AngleBracketedArg::Arg(GenericArg::Type(box ty_generic))) = args.first()
            && let Some(ty_generic) = self.ast_to_hir.get_ty(ty_generic.id, self.tcx)
        {
            let typeck = self.tcx.typeck(ty_generic.hir_id.owner);
            let ty_generic = typeck.node_type(ty_generic.hir_id);
            utils::ir::ty_size(ty_generic, def_id, self.tcx)
                == utils::ir::ty_size(ty, def_id, self.tcx)
        } else {
            false
        }
    }

    fn array_of_ptr_or_offset<'e>(&self, expr: &'e Expr) -> Option<ArrayPtr<'e, 'tcx>> {
        if let Some((array, ty)) = utils::ir::array_of_as_ptr(expr, &self.ast_to_hir, self.tcx) {
            return Some(ArrayPtr {
                array,
                ty,
                offset: None,
            });
        }

        if let ExprKind::MethodCall(call) = &unwrap_cast_and_paren(expr).kind
            && call.seg.ident.name == sym::offset
            && call.args.len() == 1
            && let Some((array, ty)) =
                utils::ir::array_of_as_ptr(&call.receiver, &self.ast_to_hir, self.tcx)
        {
            Some(ArrayPtr {
                array,
                ty,
                offset: Some(&call.args[0]),
            })
        } else {
            None
        }
    }
}

fn addr_of_pointee(expr: &Expr) -> Option<&Expr> {
    if let ExprKind::AddrOf(BorrowKind::Raw | BorrowKind::Ref, _, pointee) =
        &unwrap_cast_and_paren(expr).kind
    {
        Some(pointee)
    } else {
        None
    }
}

struct ArrayPtr<'e, 'tcx> {
    array: &'e Expr,
    ty: ty::Ty<'tcx>,
    offset: Option<&'e Expr>,
}

impl ArrayPtr<'_, '_> {
    fn slice(&self, mutable: bool) -> String {
        let array = pprust::expr_to_string(self.array);
        let borrow = if mutable { "&mut" } else { "&" };
        if let Some(offset) = self.offset {
            let offset = pprust::expr_to_string(offset);
            format!("({borrow} ({array}))[({offset}) as usize..]")
        } else {
            format!("({borrow} ({array}))")
        }
    }

    fn byte_slice(&self, mutable: bool) -> String {
        let slice = self.slice(mutable);
        let cast = if mutable {
            "bytemuck::cast_slice_mut::<_, u8>"
        } else {
            "bytemuck::cast_slice::<_, u8>"
        };
        format!("{cast}({slice})")
    }

    fn same_array(&self, other: &Self) -> bool {
        pprust::expr_to_string(self.array) == pprust::expr_to_string(other.array)
    }

    fn is_plain(&self) -> bool {
        self.offset.is_none()
    }
}

fn is_numeric_or_numeric_array(ty: ty::Ty<'_>) -> bool {
    if ty.is_numeric() {
        return true;
    }
    if let ty::TyKind::Array(elem, _) = ty.kind() {
        is_numeric_or_numeric_array(*elem)
    } else {
        false
    }
}

fn is_i8_or_u8<'tcx>(ty: ty::Ty<'tcx>, tcx: ty::TyCtxt<'tcx>) -> bool {
    ty == tcx.types.i8 || ty == tcx.types.u8
}

pub const MEMCMP: &str = r#"
pub fn memcmp(s1: &[u8], s2: &[u8], n: usize) -> i32 {
    for i in 0..n {
        let c1 = s1[i];
        let c2 = s2[i];
        if c1 != c2 {
            return c1 as i32 - c2 as i32;
        }
    }
    0
}
"#;

pub const MEMCHR: &str = r#"
pub fn memchr(s: &[u8], c: u8, n: usize) -> *mut std::ffi::c_void {
    s[..n]
        .iter()
        .position(|&x| x == c)
        .map_or(std::ptr::null_mut(), |i| s[i..].as_ptr() as *mut std::ffi::c_void)
}
"#;

fn get_fn_name_from_expr(expr: &Expr) -> Option<Symbol> {
    if let ExprKind::Path(_, path) = &expr.kind
        && let Some(segment) = path.segments.last()
    {
        Some(segment.ident.name)
    } else {
        None
    }
}
