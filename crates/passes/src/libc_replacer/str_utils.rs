use rustc_ast::{
    token,
    visit::{self, Visitor},
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hir::{
    self as hir,
    def::{DefKind, Res},
};
use rustc_middle::ty;

use crate::libc_replacer::LibItem;

impl<'tcx> super::TransformVisitor<'tcx> {
    pub(super) fn c_byte_slice(&mut self, s: &Expr) -> Option<String> {
        if let Some((array, ty)) = utils::ir::array_of_as_ptr(s, &self.ast_to_hir, self.tcx) {
            if expr_has_with_borrow_call(array) {
                return None;
            }
            let array = pprust::expr_to_string(array);
            if ty == self.tcx.types.u8 {
                return Some(format!("&({array})"));
            } else if ty == self.tcx.types.i8 {
                self.bytemuck = true;
                return Some(format!("bytemuck::cast_slice::<_, u8>(&({array}))"));
            }
        }

        if let Some((cursor, ty)) = self.slice_cursor_of_as_ptr(s, false, &[]) {
            if ty == self.tcx.types.u8 {
                return Some(cursor);
            } else if ty == self.tcx.types.i8 {
                self.bytemuck = true;
                return Some(format!("bytemuck::cast_slice::<_, u8>({cursor})"));
            }
        }

        if let ExprKind::Lit(lit) = &utils::ast::unwrap_cast_and_paren(s).kind
            && lit.kind == token::LitKind::ByteStr
        {
            return Some(pprust::expr_to_string(utils::ast::unwrap_cast_and_paren(s)));
        }

        None
    }

    pub(super) fn c_byte_slice_mut(&mut self, s: &Expr) -> Option<String> {
        self.c_byte_slice_mut_rejecting_methods(s, &[])
    }

    pub(super) fn c_byte_slice_mut_rejecting_methods(
        &mut self,
        s: &Expr,
        method_names: &[&str],
    ) -> Option<String> {
        if let Some((array, ty)) = utils::ir::array_of_as_ptr(s, &self.ast_to_hir, self.tcx) {
            if expr_is_static_path(array, &self.ast_to_hir, self.tcx) {
                return None;
            }
            if expr_has_with_borrow_call(array) || expr_has_method_call(array, method_names) {
                return None;
            }
            let already_mut_ref = self.expr_is_mut_ref(array);
            let array = pprust::expr_to_string(array);
            let array_ref = if already_mut_ref {
                format!("&mut *({array})")
            } else {
                format!("&mut ({array})")
            };
            if ty == self.tcx.types.u8 {
                return Some(array_ref);
            } else if ty == self.tcx.types.i8 {
                self.bytemuck = true;
                return Some(format!("bytemuck::cast_slice_mut::<_, u8>({array_ref})"));
            }
        }

        let (cursor, ty) = self.slice_cursor_of_as_ptr(s, true, method_names)?;
        if ty == self.tcx.types.u8 {
            Some(cursor)
        } else if ty == self.tcx.types.i8 {
            self.bytemuck = true;
            Some(format!("bytemuck::cast_slice_mut::<_, u8>({cursor})"))
        } else {
            None
        }
    }

    fn expr_is_mut_ref(&self, expr: &Expr) -> bool {
        self.ast_to_hir
            .get_expr(expr.id, self.tcx)
            .is_some_and(|hir_expr| {
                let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                matches!(
                    typeck.expr_ty(hir_expr).kind(),
                    ty::TyKind::Ref(_, _, mutability) if mutability.is_mut()
                )
            })
    }

    fn slice_cursor_of_as_ptr(
        &self,
        s: &Expr,
        mutable: bool,
        method_names: &[&str],
    ) -> Option<(String, ty::Ty<'tcx>)> {
        let ExprKind::MethodCall(call) = &utils::ast::unwrap_cast_and_paren(s).kind else {
            return None;
        };
        let method_name = call.seg.ident.name.as_str();
        if mutable {
            if method_name != "as_mut_ptr" {
                return None;
            }
        } else if method_name != "as_ptr" && method_name != "as_mut_ptr" {
            return None;
        }
        let receiver = &call.receiver;
        if expr_has_with_borrow_call(receiver) || expr_has_method_call(receiver, method_names) {
            return None;
        }
        let (elem_ty, is_mut_cursor) = self.slice_cursor_elem_ty(receiver)?;
        let is_offset_by = is_offset_by_call(receiver);
        let receiver = pprust::expr_to_string(receiver);
        let slice = if mutable {
            format!("({receiver}).as_slice_mut()")
        } else if is_mut_cursor && is_offset_by {
            format!("({receiver}).as_deref().as_slice()")
        } else {
            format!("({receiver}).as_slice()")
        };
        Some((slice, elem_ty))
    }

    fn slice_cursor_elem_ty(&self, e: &Expr) -> Option<(ty::Ty<'tcx>, bool)> {
        let hir_e = self.ast_to_hir.get_expr(e.id, self.tcx)?;
        let typeck = self.tcx.typeck(hir_e.hir_id.owner);
        let ty = typeck.expr_ty(hir_e).peel_refs();
        let ty::TyKind::Adt(adt_def, generic_args) = ty.kind() else {
            return None;
        };
        let item_name = self.tcx.item_name(adt_def.did());
        let is_mut_cursor = item_name.as_str() == "SliceCursorMut";
        if item_name.as_str() != "SliceCursor" && !is_mut_cursor {
            return None;
        }
        generic_args.iter().find_map(|arg| {
            if let ty::GenericArgKind::Type(ty) = arg.kind() {
                Some((ty, is_mut_cursor))
            } else {
                None
            }
        })
    }

    pub fn transform_strlen(&mut self, s: &Expr) -> Expr {
        if let Some(s) = self.c_byte_slice(s) {
            return utils::expr!(
                "std::ffi::CStr::from_bytes_until_nul({s}).unwrap().count_bytes()"
            );
        }

        let s_str = pprust::expr_to_string(s);
        utils::expr!("std::ffi::CStr::from_ptr(({s_str}) as _).count_bytes()")
    }

    pub fn transform_strncpy(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr> {
        let n_str = pprust::expr_to_string(n);
        let (dst_array, _) = utils::ir::array_of_as_ptr(s1, &self.ast_to_hir, self.tcx)?;
        if self.expr_contains_static(dst_array) {
            return None;
        }
        let dst = self.c_byte_slice_mut(s1)?;
        let src = self.c_byte_slice(s2)?;
        Some(utils::expr!(
            "{{ let ___n = ({n_str}) as usize; let ___dst = &mut ({dst})[..___n]; let ___src = &({src})[..]; let ___len = ___src.iter().position(|&___c| ___c == 0).map_or(___src.len(), |___i| ___i + 1).min(___n); ___dst.fill(0); ___dst[..___len].copy_from_slice(&___src[..___len]); }}"
        ))
    }

    pub fn transform_strcmp(&mut self, s1: &Expr, s2: &Expr) -> Option<Expr> {
        let s1 = self.c_byte_slice(s1)?;
        let s2 = self.c_byte_slice(s2)?;
        self.lib_items.insert(LibItem::Strcmp);
        self.lib_items.insert(LibItem::Strncmp);
        Some(utils::expr!("crate::c_lib::strcmp({s1}, {s2})"))
    }

    pub fn transform_strncmp(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr> {
        let s1 = self.c_byte_slice(s1)?;
        let s2 = self.c_byte_slice(s2)?;
        let n = pprust::expr_to_string(n);
        self.lib_items.insert(LibItem::Strncmp);
        Some(utils::expr!(
            "crate::c_lib::strncmp({s1}, {s2}, ({n}) as usize)"
        ))
    }

    pub fn transform_strcpy(&mut self, s1: &Expr, s2: &Expr) -> Option<Expr> {
        if same_ptr_receiver_root(s1, s2) {
            return None;
        }
        let s1 = self.c_byte_slice_mut(s1)?;
        let s2 = self.c_byte_slice(s2)?;
        self.lib_items.insert(LibItem::Strcpy);
        Some(utils::expr!("crate::c_lib::strcpy({s1}, {s2}) as *mut i8"))
    }

    pub fn transform_strcat(&mut self, s1: &Expr, s2: &Expr) -> Option<Expr> {
        if same_ptr_receiver_root(s1, s2) {
            return None;
        }
        let s1 = self.c_byte_slice_mut(s1)?;
        let s2 = self.c_byte_slice(s2)?;
        self.lib_items.insert(LibItem::Strcat);
        self.lib_items.insert(LibItem::Strncat);
        Some(utils::expr!("crate::c_lib::strcat({s1}, {s2}) as *mut i8"))
    }

    pub fn transform_strncat(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr> {
        if same_ptr_receiver_root(s1, s2) {
            return None;
        }
        let s1 = self.c_byte_slice_mut(s1)?;
        let s2 = self.c_byte_slice(s2)?;
        let n = pprust::expr_to_string(n);
        self.lib_items.insert(LibItem::Strncat);
        Some(utils::expr!(
            "{{ let ___n = ({n}) as usize; crate::c_lib::strncat({s1}, {s2}, ___n) as *mut i8 }}"
        ))
    }

    pub fn transform_strchr(&mut self, s: &Expr, c: &Expr) -> Option<Expr> {
        let s = self.c_byte_slice(s)?;
        let c = pprust::expr_to_string(c);
        self.lib_items.insert(LibItem::Strchr);
        Some(utils::expr!(
            "crate::c_lib::strchr({s}, ({c}) as u8) as *mut i8"
        ))
    }

    pub fn transform_strrchr(&mut self, s: &Expr, c: &Expr) -> Option<Expr> {
        let s = self.c_byte_slice(s)?;
        let c = pprust::expr_to_string(c);
        self.lib_items.insert(LibItem::Strrchr);
        Some(utils::expr!(
            "crate::c_lib::strrchr({s}, ({c}) as u8) as *mut i8"
        ))
    }

    pub fn transform_strstr(&mut self, s1: &Expr, s2: &Expr) -> Option<Expr> {
        let s1 = self.c_byte_slice(s1)?;
        let s2 = self.c_byte_slice(s2)?;
        self.lib_items.insert(LibItem::Strstr);
        Some(utils::expr!("crate::c_lib::strstr({s1}, {s2}) as *mut i8"))
    }

    pub fn transform_strcspn(&mut self, s1: &Expr, s2: &Expr) -> Option<Expr> {
        let s1 = self.c_byte_slice(s1)?;
        let s2 = self.c_byte_slice(s2)?;
        Some(utils::expr!(
            "std::ffi::CStr::from_bytes_until_nul({s1}).unwrap().to_bytes().iter().take_while(
                |c| !std::ffi::CStr::from_bytes_until_nul({s2}).unwrap().to_bytes().contains(c)
            ).count()"
        ))
    }

    fn expr_contains_static(&self, expr: &Expr) -> bool {
        struct Finder<'a, 'tcx> {
            ast_to_hir: &'a utils::ir::AstToHir,
            tcx: ty::TyCtxt<'tcx>,
            found: bool,
        }

        impl<'ast, 'tcx> Visitor<'ast> for Finder<'_, 'tcx> {
            fn visit_expr(&mut self, expr: &'ast Expr) {
                if self.found {
                    return;
                }
                if expr_is_static_path(expr, self.ast_to_hir, self.tcx) {
                    self.found = true;
                    return;
                }
                visit::walk_expr(self, expr);
            }
        }

        let mut finder = Finder {
            ast_to_hir: &self.ast_to_hir,
            tcx: self.tcx,
            found: false,
        };
        finder.visit_expr(expr);
        finder.found
    }
}

fn expr_is_static_path(expr: &Expr, ast_to_hir: &utils::ir::AstToHir, tcx: ty::TyCtxt<'_>) -> bool {
    ast_to_hir.get_expr(expr.id, tcx).is_some_and(|hir_expr| {
        matches!(
            hir_expr.kind,
            hir::ExprKind::Path(hir::QPath::Resolved(
                _,
                hir::Path {
                    res: Res::Def(DefKind::Static { .. }, _),
                    ..
                }
            ))
        )
    })
}

fn is_offset_by_call(e: &Expr) -> bool {
    matches!(
        &utils::ast::unwrap_cast_and_paren(e).kind,
        ExprKind::MethodCall(call) if call.seg.ident.name.as_str() == "offset_by"
    )
}

fn expr_has_with_borrow_call(expr: &Expr) -> bool {
    expr_has_method_call(expr, &["with_borrow", "with_borrow_mut"])
}

fn expr_has_method_call(expr: &Expr, names: &[&str]) -> bool {
    struct Finder<'a> {
        names: &'a [&'a str],
        found: bool,
    }

    impl<'ast> Visitor<'ast> for Finder<'_> {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            if self.found {
                return;
            }
            if let ExprKind::MethodCall(call) = &expr.kind
                && self
                    .names
                    .iter()
                    .any(|name| call.seg.ident.name.as_str() == *name)
            {
                self.found = true;
                return;
            }
            visit::walk_expr(self, expr);
        }
    }

    let mut finder = Finder {
        names,
        found: false,
    };
    finder.visit_expr(expr);
    finder.found
}

fn same_ptr_receiver_root(s1: &Expr, s2: &Expr) -> bool {
    ptr_receiver_root(s1)
        .zip(ptr_receiver_root(s2))
        .is_some_and(|(s1, s2)| s1 == s2)
}

fn ptr_receiver_root(s: &Expr) -> Option<String> {
    let ExprKind::MethodCall(call) = &utils::ast::unwrap_cast_and_paren(s).kind else {
        return None;
    };
    let name = call.seg.ident.name.as_str();
    if name != "as_mut_ptr" && name != "as_ptr" {
        return None;
    }

    let receiver = pprust::expr_to_string(&call.receiver);
    leading_ident(&receiver).map(str::to_string)
}

fn leading_ident(s: &str) -> Option<&str> {
    let s = s.trim_start().trim_start_matches('(').trim_start();
    let mut chars = s.char_indices();
    let (_, first) = chars.next()?;
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return None;
    }
    let end = chars
        .find_map(|(i, c)| {
            if c == '_' || c.is_ascii_alphanumeric() {
                None
            } else {
                Some(i)
            }
        })
        .unwrap_or(s.len());
    Some(&s[..end])
}

pub const STRCMP: &str = r#"
pub fn strcmp(s1: &[u8], s2: &[u8]) -> i32 {
    strncmp(s1, s2, usize::MAX)
}
"#;

pub const STRNCMP: &str = r#"
pub fn strncmp(s1: &[u8], s2: &[u8], n: usize) -> i32 {
    for i in 0..n {
        let c1 = s1.get(i).copied().unwrap_or(0);
        let c2 = s2.get(i).copied().unwrap_or(0);
        if c1 != c2 || c1 == 0 {
            return c1 as i32 - c2 as i32;
        }
    }
    0
}
"#;

pub const STRCPY: &str = r#"
pub fn strcpy<'a>(dst: &'a mut [u8], src: &[u8]) -> *mut u8 {
    let len = src.iter().position(|&c| c == 0).map_or(src.len(), |i| i + 1);
    dst[..len].copy_from_slice(&src[..len]);
    dst.as_mut_ptr()
}
"#;

pub const STRCAT: &str = r#"
pub fn strcat<'a>(dst: &'a mut [u8], src: &[u8]) -> *mut u8 {
    strncat(dst, src, usize::MAX)
}
"#;

pub const STRNCAT: &str = r#"
pub fn strncat<'a>(dst: &'a mut [u8], src: &[u8], n: usize) -> *mut u8 {
    let dst_len = dst.iter().position(|&c| c == 0).unwrap_or(dst.len());
    let src_len = src.iter().position(|&c| c == 0).unwrap_or(src.len()).min(n);
    dst[dst_len..dst_len + src_len].copy_from_slice(&src[..src_len]);
    if dst_len + src_len < dst.len() {
        dst[dst_len + src_len] = 0;
    }
    dst.as_mut_ptr()
}
"#;

pub const STRCHR: &str = r#"
pub fn strchr(s: &[u8], c: u8) -> *mut u8 {
    let s = std::ffi::CStr::from_bytes_until_nul(s).unwrap().to_bytes_with_nul();
    s.iter()
        .position(|&x| x == c)
        .map_or(std::ptr::null_mut(), |i| s[i..].as_ptr() as *mut u8)
}
"#;

pub const STRRCHR: &str = r#"
pub fn strrchr(s: &[u8], c: u8) -> *mut u8 {
    let s = std::ffi::CStr::from_bytes_until_nul(s).unwrap().to_bytes_with_nul();
    s.iter()
        .rposition(|&x| x == c)
        .map_or(std::ptr::null_mut(), |i| s[i..].as_ptr() as *mut u8)
}
"#;

pub const STRSTR: &str = r#"
pub fn strstr(haystack: &[u8], needle: &[u8]) -> *mut u8 {
    let haystack = std::ffi::CStr::from_bytes_until_nul(haystack).unwrap().to_bytes();
    let needle = std::ffi::CStr::from_bytes_until_nul(needle).unwrap().to_bytes();
    if needle.is_empty() {
        return haystack.as_ptr() as *mut u8;
    }
    haystack
        .windows(needle.len())
        .position(|window| window == needle)
        .map_or(std::ptr::null_mut(), |i| haystack[i..].as_ptr() as *mut u8)
}
"#;
