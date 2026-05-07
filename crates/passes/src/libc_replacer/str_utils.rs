use rustc_ast::{token, *};
use rustc_ast_pretty::pprust;

use crate::libc_replacer::LibItem;

impl super::TransformVisitor<'_> {
    pub(super) fn c_byte_slice(&mut self, s: &Expr) -> Option<String> {
        if let Some((array, ty)) = utils::ir::array_of_as_ptr(s, &self.ast_to_hir, self.tcx) {
            let array = pprust::expr_to_string(array);
            if array.contains("with_borrow(") || array.contains("with_borrow_mut(") {
                return None;
            }
            if ty == self.tcx.types.u8 {
                return Some(format!("&({array})"));
            } else if ty == self.tcx.types.i8 {
                self.bytemuck = true;
                return Some(format!("bytemuck::cast_slice(&({array}))"));
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
        let (array, ty) = utils::ir::array_of_as_ptr(s, &self.ast_to_hir, self.tcx)?;
        let array = pprust::expr_to_string(array);
        if array.contains("with_borrow(") || array.contains("with_borrow_mut(") {
            return None;
        }
        if ty == self.tcx.types.u8 {
            Some(format!("&mut ({array})"))
        } else if ty == self.tcx.types.i8 {
            self.bytemuck = true;
            Some(format!("bytemuck::cast_slice_mut(&mut ({array}))"))
        } else {
            None
        }
    }

    pub fn transform_strlen(&mut self, s: &Expr) -> Expr {
        if let Some((array, ty)) = utils::ir::array_of_as_ptr(s, &self.ast_to_hir, self.tcx) {
            if ty == self.tcx.types.u8 {
                let array = pprust::expr_to_string(array);
                return utils::expr!(
                    "std::ffi::CStr::from_bytes_until_nul(&({array})).unwrap().count_bytes()"
                );
            } else if ty == self.tcx.types.i8 {
                let array = pprust::expr_to_string(array);
                self.bytemuck = true;
                return utils::expr!(
                    "std::ffi::CStr::from_bytes_until_nul(bytemuck::cast_slice(&({array}))).unwrap().count_bytes()"
                );
            }
        }

        let s_str = pprust::expr_to_string(s);
        utils::expr!("std::ffi::CStr::from_ptr(({s_str}) as _).count_bytes()")
    }

    pub fn transform_strncpy(&mut self, s1: &Expr, s2: &Expr, n: &Expr) -> Option<Expr> {
        let n_str = pprust::expr_to_string(n);
        if let Some((array1, ty1)) = utils::ir::array_of_as_ptr(s1, &self.ast_to_hir, self.tcx)
            && let Some((array2, ty2)) = utils::ir::array_of_as_ptr(s2, &self.ast_to_hir, self.tcx)
        {
            if (ty1 == self.tcx.types.u8 && ty2 == self.tcx.types.u8)
                || (ty1 == self.tcx.types.i8 && ty2 == self.tcx.types.i8)
            {
                let array1 = pprust::expr_to_string(array1);
                let array2 = pprust::expr_to_string(array2);
                return Some(utils::expr!(
                    "{{ let ___n = ({n_str}) as usize; let ___dst = (&mut ({array1}))[..___n].as_mut_ptr(); let ___src = &(&({array2}))[..]; let ___len = ___src.iter().position(|&___c| ___c == 0).map_or(___src.len(), |___i| ___i + 1).min(___n); unsafe {{ std::ptr::write_bytes(___dst, 0, ___n); std::ptr::copy_nonoverlapping(___src.as_ptr(), ___dst, ___len); }} }}"
                ));
            } else if ty1 == self.tcx.types.u8 || ty1 == self.tcx.types.i8 {
                self.bytemuck = true;
                let array1 = pprust::expr_to_string(array1);
                let array2 = pprust::expr_to_string(array2);
                return Some(utils::expr!(
                    "{{ let ___n = ({n_str}) as usize; let ___dst = (&mut ({array1}))[..___n].as_mut_ptr(); let ___src = bytemuck::cast_slice(&(&({array2}))[..]); let ___len = ___src.iter().position(|&___c| ___c == 0).map_or(___src.len(), |___i| ___i + 1).min(___n); unsafe {{ std::ptr::write_bytes(___dst, 0, ___n); std::ptr::copy_nonoverlapping(___src.as_ptr(), ___dst, ___len); }} }}"
                ));
            }
        }
        None
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
        if same_ptr_receiver_root(s1, s2) || n_mentions_ptr_receiver_root(s1, n) {
            return None;
        }
        let s1 = self.c_byte_slice_mut(s1)?;
        let s2 = self.c_byte_slice(s2)?;
        let n = pprust::expr_to_string(n);
        self.lib_items.insert(LibItem::Strncat);
        Some(utils::expr!(
            "crate::c_lib::strncat({s1}, {s2}, ({n}) as usize) as *mut i8"
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
        if let Some((array1, ty1)) = utils::ir::array_of_as_ptr(s1, &self.ast_to_hir, self.tcx)
            && let Some((array2, ty2)) = utils::ir::array_of_as_ptr(s2, &self.ast_to_hir, self.tcx)
        {
            let array1 = pprust::expr_to_string(array1);
            let array1 = if ty1 == self.tcx.types.u8 {
                Some(format!("&({array1})"))
            } else if ty1 == self.tcx.types.i8 {
                self.bytemuck = true;
                Some(format!("bytemuck::cast_slice(&({array1}))"))
            } else {
                None
            };
            let array2 = pprust::expr_to_string(array2);
            let array2 = if ty2 == self.tcx.types.u8 {
                Some(format!("&({array2})"))
            } else if ty2 == self.tcx.types.i8 {
                self.bytemuck = true;
                Some(format!("bytemuck::cast_slice(&({array2}))"))
            } else {
                None
            };
            if let Some(array1) = array1
                && let Some(array2) = array2
            {
                return Some(utils::expr!(
                    "std::ffi::CStr::from_bytes_until_nul({array1}).unwrap().to_bytes().iter().take_while(
                        |c| !std::ffi::CStr::from_bytes_until_nul({array2}).unwrap().to_bytes().contains(c)
                    ).count()"
                ));
            }
        }
        None
    }
}

fn same_ptr_receiver_root(s1: &Expr, s2: &Expr) -> bool {
    ptr_receiver_root(s1)
        .zip(ptr_receiver_root(s2))
        .is_some_and(|(s1, s2)| s1 == s2)
}

fn n_mentions_ptr_receiver_root(s: &Expr, n: &Expr) -> bool {
    ptr_receiver_root(s).is_some_and(|root| pprust::expr_to_string(n).contains(&root))
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
