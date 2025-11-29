use rustc_ast::*;
use rustc_ast_pretty::pprust;

use crate::libc_replacer::LibItem;

impl super::TransformVisitor<'_> {
    pub fn transform_strtod(&mut self, nptr: &Expr, endptr: &Expr, source: Option<usize>) -> Expr {
        let nptr_str = pprust::expr_to_string(nptr);
        let endptr_str = pprust::expr_to_string(endptr);
        let error = if let Some(source) = source {
            format!("Some(&mut error{source})")
        } else {
            "None".to_string()
        };
        self.num_traits = true;
        self.lib_items.insert(LibItem::Strtod);
        self.lib_items.insert(LibItem::ParseFloat);
        self.lib_items.insert(LibItem::Peek);

        if let Some((array, ty)) = utils::ir::array_of_as_ptr(nptr, &self.ast_to_hir, self.tcx) {
            if ty == self.tcx.types.u8 {
                let array = pprust::expr_to_string(array);
                return utils::expr!(
                    "crate::c_lib::strtod(
                        &({array})[..],
                        ({endptr_str} as *mut *const u8).as_mut(),
                        {error},
                    )"
                );
            } else if ty == self.tcx.types.i8 {
                let array = pprust::expr_to_string(array);
                self.bytemuck = true;
                return utils::expr!(
                    "crate::c_lib::strtod(
                        bytemuck::cast_slice(&({array})[..]),
                        ({endptr_str} as *mut *const u8).as_mut(),
                        {error},
                    )"
                );
            }
        }

        utils::expr!(
            "crate::c_lib::strtod(
                std::slice::from_raw_parts(({nptr_str}) as _, 100000),
                ({endptr_str} as *mut *const u8).as_mut(),
                {error},
            )"
        )
    }

    pub fn transform_strtol(
        &mut self,
        nptr: &Expr,
        endptr: &Expr,
        base: &Expr,
        source: Option<usize>,
    ) -> Expr {
        let nptr_str = pprust::expr_to_string(nptr);
        let endptr_str = pprust::expr_to_string(endptr);
        let base_str = pprust::expr_to_string(base);
        let error = if let Some(source) = source {
            format!("Some(&mut error{source})")
        } else {
            "None".to_string()
        };
        self.lib_items.insert(LibItem::Strtol);
        self.lib_items.insert(LibItem::ParseInteger);
        self.lib_items.insert(LibItem::Peek);

        if let Some((array, ty)) = utils::ir::array_of_as_ptr(nptr, &self.ast_to_hir, self.tcx) {
            if ty == self.tcx.types.u8 {
                let array = pprust::expr_to_string(array);
                return utils::expr!(
                    "crate::c_lib::strtol(
                        &({array})[..],
                        ({endptr_str} as *mut *const u8).as_mut(),
                        {base_str},
                        {error},
                    )"
                );
            } else if ty == self.tcx.types.i8 {
                let array = pprust::expr_to_string(array);
                self.bytemuck = true;
                return utils::expr!(
                    "crate::c_lib::strtol(
                        bytemuck::cast_slice(&({array})[..]),
                        ({endptr_str} as *mut *const u8).as_mut(),
                        {base_str},
                        {error},
                    )"
                );
            }
        }

        utils::expr!(
            "crate::c_lib::strtol(
                std::slice::from_raw_parts(({nptr_str}) as _, 100000),
                ({endptr_str} as *mut *const u8).as_mut(),
                {base_str},
                {error},
            )"
        )
    }

    pub fn transform_strtoul(
        &mut self,
        nptr: &Expr,
        endptr: &Expr,
        base: &Expr,
        source: Option<usize>,
    ) -> Expr {
        let nptr_str = pprust::expr_to_string(nptr);
        let endptr_str = pprust::expr_to_string(endptr);
        let base_str = pprust::expr_to_string(base);
        let error = if let Some(source) = source {
            format!("Some(&mut error{source})")
        } else {
            "None".to_string()
        };
        self.lib_items.insert(LibItem::Strtoul);
        self.lib_items.insert(LibItem::ParseInteger);
        self.lib_items.insert(LibItem::Peek);

        if let Some((array, ty)) = utils::ir::array_of_as_ptr(nptr, &self.ast_to_hir, self.tcx) {
            if ty == self.tcx.types.u8 {
                let array = pprust::expr_to_string(array);
                return utils::expr!(
                    "crate::c_lib::strtoul(
                        &({array})[..],
                        ({endptr_str} as *mut *const u8).as_mut(),
                        {base_str},
                        {error},
                    )"
                );
            } else if ty == self.tcx.types.i8 {
                let array = pprust::expr_to_string(array);
                self.bytemuck = true;
                return utils::expr!(
                    "crate::c_lib::strtoul(
                        bytemuck::cast_slice(&({array})[..]),
                        ({endptr_str} as *mut *const u8).as_mut(),
                        {base_str},
                        {error},
                    )"
                );
            }
        }

        utils::expr!(
            "crate::c_lib::strtoul(
                std::slice::from_raw_parts(({nptr_str}) as _, 100000),
                ({endptr_str} as *mut *const u8).as_mut(),
                {base_str},
                {error},
            )"
        )
    }
}

pub const STRTOD: &str = r#"
pub fn strtod(
    mut nptr: &[u8],
    endptr: Option<&mut *const u8>,
    erange: Option<&mut bool>,
) -> f64 {
    let (v, e) = parse_float(&mut nptr, None, None, None);
    if let Some(endptr) = endptr {
        *endptr = nptr.as_ptr();
    }
    if let Some(erange) = erange {
        *erange = e;
    }
    v.unwrap_or(0.0)
}
"#;

pub const STRTOL: &str = r#"
pub fn strtol(
    mut nptr: &[u8],
    endptr: Option<&mut *const u8>,
    base: i32,
    erange: Option<&mut bool>,
) -> i64 {
    if base != 0 && !(2..=36).contains(&base) {
        return 0;
    }
    let (v, e) = parse_integer(&mut nptr, base as u32, true, None, None, None);
    if let Some(endptr) = endptr {
        *endptr = nptr.as_ptr();
    }
    if let Some(erange) = erange {
        *erange = e;
    }
    v.unwrap_or(0) as i64
}
"#;

pub const STRTOUL: &str = r#"
pub fn strtoul(
    mut nptr: &[u8],
    endptr: Option<&mut *const u8>,
    base: i32,
    erange: Option<&mut bool>,
) -> u64 {
    if base != 0 && !(2..=36).contains(&base) {
        return 0;
    }
    let (v, e) = parse_integer(&mut nptr, base as u32, false, None, None, None);
    if let Some(endptr) = endptr {
        *endptr = nptr.as_ptr();
    }
    if let Some(erange) = erange {
        *erange = e;
    }
    v.unwrap_or(0)
}
"#;
