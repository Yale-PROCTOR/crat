use std::fmt::Write as _;

use rustc_ast::{ptr::P, token, *};
use rustc_ast_pretty::pprust;
use utils::{
    ast::unwrap_cast_and_paren,
    expr,
    file::{
        fprintf::{self, Conversion as PrintConversion, FlagChar, LengthMod, Width},
        fscanf::{self, ConvTy, Conversion as ScanConversion, ConversionSpec},
    },
};

use crate::libc_replacer::LibItem;

impl super::TransformVisitor<'_> {
    pub(super) fn transform_sprintf(
        &mut self,
        dst: &Expr,
        fmt: &Expr,
        args: &[P<Expr>],
    ) -> Option<Expr> {
        let dst = self.c_byte_slice_mut_rejecting_methods(dst, &["unwrap_or"])?;
        let rsfmt = self.rust_printf_format(fmt, args)?;
        Some(expr!(
            "{{
                let ___s = std::fmt::format(format_args!(\"{}\", {}));
                let ___bytes = ___s.as_bytes();
                let ___dst = {dst};
                for (___d, &___b) in ___dst[..___bytes.len()].iter_mut().zip(___bytes) {{
                    *___d = ___b;
                }}
                ___dst[___bytes.len()] = 0;
                ___bytes.len() as i32
            }}",
            rsfmt.format,
            rsfmt.args,
        ))
    }

    pub(super) fn transform_snprintf(
        &mut self,
        dst: &Expr,
        size: &Expr,
        fmt: &Expr,
        args: &[P<Expr>],
    ) -> Option<Expr> {
        let dst = self.c_byte_slice_mut_rejecting_methods(dst, &["unwrap_or"])?;
        let size = pprust::expr_to_string(size);
        let rsfmt = self.rust_printf_format(fmt, args)?;
        Some(expr!(
            "{{
                let ___s = std::fmt::format(format_args!(\"{}\", {}));
                let ___bytes = ___s.as_bytes();
                let ___n = ({size}) as usize;
                let ___dst = {dst};
                if ___n != 0 && !___dst.is_empty() {{
                    let ___cap = std::cmp::min(___n, ___dst.len());
                    let ___copy_len = std::cmp::min(___bytes.len(), ___cap - 1);
                    for (___d, &___b) in ___dst[..___copy_len].iter_mut().zip(&___bytes[..___copy_len]) {{
                        *___d = ___b;
                    }}
                    ___dst[___copy_len] = 0;
                }}
                ___bytes.len() as i32
            }}",
            rsfmt.format,
            rsfmt.args,
        ))
    }

    pub(super) fn transform_sscanf(
        &mut self,
        input: &Expr,
        fmt: &Expr,
        args: &[P<Expr>],
    ) -> Option<Expr> {
        let input = self.c_byte_slice(input)?;
        let fmt = byte_str_lit(fmt)?;
        let specs = fscanf::parse_specs(&fmt);
        if specs.is_empty() || specs.iter().any(|spec| !supported_scan_spec(spec)) {
            return None;
        }
        if args.len() != specs.iter().filter(|spec| spec.assign).count() {
            return None;
        }

        let mut code = make_scan_function(&specs)?;
        let mut call = format!("crate::c_lib::{}(std::io::Cursor::new({input})", code.name);
        for (spec, arg) in specs.iter().filter(|spec| spec.assign).zip(args) {
            let arg = self.scan_arg(arg, spec)?;
            write!(call, ", {arg}").unwrap();
        }
        call.push(')');

        self.lib_items.insert(LibItem::Peek);
        self.lib_items.insert(LibItem::IsEof);
        for item in code.lib_items.drain(..) {
            self.lib_items.insert(item);
        }
        if code.num_traits {
            self.num_traits = true;
        }
        self.parsing_fns.insert(code.name, code.code);
        Some(expr!("{call}"))
    }

    fn rust_printf_format(&mut self, fmt: &Expr, args: &[P<Expr>]) -> Option<RustFormat> {
        let fmt = byte_str_lit(fmt)?;
        let conversion = to_rust_format(&fmt)?;
        if args.len() != conversion.casts.len() {
            return None;
        }

        let mut new_args = String::new();
        for (arg, cast) in args.iter().zip(conversion.casts) {
            let arg = match cast {
                PrintCast::Str => {
                    let arg = self.c_byte_slice(arg)?;
                    format!(
                        "std::ffi::CStr::from_bytes_until_nul({arg}).unwrap().to_str().unwrap()"
                    )
                }
                PrintCast::Wrapped(wrapper) => {
                    self.lib_items.insert(wrapper.item);
                    let arg = pprust::expr_to_string(arg);
                    format!("crate::c_lib::{}(({arg}) as _)", wrapper.name)
                }
                PrintCast::Cast(ty) => {
                    let arg = pprust::expr_to_string(arg);
                    format!("({arg}) as {ty}")
                }
            };
            write!(new_args, "{arg}, ").unwrap();
        }

        Some(RustFormat {
            format: conversion.format,
            args: new_args,
        })
    }

    fn scan_arg(&self, arg: &Expr, spec: &ConversionSpec) -> Option<String> {
        let ConvTy::Scalar(spec_ty) = spec.ty() else {
            return None;
        };
        if let ExprKind::AddrOf(_, _, e) = &unwrap_cast_and_paren(arg).kind
            && let Some(hir_e) = self.ast_to_hir.get_expr(e.id, self.tcx)
        {
            let typeck = self.tcx.typeck(hir_e.hir_id.owner);
            let ty = typeck.expr_ty(hir_e).to_string();
            if ty == spec_ty {
                return Some(format!("&mut ({})", pprust::expr_to_string(e)));
            }
        }
        None
    }
}

fn byte_str_lit(expr: &Expr) -> Option<Vec<u8>> {
    if let ExprKind::Lit(lit) = &unwrap_cast_and_paren(expr).kind
        && lit.kind == token::LitKind::ByteStr
    {
        Some(utils::unescape_byte_str(lit.symbol.as_str()))
    } else {
        None
    }
}

struct RustFormat {
    format: String,
    args: String,
}

struct PrintFormat {
    format: String,
    casts: Vec<PrintCast>,
}

#[derive(Clone, Copy)]
enum PrintCast {
    Cast(&'static str),
    Str,
    Wrapped(Wrapper),
}

#[derive(Clone, Copy)]
struct Wrapper {
    name: &'static str,
    item: LibItem,
}

fn to_rust_format(mut remaining: &[u8]) -> Option<PrintFormat> {
    let mut format = String::new();
    let mut casts = vec![];
    loop {
        let res = fprintf::parse_format(remaining);
        utils::format_rust_str_from_bytes(&mut format, res.prefix).unwrap();
        if let Some(cs) = res.conversion_spec {
            let mut fmt = String::new();
            let mut conv = String::new();
            let mut minus = false;
            for flag in cs.flags {
                match flag {
                    FlagChar::Apostrophe | FlagChar::Space => return None,
                    FlagChar::Minus => minus = true,
                    FlagChar::Plus => fmt.push('+'),
                    FlagChar::Hash => fmt.push('#'),
                    FlagChar::Zero => fmt.push('0'),
                }
            }
            if let Some(width) = cs.width {
                if minus {
                    fmt.insert(0, '<');
                } else {
                    fmt.insert(0, '>');
                }
                match width {
                    Width::Asterisk => return None,
                    Width::Decimal(n) => fmt.push_str(&n.to_string()),
                }
            }
            if let Some(precision) = cs.precision {
                fmt.push('.');
                match precision {
                    Width::Asterisk => return None,
                    Width::Decimal(n) => fmt.push_str(&n.to_string()),
                }
            }
            match cs.conversion {
                PrintConversion::Int | PrintConversion::Unsigned | PrintConversion::Char => {}
                PrintConversion::Str => casts.push(PrintCast::Str),
                PrintConversion::Octal => fmt.push('o'),
                PrintConversion::Hexadecimal => fmt.push('x'),
                PrintConversion::HexadecimalUpper => fmt.push('X'),
                PrintConversion::Double => {
                    if cs.precision.is_none() {
                        fmt.push_str(".6");
                    }
                }
                PrintConversion::DoubleExp => fmt.push('e'),
                PrintConversion::DoubleAuto => {}
                PrintConversion::DoubleHex
                | PrintConversion::Pointer
                | PrintConversion::Num
                | PrintConversion::C
                | PrintConversion::S => return None,
                PrintConversion::Percent => conv = "%".to_string(),
            }
            if conv.is_empty() {
                conv.push('{');
                if !fmt.is_empty() {
                    conv.push(':');
                    conv.push_str(&fmt);
                }
                conv.push('}');
            }
            format.push_str(&conv);
            if !matches!(
                cs.conversion,
                PrintConversion::Str | PrintConversion::Percent
            ) {
                casts.push(print_cast(cs.conversion, cs.length)?);
            }
        }
        if let Some(rem) = res.remaining {
            remaining = rem;
        } else {
            break;
        }
    }
    Some(PrintFormat { format, casts })
}

fn print_cast(conversion: PrintConversion, length: Option<LengthMod>) -> Option<PrintCast> {
    use LengthMod::*;
    let cast = match conversion {
        PrintConversion::Int => match length {
            None => PrintCast::Cast("i32"),
            Some(Char) => PrintCast::Cast("i8"),
            Some(Short) => PrintCast::Cast("i16"),
            Some(Long | LongLong | IntMax | Size) => PrintCast::Cast("i64"),
            Some(PtrDiff) => PrintCast::Cast("u64"),
            Some(LongDouble) => return None,
        },
        PrintConversion::Octal | PrintConversion::Unsigned => match length {
            None => PrintCast::Cast("u32"),
            Some(Char) => PrintCast::Cast("u8"),
            Some(Short) => PrintCast::Cast("u16"),
            Some(Long | LongLong | IntMax | Size | PtrDiff) => PrintCast::Cast("u64"),
            Some(LongDouble) => return None,
        },
        PrintConversion::Hexadecimal | PrintConversion::HexadecimalUpper => match length {
            None => PrintCast::Wrapped(Wrapper {
                name: "Xu32",
                item: LibItem::Xu32,
            }),
            Some(Char) => PrintCast::Wrapped(Wrapper {
                name: "Xu8",
                item: LibItem::Xu8,
            }),
            Some(Short) => PrintCast::Wrapped(Wrapper {
                name: "Xu16",
                item: LibItem::Xu16,
            }),
            Some(Long | LongLong | IntMax | Size | PtrDiff) => PrintCast::Wrapped(Wrapper {
                name: "Xu64",
                item: LibItem::Xu64,
            }),
            Some(LongDouble) => return None,
        },
        PrintConversion::Double | PrintConversion::DoubleExp => match length {
            None | Some(Long) => PrintCast::Cast("f64"),
            _ => return None,
        },
        PrintConversion::DoubleAuto => match length {
            None | Some(Long) => PrintCast::Wrapped(Wrapper {
                name: "Gf64",
                item: LibItem::Gf64,
            }),
            _ => return None,
        },
        PrintConversion::Char => PrintCast::Cast("u8 as char"),
        PrintConversion::Str | PrintConversion::Percent => return None,
        PrintConversion::DoubleHex
        | PrintConversion::Pointer
        | PrintConversion::Num
        | PrintConversion::C
        | PrintConversion::S => return None,
    };
    Some(cast)
}

fn supported_scan_spec(spec: &ConversionSpec) -> bool {
    if !spec.assign {
        return false;
    }
    matches!(
        (&spec.conversion, spec.length),
        (ScanConversion::Int10, None) | (ScanConversion::Double, Some(fscanf::LengthMod::Long))
    )
}

struct ScanFunction {
    name: String,
    code: String,
    lib_items: Vec<LibItem>,
    num_traits: bool,
}

fn make_scan_function(specs: &[ConversionSpec]) -> Option<ScanFunction> {
    let mut name = "sscanf_scan".to_string();
    let mut args = "mut stream: R".to_string();
    let mut body = String::new();
    writeln!(
        body,
        "    if is_eof(&mut stream, None, None, {}) {{
        return -1;
    }}",
        specs[0].leading_space || skips_leading_whitespace(&specs[0])
    )
    .unwrap();
    writeln!(body, "    let mut count = 0;").unwrap();

    let mut lib_items = vec![];
    let mut num_traits = false;
    for (i, spec) in specs.iter().enumerate() {
        if spec.leading_space && !skips_leading_whitespace(spec) {
            writeln!(body, "    let _ = is_eof(&mut stream, None, None, true);").unwrap();
        }
        let (suffix, ty, parser, item) = match (&spec.conversion, spec.length) {
            (ScanConversion::Int10, None) => ("d", "i32", "parse_decimal", LibItem::ParseDecimal),
            (ScanConversion::Double, Some(fscanf::LengthMod::Long)) => {
                num_traits = true;
                ("lg", "f64", "parse_f64", LibItem::ParseF64)
            }
            _ => return None,
        };
        lib_items.push(item);
        if item == LibItem::ParseDecimal {
            lib_items.push(LibItem::ParseInteger);
        } else {
            lib_items.push(LibItem::ParseFloat);
        }
        write!(name, "_{suffix}").unwrap();
        write!(args, ", v{}: &mut {ty}", i + 1).unwrap();
        writeln!(
            body,
            "    let _v = {parser}(&mut stream, {:?}, None, None);",
            spec.width
        )
        .unwrap();
        writeln!(
            body,
            "    if let Some(_v) = _v {{
        *v{} = _v as {ty};
        count += 1;
    }} else {{
        return count;
    }}",
            i + 1
        )
        .unwrap();
        if spec.trailing_space {
            writeln!(body, "    let _ = is_eof(&mut stream, None, None, true);").unwrap();
        }
    }
    writeln!(body, "    count").unwrap();
    let code = format!(
        "pub(crate) fn {name}<R: std::io::BufRead>({args}) -> i32 {{
{body}}}
"
    );
    Some(ScanFunction {
        name,
        code,
        lib_items,
        num_traits,
    })
}

fn skips_leading_whitespace(spec: &ConversionSpec) -> bool {
    !matches!(
        spec.conversion,
        ScanConversion::Seq | ScanConversion::ScanSet(_)
    )
}
