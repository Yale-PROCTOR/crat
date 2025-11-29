use std::{fmt::Write as _, ops::Deref};

use rustc_ast::*;
use rustc_ast_pretty::pprust;
use rustc_middle::ty;
use rustc_span::sym;
use utils::{
    ast::unwrap_cast_and_paren,
    expr,
    file::fscanf::{self, ConvTy, Conversion, ConversionSpec, LengthMod},
};

use super::{
    likely_lit::LikelyLit,
    stream_ty::*,
    transform::LibItem,
    visitor::{IndicatorCheck, TransformVisitor},
};

impl TransformVisitor<'_, '_, '_> {
    pub(super) fn transform_fscanf<S: StreamExpr, E: Deref<Target = Expr>>(
        &self,
        stream: &S,
        fmt: &Expr,
        args: &[E],
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        match LikelyLit::from_expr(fmt) {
            LikelyLit::Lit(fmt) => self.transform_fscanf_fmt_lit(stream, fmt.as_str(), args, ic),
            LikelyLit::If(_, _, _) => todo!(),
            LikelyLit::Path(_, _) => todo!(),
            LikelyLit::Other(_) => todo!(),
        }
    }

    fn transform_fscanf_fmt_lit<S: StreamExpr, E: Deref<Target = Expr>>(
        &self,
        stream: &S,
        fmt: &str,
        args: &[E],
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream = stream.borrow_for(StreamTrait::BufRead);
        let buf = utils::unescape_byte_str(fmt);
        let specs = fscanf::parse_specs(&buf);
        let parsing_fn = make_parsing_function(&specs);
        let err_eof_args = self.err_eof_args(ic);
        let mut code = format!(
            "crate::c_lib::{}({}, {}",
            parsing_fn.name, stream, err_eof_args
        );
        let mut i = 0;
        let mut decls = String::new();
        let mut assigns = String::new();
        for (spec, arg) in specs.iter().filter(|spec| spec.assign).zip(args) {
            match spec.ty() {
                ConvTy::Scalar(spec_ty) => {
                    if let ExprKind::AddrOf(_, _, e) = &unwrap_cast_and_paren(arg).kind
                        && let ExprKind::Unary(UnOp::Deref, e) = &unwrap_cast_and_paren(e).kind
                        && let ExprKind::MethodCall(call1) = &unwrap_cast_and_paren(e).kind
                        && call1.seg.ident.name == sym::offset
                        && let ExprKind::MethodCall(call2) =
                            &unwrap_cast_and_paren(&call1.receiver).kind
                        && call2.seg.ident.name.as_str() == "as_mut_ptr"
                        && let hir_receiver = self
                            .ast_to_hir
                            .get_expr(call2.receiver.id, self.tcx)
                            .unwrap()
                        && let typeck = self.tcx.typeck(hir_receiver.hir_id.owner)
                        && let ty = typeck.expr_ty(hir_receiver)
                        && let ty::TyKind::Array(ty, _) = ty.kind()
                        && ty.to_string() == spec_ty
                    {
                        write!(
                            code,
                            ", &mut ({})[({}) as usize]",
                            pprust::expr_to_string(&call2.receiver),
                            pprust::expr_to_string(&call1.args[0]),
                        )
                        .unwrap();
                        continue;
                    }
                    if let Some((array, ty)) = self.array_of_as_ptr(arg)
                        && ty.to_string() == spec_ty
                    {
                        write!(code, ", &mut ({})[0]", pprust::expr_to_string(array)).unwrap();
                        continue;
                    }
                    if let ExprKind::MethodCall(call) = &unwrap_cast_and_paren(arg).kind
                        && call.seg.ident.name.as_str() == "map_or"
                        && let ExprKind::MethodCall(call) =
                            &unwrap_cast_and_paren(&call.receiver).kind
                        && call.seg.ident.name.as_str() == "as_deref_mut"
                        && let hir_e = self
                            .ast_to_hir
                            .get_expr(call.receiver.id, self.tcx)
                            .unwrap()
                        && let typeck = self.tcx.typeck(hir_e.hir_id.owner)
                        && let ty = typeck.expr_ty(hir_e)
                        && let ty::TyKind::Adt(adt_def, gargs) = ty.kind()
                        && self.tcx.item_name(adt_def.did()) == sym::Option
                        && let [garg] = gargs[..]
                        && let ty::GenericArgKind::Type(ty) = garg.kind()
                        && let ty::TyKind::Ref(_, ty, _) = ty.kind()
                        && ty.to_string() == spec_ty
                    {
                        write!(
                            code,
                            ", ({}).unwrap()",
                            pprust::expr_to_string(&call.receiver)
                        )
                        .unwrap();
                        continue;
                    }
                    if let ExprKind::AddrOf(_, _, e) = &unwrap_cast_and_paren(arg).kind
                        && let hir_e = self.ast_to_hir.get_expr(e.id, self.tcx).unwrap()
                        && let typeck = self.tcx.typeck(hir_e.hir_id.owner)
                        && let ty = typeck.expr_ty(hir_e).to_string()
                        && ty == spec_ty
                    {
                        write!(code, ", &mut ({})", pprust::expr_to_string(e)).unwrap();
                        continue;
                    }
                    write!(
                        code,
                        ", &mut *(({}) as *mut {})",
                        pprust::expr_to_string(arg),
                        spec_ty,
                    )
                    .unwrap();
                }
                ConvTy::String => {
                    i += 1;
                    write!(decls, "let mut ___v_{i} = Vec::new();").unwrap();
                    write!(code, ", &mut ___v_{i}").unwrap();
                    if let Some((array, ty)) = self.array_of_as_ptr(arg) {
                        if ty == self.tcx.types.i8 {
                            let arg = pprust::expr_to_string(array);
                            write!(
                                assigns,
                                "({arg})[..___v_{i}.len()].copy_from_slice(&___v_{i}[..]);"
                            )
                            .unwrap();
                            continue;
                        } else if ty == self.tcx.types.u8 {
                            let arg = pprust::expr_to_string(array);
                            self.bytemuck.set(true);
                            write!(
                                assigns,
                                "bytemuck::cast_slice_mut(&mut ({arg})[..___v_{i}.len()])
                                    .copy_from_slice(&___v_{i}[..]);"
                            )
                            .unwrap();
                            continue;
                        }
                    }
                    let arg = pprust::expr_to_string(arg);
                    write!(
                        assigns,
                        "let ___buf: &mut [i8] =
                            std::slice::from_raw_parts_mut(({arg}) as _, ___v_{i}.len());
                        ___buf.copy_from_slice(&___v_{i}[..]);"
                    )
                    .unwrap();
                }
            }
        }
        code.push(')');
        self.lib_items.borrow_mut().extend(parsing_fn.lib_items);
        self.lib_items.borrow_mut().insert(LibItem::Peek);
        self.lib_items.borrow_mut().insert(LibItem::IsEof);
        self.parsing_fns
            .borrow_mut()
            .insert(parsing_fn.name, parsing_fn.code);
        if decls.is_empty() && assigns.is_empty() {
            expr!("{code}")
        } else {
            expr!("{{ {decls} let ___res = {code}; {assigns} ___res }}")
        }
    }
}

struct ParsingFunction {
    name: String,
    code: String,
    lib_items: Vec<LibItem>,
}

fn make_parsing_function(specs: &[ConversionSpec]) -> ParsingFunction {
    let mut lib_items = vec![];
    let mut name = "scan".to_string();
    let mut args = String::new();
    write!(
        args,
        "mut stream: R, mut err: Option<&mut i32>, mut eof: Option<&mut i32>"
    )
    .unwrap();
    let mut body = String::new();
    let consume_whitespace = !matches!(
        specs[0].conversion,
        Conversion::Seq | Conversion::ScanSet(_)
    );
    writeln!(
        body,
        "    if is_eof(&mut stream, err.as_deref_mut(), eof.as_deref_mut(), {consume_whitespace}) {{
        return -1;
    }}"
    )
    .unwrap();
    writeln!(body, "    let mut count = 0;").unwrap();
    let mut i = 0;
    for spec in specs {
        let ty = spec.ty();
        if !spec.assign {
            write!(name, "_no_assign").unwrap();
        }
        if let Some(width) = spec.width {
            write!(name, "_w{width}").unwrap();
        }
        if let Some(length) = spec.length {
            if length == LengthMod::LongDouble {
                write!(name, "_big_l",).unwrap();
            } else {
                write!(name, "_{length}",).unwrap();
            }
        }
        match &spec.conversion {
            Conversion::ScanSet(scan_set) => {
                write!(name, "_{}", !scan_set.negative).unwrap();
                for c in &scan_set.chars {
                    if c.is_ascii_digit() || c.is_ascii_lowercase() {
                        write!(name, "_{}", *c as char).unwrap();
                    } else {
                        write!(name, "_{}", *c).unwrap();
                    }
                }
            }
            Conversion::C => write!(name, "_big_c").unwrap(),
            Conversion::S => write!(name, "_big_s").unwrap(),
            Conversion::Percent => write!(name, "_percent").unwrap(),
            conv => write!(name, "_{conv}").unwrap(),
        }

        let assign = if !spec.assign {
            "".to_string()
        } else {
            i += 1;
            let mut assign = match ty {
                ConvTy::Scalar(ty) => {
                    write!(args, ", v{i}: &mut {ty}").unwrap();
                    format!("*v{i} = _v as {ty};\n")
                }
                ConvTy::String => {
                    write!(args, ", v{i}: &mut Vec<i8>").unwrap();
                    format!("v{i}.append(&mut _v); v{i}.push(0);")
                }
            };
            write!(assign, "count += 1;").unwrap();
            assign
        };

        let mut call_args = String::new();
        let f = match &spec.conversion {
            Conversion::Int10 => {
                lib_items.push(LibItem::ParseDecimal);
                lib_items.push(LibItem::ParseInteger);
                "parse_decimal"
            }
            Conversion::Int0 => {
                lib_items.push(LibItem::ParseIntAuto);
                lib_items.push(LibItem::ParseInteger);
                "parse_int_auto"
            }
            Conversion::Octal => {
                lib_items.push(LibItem::ParseOctal);
                lib_items.push(LibItem::ParseInteger);
                "parse_octal"
            }
            Conversion::Unsigned => {
                lib_items.push(LibItem::ParseUnsigned);
                lib_items.push(LibItem::ParseInteger);
                "parse_unsigned"
            }
            Conversion::Hexadecimal => {
                lib_items.push(LibItem::ParseHexadecimal);
                lib_items.push(LibItem::ParseInteger);
                "parse_hexadecimal"
            }
            Conversion::Double => {
                lib_items.push(LibItem::ParseFloat);
                match spec.length {
                    None => {
                        lib_items.push(LibItem::ParseF32);
                        "parse_f32"
                    }
                    Some(LengthMod::Long) => {
                        lib_items.push(LibItem::ParseF64);
                        "parse_f64"
                    }
                    Some(LengthMod::LongDouble) => {
                        lib_items.push(LibItem::ParseF128);
                        "parse_f128"
                    }
                    _ => panic!(),
                }
            }
            Conversion::Str => {
                lib_items.push(LibItem::ParseString);
                "parse_string"
            }
            Conversion::ScanSet(scan_set) => {
                lib_items.push(LibItem::ParseScanSet);
                write!(call_args, ", {}, b\"", !scan_set.negative).unwrap();
                for c in &scan_set.chars {
                    if let Some(s) = utils::escape(*c) {
                        write!(call_args, "{s}").unwrap();
                    } else {
                        write!(call_args, "{}", *c as char).unwrap();
                    }
                }
                write!(call_args, "\"").unwrap();
                "parse_scan_set"
            }
            Conversion::Seq => {
                lib_items.push(LibItem::ParseChar);
                "parse_char"
            }
            Conversion::Pointer => todo!(),
            Conversion::Num => todo!(),
            Conversion::C => todo!(),
            Conversion::S => todo!(),
            Conversion::Percent => todo!(),
        };
        let width = spec.width;
        writeln!(
            body,
            "    let _v = {f}(&mut stream, {width:?}, err.as_deref_mut(), eof.as_deref_mut(){call_args});",
        )
        .unwrap();
        writeln!(
            body,
            "    if let Some(mut _v) = _v {{
{assign}
    }} else {{
        return count;
    }}"
        )
        .unwrap();
    }
    writeln!(body, "    count").unwrap();
    let code = format!(
        "pub(crate) fn {name}<R: std::io::BufRead>({args}) -> i32 {{
{body}}}
"
    );
    ParsingFunction {
        name,
        code,
        lib_items,
    }
}

pub(super) static PEEK: &str = r#"
fn peek<R: std::io::BufRead>(mut stream: R, err: Option<&mut i32>, eof: Option<&mut i32>) -> u8 {
    match stream.fill_buf() {
        Ok([c, ..]) => return *c,
        Ok([]) => {
            if let Some(eof) = eof {
                *eof = 1;
            }
        }
        Err(_) => {
            if let Some(err) = err {
                *err = 1;
            }
        }
    }
    0xff
}
"#;

pub(super) static IS_EOF: &str = r#"
fn is_eof<R: std::io::BufRead>(mut stream: R, mut err: Option<&mut i32>, mut eof: Option<&mut i32>, consume_whitespace: bool) -> bool {
    if consume_whitespace {
        while peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()).is_ascii_whitespace() {
            stream.consume(1);
        }
    }
    peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()) == 0xff
}
"#;

pub(super) static PARSE_CHAR: &str = r#"
fn parse_char<R: std::io::BufRead>(mut stream: R, _width: Option<usize>, mut err: Option<&mut i32>, mut eof: Option<&mut i32>) -> Option<i8> {
    let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
    if c == 0xff {
        None
    } else {
        stream.consume(1);
        Some(c as i8)
    }
}
"#;

pub(super) static PARSE_SCAN_SET: &str = r#"
fn parse_scan_set<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
    pos: bool,
    set: &[u8],
) -> Option<Vec<u8>> {
    let mut v: Vec<u8> = Vec::new();
    while width.is_none_or(|lim| v.len() < lim) {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c == 0xff || set.contains(&c) != pos {
            break;
        }
        v.push(c);
        stream.consume(1);
    }
    if v.is_empty() {
        None
    } else {
        Some(v)
    }
}
"#;

pub(super) static PARSE_STRING: &str = r#"
fn parse_string<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> Option<Vec<i8>> {
    let mut v: Vec<i8> = Vec::new();
    while width.is_none_or(|lim| v.len() < lim) {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c == 0xff {
            break;
        } else if c.is_ascii_whitespace() {
            if !v.is_empty() {
                break;
            }
        } else {
            v.push(c as i8);
        }
        stream.consume(1);
    }
    if v.is_empty() {
        None
    } else {
        Some(v)
    }
}
"#;

pub(super) static PARSE_F32: &str = r#"
fn parse_f32<R: std::io::BufRead>(
    stream: R,
    width: Option<usize>,
    err: Option<&mut i32>,
    eof: Option<&mut i32>,
) -> Option<f32> {
    parse_float(
        stream,
        width,
        err,
        eof,
        FloatValues {
            infinity_value: f32::INFINITY,
            neg_infinity_value: f32::NEG_INFINITY,
            nan_value: f32::NAN,
            zero_value: 0.0,
            is_infinite: f32::is_infinite,
        },
        str::parse,
    ).0
}
"#;

pub(super) static PARSE_F64: &str = r#"
fn parse_f64<R: std::io::BufRead>(
    stream: R,
    width: Option<usize>,
    err: Option<&mut i32>,
    eof: Option<&mut i32>,
) -> Option<f64> {
    parse_float(
        stream,
        width,
        err,
        eof,
        FloatValues {
            infinity_value: f64::INFINITY,
            neg_infinity_value: f64::NEG_INFINITY,
            nan_value: f64::NAN,
            zero_value: 0.0,
            is_infinite: f64::is_infinite,
        },
        str::parse,
    ).0
}
"#;

pub(super) static PARSE_F128: &str = r#"
fn parse_f128<R: std::io::BufRead>(
    stream: R,
    width: Option<usize>,
    err: Option<&mut i32>,
    eof: Option<&mut i32>,
) -> Option<f128::f128> {
    parse_float(
        stream,
        width,
        err,
        eof,
        FloatValues {
            infinity_value: f128::f128::INFINITY,
            neg_infinity_value: f128::f128::NEG_INFINITY,
            nan_value: f128::f128::NAN,
            zero_value: f128::f128::ZERO,
            is_infinite: f128::f128::is_infinite,
        },
        |s| <f128::f128 as num_traits::Num>::from_str_radix(s, 10),
    ).0
}
"#;

pub(super) static PARSE_FLOAT: &str = r#"
struct FloatValues<F> {
    infinity_value: F,
    neg_infinity_value: F,
    nan_value: F,
    zero_value: F,
    is_infinite: fn(F) -> bool,
}

#[inline]
fn parse_float<R: std::io::BufRead, F: Copy + PartialEq, E>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
    values: FloatValues<F>,
    parse: impl Fn(&str) -> Result<F, E>,
) -> (Option<F>, bool) {
    let mut neg = false;
    while peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()).is_ascii_whitespace() {
        stream.consume(1);
    }
    let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
    if c == b'+' {
        stream.consume(1);
    } else if c == b'-' {
        neg = true;
        stream.consume(1);
    }

    let mut i = 0;
    let len = width.unwrap_or(8).min(8);
    let infinity = b"infinity";
    while i < len {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c | 32 == infinity[i] {
            stream.consume(1);
            i += 1;
        } else {
            break;
        }
    }
    if i == 3 || i == 8 {
        peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        let v = if neg {
            values.neg_infinity_value
        } else {
            values.infinity_value
        };
        return (Some(v), false);
    } else if i > 0 {
        return (None, false);
    }

    let mut i = 0;
    let len = width.unwrap_or(3).min(3);
    let nan = b"nan";
    while i < len {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c | 32 == nan[i] {
            stream.consume(1);
            i += 1;
        } else {
            break;
        }
    }
    if i == 3 {
        peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        return (Some(values.nan_value), false);
    } else if i > 0 {
        return (None, false);
    }

    let mut v = Vec::new();
    if neg {
        v.push(b'-');
    }

    if peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()) == b'0' {
        stream.consume(1);
        v.push(b'0');
        if peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()) | 32 == b'x' {
            stream.consume(1);
            panic!();
        }
    }

    let mut dot_seen = false;
    let mut is_nonzero = false;
    loop {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c == b'0' {
        } else if (b'1'..=b'9').contains(&c) {
            is_nonzero = true;
        } else if c == b'.' && !dot_seen {
            dot_seen = true;
        } else {
            break;
        }
        v.push(c);
        stream.consume(1);
    }

    if !v.iter().any(|c| c.is_ascii_digit()) {
        return (None, false);
    }

    if peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()) | 32 == b'e' {
        v.push(b'e');
        stream.consume(1);

        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c == b'+' || c == b'-' {
            v.push(c);
            stream.consume(1);
        }

        loop {
            let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
            if c.is_ascii_digit() {
                v.push(c);
                stream.consume(1);
            } else {
                break;
            }
        }

        while !v.last().unwrap().is_ascii_digit() {
            v.pop();
        }
    }

    let s = std::str::from_utf8(&v).unwrap();
    let f = match parse(s) {
        Ok(f) => f,
        Err(_) => panic!(),
    };
    let erange = (values.is_infinite)(f) || is_nonzero && f == values.zero_value;
    (Some(f), erange)
}
"#;

pub(super) static PARSE_DECIMAL: &str = r#"
fn parse_decimal<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> Option<u64> {
    parse_integer(&mut stream, 10, true, width, err.as_deref_mut(), eof.as_deref_mut()).0
}
"#;

pub(super) static PARSE_INT_AUTO: &str = r#"
fn parse_int_auto<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> Option<u64> {
    parse_integer(&mut stream, 0, true, width, err.as_deref_mut(), eof.as_deref_mut()).0
}
"#;

pub(super) static PARSE_OCTAL: &str = r#"
fn parse_octal<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> Option<u64> {
    parse_integer(&mut stream, 8, false, width, err.as_deref_mut(), eof.as_deref_mut()).0
}
"#;

pub(super) static PARSE_UNSIGNED: &str = r#"
fn parse_unsigned<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> Option<u64> {
    parse_integer(&mut stream, 10, false, width, err.as_deref_mut(), eof.as_deref_mut()).0
}
"#;

pub(super) static PARSE_HEXADECIMAL: &str = r#"
fn parse_hexadecimal<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> Option<u64> {
    parse_integer(&mut stream, 16, false, width, err.as_deref_mut(), eof.as_deref_mut()).0
}
"#;

pub(super) static PARSE_INTEGER: &str = r#"
#[inline]
fn parse_integer<R: std::io::BufRead>(
    mut stream: R,
    mut base: u32,
    signed: bool,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> (Option<u64>, bool) {
    let width_reached = |len: usize| width.is_some_and(|w| len >= w);

    while peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut()).is_ascii_whitespace() {
        stream.consume(1);
    }

    let mut len = 0;
    let mut negative = false;
    let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
    if c == b'+' {
        stream.consume(1);
        len += 1;
    } else if c == b'-' {
        negative = true;
        stream.consume(1);
        len += 1;
    }
    if width_reached(len) {
        return (None, false);
    }

    let mut num = String::new();
    if base == 0 || base == 16 {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c == b'0' {
            stream.consume(1);
            len += 1;
            let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
            if c == b'x' || c == b'X' {
                base = 16;
                stream.consume(1);
                len += 1;
            } else {
                num.push('0');
                if base == 0 {
                    base = 8;
                }
            }
        } else if base == 0 {
            base = 10;
        }
    }

    while !width_reached(len) {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if (base <= 10 && (b'0'..b'0' + (base as u8)).contains(&c))
            || (base > 10
                && ((b'0'..=b'9').contains(&c)
                    || (b'a'..b'a' + (base - 10) as u8).contains(&c)
                    || (b'A'..b'A' + (base - 10) as u8).contains(&c)))
        {
            num.push(c as char);
            stream.consume(1);
            len += 1;
        } else {
            break;
        }
    }

    if num.is_empty() {
        return (None, false);
    }

    match u64::from_str_radix(&num, base) {
        Ok(v) => {
            if !signed {
                (Some(v), false)
            } else if !negative {
                if v > i64::MAX as u64 {
                    (Some(i64::MAX as u64), true)
                } else {
                    (Some(v), false)
                }
            } else if v > (i64::MIN as u64).wrapping_neg() {
                (Some(i64::MIN as u64), true)
            } else {
                (Some(v.wrapping_neg()), false)
            }
        }
        Err(_) => {
            if !signed {
                (Some(u64::MAX), true)
            } else if !negative {
                (Some(i64::MAX as u64), true)
            } else {
                (Some(i64::MIN as u64), true)
            }
        }
    }
}
"#;
