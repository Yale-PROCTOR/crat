use std::{fmt::Write as _, ops::Deref};

use rustc_ast::*;
use rustc_ast_pretty::pprust;
use rustc_middle::ty;
use rustc_span::Symbol;
use utils::{
    ast::unwrap_cast_and_paren,
    expr,
    file::fprintf::{self, Conversion, FlagChar, Width},
};

use super::{
    likely_lit::LikelyLit,
    stream_ty::*,
    transform::LibItem,
    visitor::{IndicatorCheck, TransformVisitor},
};

pub(super) const FPRINTF_ITEMS: [LibItem; 8] = [
    LibItem::Fprintf,
    LibItem::Vfprintf,
    LibItem::Xu8,
    LibItem::Xu16,
    LibItem::Xu32,
    LibItem::Xu64,
    LibItem::Gf64,
    LibItem::Af64,
];

pub(super) const VFPRINTF_ITEMS: [LibItem; 7] = [
    LibItem::Vfprintf,
    LibItem::Xu8,
    LibItem::Xu16,
    LibItem::Xu32,
    LibItem::Xu64,
    LibItem::Gf64,
    LibItem::Af64,
];

impl TransformVisitor<'_, '_, '_> {
    pub(super) fn transform_fprintf<S: StreamExpr, E: Deref<Target = Expr>>(
        &self,
        stream: &S,
        fmt: &Expr,
        args: &[E],
        ctx: FprintfCtx<'_>,
    ) -> Expr {
        match LikelyLit::from_expr(fmt) {
            LikelyLit::Lit(fmt) => return self.transform_fprintf_lit(stream, fmt, args, ctx),
            LikelyLit::Path(_, span) => {
                let loc = self.hir.bound_span_to_loc[&span];
                let static_span = self.hir.loc_to_binding_span[&loc];
                if let Some(fmt) = self.analysis_res.static_span_to_lit.get(&static_span) {
                    return self.transform_fprintf_lit(stream, *fmt, args, ctx);
                }
            }
            _ => {}
        }
        let stream_str = stream.borrow_for(StreamTrait::Write);
        let fmt = pprust::expr_to_string(fmt);
        let mut s = format!("crate::stdio::rs_fprintf({stream_str}, {fmt}");
        for arg in args {
            let arg = pprust::expr_to_string(arg);
            s.push_str(", ");
            s.push_str(&arg);
        }
        s.push(')');
        self.lib_items.borrow_mut().extend(FPRINTF_ITEMS);
        self.update_error_no_eof(ctx.ic, s, stream)
    }

    pub(super) fn transform_fprintf_lit<S: StreamExpr, E: Deref<Target = Expr>>(
        &self,
        stream: &S,
        fmt: Symbol,
        args: &[E],
        ctx: FprintfCtx<'_>,
    ) -> Expr {
        let mut buf = utils::unescape_byte_str(fmt.as_str());
        if ctx.wide {
            let mut new_buf: Vec<u8> = vec![];
            for c in buf.chunks_exact(4) {
                let c = u32::from_le_bytes(c.try_into().unwrap());
                new_buf.push(c.try_into().unwrap());
            }
            buf = new_buf;
        }
        let rsfmt = to_rust_format(&buf);
        assert!(args.len() >= rsfmt.casts.len());
        let mut new_args = String::new();
        let mut width_args = String::new();
        for (i, (arg, cast)) in args.iter().zip(rsfmt.casts).enumerate() {
            let width_arg_idx =
                rsfmt
                    .width_args
                    .iter()
                    .enumerate()
                    .find_map(|(width_arg_idx, arg_idx)| {
                        if *arg_idx == i {
                            Some(width_arg_idx)
                        } else {
                            None
                        }
                    });
            let args = if let Some(width_arg_idx) = width_arg_idx {
                write!(width_args, "width{width_arg_idx} = ").unwrap();
                &mut width_args
            } else {
                &mut new_args
            };
            let arg_str = pprust::expr_to_string(arg);
            match cast {
                "&str" => {
                    let cstr = match &unwrap_cast_and_paren(arg).kind {
                        ExprKind::MethodCall(call)
                            if call.seg.ident.name == rustc_span::sym::as_ptr =>
                        {
                            let hir_receiver = self
                                .ast_to_hir
                                .get_expr(call.receiver.id, self.tcx)
                                .unwrap();
                            let typeck = self.tcx.typeck(hir_receiver.hir_id.owner);
                            let ty = typeck.expr_ty(hir_receiver);
                            let (ty::TyKind::Array(ety, _) | ty::TyKind::Slice(ety)) =
                                ty.peel_refs().kind()
                            else {
                                panic!("{arg_str} {ty}");
                            };
                            let receiver_str = pprust::expr_to_string(&call.receiver);
                            if *ety == self.tcx.types.u8 {
                                format!(
                                    "
    std::ffi::CStr::from_bytes_until_nul(&({receiver_str})).unwrap()"
                                )
                            } else if ety.is_numeric() {
                                self.bytemuck.set(true);
                                format!(
                                    "
    std::ffi::CStr::from_bytes_until_nul(bytemuck::cast_slice(&({receiver_str}))).unwrap()"
                                )
                            } else {
                                panic!("{arg_str} {ty}");
                            }
                        }
                        ExprKind::AddrOf(_, _, pointee) => {
                            if let ExprKind::Index(base, idx, _) =
                                &unwrap_cast_and_paren(pointee).kind
                            {
                                let hir_base = self.ast_to_hir.get_expr(base.id, self.tcx).unwrap();
                                let typeck = self.tcx.typeck(hir_base.hir_id.owner);
                                let ty = typeck.expr_ty(hir_base);
                                let (ty::TyKind::Array(ety, _) | ty::TyKind::Slice(ety)) =
                                    ty.peel_refs().kind()
                                else {
                                    panic!("{arg_str} {ty}");
                                };
                                let base_str = pprust::expr_to_string(base);
                                let idx_str = pprust::expr_to_string(idx);
                                if *ety == self.tcx.types.u8 {
                                    format!(
                                        "
    std::ffi::CStr::from_bytes_until_nul(&({base_str})[{idx_str}..]).unwrap()"
                                    )
                                } else if ety.is_numeric() {
                                    self.bytemuck.set(true);
                                    format!(
                                    "
    std::ffi::CStr::from_bytes_until_nul(bytemuck::cast_slice(&({base_str})[{idx_str}..])).unwrap()"
                                )
                                } else {
                                    panic!("{arg_str} {ty}");
                                }
                            } else {
                                format!("std::ffi::CStr::from_ptr(({arg_str}) as _)")
                            }
                        }
                        _ => {
                            format!("std::ffi::CStr::from_ptr(({arg_str}) as _)")
                        }
                    };
                    if self.config.assume_to_str_ok {
                        write!(args, "{cstr}.to_str().unwrap(), ").unwrap();
                    } else {
                        write!(
                            args,
                            "{{
    let ___s = {cstr};
    if let Ok(___s) = ___s.to_str() {{
        ___s.to_string()
    }} else {{
        ___s.to_bytes().iter().map(|&_b| _b as char).collect()
    }}
}}, "
                        )
                        .unwrap();
                    }
                }
                "String" => write!(
                    args,
                    "{{
    let mut p: *const u8 = {arg_str} as _;
    let mut s: String = String::new();
    loop {{
        let slice = std::slice::from_raw_parts(p, 4);
        let i = u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]);
        if i == 0 {{
            break s;
        }}
        s.push(std::char::from_u32(i).unwrap());
        p = p.offset(4);
    }}
}}, "
                )
                .unwrap(),
                "crate::stdio::Xu8" | "crate::stdio::Xu16" | "crate::stdio::Xu32"
                | "crate::stdio::Xu64" | "crate::stdio::Gf64" | "crate::stdio::Af64" => {
                    match cast {
                        "crate::stdio::Xu8" => self.lib_items.borrow_mut().insert(LibItem::Xu8),
                        "crate::stdio::Xu16" => self.lib_items.borrow_mut().insert(LibItem::Xu16),
                        "crate::stdio::Xu32" => self.lib_items.borrow_mut().insert(LibItem::Xu32),
                        "crate::stdio::Xu64" => self.lib_items.borrow_mut().insert(LibItem::Xu64),
                        "crate::stdio::Gf64" => self.lib_items.borrow_mut().insert(LibItem::Gf64),
                        "crate::stdio::Af64" => self.lib_items.borrow_mut().insert(LibItem::Af64),
                        _ => panic!(),
                    };
                    write!(args, "{cast}(({arg_str}) as _), ").unwrap()
                }
                _ => write!(args, "({arg_str}) as {cast}, ").unwrap(),
            }
        }
        let stream_str = stream.borrow_for(StreamTrait::Write);
        if ctx.retval_used {
            expr!(
                "{{
    use std::io::Write;
    let string_to_print = std::fmt::format(format_args!(\"{}\", {}{}));
    match write!({}, \"{{}}\", string_to_print) {{
        Ok(_) => string_to_print.len() as i32,
        Err(_) => {{
            {}
            -1
        }}
    }}
}}",
                rsfmt.format,
                new_args,
                width_args,
                stream_str,
                self.error_handling_no_eof(ctx.ic, stream),
            )
        } else {
            expr!(
                "{{
    use std::io::Write;
    match write!({}, \"{}\", {}{}) {{
        Ok(_) => {{}}
        Err(_) => {{
            {}
        }}
    }}
}}",
                stream_str,
                rsfmt.format,
                new_args,
                width_args,
                self.error_handling_no_eof(ctx.ic, stream),
            )
        }
    }

    #[inline]
    pub(super) fn transform_vfprintf<S: StreamExpr>(
        &self,
        stream: &S,
        fmt: &Expr,
        args: &Expr,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        let stream_str = stream.borrow_for(StreamTrait::Write);
        let fmt = pprust::expr_to_string(fmt);
        let args = pprust::expr_to_string(args);
        self.lib_items.borrow_mut().extend(VFPRINTF_ITEMS);
        self.update_error_no_eof(
            ic,
            format!("crate::stdio::rs_vfprintf({stream_str}, {fmt}, {args})"),
            stream,
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct FprintfCtx<'a> {
    pub(super) wide: bool,
    pub(super) retval_used: bool,
    pub(super) ic: IndicatorCheck<'a>,
}

#[derive(Debug)]
pub(super) struct RustFormat {
    pub(super) format: String,
    pub(super) casts: Vec<&'static str>,
    pub(super) width_args: Vec<usize>,
}

pub(super) fn to_rust_format(mut remaining: &[u8]) -> RustFormat {
    let mut format = String::new();
    let mut casts = vec![];
    let mut width_count = 0;
    let mut width_args = vec![];
    loop {
        let res = fprintf::parse_format(remaining);
        utils::format_rust_str_from_bytes(&mut format, res.prefix).unwrap();
        if let Some(cs) = res.conversion_spec {
            let mut fmt = String::new();
            let mut conv = String::new();
            let mut minus = false;
            for flag in cs.flags {
                match flag {
                    FlagChar::Apostrophe => todo!(),
                    FlagChar::Minus => minus = true,
                    FlagChar::Plus => fmt.push('+'),
                    FlagChar::Space => todo!(),
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
                    Width::Asterisk => {
                        write!(fmt, "width{width_count}$").unwrap();
                        width_count += 1;
                        width_args.push(casts.len());
                        casts.push("usize");
                    }
                    Width::Decimal(n) => fmt.push_str(&n.to_string()),
                }
            }
            if let Some(precision) = cs.precision {
                fmt.push('.');
                match precision {
                    Width::Asterisk => {
                        fmt.push('*');
                        casts.push("usize");
                    }
                    Width::Decimal(n) => fmt.push_str(&n.to_string()),
                }
            }
            match cs.conversion {
                Conversion::Int | Conversion::Unsigned | Conversion::Char | Conversion::Str => {}
                Conversion::Octal => fmt.push('o'),
                Conversion::Hexadecimal => fmt.push('x'),
                Conversion::HexadecimalUpper => fmt.push('X'),
                Conversion::Double => {
                    if cs.precision.is_none() {
                        fmt.push_str(".6");
                    }
                }
                Conversion::DoubleExp => fmt.push('e'),
                Conversion::DoubleAuto => {}
                Conversion::DoubleHex => {}
                Conversion::Pointer => fmt.push_str("#x"),
                Conversion::Num | Conversion::C | Conversion::S => unimplemented!(),
                Conversion::Percent => conv = "%".to_string(),
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
            if let Some(cast) = cs.conversion.ty(cs.length) {
                casts.push(cast);
            }
        }
        if let Some(rem) = res.remaining {
            remaining = rem;
        } else {
            break;
        }
    }
    RustFormat {
        format,
        casts,
        width_args,
    }
}

pub(super) const FPRINTF: &str = r#"
#[inline]
pub(crate) unsafe extern "C" fn rs_fprintf<W: std::io::Write>(
    stream: W,
    fmt: *const i8,
    args: ...
) -> (i32, i32) {
    let mut args_0: ::std::ffi::VaListImpl;
    args_0 = args.clone();
    rs_vfprintf(stream, fmt, args_0.as_va_list())
}
"#;

pub(super) const VFPRINTF: &str = r#"
pub(crate) unsafe fn rs_vfprintf<W: std::io::Write>(
    mut stream: W,
    fmt: *const i8,
    mut args: std::ffi::VaList,
) -> (i32, i32) {
    let fmt = std::ffi::CStr::from_ptr(fmt as _);
    let mut state = PrintfState::Percent;
    let mut flags = Vec::new();
    let mut width = None;
    let mut precision = None;
    let mut length = None;
    let mut conversion = None;
    let mut count = 0;
    for c in fmt.to_bytes() {
        if state == PrintfState::Percent {
            if *c == b'%' {
                state = PrintfState::Flag;
            } else {
                match stream.write_all(&[*c]) {
                    Ok(_) => count += 1,
                    Err(_) => return (-1, 1),
                }
            }
        } else if (b'1'..=b'9').contains(c) || (*c == b'0' && state != PrintfState::Flag) {
            match state {
                PrintfState::Flag => {
                    width = Some(PrintfWidth::Decimal((c - b'0') as usize));
                    state = PrintfState::Width;
                }
                PrintfState::Width => {
                    let Some(PrintfWidth::Decimal(n)) = &mut width else { panic!() };
                    *n = *n * 10 + (c - b'0') as usize;
                }
                PrintfState::Precision => match &mut precision {
                    None => precision = Some(PrintfWidth::Decimal((c - b'0') as usize)),
                    Some(PrintfWidth::Decimal(n)) => *n = *n * 10 + (c - b'0') as usize,
                    _ => panic!(),
                },
                _ => panic!(),
            }
        } else if let Some(flag) = PrintfFlagChar::from_u8(*c) {
            flags.push(flag);
        } else if *c == b'*' {
            match state {
                PrintfState::Flag => {
                    width = Some(PrintfWidth::Asterisk);
                    state = PrintfState::Period;
                }
                PrintfState::Precision => {
                    precision = Some(PrintfWidth::Asterisk);
                    state = PrintfState::Length;
                }
                _ => panic!(),
            }
        } else if *c == b'.' {
            if matches!(
                state,
                PrintfState::Flag | PrintfState::Width | PrintfState::Period
            ) {
                state = PrintfState::Precision;
            } else {
                panic!()
            }
        } else if let Some(len) = PrintfLengthMod::from_u8(*c) {
            match len {
                PrintfLengthMod::Short => match state {
                    PrintfState::Flag
                    | PrintfState::Width
                    | PrintfState::Period
                    | PrintfState::Precision
                    | PrintfState::Length => {
                        state = PrintfState::H;
                    }
                    PrintfState::H => {
                        length = Some(PrintfLengthMod::Char);
                        state = PrintfState::Conversion;
                    }
                    _ => panic!(),
                },
                PrintfLengthMod::Long => match state {
                    PrintfState::Flag
                    | PrintfState::Width
                    | PrintfState::Period
                    | PrintfState::Precision
                    | PrintfState::Length => {
                        state = PrintfState::L;
                    }
                    PrintfState::L => {
                        length = Some(PrintfLengthMod::LongLong);
                        state = PrintfState::Conversion;
                    }
                    _ => panic!(),
                },
                _ => {
                    length = Some(len);
                    state = PrintfState::Conversion;
                }
            }
        } else if let Some(conv) = PrintfConversion::from_u8(*c) {
            match state {
                PrintfState::Flag
                | PrintfState::Width
                | PrintfState::Period
                | PrintfState::Precision
                | PrintfState::Length
                | PrintfState::Conversion => {
                    conversion = Some(conv);
                }
                PrintfState::H => {
                    length = Some(PrintfLengthMod::Short);
                    conversion = Some(conv);
                }
                PrintfState::L => {
                    length = Some(PrintfLengthMod::Long);
                    conversion = Some(conv);
                }
                _ => panic!(),
            }
        } else {
            panic!()
        }
        if let Some(conversion) = conversion.take() {
            let mut opt = std::fmt::FormattingOptions::new();
            let mut minus = false;
            for flag in flags.drain(..) {
                match flag {
                    PrintfFlagChar::Apostrophe => panic!(),
                    PrintfFlagChar::Minus => {
                        minus = true;
                    }
                    PrintfFlagChar::Plus => {
                        opt.sign(Some(std::fmt::Sign::Plus));
                    }
                    PrintfFlagChar::Space => panic!(),
                    PrintfFlagChar::Hash => {
                        opt.alternate(true);
                    }
                    PrintfFlagChar::Zero => {
                        opt.sign_aware_zero_pad(true);
                    }
                }
            }
            if minus {
                opt.align(Some(std::fmt::Alignment::Left));
            } else {
                opt.align(Some(std::fmt::Alignment::Right));
            }
            if let Some(width) = width.take() {
                match width {
                    PrintfWidth::Asterisk => {
                        let width = args.arg::<u32>() as u16;
                        opt.width(Some(width));
                    }
                    PrintfWidth::Decimal(n) => {
                        opt.width(Some(n as u16));
                    }
                }
            }
            if let Some(precision) = precision.take() {
                match precision {
                    PrintfWidth::Asterisk => {
                        let precision = args.arg::<u32>() as u16;
                        opt.precision(Some(precision));
                    }
                    PrintfWidth::Decimal(n) => {
                        opt.precision(Some(n as u16));
                    }
                }
            }
            match conversion {
                PrintfConversion::Double => {
                    if opt.get_precision().is_none() {
                        opt.precision(Some(6));
                    }
                }
                PrintfConversion::Pointer => {
                    opt.alternate(true);
                }
                _ => {}
            }
            let mut s = String::new();
            let mut fmt = std::fmt::Formatter::new(&mut s, opt);
            match (conversion, length.take()) {
                (PrintfConversion::Int, None) => {
                    let v = args.arg::<i32>();
                    if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Int, Some(PrintfLengthMod::Char)) => {
                    let v = args.arg::<i32>() as i8;
                    if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Int, Some(PrintfLengthMod::Short)) => {
                    let v = args.arg::<i32>() as i16;
                    if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (
                    PrintfConversion::Int,
                    Some(
                        PrintfLengthMod::Long
                        | PrintfLengthMod::LongLong
                        | PrintfLengthMod::IntMax
                        | PrintfLengthMod::Size,
                    ),
                ) => {
                    let v = args.arg::<i64>();
                    if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Int, Some(PrintfLengthMod::PtrDiff)) => {
                    let v = args.arg::<u64>();
                    if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Int, Some(PrintfLengthMod::LongDouble)) => panic!(),
                (PrintfConversion::Octal, None) => {
                    let v = args.arg::<u32>();
                    if std::fmt::Octal::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Octal, Some(PrintfLengthMod::Char)) => {
                    let v = args.arg::<u32>() as u8;
                    if std::fmt::Octal::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Octal, Some(PrintfLengthMod::Short)) => {
                    let v = args.arg::<u32>() as u16;
                    if std::fmt::Octal::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (
                    PrintfConversion::Octal,
                    Some(
                        PrintfLengthMod::Long
                        | PrintfLengthMod::LongLong
                        | PrintfLengthMod::IntMax
                        | PrintfLengthMod::Size
                        | PrintfLengthMod::PtrDiff,
                    ),
                ) => {
                    let v = args.arg::<u64>();
                    if std::fmt::Octal::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Octal, Some(PrintfLengthMod::LongDouble)) => panic!(),
                (PrintfConversion::Unsigned, None) => {
                    let v = args.arg::<u32>();
                    if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Unsigned, Some(PrintfLengthMod::Char)) => {
                    let v = args.arg::<u32>() as u8;
                    if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Unsigned, Some(PrintfLengthMod::Short)) => {
                    let v = args.arg::<u32>() as u16;
                    if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (
                    PrintfConversion::Unsigned,
                    Some(
                        PrintfLengthMod::Long
                        | PrintfLengthMod::LongLong
                        | PrintfLengthMod::IntMax
                        | PrintfLengthMod::Size
                        | PrintfLengthMod::PtrDiff,
                    ),
                ) => {
                    let v = args.arg::<u64>();
                    if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Unsigned, Some(PrintfLengthMod::LongDouble)) => panic!(),
                (PrintfConversion::Hexadecimal, None) => {
                    let v = args.arg::<u32>();
                    if std::fmt::LowerHex::fmt(&Xu32(v), &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Hexadecimal, Some(PrintfLengthMod::Char)) => {
                    let v = args.arg::<u32>() as u8;
                    if std::fmt::LowerHex::fmt(&Xu8(v), &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Hexadecimal, Some(PrintfLengthMod::Short)) => {
                    let v = args.arg::<u32>() as u16;
                    if std::fmt::LowerHex::fmt(&Xu16(v), &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (
                    PrintfConversion::Hexadecimal,
                    Some(
                        PrintfLengthMod::Long
                        | PrintfLengthMod::LongLong
                        | PrintfLengthMod::IntMax
                        | PrintfLengthMod::Size
                        | PrintfLengthMod::PtrDiff,
                    ),
                ) => {
                    let v = args.arg::<u64>();
                    if std::fmt::LowerHex::fmt(&Xu64(v), &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Hexadecimal, Some(PrintfLengthMod::LongDouble)) => panic!(),
                (PrintfConversion::HexadecimalUpper, None) => {
                    let v = args.arg::<u32>();
                    if std::fmt::UpperHex::fmt(&Xu32(v), &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::HexadecimalUpper, Some(PrintfLengthMod::Char)) => {
                    let v = args.arg::<u32>() as u8;
                    if std::fmt::UpperHex::fmt(&Xu8(v), &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::HexadecimalUpper, Some(PrintfLengthMod::Short)) => {
                    let v = args.arg::<u32>() as u16;
                    if std::fmt::UpperHex::fmt(&Xu16(v), &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (
                    PrintfConversion::HexadecimalUpper,
                    Some(
                        PrintfLengthMod::Long
                        | PrintfLengthMod::LongLong
                        | PrintfLengthMod::IntMax
                        | PrintfLengthMod::Size
                        | PrintfLengthMod::PtrDiff,
                    ),
                ) => {
                    let v = args.arg::<u64>();
                    if std::fmt::UpperHex::fmt(&Xu64(v), &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::HexadecimalUpper, Some(PrintfLengthMod::LongDouble)) => panic!(),
                (PrintfConversion::Double, None | Some(PrintfLengthMod::Long)) => {
                    let v = args.arg::<f64>();
                    if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Double, _) => panic!(),
                (PrintfConversion::DoubleExp, None | Some(PrintfLengthMod::Long)) => {
                    let v = args.arg::<f64>();
                    if std::fmt::LowerExp::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::DoubleExp, _) => panic!(),
                (PrintfConversion::DoubleAuto, None | Some(PrintfLengthMod::Long)) => {
                    let v = args.arg::<f64>();
                    if std::fmt::Display::fmt(&Gf64(v), &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::DoubleAuto, _) => panic!(),
                (PrintfConversion::DoubleHex, None | Some(PrintfLengthMod::Long)) => {
                    let v = args.arg::<f64>();
                    if std::fmt::Display::fmt(&Af64(v), &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::DoubleHex, _) => panic!(),
                (PrintfConversion::Char, _) => {
                    let v = args.arg::<u32>() as u8 as char;
                    if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Str, None) => {
                    let v = args.arg::<*const u8>();
                    let v = std::ffi::CStr::from_ptr(v as _);
                    if let Ok(v) = v.to_str() {
                        if std::fmt::Display::fmt(&v, &mut fmt).is_err() {
                            return (-1, 1);
                        }
                    } else {
                        let v = v.to_bytes();
                        match stream.write_all(v) {
                            Ok(_) => count += v.len() as i32,
                            Err(_) => return (-1, 1),
                        }
                        state = PrintfState::Percent;
                        continue;
                    }
                }
                (PrintfConversion::Str, _) => panic!(),
                (PrintfConversion::Pointer, _) => {
                    let v = args.arg::<*const std::ffi::c_void>() as usize;
                    if std::fmt::LowerHex::fmt(&v, &mut fmt).is_err() {
                        return (-1, 1);
                    }
                }
                (PrintfConversion::Num | PrintfConversion::C | PrintfConversion::S, _) => {
                    panic!()
                }
                (PrintfConversion::Percent, _) => s.push('%'),
            }
            match stream.write_all(s.as_bytes()) {
                Ok(_) => count += s.len() as i32,
                Err(_) => return (-1, 1),
            }
            state = PrintfState::Percent;
        }
    }
    (count, 0)
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum PrintfState {
    Percent,
    Flag,
    Width,
    Period,
    Precision,
    Length,
    H,
    L,
    Conversion,
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum PrintfFlagChar {
    Apostrophe,
    Minus,
    Plus,
    Space,
    Hash,
    Zero,
}
impl PrintfFlagChar {
    #[inline]
    pub(super) fn from_u8(c: u8) -> Option<Self> {
        match c {
            b'\'' => Some(Self::Apostrophe),
            b'-' => Some(Self::Minus),
            b'+' => Some(Self::Plus),
            b' ' => Some(Self::Space),
            b'#' => Some(Self::Hash),
            b'0' => Some(Self::Zero),
            _ => None,
        }
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum PrintfWidth {
    Asterisk,
    Decimal(usize),
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum PrintfLengthMod {
    Char,
    Short,
    Long,
    LongLong,
    IntMax,
    Size,
    PtrDiff,
    LongDouble,
}
impl PrintfLengthMod {
    #[inline]
    pub(super) fn from_u8(c: u8) -> Option<Self> {
        match c {
            b'h' => Some(Self::Short),
            b'l' => Some(Self::Long),
            b'j' => Some(Self::IntMax),
            b'z' => Some(Self::Size),
            b't' => Some(Self::PtrDiff),
            b'L' => Some(Self::LongDouble),
            _ => None,
        }
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum PrintfConversion {
    Int,
    Octal,
    Unsigned,
    Hexadecimal,
    HexadecimalUpper,
    Double,
    DoubleExp,
    DoubleAuto,
    DoubleHex,
    Char,
    Str,
    Pointer,
    Num,
    C,
    S,
    Percent,
}
impl PrintfConversion {
    #[inline]
    pub(super) fn from_u8(c: u8) -> Option<Self> {
        match c {
            b'd' | b'i' => Some(Self::Int),
            b'o' => Some(Self::Octal),
            b'u' => Some(Self::Unsigned),
            b'x' => Some(Self::Hexadecimal),
            b'X' => Some(Self::HexadecimalUpper),
            b'f' | b'F' => Some(Self::Double),
            b'e' | b'E' => Some(Self::DoubleExp),
            b'g' | b'G' => Some(Self::DoubleAuto),
            b'a' | b'A' => Some(Self::DoubleHex),
            b'c' => Some(Self::Char),
            b's' => Some(Self::Str),
            b'p' => Some(Self::Pointer),
            b'n' => Some(Self::Num),
            b'C' => Some(Self::C),
            b'S' => Some(Self::S),
            b'%' => Some(Self::Percent),
            _ => None,
        }
    }
}
"#;

pub(super) const XU8: &str = r#"
pub(crate) struct Xu8(pub(crate) u8);
impl std::fmt::LowerHex for Xu8 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::LowerHex::fmt(&self.0, f)
        }
    }
}
impl std::fmt::UpperHex for Xu8 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::UpperHex::fmt(&self.0, f)
        }
    }
}
"#;

pub(super) const XU16: &str = r#"
pub(crate) struct Xu16(pub(crate) u16);
impl std::fmt::LowerHex for Xu16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::LowerHex::fmt(&self.0, f)
        }
    }
}
impl std::fmt::UpperHex for Xu16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::UpperHex::fmt(&self.0, f)
        }
    }
}
"#;

pub(super) const XU32: &str = r#"
pub(crate) struct Xu32(pub(crate) u32);
impl std::fmt::LowerHex for Xu32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::LowerHex::fmt(&self.0, f)
        }
    }
}
impl std::fmt::UpperHex for Xu32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::UpperHex::fmt(&self.0, f)
        }
    }
}
"#;

pub(super) const XU64: &str = r#"
pub(crate) struct Xu64(pub(crate) u64);
impl std::fmt::LowerHex for Xu64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::LowerHex::fmt(&self.0, f)
        }
    }
}
impl std::fmt::UpperHex for Xu64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() && self.0 == 0 && f.precision().unwrap_or_default() == 0 {
            f.write_str("0")
        } else {
            std::fmt::UpperHex::fmt(&self.0, f)
        }
    }
}
"#;

pub(super) const GF64: &str = r#"
pub(crate) struct Gf64(pub(crate) f64);
impl std::fmt::Display for Gf64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let v = self.0;
        if v.is_nan() {
            return f.write_str("nan");
        }
        if v.is_infinite() {
            return f.write_str(if v.is_sign_negative() { "-inf" } else { "inf" });
        }
        let sign = if v.is_sign_negative() { "-" } else { "" };
        let abs = v.abs();
        let p = match f.precision() {
            Some(0) => 1,
            Some(n) => n,
            None => 6,
        };
        let x = if abs == 0.0 {
            0
        } else {
            abs.log10().floor() as i32
        };
        let s = if x >= -4 && x < p as i32 {
            let frac_prec = (p as i32 - (x + 1)).max(0) as usize;
            let mut s = std::fmt::format(format_args!("{abs:.frac_prec$}"));
            if !f.alternate() && s.contains('.') {
                while s.ends_with('0') {
                    s.pop();
                }
                if s.ends_with('.') {
                    s.pop();
                }
            }
            s
        } else {
            let exp_prec = p.saturating_sub(1);
            let s_full = std::fmt::format(format_args!("{abs:.exp_prec$e}"));
            let idx = s_full.find('e').unwrap();
            let mut mant = s_full[..idx].to_string();
            let exp = &s_full[idx + 1..];
            if !f.alternate() && mant.contains('.') {
                while mant.ends_with('0') {
                    mant.pop();
                }
                if mant.ends_with('.') {
                    mant.pop();
                }
            }
            let (sign_e, digits) = if let Some(digits) = exp.strip_prefix('-') {
                ('-', digits)
            } else {
                (
                    '+',
                    if let Some(digits) = exp.strip_prefix('+') {
                        digits
                    } else {
                        exp
                    },
                )
            };
            let digits = if digits.len() < 2 {
                std::fmt::format(format_args!("0{digits}"))
            } else {
                digits.to_string()
            };
            std::fmt::format(format_args!("{mant}e{sign_e}{digits}"))
        };
        f.write_str(sign)?;
        f.write_str(&s)
    }
}
"#;

pub(super) const AF64: &str = r#"
pub(crate) struct Af64(pub(crate) f64);
impl std::fmt::Display for Af64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let v = self.0;
        if v.is_nan() {
            return f.write_str("nan");
        }
        if v.is_infinite() {
            if v.is_sign_negative() {
                f.write_str("-")?;
            }
            return f.write_str("inf");
        }
        let bits = v.to_bits();
        let sign = (bits >> 63) != 0;
        let exp_bits = ((bits >> 52) & 0x7ff) as i32;
        let frac_bits = bits & ((1u64 << 52) - 1);
        if sign {
            f.write_str("-")?;
        }
        if exp_bits == 0 && frac_bits == 0 {
            return f.write_str("0x0p+0");
        }
        let mut leading = if exp_bits == 0 { 0u8 } else { 1u8 };
        let mut e2: i32 = if exp_bits == 0 {
            -1022
        } else {
            exp_bits - 1023
        };
        let mut nibbles = [0u8; 13];
        for (i, nibble) in nibbles.iter_mut().enumerate() {
            let shift = 52 - 4 * (i + 1);
            *nibble = ((frac_bits >> shift) & 0xF) as u8;
        }
        match f.precision() {
            None => {
                let mut len = 13;
                while len > 0 && nibbles[len - 1] == 0 {
                    len -= 1;
                }
                f.write_str("0x")?;
                write!(f, "{}", hex_digit_char(leading) as char)?;
                if len > 0 {
                    f.write_str(".")?;
                    write_hex_bytes(f, &nibbles[..len])?;
                }
                write!(f, "p{e2:+}")
            }
            Some(p) => {
                let keep = p.min(13);
                if keep < 13 {
                    round_hex_ties_to_even(&mut leading, &mut nibbles, keep);
                    if leading >= 2 {
                        leading = 1;
                        e2 += 1;
                    }
                }
                f.write_str("0x")?;
                write!(f, "{}", hex_digit_char(leading) as char)?;
                if p > 0 {
                    f.write_str(".")?;
                    write_hex_bytes(f, &nibbles[..keep])?;
                    for _ in 0..(p.saturating_sub(13)) {
                        f.write_str("0")?;
                    }
                } else if f.alternate() {
                    f.write_str(".")?;
                }
                write!(f, "p{e2:+}")
            }
        }
    }
}
#[inline]
fn hex_digit_char(d: u8) -> u8 {
    if d < 10 {
        b'0' + d
    } else {
        b'a' + (d - 10)
    }
}
#[inline]
fn write_hex_bytes(f: &mut std::fmt::Formatter<'_>, digits: &[u8]) -> std::fmt::Result {
    let mut buf = [0u8; 13];
    for (i, &d) in digits.iter().enumerate() {
        buf[i] = hex_digit_char(d);
    }
    let s = std::str::from_utf8(&buf[..digits.len()]).unwrap();
    f.write_str(s)
}
fn round_hex_ties_to_even(leading: &mut u8, digits: &mut [u8; 13], keep: usize) {
    if keep >= 13 {
        return;
    }
    let next = digits[keep];
    let rest_nonzero = digits[(keep + 1)..].iter().any(|&d| d != 0);
    let round_up = if next > 8 {
        true
    } else if next < 8 {
        false
    } else if rest_nonzero {
        true
    } else {
        let last = if keep == 0 {
            *leading
        } else {
            digits[keep - 1]
        };
        (last & 1) == 1
    };
    for d in &mut digits[keep..] {
        *d = 0;
    }
    if round_up {
        if keep == 0 {
            *leading = leading.saturating_add(1);
        } else {
            let mut i = keep - 1;
            loop {
                if digits[i] < 15 {
                    digits[i] += 1;
                    break;
                } else {
                    digits[i] = 0;
                    if i == 0 {
                        *leading = leading.saturating_add(1);
                        break;
                    }
                    i -= 1;
                }
            }
        }
    }
}
"#;
