use std::{fmt::Write as _, ops::Deref};

use rustc_ast::*;
use rustc_ast_pretty::pprust;
use rustc_middle::ty;
use rustc_span::sym;
use utils::expr;

use super::{
    likely_lit::LikelyLit,
    stream_ty::*,
    transform::LibItem,
    unwrap_cast_and_paren,
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
        // from rustc_ast/src/util/literal.rs
        let mut buf = Vec::with_capacity(fmt.len());
        rustc_literal_escaper::unescape_unicode(
            fmt,
            rustc_literal_escaper::Mode::ByteStr,
            &mut |_, c| buf.push(rustc_literal_escaper::byte_from_char(c.unwrap())),
        );
        let specs = parse_specs(&buf);
        let parsing_fn = make_parsing_function(&specs);
        let err_eof_args = self.err_eof_args(ic);
        let mut code = format!(
            "crate::stdio::{}({}, {}",
            parsing_fn.name, stream, err_eof_args
        );
        let mut i = 0;
        let mut decls = String::new();
        let mut assigns = String::new();
        for (spec, arg) in specs.iter().filter(|spec| spec.assign).zip(args) {
            match spec.ty() {
                ConvTy::Scalar(spec_ty) => {
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
                    if let Some((array, signed)) = self.byte_array_of_as_mut_ptr(arg) {
                        let arg = pprust::expr_to_string(array);
                        if signed {
                            write!(
                                assigns,
                                "({arg})[..___v_{i}.len()].copy_from_slice(&___v_{i}[..]);"
                            )
                            .unwrap();
                        } else {
                            self.bytemuck.set(true);
                            write!(
                                assigns,
                                "bytemuck::cast_slice_mut(&mut ({arg})[..___v_{i}.len()])
                                    .copy_from_slice(&___v_{i}[..]);"
                            )
                            .unwrap();
                        }
                        continue;
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
    let mut name = "parse".to_string();
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
            Conversion::Int10 | Conversion::Unsigned => {
                lib_items.push(LibItem::ParseDecimal);
                lib_items.push(LibItem::ParseInteger);
                "parse_decimal"
            }
            Conversion::Int0 => {
                lib_items.push(LibItem::ParseIntegerAuto);
                lib_items.push(LibItem::ParseIntState);
                "parse_integer_auto"
            }
            Conversion::Octal => {
                lib_items.push(LibItem::ParseOctal);
                lib_items.push(LibItem::ParseInteger);
                "parse_octal"
            }
            Conversion::Hexadecimal => {
                lib_items.push(LibItem::ParseHexadecimal);
                lib_items.push(LibItem::ParseIntState);
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
                    if let Some(s) = escape(*c) {
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

fn parse_specs(mut remaining: &[u8]) -> Vec<ConversionSpec> {
    let mut specs = vec![];
    loop {
        let res = parse_format(remaining);
        if let Some(rem) = res.remaining {
            remaining = rem;
            specs.push(res.conversion_spec.unwrap());
        } else {
            break specs;
        }
    }
}

struct ParseResult<'a> {
    #[allow(unused)]
    prefix: &'a [u8],
    conversion_spec: Option<ConversionSpec>,
    remaining: Option<&'a [u8]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Percent,
    Asterisk,
    Width,
    H,
    L,
    Conversion,
    Circumflex,
    ScanSet,
}

fn err(s: &[u8], i: Option<usize>) -> ! {
    panic!("{}", String::from_utf8_lossy(&s[i.unwrap()..]));
}

fn parse_format(s: &[u8]) -> ParseResult<'_> {
    let mut start_idx = None;
    let mut state = State::Percent;
    let mut assign = true;
    let mut width = None;
    let mut length = None;
    let mut conversion = None;
    for (i, c) in s.iter().enumerate() {
        if state == State::Percent {
            if *c == b'%' {
                start_idx = Some(i);
                state = State::Asterisk;
            }
        } else if matches!(state, State::Circumflex | State::ScanSet) {
            if *c == b'^' {
                if state == State::Circumflex {
                    let Some((Conversion::ScanSet(ScanSet { negative, .. }), _)) = &mut conversion
                    else {
                        unreachable!()
                    };
                    *negative = true;
                    state = State::ScanSet;
                } else {
                    err(s, start_idx);
                }
            } else if *c == b']' {
                if state == State::ScanSet {
                    let Some((_, old_i)) = &mut conversion else { unreachable!() };
                    *old_i = i;
                    break;
                } else {
                    err(s, start_idx);
                }
            } else {
                state = State::ScanSet;
                let Some((Conversion::ScanSet(ScanSet { chars, .. }), _)) = &mut conversion else {
                    unreachable!()
                };
                chars.push(*c);
            }
        } else if c.is_ascii_digit() {
            match state {
                State::Asterisk => {
                    width = Some((c - b'0') as usize);
                    state = State::Width;
                }
                State::Width => {
                    let Some(n) = width.as_mut() else { unreachable!() };
                    *n = *n * 10 + (c - b'0') as usize;
                }
                _ => err(s, start_idx),
            }
        } else if *c == b'*' {
            if state == State::Asterisk {
                assign = false;
                state = State::Width;
            } else {
                err(s, start_idx);
            }
        } else if let Some(len) = LengthMod::from_u8(*c) {
            match len {
                LengthMod::Short => match state {
                    State::Asterisk | State::Width => {
                        state = State::H;
                    }
                    State::H => {
                        length = Some(LengthMod::Char);
                        state = State::Conversion;
                    }
                    _ => err(s, start_idx),
                },
                LengthMod::Long => match state {
                    State::Asterisk | State::Width => {
                        state = State::L;
                    }
                    State::L => {
                        length = Some(LengthMod::LongLong);
                        state = State::Conversion;
                    }
                    _ => err(s, start_idx),
                },
                _ => {
                    length = Some(len);
                    state = State::Conversion;
                }
            }
        } else if let Some(conv) = Conversion::from_u8(*c) {
            match state {
                State::Asterisk | State::Width | State::Conversion => {}
                State::H => length = Some(LengthMod::Short),
                State::L => length = Some(LengthMod::Long),
                _ => err(s, start_idx),
            }
            let is_set = conv.is_set();
            conversion = Some((conv, i));
            if is_set {
                state = State::Circumflex;
            } else {
                break;
            }
        } else {
            err(s, start_idx);
        }
    }

    if let Some(start_idx) = start_idx {
        if let Some((conversion, last_idx)) = conversion {
            ParseResult {
                prefix: &s[..start_idx],
                conversion_spec: Some(ConversionSpec {
                    assign,
                    width,
                    length,
                    conversion,
                }),
                remaining: Some(&s[last_idx + 1..]),
            }
        } else {
            err(s, Some(start_idx))
        }
    } else {
        ParseResult {
            prefix: s,
            conversion_spec: None,
            remaining: None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LengthMod {
    Char,
    Short,
    Long,
    LongLong,
    IntMax,
    Size,
    PtrDiff,
    LongDouble,
}

impl std::fmt::Display for LengthMod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Char => write!(f, "hh"),
            Self::Short => write!(f, "h"),
            Self::Long => write!(f, "l"),
            Self::LongLong => write!(f, "ll"),
            Self::IntMax => write!(f, "j"),
            Self::Size => write!(f, "z"),
            Self::PtrDiff => write!(f, "t"),
            Self::LongDouble => write!(f, "L"),
        }
    }
}

impl LengthMod {
    #[inline]
    fn from_u8(c: u8) -> Option<Self> {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ScanSet {
    pub(super) negative: bool,
    pub(super) chars: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Conversion {
    Int10,
    Int0,
    Octal,
    Unsigned,
    Hexadecimal,
    Double,
    Str,
    ScanSet(ScanSet),
    Seq,
    Pointer,
    Num,
    C,
    S,
    Percent,
}

impl std::fmt::Display for Conversion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int10 => write!(f, "d"),
            Self::Int0 => write!(f, "i"),
            Self::Octal => write!(f, "o"),
            Self::Unsigned => write!(f, "u"),
            Self::Hexadecimal => write!(f, "x"),
            Self::Double => write!(f, "g"),
            Self::Str => write!(f, "s"),
            Self::ScanSet(ScanSet { negative, chars }) => {
                write!(f, "[")?;
                if *negative {
                    write!(f, "^")?;
                }
                for c in chars {
                    if let Some(s) = escape(*c) {
                        write!(f, "{s}")?;
                    } else {
                        write!(f, "{}", *c as char)?;
                    }
                }
                write!(f, "]")
            }
            Self::Seq => write!(f, "c"),
            Self::Pointer => write!(f, "p"),
            Self::Num => write!(f, "n"),
            Self::C => write!(f, "C"),
            Self::S => write!(f, "S"),
            Self::Percent => write!(f, "%"),
        }
    }
}

impl Conversion {
    #[inline]
    fn from_u8(c: u8) -> Option<Self> {
        match c {
            b'd' => Some(Self::Int10),
            b'i' => Some(Self::Int0),
            b'o' => Some(Self::Octal),
            b'u' => Some(Self::Unsigned),
            b'x' => Some(Self::Hexadecimal),
            b'a' | b'e' | b'f' | b'g' => Some(Self::Double),
            b's' => Some(Self::Str),
            b'[' => Some(Self::ScanSet(ScanSet {
                negative: false,
                chars: vec![],
            })),
            b'c' => Some(Self::Seq),
            b'p' => Some(Self::Pointer),
            b'n' => Some(Self::Num),
            b'C' => Some(Self::C),
            b'S' => Some(Self::S),
            b'%' => Some(Self::Percent),
            _ => None,
        }
    }

    #[inline]
    fn is_set(&self) -> bool {
        matches!(self, Self::ScanSet { .. })
    }

    fn ty(&self, length: Option<LengthMod>) -> ConvTy {
        use LengthMod::*;
        let ty = match self {
            Self::Int10 | Self::Int0 => match length {
                None => "i32",
                Some(Char) => "i8",
                Some(Short) => "i16",
                Some(Long | LongLong | IntMax | Size) => "i64",
                Some(PtrDiff) => "u64",
                Some(LongDouble) => panic!(),
            },
            Self::Octal | Self::Unsigned | Self::Hexadecimal => match length {
                None => "u32",
                Some(Char) => "u8",
                Some(Short) => "u16",
                Some(Long | LongLong | IntMax | Size | PtrDiff) => "u64",
                Some(LongDouble) => panic!(),
            },
            Self::Double => match length {
                None => "f32",
                Some(Long) => "f64",
                Some(LongDouble) => "f128::f128",
                _ => panic!(),
            },
            Self::Str | Self::ScanSet { .. } => return ConvTy::String,
            Self::Seq => match length {
                None => "i8",
                Some(Long) => unimplemented!(),
                _ => panic!(),
            },
            Self::Pointer | Self::C | Self::S | Self::Num | Self::Percent => {
                unimplemented!()
            }
        };
        ConvTy::Scalar(ty)
    }
}

#[derive(Debug, Clone, Copy)]
enum ConvTy {
    Scalar(&'static str),
    String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ConversionSpec {
    pub(super) assign: bool,
    pub(super) width: Option<usize>,
    length: Option<LengthMod>,
    conversion: Conversion,
}

impl std::fmt::Display for ConversionSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%")?;
        if !self.assign {
            write!(f, "*")?;
        }
        if let Some(width) = self.width {
            write!(f, "{width}")?;
        }
        if let Some(length) = self.length {
            write!(f, "{length}")?;
        }
        write!(f, "{}", self.conversion)
    }
}

impl ConversionSpec {
    fn ty(&self) -> ConvTy {
        self.conversion.ty(self.length)
    }
}

pub(super) fn escape(c: u8) -> Option<&'static str> {
    match c {
        b'\n' => Some("\\n"),
        b'\r' => Some("\\r"),
        b'\t' => Some("\\t"),
        b'\\' => Some("\\\\"),
        b'\'' => Some("\\'"),
        b'\"' => Some("\\\""),
        b'\0' => Some("\\0"),
        _ => None,
    }
}

#[cfg(test)]
fn test_helper(s: &str) -> ConversionSpec {
    let res = parse_format(s.as_bytes());
    let empty: &[u8] = &[];
    assert_eq!(res.prefix, empty, "{:?}", s);
    assert_eq!(res.remaining, Some(empty), "{:?}", s);
    res.conversion_spec.expect(s)
}

#[cfg(test)]
#[test]
fn test_scanf_parse() {
    assert_eq!(
        test_helper("%d"),
        ConversionSpec {
            assign: true,
            width: None,
            length: None,
            conversion: Conversion::Int10
        }
    );
    assert_eq!(
        test_helper("%ld"),
        ConversionSpec {
            assign: true,
            width: None,
            length: Some(LengthMod::Long),
            conversion: Conversion::Int10
        }
    );
    assert_eq!(
        test_helper("%hhd"),
        ConversionSpec {
            assign: true,
            width: None,
            length: Some(LengthMod::Char),
            conversion: Conversion::Int10
        }
    );
    assert_eq!(
        test_helper("%10s"),
        ConversionSpec {
            assign: true,
            width: Some(10),
            length: None,
            conversion: Conversion::Str
        }
    );
    assert_eq!(
        test_helper("%*s"),
        ConversionSpec {
            assign: false,
            width: None,
            length: None,
            conversion: Conversion::Str
        }
    );
    assert_eq!(
        test_helper("%[abcd]"),
        ConversionSpec {
            assign: true,
            width: None,
            length: None,
            conversion: Conversion::ScanSet(ScanSet {
                negative: false,
                chars: vec![b'a', b'b', b'c', b'd']
            })
        }
    );
    assert_eq!(
        test_helper("%[^\n]"),
        ConversionSpec {
            assign: true,
            width: None,
            length: None,
            conversion: Conversion::ScanSet(ScanSet {
                negative: true,
                chars: vec![b'\n']
            })
        }
    );
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
fn parse_f32<R: std::io::BufRead>(stream: R, width: Option<usize>, mut err: Option<&mut i32>, mut eof: Option<&mut i32>) -> Option<f32> {
    parse_float(
        stream,
        width,
        err,
        eof,
        FloatValues {
            infinity_value: f32::INFINITY,
            neg_infinity_value: f32::NEG_INFINITY,
            nan_value: f32::NAN,
        },
        str::parse,
    )
}
"#;

pub(super) static PARSE_F64: &str = r#"
fn parse_f64<R: std::io::BufRead>(stream: R, width: Option<usize>, mut err: Option<&mut i32>, mut eof: Option<&mut i32>) -> Option<f64> {
    parse_float(
        stream,
        width,
        err,
        eof,
        FloatValues {
            infinity_value: f64::INFINITY,
            neg_infinity_value: f64::NEG_INFINITY,
            nan_value: f64::NAN,
        },
        str::parse,
    )
}
"#;

pub(super) static PARSE_F128: &str = r#"
fn parse_f128<R: std::io::BufRead>(
    stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
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
        },
        |s| <f128::f128 as num_traits::Num>::from_str_radix(s, 10),
    )
}
"#;

pub(super) static PARSE_FLOAT: &str = r#"
struct FloatValues<F> {
    infinity_value: F,
    neg_infinity_value: F,
    nan_value: F,
}

#[inline]
fn parse_float<R: std::io::BufRead, F, E>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
    values: FloatValues<F>,
    parse: impl Fn(&str) -> Result<F, E>,
) -> Option<F> {
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
        return Some(v);
    } else if i > 0 {
        return None;
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
        return Some(values.nan_value);
    } else if i > 0 {
        return None;
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
    loop {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if c.is_ascii_digit() {
        } else if c == b'.' && !dot_seen {
            dot_seen = true;
        } else {
            break;
        }
        v.push(c);
        stream.consume(1);
    }

    if !v.iter().any(|c| c.is_ascii_digit()) {
        return None;
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
    parse(s).ok()
}
"#;

pub(super) static PARSE_DECIMAL: &str = r#"
fn parse_decimal<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> Option<u64> {
    parse_integer(&mut stream, width, err.as_deref_mut(), eof.as_deref_mut(), |c| c.is_ascii_digit(), 10)
}
"#;

pub(super) static PARSE_OCTAL: &str = r#"
fn parse_octal<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> Option<u64> {
    parse_integer(&mut stream, width, err.as_deref_mut(), eof.as_deref_mut(), |c| matches!(c, b'0'..=b'7'), 8)
}
"#;

pub(super) static PARSE_INTEGER: &str = r#"
#[inline]
fn parse_integer<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
    is_digit: impl Fn(u8) -> bool,
    base: u64,
) -> Option<u64> {
    let mut expect_digit = false;
    let mut neg = false;
    let mut succ = false;
    let mut v = 0u64;
    let mut count = 0;
    while width.is_none_or(|lim| count < lim) {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        if is_digit(c) {
            expect_digit = true;
            succ = true;
            v = v.wrapping_mul(base);
            v = v.wrapping_add((c - b'0') as u64);
            count += 1;
        } else if expect_digit {
            break;
        } else if c == b'-' {
            expect_digit = true;
            count += 1;
            neg = true;
        } else if c == b'+' {
            expect_digit = true;
            count += 1;
        } else if c.is_ascii_whitespace() {
        } else {
            break;
        }
        stream.consume(1);
    }
    if succ {
        if neg {
            Some(v.wrapping_neg())
        } else {
            Some(v)
        }
    } else {
        None
    }
}
"#;

pub(super) static PARSE_INT_STATE: &str = r#"
enum ParseIntState {
    Whitespace,
    Zero,
    X,
    Digit,
}
"#;

pub(super) static PARSE_HEXADECIMAL: &str = r#"
fn parse_hexadecimal<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> Option<u64> {
    let mut state = ParseIntState::Whitespace;
    let mut neg = false;
    let mut succ = false;
    let mut v = 0u64;
    let mut count = 0;
    while width.is_none_or(|lim| count < lim) {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        match state {
            ParseIntState::Whitespace => {
                if c == b'0' {
                    state = ParseIntState::X;
                    count += 1;
                    succ = true;
                } else if c.is_ascii_hexdigit() {
                    state = ParseIntState::Digit;
                    continue;
                } else if c == b'-' {
                    state = ParseIntState::Zero;
                    count += 1;
                    neg = true;
                } else if c == b'+' {
                    state = ParseIntState::Zero;
                    count += 1;
                } else if c.is_ascii_whitespace() {
                } else {
                    break;
                }
            }
            ParseIntState::Zero => {
                if c == b'0' {
                    state = ParseIntState::X;
                    count += 1;
                    succ = true;
                } else if c.is_ascii_hexdigit() {
                    state = ParseIntState::Digit;
                    continue;
                } else {
                    break;
                }
            }
            ParseIntState::X => {
                if c == b'x' || c == b'X' {
                    state = ParseIntState::Digit;
                    count += 1;
                } else if c.is_ascii_hexdigit() {
                    state = ParseIntState::Digit;
                    continue;
                } else {
                    break;
                }
            }
            ParseIntState::Digit => {
                if c.is_ascii_hexdigit() {
                    succ = true;
                    v = v.wrapping_mul(16);
                    if c.is_ascii_digit() {
                        v = v.wrapping_add((c - b'0') as u64);
                    } else if c.is_ascii_lowercase() {
                        v = v.wrapping_add((c - b'a' + 10) as u64);
                    } else {
                        v = v.wrapping_add((c - b'A' + 10) as u64);
                    }
                    count += 1;
                } else {
                    break;
                }
            }
        }
        stream.consume(1);
    }
    if succ {
        if neg {
            Some(v.wrapping_neg())
        } else {
            Some(v)
        }
    } else {
        None
    }
}
"#;

pub(super) static PARSE_INTEGER_AUTO: &str = r#"
fn parse_integer_auto<R: std::io::BufRead>(
    mut stream: R,
    width: Option<usize>,
    mut err: Option<&mut i32>,
    mut eof: Option<&mut i32>,
) -> Option<u64> {
    let mut state = ParseIntState::Whitespace;
    let mut neg = false;
    let mut base = 10;
    let mut succ = false;
    let mut v = 0u64;
    let mut count = 0;
    while width.is_none_or(|lim| count < lim) {
        let c = peek(&mut stream, err.as_deref_mut(), eof.as_deref_mut());
        match state {
            ParseIntState::Whitespace => {
                if c == b'0' {
                    state = ParseIntState::X;
                    count += 1;
                    base = 8;
                    succ = true;
                } else if c.is_ascii_digit() {
                    state = ParseIntState::Digit;
                    continue;
                } else if c == b'-' {
                    state = ParseIntState::Zero;
                    count += 1;
                    neg = true;
                } else if c == b'+' {
                    state = ParseIntState::Zero;
                    count += 1;
                } else if c.is_ascii_whitespace() {
                } else {
                    break;
                }
            }
            ParseIntState::Zero => {
                if c == b'0' {
                    state = ParseIntState::X;
                    count += 1;
                    base = 8;
                    succ = true;
                } else if c.is_ascii_digit() {
                    state = ParseIntState::Digit;
                    continue;
                } else {
                    break;
                }
            }
            ParseIntState::X => {
                if c == b'x' || c == b'X' {
                    state = ParseIntState::Digit;
                    count += 1;
                    base = 16;
                } else if matches!(c, b'0'..=b'7') {
                    state = ParseIntState::Digit;
                    continue;
                } else {
                    break;
                }
            }
            ParseIntState::Digit => {
                if base == 8 && matches!(c, b'0'..=b'7') || base == 10 && c.is_ascii_digit() {
                    succ = true;
                    v = v.wrapping_mul(base);
                    v = v.wrapping_add((c - b'0') as u64);
                    count += 1;
                } else if base == 16 && c.is_ascii_hexdigit() {
                    succ = true;
                    v = v.wrapping_mul(16);
                    if c.is_ascii_digit() {
                        v = v.wrapping_add((c - b'0') as u64);
                    } else if c.is_ascii_lowercase() {
                        v = v.wrapping_add((c - b'a' + 10) as u64);
                    } else {
                        v = v.wrapping_add((c - b'A' + 10) as u64);
                    }
                    count += 1;
                } else {
                    break;
                }
            }
        }
        stream.consume(1);
    }
    if succ {
        if neg {
            Some(v.wrapping_neg())
        } else {
            Some(v)
        }
    } else {
        None
    }
}
"#;
