use std::fmt::Write as _;

use rustc_ast::{
    Expr, ExprKind, LitKind, Stmt, StmtKind, Ty,
    ptr::P,
    token::{Delimiter, TokenKind},
    tokenstream::TokenStream,
};
use rustc_hir as hir;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{Span, def_id::DefId};

use crate::observation::{local_c_foreign_function_symbol, resolved_definition};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PrintfConversionKind {
    SignedDecimal,
    UnsignedDecimal,
    Octal,
    LowerHex,
    UpperHex,
    String,
    FixedFloat,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PrintfConversion {
    pub source_specifier: String,
    pub kind: PrintfConversionKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConvertedPrintfFormat {
    pub rust_format: String,
    pub conversions: Vec<PrintfConversion>,
}

pub(crate) struct EligiblePrintfCall<'a> {
    pub format: ConvertedPrintfFormat,
    pub arguments: &'a [P<Expr>],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ResolvedPrintfDescriptor {
    local_nonunwinding_c_abi_foreign_item: bool,
    linked_symbol_is_printf: bool,
    c_variadic: bool,
    fixed_parameter_count: usize,
    fixed_parameter_is_const_c_char: bool,
    returns_c_int: bool,
}

#[derive(Debug)]
pub(crate) struct ParsedPrintMacro {
    pub format: String,
    pub format_span: Span,
    pub arguments: Vec<P<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PrintMacroError {
    pub code: &'static str,
    pub message: String,
}

pub(crate) fn parse_print_macro_statement(
    statement: &Stmt,
) -> Result<ParsedPrintMacro, PrintMacroError> {
    let StmtKind::MacCall(mac) = &statement.kind else {
        return Err(print_error(
            "printf_macro_kind",
            "expected one outer macro invocation",
        ));
    };
    if rustc_ast_pretty::pprust::path_to_string(&mac.mac.path) != "::std::print" {
        return Err(print_error(
            "printf_macro_path",
            "expected the absolute macro path `::std::print`",
        ));
    }
    if mac.mac.args.delim != Delimiter::Parenthesis {
        return Err(print_error(
            "printf_macro_delimiter",
            "expected parenthesized print macro input",
        ));
    }
    let mut expressions = parse_macro_arguments(&mac.mac.args.tokens)?;
    if expressions.is_empty() {
        return Err(print_error(
            "printf_format_literal",
            "print macro has no format literal",
        ));
    }
    let format_expression = expressions.remove(0);
    let ExprKind::Lit(token_literal) = &format_expression.kind else {
        return Err(print_error(
            "printf_format_literal",
            "print format must be one ordinary Rust string literal",
        ));
    };
    let LitKind::Str(format, rustc_ast::StrStyle::Cooked) = LitKind::from_token_lit(*token_literal)
        .map_err(|_| {
            print_error(
                "printf_format_literal",
                "print format must be one ordinary Rust string literal",
            )
        })?
    else {
        return Err(print_error(
            "printf_format_literal",
            "print format must be one ordinary Rust string literal",
        ));
    };
    for expression in &expressions {
        if matches!(expression.kind, ExprKind::Assign(..)) {
            return Err(print_error(
                "printf_named_argument",
                "named print arguments are not allowed",
            ));
        }
    }
    Ok(ParsedPrintMacro {
        format: format.to_string(),
        format_span: format_expression.span,
        arguments: expressions,
    })
}

pub(crate) fn validate_print_macro_statement(
    statement: &Stmt,
    expected_format: &str,
    expected_arguments: usize,
) -> Result<(), PrintMacroError> {
    let parsed = parse_print_macro_statement(statement)?;
    let placeholder_count = implicit_placeholder_count(&parsed.format).ok_or_else(|| {
        print_error(
            "printf_format_references",
            "print format must contain only the expected implicit-order placeholders",
        )
    })?;
    if parsed.format != expected_format {
        return Err(print_error(
            "printf_format_literal",
            "print format literal differs from the expected converted format",
        ));
    }
    if placeholder_count != expected_arguments {
        return Err(print_error(
            "printf_format_references",
            "print format must contain only the expected implicit-order placeholders",
        ));
    }
    if parsed.arguments.len() != expected_arguments {
        return Err(print_error(
            "printf_argument_count",
            "print value argument count differs from the converted format",
        ));
    }
    Ok(())
}

pub(crate) fn validate_print_template_statement(
    statement: &Stmt,
    expected_format: &str,
    expected_arguments: usize,
) -> Result<(), PrintMacroError> {
    validate_print_macro_statement(statement, expected_format, expected_arguments)?;
    let parsed = parse_print_macro_statement(statement)?;
    if parsed.arguments.iter().any(|argument| {
        if !argument.attrs.is_empty() {
            return true;
        }
        let ExprKind::MacCall(mac) = &argument.kind else {
            return true;
        };
        rustc_ast_pretty::pprust::path_to_string(&mac.path) != "todo"
            || mac.args.delim != Delimiter::Parenthesis
            || !mac.args.tokens.is_empty()
    }) {
        return Err(print_error(
            "printf_template_argument",
            "print template value arguments must be exact `todo!()` placeholders",
        ));
    }
    Ok(())
}

fn parse_macro_arguments(tokens: &TokenStream) -> Result<Vec<P<Expr>>, PrintMacroError> {
    let psess = utils::ast::new_parse_sess();
    let mut parser =
        rustc_parse::parser::Parser::new(&psess, tokens.clone(), Some("print macro arguments"));
    let mut expressions = vec![];
    while !matches!(parser.token.kind, TokenKind::Eof) {
        expressions.push(parser.parse_expr().map_err(|_| {
            print_error(
                "printf_argument_count",
                "print value argument is not one complete Rust expression",
            )
        })?);
        if matches!(parser.token.kind, TokenKind::Eof) {
            break;
        }
        if parser.token.kind != TokenKind::Comma {
            return Err(print_error(
                "printf_argument_count",
                "print value argument has trailing tokens",
            ));
        }
        parser.bump();
    }
    Ok(expressions)
}

fn implicit_placeholder_count(format: &str) -> Option<usize> {
    let bytes = format.as_bytes();
    let mut cursor = 0;
    let mut count = 0;
    while cursor < bytes.len() {
        match bytes[cursor] {
            b'{' if bytes.get(cursor + 1) == Some(&b'{') => cursor += 2,
            b'}' if bytes.get(cursor + 1) == Some(&b'}') => cursor += 2,
            b'{' => {
                let end = bytes[cursor + 1..].iter().position(|byte| *byte == b'}')? + cursor + 1;
                let field = &format[cursor + 1..end];
                if !field.is_empty() && !field.starts_with(':') {
                    return None;
                }
                count += 1;
                cursor = end + 1;
            }
            b'}' => return None,
            _ => {
                let character = format[cursor..].chars().next()?;
                cursor += character.len_utf8();
            }
        }
    }
    Some(count)
}

fn print_error(code: &'static str, message: impl Into<String>) -> PrintMacroError {
    PrintMacroError {
        code,
        message: message.into(),
    }
}

pub(crate) fn supported_printf_definition(definition: DefId, tcx: TyCtxt<'_>) -> bool {
    let Some(symbol) = local_c_foreign_function_symbol(definition, tcx) else {
        return false;
    };
    let signature = tcx.fn_sig(definition).instantiate_identity().skip_binder();
    supported_printf_descriptor(ResolvedPrintfDescriptor {
        local_nonunwinding_c_abi_foreign_item: true,
        linked_symbol_is_printf: symbol.as_str() == "printf",
        c_variadic: signature.c_variadic,
        fixed_parameter_count: signature.inputs().len(),
        fixed_parameter_is_const_c_char: signature.inputs().first().is_some_and(|input| {
            matches!(
                input.kind(),
                ty::TyKind::RawPtr(pointee, mutability)
                    if !mutability.is_mut() && is_c_char(*pointee)
            )
        }),
        returns_c_int: is_c_int(signature.output(), tcx),
    })
}

fn supported_printf_descriptor(descriptor: ResolvedPrintfDescriptor) -> bool {
    descriptor.local_nonunwinding_c_abi_foreign_item
        && descriptor.linked_symbol_is_printf
        && descriptor.c_variadic
        && descriptor.fixed_parameter_count == 1
        && descriptor.fixed_parameter_is_const_c_char
        && descriptor.returns_c_int
}

pub(crate) fn supported_printf_call(
    expression: &Expr,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> bool {
    let expression = peel_parens(expression);
    let ExprKind::Call(callee, _) = &expression.kind else { return false };
    resolved_definition(callee, ast_to_hir, tcx)
        .is_some_and(|definition| supported_printf_definition(definition, tcx))
}

pub(crate) fn eligible_printf_statement<'a>(
    statement: &'a Stmt,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<EligiblePrintfCall<'a>> {
    let StmtKind::Semi(expression) = &statement.kind else { return None };
    let expression = peel_parens(expression);
    let ExprKind::Call(callee, arguments) = &expression.kind else { return None };
    let definition = resolved_definition(callee, ast_to_hir, tcx)?;
    if !supported_printf_definition(definition, tcx) {
        return None;
    }
    let (format_argument, values) = arguments.split_first()?;
    let bytes = literal_cast_chain(format_argument, ast_to_hir, tcx)?;
    let (&0, body) = bytes.split_last()? else { return None };
    if body.contains(&0) {
        return None;
    }
    let format = convert_printf_format(body)?;
    (format.conversions.len() == values.len()).then_some(EligiblePrintfCall {
        format,
        arguments: values,
    })
}

fn peel_parens(mut expression: &Expr) -> &Expr {
    while let ExprKind::Paren(inner) = &expression.kind {
        expression = inner;
    }
    expression
}

fn literal_cast_chain(
    expression: &Expr,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<Vec<u8>> {
    let mut expression = peel_parens(expression);
    let mut targets = vec![];
    while let ExprKind::Cast(inner, target) = &expression.kind {
        targets.push(ast_type(target, ast_to_hir, tcx)?);
        expression = peel_parens(inner);
    }
    if targets.is_empty() {
        return None;
    }
    targets.reverse();
    if !targets
        .iter()
        .all(|target| is_const_char_or_u8_pointer(*target))
        || !is_const_char_or_u8_pointer(targets[0])
        || !is_const_c_char_pointer(*targets.last()?)
    {
        return None;
    }
    let hir_expression = ast_to_hir.get_expr(expression.id, tcx)?;
    let hir::ExprKind::Lit(literal) = hir_expression.kind else { return None };
    let LitKind::ByteStr(bytes, _) = &literal.node else { return None };
    Some(bytes.to_vec())
}

fn ast_type<'tcx>(
    ty: &Ty,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
) -> Option<ty::Ty<'tcx>> {
    let hir_ty = ast_to_hir.get_ty(ty.id, tcx)?;
    Some(tcx.typeck(hir_ty.hir_id.owner).node_type(hir_ty.hir_id))
}

fn is_const_char_or_u8_pointer(ty: ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::RawPtr(pointee, mutability)
            if !mutability.is_mut()
                && (is_c_char(*pointee) || matches!(pointee.kind(), ty::TyKind::Uint(ty::UintTy::U8)))
    )
}

fn is_const_c_char_pointer(ty: ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::RawPtr(pointee, mutability)
            if !mutability.is_mut() && is_c_char(*pointee)
    )
}

fn is_c_char(ty: ty::Ty<'_>) -> bool {
    // The pinned tools target is x86_64-unknown-linux-gnu, where the normalized
    // target C `char` type is `i8`.
    matches!(ty.kind(), ty::TyKind::Int(ty::IntTy::I8))
}

fn is_c_int(ty: ty::Ty<'_>, tcx: TyCtxt<'_>) -> bool {
    matches!(
        (tcx.sess.target.c_int_width, ty.kind()),
        (16, ty::TyKind::Int(ty::IntTy::I16))
            | (32, ty::TyKind::Int(ty::IntTy::I32))
            | (64, ty::TyKind::Int(ty::IntTy::I64))
    )
}

#[derive(Debug, Clone, Copy, Default)]
struct Flags {
    left: bool,
    plus: bool,
    zero: bool,
    alternate: bool,
}

pub(crate) fn convert_printf_format(bytes: &[u8]) -> Option<ConvertedPrintfFormat> {
    let text = std::str::from_utf8(bytes).ok()?;
    let bytes = text.as_bytes();
    let mut rust_format = String::new();
    let mut conversions = vec![];
    let mut cursor = 0;
    while cursor < bytes.len() {
        match bytes[cursor] {
            b'{' => {
                rust_format.push_str("{{");
                cursor += 1;
            }
            b'}' => {
                rust_format.push_str("}}");
                cursor += 1;
            }
            b'%' if bytes.get(cursor + 1) == Some(&b'%') => {
                rust_format.push('%');
                cursor += 2;
            }
            b'%' => {
                let start = cursor;
                cursor += 1;
                let mut flags = Flags::default();
                while let Some(flag) = bytes.get(cursor).copied() {
                    match flag {
                        b'-' => flags.left = true,
                        b'+' => flags.plus = true,
                        b'0' => flags.zero = true,
                        b'#' => flags.alternate = true,
                        b' ' | b'\'' => return None,
                        _ => break,
                    }
                    cursor += 1;
                }
                if bytes.get(cursor) == Some(&b'*') {
                    return None;
                }
                let (width, next) = parse_number(bytes, cursor)?;
                cursor = next;
                if bytes.get(cursor) == Some(&b'$') {
                    return None;
                }
                let precision = if bytes.get(cursor) == Some(&b'.') {
                    cursor += 1;
                    if bytes.get(cursor) == Some(&b'*') {
                        return None;
                    }
                    let (value, next) = parse_required_number(bytes, cursor)?;
                    cursor = next;
                    if bytes.get(cursor) == Some(&b'$') {
                        return None;
                    }
                    Some(value)
                } else {
                    None
                };
                let length_start = cursor;
                let length = if bytes.get(cursor..cursor + 2) == Some(b"hh")
                    || bytes.get(cursor..cursor + 2) == Some(b"ll")
                {
                    cursor += 2;
                    &text[length_start..cursor]
                } else if matches!(
                    bytes.get(cursor),
                    Some(b'h' | b'l' | b'j' | b'z' | b't' | b'L')
                ) {
                    cursor += 1;
                    &text[length_start..cursor]
                } else {
                    ""
                };
                let conversion = *bytes.get(cursor)?;
                cursor += 1;
                let source_specifier = text[start..cursor].to_owned();
                let mut field = String::from("{");
                let kind = match conversion {
                    b'd' | b'i' => {
                        if flags.alternate || precision.is_some() || !integer_length(length) {
                            return None;
                        }
                        write_format_prefix(&mut field, flags, width, true);
                        PrintfConversionKind::SignedDecimal
                    }
                    b'u' | b'o' | b'x' | b'X' => {
                        if flags.plus
                            || flags.alternate
                            || precision.is_some()
                            || !integer_length(length)
                        {
                            return None;
                        }
                        write_format_prefix(&mut field, flags, width, false);
                        match conversion {
                            b'u' => PrintfConversionKind::UnsignedDecimal,
                            b'o' => {
                                ensure_format_options(&mut field);
                                field.push('o');
                                PrintfConversionKind::Octal
                            }
                            b'x' => {
                                ensure_format_options(&mut field);
                                field.push('x');
                                PrintfConversionKind::LowerHex
                            }
                            b'X' => {
                                ensure_format_options(&mut field);
                                field.push('X');
                                PrintfConversionKind::UpperHex
                            }
                            _ => unreachable!(),
                        }
                    }
                    b's' => {
                        if flags.left
                            || flags.plus
                            || flags.zero
                            || flags.alternate
                            || width.is_some()
                            || precision.is_some()
                            || !length.is_empty()
                        {
                            return None;
                        }
                        PrintfConversionKind::String
                    }
                    b'f' | b'F' => {
                        if !matches!(length, "" | "l") {
                            return None;
                        }
                        let precision = precision.unwrap_or(6);
                        if flags.alternate && precision == 0 {
                            return None;
                        }
                        write_format_prefix(&mut field, flags, width, true);
                        ensure_format_options(&mut field);
                        write!(field, ".{precision}").ok()?;
                        PrintfConversionKind::FixedFloat
                    }
                    // These are parsed deliberately, but standard Rust formatting does not
                    // provide the exact C spelling required by the supported domain.
                    b'e' | b'E' | b'g' | b'G' | b'a' | b'A' | b'c' | b'p' | b'n' | b'%' => {
                        return None;
                    }
                    _ => return None,
                };
                field.push('}');
                rust_format.push_str(&field);
                conversions.push(PrintfConversion {
                    source_specifier,
                    kind,
                });
            }
            _ => {
                let ch = text[cursor..].chars().next()?;
                rust_format.push(ch);
                cursor += ch.len_utf8();
            }
        }
    }
    Some(ConvertedPrintfFormat {
        rust_format,
        conversions,
    })
}

fn integer_length(length: &str) -> bool {
    matches!(length, "" | "hh" | "h" | "l" | "ll" | "j" | "z" | "t")
}

fn parse_number(bytes: &[u8], start: usize) -> Option<(Option<u32>, usize)> {
    if !bytes.get(start).is_some_and(u8::is_ascii_digit) {
        return Some((None, start));
    }
    parse_required_number(bytes, start).map(|(value, end)| (Some(value), end))
}

fn parse_required_number(bytes: &[u8], start: usize) -> Option<(u32, usize)> {
    let mut cursor = start;
    let mut value = 0_u32;
    let mut any = false;
    while let Some(digit) = bytes.get(cursor).copied().filter(u8::is_ascii_digit) {
        any = true;
        value = value
            .checked_mul(10)?
            .checked_add(u32::from(digit - b'0'))?;
        if value > i32::MAX as u32 {
            return None;
        }
        cursor += 1;
    }
    any.then_some((value, cursor))
}

fn write_format_prefix(output: &mut String, flags: Flags, width: Option<u32>, signed: bool) {
    let left = flags.left && width.is_some();
    let zero = flags.zero && !flags.left && width.is_some();
    let plus = flags.plus && signed;
    if left || zero || plus || width.is_some() {
        output.push(':');
        if left {
            output.push('<');
        }
        if plus {
            output.push('+');
        }
        if zero {
            output.push('0');
        }
        if let Some(width) = width {
            write!(output, "{width}").expect("writing to a string cannot fail");
        }
    }
}

fn ensure_format_options(output: &mut String) {
    if output == "{" {
        output.push(':');
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn converted(input: &str) -> Option<(String, Vec<String>)> {
        convert_printf_format(input.as_bytes()).map(|value| {
            (
                value.rust_format,
                value
                    .conversions
                    .into_iter()
                    .map(|conversion| conversion.source_specifier)
                    .collect(),
            )
        })
    }

    #[test]
    fn resolved_printf_descriptor_requires_every_exact_dimension() {
        let accepted = ResolvedPrintfDescriptor {
            local_nonunwinding_c_abi_foreign_item: true,
            linked_symbol_is_printf: true,
            c_variadic: true,
            fixed_parameter_count: 1,
            fixed_parameter_is_const_c_char: true,
            returns_c_int: true,
        };
        assert!(supported_printf_descriptor(accepted));

        let rejected = [
            ResolvedPrintfDescriptor {
                local_nonunwinding_c_abi_foreign_item: false,
                ..accepted
            },
            ResolvedPrintfDescriptor {
                linked_symbol_is_printf: false,
                ..accepted
            },
            ResolvedPrintfDescriptor {
                c_variadic: false,
                ..accepted
            },
            ResolvedPrintfDescriptor {
                fixed_parameter_count: 0,
                ..accepted
            },
            ResolvedPrintfDescriptor {
                fixed_parameter_count: 2,
                ..accepted
            },
            ResolvedPrintfDescriptor {
                fixed_parameter_is_const_c_char: false,
                ..accepted
            },
            ResolvedPrintfDescriptor {
                returns_c_int: false,
                ..accepted
            },
        ];
        for descriptor in rejected {
            assert!(!supported_printf_descriptor(descriptor), "{descriptor:?}");
        }
    }

    #[test]
    fn supported_formats_are_converted_exactly() {
        let cases = [
            ("plain text\n", "plain text\n", vec![]),
            ("100%% done", "100% done", vec![]),
            ("{x} %%", "{{x}} %", vec![]),
            ("%d", "{}", vec!["%d"]),
            ("%i %u", "{} {}", vec!["%i", "%u"]),
            ("%o %x %X", "{:o} {:x} {:X}", vec!["%o", "%x", "%X"]),
            ("%08x", "{:08x}", vec!["%08x"]),
            ("%+8d", "{:+8}", vec!["%+8d"]),
            ("%-8d", "{:<8}", vec!["%-8d"]),
            ("%-08d", "{:<8}", vec!["%-08d"]),
            ("%s", "{}", vec!["%s"]),
            ("%f %lf", "{:.6} {:.6}", vec!["%f", "%lf"]),
            ("%.0f %.3f", "{:.0} {:.3}", vec!["%.0f", "%.3f"]),
            ("%+010.2f", "{:+010.2}", vec!["%+010.2f"]),
            ("%-+010.2f", "{:<+10.2}", vec!["%-+010.2f"]),
            ("%#f %#.2f", "{:.6} {:.2}", vec!["%#f", "%#.2f"]),
            (
                "%--++0008d %0d %-d",
                "{:<+8} {} {}",
                vec!["%--++0008d", "%0d", "%-d"],
            ),
        ];
        for (input, output, specs) in cases {
            assert_eq!(
                converted(input),
                Some((
                    output.to_owned(),
                    specs.into_iter().map(str::to_owned).collect()
                )),
                "{input}"
            );
        }
    }

    #[test]
    fn unsupported_formats_fail_atomically() {
        for input in [
            "%",
            "abc%",
            "%q",
            "%2$d",
            "%*d",
            "%2$*3$d",
            "%.*f",
            "%2$.*3$f",
            "% d",
            "% f",
            "%'d",
            "%'f",
            "%#o",
            "%#x",
            "%#X",
            "%+u",
            "%+o",
            "%+x",
            "%+X",
            "%.0d",
            "%.3u",
            "%08.3x",
            "%-s",
            "%10s",
            "%.3s",
            "%ls",
            "%c",
            "%lc",
            "%p",
            "%n",
            "%e",
            "%E",
            "%g",
            "%G",
            "%a",
            "%A",
            "%#.0f",
            "%hf",
            "%llf",
            "%jf",
            "%zf",
            "%tf",
            "%Lf",
            "%LF",
            "%#.0F",
            "%5%",
            "%-%%",
            "%d %*d %d",
        ] {
            assert_eq!(converted(input), None, "{input}");
        }
    }

    #[test]
    fn numeric_limits_are_checked_without_panics() {
        assert!(converted("%2147483647d").is_some());
        assert!(converted("%.2147483647f").is_some());
        assert_eq!(converted("%2147483648d"), None);
        assert_eq!(converted("%.2147483648f"), None);
        assert_eq!(
            convert_printf_format(&vec![b'9'; 10_000]),
            Some(ConvertedPrintfFormat {
                rust_format: "9".repeat(10_000),
                conversions: vec![],
            })
        );
        let mut width = vec![b'%'];
        width.extend(std::iter::repeat_n(b'9', 10_000));
        width.push(b'd');
        assert_eq!(convert_printf_format(&width), None);
        let mut precision = b"%.".to_vec();
        precision.extend(std::iter::repeat_n(b'9', 10_000));
        precision.push(b'f');
        assert_eq!(convert_printf_format(&precision), None);
        assert_eq!(
            converted("%0000000000000000000000000000000017d"),
            Some((
                "{:017}".to_owned(),
                vec!["%0000000000000000000000000000000017d".to_owned()]
            ))
        );
    }

    #[test]
    fn arbitrary_short_bytes_never_panic() {
        for first in 0..=u8::MAX {
            assert!(std::panic::catch_unwind(|| convert_printf_format(&[first])).is_ok());
            for second in 0..=u8::MAX {
                assert!(
                    std::panic::catch_unwind(|| convert_printf_format(&[first, second])).is_ok()
                );
            }
        }
        for byte in 0..=u8::MAX {
            for input in [[byte, b'%'], [b'%', byte]] {
                assert!(std::panic::catch_unwind(|| convert_printf_format(&input)).is_ok());
            }
        }
        for corpus in [
            vec![b'%'; 10_000],
            vec![b'9'; 10_000],
            vec![b'{'; 10_000],
            vec![0; 10_000],
            (0..=u8::MAX).cycle().take(10_000).collect(),
        ] {
            assert!(std::panic::catch_unwind(|| convert_printf_format(&corpus)).is_ok());
        }
    }

    fn flag_spellings(flags: &[char]) -> Vec<String> {
        fn permutations(prefix: String, remaining: Vec<char>, output: &mut Vec<String>) {
            if remaining.is_empty() {
                output.push(prefix);
                return;
            }
            for index in 0..remaining.len() {
                let mut next = remaining.clone();
                let flag = next.remove(index);
                permutations(format!("{prefix}{flag}"), next, output);
            }
        }
        let mut output = vec![String::new()];
        for mask in 1..(1_usize << flags.len()) {
            let selected = flags
                .iter()
                .enumerate()
                .filter_map(|(index, flag)| ((mask >> index) & 1 == 1).then_some(*flag))
                .collect::<Vec<_>>();
            let mut unique = vec![];
            permutations(String::new(), selected.clone(), &mut unique);
            for spelling in unique {
                output.push(spelling.clone());
                let repeated = selected.iter().fold(spelling, |mut value, flag| {
                    value.push(*flag);
                    value
                });
                output.push(repeated);
            }
        }
        output.sort();
        output.dedup();
        output
    }

    fn expected_field(
        flags: &str,
        width: &str,
        precision: Option<&str>,
        suffix: &str,
        signed: bool,
    ) -> String {
        let has_width = !width.is_empty();
        let left = flags.contains('-') && has_width;
        let plus = flags.contains('+') && signed;
        let zero = flags.contains('0') && !flags.contains('-') && has_width;
        let mut options = String::new();
        if left {
            options.push('<');
        }
        if plus {
            options.push('+');
        }
        if zero {
            options.push('0');
        }
        options.push_str(width);
        if let Some(precision) = precision {
            options.push('.');
            options.push_str(precision);
        }
        options.push_str(suffix);
        if options.is_empty() {
            "{}".to_owned()
        } else {
            format!("{{:{options}}}")
        }
    }

    #[test]
    fn accepted_cartesian_formats_are_complete() {
        let lengths = ["", "hh", "h", "l", "ll", "j", "z", "t"];
        let widths = ["", "1", "17", "2147483647"];
        for conversion in ['d', 'i'] {
            for length in lengths {
                for flags in flag_spellings(&['-', '+', '0']) {
                    for width in widths {
                        let specifier = format!("%{flags}{width}{length}{conversion}");
                        assert_eq!(
                            converted(&specifier),
                            Some((
                                expected_field(&flags, width, None, "", true),
                                vec![specifier.clone()]
                            )),
                            "{specifier}"
                        );
                    }
                }
            }
        }
        for conversion in ['u', 'o', 'x', 'X'] {
            let suffix = match conversion {
                'o' => "o",
                'x' => "x",
                'X' => "X",
                _ => "",
            };
            for length in lengths {
                for flags in flag_spellings(&['-', '0']) {
                    for width in widths {
                        let specifier = format!("%{flags}{width}{length}{conversion}");
                        assert_eq!(
                            converted(&specifier),
                            Some((
                                expected_field(&flags, width, None, suffix, false),
                                vec![specifier.clone()]
                            )),
                            "{specifier}"
                        );
                    }
                }
            }
        }
        for conversion in ['f', 'F'] {
            for length in ["", "l"] {
                for flags in flag_spellings(&['-', '+', '0', '#']) {
                    for width in widths {
                        for precision in
                            [None, Some("0"), Some("1"), Some("17"), Some("2147483647")]
                        {
                            if flags.contains('#') && precision == Some("0") {
                                continue;
                            }
                            let precision_text =
                                precision.map_or(String::new(), |value| format!(".{value}"));
                            let specifier =
                                format!("%{flags}{width}{precision_text}{length}{conversion}");
                            assert_eq!(
                                converted(&specifier),
                                Some((
                                    expected_field(
                                        &flags,
                                        width,
                                        Some(precision.unwrap_or("6")),
                                        "",
                                        true
                                    ),
                                    vec![specifier.clone()]
                                )),
                                "{specifier}"
                            );
                        }
                    }
                }
            }
        }
        assert_eq!(
            converted("%s"),
            Some(("{}".to_owned(), vec!["%s".to_owned()]))
        );
    }

    #[test]
    fn rejected_conversion_mutations_fail_the_complete_format() {
        for conversion in ['d', 'i', 'u', 'o', 'x', 'X', 'f', 'F'] {
            for forbidden in [' ', '\''] {
                let mutated = format!("%{forbidden}{conversion}");
                assert_eq!(converted(&mutated), None, "{mutated}");
                assert_eq!(converted(&format!("%d {mutated} %u")), None, "{mutated}");
            }
            for unsupported in ['c', 'p', 'n', 'e', 'E', 'g', 'G', 'a', 'A', 'q'] {
                let mutated = format!("%{unsupported}");
                assert_eq!(converted(&mutated), None, "{mutated}");
                assert_eq!(converted(&format!("%d {mutated} %u")), None, "{mutated}");
            }
            for dynamic in [
                format!("%*{conversion}"),
                format!("%2${conversion}"),
                format!("%2$*3${conversion}"),
            ] {
                assert_eq!(converted(&dynamic), None, "{dynamic}");
            }
        }
        for conversion in ['d', 'i', 'u', 'o', 'x', 'X'] {
            for precision in ["0", "1", "2147483647"] {
                let mutated = format!("%.{precision}{conversion}");
                assert_eq!(converted(&mutated), None, "{mutated}");
            }
            for incompatible in ["L", "H"] {
                let mutated = format!("%{incompatible}{conversion}");
                assert_eq!(converted(&mutated), None, "{mutated}");
            }
        }
        for conversion in ['u', 'o', 'x', 'X'] {
            assert_eq!(converted(&format!("%+{conversion}")), None);
        }
        for conversion in ['d', 'i', 'u', 'o', 'x', 'X'] {
            assert_eq!(converted(&format!("%#{conversion}")), None);
        }
        for conversion in ['f', 'F'] {
            for length in ["hh", "h", "ll", "j", "z", "t", "L"] {
                assert_eq!(converted(&format!("%{length}{conversion}")), None);
            }
            assert_eq!(converted(&format!("%#.0{conversion}")), None);
            for dynamic in [format!("%.*{conversion}"), format!("%2$.*3${conversion}")] {
                assert_eq!(converted(&dynamic), None);
            }
        }
        for mutation in ["%-s", "%+s", "%0s", "%#s", "%1s", "%.1s", "%hs", "%ls"] {
            assert_eq!(converted(mutation), None, "{mutation}");
        }
    }

    #[test]
    fn expression_parser_handles_nested_commas_and_trailing_comma() {
        rustc_span::create_session_if_not_set_then(
            rustc_span::edition::Edition::Edition2021,
            |_| {
                let statement = utils::ast::parse_stmt(
                    r#"::std::print!("{} {} {}", value::<A, B>(), (a, b), { call(a, b) },);"#
                        .to_owned(),
                );
                let parsed = parse_print_macro_statement(&statement).unwrap();
                assert_eq!(parsed.arguments.len(), 3);
                assert_eq!(parsed.format, "{} {} {}");
            },
        );
    }
}
