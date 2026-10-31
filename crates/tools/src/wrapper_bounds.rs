use rustc_ast::{self as ast, ptr::P};
use rustc_span::{Symbol, edition::Edition, kw};
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WrapperBoundsRequest {
    pub source: String,
    pub wrapper: Option<String>,
    pub expressions: Option<Vec<String>>,
}

#[derive(Debug, Serialize)]
pub struct WrapperBoundsResponse {
    pub wrappers: Vec<WrapperBounds>,
    pub candidate: Option<String>,
}

#[derive(Debug, Serialize)]
pub struct WrapperBounds {
    pub path: String,
    pub wrapper: String,
    pub internal: String,
    pub sites: Vec<WrapperBoundSite>,
}

#[derive(Debug, Serialize)]
pub struct WrapperBoundSite {
    pub start: usize,
    pub end: usize,
    pub text: String,
}

struct SourceOffsets {
    bom: usize,
    carriage_returns: Vec<usize>,
}

impl SourceOffsets {
    fn new(source: &str) -> Self {
        // rustc assigns spans after removing the BOM and CR from CRLF pairs.
        let bom = if source.starts_with('\u{feff}') { 3 } else { 0 };
        let mut carriage_returns = vec![];
        for (offset, pair) in source.as_bytes()[bom..].windows(2).enumerate() {
            if pair == b"\r\n" {
                carriage_returns.push(offset - carriage_returns.len());
            }
        }
        Self {
            bom,
            carriage_returns,
        }
    }

    fn original(&self, normalized: usize) -> usize {
        normalized
            + self.bom
            + self
                .carriage_returns
                .partition_point(|offset| *offset < normalized)
    }
}

pub fn process_wrapper_bounds(
    request: &WrapperBoundsRequest,
) -> Result<WrapperBoundsResponse, String> {
    rustc_span::create_session_if_not_set_then(Edition::Edition2021, |_| {
        let krate = utils::ast::try_parse_crate(request.source.clone())?;
        let mut wrappers = vec![];
        let offsets = SourceOffsets::new(&request.source);
        collect_wrappers(
            &krate.items,
            &mut vec![],
            &request.source,
            &offsets,
            &mut wrappers,
        )?;
        let candidate = match (&request.wrapper, &request.expressions) {
            (None, None) => None,
            (Some(path), Some(expressions)) => {
                let wrapper = wrappers
                    .iter()
                    .find(|wrapper| wrapper.path == *path)
                    .ok_or_else(|| format!("no eligible wrapper `{path}`"))?;
                if expressions.len() != wrapper.sites.len() {
                    return Err("replacement count differs from wrapper bound count".to_owned());
                }
                let mut candidate = request.source.clone();
                for (site, expression) in wrapper.sites.iter().zip(expressions).rev() {
                    if expression.trim().is_empty() {
                        return Err("bound replacement must not be empty".to_owned());
                    }
                    validate_expression(expression)?;
                    if expression != &site.text {
                        candidate.replace_range(site.start..site.end, &format!("({expression}\n)"));
                    }
                }
                Some(candidate)
            }
            _ => return Err("wrapper and expressions must be provided together".to_owned()),
        };
        Ok(WrapperBoundsResponse {
            wrappers,
            candidate,
        })
    })
}

fn validate_expression(expression: &str) -> Result<(), String> {
    let parsed =
        utils::ast::try_parse_crate(format!("fn __bound() {{ let _ = ({expression}\n); }}"))?;
    let [item] = parsed.items.as_slice() else {
        return Err("bound replacement must be one Rust expression".to_owned());
    };
    let ast::ItemKind::Fn(function) = &item.kind else {
        return Err("bound replacement must be one Rust expression".to_owned());
    };
    let Some(body) = &function.body else {
        return Err("bound replacement must be one Rust expression".to_owned());
    };
    let [statement] = body.stmts.as_slice() else {
        return Err("bound replacement must be one Rust expression".to_owned());
    };
    let ast::StmtKind::Let(local) = &statement.kind else {
        return Err("bound replacement must be one Rust expression".to_owned());
    };
    if !matches!(&local.kind, ast::LocalKind::Init(value) if matches!(value.kind, ast::ExprKind::Paren(_)))
    {
        return Err("bound replacement must be one Rust expression".to_owned());
    }
    Ok(())
}

fn collect_wrappers(
    items: &[P<ast::Item>],
    module: &mut Vec<String>,
    source: &str,
    offsets: &SourceOffsets,
    result: &mut Vec<WrapperBounds>,
) -> Result<(), String> {
    for item in items {
        if let ast::ItemKind::Mod(_, name, ast::ModKind::Loaded(children, ..)) = &item.kind {
            module.push(name.to_string());
            collect_wrappers(children, module, source, offsets, result)?;
            module.pop();
            continue;
        }
        let ast::ItemKind::Fn(wrapper) = &item.kind else { continue };
        let Some(body) = wrapper.body.as_deref() else { continue };
        let Some(call) = block_expression(body) else { continue };
        let ast::ExprKind::Call(callee, args) = &call.kind else { continue };
        let ast::ExprKind::Path(None, path) = &callee.kind else { continue };
        let [segment] = path.segments.as_slice() else { continue };
        let Some((internal_item, internal)) = items.iter().find_map(|item| {
            let ast::ItemKind::Fn(function) = &item.kind else { return None };
            (function.ident.name == segment.ident.name && function.body.is_some())
                .then_some((item, function))
        }) else {
            continue;
        };
        if args.len() != wrapper.sig.decl.inputs.len()
            || args.len() != internal.sig.decl.inputs.len()
        {
            continue;
        }
        let mut sites = vec![];
        let mut generated_shape = true;
        for ((argument, parameter), internal_parameter) in args
            .iter()
            .zip(&wrapper.sig.decl.inputs)
            .zip(&internal.sig.decl.inputs)
        {
            let ast::PatKind::Ident(_, ident, None) = &parameter.pat.kind else {
                generated_shape = false;
                break;
            };
            if is_name(argument, ident.name) {
                continue;
            }
            let Some((empty, nonnull)) = null_conversion(argument, ident.name) else {
                generated_shape = false;
                break;
            };
            if let Some(bound) = slice_bound(
                empty,
                nonnull,
                ident.name,
                &parameter.ty,
                &internal_parameter.ty,
            ) {
                let start = offsets.original(bound.span.lo().0 as usize);
                let end = offsets.original(bound.span.hi().0 as usize);
                let text = source.get(start..end).ok_or("invalid wrapper bound span")?;
                sites.push(WrapperBoundSite {
                    start,
                    end,
                    text: text.to_owned(),
                });
            }
        }
        if generated_shape && !sites.is_empty() {
            sites.sort_by_key(|site| site.start);
            result.push(WrapperBounds {
                path: module
                    .iter()
                    .cloned()
                    .chain([wrapper.ident.to_string()])
                    .collect::<Vec<_>>()
                    .join("::"),
                wrapper: item_source(source, item, offsets)?,
                internal: item_source(source, internal_item, offsets)?,
                sites,
            });
        }
    }
    Ok(())
}

fn item_source(source: &str, item: &ast::Item, offsets: &SourceOffsets) -> Result<String, String> {
    let start = item
        .attrs
        .iter()
        .map(|attr| attr.span.lo())
        .chain([item.span.lo()])
        .min()
        .unwrap();
    source
        .get(offsets.original(start.0 as usize)..offsets.original(item.span.hi().0 as usize))
        .map(str::to_owned)
        .ok_or_else(|| "invalid function source span".to_owned())
}

fn block_expression(block: &ast::Block) -> Option<&ast::Expr> {
    let [statement] = block.stmts.as_slice() else { return None };
    match &statement.kind {
        ast::StmtKind::Expr(expression) => Some(utils::ast::unwrap_paren(expression)),
        _ => None,
    }
}

fn is_name(expression: &ast::Expr, name: Symbol) -> bool {
    matches!(&utils::ast::unwrap_paren(expression).kind, ast::ExprKind::Path(None, path)
        if path.segments.len() == 1 && path.segments[0].ident.name == name)
}

fn null_conversion(expression: &ast::Expr, name: Symbol) -> Option<(&ast::Expr, &ast::Expr)> {
    let ast::ExprKind::If(condition, empty, Some(nonnull)) = &expression.kind else { return None };
    let ast::ExprKind::MethodCall(method) = &condition.kind else { return None };
    if method.seg.ident.name.as_str() != "is_null"
        || !method.args.is_empty()
        || !is_name(&method.receiver, name)
    {
        return None;
    }
    let ast::ExprKind::Block(nonnull, _) = &nonnull.kind else { return None };
    Some((block_expression(empty)?, block_expression(nonnull)?))
}

fn path_parts(expression: &ast::Expr) -> Option<Vec<String>> {
    let ast::ExprKind::Path(None, path) = &expression.kind else { return None };
    Some(
        path.segments
            .iter()
            .filter(|segment| segment.ident.name != kw::PathRoot)
            .map(|segment| segment.ident.name.to_string())
            .collect(),
    )
}

fn cursor_call<'a>(
    expression: &'a ast::Expr,
    cursor: &str,
    method: &str,
) -> Option<&'a [P<ast::Expr>]> {
    let ast::ExprKind::Call(callee, args) = &expression.kind else { return None };
    (path_parts(callee)?.as_slice() == ["crate", "slice_cursor", cursor, method])
        .then_some(args.as_slice())
}

fn slice_bound<'a>(
    empty: &ast::Expr,
    mut nonnull: &'a ast::Expr,
    name: Symbol,
    raw: &ast::Ty,
    internal: &ast::Ty,
) -> Option<&'a ast::Expr> {
    let ast::TyKind::Ptr(raw) = &raw.kind else { return None };
    let mutable = raw.mutbl.is_mut();
    if let ast::ExprKind::AddrOf(ast::BorrowKind::Ref, mutability, value) = &empty.kind {
        let slice_type = match &internal.kind {
            ast::TyKind::Ref(_, inner) => {
                matches!(inner.ty.kind, ast::TyKind::Slice(_)) && inner.mutbl == raw.mutbl
            }
            ast::TyKind::Path(..) => true,
            _ => false,
        };
        if !slice_type
            || *mutability != raw.mutbl
            || !matches!(&value.kind, ast::ExprKind::Array(values) if values.is_empty())
        {
            return None;
        }
    } else {
        if !matches!(internal.kind, ast::TyKind::Path(..)) {
            return None;
        }
        let cursor = if mutable {
            "SliceCursorMut"
        } else {
            "SliceCursor"
        };
        if !cursor_call(empty, cursor, "empty")?.is_empty() {
            return None;
        }
        let [parts] = cursor_call(nonnull, cursor, "new")? else { return None };
        nonnull = parts;
    }
    let ast::ExprKind::Call(callee, args) = &nonnull.kind else { return None };
    let parts = path_parts(callee)?;
    let [root, module, function] = parts.as_slice() else { return None };
    if !matches!(root.as_str(), "std" | "core")
        || module != "slice"
        || function
            != if mutable {
                "from_raw_parts_mut"
            } else {
                "from_raw_parts"
            }
    {
        return None;
    }
    let [pointer, bound] = args.as_slice() else { return None };
    let ast::ExprKind::Lit(literal) = &bound.kind else { return None };
    (is_name(pointer, name)
        && literal.kind == ast::token::LitKind::Integer
        && literal.symbol.as_str().replace('_', "").parse::<u128>() == Ok(1_000_000))
    .then_some(bound)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(source: &str) -> WrapperBoundsRequest {
        WrapperBoundsRequest {
            source: source.to_owned(),
            wrapper: None,
            expressions: None,
        }
    }

    const SOURCE: &str = r#"// Unicode: λ
mod nested {
unsafe fn read_internal(a: &[i32], b: &mut [u8], n: usize) -> i32 { a[n] + b[n] as i32 }
#[no_mangle]
pub unsafe extern "C" fn read(a: *const i32, b: *mut u8, n: usize) -> i32 {
    read_internal(if a.is_null() { &[] } else { std::slice::from_raw_parts(a, 1_000_000) },
                  if b.is_null() { &mut [] } else { std::slice::from_raw_parts_mut(b, 1000000) }, n)
}
}
"#;

    #[test]
    fn finds_ordered_byte_spans_and_exact_function_sources() {
        let output = process_wrapper_bounds(&request(SOURCE)).unwrap();
        assert!(output.candidate.is_none());
        let [wrapper] = output.wrappers.as_slice() else { panic!() };
        assert_eq!(wrapper.path, "nested::read");
        assert!(wrapper.wrapper.starts_with("#[no_mangle]"));
        assert!(wrapper.internal.starts_with("unsafe fn read_internal"));
        assert_eq!(wrapper.sites.len(), 2);
        assert!(wrapper.sites[0].start < wrapper.sites[1].start);
        for site in &wrapper.sites {
            assert_eq!(&SOURCE[site.start..site.end], site.text);
        }
    }

    #[test]
    fn preserves_byte_spans_for_crlf_and_bom_source() {
        for source in [
            SOURCE.replace('\n', "\r\n"),
            format!("\u{feff}{SOURCE}"),
            format!("\u{feff}{}", SOURCE.replace('\n', "\r\n")),
            SOURCE.replace("1_000_000)", "1_000_000\r\n)"),
        ] {
            let mut request = request(&source);
            request.wrapper = Some("nested::read".to_owned());
            request.expressions = Some(vec!["n".to_owned(), "1000000".to_owned()]);
            let output = process_wrapper_bounds(&request).unwrap();
            assert_eq!(
                output.candidate.unwrap(),
                source.replacen("1_000_000", "(n\n)", 1)
            );
        }
    }

    #[test]
    fn detects_internal_parameter_type_aliases() {
        let source = r#"
type Slice<'a> = &'a [i32];
unsafe fn internal(p: Slice<'_>) {}
unsafe fn wrapper(p: *const i32) {
    internal(if p.is_null() { &[] } else { std::slice::from_raw_parts(p, 1_000_000) })
}
type Cursor<'a> = crate::slice_cursor::SliceCursor<'a, i32>;
unsafe fn cursor_internal(p: Cursor<'_>) {}
unsafe fn cursor_wrapper(p: *const i32) {
    cursor_internal(if p.is_null() { crate::slice_cursor::SliceCursor::empty() }
        else { crate::slice_cursor::SliceCursor::new(std::slice::from_raw_parts(p, 1_000_000)) })
}
"#;
        let output = process_wrapper_bounds(&request(source)).unwrap();
        assert_eq!(output.wrappers.len(), 2);
    }

    #[test]
    fn replaces_only_bound_spans_and_keeps_original_literals_exact() {
        let mut request = request(SOURCE);
        request.wrapper = Some("nested::read".to_owned());
        request.expressions = Some(vec!["n + 1".to_owned(), "1000000".to_owned()]);
        let output = process_wrapper_bounds(&request).unwrap();
        assert_eq!(
            output.candidate.unwrap(),
            SOURCE.replacen("1_000_000", "(n + 1\n)", 1)
        );
        request.expressions = Some(vec!["1_000_000".to_owned(), "1000000".to_owned()]);
        assert_eq!(
            process_wrapper_bounds(&request).unwrap().candidate.unwrap(),
            SOURCE
        );
    }

    #[test]
    fn accepts_single_expressions_and_trailing_comments_without_escaping() {
        for expression in ["n as usize", "(n + 1) * 2", "{ n + 1 }", "n // length"] {
            let mut request = request(SOURCE);
            request.wrapper = Some("nested::read".to_owned());
            request.expressions = Some(vec![expression.to_owned(), "1000000".to_owned()]);
            assert!(process_wrapper_bounds(&request).is_ok(), "{expression}");
        }
    }

    #[test]
    fn rejects_malformed_requests_and_expression_escape_attempts() {
        for expressions in [
            vec![],
            vec!["n"],
            vec!["", "n"],
            vec!["n;", "n"],
            vec!["n); panic!(); let _ = (n", "n"],
            vec!["n); } fn injected() {} fn other() { let _ = (n", "n"],
            vec!["n, 0", "n"],
            vec!["n /*", "n"],
        ] {
            let mut request = request(SOURCE);
            request.wrapper = Some("nested::read".to_owned());
            request.expressions = Some(expressions.into_iter().map(str::to_owned).collect());
            assert!(process_wrapper_bounds(&request).is_err());
        }
        let mut request = request(SOURCE);
        request.wrapper = Some("nested::read".to_owned());
        assert!(process_wrapper_bounds(&request).is_err());
        assert!(
            serde_json::from_str::<WrapperBoundsRequest>(r#"{"source":"", "unknown":0}"#).is_err()
        );
    }

    #[test]
    fn detects_field_specialization_and_cursor_wrappers_without_name_suffixes() {
        let source = r#"
struct Ctx { x: i32 }
unsafe fn field(a: &mut [i32], ctx: Option<&i32>) {}
unsafe fn api(a: *mut i32, ctx: *const Ctx) {
    field(if a.is_null() { &mut [] } else { ::core::slice::from_raw_parts_mut(a, 1_000_000) },
          if ctx.is_null() { None } else { Some(&(*ctx).x) })
}
unsafe fn cursor_impl(p: crate::slice_cursor::SliceCursor<'_, i32>) {}
unsafe fn cursor(p: *const i32) {
    cursor_impl(if p.is_null() { crate::slice_cursor::SliceCursor::empty() }
        else { crate::slice_cursor::SliceCursor::new(std::slice::from_raw_parts(p, 1_000_000)) })
}
unsafe fn mut_cursor_impl(p: crate::slice_cursor::SliceCursorMut<'_, i32>) {}
unsafe fn r#type(p: *mut i32) {
    mut_cursor_impl(if p.is_null() { crate::slice_cursor::SliceCursorMut::empty() }
        else { crate::slice_cursor::SliceCursorMut::new(std::slice::from_raw_parts_mut(p, 1_000_000usize)) })
}
"#;
        let output = process_wrapper_bounds(&request(source)).unwrap();
        assert_eq!(
            output
                .wrappers
                .iter()
                .map(|wrapper| wrapper.path.as_str())
                .collect::<Vec<_>>(),
            ["api", "cursor", "r#type"]
        );
    }

    #[test]
    fn replacements_rediscover_current_spans_after_another_wrapper_changes() {
        let source = SOURCE.to_owned() + &SOURCE.replace("nested", "second");
        let mut first = request(&source);
        first.wrapper = Some("nested::read".to_owned());
        first.expressions = Some(vec!["n".to_owned(), "n".to_owned()]);
        let candidate = process_wrapper_bounds(&first).unwrap().candidate.unwrap();
        let mut second = request(&candidate);
        second.wrapper = Some("second::read".to_owned());
        second.expressions = Some(vec!["n + 2".to_owned(), "1000000".to_owned()]);
        let output = process_wrapper_bounds(&second).unwrap().candidate.unwrap();
        assert_eq!(output, candidate.replacen("1_000_000", "(n + 2\n)", 1));
        assert_eq!(
            process_wrapper_bounds(&request(&output))
                .unwrap()
                .wrappers
                .len(),
            1
        );
    }

    #[test]
    fn malformed_source_and_unknown_wrapper_are_rejected() {
        assert!(process_wrapper_bounds(&request("fn {")).is_err());
        let mut request = request(SOURCE);
        request.wrapper = Some("missing".to_owned());
        request.expressions = Some(vec!["0".to_owned()]);
        assert!(process_wrapper_bounds(&request).is_err());
        request.wrapper = None;
        assert!(process_wrapper_bounds(&request).is_err());
    }

    #[test]
    fn ignores_comments_strings_unrelated_calls_and_wrong_conversion_shapes() {
        for source in [
            "// std::slice::from_raw_parts(p, 1_000_000)\nfn f() {}",
            "fn f() { let _ = \"std::slice::from_raw_parts(p, 1_000_000)\"; }",
            "unsafe fn f(p: *const i32) { std::slice::from_raw_parts(p, 1_000_000); }",
            "unsafe fn inner(p: *const i32) {} unsafe fn f(p: *const i32) { inner(if p.is_null() { &[] } else { std::slice::from_raw_parts(p, 1_000_000) }) }",
            "unsafe fn inner(p: &[i32]) {} unsafe fn f(p: *const i32) { inner(if p.is_null() { &[] } else { other::slice::from_raw_parts(p, 1_000_000) }) }",
            "unsafe fn inner(p: &[i32]) {} unsafe fn f(p: *const i32) { inner(if p.is_null() { &[] } else { std::slice::from_raw_parts(p, 42) }) }",
            "unsafe fn inner(p: &[i32]) {} unsafe fn f(p: *const i32) { inner(if p.is_null() { &[0] } else { std::slice::from_raw_parts(p, 1_000_000) }) }",
            "unsafe fn inner(p: &[i32]) {} unsafe fn f(p: *const i32) { inner(if !p.is_null() { &[] } else { std::slice::from_raw_parts(p, 1_000_000) }) }",
        ] {
            assert!(
                process_wrapper_bounds(&request(source))
                    .unwrap()
                    .wrappers
                    .is_empty(),
                "{source}"
            );
        }
    }
}
