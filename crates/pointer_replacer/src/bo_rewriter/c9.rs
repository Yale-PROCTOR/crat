//! Typed C-9 call-site emission.

use crate::analyses::borrow_ownership::a5_overlap::{C9MarkKey, PairSide};

pub(crate) fn render_marked_call(
    mark: &C9MarkKey,
    callee: &str,
    arguments: &[String],
) -> Result<String, String> {
    let params = mark.pair.params();
    let shared = match mark.shared_side {
        PairSide::Left => params.first(),
        PairSide::Right => params.second(),
    };
    let index = usize::try_from(shared)
        .ok()
        .and_then(|index| index.checked_sub(1))
        .ok_or_else(|| "C-9 formal indices are one-based".to_owned())?;
    if index >= arguments.len() {
        return Err("C-9 shared argument is outside the call arity".to_owned());
    }
    let temp = format!(
        "__crat_c9_{}_{}",
        mark.location.block, mark.location.statement_index
    );
    let mut rewritten = arguments.to_vec();
    rewritten[index] = format!("&{temp}");
    Ok(format!(
        "{{ let {temp}: {} = *({}); {}({}) }}",
        mark.pointee_type,
        arguments[index],
        callee,
        rewritten.join(", ")
    ))
}

pub(crate) fn render_marked_source(mark: &C9MarkKey, source: &str) -> Result<String, String> {
    let (open, close) = argument_list(source, "C-9")?;
    let callee = source[..open].trim();
    if callee.is_empty() {
        return Err("C-9 call source has an empty callee".to_owned());
    }
    let arguments = split_arguments(&source[open + 1..close])?;
    let rendered = render_marked_call(mark, callee, &arguments)?;
    Ok(format!("{rendered}{}", &source[close + 1..]))
}

pub(crate) const A5_RAW_VALUE_PLACEHOLDER: &str = "__crat_a5_raw_value";
pub(crate) const A5_EXTENT_VALUE_PLACEHOLDER: &str = "__crat_a5_extent_value";

pub(crate) fn render_pair_raw_view_source(
    source: &str,
    temp_stem: &str,
    views: &[(usize, String, String)],
) -> Result<String, String> {
    let views = views
        .iter()
        .map(|(index, raw_expression, target_type)| {
            (
                *index,
                raw_expression.clone(),
                target_type.clone(),
                A5_RAW_VALUE_PLACEHOLDER.to_owned(),
                None,
            )
        })
        .collect::<Vec<_>>();
    render_raw_view_source(source, temp_stem, &views)
}

pub(crate) fn render_a5_raw_view_source(
    source: &str,
    temp_stem: &str,
    views: &[(usize, String, String, String, Option<String>)],
) -> Result<String, String> {
    render_raw_view_source(source, temp_stem, views)
}

fn render_raw_view_source(
    source: &str,
    temp_stem: &str,
    views: &[(usize, String, String, String, Option<String>)],
) -> Result<String, String> {
    // **R482-4(f)** — the literal rule governs this scan too: a `(` inside a
    // string is not a parenthesis.
    //
    // **R483-3 (STOP 2)** — the argument list is the call's LAST top-level
    // group, not its first. A C2Rust function-pointer call is `(*f)(a, b)`,
    // whose first `(` is at offset 0: reading that as the argument list left
    // the callee empty and held the class. Walking the top-level groups and
    // keeping the last one names `(*f)` as the callee and `(a, b)` as its
    // arguments, and leaves every ordinary shape where it was.
    let (open, close) = argument_list(source, "PAIR")?;
    let callee = source[..open].trim();
    if callee.is_empty() {
        return Err("PAIR call source has an empty callee".to_owned());
    }
    let argument_source = &source[open + 1..close];
    let mut arguments = split_arguments(argument_source).map_err(|why| {
        format!(
            "{why};argument-source={}",
            argument_source
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ")
        )
    })?;
    let mut declarations = Vec::new();
    for (argument_index, raw_expression, target_type, adapted_expression, extent_expression) in
        views
    {
        let Some(argument) = arguments.get_mut(*argument_index) else {
            return Err("PAIR raw-view argument is outside the call arity".to_owned());
        };
        let temp = format!("{temp_stem}_{argument_index}");
        let extent = format!("{temp}_extent");
        if let Some(expression) = extent_expression {
            declarations.push(format!("let {extent}: usize = {expression};"));
        }
        declarations.push(format!("let {temp}: {target_type} = {raw_expression};"));
        if adapted_expression.matches(A5_RAW_VALUE_PLACEHOLDER).count() != 1 {
            return Err("raw-view adapter must name its raw temporary exactly once".to_owned());
        }
        let mut adapted = adapted_expression.replace(A5_RAW_VALUE_PLACEHOLDER, &temp);
        let extent_uses = adapted.matches(A5_EXTENT_VALUE_PLACEHOLDER).count();
        if extent_expression.is_some() != (extent_uses == 1) {
            return Err("raw-view adapter extent placeholder mismatch".to_owned());
        }
        if extent_uses == 1 {
            adapted = adapted.replace(A5_EXTENT_VALUE_PLACEHOLDER, &extent);
        }
        *argument = adapted;
    }
    Ok(format!(
        "{{ {} {callee}({}) }}{}",
        declarations.join(" "),
        arguments.join(", "),
        &source[close + 1..],
    ))
}

/// The call's argument list: its LAST top-level parenthesised group, found
/// with literals skipped whole.
///
/// **R482-4(f)** — a `(` inside a string is not a parenthesis.
/// **R483-3 (STOP 2)** — the argument list is the call's LAST top-level group,
/// not its first. A C2Rust function-pointer call is `(*f)(a, b)`, whose first
/// `(` is at offset 0: reading that as the argument list leaves the callee
/// empty and holds the class. Keeping the last group names `(*f)` as the
/// callee and `(a, b)` as its arguments, and leaves every ordinary shape where
/// it was.
///
/// **R492-4** — `render_marked_source` had its own copy of this scan carrying
/// BOTH defects the two rulings above fixed here. The sweep of R490-4 found it;
/// there is one scan now, so a third copy cannot drift.
fn argument_list(source: &str, who: &str) -> Result<(usize, usize), String> {
    let bytes = source.as_bytes();
    let mut group = None;
    let mut index = 0usize;
    while index < bytes.len() {
        if let Some(end) = literal_end(bytes, index) {
            index = end;
            continue;
        }
        if bytes[index] != b'(' {
            index += 1;
            continue;
        }
        let start = index;
        let mut depth = 0usize;
        let mut end = None;
        while index < bytes.len() {
            if let Some(skip) = literal_end(bytes, index) {
                index = skip;
                continue;
            }
            match bytes[index] {
                b'(' => depth += 1,
                b')' => {
                    depth = depth
                        .checked_sub(1)
                        .ok_or_else(|| format!("{who} call source has unmatched ')'"))?;
                    if depth == 0 {
                        end = Some(index);
                    }
                }
                _ => {}
            }
            index += 1;
            if end.is_some() {
                break;
            }
        }
        let close = end.ok_or_else(|| format!("{who} call source has unmatched '('"))?;
        group = Some((start, close));
    }
    group.ok_or_else(|| format!("{who} call source has no argument list"))
}

/// **R482-4(f) — a literal is one token, and a delimiter inside it is data.**
///
/// The C-9 / A5 fallback renders from the CALLER's argument source text, and
/// the scan that finds the argument list and splits it counted every `(`,
/// `[`, `{` it saw. libtree's `print_line(depth, current_file,
/// b"\x1B[1;36m\0" as *const u8 as *const c_char, …)` then read the `[` of
/// an ANSI escape as an opening bracket and the whole class was held
/// `a5-fallback-unrenderable`. Arguments are split on the call's argument
/// boundaries; a byte string is not a boundary and does not nest.
///
/// Returns the byte index just past the literal starting at `bytes[index]`,
/// or `None` when this position does not begin one. Handles `"…"`, `b"…"`,
/// raw strings at any hash depth, char and byte-char literals, and — the case
/// that makes a naive scanner wrong in the other direction — LIFETIMES, where
/// `'` opens nothing at all.
pub(crate) fn literal_end(bytes: &[u8], index: usize) -> Option<usize> {
    let mut at = index;
    if bytes[at] == b'b' && at + 1 < bytes.len() && matches!(bytes[at + 1], b'"' | b'\'' | b'r') {
        at += 1;
    }
    match bytes[at] {
        b'r' => {
            let mut cursor = at + 1;
            let mut hashes = 0usize;
            while cursor < bytes.len() && bytes[cursor] == b'#' {
                hashes += 1;
                cursor += 1;
            }
            if cursor >= bytes.len() || bytes[cursor] != b'"' {
                return None;
            }
            cursor += 1;
            while cursor < bytes.len() {
                if bytes[cursor] == b'"'
                    && bytes[cursor + 1..]
                        .iter()
                        .take(hashes)
                        .filter(|byte| **byte == b'#')
                        .count()
                        == hashes
                {
                    return Some(cursor + 1 + hashes);
                }
                cursor += 1;
            }
            // Unterminated: the caller's own unmatched-delimiter error is the
            // right answer, so report the rest of the source as consumed.
            Some(bytes.len())
        }
        b'"' => {
            let mut cursor = at + 1;
            while cursor < bytes.len() {
                match bytes[cursor] {
                    b'\\' => cursor += 2,
                    b'"' => return Some(cursor + 1),
                    _ => cursor += 1,
                }
            }
            Some(bytes.len())
        }
        b'\'' => {
            // `'a` / `'static` is a lifetime: it opens nothing. A char literal
            // closes within one escape-aware step.
            let mut cursor = at + 1;
            if cursor < bytes.len() && bytes[cursor] == b'\\' {
                cursor += 2;
            } else if cursor < bytes.len() {
                cursor += 1;
            }
            (cursor < bytes.len() && bytes[cursor] == b'\'').then_some(cursor + 1)
        }
        _ => None,
    }
}

fn split_arguments(source: &str) -> Result<Vec<String>, String> {
    if source.trim().is_empty() {
        return Ok(Vec::new());
    }
    let mut answer = Vec::new();
    let mut start = 0usize;
    let mut stack = Vec::new();
    let bytes = source.as_bytes();
    let mut index = 0usize;
    while index < bytes.len() {
        // R482-4(f): a literal is one token; its delimiters are data.
        if let Some(end) = literal_end(bytes, index) {
            index = end;
            continue;
        }
        let ch = bytes[index] as char;
        match ch {
            '(' | '[' | '{' => stack.push(ch),
            ')' | ']' | '}' => {
                let Some(open) = stack.pop() else {
                    return Err("C-9 argument source has an unmatched delimiter".to_owned());
                };
                if !matches!((open, ch), ('(', ')') | ('[', ']') | ('{', '}')) {
                    return Err("C-9 argument source has mismatched delimiters".to_owned());
                }
            }
            ',' if stack.is_empty() => {
                answer.push(source[start..index].trim().to_owned());
                start = index + 1;
            }
            _ => {}
        }
        index += 1;
    }
    if !stack.is_empty() {
        return Err("C-9 argument source has an unclosed delimiter".to_owned());
    }
    answer.push(source[start..].trim().to_owned());
    if answer.iter().any(String::is_empty) {
        return Err("C-9 argument source contains an empty argument".to_owned());
    }
    Ok(answer)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyses::borrow_ownership::{
        a5_overlap::{C9MarkKey, PairSide},
        l2::{MirLocationKey, SlotKey},
    };

    fn mark() -> C9MarkKey {
        C9MarkKey::new(
            1,
            MirLocationKey::new(4, 2),
            [2],
            2,
            1,
            SlotKey {
                variant: 1,
                owner: 1,
                slot: 1,
            },
            2,
            SlotKey {
                variant: 1,
                owner: 1,
                slot: 2,
            },
            PairSide::Right,
            "i32".to_owned(),
        )
        .unwrap()
    }

    /// **R492-4 — the sweep's one finding (R490-4 STOP 3).** `render_marked_source`
    /// carried its own copy of the argument-list scan, and that copy predated
    /// BOTH rulings the sibling scan has taken: it counted a `(` inside a
    /// literal as a parenthesis (R482-4(f)) and it took the call's FIRST
    /// top-level group rather than its last (R483-3 STOP 2). The two tests
    /// below are the exact shapes those defects refuse; both now render.
    #[test]
    fn r492_4_a_marked_call_reads_a_literal_as_one_token() {
        let rendered = render_marked_source(&mark(), r#"foo(p, b"a(b\0" as *const u8 as *mut i8)"#)
            .expect("a parenthesis inside a byte-string literal is data");
        assert!(
            rendered.contains(r#"b"a(b\0" as *const u8 as *mut i8"#),
            "the literal argument survives whole: {rendered}"
        );
    }

    /// A C2Rust function-pointer call: the first `(` is at offset 0, so the
    /// old scan left the callee empty and refused the site.
    #[test]
    fn r492_4_a_marked_function_pointer_call_keeps_its_callee() {
        let rendered = render_marked_source(&mark(), "(*f)(p, q)")
            .expect("the argument list is the LAST top-level group");
        assert!(
            rendered.contains("(*f)("),
            "the callee is `(*f)`, not the empty string: {rendered}"
        );
    }

    /// **R482-4(f).** D13-W1 pinned this shape as a HOLD: libtree's ANSI byte
    /// string contains `[` as data, the delimiter-only splitter counted it as
    /// an opening bracket, and the site was held. The hold was the splitter's
    /// defect, not the source's — a literal is one token, and the `[` inside
    /// it is not a delimiter. Restated under R217-2(a): what D13-W1 protected
    /// (the rejection carries the exact argument source) is kept below on a
    /// source that really is unclosed; this shape must now RENDER.
    #[test]
    fn r482_4f_a_byte_string_bracket_is_data_not_a_delimiter() {
        let source = r#"print_line(x, b"\x1B[1;36m\0" as *const u8 as *mut i8)"#;
        let rendered = render_pair_raw_view_source(
            source,
            "__crat_pair_raw_fixture",
            &[(0, "x".to_owned(), "*mut i32".to_owned())],
        )
        .expect("a bracket inside a byte-string literal is data");
        assert!(
            rendered.contains(r#"b"\x1B[1;36m\0" as *const u8 as *mut i8"#),
            "the literal argument survives whole: {rendered}"
        );
        assert!(
            rendered.contains("let __crat_pair_raw_fixture_0: *mut i32 = x;"),
            "the viewed argument still takes its typed temporary: {rendered}"
        );
    }

    /// The other literal shapes that carry a delimiter as data. Each one is a
    /// separate scanner state, so each is asserted rather than assumed.
    #[test]
    fn r482_4f_every_literal_form_carries_its_delimiters_as_data() {
        for argument in [
            r#""a ( b [ c { d""#,
            r#"b"\x1B[1;36m\0""#,
            r#"'('"#,
            r#"b'['"#,
            r#"'\''"#,
            r#"r"raw ( and [""#,
            r##"r#"hash " raw ( ["#"##,
        ] {
            let source = format!("callee(x, {argument})");
            let rendered = render_pair_raw_view_source(
                &source,
                "__crat_lit",
                &[(0, "x".to_owned(), "*mut i32".to_owned())],
            )
            .unwrap_or_else(|why| panic!("{argument} must be one token: {why}"));
            assert!(rendered.contains(argument), "{argument}: {rendered}");
        }
    }

    /// A lifetime is not an unterminated char literal. `'static` in a cast is
    /// the shape that makes the char-literal state machine wrong if it simply
    /// scans to the next `'`.
    #[test]
    fn r482_4f_a_lifetime_is_not_a_char_literal() {
        let source = "callee(x, y as &'static [u8])";
        let rendered = render_pair_raw_view_source(
            source,
            "__crat_lt",
            &[(0, "x".to_owned(), "*mut i32".to_owned())],
        )
        .expect("a lifetime is not a literal");
        assert!(rendered.contains("y as &'static [u8]"), "{rendered}");
    }

    /// **R483-3, STOP 2.** lil's four rows: a C2Rust function-pointer call is
    /// `(*f)(a, b)`, whose FIRST `(` is at offset 0, so the callee read empty
    /// and the class was held `a5-fallback-unrenderable: PAIR call source has
    /// an empty callee`. The argument list is the call's LAST top-level
    /// parenthesised group, not its first.
    #[test]
    fn r483_3_stop2_a_parenthesised_callee_is_not_an_empty_callee() {
        let source = "(*f)(x, y)";
        let rendered = render_pair_raw_view_source(
            source,
            "__crat_fnptr",
            &[(0, "x".to_owned(), "*mut i32".to_owned())],
        )
        .expect("a parenthesised callee is a callee");
        assert!(
            rendered.contains("(*f)(__crat_fnptr_0, y)"),
            "the callee keeps its parentheses and only the view moves: {rendered}"
        );
    }

    /// Controls — the ordinary shape is unchanged, a nested group inside the
    /// arguments is not mistaken for the list, and a trailing cast still rides
    /// along.
    #[test]
    fn r483_3_stop2_the_ordinary_and_nested_shapes_are_unchanged() {
        for (source, expected) in [
            ("callee(x, y)", "callee(__crat_s_0, y)"),
            ("callee(x, g(y))", "callee(__crat_s_0, g(y))"),
            ("(*table[3].fp)(x, y)", "(*table[3].fp)(__crat_s_0, y)"),
        ] {
            let rendered = render_pair_raw_view_source(
                source,
                "__crat_s",
                &[(0, "x".to_owned(), "*mut i32".to_owned())],
            )
            .unwrap_or_else(|why| panic!("{source}: {why}"));
            assert!(rendered.contains(expected), "{source}: {rendered}");
        }
    }

    /// Control — a parenthesised expression that is NOT a call still has an
    /// empty callee. The rule admits a callee, not any last group.
    #[test]
    fn r483_3_stop2_a_bare_parenthesised_expression_is_still_an_empty_callee() {
        let error = render_pair_raw_view_source(
            "(x + y)",
            "__crat_s",
            &[(0, "x".to_owned(), "*mut i32".to_owned())],
        )
        .expect_err("a parenthesised expression is not a call");
        assert!(
            error.contains("PAIR call source has an empty callee"),
            "{error}"
        );
    }

    /// D13-W1's surviving half: a source that really is unclosed still names
    /// its argument text, so the caller can hold that one site.
    #[test]
    fn d13_w1_unclosed_delimiter_error_carries_the_argument_text() {
        let source = "print_line(x, some_call(a, b)";
        let error = render_pair_raw_view_source(
            source,
            "__crat_pair_raw_fixture",
            &[(0, "x".to_owned(), "*mut i32".to_owned())],
        )
        .expect_err("a genuinely unclosed source is still a site hold");
        assert!(
            error.contains("PAIR call source has unmatched '('"),
            "{error}"
        );
    }

    #[test]
    fn w7_mark_emits_one_typed_temp_and_substitutes_only_shared_argument() {
        assert_eq!(
            render_marked_call(&mark(), "two", &["x".to_owned(), "y".to_owned()]).unwrap(),
            "{ let __crat_c9_4_2: i32 = *(y); two(x, &__crat_c9_4_2) }"
        );
    }

    #[test]
    fn w13_suppressing_mark_export_removes_the_required_temp() {
        let emitted =
            render_marked_call(&mark(), "two", &["x".to_owned(), "y".to_owned()]).unwrap();
        let unmarked = "two(x, y)";
        assert!(emitted.contains("let __crat_c9_4_2"));
        assert!(!unmarked.contains("__crat_c9_4_2"));
        assert_ne!(emitted, unmarked);
    }

    #[test]
    fn w7_w13_compile_gate_is_nonvacuous() {
        let marked =
            render_marked_call(&mark(), "two", &["&mut *p".to_owned(), "q".to_owned()]).unwrap();
        let source = |call: &str| {
            format!(
                "fn two(x: &mut i32, y: &i32) {{ *x = *y + 1; }} \
                 fn caller(p: &mut i32) {{ let q: &i32 = &*p; {call}; }}"
            )
        };
        assert!(crate::bo_rewriter::verify::type_checks_str(&source(
            &marked
        )));
        assert!(!crate::bo_rewriter::verify::type_checks_str(&source(
            "two(&mut *p, q)"
        )));
    }

    #[test]
    fn retained_mark_rewrites_one_source_call_with_nested_arguments() {
        assert_eq!(
            render_marked_source(&mark(), "two(&mut *p, pick(q, 1));").unwrap(),
            "{ let __crat_c9_4_2: i32 = *(pick(q, 1)); two(&mut *p, &__crat_c9_4_2) };"
        );
    }
}
