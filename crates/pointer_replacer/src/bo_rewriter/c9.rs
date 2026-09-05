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
    let open = source
        .char_indices()
        .find_map(|(index, ch)| (ch == '(').then_some(index))
        .ok_or_else(|| "C-9 call source has no argument list".to_owned())?;
    let mut depth = 0usize;
    let mut close = None;
    for (offset, ch) in source[open..].char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| "C-9 call source has unmatched ')'".to_owned())?;
                if depth == 0 {
                    close = Some(open + offset);
                    break;
                }
            }
            _ => {}
        }
    }
    let close = close.ok_or_else(|| "C-9 call source has unmatched '('".to_owned())?;
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
    let open = source
        .char_indices()
        .find_map(|(index, ch)| (ch == '(').then_some(index))
        .ok_or_else(|| "PAIR call source has no argument list".to_owned())?;
    let mut depth = 0usize;
    let mut close = None;
    for (offset, ch) in source[open..].char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| "PAIR call source has unmatched ')'".to_owned())?;
                if depth == 0 {
                    close = Some(open + offset);
                    break;
                }
            }
            _ => {}
        }
    }
    let close = close.ok_or_else(|| "PAIR call source has unmatched '('".to_owned())?;
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

fn split_arguments(source: &str) -> Result<Vec<String>, String> {
    if source.trim().is_empty() {
        return Ok(Vec::new());
    }
    let mut answer = Vec::new();
    let mut start = 0usize;
    let mut stack = Vec::new();
    for (index, ch) in source.char_indices() {
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

    /// D13-W1 — LibTree's ANSI byte string contains `[` as data.  The current
    /// delimiter-only splitter rejects it, but the rejection must carry the
    /// exact argument source so the caller can turn this one site into a typed
    /// class hold instead of degrading the whole program.
    #[test]
    fn d13_w1_unclosed_delimiter_error_carries_the_argument_text() {
        let source = r#"print_line(x, b"\x1B[1;36m\0" as *const u8 as *mut i8)"#;
        let error = render_pair_raw_view_source(
            source,
            "__crat_pair_raw_fixture",
            &[(0, "x".to_owned(), "*mut i32".to_owned())],
        )
        .expect_err("the byte-string delimiter shape remains a site hold");
        assert!(
            error.contains("C-9 argument source has an unclosed delimiter")
                && error.contains(r#"b"\x1B[1;36m\0""#),
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
