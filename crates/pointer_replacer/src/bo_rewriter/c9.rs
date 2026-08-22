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
