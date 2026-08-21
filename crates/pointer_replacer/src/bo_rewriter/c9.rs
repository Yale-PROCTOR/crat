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
}
