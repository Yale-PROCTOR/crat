//! R216: nullable roots must be opened before evaluating their projections.
//! The recursive shapes come from rs-crown-derived bst::inorder and
//! avl::height/preOrder. These fixtures are compiled, never executed.

use super::{
    decision::{Decision, SubjectKind},
    emit_tests::ast_emitted_source_of,
    verify,
};

const NODE: &str = r#"
#![allow(dead_code, non_snake_case, unused_mut)]
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Node {
    pub key: i32,
    pub left: *mut Node,
    pub right: *mut Node,
    pub height: i32,
}
"#;

fn assert_optional_projection_output(input: &str, subjects: &[(&str, &str, bool)]) -> String {
    assert!(
        verify::type_checks_str(input),
        "projection input must type-check"
    );
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("projection decisions");
        for &(function, binding, local) in subjects {
            let selected = table
                .entries
                .iter()
                .find(|(subject, _)| {
                    tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
                        && subject.param_name.as_deref() == Some(binding)
                        && matches!(subject.kind, SubjectKind::Local) == local
                })
                .unwrap_or_else(|| panic!("missing {function}::{binding}: {:?}", table.entries));
            assert!(
                matches!(selected.1, Decision::Opt { slice: false, .. }),
                "{function}::{binding} must actually be admitted as a thin Option: {:?}",
                selected.1,
            );
        }
    })
    .expect("projection fixture compiler context");

    let emitted = ast_emitted_source_of(input).expect("projection emission");
    for &(_, binding, _) in subjects {
        assert!(
            emitted.contains(&format!("{binding}: Option<")),
            "the optional subject must survive class finalization: {emitted}",
        );
    }
    assert!(
        verify::type_checks_str(&emitted),
        "every native/projected use of the surviving Option must type/borrow-check: {emitted}",
    );
    emitted
}

#[test]
fn r216_bst_inorder_opens_optional_root_before_recursive_field_arguments() {
    let input = format!(
        r#"{NODE}
pub unsafe fn inorder(mut root: *mut Node) -> i32 {{
    if !root.is_null() {{
        let left = inorder((*root).left);
        let key = (*root).key;
        let right = inorder((*root).right);
        left + key + right
    }} else {{ 0 }}
}}
"#
    );
    assert_optional_projection_output(&input, &[("inorder", "root", false)]);
}

#[test]
fn r216_avl_height_keeps_the_native_optional_field_read() {
    let input = format!(
        r#"{NODE}
pub unsafe fn height(mut n: *mut Node) -> i32 {{
    if n.is_null() {{ return 0; }}
    (*n).height
}}
"#
    );
    assert_optional_projection_output(&input, &[("height", "n", false)]);
}

#[test]
fn r216_avl_preorder_opens_optional_root_for_height_and_recursive_calls() {
    let input = format!(
        r#"{NODE}
unsafe fn height(mut n: *mut Node) -> i32 {{
    if n.is_null() {{ return 0; }}
    (*n).height
}}
pub unsafe fn preOrder(mut root: *mut Node) -> i32 {{
    if !root.is_null() {{
        (*root).key + height((*root).left) + height((*root).right)
            + preOrder((*root).left) + preOrder((*root).right)
    }} else {{ 0 }}
}}
"#
    );
    assert_optional_projection_output(
        &input,
        &[("height", "n", false), ("preOrder", "root", false)],
    );
}

#[test]
fn r216_optional_local_keeps_native_deref_and_projected_call_uses() {
    let input = format!(
        r#"{NODE}
type RawNode = *mut Node;
fn value_key(value: Node) -> i32 {{ value.key }}
unsafe fn height(n: *mut Node) -> i32 {{
    if n.is_null() {{ 0 }} else {{ (*n).height }}
}}
pub unsafe fn local_projection(src: RawNode) -> i32 {{
    let current: *mut Node = src;
    if current.is_null() {{ return 0; }}
    value_key(*current) + (*current).key + height((*current).left)
}}
"#
    );
    assert_optional_projection_output(&input, &[("local_projection", "current", true)]);
}
