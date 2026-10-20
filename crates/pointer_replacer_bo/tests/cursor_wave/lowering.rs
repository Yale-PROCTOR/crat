use std::{
    fs,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};

use rustc_ast::{ExprKind, NodeId, ptr::P};
use rustc_ast_pretty::pprust::{expr_to_string, ty_to_string};

use super::cursor_ast::{self, Movement, UnsafeContext};

fn expr(source: &str) -> P<rustc_ast::Expr> {
    P(utils::ast::parse_expr(source.to_owned()))
}

fn compile(source: &str, expected_code: Option<&str>) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "crat-cursor-compile-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("lib.rs");
    fs::write(&input, source).unwrap();
    let output = Command::new("rustc")
        .args([
            "--edition=2024",
            "--crate-type=lib",
            "--emit=metadata",
            "-o",
        ])
        .arg(dir.join("lib.rmeta"))
        .arg(&input)
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    let valid = match expected_code {
        Some(code) => !output.status.success() && stderr.contains(code),
        None => output.status.success(),
    };
    fs::remove_dir_all(dir).unwrap();
    assert!(valid, "compile witness: {stderr}\nsource:\n{source}");
}

#[test]
fn w04_w15_checked_lowering_preserves_operands_once_and_order() {
    rustc_span::create_default_session_globals_then(|| {
        for (movement, name, delta_ty) in [
            (Movement::Offset, "checked_add_signed", "isize"),
            (Movement::Add, "checked_add", "usize"),
            (Movement::Sub, "checked_sub", "usize"),
        ] {
            let mut index = expr("index()");
            index.id = NodeId::from_u32(61);
            let mut delta = expr("delta()");
            delta.id = NodeId::from_u32(62);
            let image = cursor_ast::checked_step(movement, index, delta);
            let ExprKind::MethodCall(call) = &image.kind else {
                panic!("checked integer method missing")
            };
            assert_eq!(call.seg.ident.name.as_str(), name);
            assert_eq!(call.receiver.id, NodeId::from_u32(61));
            assert_eq!(call.args.len(), 1);
            assert_eq!(call.args[0].id, NodeId::from_u32(62));
            let text = expr_to_string(&image);
            compile(
                &format!(
                    "fn index() -> usize {{ 1 }} fn delta() -> {delta_ty} {{ 1 }} pub fn step() -> Option<usize> {{ {text} }}"
                ),
                None,
            );
        }
    });
}

#[test]
fn w06_w08_tuple_forms_compile_with_one_mutable_base() {
    rustc_span::create_default_session_globals_then(|| {
        for mutable in [false, true] {
            for nullable in [false, true] {
                let ty = cursor_ast::declaration(
                    P(utils::ast::parse_ty("i32".into())),
                    mutable,
                    nullable,
                );
                let ty = ty_to_string(&ty);
                assert!(ty.contains("usize") && ty.contains("[i32]"));
                assert_eq!(ty.contains("Option"), nullable);
                let base = if mutable { "&mut *base" } else { "&*base" };
                let value = expr_to_string(&cursor_ast::tuple(expr(base), expr("index")));
                let value = if nullable {
                    format!("if absent {{ None }} else {{ Some({value}) }}")
                } else {
                    value
                };
                let mode = if mutable { "mut " } else { "" };
                compile(
                    &format!(
                        "pub fn make(base: &{mode}[i32], index: usize, absent: bool) -> {ty} {{ {value} }}"
                    ),
                    None,
                );
            }
        }
    });
}

#[test]
fn w03_w17_endpoint_raw_view_uses_current_index_without_element_borrow() {
    rustc_span::create_default_session_globals_then(|| {
        for mutable in [false, true] {
            for context in [UnsafeContext::SafeBody, UnsafeContext::UnsafeBody] {
                let image = cursor_ast::raw_view(expr("base"), expr("index"), mutable, context);
                let image = expr_to_string(&image);
                assert!(image.contains(".add(index)"));
                assert!(!image.contains("[index]"));
                assert_eq!(image.contains("unsafe"), context == UnsafeContext::SafeBody);
                let mode = if mutable { "mut " } else { "" };
                let ptr = if mutable { "mut" } else { "const" };
                let safety = if context == UnsafeContext::UnsafeBody {
                    "unsafe "
                } else {
                    ""
                };
                compile(
                    &format!(
                        "#![allow(unsafe_op_in_unsafe_fn)] pub {safety}fn endpoint(base: &{mode}[i32]) -> *{ptr} i32 {{ let index = base.len(); {image} }}"
                    ),
                    None,
                );
            }
        }
    });
}

#[test]
fn w11_conflicting_element_loan_is_rejected_by_rustc() {
    rustc_span::create_default_session_globals_then(|| {
        let first = expr_to_string(&cursor_ast::element(expr("base"), expr("i"), true));
        assert!(first.contains("[i]"));
        let second = expr_to_string(&cursor_ast::element(expr("base"), expr("j"), true));
        compile(
            &format!(
                "pub fn conflict(base: &mut [i32], i: usize, j: usize) {{ let p = {first}; let q = {second}; *p += *q; }}"
            ),
            Some("E0499"),
        );
        compile(
            &format!(
                "pub fn sequential(base: &mut [i32], i: usize, j: usize) {{ let p = {first}; *p += 1; let q = {second}; *q += 1; }}"
            ),
            None,
        );
    });
}

#[test]
fn w18_generated_index_type_survives_primitive_name_shadowing() {
    rustc_span::create_default_session_globals_then(|| {
        let ty = ty_to_string(&cursor_ast::declaration(
            P(utils::ast::parse_ty("i32".into())),
            true,
            false,
        ));
        let value = expr_to_string(&cursor_ast::tuple(expr("base"), expr("index")));
        compile(
            &format!(
                "#![allow(non_camel_case_types)] pub struct usize; \
                 pub fn make(base: &mut [i32], index: ::core::primitive::usize) \
                 -> {ty} {{ {value} }}"
            ),
            None,
        );
    });
}
