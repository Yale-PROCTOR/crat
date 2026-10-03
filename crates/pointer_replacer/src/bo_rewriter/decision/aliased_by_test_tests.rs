//! Wave-6o relay 134 (R767-1): an exported entry's formal that the program's
//! own provided test passes one object to, with another formal of the entry
//! and a member writing it, is held raw `held:exported-entry-aliased-by-test`;
//! the fixture rows are `aliased_by_test::FIXTURE_TABLE`.

fn fixture(body: &str) -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\n{body}"
    )
}

const ZAHL: &str = r###"
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Z {
    pub sign: i32,
    pub used: usize,
}
#[no_mangle]
pub unsafe extern "C" fn crat_w6o_zsub(a: *mut Z, b: *mut Z, c: *mut Z) {
    (*a).sign = (*b).sign - (*c).sign;
    (*a).used = (*b).used;
}
#[no_mangle]
pub unsafe extern "C" fn crat_w6o_zcmp(a: *mut Z, b: *mut Z) -> i32 {
    (*a).sign - (*b).sign
}
#[no_mangle]
pub unsafe extern "C" fn crat_w6o_zsetu(a: *mut Z, v: i32) {
    (*a).sign = v;
    (*a).used = 1;
}
pub unsafe fn crat_w6o_caller(x: *mut Z, y: *mut Z) -> i32 {
    crat_w6o_zsub(x, y, y);
    crat_w6o_zsetu(x, 1);
    crat_w6o_zcmp(x, y)
}
"###;

fn reasons(fn_name: &str) -> Vec<(String, String)> {
    crate::bo_rewriter::emit_tests::artifact_rows_of(&fixture(ZAHL))
        .into_iter()
        .filter(|r| r.fn_path.ends_with(fn_name) && r.arg_index.is_some())
        .map(|r| {
            (
                r.param_name.clone().unwrap_or_default(),
                r.degrade_reason
                    .clone()
                    .unwrap_or_else(|| "<emitted>".to_owned()),
            )
        })
        .collect()
}

fn reason(rows: &[(String, String)], name: &str) -> String {
    rows.iter()
        .find(|(n, _)| n == name)
        .map(|(_, r)| r.clone())
        .unwrap_or_else(|| panic!("no formal {name}: {rows:?}"))
}

const HELD: &str = "held:exported-entry-aliased-by-test";

/// W1 — the witness: `zsub(a, a, c)` / `zsub(a, b, a)` in the provided test,
/// `a` written: every member the table names is held raw, receipted.
#[test]
fn w6o_r767_w1_a_test_aliased_writing_pair_holds_its_formals() {
    let rows = reasons("crat_w6o_zsub");
    for name in ["a", "b", "c"] {
        assert_eq!(reason(&rows, name), HELD, "{name}: {rows:?}");
    }
}

/// C1 — the control: an exported entry no test aliases keeps W4's delivery.
#[test]
fn w6o_r767_c1_an_unaliased_exported_entry_keeps_its_reference() {
    let rows = reasons("crat_w6o_zsetu");
    assert_ne!(reason(&rows, "a"), HELD, "{rows:?}");
    assert!(!reason(&rows, "a").starts_with("held:"), "{rows:?}");
}

/// C2 — a read-only pair (`zcmp(a, a)`, the table's `clean` row) keeps its forms.
#[test]
fn w6o_r767_c2_a_read_only_aliased_pair_keeps_its_forms() {
    let rows = reasons("crat_w6o_zcmp");
    for name in ["a", "b"] {
        assert_ne!(reason(&rows, name), HELD, "{name}: {rows:?}");
    }
}

/// C3 — per formal, not per class: the in-crate caller's own formals are not
/// blocked by the held entry formals they flow into.
#[test]
fn w6o_r767_c3_the_in_crate_caller_is_not_class_blocked() {
    let rows = reasons("crat_w6o_caller");
    for name in ["x", "y"] {
        let r = reason(&rows, name);
        assert_ne!(r, HELD, "{name}: {rows:?}");
        assert!(
            !matches!(
                r.as_str(),
                "flows-into-raw-param" | "class-blocked" | "signature-class-held"
            ),
            "{name}: {rows:?}"
        );
    }
}
