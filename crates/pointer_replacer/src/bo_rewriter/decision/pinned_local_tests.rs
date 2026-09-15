//! Locals of a fn-pointer-pinned function: lil's `fnc_*` command callbacks are
//! registered `Some(fnc_if as unsafe extern "C" fn(…))`, which pins their
//! SIGNATURES; the `referenced` gate degraded every subject of those owners
//! `call-site-not-adapted`, locals included (42 of the 44 rows at `54e9a786`).
//! Reduced from `benchmarks/rs-crown-derived/lil/lib.rs` (`fnc_if`, `fnc_charat`).

const LIL: &str = r###"
#[derive(Copy, Clone)]
#[repr(C)]
pub struct _lil_value_t { pub l: usize, pub d: *mut i8 }
#[repr(C)]
pub struct _lil_t { pub error: i32, pub cmd: Option<unsafe extern "C" fn(*mut _lil_t, usize, *mut *mut _lil_value_t) -> *mut _lil_value_t> }
pub type lil_t = *mut _lil_t;
pub type lil_value_t = *mut _lil_value_t;
pub unsafe fn lil_register(lil: lil_t, proc_0: Option<unsafe extern "C" fn(lil_t, usize, *mut lil_value_t) -> lil_value_t>) { (*lil).cmd = proc_0; }
pub unsafe fn lil_parse_value(lil: lil_t, val: lil_value_t, funclevel: i32) -> lil_value_t {
    if val.is_null() || (*val).l == 0 { return 0 as lil_value_t; }
    let r = malloc(::core::mem::size_of::<_lil_value_t>()) as lil_value_t;
    (*r).l = (*val).l; (*r).d = (*val).d;
    r
}
pub unsafe fn lil_eval_expr(lil: lil_t, code: lil_value_t) -> lil_value_t { lil_parse_value(lil, code, 0) }
pub unsafe fn lil_to_boolean(val: lil_value_t) -> i32 { if val.is_null() { return 0; } ((*val).l != 0) as i32 }
pub unsafe fn lil_free_value(val: lil_value_t) { if val.is_null() { return; } free(val as *mut core::ffi::c_void); }
pub unsafe fn lil_to_string(val: lil_value_t) -> *const i8 {
    if !val.is_null() && !((*val).d).is_null() { (*val).d as *const i8 } else { b"\0" as *const u8 as *const i8 }
}
pub unsafe fn lil_to_integer(val: lil_value_t) -> i64 { if val.is_null() { 0 } else { (*val).l as i64 } }
pub unsafe fn lil_alloc_string(str: *const i8) -> lil_value_t {
    let r = malloc(::core::mem::size_of::<_lil_value_t>()) as lil_value_t;
    (*r).l = strlen(str); (*r).d = str as *mut i8;
    r
}
unsafe extern "C" fn fnc_if(mut lil: lil_t, mut argc: usize, mut argv: *mut lil_value_t) -> lil_value_t {
    let mut val = 0 as *mut _lil_value_t;
    let mut r = 0 as lil_value_t;
    let mut base = 0i32;
    let mut not = 0i32;
    let mut v: i32 = 0;
    if argc < 1 { return 0 as lil_value_t; }
    if strcmp(lil_to_string(*argv.offset(0)), b"not\0" as *const u8 as *const i8) == 0 { not = 1; base = not; }
    if argc < (base as usize).wrapping_add(2) { return 0 as lil_value_t; }
    val = lil_eval_expr(lil, *argv.offset(base as isize));
    if val.is_null() || (*lil).error != 0 { return 0 as lil_value_t; }
    v = lil_to_boolean(val);
    if not != 0 { v = (v == 0) as i32; }
    if v != 0 {
        r = lil_parse_value(lil, *argv.offset((base + 1) as isize), 0);
    } else if argc > (base as usize).wrapping_add(2) {
        r = lil_parse_value(lil, *argv.offset((base + 2) as isize), 0);
    }
    lil_free_value(val);
    return r;
}
unsafe extern "C" fn fnc_charat(mut lil: lil_t, mut argc: usize, mut argv: *mut lil_value_t) -> lil_value_t {
    let mut index: usize = 0;
    let mut chstr: [i8; 2] = [0; 2];
    let mut str = 0 as *const i8;
    if argc < 2 { return 0 as lil_value_t; }
    str = lil_to_string(*argv.offset(0));
    index = lil_to_integer(*argv.offset(1)) as usize;
    if index >= strlen(str) { return 0 as lil_value_t; }
    chstr[0] = *str.offset(index as isize);
    chstr[1] = 0;
    return lil_alloc_string(chstr.as_ptr());
}
unsafe extern "C" fn fnc_codeat(mut lil: lil_t, mut argc: usize, mut argv: *mut lil_value_t) -> lil_value_t {
    let mut chstr: [i8; 2] = [0; 2];
    if argc < 2 { return 0 as lil_value_t; }
    let index = lil_to_integer(*argv.offset(1)) as usize;
    let cp: *mut i8 = &mut chstr[0];
    *cp = index as i8;
    let err: *mut i32 = &mut (*lil).error;
    if *err != 0 { return 0 as lil_value_t; }
    *err = *cp as i32;
    return lil_alloc_string(chstr.as_ptr());
}
pub unsafe fn register_stdcmds(lil: lil_t) {
    lil_register(lil, Some(fnc_if as unsafe extern "C" fn(lil_t, usize, *mut lil_value_t) -> lil_value_t));
    lil_register(lil, Some(fnc_charat as unsafe extern "C" fn(lil_t, usize, *mut lil_value_t) -> lil_value_t));
    lil_register(lil, Some(fnc_codeat as unsafe extern "C" fn(lil_t, usize, *mut lil_value_t) -> lil_value_t));
}
"###;

fn fixture() -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\nextern \"C\" {{ fn malloc(size: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); fn strlen(s: *const i8) -> usize; fn strcmp(a: *const i8, b: *const i8) -> i32; }}\n{LIL}"
    )
}

fn decisions(input: &str) -> Vec<(String, super::Decision)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        crate::bo_rewriter::decide_table(tcx)
            .unwrap()
            .entries
            .iter()
            .map(|(s, d)| (s.label.clone(), d.clone()))
            .collect()
    })
    .unwrap()
}
fn decision<'a>(table: &'a [(String, super::Decision)], label: &str) -> &'a super::Decision {
    &table
        .iter()
        .find(|(l, _)| l == label)
        .unwrap_or_else(|| panic!("{label}"))
        .1
}
fn reason(d: &super::Decision) -> Option<&super::DegradeReason> {
    match d {
        super::Decision::Degraded(x) => Some(&x.reason),
        _ => None,
    }
}

/// The two real rows: the local is no longer gated by its owner's pin and
/// reaches its own typed gate.
#[test]
fn w5c_pinned_local_lil_rows_reach_their_own_gates() {
    use super::DegradeReason;
    let table = decisions(&fixture());
    assert!(
        matches!(
            reason(decision(&table, "fnc_if::r")),
            Some(DegradeReason::OptUseUnsupported)
        ),
        "{:?}",
        decision(&table, "fnc_if::r")
    );
    assert!(
        matches!(
            reason(decision(&table, "fnc_charat::str")),
            Some(DegradeReason::NullInit)
        ),
        "{:?}",
        decision(&table, "fnc_charat::str")
    );
}

/// Reference-shaped locals deliver inside a pinned callback; its signature
/// does not move.
#[test]
fn w5c_pinned_local_reference_locals_deliver_in_a_pinned_callback() {
    let input = fixture();
    let table = decisions(&input);
    for label in ["fnc_codeat::cp", "fnc_codeat::err"] {
        assert!(
            matches!(
                decision(&table, label),
                super::Decision::Ref { mutable: true }
            ),
            "{label}: {:?}",
            decision(&table, label)
        );
    }
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let flat = emitted.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("let cp: &mut i8 = &mut chstr[0];"),
        "{emitted}"
    );
    assert!(
        flat.contains("let err: &mut i32 = &mut (*lil).error;"),
        "{emitted}"
    );
    assert!(
        flat.contains("fn fnc_codeat(mut lil: lil_t, mut argc: usize, mut argv: *mut lil_value_t) -> lil_value_t"),
        "{emitted}"
    );
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    if let Ok(root) = std::env::var("CRAT_W5C_FIXTURE_CAPTURE") {
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(format!("{root}/lil-pinned-original.rs"), &input).unwrap();
        std::fs::write(format!("{root}/lil-pinned-emitted.rs"), &emitted).unwrap();
    }
}

/// The pin still gates every parameter of every registered callback.
#[test]
fn w5c_pinned_local_parameters_stay_pinned() {
    use super::DegradeReason;
    let table = decisions(&fixture());
    for label in [
        "fnc_if::argv",
        "fnc_charat::lil",
        "fnc_charat::argv",
        "fnc_codeat::lil",
        "fnc_codeat::argv",
    ] {
        assert!(
            matches!(
                reason(decision(&table, label)),
                Some(DegradeReason::CallSiteNotAdapted)
            ),
            "{label}: {:?}",
            decision(&table, label)
        );
    }
}

/// Without the registration the callbacks are ordinary functions: the same
/// locals deliver and `argv` is decided by its own facts, so the rule adds
/// nothing there.
#[test]
fn w5c_pinned_local_unpinned_control() {
    use super::DegradeReason;
    let input = fixture().replace(
        "pub unsafe fn register_stdcmds(lil: lil_t) {",
        "pub unsafe fn register_stdcmds(lil: lil_t) { return;",
    );
    let unpinned = input
        .replace("lil_register(lil, Some(fnc_if as", "//")
        .replace("lil_register(lil, Some(fnc_charat as", "//")
        .replace("lil_register(lil, Some(fnc_codeat as", "//");
    let table = decisions(&unpinned);
    for label in ["fnc_codeat::cp", "fnc_codeat::err"] {
        assert!(
            matches!(
                decision(&table, label),
                super::Decision::Ref { mutable: true }
            ),
            "{label}: {:?}",
            decision(&table, label)
        );
    }
    assert!(
        !matches!(
            reason(decision(&table, "fnc_codeat::argv")),
            Some(DegradeReason::CallSiteNotAdapted)
        ),
        "{:?}",
        decision(&table, "fnc_codeat::argv")
    );
}
