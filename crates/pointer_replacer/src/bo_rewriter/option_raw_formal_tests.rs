//! Wave-6o (relay 121, R738-1): an optional reference (`Option<&T>` /
//! `Option<&mut T>`) passed to a formal that stays raw needs the optional
//! form's bridge, `x.map_or(core::ptr::null(), |r| r as *const T)` (resp.
//! `null_mut()` / `*mut T`), as a plain `&T` takes `ptr::from_ref`. brotli's
//! `CopyStat` (L01¹² diagnostic, lib.rs:493854): `input_path` / `output_path`
//! are null-tested, so optional, and handed to libc's `stat` / `utime`, whose
//! formals are `*const c_char`.
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

fn decision_of(input: &str, function: &str, binding: &str) -> Decision {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
                    && subject.param_name.as_deref() == Some(binding)
            })
            .expect("corpus-derived subject")
            .1
            .clone()
    })
    .expect("fixture compiler context")
}

const FOREIGN: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, non_camel_case_types)]
#[repr(C)] pub struct stat_t { pub st_dev: u64, pub st_mode: u32 }
#[repr(C)] pub struct utimbuf { pub actime: i64 }
extern "C" {
    fn __xstat(__ver: i32, __filename: *const i8, __stat_buf: *mut stat_t) -> i32;
    fn utime(__file: *const i8, __file_times: *const utimbuf) -> i32;
}
#[inline]
unsafe extern "C" fn stat(mut __path: *const i8, mut __statbuf: *mut stat_t) -> i32 {
    return __xstat(1 as i32, __path, __statbuf);
}
unsafe extern "C" fn CopyStat(mut input_path: *const i8, mut output_path: *const i8) {
    let mut statbuf = stat_t { st_dev: 0, st_mode: 0 };
    let mut times = utimbuf { actime: 0 };
    if input_path.is_null() || output_path.is_null() { return; }
    if stat(input_path, &mut statbuf) != 0 as i32 { return; }
    utime(output_path, &mut times);
}
unsafe fn CloseFiles(mut a: *const i8, mut b: *const i8) {
    CopyStat(a, b);
}
"#;

/// brotli's shape: `stat` is glibc's LOCAL inline wrapper over `__xstat`, its
/// `__path` stays raw; the null-tested `input_path` stays optional, and the
/// call into the local raw formal carries the optional bridge as the libc
/// calls do (`option-to-raw-null-map`).
#[test]
fn wave6o_optional_reference_into_a_local_raw_formal_is_bridged() {
    assert!(verify::type_checks_str(FOREIGN));
    let d = decision_of(FOREIGN, "CopyStat", "input_path");
    assert!(matches!(d, Decision::Opt { .. }), "{d:?}");
    let output = ast_emitted_source_of(FOREIGN).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    assert!(flat.contains("input_path:Option<&i8>"), "{output}");
    assert!(flat.contains("map_or(core::ptr::null::<"), "{output}");
    assert!(verify::type_checks_str(&output), "{output}");
}

const MUT_FORMAL: &str = r#"
#![allow(dead_code, unused_mut)]
unsafe fn fill(mut p: *mut i32, mut q: *const i32) -> i32 { 0 }
"#;

/// The `*mut` direction, at the seam's own arm (a late-raw `*mut` local formal
/// has no small natural reduction): `Option<&mut i32>` at `*mut i32` takes the
/// exclusive template, `Option<&i32>` at `*mut i32` is refused shared-to-mut,
/// and either optional at `*const i32` takes the shared one.
#[test]
fn wave6o_optional_into_a_raw_formal_selects_by_the_formal_type() {
    use super::decision::seam::{Form, optional_into_raw_formal_for_tests as bridge};
    ::utils::compilation::run_compiler_on_str(MUT_FORMAL, |tcx| {
        let fill = tcx
            .hir_body_owners()
            .find(|d| tcx.item_name(d.to_def_id()).as_str() == "fill")
            .expect("fill");
        let opt = |mutable| Form::Opt {
            mutable,
            slice: false,
        };
        assert_eq!(
            bridge(tcx, fill, 0, opt(true), "q").as_deref(),
            Ok("q.as_deref_mut().map_or(core::ptr::null_mut::<i32>(), core::ptr::from_mut)")
        );
        assert_eq!(
            bridge(tcx, fill, 0, opt(false), "q").as_deref(),
            Err(&"seam-shared-to-mut")
        );
        assert_eq!(
            bridge(tcx, fill, 1, opt(true), "q").as_deref(),
            Ok("q.as_deref().map_or(core::ptr::null::<i32>(), core::ptr::from_ref)")
        );
    })
    .expect("fixture compiler context");
}
