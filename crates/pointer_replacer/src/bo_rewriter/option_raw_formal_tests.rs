//! Wave-6o (relay 121, R738-1): an optional reference (`Option<&T>` /
//! `Option<&mut T>`) passed to a formal that stays raw needs the optional
//! form's bridge, `x.map_or(core::ptr::null(), |r| r as *const T)` (resp.
//! `null_mut()` / `*mut T`), as a plain `&T` takes `ptr::from_ref`. brotli's
//! `CopyStat` (L01¹² diagnostic, lib.rs:493854): `input_path` / `output_path`
//! are null-tested, so optional, and handed to libc's `stat` / `utime`, whose
//! formals are `*const c_char`.
use super::{emit_tests::ast_emitted_source_of, verify};

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
/// `__path` ends raw collaterally, and the null-tested `input_path` is a THIN
/// `Option<&i8>`. A thin reference carries one element of provenance and the
/// callee reads a whole C string through it (relay 122), so no bridge is
/// built: the caller's class is held `held:thin-cstring-to-libc` (receipted),
/// `CopyStat` stays raw, and the output type-checks (no E0308).
#[test]
fn wave6o_thin_optional_into_a_local_raw_formal_is_held() {
    assert!(verify::type_checks_str(FOREIGN));
    let output = ast_emitted_source_of(FOREIGN).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    // CopyStat itself: no bridge built from the thin reference; the raw value
    // reaches `stat` (CloseFiles's `from_ref(a)` into CopyStat's raw formal is
    // the pre-existing raw-boundary `RefSharedToRawConst`, not this arm).
    assert!(
        !flat.contains("input_path.as_deref()"),
        "no cast of a thin reference: {output}"
    );
    assert!(
        flat.contains("fnCopyStat(mutinput_path:*consti8"),
        "{output}"
    );
    assert!(flat.contains("stat(input_path,&mutstatbuf)"), "{output}");
    assert!(verify::type_checks_str(&output), "{output}");
}

/// The control: the same path argument also reaches libc `chmod`, whose path
/// the fatness table already types as a C string, and is indexed once (op facts
/// govern the slice form, fatness corroborates: S3.2′-2), so `input_path` is
/// FAT (`Option<&[i8]>`) and carries its extent: the bridge into the raw formal
/// is built (`OptSliceToRaw`, `.as_ptr()`).
#[test]
fn wave6o_fat_optional_into_a_local_raw_formal_is_bridged() {
    let input = FOREIGN
        .replace(
            "    fn utime(__file: *const i8, __file_times: *const utimbuf) -> i32;\n",
            "    fn utime(__file: *const i8, __file_times: *const utimbuf) -> i32;\n    fn chmod(__file: *const i8, __mode: u32) -> i32;\n",
        )
        .replace(
            "    if stat(input_path, &mut statbuf) != 0 as i32 { return; }\n",
            "    if *input_path.offset(1 as isize) == 0 as i8 { return; }\n    if stat(input_path, &mut statbuf) != 0 as i32 { return; }\n    chmod(input_path, statbuf.st_mode);\n",
        );
    assert!(verify::type_checks_str(&input));
    let output = ast_emitted_source_of(&input).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    assert!(flat.contains("input_path:Option<&[i8]>"), "{output}");
    assert!(flat.contains("as_ptr()"), "{output}");
    assert!(verify::type_checks_str(&output), "{output}");
}

const MUT_FORMAL: &str = r#"
#![allow(dead_code, unused_mut)]
unsafe fn fill(mut p: *mut i32, mut q: *const i32, mut path: *const i8) -> i32 { 0 }
"#;

/// The arm's selection, both directions: a THIN optional at a raw formal is
/// held (`held:thin-cstring-to-libc` at a `c_char` pointee,
/// `held:thin-optional-to-raw-formal` otherwise); a FAT optional is bridged by
/// the raw boundary's slice template, `*mut` and `*const`; a shared fat
/// optional at `*mut` is refused shared-to-mut.
#[test]
fn wave6o_optional_into_a_raw_formal_selects_by_the_formal_type() {
    use super::decision::seam::{Form, optional_into_raw_formal_for_tests as bridge};
    ::utils::compilation::run_compiler_on_str(MUT_FORMAL, |tcx| {
        let fill = tcx
            .hir_body_owners()
            .find(|d| tcx.item_name(d.to_def_id()).as_str() == "fill")
            .expect("fill");
        let thin = |mutable| Form::Opt {
            mutable,
            slice: false,
        };
        let fat = |mutable| Form::Opt {
            mutable,
            slice: true,
        };
        assert_eq!(
            bridge(tcx, fill, 0, thin(true), "q").as_deref(),
            Err(&"held:thin-optional-to-raw-formal")
        );
        assert_eq!(
            bridge(tcx, fill, 2, thin(false), "q").as_deref(),
            Err(&"held:thin-cstring-to-libc")
        );
        assert_eq!(
            bridge(tcx, fill, 0, fat(true), "q").as_deref(),
            Ok("q.as_deref_mut().map_or(core::ptr::null_mut::<i32>(), |slice| slice.as_mut_ptr())")
        );
        assert_eq!(
            bridge(tcx, fill, 2, fat(false), "q").as_deref(),
            Ok("q.as_deref().map_or(core::ptr::null::<i8>(), |slice| slice.as_ptr())")
        );
        assert_eq!(
            bridge(tcx, fill, 0, fat(false), "q").as_deref(),
            Err(&"seam-shared-to-mut")
        );
    })
    .expect("fixture compiler context");
}
