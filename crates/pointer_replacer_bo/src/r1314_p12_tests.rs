//! **R1314-1 (relay main/372) — premise P12 `FileBufferOwnership`'s witnesses.** P01's shape,
//! reduced from 364's kept `06-enum` tree (005 `lib.rs:900–1210`): `handleErrors` prints through
//! `stderr` and aborts, `AES256_ECB` calls it, `AES256_CTR_DRBG_Update` reads its byte-buffer
//! formal `provided_data`, and the static `main_0::sm` it is handed holds `Top` and is held by
//! it. Before P12 the retained-access check holds the buffer (`evident:cycle:elem:*mut
//! _IO_FILE`, 480 rows in P01 at 251): `stderr`'s contents are what was stored through `Top`.
//! Under P12 a `FILE`'s memory is libc's own and meets no program object. The witnesses print
//! through `fprintf` (its contract row touches its `FILE` only); a program that binds a `FILE`
//! to its own memory (`setvbuf`, `fmemopen`, a write through a `FILE` field) keeps the hold,
//! and the receipt names the binding. The control keeps 005's own `ERR_print_errors_fp` and
//! OpenSSL calls: unlisted library calls, `Top` accesses, which hold the buffer under P12 too.

use std::path::{Path, PathBuf};

const P01: &str = r#"#![allow(dead_code, unused_mut, unused_unsafe, unused_assignments, unused_variables, non_camel_case_types, non_snake_case, non_upper_case_globals)]
#![feature(extern_types)]
pub type size_t = usize;
pub type __off_t = core::ffi::c_long;
pub type __off64_t = core::ffi::c_long;
#[repr(C)]
pub struct _IO_FILE {
    pub _flags: core::ffi::c_int,
    pub _IO_read_ptr: *mut core::ffi::c_char,
    pub _IO_read_end: *mut core::ffi::c_char,
    pub _IO_read_base: *mut core::ffi::c_char,
    pub _IO_write_base: *mut core::ffi::c_char,
    pub _IO_write_ptr: *mut core::ffi::c_char,
    pub _IO_write_end: *mut core::ffi::c_char,
    pub _IO_buf_base: *mut core::ffi::c_char,
    pub _IO_buf_end: *mut core::ffi::c_char,
    pub _IO_save_base: *mut core::ffi::c_char,
    pub _IO_backup_base: *mut core::ffi::c_char,
    pub _IO_save_end: *mut core::ffi::c_char,
    pub _markers: *mut _IO_marker,
    pub _chain: *mut _IO_FILE,
    pub _fileno: core::ffi::c_int,
    pub _flags2: core::ffi::c_int,
    pub _old_offset: __off_t,
    pub _cur_column: core::ffi::c_ushort,
    pub _vtable_offset: core::ffi::c_schar,
    pub _shortbuf: [core::ffi::c_char; 1],
    pub _lock: *mut core::ffi::c_void,
    pub _offset: __off64_t,
    pub _codecvt: *mut _IO_codecvt,
    pub _wide_data: *mut _IO_wide_data,
    pub _freeres_list: *mut _IO_FILE,
    pub _freeres_buf: *mut core::ffi::c_void,
    pub __pad5: size_t,
    pub _mode: core::ffi::c_int,
    pub _unused2: [core::ffi::c_char; 20],
}
pub type FILE = _IO_FILE;
pub type EVP_CIPHER = evp_cipher_st;
pub type EVP_CIPHER_CTX = evp_cipher_ctx_st;
pub type ENGINE = engine_st;
extern "C" {
    pub type _IO_marker;
    pub type _IO_codecvt;
    pub type _IO_wide_data;
    pub type evp_cipher_st;
    pub type evp_cipher_ctx_st;
    pub type engine_st;
    fn memcpy(__dest: *mut core::ffi::c_void, __src: *const core::ffi::c_void, __n: size_t)
        -> *mut core::ffi::c_void;
    static mut stderr: *mut FILE;
    fn abort() -> !;
    fn EVP_EncryptInit_ex(ctx: *mut EVP_CIPHER_CTX, cipher: *const EVP_CIPHER,
        impl_0: *mut ENGINE, key: *const core::ffi::c_uchar, iv: *const core::ffi::c_uchar)
        -> core::ffi::c_int;
    fn EVP_EncryptUpdate(ctx: *mut EVP_CIPHER_CTX, out: *mut core::ffi::c_uchar,
        outl: *mut core::ffi::c_int, in_0: *const core::ffi::c_uchar, inl: core::ffi::c_int)
        -> core::ffi::c_int;
    fn EVP_CIPHER_CTX_new() -> *mut EVP_CIPHER_CTX;
    fn EVP_CIPHER_CTX_free(c: *mut EVP_CIPHER_CTX);
    fn EVP_aes_256_ecb() -> *const EVP_CIPHER;
    fn ERR_print_errors_fp(fp: *mut FILE);
    fn fprintf(__stream: *mut FILE, __format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
    fn kat_slot() -> *mut *mut core::ffi::c_uchar;
    fn kat_buffer() -> *mut core::ffi::c_uchar;
    @EXTERN@
}
/// P01's `main_0::sm` (005's real hold: `Top` <-> `Global(main_0::sm)`): a static buffer whose
/// address is stored through an unknown library pointer and which holds an unknown library
/// pointer, so it and `Top` hold each other; it is the buffer `AES256_CTR_DRBG_Update` reads.
static mut sm: [core::ffi::c_uchar; 64] = [0; 64];
#[no_mangle]
pub unsafe extern "C" fn record_signature() {
    let mut key: [core::ffi::c_uchar; 32] = [0; 32];
    let mut v: [core::ffi::c_uchar; 16] = [0; 16];
    *kat_slot() = sm.as_mut_ptr();
    *(sm.as_mut_ptr() as *mut *mut core::ffi::c_uchar) = kat_buffer();
    AES256_CTR_DRBG_Update(sm.as_mut_ptr(), key.as_mut_ptr(), v.as_mut_ptr());
}
@HANDLE@@ECB@#[no_mangle]
pub unsafe extern "C" fn AES256_CTR_DRBG_Update(mut provided_data: *mut core::ffi::c_uchar,
    mut Key: *mut core::ffi::c_uchar, mut V: *mut core::ffi::c_uchar) {
    let mut temp: [core::ffi::c_uchar; 48] = [0; 48];
    let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
    while i < 3 as core::ffi::c_int {
        let mut j: core::ffi::c_int = 15 as core::ffi::c_int;
        while j >= 0 as core::ffi::c_int {
            if *V.offset(j as isize) as core::ffi::c_int == 0xff as core::ffi::c_int {
                *V.offset(j as isize) = 0 as core::ffi::c_uchar;
                j -= 1;
            } else {
                *V.offset(j as isize) = (*V.offset(j as isize)).wrapping_add(1);
                break;
            }
        }
        AES256_ECB(Key, V, temp.as_mut_ptr().offset((16 as core::ffi::c_int * i) as isize));
        i += 1;
    }
    if !provided_data.is_null() {
        let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
        while i_0 < 48 as core::ffi::c_int {
            temp[i_0 as usize] = (temp[i_0 as usize] as core::ffi::c_int
                ^ *provided_data.offset(i_0 as isize) as core::ffi::c_int) as core::ffi::c_uchar;
            i_0 += 1;
        }
    }
    memcpy(Key as *mut core::ffi::c_void, temp.as_mut_ptr() as *const core::ffi::c_void,
        32 as size_t);
    memcpy(V as *mut core::ffi::c_void,
        temp.as_mut_ptr().offset(32 as core::ffi::c_int as isize) as *const core::ffi::c_void,
        16 as size_t);
}
@BODY@
"#;

/// 005's `AES256_ECB`, verbatim: its OpenSSL calls are unlisted library calls, so the
/// context pointer `EVP_CIPHER_CTX_new` returns is `Top` and the calls through it meet every
/// object.
const ECB_EVP: &str = r#"#[no_mangle]
pub unsafe extern "C" fn AES256_ECB(mut key: *mut core::ffi::c_uchar,
    mut ctr: *mut core::ffi::c_uchar, mut buffer: *mut core::ffi::c_uchar) {
    let mut ctx: *mut EVP_CIPHER_CTX = 0 as *mut EVP_CIPHER_CTX;
    let mut len: core::ffi::c_int = 0;
    ctx = EVP_CIPHER_CTX_new();
    if ctx.is_null() { handleErrors(); }
    if 1 as core::ffi::c_int != EVP_EncryptInit_ex(ctx, EVP_aes_256_ecb(), 0 as *mut ENGINE,
            key, 0 as *const core::ffi::c_uchar) {
        handleErrors();
    }
    if 1 as core::ffi::c_int != EVP_EncryptUpdate(ctx, buffer, &mut len, ctr,
            16 as core::ffi::c_int) {
        handleErrors();
    }
    EVP_CIPHER_CTX_free(ctx);
}
"#;

/// `AES256_ECB` with its OpenSSL calls taken out: the `stderr` route alone.
const ECB_FILE_ROUTE: &str = r#"#[no_mangle]
pub unsafe extern "C" fn AES256_ECB(mut key: *mut core::ffi::c_uchar,
    mut ctr: *mut core::ffi::c_uchar, mut buffer: *mut core::ffi::c_uchar) {
    if *buffer.offset(0 as core::ffi::c_int as isize) as core::ffi::c_int == 0 as core::ffi::c_int {
        handleErrors();
    }
}
"#;

/// 005's `handleErrors`, verbatim: OpenSSL's `ERR_print_errors_fp` is an unlisted library
/// call, an access through `Top` whatever it is passed.
const HANDLE_OPENSSL: &str = r#"unsafe extern "C" fn handleErrors() {
    ERR_print_errors_fp(stderr);
    abort();
}
"#;

/// `handleErrors` printing through `fprintf`, whose contract row reads and writes its `FILE`
/// and nothing else: the `stderr` route alone.
const HANDLE_FILE_ROUTE: &str = r#"unsafe extern "C" fn handleErrors() {
    fprintf(stderr, b"error\n\0" as *const u8 as *const core::ffi::c_char);
    abort();
}
"#;

/// The P01 shape with `handle` as `handleErrors`, `ecb` as `AES256_ECB`, one more extern
/// declaration and one more function.
fn p01_with(handle: &str, ecb: &str, extern_decl: &str, body: &str) -> String {
    P01.replace("@HANDLE@", handle)
        .replace("@ECB@", ecb)
        .replace("@EXTERN@", extern_decl)
        .replace("@BODY@", body)
}

/// The `stderr` route alone (the witnesses' shape).
fn p01(extern_decl: &str, body: &str) -> String {
    p01_with(HANDLE_FILE_ROUTE, ECB_FILE_ROUTE, extern_decl, body)
}

/// 005's own `handleErrors` and `AES256_ECB` (the control's shape).
fn p01_openssl() -> String {
    p01_with(HANDLE_OPENSSL, ECB_EVP, "", "")
}

/// A program buffer handed to `stderr`'s `FILE` by `setvbuf`.
const SETVBUF: (&str, &str) = (
    "fn setvbuf(stream: *mut FILE, buf: *mut core::ffi::c_char, modes: core::ffi::c_int, n: size_t) -> core::ffi::c_int;",
    "#[no_mangle]\npub unsafe extern \"C\" fn buffer_stderr(mut buf: *mut core::ffi::c_char) {\n    setvbuf(stderr, buf, 0 as core::ffi::c_int, 64 as size_t);\n}\n",
);
/// A `FILE` opened over program memory by `fmemopen`.
const FMEMOPEN: (&str, &str) = (
    "fn fmemopen(buf: *mut core::ffi::c_void, size: size_t, modes: *const core::ffi::c_char) -> *mut FILE;",
    "#[no_mangle]\npub unsafe extern \"C\" fn open_over(mut buf: *mut core::ffi::c_uchar) -> *mut FILE {\n    fmemopen(buf as *mut core::ffi::c_void, 48 as size_t, b\"r\\0\" as *const u8 as *const core::ffi::c_char)\n}\n",
);
/// A program pointer written into a `FILE` field.
const FIELD_WRITE: (&str, &str) = (
    "",
    "#[no_mangle]\npub unsafe extern \"C\" fn rebuffer(mut p: *mut core::ffi::c_char) {\n    (*stderr)._IO_buf_base = p;\n}\n",
);

/// One step-7 run of `source` with the writer on: (emitted lib.rs, subjects.tsv, the P12
/// receipts).
fn run(tag: &str, source: &str) -> (String, String, String) {
    let dir = std::env::temp_dir().join(format!("crat-r1314-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.rs"), source).unwrap();
    let artifacts = dir.join("artifacts");
    let _ =
        crate::bo_pipeline::rewrite_bo_with_artifacts(&dir.join("lib.rs"), [], Some(&artifacts));
    let emitted = std::fs::read_to_string(dir.join("lib.rs")).unwrap();
    let read = |name: &str| std::fs::read_to_string(artifacts.join(name)).unwrap_or_default();
    let (subjects, p12) = (read("subjects.tsv"), read("p12_receipts.tsv"));
    if let Some(out) = std::env::var_os("R372_OUT") {
        let out = PathBuf::from(out).join(tag);
        let _ = std::fs::remove_dir_all(&out);
        std::fs::create_dir_all(&out).unwrap();
        std::fs::write(out.join("input.rs"), source).unwrap();
        std::fs::write(out.join("emitted.rs"), &emitted).unwrap();
        for entry in std::fs::read_dir(&artifacts)
            .into_iter()
            .flatten()
            .flatten()
        {
            std::fs::copy(entry.path(), out.join(entry.file_name())).unwrap();
        }
    }
    let _ = Path::new(&dir);
    std::fs::remove_dir_all(&dir).unwrap();
    (emitted, subjects, p12)
}

/// `label -> (outcome, first_hold_reason, reason_detail)` from subjects.tsv.
fn rows(subjects: &str) -> std::collections::BTreeMap<String, (String, String, String)> {
    let mut lines = subjects.lines();
    let header: Vec<&str> = lines.next().unwrap_or_default().split('\t').collect();
    let at = |name: &str| header.iter().position(|h| *h == name).unwrap();
    lines
        .map(|line| {
            let cells: Vec<&str> = line.split('\t').collect();
            (
                cells[at("label")].to_owned(),
                (
                    cells[at("outcome")].to_owned(),
                    cells[at("first_hold_reason")].to_owned(),
                    cells[at("reason_detail")].to_owned(),
                ),
            )
        })
        .collect()
}

const SUBJECT: &str = "AES256_CTR_DRBG_Update::provided_data";

#[test]
fn r1314_p12_probe() {
    for (tag, source) in [
        ("p01", p01("", "")),
        ("p01-openssl", p01_openssl()),
        ("setvbuf", p01(SETVBUF.0, SETVBUF.1)),
        ("fmemopen", p01(FMEMOPEN.0, FMEMOPEN.1)),
        ("field-write", p01(FIELD_WRITE.0, FIELD_WRITE.1)),
    ] {
        let (_, subjects, p12) = run(tag, &source);
        eprintln!("==== {tag}");
        for (label, cells) in rows(&subjects) {
            eprintln!("  {label}\t{cells:?}");
        }
        eprintln!("  p12:\n{p12}");
    }
}

/// P12 clears the `stderr` route's hold: the buffer delivers, and its receipt row and its
/// `reason_detail` name the premise.
#[test]
fn r1314_p12_the_file_route_clears_under_p12_with_its_receipt() {
    let (_, subjects, p12) = run("w-p01", &p01("", ""));
    let r = rows(&subjects);
    assert_eq!(r[SUBJECT].0, "delivered", "{r:#?}");
    assert!(r[SUBJECT].2.contains("premise:P12"), "{r:#?}");
    assert!(p12.contains("p12_scan=clean"), "{p12}");
    assert!(
        p12.lines()
            .any(|line| line.contains(SUBJECT) && line.contains("premise:P12")),
        "{p12}"
    );
}

/// 005's own `handleErrors` and `AES256_ECB` (OpenSSL's `ERR_print_errors_fp` and `EVP_*`):
/// P12 clears the `FILE` evidence, and the buffer stays held by the next one, the unlisted
/// library calls' `Top` accesses (`evident:cycle:unknown`), as on 005 itself (measured:
/// its five `FILE`-cycle formals move to `evident:cycle:unknown | AES256_ECB`); no P12
/// receipt row.
#[test]
fn r1314_p12_the_p01_shape_with_its_openssl_calls_stays_held_by_them() {
    let (_, subjects, p12) = run("w-p01-openssl", &p01_openssl());
    let r = rows(&subjects);
    assert_eq!(r[SUBJECT].0, "held", "{r:#?}");
    assert!(r[SUBJECT].1.contains("evident:cycle:unknown"), "{r:#?}");
    assert!(!r[SUBJECT].1.contains("_IO_FILE"), "{r:#?}");
    assert!(p12.contains("p12_scan=clean"), "{p12}");
    assert!(!p12.lines().any(|line| line.contains(SUBJECT)), "{p12}");
}

/// `setvbuf` hands a program buffer to a `FILE`: the hold stands, the receipt names it.
#[test]
fn r1314_p12_setvbuf_keeps_the_hold() {
    let (_, subjects, p12) = run("w-setvbuf", &p01(SETVBUF.0, SETVBUF.1));
    let r = rows(&subjects);
    assert_eq!(r[SUBJECT].0, "held", "{r:#?}");
    assert!(p12.contains("p12_scan=setvbuf"), "{p12}");
}

/// `fmemopen` binds a `FILE` to program memory: the hold stands.
#[test]
fn r1314_p12_fmemopen_keeps_the_hold() {
    let (_, subjects, p12) = run("w-fmemopen", &p01(FMEMOPEN.0, FMEMOPEN.1));
    let r = rows(&subjects);
    assert_eq!(r[SUBJECT].0, "held", "{r:#?}");
    assert!(p12.contains("p12_scan=fmemopen"), "{p12}");
}

/// A program pointer written into a `FILE` field: the hold stands.
#[test]
fn r1314_p12_a_file_field_write_keeps_the_hold() {
    let (_, subjects, p12) = run("w-field-write", &p01(FIELD_WRITE.0, FIELD_WRITE.1));
    let r = rows(&subjects);
    assert_eq!(r[SUBJECT].0, "held", "{r:#?}");
    assert!(
        p12.contains("p12_scan=write:_IO_FILE._IO_buf_base"),
        "{p12}"
    );
}
