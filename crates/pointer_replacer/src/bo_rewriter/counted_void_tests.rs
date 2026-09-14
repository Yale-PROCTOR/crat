//! Counted byte loops reduced from rs-crown/lodepng/src/lodepng.rs:352,365.

const COPY: &str = r#"
#![allow(dead_code, unused_mut)]
unsafe fn lodepng_memcpy(mut dst: *mut core::ffi::c_void,
    mut src: *const core::ffi::c_void, mut size: usize) {
    let mut i: usize = 0;
    i = 0;
    while i < size {
        *(dst as *mut i8).offset(i as isize) = *(src as *const i8).offset(i as isize);
        i = i.wrapping_add(1);
    }
}
"#;
const FILL: &str = r#"
#![allow(dead_code, unused_mut)]
unsafe fn lodepng_memset(mut dst: *mut core::ffi::c_void,
    mut value: i32, mut num: usize) {
    let mut i: usize = 0;
    i = 0;
    while i < num {
        *(dst as *mut i8).offset(i as isize) = value as i8;
        i = i.wrapping_add(1);
    }
}
"#;

fn check(input: &str, names: &[&str]) -> String {
    let rows = super::emit_tests::decisions_of(input);
    for name in names {
        assert!(
            rows.iter()
                .any(|(n, p, r)| n == name && *p && r == "<emitted>"),
            "counted parameter {name} must deliver: {rows:?}"
        );
    }
    let source = super::emit_tests::ast_emitted_source_of(input).expect("AST output");
    assert!(
        source.contains("dst: &mut [core::mem::MaybeUninit<u8>]"),
        "byte declaration: {source}"
    );
    assert!(
        !source.contains("&mut core::ffi::c_void"),
        "no thin void: {source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "output compiles: {source}"
    );
    source
}

#[test]
fn w6v_lodepng_memcpy_counted_bytes() {
    let source = check(COPY, &["dst", "src"]);
    assert!(
        source.contains("src: &[u8]"),
        "shared byte declaration: {source}"
    );
}

#[test]
fn w6v_lodepng_memset_count_is_num_not_value() {
    let source = check(FILL, &["dst"]);
    assert!(source.contains("i < num"), "count retained: {source}");
}

#[test]
fn w6v_fill_raw_caller_uses_exact_count() {
    let input = format!(
        "{FILL}\nunsafe fn fill_caller(dst: *mut core::ffi::c_void, n: usize) {{ lodepng_memset(dst, 255, n); }}"
    );
    let source = check(&input, &["dst"]);
    assert!(
        source.contains("(n) as usize"),
        "count must be n, not value=255: {source}"
    );
    assert!(
        !source.contains("FALLBACK_SLICE_EXTENT"),
        "count is known: {source}"
    );
}

#[test]
fn w6v_unbounded_and_narrowed_accesses_remain_held() {
    for input in [
        FILL.replace("i as isize", "i as u8 as isize"),
        FILL.replace("while i < num", "while i <= num"),
        FILL.replace(
            "i = i.wrapping_add(1);",
            "num = num.wrapping_add(1); i = i.wrapping_add(1);",
        ),
        FILL.replace("*(dst as", "i = num; *(dst as"),
        COPY.replace("i = i.wrapping_add(1);", "break;"),
    ] {
        let rows = super::emit_tests::decisions_of(&input);
        assert!(
            rows.iter()
                .filter(|(_, p, _)| *p)
                .all(|(_, _, r)| r != "<emitted>"),
            "unproved counted extent: {rows:?}"
        );
    }
}

#[test]
fn w6v_zero_length_bridge_never_retags_null() {
    use super::decision::{
        counted_void::{ByteElement, render_bridge},
        seam::{GlueCore, GlueSpec},
    };
    let mut spec = GlueSpec::core(GlueCore::FromRawParts, true).with_len("n");
    spec.counted_byte = Some(ByteElement::Write);
    let rendered = render_bridge(&spec, ByteElement::Write, "p").expect("typed byte bridge");
    assert!(rendered.contains("if __crat_counted_len == 0"));
    let input = format!(
        "pub unsafe fn zero(p: *mut core::ffi::c_void,n: usize) {{ let _: &mut [core::mem::MaybeUninit<u8>] = {rendered}; }}"
    );
    assert!(super::verify::type_checks_str(&input));
}

fn run_binary(source: &str) -> Vec<u8> {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("crat-w6v-runtime-{}-{id}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let input = dir.join("main.rs");
    let binary = dir.join("main");
    std::fs::write(&input, source).unwrap();
    let compiled = std::process::Command::new("rustc")
        .args(["--edition=2021", "-Awarnings"])
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "runtime build: {}\n{source}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let run = std::process::Command::new(&binary).output().unwrap();
    assert!(
        run.status.success(),
        "runtime: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    std::fs::remove_dir_all(&dir).unwrap();
    run.stdout
}

#[test]
fn w6v_emitted_fill_matches_zero_and_uninitialized_writes() {
    let helper = format!(
        "{FILL}\npub unsafe fn fill_caller(dst: *mut core::ffi::c_void, n: usize) {{ lodepng_memset(dst, 255, n); }}"
    );
    let emitted = check(&helper, &["dst"]);
    let main = r#"fn main() { unsafe {
        fill_caller(core::ptr::null_mut(),0);
        let mut bytes=[core::mem::MaybeUninit::<u8>::uninit();4];
        fill_caller(bytes.as_mut_ptr().cast(),4);
        let result=bytes.map(|b|b.assume_init());
        assert_eq!(result,[255,255,255,255]);println!("{:?}",result);
    }}"#;
    let original = run_binary(&format!("{helper}\n{main}"));
    assert_eq!(original, run_binary(&format!("{emitted}\n{main}")));
}

#[test]
fn w6v_emitted_copy_preserves_signed_byte_bits() {
    // The emitted safe helper receives distinct source/destination arrays.
    let emitted = check(COPY, &["dst", "src"]);
    let original_main = r#"fn main() { unsafe {
        let source=[0u8,127,128,255]; let mut target=[0u8;4];
        lodepng_memcpy(target.as_mut_ptr().cast(),source.as_ptr().cast(),4);
        println!("{:?}",target);
    }}"#;
    let emitted_main = r#"fn main() { unsafe {
        let source=[0u8,127,128,255]; let mut target=[core::mem::MaybeUninit::<u8>::uninit();4];
        lodepng_memcpy(&mut target,&source,4);
        let target=target.map(|b|b.assume_init());println!("{:?}",target);
    }}"#;
    assert_eq!(
        run_binary(&format!("{COPY}\n{original_main}")),
        run_binary(&format!("{emitted}\n{emitted_main}"))
    );
}

#[test]
fn w6v_addressed_count_requires_a_call_snapshot() {
    let input = format!(
        "{FILL}\nunsafe fn alias_count() {{ let mut n=8usize; let p: *mut core::ffi::c_void = &mut n as *mut usize as *mut core::ffi::c_void; lodepng_memset(p,0,n); }}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        !source.contains("dst: &mut ["),
        "addressed count must not be read again behind a new mutable view: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
}

#[test]
fn w6v_scalar_memory_read_requires_a_call_snapshot() {
    let input = format!(
        "{FILL}\nunsafe fn fill_from_value(dst: *mut core::ffi::c_void, n: usize) {{ lodepng_memset(dst, *(dst as *const i32), n); }}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        !source.contains("dst: &mut ["),
        "a scalar memory read after a new mutable view needs an argument snapshot: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
}

#[test]
fn w6v_adapter_preserves_a_count_named_like_its_pointer_temporary() {
    use super::decision::{
        counted_void::{ByteElement, render_bridge},
        seam::{GlueCore, GlueSpec},
    };
    let spec = GlueSpec::core(GlueCore::FromRawParts, true).with_len("__crat_counted_ptr");
    let rendered = render_bridge(&spec, ByteElement::Write, "p").unwrap();
    let source = format!(
        "unsafe fn length(p: *mut core::ffi::c_void, __crat_counted_ptr: usize) -> usize {{ let view: &mut [core::mem::MaybeUninit<u8>] = {rendered}; view.len() }} fn main() {{ let mut bytes=[0u8;4]; println!(\"{{}}\",unsafe{{length(bytes.as_mut_ptr().cast(),4)}}); }}"
    );
    assert_eq!(run_binary(&source), b"4\n");
}

#[test]
fn w6v_addressed_pointer_storage_requires_a_call_snapshot() {
    let input = format!(
        "{COPY}\nunsafe fn copy_pointer_storage() {{ let data=[1u8;8]; let mut src: *const core::ffi::c_void=data.as_ptr().cast(); let dst: *mut core::ffi::c_void=&raw mut src as *mut *const core::ffi::c_void as *mut core::ffi::c_void; lodepng_memcpy(dst,src,1); }}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        !source.contains("dst: &mut ["),
        "pointer argument storage must be evaluated before any new aliasing view: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
}
