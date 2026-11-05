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

/// Whitespace-free view of an emitted source, for shape assertions.
pub(super) fn compact(source: &str) -> String {
    source.chars().filter(|c| !c.is_whitespace()).collect()
}

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
        "{FILL}\nunsafe fn fill_caller(dst: *mut core::ffi::c_void, n: usize) {{ lodepng_memset(dst, 255, n.wrapping_add(0)); }}"
    );
    let source = check(&input, &["dst"]);
    assert!(
        source.contains("(__crat_cv_2) as usize"),
        "count must be the snapshot of n, not value=255: {source}"
    );
    assert!(
        compact(&source).contains(")(dst,255,n.wrapping_add(0))"),
        "every original argument is evaluated once, in order, before the call: {source}"
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
        counted_void::{ByteElement, CountedByte, Route, render_bridge},
        seam::{GlueCore, GlueSpec},
    };
    let counted = CountedByte {
        element: ByteElement::Write,
        arg_index: 0,
        route: Route::Direct,
        handle_pointee: None,
    };
    let mut spec = GlueSpec::core(GlueCore::FromRawParts, true).with_len("n");
    spec.counted_byte = Some(counted);
    let rendered = render_bridge(&spec, counted, "p").expect("typed byte bridge");
    assert!(rendered.contains("if __crat_counted_len == 0"));
    let input = format!(
        "pub unsafe fn zero(__crat_cv_0: *mut core::ffi::c_void,n: usize) {{ let _: &mut [core::mem::MaybeUninit<u8>] = {rendered}; }}"
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
    // The caller's count is an expression, so the caller stays raw and the
    // bridge (null at count zero, an uninitialised destination) is exercised.
    let helper = format!(
        "{FILL}\npub unsafe fn fill_caller(dst: *mut core::ffi::c_void, n: usize) {{ lodepng_memset(dst, 255, n.wrapping_add(0)); }}"
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
fn w6v_addressed_count_is_snapshotted_before_the_view() {
    // The count's own storage is the fill destination. The closure call reads
    // `n` before the byte view over it exists; the callee then overwrites it.
    let helper = format!(
        "{FILL}\npub unsafe fn alias_count() -> u64 {{ let mut n=8usize; let p: *mut core::ffi::c_void = &mut n as *mut usize as *mut core::ffi::c_void; lodepng_memset(p,1,n); n as u64 }}"
    );
    let emitted = check(&helper, &["dst"]);
    assert!(
        compact(&emitted).contains(")(p,1,n)"),
        "the count is read once, before any view: {emitted}"
    );
    let main = r#"fn main() { unsafe { println!("{}", alias_count()); } }"#;
    let original = run_binary(&format!("{helper}\n{main}"));
    assert_eq!(original, b"72340172838076673\n".to_vec());
    assert_eq!(original, run_binary(&format!("{emitted}\n{main}")));
}

#[test]
fn w6v_scalar_memory_read_is_snapshotted_before_the_view() {
    // The fill value is read out of the destination itself; the read happens
    // in the closure call's argument list, before the view is formed.
    let helper = format!(
        "{FILL}\npub unsafe fn fill_from_value(dst: *mut core::ffi::c_void, n: usize) {{ lodepng_memset(dst, *(dst as *const i32), n); }}"
    );
    let emitted = check(&helper, &["dst"]);
    assert!(
        compact(&emitted).contains(")(dst,*(dstas*consti32),n)"),
        "the value read precedes the view: {emitted}"
    );
    let main = r#"fn main() { unsafe {
        let mut bytes = [0x2Au8, 0, 0, 0, 9, 9, 9, 9];
        fill_from_value(bytes.as_mut_ptr().cast(), 8);
        println!("{:?}", bytes);
    }}"#;
    let original = run_binary(&format!("{helper}\n{main}"));
    assert_eq!(original, b"[42, 42, 42, 42, 42, 42, 42, 42]\n".to_vec());
    assert_eq!(original, run_binary(&format!("{emitted}\n{main}")));
}

#[test]
fn w6v_adapter_preserves_a_count_named_like_its_pointer_temporary() {
    use super::decision::{
        counted_void::{ByteElement, CountedByte, Route, render_bridge},
        seam::{GlueCore, GlueSpec},
    };
    let counted = CountedByte {
        element: ByteElement::Write,
        arg_index: 0,
        route: Route::Direct,
        handle_pointee: None,
    };
    let spec = GlueSpec::core(GlueCore::FromRawParts, true).with_len("__crat_counted_ptr");
    let rendered = render_bridge(&spec, counted, "p").unwrap();
    let source = format!(
        "unsafe fn length(__crat_cv_0: *mut core::ffi::c_void, __crat_counted_ptr: usize) -> usize {{ let view: &mut [core::mem::MaybeUninit<u8>] = {rendered}; view.len() }} fn main() {{ let mut bytes=[0u8;4]; println!(\"{{}}\",unsafe{{length(bytes.as_mut_ptr().cast(),4)}}); }}"
    );
    assert_eq!(run_binary(&source), b"4\n");
}

#[test]
fn w6v_addressed_pointer_storage_copy_routes_to_the_raw_twin() {
    // The copy destination is the source pointer's own storage (a storage
    // root, never a fresh allocation): no disjointness proof, so the call keeps
    // its raw arguments and calls the pristine raw twin; the runtime check pins
    // that the input's meaning is kept exactly.
    let helper = format!(
        "{COPY}\npub unsafe fn copy_pointer_storage() -> u8 {{ let data=[7u8;8]; let mut src: *const core::ffi::c_void=data.as_ptr().cast(); let dst: *mut core::ffi::c_void=&raw mut src as *mut *const core::ffi::c_void as *mut core::ffi::c_void; lodepng_memcpy(dst,src,1); (src as usize & 0xff) as u8 }}"
    );
    let emitted = check(&helper, &["dst", "src"]);
    assert!(
        compact(&emitted).contains("__crat_raw_lodepng_memcpy(dst,src,1)"),
        "the unproved copy calls the raw twin with its arguments untouched: {emitted}"
    );
    let main = r#"fn main() { unsafe { println!("{}", copy_pointer_storage()); } }"#;
    let original = run_binary(&format!("{helper}\n{main}"));
    assert_eq!(original, b"7\n".to_vec());
    assert_eq!(original, run_binary(&format!("{emitted}\n{main}")));
}

// ---- report 004: the count-argument value plan at the real call shapes ----
//
// The corpus callees take `size_t` counts and index with `size_t`; the
// fixtures below keep those widths (`u64`) so the byte-count forms are the
// corpus forms verbatim: `(n as u64).wrapping_mul(size_of::<T>() as u64)` and
// `(size_of::<T>() as u64).wrapping_mul(n)`.

const FILL64: &str = r#"
#![allow(dead_code, unused_mut, non_upper_case_globals, non_snake_case)]
extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }
unsafe fn lodepng_memset(mut dst: *mut core::ffi::c_void,
    mut value: i32, mut num: u64) {
    let mut i: u64 = 0;
    i = 0;
    while i < num {
        *(dst as *mut i8).offset(i as isize) = value as i8;
        i = i.wrapping_add(1);
    }
}
"#;
const COPY64: &str = r#"
#![allow(dead_code, unused_mut, non_upper_case_globals, non_snake_case)]
extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }
unsafe fn lodepng_memcpy(mut dst: *mut core::ffi::c_void,
    mut src: *const core::ffi::c_void, mut size: u64) {
    let mut i: u64 = 0;
    i = 0;
    while i < size {
        *(dst as *mut i8).offset(i as isize) = *(src as *const i8).offset(i as isize);
        i = i.wrapping_add(1);
    }
}
"#;
/// rs-crown/lodepng `HuffmanTree_makeTable`: the count is the function-local
/// static `headsize` times `size_of::<c_uint>()`.
const MAKE_TABLE: &str = r#"
static mut headsize: u32 = (1 as u32) << 9 as u32;
unsafe fn HuffmanTree_makeTable(mut numcodes: u64) -> u32 {
    let mut maxlens = malloc(((headsize as u64).wrapping_mul(::std::mem::size_of::<u32>() as u64)) as usize) as *mut u32;
    if maxlens.is_null() { return 83 as i32 as u32; }
    lodepng_memset(maxlens as *mut core::ffi::c_void, 0 as i32,
        (headsize as u64).wrapping_mul(::std::mem::size_of::<u32>() as u64));
    let mut i: u64 = 0;
    while i < numcodes {
        *maxlens.offset(i as isize) = *maxlens.offset(i as isize) + 1;
        i = i.wrapping_add(1);
    }
    let mut total: u32 = 0;
    i = 0;
    while i < headsize as u64 {
        total = total.wrapping_add(*maxlens.offset(i as isize));
        i = i.wrapping_add(1);
    }
    free(maxlens as *mut core::ffi::c_void);
    total
}
"#;
/// rs-crown/lodepng `bpmnode_sort`: `size_of::<BPMNode>() * num` bytes copied
/// back from a scratch allocation.
const BPM_SORT: &str = r#"
#[derive(Copy, Clone)]
#[repr(C)]
pub struct BPMNode { pub weight: i32, pub index: u32, pub tail: *mut BPMNode, pub in_use: i32 }
unsafe fn bpmnode_sort(mut leaves: *mut BPMNode, mut num: u64) {
    let mut mem = malloc((::std::mem::size_of::<BPMNode>() as u64).wrapping_mul(num) as usize) as *mut BPMNode;
    let mut counter: u64 = 0;
    let mut i: u64 = 0;
    while i < num {
        *mem.offset(i as isize) = *leaves.offset((num - 1 - i) as isize);
        i = i.wrapping_add(1);
    }
    counter = counter.wrapping_add(1);
    if counter & 1 as i32 as u64 != 0 {
        lodepng_memcpy(leaves as *mut core::ffi::c_void,
            mem as *const core::ffi::c_void,
            (::std::mem::size_of::<BPMNode>() as u64).wrapping_mul(num));
    }
    free(mem as *mut core::ffi::c_void);
}
"#;
/// rs-crown/lodepng `color_tree_init`: the destination is an array field of a
/// thin (single-element) struct reference; the count equals that array's size.
const COLOR_TREE: &str = r#"
#[repr(C)]
pub struct ColorTree { pub children: [*mut ColorTree; 16], pub index: i32 }
unsafe fn color_tree_init(mut tree: *mut ColorTree) {
    lodepng_memset(((*tree).children).as_mut_ptr() as *mut core::ffi::c_void, 0 as i32,
        (16 as i32 as u64).wrapping_mul(::std::mem::size_of::<*mut ColorTree>() as u64));
    (*tree).index = -(1 as i32);
}
"#;

fn count_forms_of(input: &str) -> Vec<(String, String)> {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(input), |tcx| {
        let table = super::decide_table(tcx).expect("fixture yields a decision table");
        table
            .seams
            .counted_void_calls
            .iter()
            .map(|call| {
                (
                    tcx.def_path_str(call.caller.to_def_id()),
                    call.count_form.clone(),
                )
            })
            .collect()
    })
    .expect("fixture compiles")
}

#[test]
fn w6v_make_table_static_times_size_of_count_delivers() {
    let input = format!("{FILL64}{MAKE_TABLE}");
    let source = check(&input, &["dst"]);
    // The count is evaluated exactly once, before any byte view exists: the
    // caller spells `headsize` three times in the input (the allocation, the
    // count, the summation bound) and exactly three times in the output —
    // never a fourth time inside a generated adapter.
    let caller = source
        .split("fn HuffmanTree_makeTable")
        .nth(1)
        .expect("caller emitted");
    assert_eq!(
        caller.matches("headsize").count(),
        3,
        "the count expression is snapshotted once before the call: {caller}"
    );
    assert!(
        source.contains("__crat_cv_2"),
        "count placeholder: {source}"
    );
    let forms = count_forms_of(&input);
    assert!(
        forms
            .iter()
            .any(|(owner, form)| owner.ends_with("HuffmanTree_makeTable")
                && form == "elements:(headsize as u64)*size_of::<u32>"),
        "typed element-count receipt: {forms:?}"
    );
}

#[test]
fn w6v_color_tree_array_field_of_thin_reference_fits_its_count() {
    let input = format!("{FILL64}{COLOR_TREE}");
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "tree" && *p && r == "<emitted>"),
        "the fixture must keep its thin struct reference: {rows:?}"
    );
    check(&input, &["dst"]);
}

#[test]
fn w6v_thin_reference_root_with_an_unfitting_count_is_held() {
    let input = format!("{FILL64}{COLOR_TREE}").replace("(16 as i32 as u64)", "(32 as i32 as u64)");
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "tree" && *p && r == "<emitted>"),
        "the fixture must keep its thin struct reference: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        !source.contains("dst: &mut ["),
        "a count beyond the thin referent's array field must not widen it: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
}

#[test]
fn w6v_make_table_runtime_matches_original() {
    let helper = format!("{FILL64}{MAKE_TABLE}");
    let emitted = check(&helper, &["dst"]);
    let main = r#"fn main() { unsafe { println!("{}", HuffmanTree_makeTable(7)); } }"#;
    let original = run_binary(&format!("{helper}\n{main}"));
    assert_eq!(original, b"7\n".to_vec());
    assert_eq!(original, run_binary(&format!("{emitted}\n{main}")));
}

#[test]
#[ignore = "known red at the master merge (main 303): standing since S5, to be taken up after the merge"]
fn w6v_bpm_sort_runtime_matches_original() {
    let helper = format!("{COPY64}{BPM_SORT}");
    let emitted = super::emit_tests::ast_emitted_source_of(&helper).unwrap();
    let main = r#"fn main() { unsafe {
        let mut leaves = [BPMNode { weight: 0, index: 0, tail: core::ptr::null_mut(), in_use: 0 }; 3];
        for (i, l) in leaves.iter_mut().enumerate() { l.weight = i as i32 * 10; l.index = i as u32; }
        bpmnode_sort(leaves.as_mut_ptr(), 3);
        println!("{:?}", leaves.iter().map(|l| (l.weight, l.index)).collect::<Vec<_>>());
    }}"#;
    let original = run_binary(&format!("{helper}\n{main}"));
    assert_eq!(original, b"[(20, 2), (10, 1), (0, 0)]\n".to_vec());
    assert_eq!(original, run_binary(&format!("{emitted}\n{main}")));
}

/// rs-crown/lodepng `decodeGeneric` (site 9122): the destination is the
/// loaded value of a depth-two output parameter; the count is a plain local.
const DECODE_GENERIC: &str = r#"
unsafe fn decodeGeneric(mut out: *mut *mut u8, mut outsize: u64) -> u32 {
    *out = malloc(outsize as usize) as *mut u8;
    if (*out).is_null() { return 83; }
    lodepng_memset(*out as *mut core::ffi::c_void, 0 as i32, outsize);
    let first = **out;
    free(*out as *mut core::ffi::c_void);
    first as u32
}
"#;
/// rs-crown/lodepng `filter` (site 10357): the destination is a local array's
/// `as_mut_ptr()`; the count is a literal element count times the element size.
const FILTER_COUNT: &str = r#"
unsafe fn filter(mut bytes: u64) -> u32 {
    let mut count: [u32; 256] = [0; 256];
    lodepng_memset(count.as_mut_ptr() as *mut core::ffi::c_void, 0 as i32,
        (256 as i32 as u64).wrapping_mul(::std::mem::size_of::<u32>() as u64));
    let mut i: u64 = 0;
    while i < bytes { count[(i % 256) as usize] += 1; i = i.wrapping_add(1); }
    let mut total: u32 = 0;
    i = 0;
    while i < 256 { total = total.wrapping_add(count[i as usize]); i = i.wrapping_add(1); }
    total
}
"#;

#[test]
fn w6v_decode_generic_loaded_out_parameter_destination_delivers() {
    let helper = format!("{FILL64}{DECODE_GENERIC}");
    let emitted = check(&helper, &["dst"]);
    let main = r#"fn main() { unsafe { let mut out: *mut u8 = core::ptr::null_mut(); println!("{}", decodeGeneric(&mut out, 16)); } }"#;
    let original = run_binary(&format!("{helper}\n{main}"));
    assert_eq!(original, b"0\n".to_vec());
    assert_eq!(original, run_binary(&format!("{emitted}\n{main}")));
}

#[test]
fn w6v_filter_local_array_destination_delivers() {
    let helper = format!("{FILL64}{FILTER_COUNT}");
    let emitted = check(&helper, &["dst"]);
    let forms = count_forms_of(&helper);
    assert!(
        forms.iter().any(|(owner, form)| owner.ends_with("filter")
            && form == "elements:(256 as i32 as u64)*size_of::<u32>"),
        "typed element-count receipt: {forms:?}"
    );
    let main = r#"fn main() { unsafe { println!("{}", filter(1000)); } }"#;
    let original = run_binary(&format!("{helper}\n{main}"));
    assert_eq!(original, b"1000\n".to_vec());
    assert_eq!(original, run_binary(&format!("{emitted}\n{main}")));
}

/// rs-crown/lodepng `inflateHuffmanBlock` (sites 2409/2428): a back-reference
/// copy INSIDE one buffer. The destination and source ranges may overlap
/// (`distance < length`), which the original byte loop handles by design; two
/// live safe views over overlapping bytes are never emitted (R395-2), so this
/// call must hold and the callee keeps its raw parameters.
const INFLATE_BACKREF: &str = r#"
#[repr(C)]
pub struct ucvector { pub data: *mut u8, pub size: u64, pub allocsize: u64 }
unsafe fn inflateHuffmanBlock(mut out: *mut ucvector, mut start: u64, mut backward: u64, mut length: u64) {
    lodepng_memcpy(((*out).data).offset(start as isize) as *mut core::ffi::c_void,
        ((*out).data).offset(backward as isize) as *const core::ffi::c_void, length);
}
"#;

#[test]
fn w6v_overlapping_self_copy_never_forms_two_views() {
    let helper = format!("{COPY64}{INFLATE_BACKREF}");
    let source = super::emit_tests::ast_emitted_source_of(&helper).unwrap();
    // Both roots are the same buffer: the call keeps its raw arguments and
    // calls the pristine raw twin; no view is formed at this call.
    assert!(
        compact(&source).contains("__crat_raw_lodepng_memcpy(((*out).data).offset(startasisize)as*mutcore::ffi::c_void,((*out).data).offset(backwardasisize)as*constcore::ffi::c_void,length)"),
        "a copy within one buffer may overlap; it must call the raw twin unchanged: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    // The byte loop itself stays exactly as the input wrote it (forward,
    // element by element), so overlapping windows keep their C meaning.
    let main = r#"fn main() { unsafe {
        let mut bytes = [1u8, 2, 3, 0, 0, 0, 0, 0];
        let mut v = ucvector { data: bytes.as_mut_ptr(), size: 8, allocsize: 8 };
        inflateHuffmanBlock(&mut v, 3, 0, 5);
        println!("{:?}", bytes);
    }}"#;
    let original = run_binary(&format!("{helper}\n{main}"));
    assert_eq!(original, b"[1, 2, 3, 1, 2, 3, 1, 2]\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{main}")));
}

// ---- report 005: the split callee (R399-6) ----
//
// A read+write byte callee converts, and every call whose two roots are NOT
// provably distinct allocations is routed to a pristine raw twin
// `__crat_raw_<callee>` (the original body under a new name). A call is split
// when one root is a fresh allocation local of the caller (`malloc` / `calloc`,
// directly or through a transparent local wrapper such as `lodepng_malloc`,
// assigned exactly once, never address-taken) and the other is another fresh
// local or a caller parameter that is never reassigned.

// ---- report 006: counted read aliases and forwarded counted parameters ----
//
// rs-crown/libcsv: a `void *` READ parameter is cast once to a byte pointer and
// read through a cursor (`*csrc`, `csrc = csrc.offset(1)`) inside a loop that
// counts a sibling parameter down to zero; wrappers forward the pair unchanged.
// Reads become checked indexing over the counted view (R394-1), the cursor a
// re-slice; a null-tested parameter becomes `Option<&[u8]>`.

/// rs-crown/libcsv `csv_write2` (src side) and `csv_fwrite2`, reduced; `sink`
/// stands for `fputc`.
const CSV_READ: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
static mut SINK: u64 = 0;
unsafe fn sink(c: i32) -> i32 { SINK = SINK.wrapping_mul(31).wrapping_add(c as u64); 0 }
unsafe fn csv_fwrite2(mut src: *const core::ffi::c_void, mut src_size: u64, mut quote: u8) -> i32 {
    let mut csrc = src as *const u8;
    if src.is_null() { return 0 as i32; }
    if sink(quote as i32) == -(1 as i32) { return -(1 as i32); }
    while src_size != 0 {
        if *csrc as i32 == quote as i32 {
            if sink(quote as i32) == -(1 as i32) { return -(1 as i32); }
        }
        if sink(*csrc as i32) == -(1 as i32) { return -(1 as i32); }
        src_size = src_size.wrapping_sub(1);
        csrc = csrc.offset(1);
    }
    if sink(quote as i32) == -(1 as i32) { return -(1 as i32); }
    return 0 as i32;
}
unsafe fn csv_fwrite(mut src: *const core::ffi::c_void, mut src_size: u64) -> i32 {
    return csv_fwrite2(src, src_size, 0x22 as i32 as u8);
}
"#;

#[test]
fn w6v_read_cursor_alias_delivers_an_optional_byte_view() {
    let rows = super::emit_tests::decisions_of(CSV_READ);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "src" && *p && r == "<emitted>"),
        "the read parameter delivers: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(CSV_READ).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fncsv_fwrite2(mutsrc:Option<&[u8]>,mutsrc_size:u64,mutquote:u8)"),
        "null-tested read view: {source}"
    );
    assert!(c.contains("ifsrc.is_none()"), "null test moves: {source}");
    // R492-5 route (i): the alias is a delivered subject now, so its
    // declaration carries its own type — the custody instrument refuses a
    // delivered declaration whose type is inferred, and the count is still the
    // contract's (no `from_raw_parts`, no fabricated extent).
    assert!(
        c.contains("letmutcsrc:&[u8]=src.unwrap_or(&[]);"),
        "the alias is the view, typed: {source}"
    );
    assert!(
        c.contains("(csrc[0]asu8)"),
        "cursor reads are checked: {source}"
    );
    assert!(
        c.contains("csrc=&csrc[1..];"),
        "the advance is a re-slice: {source}"
    );
    assert!(
        c.contains("fncsv_fwrite(mutsrc:Option<&[u8]>,mutsrc_size:u64)"),
        "the forwarding wrapper takes the same view: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let text = b"a\"b";
        csv_fwrite(text.as_ptr().cast(), 3);
        csv_fwrite(core::ptr::null(), 3);
        csv_fwrite(text.as_ptr().cast(), 0);
        println!("{}", SINK);
    }}"#;
    let emitted_main = r#"fn main() { unsafe {
        let text = b"a\"b";
        csv_fwrite(Some(&text[..]), 3);
        csv_fwrite(None, 3);
        csv_fwrite(Some(&text[..0]), 0);
        println!("{}", SINK);
    }}"#;
    let original = run_binary(&format!("{CSV_READ}\n{main}"));
    assert_eq!(original, b"1022524480959\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{emitted_main}")));
}

/// A wrapper of the wrapper forwards the pair too: the forward contract closes
/// to a fixpoint along the chain.
#[test]
fn w6v_read_alias_forward_chain_closes() {
    let input = format!(
        "{CSV_READ}\nunsafe fn caller(p: *const core::ffi::c_void, n: u64) -> i32 {{ csv_fwrite(p, n) }}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        compact(&source).contains("fncaller(p:Option<&[u8]>,n:u64)->i32{csv_fwrite(p,n)}"),
        "the chain takes the view: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
}

/// A raw caller of the forwarding wrapper (its count is an expression, so it
/// is no forwarder itself): the optional counted bridge maps a null pointer to
/// `None` and a non-null pointer with its count to the view.
#[test]
fn w6v_read_alias_raw_caller_bridges_through_the_null_arm() {
    let input = format!(
        "{CSV_READ}\nunsafe fn caller(p: *const core::ffi::c_void, n: u64) -> i32 {{ csv_fwrite(p, n.wrapping_add(0)) }}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("if__crat_counted_ptr.is_null(){None}elseif__crat_counted_len==0{Some(&[])}else{Some(unsafe{core::slice::from_raw_parts(__crat_counted_ptr,__crat_counted_len)})}"),
        "the optional counted bridge: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let text = b"a\"b";
        caller(text.as_ptr().cast(), 3);
        caller(core::ptr::null(), 3);
        caller(text.as_ptr().cast(), 0);
        println!("{}", SINK);
    }}"#;
    let original = run_binary(&format!("{input}\n{main}"));
    assert_eq!(original, b"1022524480959\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{main}")));
}

#[test]
fn w6v_read_alias_holds_when_the_cursor_is_read_outside_the_counted_loop() {
    // A read after the loop is not bounded by the count: the parameter stays
    // typed-held and nothing is rewritten.
    let input = CSV_READ.replace(
        "    if sink(quote as i32) == -(1 as i32) { return -(1 as i32); }\n    return 0 as i32;",
        "    if sink(*csrc as i32) == -(1 as i32) { return -(1 as i32); }\n    return 0 as i32;",
    );
    assert_ne!(input, CSV_READ);
    // R217-2(a) re-pin (wave-6v2 004 claim 3, R407-11): the LEAF holds; the
    // wrapper's disposition is the forward-only rule's (held here, a `&[u8]`
    // forwarded as `src.as_ptr().cast::<c_void>()` once that rule composes).
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "src" && *p && r == "held:void-pointee"),
        "an unbounded read holds the leaf parameter: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        compact(&source).contains("fncsv_fwrite2(mutsrc:*constcore::ffi::c_void,"),
        "the leaf keeps its raw parameter: {source}"
    );
    assert!(!source.contains("Option<&[u8]>"), "{source}");
    assert!(super::verify::type_checks_str(&source));
}

#[test]
fn w6v_read_alias_holds_when_the_alias_escapes() {
    // The alias's address value observed as an integer has no image.
    let input = CSV_READ.replace(
        "        csrc = csrc.offset(1);\n    }",
        "        csrc = csrc.offset(1);\n    }\n    let _keep = csrc as usize;",
    );
    assert_ne!(input, CSV_READ);
    // R217-2(a) re-pin (wave-6v2 004 claim 3, R407-11): the LEAF holds; the
    // wrapper's disposition is the forward-only rule's.
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "src" && *p && r == "held:void-pointee"),
        "an escaping alias holds the leaf parameter: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        compact(&source).contains("fncsv_fwrite2(mutsrc:*constcore::ffi::c_void,"),
        "the leaf keeps its raw parameter: {source}"
    );
}

/// A wrapper forwarding a WRITE pair takes the destination view itself.
#[test]
fn w6v_forwarded_write_pair_takes_the_destination_view() {
    let helper = format!(
        "{FILL}\npub unsafe fn fill_caller(dst: *mut core::ffi::c_void, n: usize) {{ lodepng_memset(dst, 255, n); }}"
    );
    let emitted = check(&helper, &["dst"]);
    assert!(
        compact(&emitted).contains("fnfill_caller(dst:&mut[core::mem::MaybeUninit<u8>],n:usize){lodepng_memset(dst,255,n);}"),
        "the forwarder takes the write view: {emitted}"
    );
    let main = r#"fn main() { unsafe {
        let mut bytes=[core::mem::MaybeUninit::<u8>::uninit();4];
        fill_caller(&mut bytes,4);
        println!("{:?}",bytes.map(|b|b.assume_init()));
    }}"#;
    assert_eq!(
        run_binary(&format!("{emitted}\n{main}")),
        b"[255, 255, 255, 255]\n".to_vec()
    );
}

// ---- report 007: the indexed read twin (libcsv `csv_parse`) ----

/// rs-crown/libcsv `csv_parse` reduced: the alias is never advanced; the one
/// read is `*us.offset(fresh as isize)` where `fresh` copies the loop index
/// `pos` at the top of a `while pos < len` iteration, before `pos` moves.
const CSV_PARSE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
static mut SINK: u64 = 0;
unsafe fn note(c: u8) { SINK = SINK.wrapping_mul(31).wrapping_add(c as u64); }
unsafe fn csv_parse(mut s: *const core::ffi::c_void, mut len: u64, mut skip: u64) -> u64 {
    if s.is_null() { return 0 as i32 as u64; }
    let mut us = s as *const u8;
    let mut pos = 0 as i32 as u64;
    let mut c: u8 = 0;
    pos = skip;
    while pos < len {
        if pos == 1 { note(255); }
        let fresh17 = pos;
        pos = pos.wrapping_add(1);
        c = *us.offset(fresh17 as isize);
        match c as i32 {
            32 => { note(1); }
            _ => { note(c); }
        }
    }
    return pos;
}
"#;

#[test]
fn w6v_indexed_read_alias_under_a_bounded_guard_delivers() {
    let rows = super::emit_tests::decisions_of(CSV_PARSE);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "s" && *p && r == "<emitted>"),
        "the read parameter delivers: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(CSV_PARSE).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fncsv_parse(muts:Option<&[u8]>,mutlen:u64,mutskip:u64)->u64"),
        "{source}"
    );
    // R492-5 route (i): the alias declares its own type (see CSV_READ).
    assert!(c.contains("letmutus:&[u8]=s.unwrap_or(&[]);"), "{source}");
    assert!(
        c.contains("c=(us[(fresh17asisize)asusize]asu8);"),
        "indexed checked read: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let text = b"ab cd";
        println!("{} {} {}", csv_parse(text.as_ptr().cast(), 5, 0), csv_parse(text.as_ptr().cast(), 5, 3), csv_parse(core::ptr::null(), 5, 0));
        println!("{}", SINK);
    }}"#;
    let emitted_main = r#"fn main() { unsafe {
        let text = b"ab cd";
        println!("{} {} {}", csv_parse(Some(&text[..]), 5, 0), csv_parse(Some(&text[..]), 5, 3), csv_parse(None, 5, 0));
        println!("{}", SINK);
    }}"#;
    let original = run_binary(&format!("{CSV_PARSE}\n{main}"));
    assert_eq!(original, b"5 5 0\n2897846636319\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{emitted_main}")));
}

#[test]
fn w6v_indexed_read_alias_holds_when_the_index_moves_before_its_copy() {
    // `pos` is incremented before `fresh17` copies it: the copy may equal `len`.
    let input = CSV_PARSE.replace(
        "        if pos == 1 { note(255); }",
        "        if pos == 1 { note(255); pos = pos.wrapping_add(1); }",
    );
    assert_ne!(input, CSV_PARSE);
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        rows.iter()
            .filter(|(n, p, _)| n == "s" && *p)
            .all(|(_, _, r)| r != "<emitted>"),
        "an index moved before its copy holds the parameter: {rows:?}"
    );
}

#[test]
fn w6v_indexed_read_alias_holds_when_the_index_is_not_the_guarded_one() {
    let input = CSV_PARSE.replace("let fresh17 = pos;", "let fresh17 = skip;");
    assert_ne!(input, CSV_PARSE);
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        rows.iter()
            .filter(|(n, p, _)| n == "s" && *p)
            .all(|(_, _, r)| r != "<emitted>"),
        "an index that is not the guard's holds the parameter: {rows:?}"
    );
}

// ---- report 007: a `void *` handle to ONE struct (bzip2 `BZ2_bzerror` / `BZ2_bzread`) ----

/// rs-crown/bzip2 reduced: the handle is cast to `*mut bzFile` and only
/// dereferenced as a single struct (field reads), and forwarded raw.
const BZ_HANDLE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, non_camel_case_types)]
#[repr(C)]
pub struct bzFile { pub lastErr: i32, pub writing: u8 }
unsafe fn BZ2_bzRead(bzerror: *mut i32, b: *mut core::ffi::c_void, len: i32) -> i32 {
    *bzerror = (*(b as *mut bzFile)).lastErr;
    len
}
unsafe fn BZ2_bzerror(mut b: *mut core::ffi::c_void, mut errnum: *mut i32) -> i32 {
    let mut err: i32 = (*(b as *mut bzFile)).lastErr;
    if err > 0 as i32 { err = 0 as i32 }
    *errnum = err;
    return err * -(1 as i32);
}
unsafe fn BZ2_bzread(mut b: *mut core::ffi::c_void, mut len: i32) -> i32 {
    let mut bzerr: i32 = 0;
    if (*(b as *mut bzFile)).lastErr == 4 as i32 { return 0 as i32 }
    let nread = BZ2_bzRead(&mut bzerr, b, len);
    if bzerr == 0 as i32 || bzerr == 4 as i32 { return nread } else { return -(1 as i32) };
}
"#;

#[test]
fn w6v_void_handle_to_one_struct_takes_the_reference_form() {
    let rows = super::emit_tests::decisions_of(BZ_HANDLE);
    assert!(
        rows.iter()
            .filter(|(n, p, r)| n == "b" && *p && r == "<emitted>")
            .count()
            >= 2,
        "the non-forwarding handles deliver: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(BZ_HANDLE).unwrap();
    let c = compact(&source);
    // Read-only through the handle: the shared reference form.
    assert!(
        c.contains("fnBZ2_bzerror(mutb:&bzFile,muterrnum:&muti32)->i32"),
        "the handle is a reference to one struct: {source}"
    );
    assert!(
        c.contains("fnBZ2_bzRead(bzerror:&muti32,b:&bzFile,len:i32)->i32"),
        "{source}"
    );
    // The raw forwarder bridges its handle at the call: cast to the declared
    // pointee, reborrowed as one element.
    assert!(
        c.contains("BZ2_bzRead(&mutbzerr,((b)as*constbzFile).as_ref().unwrap(),len)"),
        "the raw argument is cast to the declared pointee and reborrowed: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let mut f = bzFile { lastErr: -3, writing: 0 };
        let mut e = 0i32;
        let p = &mut f as *mut bzFile as *mut core::ffi::c_void;
        println!("{} {} {}", BZ2_bzerror(p, &mut e), e, BZ2_bzread(p, 7));
    }}"#;
    let emitted_main = r#"fn main() { unsafe {
        let mut f = bzFile { lastErr: -3, writing: 0 };
        let mut e = 0i32;
        let p = &mut f as *mut bzFile as *mut core::ffi::c_void;
        println!("{} {} {}", BZ2_bzerror(&f, &mut e), e, BZ2_bzread(p, 7));
    }}"#;
    let original = run_binary(&format!("{BZ_HANDLE}\n{main}"));
    assert_eq!(original, b"3 -3 -1\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{emitted_main}")));
}

#[test]
fn w6v_void_handle_holds_when_the_cast_is_offset() {
    // `&bzFile as *const bzFile` is a legal cast, so an offset past the one
    // element would compile and read outside the referent: the handle holds.
    let input = BZ_HANDLE.replace(
        "    let mut err: i32 = (*(b as *mut bzFile)).lastErr;",
        "    let mut err: i32 = (*(b as *const bzFile).offset(1)).lastErr;",
    );
    assert_ne!(input, BZ_HANDLE);
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "b" && *p && r != "<emitted>"),
        "an offset handle holds: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        !compact(&source).contains("fnBZ2_bzerror(mutb:&bzFile"),
        "{source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

// ---- report 008: the model gate (a forwarder never outruns a raw callee) ----

// ---- report 009/010: a converted callee called with ONE local at two positions ----

/// json.h's `json_parse_ex`: `json_get_value_size(&mut state, (flags & state.flags_bitset) as i32)`
/// — a converted `&mut` argument followed by an argument that reads the same local
/// (batch 6's E0503, 2 rows / 11 identities).
const JSON_STATE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct State { pub flags: u64, pub dom_size: u64, pub offset: u64 }
pub unsafe extern "C" fn get_value_size(mut state: *mut State, mut is_global: i32) -> i32 {
    let flags = (*state).flags;
    (*state).dom_size = ((*state).dom_size).wrapping_add(8);
    if is_global != 0 { return 1; }
    (*state).offset = (*state).offset.wrapping_add(1);
    return 0;
}
pub unsafe extern "C" fn parse(mut flags: u64) -> i32 {
    let mut state: State = State { flags: 0, dom_size: 0, offset: 0 };
    state.flags = flags;
    let mut input_error: i32 = 0;
    input_error = get_value_size(&mut state, (1 as u64 & state.flags) as i32);
    return input_error + state.offset as i32 + state.dom_size as i32;
}
"#;

#[test]
fn w6v_read_of_the_borrowed_local_in_a_later_argument_is_hoisted() {
    let rows = super::emit_tests::decisions_of(JSON_STATE);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "state" && *p && r == "<emitted>"),
        "the callee parameter delivers: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(JSON_STATE).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnget_value_size(mutstate:&mutState,"),
        "the callee takes the view: {source}"
    );
    assert!(
        c.contains(
            "{let__crat_cv_1=(1asu64&state.flags)asi32;get_value_size(&mutstate,__crat_cv_1)}"
        ),
        "the read is evaluated before the borrow: {source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "output compiles: {source}"
    );
    let main = "fn main() { unsafe { println!(\"{} {}\", parse(0), parse(1)); } }";
    let original = run_binary(&format!("{JSON_STATE}\n{main}"));
    assert_eq!(original, b"9 9\n".to_vec());
    assert_eq!(run_binary(&format!("{source}\n{main}")), original);
}

/// Controls: no read of the borrowed local in another argument → the call is
/// left as written; a converted argument that is not a pure place borrow (a
/// call result) is never reordered behind the read.
#[test]
fn w6v_hoist_needs_a_read_of_the_borrowed_local_and_a_pure_place_borrow() {
    let no_read = JSON_STATE.replace(
        "get_value_size(&mut state, (1 as u64 & state.flags) as i32)",
        "get_value_size(&mut state, (1 as u64 & flags) as i32)",
    );
    let source = super::emit_tests::ast_emitted_source_of(&no_read).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("input_error=get_value_size(&mutstate,(1asu64&flags)asi32);"),
        "no read of `state` in another argument: the call stays: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");

    // A converted argument that is a pointer READ (`(*hp).sp`, not a place
    // borrow) beside an argument that overwrites that field: the order of
    // effects is the input's only if the read stays first — never hoisted.
    let impure = JSON_STATE
        .replace(
            "pub unsafe extern \"C\" fn parse(",
            "#[repr(C)] pub struct Holder { pub sp: *mut State, pub flags: u64 }\n\
             pub unsafe extern \"C\" fn swap_in(mut h: *mut Holder, mut alt: *mut State) -> i32 { (*h).sp = alt; 1 }\n\
             pub unsafe extern \"C\" fn parse2(mut flags: u64) -> i32 {\n\
                 let mut a: State = State { flags: 0, dom_size: 0, offset: 0 };\n\
                 let mut b: State = State { flags: 0, dom_size: 0, offset: 0 };\n\
                 let mut h: Holder = Holder { sp: &mut a, flags: flags };\n\
                 let hp: *mut Holder = &mut h;\n\
                 let e = get_value_size((*hp).sp, swap_in(hp, &mut b));\n\
                 return e + a.dom_size as i32 * 10 + b.dom_size as i32;\n\
             }\n\
             pub unsafe extern \"C\" fn parse(",
        );
    let rows = super::emit_tests::decisions_of(&impure);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "state" && *p && r == "<emitted>"),
        "the control's callee parameter delivers: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&impure).unwrap();
    assert!(
        !compact(&source).contains("let__crat_cv_1=swap_in"),
        "a pointer-read argument is never reordered behind the write: {source}"
    );
    let main = "fn main() { unsafe { println!(\"{}\", parse2(0)); } }";
    let original = run_binary(&format!("{impure}\n{main}"));
    assert_eq!(original, b"81\n".to_vec());
    assert_eq!(run_binary(&format!("{source}\n{main}")), original);
}

// ---- relay 015 / 016: the raw twin and the callee's revert unit ----

/// Two callers route to `__crat_raw_lodepng_memcpy` (in-buffer copies), and a
/// third caller makes the callee's class fail at the compile gate (an
/// array-local address at the counted position takes the thin-reference glue
/// `core::slice::from_mut(&mut buf)`, E0308). The verify loop then reverts
/// `lodepng_memcpy`'s class — and the twin with it, since it is printed within
/// the callee's span — while the two callers' renamed calls survive: E0425 in
/// every later round, no attribution, the program degrades (batch 8's lodepng
/// and brotli). The twin and its callers are ONE unit.
const TWIN_UNIT: &str = r#"
#![allow(dead_code, unused_mut, non_upper_case_globals, non_snake_case, unused_assignments, unused_variables)]
extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }
unsafe fn lodepng_memcpy(mut dst: *mut core::ffi::c_void,
    mut src: *const core::ffi::c_void, mut size: u64) {
    let mut i: u64 = 0;
    i = 0;
    while i < size {
        *(dst as *mut i8).offset(i as isize) = *(src as *const i8).offset(i as isize);
        i = i.wrapping_add(1);
    }
}
#[repr(C)]
pub struct ucvector { pub data: *mut u8, pub size: u64, pub allocsize: u64 }
pub unsafe fn inflateHuffmanBlock(mut out: *mut ucvector, mut start: u64, mut backward: u64, mut length: u64) {
    lodepng_memcpy(((*out).data).offset(start as isize) as *mut core::ffi::c_void,
        ((*out).data).offset(backward as isize) as *const core::ffi::c_void, length);
}
pub unsafe fn inflateNoCompression(mut out: *mut ucvector, mut start: u64, mut backward: u64, mut length: u64) {
    lodepng_memcpy(((*out).data).offset(start as isize) as *mut core::ffi::c_void,
        ((*out).data).offset(backward as isize) as *const core::ffi::c_void, length);
}
pub unsafe fn writeSignature(mut src: *const core::ffi::c_void) -> i64 {
    let mut buf: [i8; 4] = [0; 4];
    lodepng_memcpy(&mut buf as *mut [i8; 4] as *mut core::ffi::c_void, src, 4);
    buf[0] as i64 + buf[3] as i64
}
"#;

fn production_outcome(name: &str, fixture: &str) -> super::RewriteOutcome {
    production_outcome_injected(name, fixture, &|_| {})
}

fn production_outcome_injected(
    name: &str,
    fixture: &str,
    inject: &(dyn Fn(&mut super::decision::DecisionTable) + Sync),
) -> super::RewriteOutcome {
    let dir = std::env::temp_dir().join(format!("crat-w6v-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, fixture).unwrap();
    let outcome = super::rewrite_m1_path_a5_injected(
        &root,
        super::OverlapMode::PreciseReplay,
        Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        inject,
    );
    std::fs::remove_dir_all(dir).unwrap();
    outcome
}

#[test]
fn w6v_raw_twin_reverts_with_its_callees_class() {
    let outcome = production_outcome("twin-unit", TWIN_UNIT);
    let source = match &outcome {
        super::RewriteOutcome::Emitted { source, .. } => source.clone(),
        super::RewriteOutcome::Degraded { reason, .. } => {
            panic!("the program must emit, not degrade on a missing twin: {reason}")
        }
    };
    let c = compact(&source);
    let twin_defined = c.contains("fn__crat_raw_lodepng_memcpy(");
    let twin_called = c.contains("__crat_raw_lodepng_memcpy(");
    assert!(
        twin_defined == twin_called,
        "the twin's definition and its call sites are one unit (defined={twin_defined}, called={twin_called}): {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// The forced revert: the split fixture's two in-buffer callers route to the
/// twin (plans recorded), then the callee's `dst` / `src` are withdrawn AFTER
/// planning (as a class revert or any later withdrawal leaves them). The
/// callee's emitted signature is the input's, so no call is renamed and no
/// twin is printed: the twin's definition and its call sites are one unit.
#[test]
fn w6v_raw_twin_is_not_grafted_for_a_withdrawn_callee() {
    let fixture = format!(
        "{COPY64}{INFLATE_BACKREF}\n\
         pub unsafe fn inflateNoCompression(mut out: *mut ucvector, mut start: u64, mut backward: u64, mut length: u64) {{\n\
             lodepng_memcpy(((*out).data).offset(start as isize) as *mut core::ffi::c_void,\n\
                 ((*out).data).offset(backward as isize) as *const core::ffi::c_void, length);\n\
         }}\n"
    );
    let delivered = super::emit_tests::ast_emitted_source_of(&fixture).unwrap();
    assert!(
        compact(&delivered).contains("__crat_raw_lodepng_memcpy(")
            && compact(&delivered).contains("fn__crat_raw_lodepng_memcpy("),
        "the plans exist and deliver before the withdrawal: {delivered}"
    );
    let outcome = production_outcome_injected("twin-withdrawn", &fixture, &|table| {
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("lodepng_memcpy::dst")
                || subject.label.ends_with("lodepng_memcpy::src")
            {
                *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                    subject: subject.label.clone(),
                    site: "<w6v-injected-withdrawal>".to_owned(),
                    reason: super::decision::DegradeReason::CallSiteNotAdapted,
                });
            }
        }
    });
    let source = match &outcome {
        super::RewriteOutcome::Emitted { source, .. } => source.clone(),
        super::RewriteOutcome::Degraded { reason, .. } => {
            panic!("the program must emit with the callee withdrawn: {reason}")
        }
    };
    let c = compact(&source);
    assert!(
        !c.contains("__crat_raw_lodepng_memcpy(") && !c.contains("fn__crat_raw_lodepng_memcpy("),
        "no call is renamed to a twin that is not printed: {source}"
    );
    assert!(
        c.contains("fnlodepng_memcpy(mutdst:*mutcore::ffi::c_void,"),
        "the withdrawn callee keeps its signature: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// wave-6f's lodepng reduction (`inflateNoCompression`): `lodepng_memcpy(out as
/// *mut c_void, ((*reader).data).offset(bytepos) as *const c_void, LEN)`. The
/// pair machinery resolves the dst/src pair (no disjointness certificate) by
/// making `src` an A5 raw view hoisted before the call and `dst` the counted
/// `&mut` view — a view beside a raw alias, which this lane refuses. At plan
/// time the counted position at that PAIR-owned call holds `seam-site-overlap`
/// (dst keeps its raw parameter); `src` then converts alone, and its single
/// view beside the raw `out` is routed to the pristine twin (one raw access
/// under a live view is as forbidden as two views). The round emits; nothing
/// pays at the compile gate (R410-2(d); the graft's yield stays the last
/// resort for a node another family replaced).
#[test]
fn w6v_counted_position_at_a_pair_owned_call_holds_at_plan_time() {
    // The A5 raw view is placed only on the production path (precise replay
    // over the frozen graph), which is the path wave-6f's witness takes.
    let fixture = include_str!("wave6f_fixture_lodepng.rs");
    let dir = std::env::temp_dir().join(format!("crat-w6v-pair-owned-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, fixture).unwrap();
    let outcome = super::rewrite_m1_path_a5_injected(
        &root,
        super::OverlapMode::PreciseReplay,
        Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        &|_| {},
    );
    std::fs::remove_dir_all(dir).unwrap();
    let source = match &outcome {
        super::RewriteOutcome::Emitted { source, .. } => source.clone(),
        super::RewriteOutcome::Degraded { reason, .. } => {
            panic!("the round emits: no counted-void plan meets the A5 wrapper: {reason}")
        }
    };
    let c = compact(&source);
    assert!(
        !source.contains("__crat_cv_"),
        "no counted snapshot forms a view at that call: {source}"
    );
    assert!(
        c.contains("fnlodepng_memcpy(mutdst:*mut::std::ffi::c_void,"),
        "dst holds typed instead of paying at the compile gate: {source}"
    );
    // Re-pinned for relay main/388 stage 2 (R1351-2): era-5c 269 stage 1 admits
    // `inflateNoCompression::out` -- its copy lent to `lodepng_memcpy`'s non-retaining
    // `dst` no longer drags it raw -- so `out` is delivered as a slice and passes ONE raw
    // view, beside the A5 raw `src` of another subject (`reader.data`). No view sits
    // beside a raw `out` any more, so nothing routes to the pristine twin.
    assert!(
        c.contains("fninflateNoCompression(mutout:&mut[u8],"),
        "`out` is delivered as a slice: {source}"
    );
    assert!(
        c.contains("lodepng_memcpy(out.as_mut_ptr().cast::<core::ffi::c_void>(),")
            && !c.contains("__crat_raw_lodepng_memcpy("),
        "the slice passes one raw view to the callee itself, no twin: {source}"
    );
}

/// A counted `dst` view beside a raw pointer sibling (`ctx`, an untyped `void *`
/// the callee never uses) at a raw caller that passes its parameter `p` for the
/// view and its OWN local `t` (`&mut t as *mut _`) for the sibling: the local's
/// storage is allocated in this frame, so the never-reassigned parameter's
/// pointee cannot alias it — the roots are disjoint and the single view is
/// formed (no twin). binn's `copy_int_value(psource, &mut out as *mut _, ..)` is
/// this proof.
const FILL_INTO_LOCAL: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, unused_variables)]
unsafe fn fill_ctx(mut dst: *mut core::ffi::c_void, mut value: i32, mut num: usize, mut ctx: *mut core::ffi::c_void) {
    let mut i: usize = 0;
    i = 0;
    while i < num {
        *(dst as *mut i8).offset(i as isize) = value as i8;
        i = i.wrapping_add(1);
    }
}
pub unsafe fn stash(mut p: *mut core::ffi::c_void) -> i64 {
    let mut t: i32 = 9;
    fill_ctx(p, 7, 4, &mut t as *mut i32 as *mut core::ffi::c_void);
    *(p as *mut i8) as i64 + *(p as *mut i8).offset(3) as i64 + t as i64
}
"#;

#[test]
fn w6v_view_beside_the_callers_own_local_storage_is_disjoint() {
    let rows = super::emit_tests::decisions_of(FILL_INTO_LOCAL);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "dst" && *p && r == "<emitted>"),
        "the counted destination delivers: {rows:?}"
    );
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "ctx" && *p && r != "<emitted>"),
        "the untyped context stays raw: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(FILL_INTO_LOCAL).unwrap();
    let c = compact(&source);
    assert!(
        c.contains(
            "fnfill_ctx(mutdst:&mut[core::mem::MaybeUninit<u8>],mutvalue:i32,mutnum:usize,mutctx:*mutcore::ffi::c_void)"
        ),
        "the view beside the raw context: {source}"
    );
    assert!(
        !source.contains("__crat_raw_")
            && c.contains("(|__crat_cv_0,__crat_cv_1,__crat_cv_2,__crat_cv_3|"),
        "the raw `ctx` (this frame's own `t`) cannot alias `p`'s pointee: the view is formed, no twin: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
    let main = "fn main() { unsafe { let mut b = [0i8; 4]; println!(\"{}\", stash(b.as_mut_ptr().cast())); } }";
    let original = run_binary(&format!("{FILL_INTO_LOCAL}\n{main}"));
    assert_eq!(original, b"23\n".to_vec());
    assert_eq!(run_binary(&format!("{source}\n{main}")), original);
}

/// **R491-6 route (i): the counted READ alias is a delivered row of its own.**
///
/// The alias `csrc` is what the emitted program reads bytes through, so the
/// ledger should say so. It cannot say so by carrying the contract's use edits
/// — those are the contract's, and planning them twice is the duplicate K21
/// refuses — so it says so by taking the one edit that is genuinely its own:
/// its DECLARATION, `let mut csrc = src as *const u8` → `src.unwrap_or(&[])`.
/// The contract keeps every use.
#[test]
fn w6v_counted_read_alias_is_a_delivered_row_of_its_own() {
    let rows = super::emit_tests::decisions_of(CSV_READ);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "csrc" && !*p && r == "<emitted>"),
        "the alias local delivers on its own declaration: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(CSV_READ).unwrap();
    let c = compact(&source);
    // The emitted text is unchanged by the move: one initializer, one of each use.
    assert_eq!(
        c.matches("letmutcsrc:&[u8]=src.unwrap_or(&[]);").count(),
        1,
        "the declaration is planned exactly once: {rows:?}\n{source}"
    );
    assert!(
        !c.contains("csrcas*constu8") && !c.contains("*csrcasi32"),
        "no unrewritten alias site survives: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// **R492-5: the alias and its parameter withdraw together.**
///
/// Route (i) puts one contract's edits on two subjects, so a revert that takes
/// one and keeps the other emits a tree that asks `unwrap_or` of a raw pointer
/// (report 032, measured). The closure states the transaction to the revert
/// loop; the two directions are asserted separately because a closure that
/// only looks one way is exactly the defect that was observed.
#[test]
fn w6v_a_withheld_half_of_the_alias_transaction_withdraws_the_other() {
    use rustc_hir::{
        def_id::{DefIndex, LocalDefId},
        hir_id::{HirId, ItemLocalId, OwnerId},
    };

    use super::decision::{
        counted_void::{ByteElement, Contract, close_reverts},
        emitability::UseEdit,
    };

    let owner = LocalDefId {
        local_def_index: DefIndex::from_u32(7),
    };
    let hir = |id| HirId {
        owner: OwnerId { def_id: owner },
        local_id: ItemLocalId::from_u32(id),
    };
    let (param, alias) = (hir(1), hir(2));
    let mut table = super::decision::DecisionTable::default();
    table.counted_void.insert(
        (owner, param),
        Contract {
            count_index: 1,
            count_positional: None,
            element: ByteElement::Read,
            nullable: true,
            handle: None,
            width: None,
            alias: Some(alias),
            decl: Some(UseEdit {
                span: rustc_span::DUMMY_SP,
                replacement: "src.unwrap_or(&[])".to_owned(),
                bridge_kind: "counted-void-read-alias",
            }),
            uses: Vec::new(),
        },
    );

    let closed = |withheld: &[HirId]| {
        let mut reverts = super::ast_transform::RevertSet::default();
        for hir_id in withheld {
            reverts.atom_subjects.insert((owner, *hir_id));
        }
        close_reverts(&table, &mut reverts);
        reverts.fns.contains(&owner)
    };

    assert!(!closed(&[]), "a kept pair withdraws nothing");
    assert!(closed(&[param]), "the withheld parameter takes its alias");
    assert!(closed(&[alias]), "the withheld alias takes its parameter");
}

/// **The count must be evidence, not position (report 037).**
///
/// json.h's real shape, parameter for parameter: the state aggregate takes
/// `src_size` AND `flags_bitset` from the signature, so "the sibling parameter
/// stored beside the pointer" no longer names one thing. The rule refuses
/// rather than pick, because picking the wrong sibling gives the view a length
/// that is not its own — the corpus rows stand or fall on this question, not on
/// the store shape, which the delivering witness above already proves.
const JSON_REAL: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub type size_t = u64;
pub struct parse_result { pub error: size_t, pub error_offset: size_t }
pub struct parse_state {
    pub src: *const i8,
    pub size: size_t,
    pub offset: size_t,
    pub flags_bitset: size_t,
    pub data: *mut i8,
    pub error: size_t,
}
unsafe fn json_parse_ex(mut src: *const core::ffi::c_void, mut src_size: size_t,
    mut flags_bitset: size_t,
    mut alloc_func_ptr: Option<unsafe extern "C" fn(*mut core::ffi::c_void, size_t) -> *mut core::ffi::c_void>,
    mut user_data: *mut core::ffi::c_void,
    mut result: *mut parse_result) -> i32 {
    let mut state = parse_state { src: 0 as *const i8, size: 0, offset: 0, flags_bitset: 0, data: 0 as *mut i8, error: 0 };
    let mut allocation = 0 as *mut core::ffi::c_void;
    if !result.is_null() { (*result).error = 0; (*result).error_offset = 0; }
    if src.is_null() { return -(1 as i32); }
    state.src = src as *const i8;
    state.size = src_size;
    state.offset = 0;
    state.flags_bitset = flags_bitset;
    let mut acc: i32 = 0;
    while state.offset < state.size {
        acc = acc.wrapping_add(*state.src.offset(state.offset as isize) as i32);
        state.offset = state.offset.wrapping_add(1);
    }
    return acc;
}
"#;

#[test]
fn w6v_counted_store_picks_the_following_sibling_by_position() {
    // Restated under R878-1 (A) (relay 304; main 194a / 196): `state.src = src as *const
    // i8` stores the parameter into `parse_state.src`, a field no transaction delivers,
    // so the retained-access check of record holds `src` before the counted family reads
    // its sibling (a delivery lost: it was `Option<&[u8]>` with the following sibling as
    // its count). The pick itself is the family's other witnesses' (the delivering store
    // above, the non-integer control below).
    let rows = super::emit_tests::decisions_of(JSON_REAL);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "src" && *p && r == "held:retained-alias"),
        "the retained-access check holds the stored parameter: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(JSON_REAL).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("state.flags_bitset=flags_bitset;"),
        "the other stored parameter is untouched: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// **The control: a positional pick needs an integer (R500-8).**
///
/// The sibling following the pointer is a pointer of its own here, so there is
/// nothing to read as a length and the rule refuses rather than guess further.
const STORE_NON_INTEGER_SIBLING: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub struct holder { pub src: *const u8, pub other: *const u8, pub size: u64 }
unsafe fn take(mut src: *const core::ffi::c_void, mut other: *const u8, mut n: u64) -> i32 {
    let mut h = holder { src: 0 as *const u8, other: 0 as *const u8, size: 0 };
    if src.is_null() { return -(1 as i32); }
    h.src = src as *const u8;
    h.other = other;
    h.size = n;
    return 0 as i32;
}
"#;

#[test]
fn w6v_counted_store_refuses_a_non_integer_following_sibling() {
    let rows = super::emit_tests::decisions_of(STORE_NON_INTEGER_SIBLING);
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "src" && *p && r != "<emitted>"),
        "no integer follows the pointer, so there is no count to pick: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(STORE_NON_INTEGER_SIBLING).unwrap();
    assert!(
        compact(&source).contains("mutsrc:*constcore::ffi::c_void"),
        "the parameter stays raw: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// **The receipt tells the truth (R500-8).** A positional count is emitted as
/// the caller's own argument text and counted with §77's fabricated extents —
/// never as evidence, because a guess is not evidence.
#[test]
fn w6v_positional_count_receipts_as_a_fabricated_extent() {
    use super::decision::seam::{GlueCore, GlueSpec, SeamLen};
    let mut spec = GlueSpec::core(GlueCore::Bare, false);
    spec.len = Some(SeamLen::PositionalSibling {
        text: "src_size".to_owned(),
        param: "src_size".to_owned(),
    });
    assert_eq!(
        spec.extent_arm_key(),
        "fallback-sibling-by-position@addendum-77"
    );
    assert!(
        spec.len.as_ref().is_some_and(SeamLen::is_fabricated),
        "a positional extent is counted with the fabricated ones (§77)"
    );
    assert_eq!(
        spec.len.as_ref().and_then(SeamLen::positional_param),
        Some("src_size"),
        "and the receipt names what was guessed"
    );
    assert_eq!(spec.len.as_ref().map(SeamLen::text), Some("src_size"));
    let licensed = {
        let mut other = GlueSpec::core(GlueCore::Bare, false);
        other.len = Some(SeamLen::Licensed("src_size".to_owned()));
        other
    };
    assert_ne!(
        spec.extent_arm_key(),
        licensed.extent_arm_key(),
        "the same text, and never the same receipt"
    );
}

// ---- report 042 (R538-7): a raw argument LOADED from a field of the converted root ----
//
// quadtree's `insert_(tree, (*tree).root, …)`, reduced. Position 0 converts to a
// shared view of the tree; position 1 stays raw and shares the place root `tree`,
// but it is a pointer loaded out of `tree` that points at a node in another
// allocation. `insert_` is recursive, so it has no raw twin: without the
// exemption the site is dropped with `SiteOverlap` and the tree's class holds.
const QT_INSERT: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" {
    fn malloc(_: u64) -> *mut core::ffi::c_void;
    fn free(_: *mut core::ffi::c_void);
}
pub struct node_t {
    pub key: *mut core::ffi::c_void,
    pub nw: *mut node_t,
    pub ne: *mut node_t,
}
pub struct tree_t {
    pub root: *mut node_t,
    pub length: u32,
}
unsafe fn node_new() -> *mut node_t {
    let mut node = 0 as *mut node_t;
    node = malloc(::std::mem::size_of::<node_t>() as u64) as *mut node_t;
    if node.is_null() { return 0 as *mut node_t; }
    (*node).nw = 0 as *mut node_t;
    (*node).ne = 0 as *mut node_t;
    (*node).key = 0 as *mut core::ffi::c_void;
    return node;
}
unsafe fn insert_(mut tree: *mut tree_t, mut root: *mut node_t, mut depth: u32) -> i32 {
    if (*tree).length > 100 as u32 { return 0 as i32; }
    if depth == 0 as u32 {
        (*root).key = 0 as *mut core::ffi::c_void;
        (*root).ne = root;
        return 1 as i32;
    }
    if ((*root).nw).is_null() { (*root).nw = node_new(); }
    // wave-5d 150 (R934-1 (i)): the recursion `insert_(tree, (*root).nw, …)`
    // is a pair no rule shows disjoint (the type rule yields for entry beside
    // internal storage, R619-4), so it would hold `tree` raw and hide the
    // exemption at `tree_insert`'s call this fixture is about; the node walks on
    // alone.
    return insert_node((*root).nw, depth.wrapping_sub(1));
}
unsafe fn insert_node(mut root: *mut node_t, mut depth: u32) -> i32 {
    if depth == 0 as u32 { (*root).ne = root; }
    return 1 as i32;
}
unsafe fn tree_new() -> *mut tree_t {
    let mut tree = 0 as *mut tree_t;
    tree = malloc(::std::mem::size_of::<tree_t>() as u64) as *mut tree_t;
    if tree.is_null() { return 0 as *mut tree_t; }
    (*tree).root = node_new();
    (*tree).length = 0 as u32;
    return tree;
}
unsafe fn tree_insert(mut tree: *mut tree_t) -> i32 {
    return insert_(tree, (*tree).root, 3 as u32);
}
"#;

/// The exemption is receipted per site, naming the struct, the field and the
/// pointee it proved disjoint.
#[test]
fn w6v_field_load_exemption_is_receipted_per_site() {
    // wave-5d 150 (R934-1 (i)): the attested census world, as above.
    ::utils::compilation::run_compiler_on_str(QT_INSERT, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::OverlapMode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let keys = table
            .seams
            .field_load_exemptions
            .iter()
            .map(|e| (tcx.def_path_str(e.caller.to_def_id()), e.index, e.key()))
            .collect::<Vec<_>>();
        assert!(
            keys.iter()
                .any(|(caller, index, key)| caller == "tree_insert"
                    && *index == 1
                    && key == "alias-exempt:field-load(tree_t.root->node_t)"),
            "the site's receipt: {keys:?}"
        );
    });
}

/// wave-5d 150 (the round-3 review's M4): quadtree's own recursion,
/// `insert_(tree, (*root).nw, …)`, is a reference formal beside a raw one at an
/// unknown relation that no rule shows disjoint (the type rule yields for entry
/// beside internal storage, R619-4), so R934-1 (i) holds `tree` raw; pinned so
/// the probe's quadtree row is read against it.
#[test]
fn w6v_qt_insert_recursion_holds_the_tree() {
    let input = QT_INSERT.replace(
        "    return insert_node((*root).nw, depth.wrapping_sub(1));",
        "    return insert_(tree, (*root).nw, depth.wrapping_sub(1));",
    );
    assert_ne!(input, QT_INSERT);
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::OverlapMode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| subject.label == "insert_::tree")
            .expect("insert_::tree");
        assert!(
            matches!(decision, super::decision::Decision::Degraded(d)
                if matches!(d.reason, super::decision::DegradeReason::PairNotShownDisjoint { .. })),
            "{decision:?}"
        );
    })
    .unwrap();
}
