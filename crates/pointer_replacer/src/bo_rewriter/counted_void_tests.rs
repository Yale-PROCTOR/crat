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
fn compact(source: &str) -> String {
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

/// Typed family-site withdrawal causes of a fixture (the seam block that
/// withdrew a declaration), as the census receipts carry them.
fn withdrawals_of(input: &str) -> Vec<String> {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(input), |tcx| {
        let (_, ctx) = super::decide_table_with_ctx(tcx).expect("fixture yields a decision table");
        format!("{:#?}", ctx.raw_boundary_artifacts.additive_family_receipts)
            .lines()
            .map(str::trim)
            .filter(|line| line.contains("unsatisfied-family-site"))
            .map(str::to_owned)
            .collect()
    })
    .expect("fixture compiles")
}

/// The copy shape at a real call: `mem` is a fresh `malloc` local and `leaves`
/// a parameter that is never reassigned, so the two roots are distinct
/// allocations and the call is split (both views, closure snapshot).
#[test]
fn w6v_bpm_sort_direct_malloc_local_vs_parameter_splits() {
    let input = format!("{COPY64}{BPM_SORT}");
    let source = check(&input, &["dst", "src"]);
    let routes = routes_of(&input);
    assert!(
        routes
            .iter()
            .any(|(c, r)| c.ends_with("bpmnode_sort") && r == "split"),
        "fresh local vs parameter is split: {routes:?}"
    );
    assert!(
        !source.contains("__crat_raw_lodepng_memcpy"),
        "no twin needed: {source}"
    );
    let withdrawals = withdrawals_of(&input);
    assert!(
        !withdrawals
            .iter()
            .any(|line| line.contains("lodepng_memcpy")),
        "no withdrawal at the copy call: {withdrawals:?}"
    );
}

/// The `size_of::<T>() * n` operand order (R397-4), receipted at a
/// single-pointer callee with the `bpmnode_sort` count expression.
#[test]
fn w6v_size_of_times_num_count_form_is_receipted() {
    let input = format!(
        "{FILL64}{}",
        BPM_SORT
            .replace("unsafe fn bpmnode_sort", "unsafe fn bpmnode_clear")
            .replace(
                "lodepng_memcpy(leaves as *mut core::ffi::c_void,\n            mem as *const core::ffi::c_void,",
                "lodepng_memset(leaves as *mut core::ffi::c_void, 0 as i32,"
            )
    );
    assert!(
        input.contains("lodepng_memset(leaves"),
        "fixture rewrite applied: {input}"
    );
    check(&input, &["dst"]);
    let forms = count_forms_of(&input);
    assert!(
        forms
            .iter()
            .any(|(owner, form)| owner.ends_with("bpmnode_clear")
                && form == "elements:num*size_of::<BPMNode>"),
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

const ALLOC_WRAPPER: &str = r#"
unsafe fn lodepng_malloc(mut size: u64) -> *mut core::ffi::c_void {
    return malloc(size as usize);
}
"#;
/// rs-crown/lodepng `alloc_string_sized` (site 825): fresh `out` vs parameter `in_0`.
const ALLOC_STRING: &str = r#"
unsafe fn alloc_string_sized(mut in_0: *const i8, mut insize: u64) -> *mut i8 {
    let mut out = lodepng_malloc(insize.wrapping_add(1 as i32 as u64)) as *mut i8;
    if !out.is_null() {
        lodepng_memcpy(out as *mut core::ffi::c_void, in_0 as *const core::ffi::c_void, insize);
        *out.offset(insize as isize) = 0 as i32 as i8;
    }
    return out;
}
"#;
/// rs-crown/lodepng `readChunk_tEXt` (site 8125): `key` is null-initialised and
/// assigned once from the wrapper; `data` is a parameter.
const READ_CHUNK: &str = r#"
unsafe fn readChunk_tEXt(mut data: *const u8, mut chunkLength: u64) -> u32 {
    let mut key = 0 as *mut i8;
    let mut length: u64 = 0;
    while length < chunkLength && *data.offset(length as isize) as i32 != 0 { length = length.wrapping_add(1); }
    key = lodepng_malloc(length.wrapping_add(1)) as *mut i8;
    if key.is_null() { return 83; }
    lodepng_memcpy(key as *mut core::ffi::c_void, data as *const core::ffi::c_void, length);
    *key.offset(length as isize) = 0;
    let first = *key as u32;
    free(key as *mut core::ffi::c_void);
    first
}
"#;
/// rs-crown/lodepng `lodepng_color_mode_copy` (site 4488): two parameters — no
/// disjointness proof, so the call keeps the raw signature.
const COLOR_MODE_COPY: &str = r#"
#[repr(C)]
pub struct LodePNGColorMode { pub colortype: i32, pub bitdepth: u32, pub palette: *mut u8, pub palettesize: u64 }
unsafe fn lodepng_color_mode_copy(mut dest: *mut LodePNGColorMode, mut source: *const LodePNGColorMode) {
    lodepng_memcpy(dest as *mut core::ffi::c_void, source as *const core::ffi::c_void,
        ::std::mem::size_of::<LodePNGColorMode>() as u64);
}
"#;

fn routes_of(input: &str) -> Vec<(String, String)> {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(input), |tcx| {
        let table = super::decide_table(tcx).expect("fixture yields a decision table");
        table
            .seams
            .counted_void_calls
            .iter()
            .map(|call| {
                (
                    tcx.def_path_str(call.caller.to_def_id()),
                    call.route.key().to_owned(),
                )
            })
            .collect()
    })
    .expect("fixture compiles")
}

#[test]
fn w6v_split_fresh_wrapper_local_vs_parameter_delivers_the_copy() {
    let input = format!("{COPY64}{ALLOC_WRAPPER}{ALLOC_STRING}{INFLATE_BACKREF}");
    let source = check(&input, &["dst", "src"]);
    assert!(
        source.contains("src: &[u8]"),
        "shared byte declaration: {source}"
    );
    let routes = routes_of(&input);
    assert!(
        routes
            .iter()
            .any(|(c, r)| c.ends_with("alloc_string_sized") && r == "split"),
        "the fresh-vs-parameter call is split: {routes:?}"
    );
    assert!(
        routes
            .iter()
            .any(|(c, r)| c.ends_with("inflateHuffmanBlock") && r == "raw-twin"),
        "the in-buffer copy keeps the raw signature: {routes:?}"
    );
    let compact_source = compact(&source);
    assert!(
        compact_source.contains("fn__crat_raw_lodepng_memcpy(mutdst:*mutcore::ffi::c_void,mutsrc:*constcore::ffi::c_void,mutsize:u64)"),
        "a pristine raw twin is emitted: {source}"
    );
    assert!(
        compact_source.contains("__crat_raw_lodepng_memcpy(((*out).data).offset(startasisize)"),
        "the in-buffer call is routed to the raw twin with its arguments untouched: {source}"
    );
    assert_eq!(
        source.matches("fn __crat_raw_lodepng_memcpy").count(),
        1,
        "one twin per callee: {source}"
    );
    let main = r#"fn main() { unsafe {
        let text = b"hello\0";
        let copy = alloc_string_sized(text.as_ptr().cast(), 5);
        let s = std::ffi::CStr::from_ptr(copy).to_str().unwrap().to_owned();
        free(copy as *mut core::ffi::c_void);
        let mut bytes = [1u8, 2, 3, 0, 0, 0, 0, 0];
        let mut v = ucvector { data: bytes.as_mut_ptr(), size: 8, allocsize: 8 };
        inflateHuffmanBlock(&mut v, 3, 0, 5);
        println!("{s} {:?}", bytes);
    }}"#;
    let original = run_binary(&format!("{input}\n{main}"));
    assert_eq!(original, b"hello [1, 2, 3, 1, 2, 3, 1, 2]\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{main}")));
}

#[test]
fn w6v_split_bpm_sort_and_null_initialised_key_are_fresh_roots() {
    let input = format!(
        "{COPY64}{ALLOC_WRAPPER}{}{READ_CHUNK}",
        BPM_SORT
            .replace("malloc((", "lodepng_malloc((")
            .replace(".wrapping_mul(num) as usize)", ".wrapping_mul(num))")
    );
    assert!(
        input.contains("let mut mem = lodepng_malloc("),
        "fixture uses the wrapper: {input}"
    );
    let source = check(&input, &["dst", "src"]);
    let routes = routes_of(&input);
    for owner in ["bpmnode_sort", "readChunk_tEXt"] {
        assert!(
            routes
                .iter()
                .any(|(c, r)| c.ends_with(owner) && r == "split"),
            "{owner} is split: {routes:?}"
        );
    }
    assert!(
        !source.contains("__crat_raw_lodepng_memcpy"),
        "no twin when every call splits: {source}"
    );
    let main = r#"fn main() { unsafe {
        let mut leaves = [BPMNode { weight: 0, index: 0, tail: core::ptr::null_mut(), in_use: 0 }; 3];
        for (i, l) in leaves.iter_mut().enumerate() { l.weight = i as i32 * 10; l.index = i as u32; }
        bpmnode_sort(leaves.as_mut_ptr(), 3);
        println!("{:?} {}", leaves.iter().map(|l| (l.weight, l.index)).collect::<Vec<_>>(), readChunk_tEXt(b"key\0value".as_ptr(), 9));
    }}"#;
    let input = input.replace("pub in_use: i32", "pub in_use: i64"); // padding-free struct: the byte copy reads no padding
    let source = check(&input, &["dst", "src"]);
    let original = run_binary(&format!("{input}\n{main}"));
    assert_eq!(original, b"[(20, 2), (10, 1), (0, 0)] 107\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{main}")));
}

#[test]
fn w6v_split_refuses_two_parameters_and_a_reassigned_fresh_local() {
    // Two parameters: no proof.
    let input = format!("{COPY64}{ALLOC_WRAPPER}{ALLOC_STRING}{COLOR_MODE_COPY}");
    let routes = routes_of(&input);
    assert!(
        routes
            .iter()
            .any(|(c, r)| c.ends_with("lodepng_color_mode_copy") && r == "raw-twin"),
        "two parameters keep the raw signature: {routes:?}"
    );
    // A fresh local that is reassigned from the parameter is no longer fresh.
    let reassigned = ALLOC_STRING.replace(
        "    if !out.is_null() {",
        "    if insize == 0 { out = in_0 as *mut i8; }\n    if !out.is_null() {",
    );
    let input = format!("{COPY64}{ALLOC_WRAPPER}{reassigned}");
    let routes = routes_of(&input);
    assert!(
        routes
            .iter()
            .any(|(c, r)| c.ends_with("alloc_string_sized") && r == "raw-twin"),
        "a reassigned local is not a fresh root: {routes:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(super::verify::type_checks_str(&source));
}

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
    assert!(
        c.contains("letmutcsrc=src.unwrap_or(&[]);"),
        "the alias is the view: {source}"
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
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        rows.iter()
            .filter(|(n, p, _)| n == "src" && *p)
            .all(|(_, _, r)| r != "<emitted>"),
        "an unbounded read holds the parameter: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
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
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        rows.iter()
            .filter(|(n, p, _)| n == "src" && *p)
            .all(|(_, _, r)| r != "<emitted>"),
        "an escaping alias holds the parameter: {rows:?}"
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
    assert!(c.contains("letmutus=s.unwrap_or(&[]);"), "{source}");
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
        c.contains("BZ2_bzRead(&mutbzerr,&*((b)as*constbzFile),len)"),
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
