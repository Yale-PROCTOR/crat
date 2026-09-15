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
        "{FILL}\nunsafe fn fill_caller(dst: *mut core::ffi::c_void, n: usize) {{ lodepng_memset(dst, 255, n); }}"
    );
    let source = check(&input, &["dst"]);
    assert!(
        source.contains("(__crat_cv_2) as usize"),
        "count must be the snapshot of n, not value=255: {source}"
    );
    assert!(
        compact(&source).contains(")(dst,255,n)"),
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
        counted_void::{ByteElement, CountedByte, render_bridge},
        seam::{GlueCore, GlueSpec},
    };
    let counted = CountedByte {
        element: ByteElement::Write,
        arg_index: 0,
    };
    let mut spec = GlueSpec::core(GlueCore::FromRawParts, true).with_len("n");
    spec.counted_byte = Some(counted);
    let rendered = render_bridge(&spec, counted).expect("typed byte bridge");
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
        counted_void::{ByteElement, CountedByte, render_bridge},
        seam::{GlueCore, GlueSpec},
    };
    let counted = CountedByte {
        element: ByteElement::Write,
        arg_index: 0,
    };
    let spec = GlueSpec::core(GlueCore::FromRawParts, true).with_len("__crat_counted_ptr");
    let rendered = render_bridge(&spec, counted).unwrap();
    let source = format!(
        "unsafe fn length(__crat_cv_0: *mut core::ffi::c_void, __crat_counted_ptr: usize) -> usize {{ let view: &mut [core::mem::MaybeUninit<u8>] = {rendered}; view.len() }} fn main() {{ let mut bytes=[0u8;4]; println!(\"{{}}\",unsafe{{length(bytes.as_mut_ptr().cast(),4)}}); }}"
    );
    assert_eq!(run_binary(&source), b"4\n");
}

#[test]
fn w6v_addressed_pointer_storage_copy_holds_and_keeps_its_meaning() {
    // The copy destination is the source pointer's own storage. A copy call
    // bridges no position (two counted positions at one call), so the input's
    // meaning is kept exactly; the runtime check pins that.
    let helper = format!(
        "{COPY}\npub unsafe fn copy_pointer_storage() -> u8 {{ let data=[7u8;8]; let mut src: *const core::ffi::c_void=data.as_ptr().cast(); let dst: *mut core::ffi::c_void=&raw mut src as *mut *const core::ffi::c_void as *mut core::ffi::c_void; lodepng_memcpy(dst,src,1); (src as usize & 0xff) as u8 }}"
    );
    let emitted = super::emit_tests::ast_emitted_source_of(&helper).unwrap();
    assert!(
        !emitted.contains("dst: &mut [") && !emitted.contains("src: &[u8]"),
        "no view at a two-position copy: {emitted}"
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

/// The copy shape at a real call: two counted positions at one call may cover
/// overlapping bytes, so the call holds typed and BOTH callee parameters stay
/// raw (no disjointness proof exists at this site or at lodepng's LZ77 sites).
#[test]
fn w6v_bpm_sort_two_counted_positions_hold_as_site_overlap() {
    let input = format!("{COPY64}{BPM_SORT}");
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        !source.contains("dst: &mut [") && !source.contains("src: &[u8]"),
        "a read+write byte callee keeps raw parameters at a real call: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let withdrawals = withdrawals_of(&input);
    assert!(
        withdrawals
            .iter()
            .any(|line| line.contains("seam-site-overlap")),
        "typed hold at the copy call: {withdrawals:?}"
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
    assert!(
        !(source.contains("dst: &mut [") && source.contains("src: &[u8]")),
        "a copy within one buffer may overlap; two live views are forbidden: {source}"
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
