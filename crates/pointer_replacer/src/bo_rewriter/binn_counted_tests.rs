//! binn's counted `void *` parameters (wave-6v2). Fixtures are reduced from
//! rs-crown-derived/binn/lib.rs: `binn_get_ptr_type` (:499, a fixed-width
//! magic read), `binn_type` (:1286, its raw caller), `copy_int_value` (:2144,
//! a width selected by a sibling type parameter), `binn_memdup` (:264, a
//! sibling-counted foreign copy source).

/// Whitespace-free view of an emitted source, for shape assertions.
fn compact(source: &str) -> String {
    source.chars().filter(|c| !c.is_whitespace()).collect()
}

fn delivers(rows: &[(String, bool, String)], name: &str) -> bool {
    rows.iter()
        .any(|(n, p, r)| n == name && *p && r == "<emitted>")
}

/// `(function, parameter, reason)` for every parameter row.
fn by_function(input: &str) -> Vec<(String, String, String)> {
    super::emit_tests::artifact_rows_of(input)
        .iter()
        .filter(|r| r.arg_index.is_some())
        .map(|r| {
            (
                r.fn_path
                    .rsplit("::")
                    .next()
                    .unwrap_or(&r.fn_path)
                    .to_owned(),
                r.param_name.clone().unwrap_or_default(),
                r.degrade_reason
                    .clone()
                    .unwrap_or_else(|| "<emitted>".to_owned()),
            )
        })
        .collect()
}

fn reason(rows: &[(String, bool, String)], name: &str) -> String {
    rows.iter()
        .find(|(n, p, _)| n == name && *p)
        .map(|(_, _, r)| r.clone())
        .unwrap_or_else(|| panic!("no parameter {name}: {rows:?}"))
}

fn run_binary(source: &str) -> Vec<u8> {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("crat-w6v2-runtime-{}-{id}", std::process::id()));
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

/// binn.rs:499 `binn_get_ptr_type` and :1286 `binn_type`: the opaque header
/// pointer is read once, as a `c_uint`, through a null test; the caller keeps
/// its own `void *` (a struct-or-buffer pointer this build does not deliver).
const MAGIC: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct binn { pub header: i32, pub type_0: i32, pub ptr: *mut core::ffi::c_void }
unsafe fn binn_get_ptr_type(mut ptr: *mut core::ffi::c_void) -> i32 {
    if ptr.is_null() { return 0 as i32; }
    match *(ptr as *mut u32) {
        522367263 => return 1 as i32,
        _ => return 2 as i32,
    };
}
pub unsafe fn binn_type(mut ptr: *mut core::ffi::c_void) -> i32 {
    let mut item = 0 as *mut binn;
    match binn_get_ptr_type(ptr) {
        1 => { item = ptr as *mut binn; return (*item).type_0; }
        2 => return 7 as i32,
        _ => return -(1 as i32),
    };
}
"#;

#[test]
fn w6v2_fixed_width_magic_read_delivers_a_byte_view() {
    let rows = super::emit_tests::decisions_of(MAGIC);
    assert!(
        delivers(&rows, "ptr"),
        "the fixed-width read parameter delivers: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(MAGIC).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnbinn_get_ptr_type(mutptr:Option<&[u8]>)->i32"),
        "null-tested constant-width read view: {source}"
    );
    assert!(c.contains("ifptr.is_none()"), "null test moves: {source}");
    assert!(
        c.contains("ptr.unwrap_or(&[])[..core::mem::size_of::<u32>()]"),
        "the typed read is checked against the width: {source}"
    );
    assert!(
        c.contains(".as_ptr().cast::<u32>().read_unaligned()"),
        "the typed read is a receipted unaligned read: {source}"
    );
    assert!(
        c.contains("core::mem::size_of::<u32>())asusize"),
        "the raw caller's count is the callee's own width: {source}"
    );
    assert!(
        !source.contains("FALLBACK_SLICE_EXTENT"),
        "the width is evidence, never the fallback: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let mut item = binn { header: 522367263, type_0: 0xe1, ptr: core::ptr::null_mut() };
        let mut buffer = [0xe0u8, 3, 0, 0, 0, 0, 0, 0];
        println!("{} {} {}", binn_type(&mut item as *mut binn as *mut core::ffi::c_void),
            binn_type(buffer.as_mut_ptr().cast()), binn_type(core::ptr::null_mut()));
    }}"#;
    let original = run_binary(&format!("{MAGIC}\n{main}"));
    assert_eq!(original, b"225 7 -1\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{main}")));
}

/// binn.rs:2144 `copy_int_value`: the source width is selected by the sibling
/// `source_type`; every arm reads one type at offset zero. (`pdest` is written
/// through the same selection and stays held in this build.)
const SELECTED: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
unsafe fn copy_int_value(mut psource: *mut core::ffi::c_void,
    mut pdest: *mut core::ffi::c_void, mut source_type: i32, mut dest_type: i32) -> i32 {
    let mut vint64: i64 = 0;
    match source_type {
        33 => { vint64 = *(psource as *mut i8) as i64; }
        65 => { vint64 = *(psource as *mut i16) as i64; }
        97 => { vint64 = *(psource as *mut i32) as i64; }
        129 => { vint64 = *(psource as *mut i64); }
        _ => return 0 as i32,
    }
    match dest_type {
        97 => { *(pdest as *mut i32) = vint64 as i32; }
        129 => { *(pdest as *mut i64) = vint64; }
        _ => return 0 as i32,
    }
    return 1 as i32;
}
pub unsafe fn convert(mut src: *mut core::ffi::c_void, mut kind: i32) -> i64 {
    let mut out: i64 = 0;
    copy_int_value(src, &mut out as *mut i64 as *mut core::ffi::c_void, kind.wrapping_add(0), 129);
    return out;
}
pub unsafe fn forward(mut src: *mut core::ffi::c_void, mut kind: i32) -> i64 {
    let mut out: i64 = 0;
    copy_int_value(src, &mut out as *mut i64 as *mut core::ffi::c_void, kind, 129);
    return out;
}
"#;

#[test]
fn w6v2_sibling_selected_width_delivers_a_byte_view() {
    let rows = super::emit_tests::decisions_of(SELECTED);
    assert!(
        delivers(&rows, "psource"),
        "the width-selected read parameter delivers: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(SELECTED).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fncopy_int_value(mutpsource:&[u8],"),
        "the read view: {source}"
    );
    assert!(
        c.contains("psource[..core::mem::size_of::<i16>()]")
            && c.contains(".as_ptr().cast::<i16>().read_unaligned()"),
        "each arm reads its own width, checked: {source}"
    );
    assert!(
        c.contains("match__crat_cv_2{33=>core::mem::size_of::<i8>(),65=>core::mem::size_of::<i16>(),97=>core::mem::size_of::<i32>(),129=>core::mem::size_of::<i64>(),_=>0,}"),
        "the raw caller's count is the callee's own width table over the snapshotted discriminant: {source}"
    );
    assert!(
        c.contains("fnforward(mutsrc:&[u8],mutkind:i32)->i64"),
        "a caller passing its own sibling unchanged forwards the table (the parent's fixpoint, re-keyed): {source}"
    );
    assert!(
        !source.contains("FALLBACK_SLICE_EXTENT"),
        "the width is evidence, never the fallback: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let mut a: i16 = -2; let mut b: i64 = 1 << 40; let mut c: i8 = 5;
        println!("{} {} {} {}", convert(&mut a as *mut i16 as *mut core::ffi::c_void, 65),
            convert(&mut b as *mut i64 as *mut core::ffi::c_void, 129),
            convert(&mut c as *mut i8 as *mut core::ffi::c_void, 33),
            convert(&mut c as *mut i8 as *mut core::ffi::c_void, 7));
    }}"#;
    let original = run_binary(&format!("{SELECTED}\n{main}"));
    assert_eq!(original, b"-2 1099511627776 5 0\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{main}")));
}

/// A thin caller is never widened (R395-2): `convert_narrow` hands a `*mut i32`
/// where the literal discriminant selects eight bytes. fix-2 holds the caller
/// (`held:local-callee-access-extent`, the first enforcement point), so the
/// argument reaches the seam as a RAW root and the view carries the callee's
/// exact width over it — the input's own obligation (§28), not a widened
/// reference. [`super::decision::binn_counted::root_rule`] is the second
/// enforcement point of the same premise (R312-1: declared redundant, kept).
#[test]
fn w6v2_selected_width_never_widens_a_thin_root() {
    let input = format!(
        "{SELECTED}\npub unsafe fn convert_narrow(mut src: *mut i32) -> i64 {{ let mut out: i64 = 0; copy_int_value(src as *mut core::ffi::c_void, &mut out as *mut i64 as *mut core::ffi::c_void, 129, 129); out }}"
    );
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        delivers(&rows, "psource"),
        "the callee keeps its view: {rows:?}"
    );
    assert!(
        rows.iter()
            .any(|(n, p, r)| n == "src" && *p && r == "held:local-callee-access-extent"),
        "the thin caller is held, not widened: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnconvert_narrow(mutsrc:*muti32)->i64"),
        "the caller stays raw: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
}

/// The root rule itself, on the table: a thin root fits only a width known at
/// the site and equal to the viewed place's size.
#[test]
fn w6v2_width_table_selects_exactly_by_literal() {
    use super::decision::binn_counted::WidthTable;
    let table = WidthTable {
        discriminant: Some(2),
        arms: vec![(33, "i8".to_owned(), 1), (129, "i64".to_owned(), 8)],
    };
    assert_eq!(
        table.render(),
        "match __crat_cv_2 { 33 => core::mem::size_of::<i8>(), 129 => core::mem::size_of::<i64>(), _ => 0, }"
    );
    assert_eq!(table.receipt(), "width-table:arg2:{33:i8,129:i64}");
    assert_eq!(
        table.rekey(5).render(),
        table.render().replace("__crat_cv_2", "__crat_cv_5")
    );
    let constant = WidthTable {
        discriminant: None,
        arms: vec![(0, "u32".to_owned(), 4)],
    };
    assert_eq!(constant.render(), "core::mem::size_of::<u32>()");
    assert_eq!(constant.receipt(), "width:size_of::<u32>");
}

/// A width selected by anything but a literal-armed match over one unchanged
/// sibling parameter is not a table: the parameter stays typed-held.
#[test]
fn w6v2_width_not_selected_by_a_sibling_literal_stays_held() {
    for input in [
        // two widths in one arm
        SELECTED.replace(
            "65 => { vint64 = *(psource as *mut i16) as i64; }",
            "65 => { vint64 = *(psource as *mut i16) as i64 + *(psource as *mut i8) as i64; }",
        ),
        // the discriminant is written before the read
        SELECTED.replace(
            "let mut vint64: i64 = 0;",
            "let mut vint64: i64 = 0; source_type = dest_type;",
        ),
        // a read outside every arm
        SELECTED.replace(
            "let mut vint64: i64 = 0;",
            "let mut vint64: i64 = *(psource as *mut i8) as i64;",
        ),
        // a read at an offset
        SELECTED.replace("*(psource as *mut i16)", "*(psource as *mut i16).offset(1)"),
    ] {
        let rows = super::emit_tests::decisions_of(&input);
        assert!(
            !delivers(&rows, "psource"),
            "unproved width stays held: {rows:?}"
        );
        assert!(
            reason(&rows, "psource").starts_with("held:void-pointee"),
            "the hold keeps its family: {rows:?}"
        );
    }
}

/// binn.rs:264 `binn_memdup`: the source is read by a foreign `memcpy` whose
/// count is the sibling `size`; the destination is an allocation (held).
const MEMDUP: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" {
    fn malloc(n: u64) -> *mut core::ffi::c_void;
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
}
unsafe fn binn_memdup(mut src: *mut core::ffi::c_void, mut size: i32) -> *mut core::ffi::c_void {
    let mut dest = 0 as *mut core::ffi::c_void;
    if src.is_null() || size <= 0 as i32 { return 0 as *mut core::ffi::c_void; }
    dest = malloc(size as u64);
    if dest.is_null() { return 0 as *mut core::ffi::c_void; }
    memcpy(dest, src, size as u64);
    return dest;
}
pub unsafe fn dup_bytes(mut p: *mut core::ffi::c_void, mut n: i32) -> *mut core::ffi::c_void {
    return binn_memdup(p, n.wrapping_add(0));
}
"#;

#[test]
#[ignore = "build queued (wave-6v2 build 2): the foreign memcpy position is unmodeled in the pinned contract table; wave-4 #1b's contract rows land in batch 7"]
fn w6v2_foreign_copy_source_counted_by_a_sibling_delivers() {
    let rows = super::emit_tests::decisions_of(MEMDUP);
    assert!(
        delivers(&rows, "src"),
        "the counted copy source delivers: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(MEMDUP).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnbinn_memdup(mutsrc:Option<&[u8]>,mutsize:i32)"),
        "null-tested counted read view: {source}"
    );
    assert!(
        c.contains("(__crat_cv_1)asusize"),
        "the raw caller's count is the snapshot of the sibling: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let text = b"binn";
        let copy = dup_bytes(text.as_ptr() as *mut core::ffi::c_void, 4) as *const u8;
        let null = dup_bytes(core::ptr::null_mut(), 4);
        let empty = dup_bytes(text.as_ptr() as *mut core::ffi::c_void, 0);
        println!("{:?} {} {}", core::slice::from_raw_parts(copy, 4), null.is_null(), empty.is_null());
    }}"#;
    let original = run_binary(&format!("{MEMDUP}\n{main}"));
    assert_eq!(original, b"[98, 105, 110, 110] true true\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{main}")));
}

/// The copy's count must be the sibling parameter itself, unchanged: a count
/// the callee re-derives is not the caller's extent.
#[test]
fn w6v2_foreign_copy_with_a_rederived_count_stays_held() {
    let input = MEMDUP.replace(
        "memcpy(dest, src, size as u64);",
        "size = size + 1; memcpy(dest, src, size as u64);",
    );
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        !delivers(&rows, "src"),
        "a re-derived count holds: {rows:?}"
    );
}

/// binn.rs:508 `binn_is_struct` (a magic read in a condition) and :2229
/// `copy_float_value` (two float arms): the same rule on the other two corpus
/// rows this build targets.
#[test]
fn w6v2_condition_read_and_float_arms_deliver() {
    let input = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn binn_is_struct(mut ptr: *mut core::ffi::c_void) -> i32 {
    if ptr.is_null() { return 0 as i32; }
    if *(ptr as *mut u32) == 0x1f22b11f as i32 as u32 { return 1 as i32 } else { return 0 as i32 };
}
unsafe fn copy_float_value(mut psource: *mut core::ffi::c_void,
    mut pdest: *mut core::ffi::c_void, mut source_type: i32, mut dest_type: i32) -> i32 {
    match source_type {
        98 => { *(pdest as *mut f64) = *(psource as *mut f32) as f64; }
        130 => { *(pdest as *mut f32) = *(psource as *mut f64) as f32; }
        _ => return 0 as i32,
    }
    return 1 as i32;
}
pub unsafe fn widen(mut src: *mut core::ffi::c_void, mut kind: i32) -> f64 {
    let mut out: f64 = 0.;
    copy_float_value(src, &mut out as *mut f64 as *mut core::ffi::c_void, kind.wrapping_add(0), 130);
    return out;
}
"#;
    let rows = super::emit_tests::decisions_of(input);
    assert!(
        delivers(&rows, "ptr"),
        "the condition read delivers: {rows:?}"
    );
    assert!(
        delivers(&rows, "psource"),
        "the float arms deliver: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(input).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnbinn_is_struct(mutptr:Option<&[u8]>)->i32")
            && c.contains("fncopy_float_value(mutpsource:&[u8],"),
        "both views: {source}"
    );
    assert!(
        c.contains("match__crat_cv_2{98=>core::mem::size_of::<f32>(),130=>core::mem::size_of::<f64>(),_=>0,}"),
        "the float width table: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let mut a: f32 = 1.5; let mut magic: u32 = 0x1f22b11f; let mut other: u32 = 7;
        println!("{} {} {} {}", widen(&mut a as *mut f32 as *mut core::ffi::c_void, 98),
            binn_is_struct(&mut magic as *mut u32 as *mut core::ffi::c_void),
            binn_is_struct(&mut other as *mut u32 as *mut core::ffi::c_void),
            binn_is_struct(core::ptr::null_mut()));
    }}"#;
    // The public entry's signature moved; the emitted main hands it the views.
    let emitted_main = r#"fn main() { unsafe {
        let mut a: f32 = 1.5; let magic: u32 = 0x1f22b11f; let other: u32 = 7;
        println!("{} {} {} {}", widen(&mut a as *mut f32 as *mut core::ffi::c_void, 98),
            binn_is_struct(Some(&magic.to_ne_bytes()[..])),
            binn_is_struct(Some(&other.to_ne_bytes()[..])),
            binn_is_struct(None));
    }}"#;
    let original = run_binary(&format!("{input}\n{main}"));
    assert_eq!(original, b"1.5 1 0 0\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{emitted_main}")));
}

/// An escaping cast (binn.rs:2116 `copy_raw_value` stores `psource` through
/// `pdest`) holds, typed in the family; a pure forward of a constant-width
/// position (`wrap`) inherits the width (build 2). `binn_type` (:1286) both
/// forwards and casts to the struct: still held.
#[test]
fn w6v2_escaping_cast_stays_held_and_a_constant_width_forwards() {
    let input = format!(
        "{MAGIC}\nunsafe fn copy_raw_value(mut psource: *mut core::ffi::c_void, mut pdest: *mut core::ffi::c_void, mut data_store: i32) -> i32 {{ match data_store {{ 32 => {{ *(pdest as *mut i8) = *(psource as *mut i8); }} 192 => {{ *(pdest as *mut *mut i8) = psource as *mut i8; }} _ => return 0 as i32, }} return 1 as i32; }}\nunsafe fn wrap(mut p: *mut core::ffi::c_void) -> i32 {{ binn_get_ptr_type(p) }}"
    );
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        delivers(&rows, "ptr"),
        "the magic read still delivers: {rows:?}"
    );
    assert_eq!(
        reason(&rows, "psource"),
        "held:void-pointee",
        "the escaping cast stays in the family: {rows:?}"
    );
    // Build 2: a pure forward of a constant-width position inherits the width.
    assert!(
        delivers(&rows, "p"),
        "the forwarder inherits the constant width: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        compact(&source).contains("fnwrap(mutp:Option<&[u8]>)->i32{binn_get_ptr_type(p)}"),
        "the forward is a safe-to-safe seam: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
}

/// binn.rs:2629 `binn_list_int32` → :2493 `binn_list_get` → :1561
/// `binn_list_get_value` (reassigned from `binn_ptr`, held) → :1254 `binn_ptr`.
/// The two forwarders pass their `void *` on unchanged; the leaf keeps its raw
/// parameter, so every forward crosses an outbound raw seam. Under build 2b
/// the byte-view bridge exists and the descendant question is discharged by
/// the frame-confined out-param, but the retention verdict still holds the
/// chain: `binn_list_get_value`'s `ptr` reaches `binn_ptr`, which RETURNS it,
/// and the returned alias — not the parameter — is what the leaf stores into
/// `*value`. A positive sink reached through a dependency's return is outside
/// the stack-storage certificate (report 003, next shape), so every forward
/// is withdrawn as a dropped class site and the parameters stay
/// `held:void-pointee` — never an unbridged view.
const CHAIN: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct binn { pub header: i32, pub type_0: i32, pub size: i32, pub ptr: *mut core::ffi::c_void }
unsafe fn binn_get_ptr_type(mut ptr: *mut core::ffi::c_void) -> i32 {
    if ptr.is_null() { return 0 as i32; }
    match *(ptr as *mut u32) {
        522367263 => return 1 as i32,
        _ => return 2 as i32,
    };
}
pub unsafe fn binn_ptr(mut ptr: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let mut item = 0 as *mut binn;
    match binn_get_ptr_type(ptr) {
        1 => { item = ptr as *mut binn; return (*item).ptr; }
        2 => return ptr,
        _ => return 0 as *mut core::ffi::c_void,
    };
}
pub unsafe fn binn_list_get_value(mut ptr: *mut core::ffi::c_void, mut pos: i32, mut value: *mut binn) -> i32 {
    ptr = binn_ptr(ptr);
    if ptr.is_null() || value.is_null() { return 0 as i32; }
    let mut p = ptr as *mut u8;
    if *p as i32 != 0xe0 as i32 { return 0 as i32; }
    (*value).type_0 = *p.offset(pos as isize) as i32;
    (*value).ptr = p.offset(pos as isize) as *mut core::ffi::c_void;
    return 1 as i32;
}
pub unsafe fn binn_list_get(mut ptr: *mut core::ffi::c_void, mut pos: i32, mut type_0: i32, mut pvalue: *mut i32) -> i32 {
    let mut value = binn { header: 0, type_0: 0, size: 0, ptr: 0 as *mut core::ffi::c_void };
    if binn_list_get_value(ptr, pos, &mut value) == 0 as i32 { return 0 as i32; }
    *pvalue = value.type_0;
    return 1 as i32;
}
pub unsafe fn binn_list_int32(mut list: *mut core::ffi::c_void, mut pos: i32) -> i32 {
    let mut value: i32 = 0;
    binn_list_get(list, pos, 0x61 as i32, &mut value);
    return value;
}
"#;

#[test]
fn w6v2_forwards_into_a_returned_alias_chain_stay_held() {
    let rows = by_function(CHAIN);
    assert!(
        rows.contains(&(
            "binn_get_ptr_type".to_owned(),
            "ptr".to_owned(),
            "<emitted>".to_owned()
        )),
        "the leaf read delivers: {rows:?}"
    );
    for (function, parameter) in [
        ("binn_list_int32", "list"),
        ("binn_list_get", "ptr"),
        ("binn_list_get_value", "ptr"),
        ("binn_ptr", "ptr"),
    ] {
        assert!(
            rows.contains(&(
                function.to_owned(),
                parameter.to_owned(),
                "held:void-pointee".to_owned()
            )),
            "{function}::{parameter} stays in the family: {rows:?}"
        );
    }
    let source = super::emit_tests::ast_emitted_source_of(CHAIN).unwrap();
    assert!(
        compact(&source)
            .contains("fnbinn_list_int32(mutlist:*mutcore::ffi::c_void,mutpos:i32)->i32"),
        "a withdrawn forward keeps its raw parameter: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
}

/// R406-6 finding B, the direct shape: `get_value` stores the pointer it is
/// handed into the caller's out-parameter `*value`; `get_type` passes
/// `&mut value` where `value` is its own local that never leaves its frame
/// (only a scalar field is read out of it). `get_type`'s `ptr` is a thin
/// subject whose only raw seam is that call: positive retention before, T1
/// under the stack-storage certificate now.
const CONFINED: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct binn { pub header: i32, pub type_0: i32, pub size: i32, pub ptr: *mut core::ffi::c_void }
pub unsafe fn get_value(mut ptr: *mut u8, mut pos: i32, mut value: *mut binn) -> i32 {
    if ptr.is_null() || value.is_null() { return 0 as i32; }
    (*value).type_0 = *ptr as i32 + pos;
    (*value).ptr = ptr as *mut core::ffi::c_void;
    return 1 as i32;
}
pub unsafe fn get_type(mut ptr: *mut u8, mut pos: i32) -> i32 {
    let mut value = binn { header: 0, type_0: 0, size: 0, ptr: 0 as *mut core::ffi::c_void };
    if get_value(ptr, pos, &mut value) == 0 as i32 { return 0 as i32; }
    return value.type_0;
}
"#;

#[test]
fn w6v2_stack_confined_out_param_retention_is_t1() {
    let rows = by_function(CONFINED);
    assert!(
        rows.contains(&(
            "get_type".to_owned(),
            "ptr".to_owned(),
            "<emitted>".to_owned()
        )),
        "the retained-into-confined-storage subject delivers: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(CONFINED).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnget_type(mutptr:&u8,mutpos:i32)->i32")
            || c.contains("fnget_type(mutptr:&mutu8,mutpos:i32)->i32"),
        "the subject takes its reference form: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let mut buffer = [0xe0u8, 3, 9, 0, 0, 0, 0, 0];
        println!("{} {}", get_type(buffer.as_mut_ptr(), 0), get_type(buffer.as_mut_ptr(), 1));
    }}"#;
    let emitted_main = r#"fn main() { unsafe {
        let mut buffer = [0xe0u8, 3, 9, 0, 0, 0, 0, 0];
        println!("{} {}", get_type(&mut buffer[0], 0), get_type(&mut buffer[0], 1));
    }}"#;
    let original = run_binary(&format!("{CONFINED}\n{main}"));
    assert_eq!(original, b"224 225\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{emitted_main}")));
}

/// The certificate's own line: a caller local whose pointer-carrying field is
/// read out (`value.ptr` handed on) is NOT frame-confined, and the forward
/// stays held; so does one whose address is taken at a second call.
#[test]
fn w6v2_escaping_out_param_storage_keeps_the_hold() {
    for input in [
        CONFINED.replace(
            "return value.type_0;",
            "sink(value.ptr); return value.type_0;",
        ) + "\nunsafe fn sink(p: *mut core::ffi::c_void) {}",
        CONFINED.replace(
            "return value.type_0;",
            "touch(&mut value); return value.type_0;",
        ) + "\nunsafe fn touch(p: *mut binn) {}",
        // The callee also hands the pointer to a callee that keeps it: the
        // confined out-param does not discharge a sink reached elsewhere.
        CONFINED.replace(
            "(*value).ptr = ptr as *mut core::ffi::c_void;",
            "(*value).ptr = ptr as *mut core::ffi::c_void; keep(ptr);",
        ) + "\nstatic mut KEPT: *mut u8 = 0 as *mut u8;\nunsafe fn keep(p: *mut u8) { KEPT = p; }",
    ] {
        let rows = by_function(&input);
        assert!(
            !rows.contains(&(
                "get_type".to_owned(),
                "ptr".to_owned(),
                "<emitted>".to_owned()
            )),
            "an escaping out-param local keeps the hold: {rows:?}"
        );
        let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
        assert!(super::verify::type_checks_str(&source));
    }
}

/// R406-6 finding A: the byte-view bridges at a `c_void` position, cell by
/// cell — the shared view under negative-write evidence, and the three
/// optional views — render the R130 bridge text with `None` mapped to null.
#[test]
fn w6v2_byte_view_void_templates_render_the_bridge() {
    use super::decision::{
        Decision,
        raw_boundary::{BridgeRender, BridgeTemplate, RawMutability, RawTargetType, template_for},
    };
    let target = |mutability| RawTargetType {
        rendered: "*mut core::ffi::c_void".to_owned(),
        pointee: "core::ffi::c_void".to_owned(),
        mutability,
        depth2: None,
    };
    let shared = Decision::Slice {
        mutable: false,
        uses: Vec::new(),
    };
    assert_eq!(
        template_for(&shared, &target(RawMutability::Mut), None, true),
        Ok(BridgeTemplate::VoidFromSliceCastMut)
    );
    assert!(template_for(&shared, &target(RawMutability::Mut), None, false).is_err());
    let cells = [
        (
            Decision::Opt {
                mutable: true,
                slice: true,
                uses: Vec::new(),
            },
            RawMutability::Mut,
            true,
            BridgeTemplate::OptSliceMutToVoidMut,
            "x.as_deref_mut().map_or(core::ptr::null_mut::<core::ffi::c_void>(), |slice| slice.as_mut_ptr().cast::<core::ffi::c_void>())",
        ),
        (
            Decision::Opt {
                mutable: false,
                slice: true,
                uses: Vec::new(),
            },
            RawMutability::Const,
            false,
            BridgeTemplate::OptSliceToVoidConst,
            "x.as_deref().map_or(core::ptr::null::<core::ffi::c_void>(), |slice| slice.as_ptr().cast::<core::ffi::c_void>())",
        ),
        (
            Decision::Opt {
                mutable: false,
                slice: true,
                uses: Vec::new(),
            },
            RawMutability::Mut,
            true,
            BridgeTemplate::OptSliceToVoidMut,
            "x.as_deref().map_or(core::ptr::null_mut::<core::ffi::c_void>(), |slice| slice.as_ptr().cast::<core::ffi::c_void>().cast_mut())",
        ),
    ];
    for (decision, mutability, negative_write, template, rendered) in cells {
        assert_eq!(
            template_for(&decision, &target(mutability), None, negative_write),
            Ok(template)
        );
        assert_eq!(
            template.render("x", mutability, false, Some("core::ffi::c_void")),
            Ok(BridgeRender::Edit(rendered.to_owned()))
        );
    }
    assert_eq!(
        BridgeTemplate::VoidFromSliceCastMut.render(
            "x",
            RawMutability::Mut,
            false,
            Some("core::ffi::c_void")
        ),
        Ok(BridgeRender::Edit(
            "x.as_ptr().cast::<core::ffi::c_void>().cast_mut()".to_owned()
        ))
    );
    // A shared optional view at a `*mut` position without the evidence stays closed.
    assert!(
        template_for(
            &Decision::Opt {
                mutable: false,
                slice: true,
                uses: Vec::new()
            },
            &target(RawMutability::Mut),
            None,
            false
        )
        .is_err()
    );
}
