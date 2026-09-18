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
        fabricated: false,
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
        fabricated: false,
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

/// A WRITE position of the row (`memcpy`'s destination) is not a read view:
/// the parameter stays held (the destination is the allocation's, not this
/// rule's).
#[test]
fn w6v2_foreign_copy_destination_position_stays_held() {
    let input = MEMDUP
        .replace(
            "memcpy(dest, src, size as u64);",
            "memcpy(src, dest, size as u64);",
        )
        .replace(
            "let mut dest = 0 as *mut core::ffi::c_void;",
            "let mut dest = 0 as *mut core::ffi::c_void; let _ = &mut dest;",
        );
    let rows = super::emit_tests::decisions_of(&input);
    assert!(
        !delivers(&rows, "src"),
        "a written position holds: {rows:?}"
    );
    assert!(
        reason(&rows, "src").starts_with("held:void-pointee"),
        "the hold keeps its family: {rows:?}"
    );
}

/// The emitted copy site: the shared byte view reaches `memcpy`'s source
/// position through the row's bridge, and nothing is fabricated.
#[test]
fn w6v2_foreign_copy_site_is_bridged_by_the_row() {
    let source = super::emit_tests::ast_emitted_source_of(MEMDUP).unwrap();
    assert!(!source.contains("FALLBACK_SLICE_EXTENT"), "{source}");
    let c = compact(&source);
    assert!(
        c.contains("memcpy(dest,src.as_deref().map_or(core::ptr::null::<core::ffi::c_void>(),|slice|slice.as_ptr().cast::<core::ffi::c_void>()),sizeasu64)"),
        "the row bridges the source position: {source}"
    );
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
/// `binn_list_get_value` (reassigned from `binn_ptr`) → :1254 `binn_ptr`.
/// R407-11: the two forwarders take the byte view and cross their raw seams
/// by the byte-view bridge; `binn_ptr` only RETURNS its argument, so the
/// returned-alias continuation makes `binn_list_get_value`'s own sinks the
/// ones that count (T2 under the waiver here: `offset` and `is_null` are open
/// calls in the walk). The leaf itself is reassigned (`ptr = binn_ptr(ptr)`)
/// and stays held — build 3's shadow shape.
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
fn w6v2_forwarders_over_a_returned_alias_chain_deliver() {
    let rows = by_function(CHAIN);
    for (function, parameter) in [
        ("binn_list_int32", "list"),
        ("binn_list_get", "ptr"),
        ("binn_get_ptr_type", "ptr"),
    ] {
        assert!(
            rows.contains(&(
                function.to_owned(),
                parameter.to_owned(),
                "<emitted>".to_owned()
            )),
            "{function}::{parameter} delivers: {rows:?}"
        );
    }
    for (function, parameter) in [("binn_list_get_value", "ptr"), ("binn_ptr", "ptr")] {
        assert!(
            rows.contains(&(
                function.to_owned(),
                parameter.to_owned(),
                "held:void-pointee".to_owned()
            )),
            "{function}::{parameter} (reassigned / returned) stays held: {rows:?}"
        );
    }
    let source = super::emit_tests::ast_emitted_source_of(CHAIN).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnbinn_list_int32(mutlist:&[u8],mutpos:i32)->i32{letmutvalue:i32=0;binn_list_get(list,pos,0x61asi32,&mutvalue);"),
        "the accessor forwards its view safe-to-safe: {source}"
    );
    assert!(
        c.contains("fnbinn_list_get(mutptr:&[u8],")
            && c.contains(
                "binn_list_get_value(ptr.as_ptr().cast::<core::ffi::c_void>().cast_mut(),pos,"
            ),
        "the middle forwarder crosses the raw seam by the byte-view bridge: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let mut buffer = [0xe0u8, 3, 9, 0, 0, 0, 0, 0];
        println!("{} {}", binn_list_int32(buffer.as_mut_ptr().cast(), 2), binn_list_int32(buffer.as_mut_ptr().cast(), 1));
    }}"#;
    let emitted_main = r#"fn main() { unsafe {
        let mut buffer = [0xe0u8, 3, 9, 0, 0, 0, 0, 0];
        println!("{} {}", binn_list_int32(&buffer[..], 2), binn_list_int32(&buffer[..], 1));
    }}"#;
    let original = run_binary(&format!("{CHAIN}\n{main}"));
    assert_eq!(original, b"9 3\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{emitted_main}")));
}

/// The full binn shape of the typed accessors (lib.rs:1389 `GetValue` storing
/// into `(*value).ptr`; :2267 `copy_value` → :2116 `copy_raw_value` storing
/// the source through `pdest`; :2493 `binn_list_get` reading `value.ptr` on
/// and passing its own `pvalue`; :2629 `binn_list_int32` with an `i32` local,
/// :2716 `binn_list_str` with a pointer local). The container pointer is
/// stored through three levels of output storage: the walk transposes each
/// level to the caller's own output parameter, follows the confined local's
/// pointer-field read, and discharges at the accessor whose out-storage is an
/// `i32` (never a pointer); `binn_list_str` returns its pointer local and
/// holds. The middle `binn_list_get::ptr` reads `value.ptr` on, which the
/// SITE-level descendant question (R283-3, K18' evidence — wave-6r's) does
/// not discharge: it stays held, and the accessor bridges its view at it.
const ACCESSORS: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct binn { pub header: i32, pub type_0: i32, pub size: i32, pub ptr: *mut core::ffi::c_void }
unsafe fn GetValue(mut p: *mut u8, mut value: *mut binn) -> i32 {
    (*value).type_0 = *p as i32;
    (*value).ptr = p as *mut core::ffi::c_void;
    return 1 as i32;
}
pub unsafe fn get_value(mut ptr: *mut core::ffi::c_void, mut pos: i32, mut value: *mut binn) -> i32 {
    if ptr.is_null() { return 0 as i32; }
    let mut p = ptr as *mut u8;
    return GetValue(p, value);
}
unsafe fn copy_raw_value(mut psource: *mut core::ffi::c_void, mut pdest: *mut core::ffi::c_void, mut data_store: i32) -> i32 {
    match data_store {
        96 => { *(pdest as *mut i32) = *(psource as *mut i32); }
        160 => { *(pdest as *mut *mut i8) = psource as *mut i8; }
        _ => return 0 as i32,
    }
    return 1 as i32;
}
unsafe fn copy_value(mut psource: *mut core::ffi::c_void, mut pdest: *mut core::ffi::c_void, mut data_store: i32) -> i32 {
    return copy_raw_value(psource, pdest, data_store);
}
pub unsafe fn binn_list_get(mut ptr: *mut core::ffi::c_void, mut pos: i32, mut type_0: i32, mut pvalue: *mut core::ffi::c_void) -> i32 {
    let mut value = binn { header: 0, type_0: 0, size: 0, ptr: 0 as *mut core::ffi::c_void };
    if get_value(ptr, pos, &mut value) == 0 as i32 { return 0 as i32; }
    if copy_value(value.ptr, pvalue, type_0) == 0 as i32 { return 0 as i32; }
    return 1 as i32;
}
pub unsafe fn binn_list_int32(mut list: *mut core::ffi::c_void, mut pos: i32) -> i32 {
    let mut value: i32 = 0;
    binn_list_get(list, pos, 96 as i32, &mut value as *mut i32 as *mut core::ffi::c_void);
    return value;
}
pub unsafe fn binn_list_str(mut list: *mut core::ffi::c_void, mut pos: i32) -> *mut i8 {
    let mut value: *mut i8 = 0 as *mut i8;
    binn_list_get(list, pos, 160 as i32, &mut value as *mut *mut i8 as *mut core::ffi::c_void);
    return value;
}
"#;

#[test]
fn w6v2_typed_accessor_discharges_through_three_output_levels() {
    let rows = by_function(ACCESSORS);
    assert!(
        rows.contains(&(
            "binn_list_int32".to_owned(),
            "list".to_owned(),
            "<emitted>".to_owned()
        )),
        "the int accessor's container view delivers: {rows:?}"
    );
    for (function, parameter) in [("binn_list_str", "list"), ("binn_list_get", "ptr")] {
        assert!(
            rows.contains(&(
                function.to_owned(),
                parameter.to_owned(),
                "held:void-pointee".to_owned()
            )),
            "{function}::{parameter} stays held: {rows:?}"
        );
    }
    let source = super::emit_tests::ast_emitted_source_of(ACCESSORS).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnbinn_list_int32(mutlist:&[u8],mutpos:i32)->i32")
            && c.contains(
                "binn_list_get(list.as_ptr().cast::<core::ffi::c_void>().cast_mut(),pos,96asi32,"
            ),
        "the accessor bridges its view at the held middle: {source}"
    );
    assert!(
        c.contains("fnbinn_list_str(mutlist:*mutcore::ffi::c_void,mutpos:i32)->*muti8"),
        "the string accessor stays raw: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let mut buffer = [7u8, 0, 0, 0, 0, 0, 0, 0];
        println!("{} {}", binn_list_int32(buffer.as_mut_ptr().cast(), 0), *binn_list_str(buffer.as_mut_ptr().cast(), 0));
    }}"#;
    let emitted_main = r#"fn main() { unsafe {
        let mut buffer = [7u8, 0, 0, 0, 0, 0, 0, 0];
        println!("{} {}", binn_list_int32(&buffer[..], 0), *binn_list_str(buffer.as_mut_ptr().cast(), 0));
    }}"#;
    let original = run_binary(&format!("{ACCESSORS}\n{main}"));
    assert_eq!(original, b"7 7\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{emitted_main}")));
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
/// stays held; so does one whose address is taken at a second call into a
/// reader that hands the loaded pointer out (relay wave-6v2/011: a READ-ONLY
/// reader at a second call is confined — `w6v2_iterator_*`).
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
        ) + "\nstatic mut KEPT2: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;\nunsafe fn touch(p: *mut binn) { KEPT2 = (*p).ptr; }",
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

/// The returned-alias continuation's own line: the alias a returning callee
/// hands back is THIS body's to account for — stored into a global, it holds.
#[test]
fn w6v2_returned_alias_stored_globally_keeps_the_hold() {
    let input = CHAIN.replace(
        "pub unsafe fn binn_list_get_value(mut ptr: *mut core::ffi::c_void, mut pos: i32, mut value: *mut binn) -> i32 {\n    ptr = binn_ptr(ptr);",
        "static mut KEPT: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;\npub unsafe fn binn_list_get_value(mut ptr: *mut core::ffi::c_void, mut pos: i32, mut value: *mut binn) -> i32 {\n    let q = binn_ptr(ptr); KEPT = q; ptr = binn_ptr(ptr);",
    );
    assert_ne!(input, CHAIN);
    let rows = by_function(&input);
    for (function, parameter) in [("binn_list_int32", "list"), ("binn_list_get", "ptr")] {
        assert!(
            !rows.contains(&(
                function.to_owned(),
                parameter.to_owned(),
                "<emitted>".to_owned()
            )),
            "{function}::{parameter} holds behind a globally stored returned alias: {rows:?}"
        );
    }
}

/// R410-3 §1: the descendant discharge of the R283-3 arm needs the callee's
/// BODY, not its signature. `keep` looks harmless by signature (returns an
/// `i32`; its only output storage is the confined `out`) but stores a pointer
/// DERIVED from the argument (`p.cast()`) into a global: a shared view bridged
/// into it would leave `SharedReadOnly` provenance in `KEPT`, UB on any later
/// write. The subject stays held; with a clean body the confined out-param
/// discharges the sink and it delivers. (An OPEN foreign call in the callee
/// is the standing T2 waiver path — retention-unknown — not this arm's.)
const KEEP: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct binn { pub header: i32, pub type_0: i32, pub size: i32, pub ptr: *mut core::ffi::c_void }
static mut KEPT: *mut u8 = 0 as *mut u8;
extern "C" { fn stash(p: *mut i8); }
unsafe fn keep(mut p: *mut u8, mut out: *mut binn) -> i32 {
    (*out).type_0 = *p as i32;
    (*out).ptr = p as *mut core::ffi::c_void;
    //ESCAPE//
    return 1 as i32;
}
pub unsafe fn probe(mut s: *mut u8) -> i32 {
    let mut out = binn { header: 0, type_0: 0, size: 0, ptr: 0 as *mut core::ffi::c_void };
    if keep(s, &mut out) == 0 as i32 { return 0 as i32; }
    return out.type_0;
}
"#;

#[test]
fn w6v2_descendant_discharge_needs_the_callee_body() {
    for (name, escape) in [("derived-global-store", "KEPT = p.cast::<i8>() as *mut u8;")] {
        let input = KEEP.replace("//ESCAPE//", escape);
        let rows = by_function(&input);
        assert!(
            !rows.contains(&("probe".to_owned(), "s".to_owned(), "<emitted>".to_owned())),
            "{name}: the body has no evidence of confinement — held: {rows:?}"
        );
        let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
        assert!(super::verify::type_checks_str(&source));
    }
    let clean = KEEP.replace("//ESCAPE//", "");
    let rows = by_function(&clean);
    assert!(
        rows.contains(&("probe".to_owned(), "s".to_owned(), "<emitted>".to_owned())),
        "with a clean body the confined out-param discharges: {rows:?}"
    );
}

/// R410-2(d): a width reader (`return *(p as *const u32)`) is wave-6b's
/// region shape; this lane's typed-width rule yields so the region wins.
#[test]
fn w6v2_width_reader_yields_to_the_region() {
    let input = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
unsafe fn BrotliUnalignedRead32(mut p: *const core::ffi::c_void) -> u32 {
    return *(p as *const u32);
}
unsafe fn tail(mut p: *const core::ffi::c_void) -> u64 {
    *(p as *const u32) as u64
}
"#;
    // The region (wave-6b) may deliver them on a composed line; what this
    // lane asserts is that ITS rule minted no contract for either.
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(input), |tcx| {
        let table = super::decide_table(tcx).expect("table");
        let minted = table
            .counted_void
            .keys()
            .map(|(f, _)| tcx.def_path_str(f.to_def_id()))
            .collect::<Vec<_>>();
        assert!(
            minted.is_empty(),
            "the width readers are the region's: {minted:?}"
        );
    })
    .expect("compiles");
}

/// binn.rs:441 `binn_copy`: `old_ptr = binn_ptr(old)` — `binn_ptr` only RETURNS
/// its argument and the caller USES the result (reads the header through
/// it). R412-7: the site is T2 `ReturnedAliasUsed` under the named waiver —
/// the tier a contract callee with `returns_alias_of` gets — and `old`
/// takes the byte view; the alias's fate is the caller's own row (the
/// returned-alias continuation), which here reads and copies only.
const COPY_OLD: &str = r#"
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
pub unsafe fn binn_copy(mut old: *mut core::ffi::c_void) -> i32 {
    let mut old_ptr = binn_ptr(old) as *mut u8;
    if old_ptr.is_null() { return 0 as i32; }
    return *old_ptr as i32 + *old_ptr.offset(1) as i32;
}
"#;

#[test]
fn w6v2_used_returned_alias_site_is_t2() {
    let rows = by_function(COPY_OLD);
    assert!(
        rows.contains(&(
            "binn_copy".to_owned(),
            "old".to_owned(),
            "<emitted>".to_owned()
        )),
        "the caller of a returning callee delivers its view: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(COPY_OLD).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnbinn_copy(mutold:&[u8])->i32")
            && c.contains("binn_ptr(old.as_ptr().cast::<core::ffi::c_void>().cast_mut())"),
        "the bridge at the returning callee: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let main = r#"fn main() { unsafe {
        let mut buffer = [0xe0u8, 3, 9, 0, 0, 0, 0, 0];
        println!("{}", binn_copy(buffer.as_mut_ptr().cast()));
    }}"#;
    let emitted_main = r#"fn main() { unsafe {
        let mut buffer = [0xe0u8, 3, 9, 0, 0, 0, 0, 0];
        println!("{}", binn_copy(&buffer[..]));
    }}"#;
    let original = run_binary(&format!("{COPY_OLD}\n{main}"));
    assert_eq!(original, b"227\n".to_vec());
    assert_eq!(original, run_binary(&format!("{source}\n{emitted_main}")));
}

/// The tier is for a callee that ONLY returns the argument: one that also
/// stores it into a global keeps positive retention at the site.
#[test]
fn w6v2_returning_callee_that_also_stores_keeps_the_hold() {
    let input = COPY_OLD.replace(
        "        2 => return ptr,",
        "        2 => { KEPT = ptr; return ptr; }",
    ).replace("pub unsafe fn binn_ptr", "static mut KEPT: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;\npub unsafe fn binn_ptr");
    assert_ne!(input, COPY_OLD);
    let rows = by_function(&input);
    assert!(
        !rows.contains(&(
            "binn_copy".to_owned(),
            "old".to_owned(),
            "<emitted>".to_owned()
        )),
        "a callee that stores the argument is not Return-only: {rows:?}"
    );
}

/// The descendant question stays: a caller that WRITES through the returned
/// alias of a shared view is the write-through-shared-view hazard and holds.
#[test]
fn w6v2_write_through_returned_alias_keeps_the_hold() {
    let input = COPY_OLD.replace(
        "    return *old_ptr as i32 + *old_ptr.offset(1) as i32;",
        "    *old_ptr = 1;\n    return *old_ptr as i32;",
    );
    assert_ne!(input, COPY_OLD);
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    let c = compact(&source);
    // Either the view is held, or the analysis made it MUTABLE (the write
    // through the alias is a write through the subject) — never a shared
    // view with a write behind it.
    assert!(
        c.contains("fnbinn_copy(mutold:*mutcore::ffi::c_void)->i32")
            || c.contains("fnbinn_copy(mutold:&mut[core::mem::MaybeUninit<u8>])->i32"),
        "a write through the returned alias is never behind a shared view: {source}"
    );
    assert!(!c.contains("fnbinn_copy(mutold:&[u8])"), "{source}");
    assert!(super::verify::type_checks_str(&source));
}

/// brotli `InitBlockSplitIterator` / `BlockSplitIteratorNext` (wave-6r 016
/// claim 7, relay 011): the callee stores the shared argument into the
/// caller's frame-local iterator; the local's only other uses are a second
/// `&mut` into a reader that LOADS the stored pointer and reads through it,
/// and non-pointer field reads.
const ITERATOR: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, static_mut_refs)]
pub struct Split { types: *const u8, lengths: *const u32, num: usize }
pub struct It { split_: *const Split, idx_: usize, type_: usize, length_: usize }
pub static mut KEEP: *const Split = core::ptr::null();
unsafe fn init(self_0: *mut It, split: *const Split) {
    (*self_0).split_ = split;
    (*self_0).idx_ = 0;
    (*self_0).type_ = 0;
    (*self_0).length_ = if !((*split).lengths).is_null() { *((*split).lengths).offset(0) } else { 0 } as usize;
}
unsafe fn next(self_0: *mut It) {
    if (*self_0).length_ == 0 {
        (*self_0).idx_ += 1;
        (*self_0).type_ = *((*(*self_0).split_).types).offset((*self_0).idx_ as isize) as usize;
        (*self_0).length_ = *((*(*self_0).split_).lengths).offset((*self_0).idx_ as isize) as usize;
    }
    (*self_0).length_ -= 1;
}
pub unsafe fn build(split: *const Split, n: usize) -> usize {
    let mut it = It { split_: core::ptr::null(), idx_: 0, type_: 0, length_: 0 };
    init(&mut it, split);
    let mut acc = 0usize;
    let mut i = 0usize;
    while i < n {
        next(&mut it);
        acc += it.type_;
        i += 1;
    }
    acc
}
"#;

fn iterator_site_rows(input: &str) -> Vec<String> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        ctx.raw_boundary
            .receipts_tsv()
            .lines()
            .filter(|l| l.starts_with("build\t") && l.contains("\tinit\t1\t"))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    })
    .unwrap()
}

/// The `build → init` arg-1 site is T1: the store lands in `it`, which is
/// stack-confined — its second `&mut` goes to `next`, whose loads of `split_`
/// are read through only — and the callee is descendant-free modulo that
/// certified output storage.
#[test]
fn w6v2_iterator_store_into_a_read_only_reader_local_is_t1() {
    let rows = by_function(ITERATOR);
    let site = iterator_site_rows(ITERATOR);
    assert!(
        site.iter().any(|l| l.contains("\tT1\t")),
        "the init site is T1: {site:?}\n{rows:?}"
    );
    let decisions = super::emit_tests::decisions_of(ITERATOR);
    assert!(
        delivers(&decisions, "split"),
        "build::split delivers: {decisions:?}"
    );
}

/// The reader hands the loaded pointer out (a global store): the second
/// `&mut it` is not confined and the site keeps its hold.
#[test]
fn w6v2_iterator_reader_that_keeps_the_loaded_field_holds() {
    let input = ITERATOR.replace(
        "    (*self_0).length_ -= 1;\n}\npub unsafe fn build",
        "    (*self_0).length_ -= 1;\n    KEEP = (*self_0).split_;\n}\npub unsafe fn build",
    );
    assert_ne!(input, ITERATOR);
    let site = iterator_site_rows(&input);
    assert!(
        !site.iter().any(|l| l.contains("\tT1\t")),
        "a kept load is not confined: {site:?}"
    );
}

/// The callee stores the argument beside the output storage (a global): the
/// residual is not descendant-free modulo the output and the site holds.
#[test]
fn w6v2_iterator_callee_with_a_second_sink_holds() {
    let input = ITERATOR.replace(
        "    (*self_0).split_ = split;\n    (*self_0).idx_ = 0;",
        "    (*self_0).split_ = split;\n    KEEP = split;\n    (*self_0).idx_ = 0;",
    );
    assert_ne!(input, ITERATOR);
    let site = iterator_site_rows(&input);
    assert!(
        !site.iter().any(|l| l.contains("\tT1\t")),
        "a second sink keeps the hold: {site:?}"
    );
}

/// The caller reads an INTEGER field of the local (`it.type_`), so the callee
/// may not write an integer image of the argument into it: wave-6r's scan
/// modulo the output refuses the cast and the site holds.
#[test]
fn w6v2_iterator_callee_that_writes_an_integer_image_holds() {
    let input = ITERATOR.replace(
        "    (*self_0).type_ = 0;\n",
        "    (*self_0).type_ = split as usize;\n",
    );
    assert_ne!(input, ITERATOR);
    let site = iterator_site_rows(&input);
    assert!(
        !site.iter().any(|l| l.contains("\tT1\t")),
        "an integer image in a read field keeps the hold: {site:?}"
    );
}

/// The callee reads through a DERIVED alias of the argument (`split.offset(0)`):
/// T1, not the T2 waiver. Two admissible readings (R217-2(a)): where the core
/// call is an open step for the certificate the residual is unknown and the
/// body scan modulo the output discharges it (`descendant-free-modulo-output`);
/// where wave-6r's landed hooks 3/4 call the same step a known no-retain
/// (batch 8 `6f521bfc` / `32f42251`, restored on the composition by their
/// core-method seam) the residual is no-retain and the stack-storage
/// certificate discharges it one tier earlier.
#[test]
fn w6v2_iterator_callee_reading_through_a_derived_alias_is_t1() {
    let input = ITERATOR.replace(
        "    (*self_0).idx_ = 0;\n    (*self_0).type_ = 0;\n",
        "    (*self_0).idx_ = 0;\n    let q = split.offset(0);\n    (*self_0).type_ = (*q).num;\n",
    );
    assert_ne!(input, ITERATOR);
    let site = iterator_site_rows(&input);
    assert!(
        site.iter().any(|l| l.contains("\tT1\t")
            && (l.contains("descendant-free-modulo-output")
                || l.contains("stack-storage-certificate"))),
        "the derived read is discharged by the scan or the certificate: {site:?}"
    );
}

/// R416-11: an integer IMAGE of a reachable pointer (`p as usize`) is a
/// hand-out for the retention walk — an exposed address is an alias under the
/// permissive provenance model — so a callee that stores it is never
/// `no-retain`; a callee that only compares the image is not certified either
/// (the walk cannot follow an integer).
#[test]
fn w6v2_integer_image_of_the_argument_is_an_open_step() {
    let input = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, static_mut_refs)]
pub static mut KEPT: usize = 0;
pub unsafe fn keep(p: *mut u8) { let image = p as usize; KEPT = image; }
pub unsafe fn compare(p: *mut u8, q: *mut u8) -> bool { (p as usize) < (q as usize) }
pub unsafe fn read(p: *mut u8) -> u8 { *p }
"#;
    let rows = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        ctx.retention.to_tsv()
    })
    .expect("input type-checks");
    let row = |function: &str, index: &str| {
        rows.lines()
            .find(|l| {
                l.starts_with(&format!("{function}\t")) && l.contains(&format!("\t{index}\t"))
            })
            .map(str::to_owned)
            .unwrap_or_else(|| panic!("{function} arg {index} row: {rows}"))
    };
    assert!(
        !row("keep", "0").contains("\tno-retain\t") && row("keep", "0").contains("integer image"),
        "{}",
        row("keep", "0")
    );
    assert!(
        !row("compare", "0").contains("\tno-retain\t"),
        "{}",
        row("compare", "0")
    );
    assert!(
        !row("compare", "1").contains("\tno-retain\t"),
        "{}",
        row("compare", "1")
    );
    assert!(
        row("read", "0").contains("\tno-retain\t"),
        "{}",
        row("read", "0")
    );
}

/// The tag `core-pointer-method` is what lets `descendant_free` accept an open
/// core call: the derived pointer is an alias whose sinks the walk sees. That
/// premise fails for a derivation the function RETURNS — wave-6r's `070164b9`
/// gives it no alias edge, so its hand-out through the return is invisible —
/// and the step must therefore drop the tag.
#[test]
fn w6v2_returned_derivation_is_an_untagged_open_step() {
    let input = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub unsafe fn dup(q: *const i32) -> *mut i32 { q.cast_mut() }
pub unsafe fn read_only(q: *const i32) -> i32 { *q.offset(1) }
"#;
    let rows = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        ctx.retention.to_tsv()
    })
    .expect("input type-checks");
    let row = |function: &str| {
        rows.lines()
            .find(|l| l.starts_with(&format!("{function}\t")))
            .map(str::to_owned)
            .unwrap_or_else(|| panic!("{function} row: {rows}"))
    };
    assert!(
        !row("dup").contains("core-pointer-method") && row("dup").contains("returned-derivation"),
        "{}",
        row("dup")
    );
    // The control: a derivation that is only read through keeps the tag (and,
    // on this line, wave-6r's known-no-retain reading of the same call).
    assert!(
        row("read_only").contains("core-pointer-method"),
        "{}",
        row("read_only")
    );
}

/// binn `copy_int_value` (batch-9 census, report 014): the typed-width rule
/// delivers the callee's `psource` as `&[u8]`, and its RAW callers pass a
/// field read (`copy_int_value((*value).ptr, ..)`) or forward their own raw
/// parameter. Every such site must route (the raw twin, or a bridge) or the
/// class must drop: two of the six sites kept the raw argument against the
/// safe formal, which is `E0308` at verify — the function reverted and took
/// its whole closure partition (50 functions, 18 delivered chain heads) with
/// it.
const COPY_INT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct binn { pub type_0: i32, pub ptr: *mut core::ffi::c_void }
unsafe fn int_type(t: i32) -> i32 { if t & 0x10 != 0 { 22 } else { 11 } }
unsafe extern "C" fn copy_int_value(mut psource: *mut core::ffi::c_void,
    mut pdest: *mut core::ffi::c_void, mut source_type: i32,
    mut dest_type: i32) -> i32 {
    let mut vuint64 = 0 as i32 as u64;
    let mut vi64 = 0 as i32 as i64;
    match source_type {
        33 => { vi64 = *(psource as *mut i8) as i64; }
        65 => { vi64 = *(psource as *mut i16) as i64; }
        97 => { vi64 = *(psource as *mut i32) as i64; }
        129 => { vi64 = *(psource as *mut i64); }
        32 => {
            vuint64 = *(psource as *mut u8) as u64;
        }
        64 => {
            vuint64 = *(psource as *mut u16) as u64;
        }
        96 => { vuint64 = *(psource as *mut u32) as u64; }
        128 => { vuint64 = *(psource as *mut u64); }
        _ => return 0 as i32,
    }
    if int_type(source_type) == 22 as i32 &&
            int_type(dest_type) == 11 as i32 {
        if vuint64 >
                9223372036854775807 as i64 as u64 {
            return 0 as i32;
        }
        vi64 = vuint64 as i64;
    } else if int_type(source_type) == 11 as i32 &&
            int_type(dest_type) == 22 as i32 {
        if vi64 < 0 as i32 as i64 {
            return 0 as i32;
        }
        vuint64 = vi64 as u64;
    }
    match dest_type {
        33 => {
            if vi64 < -(128 as i32) as i64 ||
                    vi64 > 127 as i32 as i64 {
                return 0 as i32;
            }
            *(pdest as *mut i8) = vi64 as i8;
        }
        65 => {
            if vi64 <
                        (-(32767 as i32) - 1 as i32) as
                            i64 ||
                    vi64 > 32767 as i32 as i64 {
                return 0 as i32;
            }
            *(pdest as *mut i16) = vi64 as i16;
        }
        97 => {
            if vi64 <
                        (-(2147483647 as i32) - 1 as i32) as
                            i64 ||
                    vi64 > 2147483647 as i32 as i64 {
                return 0 as i32;
            }
            *(pdest as *mut i32) = vi64 as i32;
        }
        129 => { *(pdest as *mut i64) = vi64; }
        32 => {
            if vuint64 > 255 as i32 as u64 {
                return 0 as i32;
            }
            *(pdest as *mut u8) = vuint64 as u8;
        }
        64 => {
            if vuint64 > 65535 as i32 as u64 {
                return 0 as i32;
            }
            *(pdest as *mut u16) = vuint64 as u16;
        }
        96 => {
            if vuint64 > 4294967295 as u32 as u64
                {
                return 0 as i32;
            }
            *(pdest as *mut u32) = vuint64 as u32;
        }
        128 => { *(pdest as *mut u64) = vuint64; }
        _ => return 0 as i32,
    }
    return 1 as i32;
}
unsafe extern "C" { fn opaque_store(p: *mut core::ffi::c_void); }
unsafe fn copy_value(mut psource: *mut core::ffi::c_void, mut pdest: *mut core::ffi::c_void, mut source_type: i32, mut dest_type: i32) -> i32 {
    if source_type == 0 { opaque_store(psource); return 0; }
    return copy_int_value(psource, pdest, source_type, dest_type);
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn binn_get_int32(mut value: *mut binn, mut pint: *mut i32) -> i32 {
    if value.is_null() || pint.is_null() { return 0; }
    return copy_int_value((*value).ptr, pint as *mut core::ffi::c_void, (*value).type_0, 0x61);
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn binn_get_int64(mut value: *mut binn, mut pint: *mut i64) -> i32 {
    if value.is_null() || pint.is_null() { return 0; }
    return copy_int_value((*value).ptr, pint as *mut core::ffi::c_void, (*value).type_0, 0x81);
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn binn_get_double(mut value: *mut binn, mut pfloat: *mut f64) -> i32 {
    let mut vint: i64 = 0;
    if value.is_null() || pfloat.is_null() { return 0; }
    if copy_int_value((*value).ptr, &mut vint as *mut i64 as *mut core::ffi::c_void, (*value).type_0, 0x81) == 0 {
        return 0;
    }
    *pfloat = vint as f64;
    1
}
"#;

/// The COLLISION the corpus shows (report 015, handed to wave-5d): the A5
/// proof site for argument 1 (`pint as *mut c_void`, a cast of a delivered
/// `Option<&mut T>` local — `cast-of-local` / `opt-ref-mut` / verdict
/// `overlapping` / T2) renders a raw view over the WHOLE call, while the
/// counted-void seam has planned an argument adapter for argument 0 inside
/// that same call. Whoever renders last wins, and in the corpus the adapter
/// is the one discarded.
#[test]
fn w6v2_counted_call_under_an_a5_raw_view_is_the_collision() {
    let (proofs, calls) = ::utils::compilation::run_compiler_on_str(COPY_INT, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let proofs = ctx
            .raw_boundary_artifacts
            .a5_proof_site_fallback_rows
            .iter()
            .map(|row| format!("{row:?}"))
            .collect::<Vec<_>>();
        let calls = table
            .seams
            .counted_void_calls
            .iter()
            .map(|call| {
                format!(
                    "{}->{} {:?} {:?}",
                    tcx.def_path_str(call.caller.to_def_id()),
                    tcx.def_path_str(call.callee.to_def_id()),
                    call.route,
                    call.call_span
                )
            })
            .collect::<Vec<_>>();
        (proofs, calls)
    })
    .expect("input type-checks");
    println!("A5PROOFS {proofs:#?}\nCOUNTEDCALLS {calls:#?}");
    assert!(
        !calls.is_empty(),
        "the counted-void seam plans a call adapter: {calls:?}"
    );
}

#[test]
fn w6v2_delivered_callee_routes_every_raw_caller_site() {
    let rows = by_function(COPY_INT);
    let source = super::emit_tests::ast_emitted_source_of(COPY_INT).unwrap();
    assert!(
        super::verify::type_checks_str(&source),
        "every raw site routes (twin or bridge) or the class drops: {rows:?}\n{source}"
    );
}

/// R451-7 (relay 023, for wave-6r's seam guard): the caller-level fact.
/// `get_value` retains its `ptr` by storing it through the out-parameter
/// `value` — its retention ROW says `retains`, which is what the seam guard
/// reads today. The fact says the position is nonetheless SETTLED: every call
/// supplies `value` from a frame-confined caller local, so the store dies with
/// the caller's frame. The control is the same callee at a call whose
/// out-parameter escapes: one unconfined call makes the fact false.
#[test]
fn w6v2_output_storage_settled_at_every_call() {
    let settled = |input: &str| {
        ::utils::compilation::run_compiler_on_str(input, |tcx| {
            let (_, ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    super::A5Mode::PreciseReplay,
                    Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .expect("native decisions");
            let callee = tcx
                .hir_body_owners()
                .find(|owner| tcx.def_path_str(owner.to_def_id()).ends_with("get_value"))
                .expect("the callee exists");
            (
                // R453-6: the seam guard's channel — the fact is asked of the
                // summaries, exactly as `returned_alias_settled` is, with no
                // site facts at the call.
                ctx.retention.output_storage_settled(callee, 0),
                ctx.retention
                    .to_tsv()
                    .lines()
                    .find(|line| line.starts_with("get_value\t"))
                    .unwrap_or("<no row>")
                    .to_owned(),
            )
        })
        .expect("input type-checks")
    };
    let (confined, row) = settled(CONFINED);
    assert!(
        row.contains("retains"),
        "the callee's ROW is what the seam guard reads: {row}"
    );
    assert!(
        confined,
        "every call supplies a frame-confined output: {row}"
    );
    // The control: a second caller whose out-parameter is a global.
    let escaping = CONFINED.replace(
        "pub unsafe fn get_type(",
        "pub static mut KEPT: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;\n\
         pub unsafe fn leak(mut ptr: *mut u8) -> i32 {\n\
             let mut value = binn { header: 0, type_0: 0, size: 0, ptr: 0 as *mut core::ffi::c_void };\n\
             if get_value(ptr, 0, &mut value) == 0 as i32 { return 0 as i32; }\n\
             KEPT = value.ptr;\n\
             return 1 as i32;\n\
         }\n\
         pub unsafe fn get_type(",
    );
    assert_ne!(escaping, CONFINED);
    let (escaping, row) = settled(&escaping);
    assert!(
        !escaping,
        "one unconfined call makes the position unsettled: {row}"
    );
    // A position with NO inventoried call settles nothing: the fact is a claim
    // about calls, and there is no evidence where there is no call.
    let uncalled = CONFINED.replace(
        "pub unsafe fn get_type(mut ptr: *mut u8, mut pos: i32) -> i32 {\n    let mut value = binn { header: 0, type_0: 0, size: 0, ptr: 0 as *mut core::ffi::c_void };\n    if get_value(ptr, pos, &mut value) == 0 as i32 { return 0 as i32; }\n    return value.type_0;\n}",
        "pub unsafe fn get_type(mut ptr: *mut u8, mut pos: i32) -> i32 { return *ptr as i32 + pos; }",
    );
    assert_ne!(uncalled, CONFINED);
    let (uncalled, row) = settled(&uncalled);
    assert!(!uncalled, "no call, nothing settled: {row}");
}

/// R457-5 (the seat's ruling on report 023): binn's `IsValidBinnHeader` walks
/// the buffer by an extent the program never states — its own `plimit` is built
/// from a positive `*psize`, and every call passes null or zero. The view takes
/// the ruled fallback extent with a per-site receipt; the write positions do
/// not.
const HEADER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn IsValidBinnHeader(mut pbuf: *mut core::ffi::c_void, mut ptype: *mut i32,
    mut psize: *mut i32) -> i32 {
    let mut p = 0 as *mut u8;
    let mut byte: u8 = 0;
    if pbuf.is_null() { return 0; }
    p = pbuf as *mut u8;
    byte = *p;
    p = p.offset(1);
    if byte as i32 & 0xe0 != 0xe0 { return 0; }
    if !ptype.is_null() { *ptype = byte as i32; }
    if !psize.is_null() { *psize = *p as i32; }
    return p.offset_from(pbuf as *mut u8) as i32;
}
pub unsafe fn binn_buf_type(mut pbuf: *mut core::ffi::c_void) -> i32 {
    let mut type_0: i32 = 0;
    if IsValidBinnHeader(pbuf, &mut type_0, 0 as *mut i32) == 0 { return 0; }
    return type_0;
}
"#;

/// binn's real header reader hands its cursor to a local callee that reads
/// through it (`copy_be32(&mut int32 as *mut u32, p as *mut u32)`). That is a
/// read-through at a local callee, which wave-6r's MIR scan decides — and the
/// scan is a pure function of `tcx` and the program's functions, so the
/// contract chain can ask it directly (report 025: this instance of the
/// staging wall is not one).
const HEADER_WITH_CALLEE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn copy_be32(mut pdest: *mut u32, mut psource: *mut u32) {
    let mut source = psource as *mut u8;
    let mut dest = pdest as *mut u8;
    *dest.offset(0) = *source.offset(3);
    *dest.offset(1) = *source.offset(2);
    *dest.offset(2) = *source.offset(1);
    *dest.offset(3) = *source.offset(0);
}
pub unsafe fn IsValidBinnHeader(mut pbuf: *mut core::ffi::c_void, mut ptype: *mut i32,
    mut psize: *mut i32) -> i32 {
    let mut p = 0 as *mut u8;
    let mut int32: u32 = 0;
    let mut byte: u8 = 0;
    if pbuf.is_null() { return 0; }
    p = pbuf as *mut u8;
    byte = *p;
    p = p.offset(1);
    if byte as i32 & 0xe0 != 0xe0 { return 0; }
    copy_be32(&mut int32 as *mut u32, p as *mut u32);
    p = p.offset(4);
    if !ptype.is_null() { *ptype = byte as i32; }
    if !psize.is_null() { *psize = int32 as i32; }
    return p.offset_from(pbuf as *mut u8) as i32;
}
pub unsafe fn binn_buf_type(mut pbuf: *mut core::ffi::c_void) -> i32 {
    let mut type_0: i32 = 0;
    if IsValidBinnHeader(pbuf, &mut type_0, 0 as *mut i32) == 0 { return 0; }
    return type_0;
}
"#;

#[test]
fn w6v2_header_path_admits_a_cursor_read_through_at_a_local_callee() {
    // This family no longer holds the shape: the cursor's local callee reads
    // through and hands nothing back. In THIS reduction the analysis then
    // settles the subject `kind-raw` (a fixture artefact: the corpus's own
    // `IsValidBinnHeader` is not analysis-raw), so what the witness pins is the
    // family's verdict, and the corpus census is the delivery evidence —
    // report 025: binn's `held:void-pointee` 79 -> 75 with this arm.
    let rows = by_function(HEADER_WITH_CALLEE);
    assert!(
        !rows.contains(&(
            "IsValidBinnHeader".to_owned(),
            "pbuf".to_owned(),
            "held:void-pointee".to_owned()
        )),
        "the read-through callee lifts this family's hold: {rows:?}"
    );
}

/// The control: the same call, but the callee KEEPS what it is given. The
/// cursor escapes through it and the hold stands.
#[test]
fn w6v2_header_path_refuses_a_cursor_a_callee_keeps() {
    let input = HEADER_WITH_CALLEE.replace(
        "pub unsafe fn copy_be32(mut pdest: *mut u32, mut psource: *mut u32) {
    let mut source = psource as *mut u8;",
        "pub static mut KEPT: *mut u32 = 0 as *mut u32;
pub unsafe fn copy_be32(mut pdest: *mut u32, mut psource: *mut u32) {
    KEPT = psource;
    let mut source = psource as *mut u8;",
    );
    assert_ne!(input, HEADER_WITH_CALLEE);
    let rows = by_function(&input);
    assert!(
        !rows.contains(&(
            "IsValidBinnHeader".to_owned(),
            "pbuf".to_owned(),
            "<emitted>".to_owned()
        )),
        "a callee that keeps the cursor holds the parameter: {rows:?}"
    );
}

/// **R464-3 — the call-site fallback extent.** A RAW caller of a header-path
/// view has no length to supply: the callee's count is the ruled fallback
/// extent, not one of the call's arguments. Report 026 measured this as binn's
/// second gate (`seam-len-unknown` at `binn_buf_{type,count,size}(ptr)`), and it
/// is R457-5's own condition one layer out — so the same waiver applies, with
/// the same per-site receipt.
const HEADER_WITH_RAW_CALLER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct binn { pub header: i32, pub type_0: i32 }
pub unsafe fn IsValidBinnHeader(mut pbuf: *mut core::ffi::c_void, mut ptype: *mut i32,
    mut psize: *mut i32) -> i32 {
    let mut p = 0 as *mut u8;
    let mut byte: u8 = 0;
    if pbuf.is_null() { return 0; }
    p = pbuf as *mut u8;
    byte = *p;
    p = p.offset(1);
    if byte as i32 & 0xe0 != 0xe0 { return 0; }
    if !ptype.is_null() { *ptype = byte as i32; }
    if !psize.is_null() { *psize = *p as i32; }
    return p.offset_from(pbuf as *mut u8) as i32;
}
pub unsafe fn binn_buf_type(mut pbuf: *mut core::ffi::c_void) -> i32 {
    let mut type_0: i32 = 0;
    if IsValidBinnHeader(pbuf, &mut type_0, 0 as *mut i32) == 0 { return 0; }
    return type_0;
}
pub unsafe fn binn_type(mut ptr: *mut core::ffi::c_void) -> i32 {
    let mut item = 0 as *mut binn;
    if ptr.is_null() { return -1; }
    item = ptr as *mut binn;
    if (*item).header == 0x1f22b11f { return (*item).type_0; }
    return binn_buf_type(ptr);
}
"#;

#[test]
fn w6v2_raw_caller_of_a_header_view_takes_the_fallback_extent() {
    let source = super::emit_tests::ast_emitted_source_of(HEADER_WITH_RAW_CALLER).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnbinn_buf_type(mutpbuf:Option<&[u8]>"),
        "the callee still delivers the view: {source}"
    );
    // The caller stays raw (it casts to `binn`), so the call must BRIDGE, and
    // the only extent available is the ruled fallback one.
    assert!(
        source.contains("crate::FALLBACK_SLICE_EXTENT"),
        "the raw caller's bridge takes the named fallback extent: {source}"
    );
    // The number appears exactly once, in the const ITEM the emitter inserts;
    // the call site names the path, never the literal.
    assert_eq!(
        source.matches("1024").count(),
        1,
        "the extent is the named const, never an inlined number: {source}"
    );
    assert!(
        c.contains("(crate::FALLBACK_SLICE_EXTENT)asusize"),
        "the bridge reads the count through the named path: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// **The control.** The waiver is for READ positions. A fabricated extent on a
/// `&mut [u8]` claims writable bytes, which is a different and worse claim than
/// a read, so a mutable counted view with no evidence-backed length keeps its
/// raw caller raw.
#[test]
fn w6v2_raw_caller_of_a_written_view_is_refused_the_fallback_extent() {
    let input = HEADER_WITH_RAW_CALLER
        .replace("if !psize.is_null() { *psize = *p as i32; }", "*p = 0;")
        .replace("byte = *p;", "byte = *p; *p = byte;");
    assert_ne!(input, HEADER_WITH_RAW_CALLER);
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        !source.contains("crate::FALLBACK_SLICE_EXTENT"),
        "a written-through cursor takes no fabricated extent: {source}"
    );
}

#[test]
fn w6v2_header_path_takes_the_ruled_fallback_extent() {
    let rows = by_function(HEADER);
    assert!(
        rows.contains(&(
            "IsValidBinnHeader".to_owned(),
            "pbuf".to_owned(),
            "<emitted>".to_owned()
        )),
        "the header reader delivers under the waiver: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(HEADER).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnIsValidBinnHeader(mutpbuf:Option<&[u8]>"),
        "the view is a nullable byte view: {source}"
    );
    // The forward-only rule carries the chain: `binn_buf_type` takes the view
    // too, so this reduction has no RAW caller left and therefore no bridge to
    // fabricate. The fabricated extent itself is a corpus fact (report 024's
    // census), not something this fixture can show.
    assert!(
        c.contains("fnbinn_buf_type(mutpbuf:Option<&[u8]>"),
        "the chain carries the view: {source}"
    );
    assert!(
        !source.contains("1024"),
        "no extent is ever inlined as a number: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// The waiver is for the READ path only, and for a BYTE cursor only. A write
/// through the parameter's own cast claims writable bytes, which the fallback
/// extent may not do; a cast to a wider element is not a byte view at all.
#[test]
fn w6v2_header_path_refuses_a_write_and_a_wide_cursor() {
    let held = |input: &str, what: &str| {
        let rows = by_function(input);
        assert!(
            !rows.contains(&(
                "IsValidBinnHeader".to_owned(),
                "pbuf".to_owned(),
                "<emitted>".to_owned()
            )),
            "{what}: {rows:?}"
        );
    };
    // The write is through the parameter's own cast, so only the read-path
    // guard can refuse it.
    let written = HEADER.replace(
        "    byte = *p;\n",
        "    byte = *p;\n    *(pbuf as *mut u8) = 0;\n",
    );
    assert_ne!(written, HEADER);
    held(&written, "a write through the header buffer keeps the hold");
    // A wide cursor: the cast is to `*mut u32`, so the view would not be a
    // byte view; only the element-size guard refuses it.
    let wide = HEADER
        .replace("let mut p = 0 as *mut u8;", "let mut p = 0 as *mut u32;")
        .replace("p = pbuf as *mut u8;", "p = pbuf as *mut u32;")
        .replace("byte = *p;", "byte = *p as u8;")
        .replace(
            "if !psize.is_null() { *psize = *p as i32; }",
            "if !psize.is_null() { *psize = *p as i32; }",
        )
        .replace(
            "return p.offset_from(pbuf as *mut u8) as i32;",
            "return p.offset_from(pbuf as *mut u32) as i32;",
        );
    assert_ne!(wide, HEADER);
    held(&wide, "a wide cursor is not a byte view");
}
