//! wave-6a rule **W6A-C1** (`decision/box_param.rs`): Box parameters of
//! consuming callees under the closed world — the chain (allocation local →
//! transfer call → freeing formal) planned whole, or a typed hold.
//!
//! Corpus-derived controls: ht `ht_destroy` (no in-program caller), brotli
//! `BrotliDefaultFreeFunc` (reached through the `free_func` fn-pointer field),
//! heman `qselect` (a lend the model calls Owning). The delivering shapes are
//! the corpus shapes' minimal forms: the frame has no consuming callee whose
//! every caller passes an allocation local (report 003 §2).

use super::wave6a_allocation_tests::{compact, emitted, reason_of};

const PRELUDE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
"#;

/// A callee that reads, writes and frees its sized formal; its one caller
/// allocates, stores once, reads, and hands the allocation over.
const SIZED_CHAIN: &str = r#"
unsafe extern "C" fn consume(mut p: *mut i32) {
    *p += 1 as i32;
    free(p as *mut core::ffi::c_void);
}
pub unsafe extern "C" fn producer() -> i32 {
    let mut p = malloc(::std::mem::size_of::<i32>()) as *mut i32;
    *p = 7 as i32;
    let mut v = *p;
    consume(p);
    return v;
}
"#;

/// A callee that indexes and frees its slice formal; two callers, each with
/// its own `calloc`.
const SLICE_CHAIN: &str = r#"
unsafe extern "C" fn sum_and_release(mut v: *mut i32, mut n: i32) -> i32 {
    let mut i = 0 as i32;
    let mut s = 0 as i32;
    while i < n {
        s += *v.offset(i as isize);
        i += 1;
    }
    free(v as *mut core::ffi::c_void);
    return s;
}
pub unsafe extern "C" fn run(mut n: i32) -> i32 {
    let mut v = calloc(n as usize, ::std::mem::size_of::<i32>()) as *mut i32;
    *v.offset(0 as i32 as isize) = 1 as i32;
    return sum_and_release(v, n);
}
pub unsafe extern "C" fn run_twice(mut n: i32) -> i32 {
    let mut w = calloc((n * 2 as i32) as usize, ::std::mem::size_of::<i32>()) as *mut i32;
    *w.offset(1 as i32 as isize) = 2 as i32;
    let mut a = sum_and_release(w, n * 2 as i32);
    return a;
}
"#;

/// Control: the caller reads the allocation after the transfer.
const USED_AFTER: &str = r#"
unsafe extern "C" fn consume(mut p: *mut i32) {
    free(p as *mut core::ffi::c_void);
}
pub unsafe extern "C" fn producer() -> i32 {
    let mut p = malloc(::std::mem::size_of::<i32>()) as *mut i32;
    *p = 7 as i32;
    consume(p);
    return *p;
}
"#;

/// Control: the allocation is lent to a raw callee before the transfer — a
/// second call position this rule does not model (a raw callee may keep it).
const LENT_BEFORE: &str = r#"
unsafe extern "C" fn touch(mut q: *mut i32) {
    *q = 3 as i32;
}
unsafe extern "C" fn consume(mut p: *mut i32) {
    free(p as *mut core::ffi::c_void);
}
pub unsafe extern "C" fn producer() -> i32 {
    let mut p = malloc(::std::mem::size_of::<i32>()) as *mut i32;
    *p = 7 as i32;
    touch(p);
    consume(p);
    return 0 as i32;
}
"#;

/// Emitted sources for the Miri run (`CRAT_W6A_EMIT_DIR`), test-only.
fn record(name: &str, source: &str) {
    if let Ok(dir) = std::env::var("CRAT_W6A_EMIT_DIR") {
        std::fs::write(format!("{dir}/{name}-emitted.rs"), source).unwrap();
    }
}

/// ht `ht_destroy`: `#[no_mangle]` export, nothing in the program calls it.
const HT_DESTROY: &str = r#"
#[repr(C)]
pub struct ht_entry {
    pub key: *const std::os::raw::c_char,
    pub value: *mut core::ffi::c_void,
}
#[repr(C)]
pub struct ht {
    pub entries: *mut ht_entry,
    pub capacity: usize,
    pub length: usize,
}
#[no_mangle]
pub unsafe extern "C" fn ht_create() -> *mut ht {
    let mut table = malloc(::std::mem::size_of::<ht>()) as *mut ht;
    if table.is_null() {
        return 0 as *mut ht;
    }
    (*table).length = 0 as usize;
    (*table).capacity = 16 as usize;
    (*table).entries = calloc((*table).capacity, ::std::mem::size_of::<ht_entry>()) as *mut ht_entry;
    return table;
}
#[no_mangle]
pub unsafe extern "C" fn ht_destroy(mut table: *mut ht) {
    let mut i = 0 as usize;
    while i < (*table).capacity {
        free((*((*table).entries).offset(i as isize)).key as *mut core::ffi::c_void);
        i = i.wrapping_add(1);
    }
    free((*table).entries as *mut core::ffi::c_void);
    free(table as *mut core::ffi::c_void);
}
"#;

/// brotli `BrotliDefaultFreeFunc` reached through `MemoryManager::free_func`.
const BROTLI_FREE_FUNC: &str = r#"
pub type brotli_free_func = Option<unsafe extern "C" fn(*mut core::ffi::c_void, *mut core::ffi::c_void) -> ()>;
#[repr(C)]
pub struct MemoryManager {
    pub free_func: brotli_free_func,
    pub opaque: *mut core::ffi::c_void,
}
pub unsafe extern "C" fn BrotliDefaultFreeFunc(mut opaque: *mut core::ffi::c_void, mut address: *mut core::ffi::c_void) {
    free(address);
}
pub unsafe extern "C" fn BrotliInitMemoryManager(mut m: *mut MemoryManager) {
    (*m).free_func = Some(BrotliDefaultFreeFunc as unsafe extern "C" fn(*mut core::ffi::c_void, *mut core::ffi::c_void) -> ());
    (*m).opaque = 0 as *mut core::ffi::c_void;
}
pub unsafe extern "C" fn BrotliFree(mut m: *mut MemoryManager, mut p: *mut core::ffi::c_void) {
    ((*m).free_func).expect("non-null function pointer")((*m).opaque, p);
}
pub unsafe extern "C" fn use_it(mut m: *mut MemoryManager) {
    let mut block = malloc(16 as usize) as *mut u8;
    BrotliFree(m, block as *mut core::ffi::c_void);
}
"#;

/// heman `qselect`: the formal is read, written and recursed on, never freed.
const QSELECT: &str = r#"
unsafe extern "C" fn qselect(mut v: *mut f32, mut len: i32, mut k: i32) -> f32 {
    let mut i = 0 as i32;
    let mut st = 0 as i32;
    while i < len - 1 as i32 {
        if !(*v.offset(i as isize) > *v.offset((len - 1 as i32) as isize)) {
            let mut f = *v.offset(i as isize);
            *v.offset(i as isize) = *v.offset(st as isize);
            *v.offset(st as isize) = f;
            st += 1;
        }
        i += 1;
    }
    return if k == st {
        *v.offset(st as isize)
    } else if st > k {
        qselect(v, st, k)
    } else {
        qselect(v.offset(st as isize), len - st, k - st)
    };
}
pub unsafe extern "C" fn percentiles(mut n: i32) -> f32 {
    let mut vals = malloc((n as usize).wrapping_mul(::std::mem::size_of::<f32>())) as *mut f32;
    let mut i = 0 as i32;
    while i < n {
        *vals.offset(i as isize) = i as f32;
        i += 1;
    }
    let mut m = qselect(vals, n, n / 2 as i32);
    free(vals as *mut core::ffi::c_void);
    return m;
}
"#;

fn with_prelude(body: &str) -> String {
    format!("{PRELUDE}{body}")
}

/// The custody instrument (main 033) reads only explicit types.
fn assert_custody(source: &str, expected: &[(&str, &str, &str)]) {
    let declarations =
        super::delivery_custody::inventory_source("lib.rs", source).expect("inventory");
    for (owner, binding, ty) in expected {
        let row = declarations
            .iter()
            .find(|row| row.owner == *owner && row.binding == *binding)
            .unwrap_or_else(|| panic!("{owner}::{binding}: {declarations:#?}"));
        assert!(row.type_is_fully_explicit, "{row:#?}");
        assert_eq!(row.explicit_type.as_deref(), Some(*ty), "{row:#?}");
    }
}

#[test]
fn w6a_c1_sized_chain_moves_the_allocation_into_the_freeing_callee() {
    let out = emitted("boxparam-sized", &with_prelude(SIZED_CHAIN));
    record("sized-chain", &out.source);
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        src.contains("fnconsume(mutp:Box<i32>){(*p)+=1asi32;drop(p);}"),
        "{}",
        out.source
    );
    assert!(
        src.contains("letmutp:Box<i32>=Box::new(7asi32);"),
        "{}",
        out.source
    );
    assert!(src.contains("letmutv=(*p);consume(p);"), "{}", out.source);
    assert!(!src.contains("*p=7asi32;"), "{}", out.source);
    assert_custody(
        &out.source,
        &[("producer", "p", "Box<i32>"), ("consume", "p", "Box<i32>")],
    );
    for subject in ["consume::p", "producer::p"] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}: {:#?}",
            out.degradations
        );
    }
    assert!(
        out.artifacts.box_param_receipts.contains(
            "-\tadmitted\tbox-param-chain callee=consume index=0 pointee=i32 shape=sized callers=1 members=producer::p"
        ),
        "{}",
        out.artifacts.box_param_receipts
    );
}

#[test]
fn w6a_c1_slice_chain_indexes_in_callee_and_callers() {
    let out = emitted("boxparam-slice", &with_prelude(SLICE_CHAIN));
    record("slice-chain", &out.source);
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        src.contains("fnsum_and_release(mutv:Box<[i32]>,mutn:i32)->i32{"),
        "{}",
        out.source
    );
    assert!(src.contains("s+=v[(i)asusize];"), "{}", out.source);
    assert!(src.contains("drop(v);"), "{}", out.source);
    assert!(src.contains("v[(0asi32)asusize]=1asi32;"), "{}", out.source);
    assert!(src.contains("w[(1asi32)asusize]=2asi32;"), "{}", out.source);
    assert!(
        src.contains("returnsum_and_release(v,n);"),
        "{}",
        out.source
    );
    assert!(
        src.contains("=sum_and_release(w,n*2asi32);"),
        "{}",
        out.source
    );
    assert!(!src.contains("*muti32"), "{}", out.source);
    assert_custody(
        &out.source,
        &[
            ("run", "v", "Box<[i32]>"),
            ("run_twice", "w", "Box<[i32]>"),
            ("sum_and_release", "v", "Box<[i32]>"),
        ],
    );
    for subject in ["sum_and_release::v", "run::v", "run_twice::w"] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}: {:#?}",
            out.degradations
        );
    }
    assert!(
        out.artifacts.box_param_receipts.contains(
            "box-param-chain callee=sum_and_release index=0 pointee=i32 shape=slice callers=2 members=run::v,run_twice::w"
        ),
        "{}",
        out.artifacts.box_param_receipts
    );
}

#[test]
fn w6a_c1_caller_reading_after_the_transfer_holds_typed() {
    let out = emitted("boxparam-used-after", &with_prelude(USED_AFTER));
    let src = compact(&out.source);
    assert!(!src.contains("Box<i32>"), "{}", out.source);
    assert_eq!(
        reason_of(&out.degradations, "consume::p").as_deref(),
        Some("box-param-caller-retains"),
        "{:#?}",
        out.degradations
    );
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("consume::p\theld\tbox-param-caller-retains:producer:used-after-transfer"),
        "{}",
        out.artifacts.box_param_receipts
    );
}

#[test]
fn w6a_c1_allocation_lent_before_the_transfer_holds_typed() {
    let out = emitted("boxparam-lent", &with_prelude(LENT_BEFORE));
    let src = compact(&out.source);
    // The FORMAL stays raw (no chain); the caller's local is not this rule's
    // to hold — on batch 8's composition ownership/fields' native rule boxes
    // it and transfers through `Box::into_raw` at the raw consuming callee.
    assert!(src.contains("fnconsume(mutp:*muti32){"), "{}", out.source);
    assert_eq!(
        reason_of(&out.degradations, "consume::p").as_deref(),
        Some("box-param-caller-retains"),
        "{:#?}",
        out.degradations
    );
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("consume::p\theld\tbox-param-caller-retains:producer:other-call-use"),
        "{}",
        out.artifacts.box_param_receipts
    );
}

#[test]
fn w6a_c1_ht_destroy_without_callers_holds_typed() {
    let out = emitted("boxparam-ht", &with_prelude(HT_DESTROY));
    let src = compact(&out.source);
    assert!(!src.contains("Box<ht>"), "{}", out.source);
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("ht_destroy::table\theld\tbox-param-no-callers:ht_destroy"),
        "{}",
        out.artifacts.box_param_receipts
    );
}

#[test]
fn w6a_c1_brotli_free_func_behind_a_fn_pointer_holds_typed() {
    let out = emitted("boxparam-brotli", &with_prelude(BROTLI_FREE_FUNC));
    let src = compact(&out.source);
    assert!(!src.contains("address:Box<"), "{}", out.source);
    assert!(
        out.artifacts.box_param_receipts.contains(
            "BrotliDefaultFreeFunc::address\theld\tbox-param-indirect-callers:BrotliDefaultFreeFunc"
        ),
        "{}",
        out.artifacts.box_param_receipts
    );
}

#[test]
fn w6a_c1_qselect_lend_is_not_a_box_parameter() {
    let out = emitted("boxparam-qselect", &with_prelude(QSELECT));
    let src = compact(&out.source);
    assert!(!src.contains("v:Box<"), "{}", out.source);
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("qselect::v\theld\tbox-param-callee-lends:qselect"),
        "{}",
        out.artifacts.box_param_receipts
    );
}
