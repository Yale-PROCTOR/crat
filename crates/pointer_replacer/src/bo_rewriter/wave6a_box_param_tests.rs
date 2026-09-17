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
            "-\tadmitted\tbox-param-chain callee=consume index=0 sink=free pointee=i32 shape=sized callers=1 members=producer::p"
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
            "box-param-chain callee=sum_and_release index=0 sink=free pointee=i32 shape=slice callers=2 members=run::v,run_twice::w"
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
    // The full ht shape: `ht` closes at the surface (R427-4 — `ht_create` and
    // `ht_destroy` are its only signatures and no field holds one), so the
    // chain is attempted with no in-crate caller and refuses LATER, on the
    // body: the sized owner is indexed (`(*table).entries` walked by
    // `.offset`), which this rule does not rewrite. A typed hold either way,
    // and no `Box<ht>` formal.
    let out = emitted("boxparam-ht", &with_prelude(HT_DESTROY));
    let src = compact(&out.source);
    assert!(!src.contains("table:Box<ht>"), "{}", out.source);
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("ht_destroy::table\theld\tbox-param-shape:ht_destroy:sized-owner-indexed"),
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

/// **W6A-C2, the store sink** (relay wave-6a/006 §4, charter §1(c)): the ht
/// shape reduced — a callee that STORES its formal into the program's own
/// raw storage instead of freeing it (`(*slots.offset(i)).key = key`) takes
/// `Box<T>` and hands ownership over at the store
/// (`Box::into_raw(key) as *mut i8`); the caller's allocation local moves at
/// the call, exactly as at a freeing callee. The C free of that storage is
/// someone else's subject and stays a C free.
#[test]
fn w6a_c2_store_sink_moves_the_allocation_into_the_programs_storage() {
    const STORE_CHAIN: &str = r#"
#[repr(C)]
pub struct slot { pub key: *mut i8, pub value: i32 }
unsafe extern "C" fn slot_set(mut slots: *mut slot, mut index: usize, mut key: *mut i8, mut value: i32) {
    *key.offset(0 as isize) = 0 as i8;
    (*slots.offset(index as isize)).value = value;
    (*slots.offset(index as isize)).key = key;
}
pub unsafe extern "C" fn table_put(mut slots: *mut slot, mut index: usize) {
    let mut key = calloc(8 as usize, ::std::mem::size_of::<i8>()) as *mut i8;
    *key.offset(1 as isize) = 65 as i8;
    slot_set(slots, index, key, 7 as i32);
}
"#;
    let out = emitted("boxparam-store", &with_prelude(STORE_CHAIN));
    if let Ok(path) = std::env::var("W6A_DUMP_EMITTED") {
        std::fs::write(path, &out.source).expect("dump");
    }
    let src = compact(&out.source);
    if std::env::var("W6A_DUMP").is_ok() {
        panic!(
            "{}\nRECEIPTS\n{}\nDEGRADATIONS {:#?}",
            out.source, out.artifacts.box_param_receipts, out.degradations
        );
    }
    assert_eq!(
        out.reverted, 0,
        "{}
{:#?}",
        out.source, out.degradations
    );
    assert!(src.contains("mutkey:Box<[i8]>,"), "{}", out.source);
    assert!(
        src.contains("slots[index].key=Box::into_raw(key)as*muti8;"),
        "{}",
        out.source
    );
    assert!(src.contains("key[0]=0asi8;"), "{}", out.source);
    assert!(
        src.contains(
            "letmutkey:Box<[i8]>=::std::vec![0i8;((8asusize)asusize)].into_boxed_slice();"
        ),
        "{}",
        out.source
    );
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("box-param-chain callee=slot_set index=2 sink=store"),
        "{}",
        out.artifacts.box_param_receipts
    );
    assert_eq!(
        reason_of(&out.degradations, "table_put::key"),
        None,
        "{:#?}",
        out.degradations
    );
}

/// W6A-C2 controls, each the delivering fixture with exactly ONE violation
/// so the refusal it measures is the gate under test: the store inside a loop
/// (the move would run twice), the formal re-assigned before the store (what
/// is stored is not the caller's allocation — ht's `key = strdup(key)`
/// shape), a use of the formal after the store (a use after a MOVE, which C
/// permits and Rust does not), and both a store and a free. None of them
/// takes a store chain.
#[test]
fn w6a_c2_one_violation_each_keeps_the_typed_hold() {
    const SHAPES: [(&str, &str); 4] = [
        (
            "loop",
            r#"
unsafe extern "C" fn slot_set(mut slots: *mut slot, mut n: usize, mut key: *mut i8) {
    let mut i = 0 as usize;
    while i < n {
        (*slots.offset(i as isize)).key = key;
        i = i.wrapping_add(1);
    }
}
"#,
        ),
        (
            "reassigned",
            r#"
unsafe extern "C" fn slot_set(mut slots: *mut slot, mut n: usize, mut key: *mut i8) {
    key = calloc(4 as usize, ::std::mem::size_of::<i8>()) as *mut i8;
    (*slots.offset(0 as isize)).key = key;
}
"#,
        ),
        (
            "used-after-store",
            r#"
unsafe extern "C" fn slot_set(mut slots: *mut slot, mut n: usize, mut key: *mut i8) {
    (*slots.offset(0 as isize)).key = key;
    *key.offset(0 as isize) = 1 as i8;
}
"#,
        ),
        (
            "stored-and-freed",
            r#"
unsafe extern "C" fn slot_set(mut slots: *mut slot, mut n: usize, mut key: *mut i8) {
    (*slots.offset(0 as isize)).key = key;
    free(key as *mut core::ffi::c_void);
}
"#,
        ),
    ];
    for (name, callee) in SHAPES {
        let source = format!(
            "{}
#[repr(C)]
pub struct slot {{ pub key: *mut i8, pub value: i32 }}
{callee}
             pub unsafe extern \"C\" fn table_put(mut slots: *mut slot, mut n: usize) {{
             let mut key = calloc(8 as usize, ::std::mem::size_of::<i8>()) as *mut i8;
             slot_set(slots, n, key);
}}
",
            PRELUDE
        );
        let out = emitted(&format!("boxparam-store-{name}"), &source);
        let receipts = &out.artifacts.box_param_receipts;
        assert!(
            !receipts.contains("sink=store"),
            "{name}: {receipts}\n{}",
            out.source
        );
        assert!(
            !compact(&out.source).contains("key:Box<"),
            "{name}: {}",
            out.source
        );
    }
}

/// **The leak-parity line of W6A-C2.** A store into a field the input's own C
/// `free` releases would hand a Rust-allocated block to libc: refused with
/// `box-param-store-c-free:<callee>:<field>` (the composition where that
/// field is an owned `Box` field — wave-6f's W6F-3 — is where the store
/// becomes a move and the drop is theirs).
#[test]
fn w6a_c2_store_into_a_c_freed_field_is_refused() {
    const FREED: &str = r#"
#[repr(C)]
pub struct slot { pub key: *mut i8, pub value: i32 }
unsafe extern "C" fn slot_set(mut slots: *mut slot, mut index: usize, mut key: *mut i8) {
    (*slots.offset(index as isize)).key = key;
}
pub unsafe extern "C" fn table_put(mut slots: *mut slot, mut index: usize) {
    let mut key = calloc(8 as usize, ::std::mem::size_of::<i8>()) as *mut i8;
    slot_set(slots, index, key);
}
pub unsafe extern "C" fn table_clear(mut slots: *mut slot, mut index: usize) {
    free((*slots.offset(index as isize)).key as *mut core::ffi::c_void);
    (*slots.offset(index as isize)).key = 0 as *mut i8;
}
"#;
    let out = emitted("boxparam-store-cfree", &with_prelude(FREED));
    let src = compact(&out.source);
    assert!(!src.contains("Box<[i8]>"), "{}", out.source);
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("slot_set::key\theld\tbox-param-store-c-free:slot_set:"),
        "{}",
        out.artifacts.box_param_receipts
    );
}

/// R423-7: the wrapper bridges a SIZED owning formal
/// (`__crat_safe_f(Box::from_raw(p))`) but a `Box<[T]>` one has no extent at
/// the raw surface, so a slice chain whose consuming callee is a
/// fn-pointer-web member still holds whole (`chain-endpoint-raw:…:slice`);
/// the callers' allocation locals stay raw and nothing reverts.
#[test]
fn w6a_c1_slice_chain_on_a_web_member_holds_whole() {
    const TABLE: &str = r#"
pub static mut HOOKS: [Option<unsafe extern "C" fn(i32) -> i32>; 1] = [Some(run as unsafe extern "C" fn(i32) -> i32)];
"#;
    let out = emitted(
        "boxparam-slice-web",
        &format!("{}{TABLE}", with_prelude(SLICE_CHAIN)),
    );
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    assert!(!src.contains("Box<[i32]>"), "{}", out.source);
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("\theld\tchain-endpoint-raw:sum_and_release:slice"),
        "{}",
        out.artifacts.box_param_receipts
    );
}

/// **The exported pair at the surface** (relay wave-6a/017 §1, R427-4; the
/// user's Box-emission priority): ht's `ht_create` / `ht_destroy` are
/// `#[no_mangle]` exports with NO in-program caller, so the consuming formal
/// had `box-param-no-callers` and the producer's certificate
/// `return-certificate-no-receivers`. Under R415-7 each crate is the whole
/// program, so the only producer of that pointee IS the export and the pair
/// closes at the surface.
#[test]
fn w6a_c1_exported_pair_delivers_through_the_surface() {
    const PAIR: &str = r#"
#[repr(C)]
pub struct ht { pub length: usize, pub capacity: usize }
#[no_mangle]
pub unsafe extern "C" fn ht_create() -> *mut ht {
    let mut table = malloc(::std::mem::size_of::<ht>()) as *mut ht;
    if table.is_null() { return 0 as *mut ht; }
    (*table).length = 0 as usize;
    (*table).capacity = 16 as usize;
    return table;
}
#[no_mangle]
pub unsafe extern "C" fn ht_destroy(mut table: *mut ht) {
    free(table as *mut core::ffi::c_void);
}
"#;
    let out = emitted("boxparam-exported-pair", &with_prelude(PAIR));
    let src = compact(&out.source);
    let receipts = format!(
        "{}\n{}",
        out.artifacts.box_param_receipts, out.artifacts.return_certificate_receipts
    );
    // R427-4: the pair CLOSES — `ht` is mentioned by nothing but the exported
    // producer and the exported consumer, and no struct field holds one — so
    // the producer returns `Box<ht>` behind a wrapper that hands the raw
    // pointer out and the consumer takes `Box<ht>` behind a wrapper that takes
    // it back. The block is allocated and released by one allocator; it
    // crosses C only as an opaque handle.
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    // Neither end is a fn-pointer-web member or a positive seed, so the
    // exposure family gives them no wrapper (`NotApplicable`): the converted
    // `#[no_mangle] extern "C"` signatures ARE the surface — admissible under
    // R415-7 (relay 015 STOP 2) and ABI-identical to the raw pointer.
    assert!(
        src.contains("fnht_create()->Box<ht>{"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        src.contains(
            "letmuttable:Box<crate::ht>=Box::new(crate::ht{length:0asusize,capacity:0asusize});"
        ),
        "{}",
        out.source
    );
    assert!(
        src.contains("fnht_destroy(muttable:Box<ht>){drop(table);}"),
        "{}",
        out.source
    );
    assert!(
        receipts.contains("exported-pair-closure callee=ht_create"),
        "{receipts}"
    );
    assert!(
        receipts.contains("callers=0 exported-pair-closure"),
        "{receipts}"
    );
    assert_eq!(
        reason_of(&out.degradations, "ht_destroy::table"),
        None,
        "{:#?}",
        out.degradations
    );
}

/// R427-4's fail-closed gates, one violation each over the delivering pair:
/// a THIRD signature mentioning the pointee (a lend the closure cannot
/// account for), a struct FIELD holding one (it could be stored and released
/// anywhere), an end that is not exported (an in-crate caller could still
/// hand in a foreign block), and a producer with no consumer (the owner would
/// cross the surface with nothing to release it). None of them converts.
#[test]
fn w6a_c1_exported_pair_gates_hold_one_violation_each() {
    const CREATE: &str = r#"
#[repr(C)]
pub struct ht { pub length: usize, pub capacity: usize }
#[no_mangle]
pub unsafe extern "C" fn ht_create() -> *mut ht {
    let mut table = malloc(::std::mem::size_of::<ht>()) as *mut ht;
    if table.is_null() { return 0 as *mut ht; }
    (*table).length = 0 as usize;
    (*table).capacity = 16 as usize;
    return table;
}
"#;
    const DESTROY: &str = r#"
#[no_mangle]
pub unsafe extern "C" fn ht_destroy(mut table: *mut ht) {
    free(table as *mut core::ffi::c_void);
}
"#;
    const SHAPES: [(&str, &str); 4] = [
        (
            "third-signature",
            r#"
#[no_mangle]
pub unsafe extern "C" fn ht_length(mut table: *mut ht) -> usize { return (*table).length; }
"#,
        ),
        (
            "struct-field",
            r#"
#[repr(C)]
pub struct registry { pub table: *mut ht }
"#,
        ),
        ("not-exported", ""),
        ("producer-only", ""),
    ];
    for (name, extra) in SHAPES {
        let source = match name {
            // The producer alone: an owner would cross the surface with
            // nothing to release it.
            "producer-only" => format!("{}{CREATE}", PRELUDE),
            // The consumer is not `#[no_mangle]`: an in-crate caller could
            // still hand it a block from anywhere.
            "not-exported" => format!(
                "{}{CREATE}{}",
                PRELUDE,
                DESTROY.replace("#[no_mangle]\n", "")
            ),
            _ => format!("{}{CREATE}{DESTROY}{extra}", PRELUDE),
        };
        let out = emitted(&format!("boxparam-pair-{name}"), &source);
        let src = compact(&out.source);
        let receipts = format!(
            "{}\n{}",
            out.artifacts.box_param_receipts, out.artifacts.return_certificate_receipts
        );
        assert!(
            !src.contains("->Box<ht>") && !src.contains("table:Box<ht>"),
            "{name}: {}\n{receipts}",
            out.source
        );
    }
}

/// **avl's rotations** (relay wave-6a/026): a `Box` parameter the callee does
/// not free but MOVES INTO THE TREE — `(*x).right = y` — while reading and
/// writing the owner's own fields, and the function returns the node that now
/// owns it. The three corpus rows (`rightRotate::y`, `leftRotate::x`,
/// `insert::node`) hold `box-param-callee-lends`.
///
/// This witness pins where the chain stands: the field projections of a sized
/// `Box` owner are ADMITTED (they compile as written — `*y` derefs the Box —
/// so the chain needs no edit for them), and what holds the shape now is the
/// CALLER side, whose argument is its own parameter rather than a local
/// allocation. Report 021 §3 names the rest of the ladder.
const AVL_ROTATIONS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: std::os::raw::c_ulong) -> *mut core::ffi::c_void;
}
#[repr(C)]
pub struct Node {
    pub key: i32,
    pub left: *mut Node,
    pub right: *mut Node,
    pub height: i32,
}
pub unsafe extern "C" fn height(mut n: *mut Node) -> i32 {
    if n.is_null() { return 0 as i32; }
    return (*n).height;
}
pub unsafe extern "C" fn max(mut a: i32, mut b: i32) -> i32 {
    return if a > b { a } else { b };
}
pub unsafe extern "C" fn newNode(mut key: i32) -> *mut Node {
    let mut node = malloc(::std::mem::size_of::<Node>() as std::os::raw::c_ulong) as *mut Node;
    (*node).key = key;
    (*node).left = 0 as *mut Node;
    (*node).right = 0 as *mut Node;
    (*node).height = 1 as i32;
    return node;
}
pub unsafe extern "C" fn rightRotate(mut y: *mut Node) -> *mut Node {
    let mut x = (*y).left;
    let mut T2 = (*x).right;
    (*y).left = T2;
    (*y).height = max(height((*y).left), height((*y).right)) + 1 as i32;
    (*x).right = y;
    (*x).height = max(height((*x).left), height((*x).right)) + 1 as i32;
    return x;
}
pub unsafe extern "C" fn insert(mut node: *mut Node, mut key: i32) -> *mut Node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key {
        (*node).left = insert((*node).left, key);
    } else {
        (*node).right = insert((*node).right, key);
    }
    (*node).height = 1 as i32 + max(height((*node).left), height((*node).right));
    if height((*node).left) > height((*node).right) + 1 as i32 {
        return rightRotate(node);
    }
    return node;
}
"#;

#[test]
fn w6a_c1_avls_rotation_owner_passes_the_use_check_and_holds_on_its_caller() {
    let out = emitted("bp-avl", AVL_ROTATIONS);
    let receipts = &out.artifacts.box_param_receipts;
    // The uses of the owner are its own fields, and they no longer hold the
    // chain: what the collector reads as a raw use is a projection that needs
    // no edit.
    assert!(
        !receipts.contains("raw-use:y"),
        "a field projection of a sized Box owner is not a raw use\n{receipts}"
    );
    // The caller side is what holds it: `insert` hands `rightRotate` its own
    // PARAMETER, and the chain admits only a local allocation (or a
    // certificate's receiver) there.
    assert!(
        receipts.contains("rightRotate::y\theld\tbox-param-caller-retains:insert:"),
        "{receipts}"
    );
    assert!(
        !compact(&out.source).contains("Box<Node>"),
        "{}",
        out.source
    );
}

/// **Rung 3, pinned** (relay wave-6a/027, report 022 §2): a consuming callee
/// whose owner is a STRUCT — used through its fields and freed there — whose
/// CALLER allocated it with the contract's allocator. The callee side passes
/// (rung 1 closed its use check); the chain holds on the caller, because the
/// ordinary Box arm has no initializer form for a struct pointee.
///
/// The obvious repair — let the chain move the CONTRACT's plan for that local —
/// was built and reverted: with the transfer admitted as the contract's sink,
/// both families plan the same binding, and C1's own witnesses go red. Which
/// family owns a local whose allocation is the contract's and whose release is
/// a callee's is a design question, and report 022 §3 asks it.
const CONTRACT_OWNER_CHAIN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: std::os::raw::c_ulong) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct Node {
    pub key: i32,
    pub height: i32,
}
pub unsafe extern "C" fn retire(mut p: *mut Node) -> i32 {
    (*p).height = 0 as i32;
    let mut k = (*p).key;
    free(p as *mut core::ffi::c_void);
    return k;
}
pub unsafe extern "C" fn build_and_retire(mut key: i32) -> i32 {
    let mut n = malloc(::std::mem::size_of::<Node>() as std::os::raw::c_ulong) as *mut Node;
    (*n).key = key;
    (*n).height = 1 as i32;
    return retire(n);
}
"#;

#[test]
fn w6a_c1_a_contract_owner_holds_on_its_callers_initializer() {
    let out = emitted("bp-contract-chain", CONTRACT_OWNER_CHAIN);
    let receipts = &out.artifacts.box_param_receipts;
    // The CALLEE side is settled: the owner's field uses no longer hold it.
    assert!(
        !receipts.contains("raw-use:p"),
        "rung 1 is closed\n{receipts}"
    );
    // The CALLER side is rung 3, named exactly.
    assert!(
        receipts.contains(
            "retire::p\theld\tbox-param-caller-retains:build_and_retire:unplanned-argument:box-initializer-unsupported"
        ),
        "{receipts}"
    );
    assert!(
        !compact(&out.source).contains("Box<Node>"),
        "{}",
        out.source
    );
}
