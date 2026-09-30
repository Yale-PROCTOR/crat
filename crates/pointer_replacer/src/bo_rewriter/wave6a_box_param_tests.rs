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

const CONTRACT_CHAIN_UNCONFIRMED: &str = r#"
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
pub unsafe extern "C" fn retire2(mut p: *mut Node) -> i32 {
    let mut k = (*p).key;
    free(p as *mut core::ffi::c_void);
    return k;
}
pub unsafe extern "C" fn good(mut key: i32) -> i32 {
    let mut n = malloc(::std::mem::size_of::<Node>() as std::os::raw::c_ulong) as *mut Node;
    (*n).key = key;
    return retire2(n);
}
pub unsafe extern "C" fn keeps(mut key: i32) -> i32 {
    let mut m = malloc(::std::mem::size_of::<Node>() as std::os::raw::c_ulong) as *mut Node;
    (*m).key = key;
    let mut r = retire2(m);
    (*m).height = 0 as i32;
    return r;
}
"#;

/// **The confirmation is load-bearing** (R450-8 rung 3). `good::n` is admitted
/// by the contract row on the optimistic reading that `retire2` consumes its
/// formal — `consuming_formals` is syntactic, as the allocation-return
/// certificate's use of it is. The CHAIN then refuses the formal, because the
/// second caller reads its local after the call (`keeps`), and without
/// `confirm_transfers` `good::n` would emit a `Box<Node>` into a raw formal.
/// The withdrawal names the callee it waited on.
#[test]
fn w6a_c1_an_unconfirmed_contract_transfer_is_withdrawn() {
    let out = emitted("bp-contract-unconfirmed", CONTRACT_CHAIN_UNCONFIRMED);
    let contract = &out.artifacts.allocator_contract_receipts;
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    assert!(
        contract
            .contains("good::n\tyielded\tcontract-allocation:use:transfer-unconfirmed:retire2#0"),
        "the owner is withdrawn with its callee named\n{contract}"
    );
    assert!(
        !contract.contains("good::n\tadmitted"),
        "no admission survives the withdrawal\n{contract}"
    );
    let text = compact(&out.source);
    assert!(!text.contains("Box<Node>"), "{}", out.source);
    assert!(text.contains("returnretire2(n);"), "{}", out.source);
}

/// **The full ht shape, delivered.** `ht` closes at the surface (R427-4 —
/// `ht_create` and `ht_destroy` are its only signatures and no field holds
/// one), so the exported-pair closure of report 012 admits the chain with no
/// in-crate caller. Its last wall was the shape check reading `(*table)` — the
/// owner's own deref, in a field projection — as an indexing use it does not
/// rewrite. It is not a use to rewrite at all: `(*table).entries` reads a
/// `Box<ht>` exactly as it read the raw pointer, and R450-8's rung 3 is where
/// that mattered enough to say so. The field's own `.offset` walk is the
/// FIELD's raw pointer and is untouched; the C frees of the entries stay C
/// frees, and only the owner's own free becomes the `drop`.
#[test]
fn w6a_c1_ht_destroy_delivers_through_the_surface_closure() {
    let out = emitted("boxparam-ht", &with_prelude(HT_DESTROY));
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    assert!(
        src.contains("fnht_destroy(muttable:Box<ht>)"),
        "{}",
        out.source
    );
    assert!(src.contains("drop(table);"), "{}", out.source);
    // The entries are C memory and stay C memory: their frees keep their text
    // and the field walk keeps its `.offset`.
    assert!(
        src.contains("free((*((*table).entries).offset(iasisize)).keyas*mutcore::ffi::c_void);"),
        "{}",
        out.source
    );
    assert!(
        src.contains("free((*table).entriesas*mutcore::ffi::c_void);"),
        "{}",
        out.source
    );
    assert!(
        !out.artifacts
            .box_param_receipts
            .contains("box-param-shape:ht_destroy:sized-owner-indexed"),
        "the deref is not an indexing use\n{}",
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
    // Restated for W6A-A9 (relay wave-6a/048): the classification is
    // unchanged — the body lends and this family refuses it — but the refusal
    // is now a DECLINE that leaves the owning arm rather than a hold that
    // degrades there, so the row reads `yielded`.
    //
    // R528-2: its own name. `emitted` writes the fixture to a directory keyed
    // on this name and the process id, and removes it after; sharing
    // `boxparam-qselect` with `w6a_a9_qselect_leaves_the_owning_arm` let one
    // test delete the file the other was reading.
    let out = emitted("boxparam-qselect-lend", &with_prelude(QSELECT));
    let src = compact(&out.source);
    assert!(!src.contains("v:Box<"), "{}", out.source);
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("qselect::v\tyielded\tbox-param-lend-leaves-owning:qselect"),
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
/// `free` releases hands a Rust-allocated block to libc. Under R448-1 (B′)
/// every emitted crate declares the system allocator, whose blocks libc may
/// free (R620-3 (a)), so the refusal
/// `box-param-store-c-free:<callee>:<field>` stands only where the crate's
/// allocator is ANOTHER one: here a user type that forwards to `System` (the
/// composition where that field is an owned `Box` field — wave-6f's W6F-3 —
/// is where the store becomes a move and the drop is theirs).
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
    let out = emitted(
        "boxparam-store-cfree",
        &with_prelude(&format!("{FREED}{CUSTOM_ALLOCATOR}")),
    );
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
            "letmuttable:Box<crate::ht>=::std::boxed::Box::new(crate::ht{length:0usize,capacity:0usize,});"
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
/// hand in a foreign block), and a producer with no consumer. None of them
/// converts the CONSUMER through the closure (R531-4 (vi) now delivers an
/// exported one under its own waiver). Restated for R517-9's callee-less extension: the
/// PRODUCER is an exported function nothing in the program receives, so it
/// delivers `Box<ht>` at the surface under the exported-producer waiver in
/// every shape — the closure no longer decides it.
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
        // Restated for R531-4 (vi), the consumer half: where `ht_destroy` is
        // exported and nothing in the program calls it, it takes `Box<ht>`
        // under the exported-consumer waiver; unexported (or absent), it
        // keeps its raw formal.
        let consumer_waived = matches!(name, "third-signature" | "struct-field");
        assert_eq!(
            src.contains("fnht_destroy(muttable:Option<Box<ht>>)"),
            consumer_waived,
            "{name}: {}\n{receipts}",
            out.source
        );
        assert_eq!(
            receipts.contains("exported-consumer-waiver callee=ht_destroy"),
            consumer_waived,
            "{name}: {receipts}"
        );
        assert!(
            src.contains("fnht_create()->Box<ht>{")
                && receipts.contains("exported-producer-waiver callee=ht_create"),
            "{name}: {}\n{receipts}",
            out.source
        );
    }
}

/// **W6S-17 (R641-12) — the optional form through a pointer alias.** ht's
/// exported consumer spelled `ht_destroy(mut table: ht_t)`, `ht_t = *mut ht`,
/// with a lending third signature (the shape above that waives the consumer):
/// the declaration is spelled from the alias's resolved pointee,
/// `Option<Box<crate::ht>>`, as the raw spelling's `Option<Box<ht>>`.
#[test]
fn w6s17_an_alias_spelled_exported_consumer_takes_option_box() {
    const SOURCE: &str = r#"
#[repr(C)]
pub struct ht { pub length: usize, pub capacity: usize }
pub type ht_t = *mut ht;
#[no_mangle]
pub unsafe extern "C" fn ht_create() -> *mut ht {
    let mut table = malloc(::std::mem::size_of::<ht>()) as *mut ht;
    if table.is_null() { return 0 as *mut ht; }
    (*table).length = 0 as usize;
    (*table).capacity = 16 as usize;
    return table;
}
#[no_mangle]
pub unsafe extern "C" fn ht_destroy(mut table: ht_t) {
    free(table as *mut core::ffi::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn ht_length(mut table: *mut ht) -> usize { return (*table).length; }
"#;
    let out = emitted("w6s17-ht-alias", &format!("{PRELUDE}{SOURCE}"));
    let src = compact(&out.source);
    let receipts = format!(
        "{}\n{}",
        out.artifacts.box_param_receipts, out.artifacts.return_certificate_receipts
    );
    assert!(
        src.contains("fnht_destroy(muttable:Option<Box<crate::ht>>)")
            && receipts.contains("exported-consumer-waiver callee=ht_destroy"),
        "{receipts}\n{}",
        out.source
    );
    assert!(
        out.artifacts.declaration_rows.iter().any(|row| {
            row.original_type_form == "ht_t" && row.settled_emitted_type == "Option<Box<crate::ht>>"
        }),
        "{:#?}",
        out.artifacts.declaration_rows
    );
    assert_eq!(
        reason_of(&out.degradations, "ht_destroy::table"),
        None,
        "{:#?}",
        out.degradations
    );
    assert_eq!(out.reverted, 0, "{receipts}\n{}", out.source);
}

/// **W6S-17 — a pointee in a nested module, and the hold that stays.** A
/// consuming formal spelled `shell::cell_t` (`= *mut hidden::cell`, the
/// corpus's module-nested shape): where `hidden` is public the formal delivers
/// `Box<crate::shell::hidden::cell>`; where it is private to `shell`, the
/// owner cannot name the pointee, so there is nothing to spell `Box<..>` over
/// and the chain holds typed (`box-param-alias-formal`) — the formal left raw
/// under a `Box` member would be bridged as a lend and freed twice.
#[test]
fn w6s17_an_alias_formal_spells_a_nested_pointee_and_holds_an_unnameable_one() {
    const SOURCE: &str = r#"
pub mod shell {
    pub mod hidden {
        #[repr(C)]
        pub struct cell { pub v: i32 }
    }
    pub type cell_t = *mut hidden::cell;
    pub type cell_size = hidden::cell;
}
unsafe extern "C" fn consume(mut p: shell::cell_t) {
    (*p).v += 1 as i32;
    free(p as *mut core::ffi::c_void);
}
pub unsafe extern "C" fn producer() -> i32 {
    let mut p = malloc(::std::mem::size_of::<shell::cell_size>()) as shell::cell_t;
    (*p).v = 7 as i32;
    let mut v = (*p).v;
    consume(p);
    return v;
}
"#;
    let out = emitted("w6s17-nested", &format!("{PRELUDE}{SOURCE}"));
    let src = compact(&out.source);
    let receipts = out.artifacts.box_param_receipts.clone();
    assert!(
        src.contains("fnconsume(mutp:Box<crate::shell::hidden::cell>){")
            && receipts.contains("box-param-chain callee=consume index=0 sink=free"),
        "{receipts}\n{}",
        out.source
    );
    assert_eq!(out.reverted, 0, "{receipts}\n{}", out.source);

    let hidden = SOURCE.replace("    pub mod hidden {", "    mod hidden {");
    assert_ne!(hidden, SOURCE);
    let out = emitted("w6s17-unnameable", &format!("{PRELUDE}{hidden}"));
    let src = compact(&out.source);
    let receipts = out.artifacts.box_param_receipts.clone();
    assert!(
        receipts.contains("consume::p\theld\tbox-param-alias-formal:consume"),
        "{receipts}\n{}",
        out.source
    );
    assert!(!src.contains("fnconsume(mutp:Box<"), "{}", out.source);
    assert!(!src.contains("as_mut())"), "{}", out.source);
    assert_eq!(out.reverted, 0, "{receipts}\n{}", out.source);
}

/// **R517-9 — the callee-less exported producer.** ht's `ht_create` with a
/// lending third signature (`ht_length`, the corpus's `ht_get` / `ht_set`):
/// the closure holds, nothing in the program receives the result, and the
/// export delivers `Box<ht>` under the waiver. The control drops the export
/// attribute: an unexported producer with no receivers has no one to hand the
/// owner to and keeps `no-receivers`.
#[test]
fn w6a_r517_9_a_callee_less_export_delivers_under_the_waiver() {
    const PRODUCER: &str = r#"
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
pub unsafe extern "C" fn ht_length(mut table: *mut ht) -> usize { return (*table).length; }
"#;
    let out = emitted("r517-9-export", &with_prelude(PRODUCER));
    let receipts = &out.artifacts.return_certificate_receipts;
    assert!(
        compact(&out.source).contains("fnht_create()->Box<ht>{"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        receipts.contains("exported-producer-waiver callee=ht_create"),
        "{receipts}"
    );
    let unexported = PRODUCER.replacen("#[no_mangle]\n", "", 1);
    assert_ne!(unexported, PRODUCER);
    let out = emitted("r517-9-unexported", &with_prelude(&unexported));
    let receipts = &out.artifacts.return_certificate_receipts;
    assert!(
        !compact(&out.source).contains("->Box<ht>"),
        "{}",
        out.source
    );
    assert!(
        receipts.contains("return-certificate-no-receivers:ht_create"),
        "{receipts}"
    );
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
    // Restated for R517-9: `newNode` IS certified now — its allocation local
    // is a `Box<Node>` returned through the pass-through — so the absence this
    // control pins is the ROTATION owner's, not the program's. `rightRotate`'s
    // own parameter stays raw, which is what `caller-retains` above says.
    let text = compact(&out.source);
    assert!(
        !text.contains("fnrightRotate(muty:Box<Node>)")
            && !text.contains("fnleftRotate(mutx:Box<Node>)"),
        "{}",
        out.source
    );
}

/// **Rung 3, delivered** (R450-8, ruled at relay wave-6a/031 §4): a consuming
/// callee whose owner is a STRUCT — used through its fields and freed there —
/// whose CALLER allocated it with the contract's allocator. The callee side
/// passed since rung 1; the caller side held on `box-initializer-unsupported`,
/// because the ordinary Box arm has no initializer form for a struct pointee.
///
/// The ruling settles which family owns such a binding: **the contract row
/// owns it** (its allocation is the contract's), and **the chain consumes that
/// plan** rather than building a second one. Three things make it work
/// together: the contract reads a call into a consuming formal as the
/// generation's RELEASE (so no implicit close), the chain takes the contract's
/// plan for the caller member exactly as it takes a certificate's (A1-c), and
/// `allocator_contract::confirm_transfers` withdraws the owner if the chain
/// does not plan the formal after all.
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
fn w6a_c1_a_contract_owners_chain_delivers_through_the_consuming_callee() {
    let out = emitted("bp-contract-chain", CONTRACT_OWNER_CHAIN);
    let receipts = &out.artifacts.box_param_receipts;
    let contract = &out.artifacts.allocator_contract_receipts;
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    // The contract row keeps the local — it is not yielded to the fields
    // family — and its generation is released by the callee, so `frees=0`
    // with no implicit close anywhere.
    assert!(
        contract.contains("build_and_retire::n\tadmitted")
            && contract.contains("shape=sized optional=false generations=1 moves_in=0 frees=0"),
        "the contract owns the local\n{contract}"
    );
    assert!(
        !contract.contains("model-owning-is-the-fields-family"),
        "the yield is narrowed for a callee-released owner\n{contract}"
    );
    // The chain plans the formal and names the contract as the member's source.
    assert!(
        receipts.contains(
            "box-param-chain callee=retire index=0 sink=free pointee=Node shape=sized callers=1 members=build_and_retire::n"
        ),
        "{receipts}"
    );
    let text = compact(&out.source);
    assert!(text.contains("fnretire(mutp:Box<Node>)"), "{}", out.source);
    // The drop stays at the C free site; the field uses keep their text; the
    // caller moves the owner at the call.
    assert!(text.contains("drop(p);"), "{}", out.source);
    assert!(
        text.contains("(*p).height=0asi32;") && text.contains("letmutk=(*p).key;"),
        "{}",
        out.source
    );
    assert!(
        text.contains("letmutn:Box<crate::Node>=Box::from_raw(malloc("),
        "{}",
        out.source
    );
    assert!(text.contains("returnretire(n);"), "{}", out.source);
}

const PASS_ON_CHAIN: &str = r#"
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
pub unsafe extern "C" fn sink_free(mut p: *mut Node) -> i32 {
    let mut k = (*p).key;
    free(p as *mut core::ffi::c_void);
    return k;
}
pub unsafe extern "C" fn pass_on(mut q: *mut Node) -> i32 {
    (*q).height = 0 as i32;
    return sink_free(q);
}
pub unsafe extern "C" fn build(mut key: i32) -> i32 {
    let mut n = malloc(::std::mem::size_of::<Node>() as std::os::raw::c_ulong) as *mut Node;
    (*n).key = key;
    return pass_on(n);
}
pub unsafe extern "C" fn reads_it(mut r: *mut Node) -> i32 {
    return (*r).key;
}
pub unsafe extern "C" fn pass_on_to_a_reader(mut s: *mut Node) -> i32 {
    return reads_it(s);
}
pub unsafe extern "C" fn sink_free2(mut p2: *mut Node) -> i32 {
    let mut k = (*p2).key;
    free(p2 as *mut core::ffi::c_void);
    return k;
}
pub unsafe extern "C" fn ping(mut a: *mut Node) -> i32 {
    if (*a).key > 0 as i32 { return pong(a); }
    return 0 as i32;
}
pub unsafe extern "C" fn pong(mut b: *mut Node) -> i32 {
    if (*b).height > 0 as i32 { return ping(b); }
    return 1 as i32;
}
pub unsafe extern "C" fn keeps_after(mut t: *mut Node) -> i32 {
    let mut v = sink_free2(t);
    return v + (*t).height;
}
"#;

/// **Rung 2 (R450-8): the parameter-to-parameter move.** `pass_on` hands its
/// OWN PARAMETER to a consuming callee, so its formal has no free and no store
/// of its own — its sink is the move itself. The chain reads that as a third
/// sink kind and plans `pass_on(q: Box<Node>)`, which makes `pass_on` a
/// consuming callee in turn, so `build`'s allocation local moves into it. One
/// pass of the chain cannot see this: the inner chain must be planned before
/// the outer formal's sink is known, so the derive runs to a depth-bounded
/// fixpoint.
#[test]
fn w6a_c1_a_parameter_moved_on_to_a_consuming_callee_is_an_owner() {
    let out = emitted("bp-pass-on", PASS_ON_CHAIN);
    let text = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    assert!(
        text.contains("fnsink_free(mutp:Box<Node>)"),
        "{}",
        out.source
    );
    assert!(text.contains("fnpass_on(mutq:Box<Node>)"), "{}", out.source);
    assert!(text.contains("drop(p);"), "{}", out.source);
    // The move on keeps its text: a `Box` argument at a `Box` formal.
    assert!(text.contains("returnsink_free(q);"), "{}", out.source);
    assert!(text.contains("returnpass_on(n);"), "{}", out.source);
    assert!(
        text.contains("letmutn:Box<crate::Node>=Box::from_raw(malloc("),
        "{}",
        out.source
    );
    // Control: a formal moved on to a callee that only READS it is not an
    // owner — the move-on relation is over CONSUMING formals, not over calls.
    assert!(
        !text.contains("fnpass_on_to_a_reader(muts:Box<Node>)")
            && !text.contains("fnreads_it(mutr:Box<Node>)"),
        "a reader's argument is not a sink\n{}",
        out.source
    );
    // Control: a formal READ after the move on keeps its raw form — the move
    // is not the last act, so it is not the sink.
    assert!(
        !text.contains("fnkeeps_after(mutt:Box<Node>)"),
        "a use after the move on refuses the owner\n{}",
        out.source
    );
    // Control: a CYCLE in the move-on relation admits nothing and terminates —
    // which is what the depth bound is for. Neither formal ever reaches a free
    // or a store, so no pass can add either, and the loop stops as soon as a
    // pass adds nothing.
    // The move-on chain names its own sink, so the census can count rung 2's
    // rows apart from the frees it never emitted.
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("box-param-chain callee=pass_on index=0 sink=move-on"),
        "{}",
        out.artifacts.box_param_receipts
    );
    assert!(
        !text.contains("fnping(muta:Box<Node>)") && !text.contains("fnpong(mutb:Box<Node>)"),
        "a cycle is not an owner\n{}",
        out.source
    );
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("box-param-chain callee=sink_free index=0 sink=free"),
        "{}",
        out.artifacts.box_param_receipts
    );
}

/// **wave-6a rule W6A-A9 — a lend is not the Box family's subject** (relay
/// wave-6a/043 §A9, /048). The corpus rows the `box-param-callee-lends` hold
/// names are struct-pointer lends: lodepng `filter::settings` /
/// `preProcessScanlines::settings` (`*const LodePNGEncoderSettings`),
/// `inflateNoCompression::reader`, brotli `BrotliBitReaderRestoreState::from`
/// (`*mut BrotliBitReaderState`, read only). Their bodies deref the formal for
/// fields and nothing else — no free, no store, no move on, no return.
///
/// The model calls such a formal `Owning`, so the decide ladder's owning arm
/// claims it and, finding no consumer, degrades it `BoxFailure`. The body
/// proof says the Box family is the WRONG family for it: this rule does not
/// decide what the subject becomes, it declines the ownership claim the body
/// disproves and lets the borrowing arms below decide under their own gates —
/// exactly as they would for a `Ref`-modeled formal.
const STRUCT_LEND: &str = r#"
#[repr(C)]
pub struct Settings {
    pub width: i32,
    pub height: i32,
}
unsafe extern "C" fn area(mut settings: *const Settings) -> i32 {
    return (*settings).width * (*settings).height;
}
pub unsafe extern "C" fn measure() -> i32 {
    let mut s = malloc(::std::mem::size_of::<Settings>()) as *mut Settings;
    (*s).width = 3 as i32;
    (*s).height = 4 as i32;
    let mut a = area(s);
    free(s as *mut core::ffi::c_void);
    return a;
}
"#;

/// The corpus shape whose model verdict is `Owning`: the SAME allocation is
/// lent to one callee and released by another, so the solver carries the
/// ownership into both formals. lodepng's `filter::settings` sits in exactly
/// this position.
const STRUCT_LEND_OWNING: &str = r#"
#[repr(C)]
pub struct Settings {
    pub width: i32,
    pub height: i32,
}
unsafe extern "C" fn area(mut settings: *const Settings) -> i32 {
    return (*settings).width * (*settings).height;
}
unsafe extern "C" fn release(mut settings: *mut Settings) {
    free(settings as *mut core::ffi::c_void);
}
pub unsafe extern "C" fn measure() -> i32 {
    let mut s = malloc(::std::mem::size_of::<Settings>()) as *mut Settings;
    (*s).width = 3 as i32;
    (*s).height = 4 as i32;
    let mut a = area(s);
    release(s);
    return a;
}
"#;

/// Control: the same shape where the callee FREES the formal — the chain is a
/// transfer and the Box family keeps it.
const STRUCT_CONSUMER: &str = r#"
#[repr(C)]
pub struct Settings {
    pub width: i32,
    pub height: i32,
}
unsafe extern "C" fn area_and_release(mut settings: *mut Settings) -> i32 {
    let mut a = (*settings).width * (*settings).height;
    free(settings as *mut core::ffi::c_void);
    return a;
}
pub unsafe extern "C" fn measure() -> i32 {
    let mut s = malloc(::std::mem::size_of::<Settings>()) as *mut Settings;
    (*s).width = 3 as i32;
    (*s).height = 4 as i32;
    return area_and_release(s);
}
"#;

#[test]
fn w6a_a9_the_model_ref_lend_needs_no_rule() {
    // Control, and the reason the rule is keyed on the model's verdict rather
    // than on the body alone: where the model already calls a lent formal
    // `Ref`, the borrowing arms deliver it today — `area(settings: &Settings)`
    // with `area(&*s)` at the caller's `Box`. Nothing is receipted, because
    // the owning arm never claimed it.
    let out = emitted("boxparam-structlend", &with_prelude(STRUCT_LEND));
    let text = compact(&out.source);
    assert!(
        text.contains("fnarea(mutsettings:&Settings)") && text.contains("area(&*s)"),
        "{}",
        out.source
    );
    assert!(
        !out.artifacts
            .box_param_receipts
            .contains("box-param-lend-leaves-owning"),
        "{}",
        out.artifacts.box_param_receipts
    );
}

#[test]
fn w6a_a9_qselect_leaves_the_owning_arm() {
    // The corpus shape (heman `qselect`, and the `box-param-callee-lends`
    // rows of lodepng / brotli): the model calls the lent formal `Owning`, so
    // the owning arm claims it, finds no consumer and degrades it. A9 declines
    // the claim the body disproves and lets the borrowing arms decide.
    let out = emitted("boxparam-qselect", &with_prelude(QSELECT));
    let text = compact(&out.source);
    assert!(
        !text.contains("v:Box<"),
        "a lend is not an owner\n{}",
        out.source
    );
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("qselect::v\tyielded\tbox-param-lend-leaves-owning:qselect"),
        "the lend must be receipted as leaving the owning arm\n{}",
        out.artifacts.box_param_receipts
    );
    assert_ne!(
        reason_of(&out.degradations, "qselect::v").as_deref(),
        Some("box-failure"),
        "the owning arm must not claim a proven lend\n{:?}",
        out.degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn w6a_a9_a_lend_beside_a_release_needs_no_rule() {
    // The second control, and the measurement that keeps A9's market honest:
    // lending one callee and releasing through another does NOT make the
    // model call the lent formal `Owning`. The whole shape delivers with no
    // rule — `area(settings: &Settings)`, `release(settings: Box<Settings>)`
    // with `drop`, and `area(&*s)` / `release(s)` at the caller — so the rows
    // A9 addresses are the narrower ones the model does call `Owning`.
    let out = emitted("boxparam-lendowning", &with_prelude(STRUCT_LEND_OWNING));
    let text = compact(&out.source);
    assert!(
        text.contains("fnarea(mutsettings:&Settings)")
            && text.contains("fnrelease(mutsettings:Box<Settings>)")
            && text.contains("area(&*s)")
            && text.contains("release(s)"),
        "{}",
        out.source
    );
    assert!(
        !out.artifacts
            .box_param_receipts
            .contains("box-param-lend-leaves-owning"),
        "{}",
        out.artifacts.box_param_receipts
    );
    assert!(out.degradations.is_empty(), "{:?}", out.degradations.len());
}

/// Control, and the measurement that decided A9 needs no return clause: the
/// SAME body as `QSELECT` — the one shape in the frame whose lent formal the
/// model calls `Owning` — with one act added, HANDING THE FORMAL BACK. That
/// act is the only one left that could carry the allocation out of the body,
/// and a guard against it would be unwitnessable logic: adding the return
/// makes the model drop the `Owning` verdict (`qselect::v` degrades
/// `slice-use-unsupported`, `percentiles::vals` `kind-raw`), so such a formal
/// never reaches the lend branch at all. This control pins that; if a later
/// frame ever admits one, it fails and the guard goes in.
const QSELECT_RETURNS: &str = r#"
unsafe extern "C" fn qselect(mut v: *mut f32, mut len: i32, mut k: i32) -> *mut f32 {
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
    if k == st { return v; }
    if st > k { return qselect(v, st, k); }
    return qselect(v.offset(st as isize), len - st, k - st);
}
pub unsafe extern "C" fn percentiles(mut n: i32) -> f32 {
    let mut vals = malloc((n as usize).wrapping_mul(::std::mem::size_of::<f32>())) as *mut f32;
    let mut i = 0 as i32;
    while i < n {
        *vals.offset(i as isize) = i as f32;
        i += 1;
    }
    let mut m = *qselect(vals, n, n / 2 as i32);
    free(vals as *mut core::ffi::c_void);
    return m;
}
"#;

#[test]
fn w6a_a9_a_returning_lend_never_reaches_the_branch() {
    let out = emitted("boxparam-qselectreturns", &with_prelude(QSELECT_RETURNS));
    let receipts = &out.artifacts.box_param_receipts;
    assert!(
        !receipts.contains("box-param-lend-leaves-owning"),
        "a formal the body hands back must not leave the owning arm\n{receipts}"
    );
    assert_eq!(
        reason_of(&out.degradations, "qselect::v").as_deref(),
        Some("slice-use-unsupported"),
        "the model must still drop Owning for a returned formal\n{:?}",
        out.degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn w6a_a9_a_consuming_callee_stays_the_box_familys() {
    let out = emitted("boxparam-structconsumer", &with_prelude(STRUCT_CONSUMER));
    assert!(
        !out.artifacts
            .box_param_receipts
            .contains("box-param-lend-leaves-owning"),
        "a callee that frees is not a lend\n{}",
        out.artifacts.box_param_receipts
    );
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("box-param-chain callee=area_and_release index=0 sink=free"),
        "{}",
        out.artifacts.box_param_receipts
    );
}

/// **The nine `box-param-callee-lends` rows, reduced** (relay wave-6a/050).
/// Five are signature-only — the body reads or writes FIELDS of the formal —
/// and four walk elements through `offset`. Each is its own callee here, with
/// one caller that allocates, lends and frees, so every formal is an
/// `Owning`-modeled lend of exactly the corpus shape.
const NINE_SHAPES: &str = r#"
#[repr(C)]
pub struct Reader { pub val_: u64, pub bit_pos_: u32 }
#[repr(C)]
pub struct Settings { pub width: i32, pub height: i32 }
/// brotli `BrotliBitReaderRestoreState::from`: read-only field copies.
unsafe extern "C" fn restore_state(mut to: *mut Reader, mut from: *mut Reader) {
    (*to).val_ = (*from).val_;
    (*to).bit_pos_ = (*from).bit_pos_;
}
/// lodepng `filter::settings` / `preProcessScanlines::settings`: read-only.
unsafe extern "C" fn area(mut settings: *const Settings) -> i32 {
    return (*settings).width * (*settings).height;
}
/// lodepng `inflateNoCompression::reader`: a field WRITE.
unsafe extern "C" fn advance(mut reader: *mut Reader) {
    (*reader).bit_pos_ = (*reader).bit_pos_.wrapping_add(8 as u32);
}
/// heman `edt_with_payload::payload_out` / `generate_gaussian_row::target`:
/// element stores through `offset`.
unsafe extern "C" fn fill(mut target: *mut f32, mut n: i32) {
    let mut i = 0 as i32;
    while i < n {
        *target.offset(i as isize) = i as f32;
        i += 1;
    }
}
pub unsafe extern "C" fn drive(mut n: i32) -> i32 {
    let mut a = malloc(::std::mem::size_of::<Reader>()) as *mut Reader;
    let mut b = malloc(::std::mem::size_of::<Reader>()) as *mut Reader;
    (*b).val_ = 1 as u64;
    restore_state(a, b);
    advance(a);
    let mut s = malloc(::std::mem::size_of::<Settings>()) as *mut Settings;
    (*s).width = 2 as i32;
    (*s).height = 3 as i32;
    let mut q = area(s);
    let mut v = calloc(n as usize, ::std::mem::size_of::<f32>()) as *mut f32;
    fill(v, n);
    free(v as *mut core::ffi::c_void);
    free(s as *mut core::ffi::c_void);
    free(b as *mut core::ffi::c_void);
    free(a as *mut core::ffi::c_void);
    return q;
}
"#;

#[test]
fn w6a_a9_the_nine_shapes_take_their_form_from_the_write_facts() {
    // Relay 050 correction 1: the decline decides nothing, so the borrowing
    // arms must read the mutability facts — a uniform shared form at a written
    // formal would be the defect. Measured on all four shapes at once:
    //   restore_state  to written / from read  ->  &mut Reader / &Reader
    //   area           read only               ->  &Settings (needs no rule:
    //                                               the model calls it Ref)
    //   advance        a field write           ->  &mut Reader
    //   fill           element stores          ->  &mut [f32]
    // The last answers relay 050's open question for heman's four: the slice
    // arm DOES render a callee's `offset` element uses as indexing.
    let out = emitted("boxparam-nine", &with_prelude(NINE_SHAPES));
    let text = compact(&out.source);
    for (signature, why) in [
        (
            "fnrestore_state(mutto:&mutReader,mutfrom:&Reader)",
            "the written and read halves split",
        ),
        (
            "fnarea(mutsettings:&Settings)",
            "a read-only lend is shared",
        ),
        (
            "fnadvance(mutreader:&mutReader)",
            "a field write takes &mut",
        ),
        (
            "fnfill(muttarget:&mut[f32],mutn:i32)",
            "element stores take a mutable slice",
        ),
    ] {
        assert!(
            text.contains(signature),
            "{why}: {signature}\n{}",
            out.source
        );
    }
    let receipts = &out.artifacts.box_param_receipts;
    for parameter in [
        "restore_state::to",
        "restore_state::from",
        "advance::reader",
        "fill::target",
    ] {
        assert!(
            receipts.contains(&format!(
                "{parameter}\tyielded\tbox-param-lend-leaves-owning:"
            )),
            "{parameter} must be a declined claim\n{receipts}"
        );
    }
    assert!(
        !receipts.contains("area::settings"),
        "a Ref-modeled lend needs no decline\n{receipts}"
    );
}

/// **W6A-A9's companion gate** (report 044, option (c)). A struct with a field
/// another family OWNS — the model calls the field slot `Owning` — is not a
/// struct whose formal A9 may decline: a reference formal puts the deallocator
/// argument behind an A5 raw view, and the owned field's edit cannot live
/// inside one. Measured on wave-6f's own fixture before this control was
/// written: without the gate their whole program DEGRADES
/// (`field-transaction-a5-raw-view:owned-edit-inside-view`); with it the
/// program emits, `reverted=0`, and the field keeps its `opt-box` delivery.
///
/// Here the same shape stands on its own frame, with no other lane's file
/// involved: `Owner::slot_` is forced `Owning`, and the two formals that only
/// lend the owner are held with the typed reason rather than declined.
const OWNED_FIELD_LEND: &str = r#"
// w6a-a9-owned-field-frame
#[repr(C)]
pub struct Owner {
    pub count: i32,
    pub slot_: *mut i32,
}
unsafe extern "C" fn read_count(mut o: *mut Owner) -> i32 {
    return (*o).count;
}
unsafe extern "C" fn bump(mut o: *mut Owner) {
    (*o).count = (*o).count + 1 as i32;
}
pub unsafe extern "C" fn drive() -> i32 {
    let mut o = malloc(::std::mem::size_of::<Owner>()) as *mut Owner;
    (*o).count = 0 as i32;
    (*o).slot_ = malloc(::std::mem::size_of::<i32>()) as *mut i32;
    bump(o);
    let mut c = read_count(o);
    free((*o).slot_ as *mut core::ffi::c_void);
    free(o as *mut core::ffi::c_void);
    return c;
}
"#;

#[test]
fn w6a_a9_an_owned_field_keeps_the_formal() {
    use crate::analyses::borrow_ownership::SlotKind;
    // R528-2: the override is global state; the crate-wide lock serializes
    // it against every other test that sets or reads one.
    let _frame = super::test_model_override::frame_lock();
    super::test_model_override::set_with_contract(
        "w6a-a9-owned-field-frame",
        vec![("Owner".to_owned(), 1, SlotKind::Owning)],
        Vec::new(),
        Vec::new(),
    );
    let out = emitted("boxparam-ownedfield", &with_prelude(OWNED_FIELD_LEND));
    super::test_model_override::clear();
    let receipts = &out.artifacts.box_param_receipts;
    assert!(
        receipts.contains("bump::o\theld\tbox-param-callee-lends-owned-field:"),
        "bump::o must keep its formal for the owned field\n{receipts}"
    );
    // Re-pinned at the L01⁸ frame landing (era-5c report 064): `read_count`
    // stores nothing and frees nothing, so era 5b's reader certificate
    // (`readers::Plan::borrows_parameter`, the C02 borrowed call role, active
    // in both passes) lends its formal at the call: the formal is zeroed,
    // never Owning, and no box-param subject. Give it a store and the held
    // receipt returns (measured).
    assert!(
        !receipts.contains("read_count::o\t"),
        "read_count::o is a certified reader's formal, not a box parameter\n{receipts}"
    );
    assert!(
        !receipts.contains("box-param-lend-leaves-owning"),
        "no formal of an owned-field struct is declined\n{receipts}"
    );
}

/// **R531-4 (vii) — A9's companion gate admits a HELD owned field**, the
/// parameter-side mirror of `4ffa35319`. The gate kept the formal because a
/// DELIVERED owned field's edit cannot live inside the A5 raw view a
/// reference formal puts its deallocator argument behind; the control above
/// is that case and still holds. Here `slot_` is indexed and its store has no
/// length, so its transaction is held, the field stays `*mut i32`, there is
/// no edit to put inside a view — and the two lends are declined as A9 says.
#[test]
fn w6a_r531_a9_a_held_owned_field_declines_the_lend() {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = super::test_model_override::frame_lock();
    let source = OWNED_FIELD_LEND
        .replace("// w6a-a9-owned-field-frame", "// w6a-r531-held-owned-field-frame")
        .replace(
            "    (*o).slot_ = malloc(::std::mem::size_of::<i32>()) as *mut i32;\n",
            "    (*o).slot_ = calloc(4 as usize, ::std::mem::size_of::<i32>()) as *mut i32;\n    *(*o).slot_.offset(1 as isize) = 3 as i32;\n",
        );
    assert!(
        source.contains("offset(1 as isize)"),
        "the fixture must index the field"
    );
    super::test_model_override::set_with_contract(
        "w6a-r531-held-owned-field-frame",
        vec![("Owner".to_owned(), 1, SlotKind::Owning)],
        Vec::new(),
        Vec::new(),
    );
    let out = emitted("r531-a9-held-field", &with_prelude(&source));
    super::test_model_override::clear();
    let receipts = &out.artifacts.box_param_receipts;
    assert!(
        receipts.contains("bump::o\tyielded\tbox-param-lend-leaves-owning:"),
        "bump::o is declined: its field's transaction is held\n{receipts}"
    );
    // Re-pinned at the L01⁸ frame landing (era-5c report 064): era 5b's
    // reader certificate lends `read_count`'s formal (see the control above).
    assert!(
        !receipts.contains("read_count::o\t"),
        "read_count::o is a certified reader's formal, not a box parameter\n{receipts}"
    );
    assert!(!receipts.contains("callee-lends-owned-field"), "{receipts}");
    assert!(
        compact(&out.source).contains("pubslot_:*muti32"),
        "the held field stays raw\n{}",
        out.source
    );
}

/// quadtree's `quadtree_new` → `test_tree` → `quadtree_free` reduced: the
/// producer can return null, so its certificate makes the receiver an
/// `Option<Box<tree_t>>`; the receiver is handed to a consuming callee that
/// reads through its formal and frees it.
const OPTIONAL_OWNER_CHAIN: &str = r#"
#[repr(C)]
pub struct tree_t { pub length: u32, pub depth: i32, pub root: *mut i32 }
pub unsafe extern "C" fn tree_new() -> *mut tree_t {
    let mut tree = 0 as *mut tree_t;
    tree = malloc(::std::mem::size_of::<tree_t>()) as *mut tree_t;
    if tree.is_null() { return 0 as *mut tree_t; }
    (*tree).length = 0 as u32;
    (*tree).depth = 0 as i32;
    (*tree).root = malloc(::std::mem::size_of::<i32>()) as *mut i32;
    if ((*tree).root).is_null() {
        free(tree as *mut core::ffi::c_void);
        return 0 as *mut tree_t;
    }
    return tree;
}
pub unsafe extern "C" fn tree_free(mut tree: *mut tree_t) {
    (*tree).depth = 0 as i32;
    free((*tree).root as *mut core::ffi::c_void);
    free(tree as *mut core::ffi::c_void);
}
pub unsafe extern "C" fn run() -> u32 {
    let mut tree = tree_new();
    let mut n = (*tree).length;
    tree_free(tree);
    return n;
}
"#;

/// **R531-4 (iii) — a C1 chain moves an OPTIONAL owner.** The certificate's
/// receiver is `Option<Box<tree_t>>` (the producer may return null), so the
/// consuming formal takes the same type — `free(NULL)` is legal C and
/// `drop(None)` is its image — and its derefs read through
/// `as_deref_mut().unwrap()`. The call moves the owner as written. Before
/// this, the chain refused `box-param-caller-retains:run:optional-owner` and
/// the certificate withdrew `transfer-unconfirmed` (quadtree, report 076 §4).
#[test]
fn w6a_r531_an_optional_owner_moves_into_a_consuming_formal() {
    let out = emitted("r531-owner-moves", &with_prelude(OPTIONAL_OWNER_CHAIN));
    let src = compact(&out.source);
    let receipts = format!(
        "{}\n{}",
        out.artifacts.box_param_receipts, out.artifacts.return_certificate_receipts
    );
    assert_eq!(out.reverted, 0, "{}\n{receipts}", out.source);
    assert!(
        src.contains("fntree_new()->Option<Box<tree_t>>"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        src.contains("fntree_free(muttree:Option<Box<tree_t>>)"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        src.contains("(*tree.as_deref_mut().unwrap()).depth=0asi32;"),
        "{}",
        out.source
    );
    assert!(
        src.contains(
            "free((*tree.as_deref_mut().unwrap()).rootas*mutcore::ffi::c_void);drop(tree);"
        ),
        "{}",
        out.source
    );
    assert!(src.contains("tree_free(tree);"), "{}", out.source);
    assert!(
        !receipts.contains(":optional-owner") && !receipts.contains("transfer-unconfirmed"),
        "{receipts}"
    );
}

/// **R561-4 W2 — a mixed chain** (restates R531-4 (iii)'s control, which pinned
/// the hold this rule lifts). A second caller hands the same formal a
/// NON-optional owner: the formal is `Option<Box<T>>` for the whole chain and
/// that caller passes `Some(t)`; `drop(Some(b))` is `free(b)`. buffer's
/// `buffer_free` is this shape — five `buffer_slice` receivers optional,
/// nineteen constructor receivers not (report 095).
#[test]
fn w6a_r561_a_mixed_optional_chain_takes_the_option_formal() {
    let source = OPTIONAL_OWNER_CHAIN.replace(
        "    return n;\n}\n",
        "    return n;\n}\npub unsafe extern \"C\" fn run_sized() {\n    let mut t = malloc(::std::mem::size_of::<tree_t>()) as *mut tree_t;\n    (*t).length = 1 as u32;\n    (*t).depth = 1 as i32;\n    (*t).root = 0 as *mut i32;\n    tree_free(t);\n}\n",
    );
    assert_ne!(source, OPTIONAL_OWNER_CHAIN);
    let out = emitted("r561-optional-mixed", &with_prelude(&source));
    let src = compact(&out.source);
    let receipts = format!(
        "{}\n{}",
        out.artifacts.box_param_receipts, out.artifacts.return_certificate_receipts
    );
    assert_eq!(out.reverted, 0, "{}\n{receipts}", out.source);
    assert!(
        src.contains("fntree_free(muttree:Option<Box<tree_t>>)"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        src.contains("tree_free(Some(t));"),
        "{}\n{receipts}",
        out.source
    );
    assert!(src.contains("tree_free(tree);"), "{}", out.source);
    assert!(!receipts.contains("optional-owner-mixed"), "{receipts}");
    assert_eq!(
        reason_of(&out.degradations, "run_sized::t"),
        None,
        "{:#?}",
        out.degradations
    );
}

/// **R561-4 W1 at the chain.** buffer's `test_buffer_trim` re-seats one
/// certified receiver through the consuming callee: `buffer_free(buf); buf =
/// buffer_new_with_copy(..); .. buffer_free(buf);` ×3. Each call moves one
/// generation, and a use after the call belongs to the next generation once a
/// re-seat stands between them, so the chain must not read the re-seat as a
/// use of the moved owner (`used-after-transfer`). With an optional member in
/// the same chain (W2), every call of the re-seated member takes `Some(..)`,
/// not only the first.
#[test]
fn w6a_r561_a_reseated_member_moves_one_generation_per_call() {
    let source = OPTIONAL_OWNER_CHAIN.replace(
        "    return n;\n}\n",
        "    return n;\n}\npub unsafe extern \"C\" fn tree_make(mut n: u32) -> *mut tree_t {\n    let mut t = malloc(::std::mem::size_of::<tree_t>()) as *mut tree_t;\n    if t.is_null() { return 0 as *mut tree_t; }\n    (*t).length = n;\n    (*t).depth = 0 as i32;\n    (*t).root = malloc(::std::mem::size_of::<i32>()) as *mut i32;\n    return t;\n}\npub unsafe extern \"C\" fn run_trim() -> u32 {\n    let mut t = tree_make(1 as u32);\n    let mut n = (*t).length;\n    tree_free(t);\n    t = tree_make(2 as u32);\n    n = n.wrapping_add((*t).length);\n    tree_free(t);\n    t = tree_make(3 as u32);\n    n = n.wrapping_add((*t).length);\n    tree_free(t);\n    return n;\n}\n",
    );
    assert_ne!(source, OPTIONAL_OWNER_CHAIN);
    let out = emitted("r561-reseat-chain", &with_prelude(&source));
    let src = compact(&out.source);
    let receipts = format!(
        "{}\n{}",
        out.artifacts.box_param_receipts, out.artifacts.return_certificate_receipts
    );
    assert_eq!(out.reverted, 0, "{}\n{receipts}", out.source);
    assert!(!receipts.contains("used-after-transfer"), "{receipts}");
    assert!(
        src.contains("fntree_free(muttree:Option<Box<tree_t>>)"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        src.contains("letmutt:Box<crate::tree_t>=tree_make(1asu32);"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        src.contains("tree_free(Some(t));t=tree_make(2asu32);"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        src.contains("tree_free(Some(t));t=tree_make(3asu32);"),
        "{}\n{receipts}",
        out.source
    );
    assert_eq!(
        src.matches("tree_free(Some(t));").count(),
        3,
        "every generation's call is wrapped:\n{}",
        out.source
    );
    assert!(src.contains("tree_free(tree);"), "{}", out.source);
    assert_eq!(
        reason_of(&out.degradations, "run_trim::t"),
        None,
        "{:#?}\n{receipts}",
        out.degradations
    );
}

/// ht's surface: an exported producer, an exported consumer, and a third
/// exported signature that lends the pointee (the corpus's `ht_get` /
/// `ht_set`), so R427-4's closure holds and nothing in the program calls
/// `ht_destroy`.
const EXPORTED_CONSUMER: &str = r#"
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
pub unsafe extern "C" fn ht_length(mut table: *mut ht) -> usize { return (*table).length; }
#[no_mangle]
pub unsafe extern "C" fn ht_destroy(mut table: *mut ht) {
    (*table).length = 0 as usize;
    free(table as *mut core::ffi::c_void);
}
"#;

/// **R534-1 (USER) — the exported-consumer waiver**, the mirror of R517-9's
/// producer. An exported consumer nothing in the program calls, whose body
/// consumes its formal (C1's proof: one free, no store, no move on), takes
/// `Option<Box<ht>>`: the caller is outside the program, its handle may be
/// null (`free(NULL)` is legal C), and under R443 the block is one the system
/// allocator made, released by our drop at the C free site. Two controls, as
/// ruled: the exported LENDING body in the same program (`ht_length`) is not
/// waived, and the same consumer without `#[no_mangle]` keeps
/// `box-param-no-callers`.
#[test]
fn w6a_r531_an_exported_consumer_takes_the_box_under_the_waiver() {
    let out = emitted("r531-exported-consumer", &with_prelude(EXPORTED_CONSUMER));
    let src = compact(&out.source);
    let receipts = &out.artifacts.box_param_receipts;
    assert_eq!(out.reverted, 0, "{}\n{receipts}", out.source);
    assert!(
        src.contains(
            "fnht_destroy(muttable:Option<Box<ht>>){(*table.as_deref_mut().unwrap()).length=0asusize;drop(table);}"
        ),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        receipts.contains("exported-consumer-waiver callee=ht_destroy"),
        "{receipts}"
    );
    assert!(
        !src.contains("fnht_length(muttable:Option<Box<ht>>)")
            && !src.contains("fnht_length(muttable:Box<ht>)")
            && !receipts.contains("exported-consumer-waiver callee=ht_length"),
        "a lending body is not waived\n{}\n{receipts}",
        out.source
    );
    let unexported = EXPORTED_CONSUMER.replace(
        "#[no_mangle]\npub unsafe extern \"C\" fn ht_destroy",
        "pub unsafe extern \"C\" fn ht_destroy",
    );
    assert_ne!(unexported, EXPORTED_CONSUMER);
    let out = emitted("r531-unexported-consumer", &with_prelude(&unexported));
    assert!(
        !compact(&out.source).contains("table:Box<ht>"),
        "{}",
        out.source
    );
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("ht_destroy::table\theld\tbox-param-no-callers:ht_destroy"),
        "{}",
        out.artifacts.box_param_receipts
    );
}

/// A consumer whose body tests its formal for null: the owner walk renders
/// the test as `is_none()` on the waived `Option<Box<ht>>`.
#[test]
fn w6a_r531_a_null_testing_exported_consumer_takes_an_option() {
    let source = EXPORTED_CONSUMER.replace(
        "    (*table).length = 0 as usize;\n    free(table",
        "    if table.is_null() { return; }\n    (*table).length = 0 as usize;\n    free(table",
    );
    assert_ne!(source, EXPORTED_CONSUMER);
    let out = emitted("r531-exported-consumer-null", &with_prelude(&source));
    let src = compact(&out.source);
    let receipts = &out.artifacts.box_param_receipts;
    assert_eq!(out.reverted, 0, "{}\n{receipts}", out.source);
    assert!(
        src.contains("fnht_destroy(muttable:Option<Box<ht>>)"),
        "{}\n{receipts}",
        out.source
    );
    assert!(src.contains("iftable.is_none(){return;}"), "{}", out.source);
    assert!(
        receipts.contains("exported-consumer-waiver callee=ht_destroy"),
        "{receipts}"
    );
}

/// Controls for the waiver's sink: an exported function nothing calls that
/// STORES its formal into the program's own storage, and one that MOVES it on
/// into a consuming callee, are not consumers by C1's proof of a free — the
/// ruling licenses the free alone — so neither is waived. The waived formal
/// is rendered by the certificate's owner walk, and that walk refuses a store
/// or a transfer of it (`optional-owner-escapes`).
#[test]
fn w6a_r534_a_storing_or_moving_export_is_not_waived() {
    const STORE: &str = r#"
#[repr(C)]
pub struct ht { pub length: usize }
#[repr(C)]
pub struct registry { pub table: *mut ht }
#[no_mangle]
pub unsafe extern "C" fn ht_park(mut holder: *mut registry, mut table: *mut ht) {
    (*table).length = 1 as usize;
    (*holder).table = table;
}
"#;
    const MOVE_ON: &str = r#"
#[repr(C)]
pub struct ht { pub length: usize }
unsafe extern "C" fn ht_sink(mut table: *mut ht) {
    free(table as *mut core::ffi::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn ht_release(mut table: *mut ht) {
    (*table).length = 0 as usize;
    ht_sink(table);
}
"#;
    for (name, source, formal) in [
        ("r534-store", STORE, "fnht_park"),
        ("r534-move-on", MOVE_ON, "fnht_release"),
    ] {
        let out = emitted(name, &with_prelude(source));
        let src = compact(&out.source);
        let receipts = &out.artifacts.box_param_receipts;
        assert!(
            receipts.contains("optional-owner-escapes"),
            "{name}: the owner walk refuses the sink\n{receipts}"
        );
        assert!(
            !receipts.contains("exported-consumer-waiver"),
            "{name}\n{receipts}"
        );
        assert!(src.contains(formal), "{name}: {}", out.source);
        assert!(
            !src.contains("table:Option<Box<ht>>"),
            "{name}: {}\n{receipts}",
            out.source
        );
    }
}

/// **R536-5 — the two exported-surface waivers, counted per program.** ht's
/// surface emits both: `ht_create` under the exported-producer waiver
/// (R517-9, in the certificate receipts) and `ht_destroy` under the
/// exported-consumer waiver (R534-1, in the box-parameter receipts). The
/// census counts each from the table it publishes, ADMITTED rows only, and
/// both tables are registered in the artifact set.
#[test]
fn w6a_r536_the_exported_waivers_are_counted_per_program() {
    let out = emitted("r536-waiver-columns", &with_prelude(EXPORTED_CONSUMER));
    assert_eq!(
        crate::bo_c1::exported_waiver_counts(&out.artifacts),
        (1, 1),
        "{}\n{}",
        out.artifacts.return_certificate_receipts,
        out.artifacts.box_param_receipts
    );
    let unexported = EXPORTED_CONSUMER.replace("#[no_mangle]\n", "");
    let out = emitted("r536-waiver-columns-none", &with_prelude(&unexported));
    assert_eq!(crate::bo_c1::exported_waiver_counts(&out.artifacts), (0, 0));
    let census = include_str!("../bo_c1.rs");
    for registered in [
        "(\"box-param-receipt\", artifact.box_param_receipts.as_str())",
        "stamp(&artifact.return_certificate_receipts),",
        "row.set(raw_schema::EXPORTED_PRODUCER_WAIVER, producers.to_string());",
        "row.set(raw_schema::EXPORTED_CONSUMER_WAIVER, consumers.to_string());",
    ] {
        assert!(census.contains(registered), "{registered}");
    }
    // R450-9: two additive columns of their own.
    let all = crate::raw_boundary_census_schema::ALL;
    assert!(all.contains(&crate::raw_boundary_census_schema::EXPORTED_PRODUCER_WAIVER));
    assert!(all.contains(&crate::raw_boundary_census_schema::EXPORTED_CONSUMER_WAIVER));
    assert_ne!(
        crate::raw_boundary_census_schema::EXPORTED_PRODUCER_WAIVER,
        crate::raw_boundary_census_schema::EXPORTED_CONSUMER_WAIVER
    );
}

/// bst reduced (R536-3): `insert` consumes its formal and returns it — the
/// re-seat `root = insert(root, key)` — and re-seats the owned children with
/// `(*node).left = insert((*node).left, key)`. The model is L01⁶'s on the
/// corpus: both children `Owning`, and `insert::node` `Owning`.
const BST_RESEAT: &str = r#"
// w6a-r536-bst-reseat-frame
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct node {
    pub key: i32,
    pub left: *mut node,
    pub right: *mut node,
}
pub unsafe extern "C" fn newNode(mut item: i32) -> *mut node {
    let mut temp = malloc(::std::mem::size_of::<node>()) as *mut node;
    (*temp).key = item;
    (*temp).left = 0 as *mut node;
    (*temp).right = 0 as *mut node;
    return temp;
}
#[no_mangle]
pub unsafe extern "C" fn insert(mut node: *mut node, mut key: i32) -> *mut node {
    if node.is_null() {
        return newNode(key);
    }
    if key < (*node).key {
        (*node).left = insert((*node).left, key);
    } else {
        (*node).right = insert((*node).right, key);
    }
    return node;
}
"#;

fn bst_reseat(name: &str, source: &str) -> super::wave6a_allocation_tests::Emitted {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = super::test_model_override::frame_lock();
    super::test_model_override::set_with_contract(
        "w6a-r536-bst-reseat-frame",
        vec![
            ("node".to_owned(), 1, SlotKind::Owning),
            ("node".to_owned(), 2, SlotKind::Owning),
        ],
        vec![("insert::node".to_owned(), SlotKind::Owning)],
        Vec::new(),
    );
    let out = emitted(name, source);
    super::test_model_override::clear();
    out
}

/// **R536-3 — the re-seat.** `insert::node` is not a lend (A9's gate asked it
/// the wrong question): the body consumes the formal and hands it back. It
/// takes `Option<Box<node>>`, its null test reads `is_none()`, and the
/// recursive calls move each owned child out with `.take()`.
///
/// Restated for R579-4: the re-seated formal is the owner `insert`'s return
/// certificate reads (R2), so the return is certified — `-> Option<Box<node>>`,
/// `return node` (C1), `return Some(newNode(key))` — and the result goes back
/// into the field as a plain move (C2) where it went through `Box::into_raw`
/// and wave-6f's `from_raw` bridge.
#[test]
fn w6a_r536_a_consumed_and_returned_formal_is_reseated() {
    let out = bst_reseat("r536-bst-reseat", BST_RESEAT);
    let src = compact(&out.source);
    let receipts = &out.artifacts.box_param_receipts;
    assert_eq!(out.reverted, 0, "{}\n{receipts}", out.source);
    assert!(
        receipts.contains("box-param-reseat callee=insert index=0 fields=2"),
        "{receipts}"
    );
    assert!(
        src.contains("fninsert(mutnode:Option<Box<node>>,mutkey:i32)->Option<Box<node>>"),
        "{}",
        out.source
    );
    assert!(src.contains("ifnode.is_none(){"), "{}", out.source);
    assert!(src.contains("returnnode;"), "{}", out.source);
    assert!(src.contains("returnSome(newNode(key));"), "{}", out.source);
    assert!(src.contains(".left.take()"), "{}", out.source);
    assert!(
        !src.contains("into_raw") && !src.contains("from_raw"),
        "{}",
        out.source
    );
    assert_eq!(
        reason_of(&out.degradations, "insert::node"),
        None,
        "{receipts}"
    );
}

/// Control: a call that does not store its result back into the field it
/// moved out of would leave that field `None` where C left it intact, so the
/// re-seat holds.
#[test]
fn w6a_r536_a_reseat_needs_the_result_stored_back() {
    let discarded = BST_RESEAT.replace(
        "        (*node).left = insert((*node).left, key);\n",
        "        insert((*node).left, key);\n",
    );
    assert_ne!(discarded, BST_RESEAT);
    let out = bst_reseat("r536-bst-discarded", &discarded);
    let receipts = &out.artifacts.box_param_receipts;
    assert!(
        receipts.contains("box-param-reseat-caller:insert:insert((*node).left, key)"),
        "{receipts}"
    );
    assert!(
        !compact(&out.source).contains("node:Option<Box<node>>"),
        "{}",
        out.source
    );
}

/// Control: the same `insert` where the children are NOT owned fields (no
/// transaction delivers them, so they stay `*mut node`). The call sites would
/// hand a raw pointer to the `Option<Box<node>>` formal, so after the field
/// transactions finalize the re-seat is withdrawn with a typed hold and the
/// stage re-derives.
#[test]
fn w6a_r536_a_reseat_over_raw_fields_is_withdrawn() {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = super::test_model_override::frame_lock();
    let source = BST_RESEAT.replace(
        "// w6a-r536-bst-reseat-frame",
        "// w6a-r536-raw-fields-frame",
    );
    super::test_model_override::set_with_contract(
        "w6a-r536-raw-fields-frame",
        Vec::new(),
        vec![("insert::node".to_owned(), SlotKind::Owning)],
        Vec::new(),
    );
    let out = emitted("r536-bst-raw-fields", &source);
    super::test_model_override::clear();
    let receipts = &out.artifacts.box_param_receipts;
    assert!(
        receipts.contains("insert::node\theld\tbox-param-reseat-field-not-delivered:insert"),
        "{receipts}\n{}",
        out.source
    );
    assert!(
        !compact(&out.source).contains("node:Option<Box<node>>"),
        "{}",
        out.source
    );
    assert_eq!(out.reverted, 0, "{}", out.source);
}

/// **R645-12 (a), wave-6s 091 STOP 2 — a re-seat formal spelled through a
/// pointer alias.** `insert` consumes and returns a node spelled
/// `tree::node_t` (`= *mut hidden::node`, the corpus's module-nested shape),
/// and its one caller re-seats an owned field of ANOTHER struct,
/// `(*h).a = insert((*h).a, key)` (a struct an alias mentions holds its own
/// fields, `field-transaction-incomplete:type-alias`, so bst's self-referential
/// `node` never gets this far). Where `hidden` is public the re-seat delivers
/// over the alias's resolved pointee (W6S-17); where it is private to `tree`
/// the owner cannot name the pointee, so the re-seat holds typed
/// (`box-param-alias-formal`), as a chain's formal does, and the owned field
/// crosses the raw formal by value. Planned instead, the formal is degraded
/// under a caller that moves the field out as a `Box`: the emitted crate
/// fails (E0603 on the spelled pointee, E0308 at the move) and its classes
/// revert.
const RESEAT_ALIAS: &str = r#"
// w6a-r645-reseat-alias-frame
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
pub mod tree {
    pub mod hidden {
        #[repr(C)]
        pub struct node {
            pub key: i32,
        }
    }
    #[repr(C)]
    pub struct holder {
        pub a: *mut hidden::node,
        pub n: i32,
    }
    pub type node_t = *mut hidden::node;
}
#[no_mangle]
pub unsafe extern "C" fn insert(mut node: tree::node_t, mut key: i32) -> tree::node_t {
    if node.is_null() {
        return 0 as tree::node_t;
    }
    (*node).key = key;
    return node;
}
#[no_mangle]
pub unsafe extern "C" fn put(mut h: *mut tree::holder, mut key: i32) {
    (*h).a = insert((*h).a, key);
}
"#;

fn reseat_alias(name: &str, source: &str) -> super::wave6a_allocation_tests::Emitted {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = super::test_model_override::frame_lock();
    super::test_model_override::set_with_contract(
        "w6a-r645-reseat-alias-frame",
        vec![("holder".to_owned(), 0, SlotKind::Owning)],
        vec![("insert::node".to_owned(), SlotKind::Owning)],
        Vec::new(),
    );
    let out = emitted(name, source);
    super::test_model_override::clear();
    out
}

#[test]
fn w6a_r645_a_reseat_formal_spelled_through_an_alias_holds_an_unnameable_pointee() {
    let out = reseat_alias("r645-reseat-alias", RESEAT_ALIAS);
    let src = compact(&out.source);
    let receipts = &out.artifacts.box_param_receipts;
    let context = format!(
        "{receipts}\n{}\n{}\n{:#?}",
        out.source, out.artifacts.field_transactions, out.degradations
    );
    assert!(
        receipts.contains("box-param-reseat callee=insert index=0 fields=1"),
        "{context}"
    );
    assert!(
        src.contains("fninsert(mutnode:Option<Box<crate::tree::hidden::node>>,"),
        "{context}"
    );
    assert!(src.contains(".a.take()"), "{context}");
    assert_eq!(
        reason_of(&out.degradations, "insert::node"),
        None,
        "{context}"
    );
    assert_eq!(out.reverted, 0, "{context}");

    let hidden = RESEAT_ALIAS.replace("    pub mod hidden {", "    mod hidden {");
    assert_ne!(hidden, RESEAT_ALIAS);
    let out = reseat_alias("r645-reseat-alias-unnameable", &hidden);
    let src = compact(&out.source);
    let receipts = &out.artifacts.box_param_receipts;
    let context = format!(
        "{receipts}\n{}\n{}\n{:#?}",
        out.source, out.artifacts.field_transactions, out.degradations
    );
    assert!(
        receipts.contains("insert::node\theld\tbox-param-alias-formal:insert"),
        "{context}"
    );
    assert!(
        !receipts.contains("box-param-reseat callee=insert "),
        "{context}"
    );
    // The formal stays raw, and the owned field crosses it by value: out
    // through `Box::into_raw`, back through `from_raw` (wave-6f's raw move).
    assert!(
        src.contains("fninsert(mutnode:tree::node_t,mutkey:i32)->tree::node_t{"),
        "{context}"
    );
    assert!(
        src.contains("insert((*h).a.take().map_or(core::ptr::null_mut(),Box::into_raw),key)"),
        "{context}"
    );
    assert!(!src.contains("as_mut())"), "{context}");
    assert_eq!(out.reverted, 0, "{context}");
}

/// quadtree's `test_tree`, reduced: an optional Box owner (`tree_new` may
/// return null) whose raw field `root` is passed to a callee that decides
/// `&mut`. Since joint (d) (R555-1) the owner view is the OWNER's, so
/// `(*tree).root` is no longer read as the owner's view: it crosses at the C
/// arm (`c-raw-reborrow-mut`), whose interval strictly contains the owner's
/// own `box-expression` edit of `(*tree)`. That is a composition the seam pass
/// renders around the grafted operand, like the `("c-raw-slice-shared",
/// "box-expression")` row. Held, it cost quadtree 23 → 12 at batch 34′
/// (`cross-class-interval-collision`, then `dependency-class-held`).
const QUADTREE_WALK_OF_BOX_FIELD: &str = r#"
#[repr(C)]
pub struct node_t { pub nw: *mut node_t, pub count: i32 }
#[repr(C)]
pub struct tree_t { pub root: *mut node_t, pub length: u32 }
pub unsafe extern "C" fn node_new() -> *mut node_t {
    let mut node = 0 as *mut node_t;
    node = malloc(::std::mem::size_of::<node_t>()) as *mut node_t;
    if node.is_null() { return 0 as *mut node_t; }
    (*node).nw = 0 as *mut node_t;
    (*node).count = 0 as i32;
    return node;
}
pub unsafe extern "C" fn tree_new() -> *mut tree_t {
    let mut tree = 0 as *mut tree_t;
    tree = malloc(::std::mem::size_of::<tree_t>()) as *mut tree_t;
    if tree.is_null() { return 0 as *mut tree_t; }
    (*tree).root = node_new();
    if ((*tree).root).is_null() {
        free(tree as *mut core::ffi::c_void);
        return 0 as *mut tree_t;
    }
    (*tree).length = 0 as u32;
    return tree;
}
pub unsafe extern "C" fn tree_free(mut tree: *mut tree_t) {
    free((*tree).root as *mut core::ffi::c_void);
    free(tree as *mut core::ffi::c_void);
}
pub unsafe extern "C" fn walk(mut root: *mut node_t) {
    (*root).count += 1 as i32;
    if !((*root).nw).is_null() {
        walk((*root).nw);
    }
}
pub unsafe extern "C" fn test_tree() {
    let mut tree = tree_new();
    (*tree).length = 1 as u32;
    walk((*tree).root);
    tree_free(tree);
}
"#;

#[test]
fn w6a_r564_a_box_owner_field_crosses_at_the_c_arm_around_the_owner_edit() {
    let out = emitted(
        "r564-quadtree-walk",
        &with_prelude(QUADTREE_WALK_OF_BOX_FIELD),
    );
    let src = compact(&out.source);
    let receipts = format!(
        "{}\n{}",
        out.artifacts.box_param_receipts, out.artifacts.return_certificate_receipts
    );
    assert_eq!(out.reverted, 0, "{}\n{receipts}", out.source);
    assert!(
        src.contains("fnwalk(mutroot:&mutnode_t)"),
        "{}\n{receipts}\n{:#?}\n{}",
        out.source,
        out.degradations,
        out.artifacts.class_collisions
    );
    assert!(
        src.contains("letmuttree:Option<Box<crate::tree_t>>=tree_new();"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        src.contains("walk(&mut*(*tree.as_deref_mut().unwrap()).root);"),
        "{}\n{receipts}",
        out.source
    );
    for subject in ["test_tree::tree", "walk::root"] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}\n{:#?}\n{receipts}\n{}",
            out.degradations,
            out.source
        );
    }
}

/// R561-5 (report 094): brotli's `metablock` E0499. `&mut place` twice at a
/// callee whose formals are shared: wave-6p's weakening renders `&(place)`
/// when the caller is converted, and must do the same when the caller is
/// emitted in its INPUT form beside the converted callee.
const SAME_PLACE_TWICE: &str = r#"
#[repr(C)]
#[derive(Copy, Clone)]
pub struct DistParams { pub postfix: u32, pub ndirect: u32 }
#[repr(C)]
#[derive(Copy, Clone)]
pub struct Params { pub quality: i32, pub dist: DistParams }
pub unsafe extern "C" fn ComputeDistanceCost(mut orig_params: *const DistParams, mut new_params: *const DistParams, mut cost: *mut f64) -> i32 {
    if (*orig_params).postfix == (*new_params).postfix { *cost = 1.0f64; return 1 as i32; }
    *cost = ((*orig_params).ndirect + (*new_params).ndirect) as f64;
    return 0 as i32;
}
pub unsafe extern "C" fn BuildMetaBlock(mut params: *mut Params) {
    let mut orig_params = *params;
    let mut new_params = *params;
    let mut dist_cost: f64 = 0.;
    ComputeDistanceCost(&mut orig_params.dist, &mut new_params.dist, &mut dist_cost);
    let mut dist_cost_0: f64 = 0.;
    ComputeDistanceCost(&mut orig_params.dist, &mut orig_params.dist, &mut dist_cost_0);
    if dist_cost_0 < dist_cost { (*params).dist = orig_params.dist; }
}
"#;

#[test]
fn w6a_r561_5_input_form_caller_weakens_the_same_place_twice() {
    let src = with_prelude(SAME_PLACE_TWICE);
    let (source, callee_converted) = ::utils::compilation::run_compiler_on_str(&src, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("ast");
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("decide");
        let caller = table
            .entries
            .iter()
            .map(|(s, _)| s.fn_did)
            .find(|d| tcx.def_path_str(d.to_def_id()).ends_with("BuildMetaBlock"))
            .expect("caller");
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("emit");
        // The caller in its input form, the callee kept: brotli's tree.
        let mut reverted = emission.plan.held_classes();
        reverted.insert(super::bridge_receipt::SignatureClassId::of(caller));
        let (files, ..) = super::round_files(
            tcx,
            &capture,
            &emission.plan,
            &emission.texts,
            &reverted,
            &std::collections::BTreeSet::new(),
            emission.plan.root_file.as_ref(),
            &table,
        )
        .expect("round");
        let source = files.into_values().next().expect("file");
        let callee_converted = source.contains("orig_params: &DistParams");
        (source, callee_converted)
    })
    .expect("compiles");
    let flat: String = source.split_whitespace().collect();
    assert!(callee_converted, "the callee is kept converted:\n{source}");
    assert!(
        flat.contains("fnBuildMetaBlock(mutparams:*mutParams)"),
        "the caller is in its input form:\n{source}"
    );
    assert!(
        flat.contains(
            "ComputeDistanceCost(&(orig_params.dist),&(orig_params.dist),&mutdist_cost_0)"
        ),
        "the input-form call carries the shared weakening at both positions:\n{source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "no E0499 at the input-form call:\n{source}"
    );
}

/// A user allocator that forwards to `System` is still not `System` (R619-8):
/// the refusal's remaining case once (B′) declares the system's everywhere.
const CUSTOM_ALLOCATOR: &str = "\nstruct A;\nunsafe impl std::alloc::GlobalAlloc for A {\n    unsafe fn alloc(&self, l: std::alloc::Layout) -> *mut u8 { std::alloc::GlobalAlloc::alloc(&std::alloc::System, l) }\n    unsafe fn dealloc(&self, p: *mut u8, l: std::alloc::Layout) { std::alloc::GlobalAlloc::dealloc(&std::alloc::System, p, l) }\n}\n#[global_allocator]\nstatic GLOBAL: A = A;\n";

/// The emitted crate's allocator is the system's (R443-1), declared by the
/// input itself; (B′) declares the same one where the input declares none.
const SYSTEM_ALLOCATOR: &str =
    "\n#[global_allocator]\nstatic GLOBAL: std::alloc::System = std::alloc::System;\n";

/// **R620-3 (a) — a store into a field C frees lifts under R443.** The
/// refusal `w6a_c2_store_into_a_c_freed_field_is_refused` pins was written
/// before R443: a Rust-allocated block reaching libc's `free` is defined once
/// the emitted crate's global allocator IS the system's, because then the
/// block is a `malloc`/`calloc` block. So the lift reads that declaration,
/// and each member's block must be a real one: `vec![0; 0]` is a dangling
/// pointer that libc's `free` would be handed, so an ordinary allocation
/// lifts only on a positive literal count that every cast preserves.
/// Under R448-1 (B′) an input that declares no allocator is emitted with the
/// system's, so it lifts too. Controls, one violation each: a declared
/// allocator that is not `System`, that allocator beside an unrelated
/// `System` static, a literal a narrowing cast zeroes, a count the program
/// computes.
#[test]
fn w6a_r620_a_c_freed_store_lifts_under_the_declared_system_allocator() {
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
    let declared = format!("{FREED}{SYSTEM_ALLOCATOR}");
    let out = emitted("r620-store-cfree-system", &with_prelude(&declared));
    let src = compact(&out.source);
    let receipts = &out.artifacts.box_param_receipts;
    assert_eq!(out.reverted, 0, "{}\n{receipts}", out.source);
    assert!(
        src.contains("mutkey:Box<[i8]>)"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        src.contains("slots[index].key=Box::into_raw(key)as*muti8;"),
        "{}",
        out.source
    );
    assert!(
        receipts.contains("box-param-chain callee=slot_set index=2 sink=store"),
        "{receipts}"
    );
    assert!(
        receipts.contains(
            "box-param-store-c-free-lift callee=slot_set index=2 field=slot::key allocator=System"
        ),
        "{receipts}"
    );

    // R448-1 (B′): an input that declares no allocator is emitted with the
    // system's, so it lifts exactly as the declared one does.
    let out = emitted("r620-store-cfree-undeclared", &with_prelude(FREED));
    let receipts = &out.artifacts.box_param_receipts;
    assert_eq!(out.reverted, 0, "{}\n{receipts}", out.source);
    assert!(
        compact(&out.source).contains("mutkey:Box<[i8]>)"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        receipts.contains(
            "box-param-store-c-free-lift callee=slot_set index=2 field=slot::key allocator=System"
        ),
        "{receipts}"
    );

    let custom = format!("{FREED}{CUSTOM_ALLOCATOR}");
    // A custom allocator IS the global one; an unrelated `System` static
    // beside it does not make the crate's allocator the system's.
    let beside = custom.replace(
        "#[global_allocator]\nstatic GLOBAL: A = A;\n",
        "#[global_allocator]\nstatic GLOBAL: A = A;\nstatic UNRELATED: std::alloc::System = std::alloc::System;\n",
    );
    assert_ne!(beside, custom);
    // A literal that a narrowing cast turns into zero (`256 as u8`).
    let narrowed = declared.replace("calloc(8 as usize,", "calloc((256 as i32 as u8) as usize,");
    assert_ne!(narrowed, declared);
    let computed = declared.replace(
        "pub unsafe extern \"C\" fn table_put(mut slots: *mut slot, mut index: usize) {\n    let mut key = calloc(8 as usize,",
        "pub unsafe extern \"C\" fn table_put(mut slots: *mut slot, mut index: usize, mut n: usize) {\n    let mut key = calloc(n,",
    );
    assert_ne!(computed, declared);
    for (name, source, reason) in [
        (
            "r620-store-cfree-custom",
            custom,
            "slot_set::key\theld\tbox-param-store-c-free:slot_set:slot::key",
        ),
        (
            "r620-store-cfree-custom-beside-system",
            beside,
            "slot_set::key\theld\tbox-param-store-c-free:slot_set:slot::key",
        ),
        (
            "r620-store-cfree-narrowed",
            narrowed,
            "slot_set::key\theld\tbox-param-store-c-free:slot_set:slot::key:member-block:table_put::key",
        ),
        (
            "r620-store-cfree-computed",
            computed,
            "slot_set::key\theld\tbox-param-store-c-free:slot_set:slot::key:member-block:table_put::key",
        ),
    ] {
        let out = emitted(name, &with_prelude(&source));
        let receipts = &out.artifacts.box_param_receipts;
        assert!(
            !compact(&out.source).contains("Box<[i8]>"),
            "{name}: {}",
            out.source
        );
        assert!(receipts.contains(reason), "{name}\n{receipts}");
        assert!(
            !receipts.contains("box-param-store-c-free-lift"),
            "{name}\n{receipts}"
        );
    }
}

/// buffer's `buffer_new_with_string` reduced (batch 48,
/// `buffer_new_with_string::str` `thin-extent`): an exported entry nothing in
/// the program calls measures its C string and hands it on, in C2Rust's
/// hoisted-argument block, to an exported callee that stores it into
/// `(*self_0).alloc`, which `buffer_free` frees.
const EXPORTED_STORE: &str = r#"
extern "C" {
    fn strlen(s: *const i8) -> usize;
}
#[repr(C)]
pub struct buffer_t { pub len: usize, pub alloc: *mut i8, pub data: *mut i8 }
#[no_mangle]
pub unsafe extern "C" fn buffer_new_with_string(mut str: *mut i8) -> *mut buffer_t {
    return {
        let __arg_1 = strlen(str);
        buffer_new_with_string_length(str, __arg_1)
    };
}
#[no_mangle]
pub unsafe extern "C" fn buffer_new_with_string_length(mut str: *mut i8, mut len: usize) -> *mut buffer_t {
    let mut self_0 = malloc(::std::mem::size_of::<buffer_t>()) as *mut buffer_t;
    if self_0.is_null() {
        return 0 as *mut buffer_t;
    }
    (*self_0).len = len;
    (*self_0).alloc = str;
    (*self_0).data = (*self_0).alloc;
    return self_0;
}
#[no_mangle]
pub unsafe extern "C" fn buffer_free(mut self_0: *mut buffer_t) {
    free((*self_0).alloc as *mut core::ffi::c_void);
    free(self_0 as *mut core::ffi::c_void);
}
"#;

/// The same consumer storing its formal ITSELF into the field the program
/// frees (R620-3's other shape: C2's lifted store with no member).
const EXPORTED_DIRECT_STORE: &str = r#"
extern "C" {
    fn strlen(s: *const i8) -> usize;
}
#[repr(C)]
pub struct buffer_t { pub len: usize, pub alloc: *mut i8, pub data: *mut i8 }
#[no_mangle]
pub unsafe extern "C" fn buffer_adopt(mut holder: *mut buffer_t, mut str: *mut i8) {
    let mut len = strlen(str);
    (*holder).len = len;
    (*holder).alloc = str;
}
#[no_mangle]
pub unsafe extern "C" fn buffer_release(mut holder: *mut buffer_t) {
    free((*holder).alloc as *mut core::ffi::c_void);
}
"#;

/// **R620-3 (USER) — R534 extends to an exported consumer that STORES its
/// formal** into storage the program later frees. buffer's entry takes the
/// owning form at its surface: `Box<[i8]>`, because the body's first act is
/// `strlen(str)`, which makes the formal a C string (a block of
/// `strlen + 1` elements, `strdup`'s postcondition) and non-null (a null
/// argument is UB in the input, §28). It moves on into the storing callee,
/// whose store releases it (`Box::into_raw`) into the field `buffer_free`
/// frees: C2's store chain with the waived formal as its one member, lifted
/// under the declared system allocator. Receipted `exported-consumer-store`.
#[test]
fn w6a_r620_an_exported_store_consumer_takes_the_owning_form() {
    let declared = format!("{EXPORTED_STORE}{SYSTEM_ALLOCATOR}");
    let out = emitted("r620-exported-store", &with_prelude(&declared));
    if let Ok(path) = std::env::var("W6A_DUMP_EMITTED") {
        std::fs::write(path, &out.source).expect("dump");
    }
    let src = compact(&out.source);
    let receipts = &out.artifacts.box_param_receipts;
    assert_eq!(out.reverted, 0, "{}\n{receipts}", out.source);
    assert!(
        src.contains("fnbuffer_new_with_string(mutstr:Box<[i8]>)"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        src.contains("fnbuffer_new_with_string_length(mutstr:Box<[i8]>,"),
        "{}\n{receipts}",
        out.source
    );
    assert!(src.contains("strlen(str.as_"), "{}", out.source);
    assert!(
        src.contains("buffer_new_with_string_length(str,__arg_1)"),
        "{}",
        out.source
    );
    assert!(
        src.contains("(*self_0).alloc=Box::into_raw(str)as*muti8;"),
        "{}",
        out.source
    );
    assert!(
        receipts.contains(
            "exported-consumer-store callee=buffer_new_with_string index=0 extent=strlen+1"
        ),
        "{receipts}"
    );
    assert!(
        receipts.contains(
            "box-param-store-c-free-lift callee=buffer_new_with_string_length index=0 field=buffer_t::alloc allocator=System"
        ),
        "{receipts}"
    );
    assert!(
        !receipts.contains("exported-consumer-waiver callee=buffer_new_with_string"),
        "{receipts}"
    );

    // The same consumer storing the formal ITSELF, into the field the
    // program frees: C2's lifted store with no member at all.
    let out = emitted(
        "r620-exported-direct-store",
        &with_prelude(&format!("{EXPORTED_DIRECT_STORE}{SYSTEM_ALLOCATOR}")),
    );
    let src = compact(&out.source);
    let receipts = &out.artifacts.box_param_receipts;
    assert_eq!(out.reverted, 0, "{}\n{receipts}", out.source);
    assert!(
        src.contains("mutstr:Box<[i8]>)"),
        "{}\n{receipts}",
        out.source
    );
    assert!(
        src.contains(".alloc=Box::into_raw(str)as*muti8;"),
        "{}",
        out.source
    );
    assert!(
        receipts.contains("exported-consumer-store callee=buffer_adopt index=1 extent=strlen+1"),
        "{receipts}"
    );
    assert!(
        receipts.contains(
            "box-param-store-c-free-lift callee=buffer_adopt index=1 field=buffer_t::alloc allocator=System"
        ),
        "{receipts}"
    );
}

/// R620-3's controls, one violation each: under another allocator the store
/// stays refused; a field the program never frees is not the
/// ruled shape (R534's own store control, `ht_park`, is that one); a formal
/// tested for null before it is measured may be null, so it is not a
/// non-null C string. Outside the extension nothing supersedes the model,
/// so the formal keeps its own verdict (`Ref`). And a consumer that stores
/// its formal AND hands it to another consumer has two sinks: the owner walk
/// refuses it.
#[test]
fn w6a_r620_the_store_extension_holds_outside_its_shape() {
    let declared = format!("{EXPORTED_STORE}{SYSTEM_ALLOCATOR}");
    let never_freed =
        declared.replace("    free((*self_0).alloc as *mut core::ffi::c_void);\n", "");
    let tested = declared.replace(
        "    return {\n        let __arg_1 = strlen(str);",
        "    if str.is_null() {\n        return 0 as *mut buffer_t;\n    }\n    return {\n        let __arg_1 = strlen(str);",
    );
    let two_sinks = format!("{EXPORTED_DIRECT_STORE}{SYSTEM_ALLOCATOR}")
        .replace(
            "    let mut len = strlen(str);\n",
            "    let mut len = strlen(str);\n    keep(str);\n",
        )
        .replace(
            "#[no_mangle]\npub unsafe extern \"C\" fn buffer_adopt",
            "static mut KEPT: *mut i8 = 0 as *mut i8;\nunsafe extern \"C\" fn keep(mut s: *mut i8) {\n    KEPT = s;\n}\n#[no_mangle]\npub unsafe extern \"C\" fn buffer_adopt",
        );
    assert_ne!(never_freed, declared);
    assert_ne!(tested, declared);
    assert!(two_sinks.contains("keep(str);") && two_sinks.contains("KEPT = s;"));
    for (name, source, reason) in [
        (
            "r620-exported-store-custom-allocator",
            format!("{EXPORTED_STORE}{CUSTOM_ALLOCATOR}"),
            "box-param-store-c-free:buffer_new_with_string_length:buffer_t::alloc",
        ),
        (
            "r620-exported-store-never-freed",
            never_freed,
            "buffer_new_with_string::str\theld\tbox-param-model:buffer_new_with_string::str:Some(Ref)",
        ),
        (
            "r620-exported-store-tested",
            tested,
            "buffer_new_with_string::str\theld\tbox-param-model:buffer_new_with_string::str:Some(Ref)",
        ),
        (
            "r620-exported-store-two-sinks",
            two_sinks,
            "buffer_adopt::str\theld\tbox-param-callee-use:buffer_adopt:store-consumer-escapes",
        ),
    ] {
        let out = emitted(name, &with_prelude(&source));
        let src = compact(&out.source);
        let receipts = &out.artifacts.box_param_receipts;
        assert!(
            !src.contains("mutstr:Box<[i8]>") && !src.contains("mutstr:Option<Box<"),
            "{name}: {}\n{receipts}",
            out.source
        );
        assert!(receipts.contains(reason), "{name}\n{receipts}");
        assert!(
            !receipts.contains("exported-consumer-store"),
            "{name}\n{receipts}"
        );
    }
}

/// The census model of analysis-fanout 020's linked list (`r029_B0_main/
/// model-slots.tsv`, R697-3): `next`, `push` at both ends, `drop_0`'s formal
/// and `main_0`'s `l` Owning, `last` Ref; `extra` adds or overrides.
fn linked_list_with(
    name: &str,
    source: &str,
    extra: &[(&str, crate::analyses::borrow_ownership::SlotKind)],
) -> super::wave6a_allocation_tests::Emitted {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = super::test_model_override::frame_lock();
    let mut locals = vec![
        ("push::head".to_owned(), SlotKind::Owning),
        ("push::n".to_owned(), SlotKind::Owning),
        ("last::head".to_owned(), SlotKind::Ref),
        ("drop_0::head".to_owned(), SlotKind::Owning),
        ("main_0::l".to_owned(), SlotKind::Owning),
    ];
    locals.extend(
        extra
            .iter()
            .map(|(label, kind)| ((*label).to_owned(), *kind)),
    );
    super::test_model_override::set(
        "w6a-r697-linked-list-frame",
        vec![("Node".to_owned(), 1, SlotKind::Owning)],
        locals,
    );
    let out = emitted(name, &with_prelude(source));
    super::test_model_override::clear();
    out
}

/// analysis-fanout 020's linked list, variant C (`0` for `NULL`) with `main`,
/// as C2Rust gives it (`r029_B0_main/substrate-lib.rs`).
const LINKED_LIST_MAIN: &str = r#"
// w6a-r697-linked-list-frame
#[repr(C)]
pub struct Node {
    pub val: ::core::ffi::c_int,
    pub next: *mut Node,
}
#[no_mangle]
pub unsafe extern "C" fn push(mut head: *mut Node, mut val: ::core::ffi::c_int) -> *mut Node {
    let mut n = malloc(::core::mem::size_of::<Node>() as usize) as *mut Node;
    (*n).val = val;
    (*n).next = head;
    return n;
}
#[no_mangle]
pub unsafe extern "C" fn last(mut head: *mut Node) -> *mut Node {
    while !(*head).next.is_null() {
        head = (*head).next;
    }
    return head;
}
#[export_name = "drop"]
pub unsafe extern "C" fn drop_0(mut head: *mut Node) {
    if head.is_null() {
        return;
    }
    drop_0((*head).next);
    free(head as *mut ::core::ffi::c_void);
}
unsafe fn main_0() -> ::core::ffi::c_int {
    let mut l = push(
        push(::core::ptr::null_mut::<Node>(), 1 as ::core::ffi::c_int),
        2 as ::core::ffi::c_int,
    );
    (*last(l)).val = 3 as ::core::ffi::c_int;
    drop_0(l);
    return 0 as ::core::ffi::c_int;
}
"#;

/// **R697-3 (1)** — 020's `push` with its null literal alone: `a` is built on
/// `push(null_mut(), 1)` and handed into `push(a, 2)`; `main_0` frees the
/// list's head. The null actual retains nothing, it is `None`: the formal is
/// `Option<Box<Node>>`, the literal `None`, the certified receiver `Some(a)`.
const NULL_ACTUAL: &str = r#"
// w6a-r697-linked-list-frame
#[repr(C)]
pub struct Node {
    pub val: ::core::ffi::c_int,
    pub next: *mut Node,
}
#[no_mangle]
pub unsafe extern "C" fn push(mut head: *mut Node, mut val: ::core::ffi::c_int) -> *mut Node {
    let mut n = malloc(::core::mem::size_of::<Node>() as usize) as *mut Node;
    (*n).val = val;
    (*n).next = head;
    return n;
}
unsafe fn main_0() -> ::core::ffi::c_int {
    let mut a = push(::core::ptr::null_mut::<Node>(), 1 as ::core::ffi::c_int);
    let mut l = push(a, 2 as ::core::ffi::c_int);
    let mut v = (*l).val;
    free(l as *mut ::core::ffi::c_void);
    return v;
}
"#;

#[test]
fn w6a_r697_a_null_literal_actual_is_none() {
    let out = linked_list_with(
        "r697-null-actual",
        NULL_ACTUAL,
        &[(
            "main_0::a",
            crate::analyses::borrow_ownership::SlotKind::Owning,
        )],
    );
    let src = compact(&out.source);
    let context = format!(
        "{}\n{}\n{}\n{:#?}",
        out.artifacts.box_param_receipts,
        out.artifacts.return_certificate_receipts,
        out.source,
        out.degradations
    );
    assert!(
        src.contains("fnpush(muthead:Option<Box<Node>>,"),
        "{context}"
    );
    assert!(
        src.contains("push(None,1asi32)") || src.contains("push(None,1as::core::ffi::c_int)"),
        "{context}"
    );
    assert!(src.contains("push(Some(a),"), "{context}");
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("box-param-chain callee=push index=0 sink=store"),
        "{context}"
    );
    for subject in ["push::head", "main_0::a", "main_0::l"] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}\n{context}"
        );
    }
    assert_eq!(out.reverted, 0, "{context}");

    // C2Rust's other spelling of C's `0`: the literal under its cast.
    let literal = NULL_ACTUAL.replace("::core::ptr::null_mut::<Node>()", "0 as *mut Node");
    assert_ne!(literal, NULL_ACTUAL);
    let out = linked_list_with(
        "r697-null-actual-literal",
        &literal,
        &[(
            "main_0::a",
            crate::analyses::borrow_ownership::SlotKind::Owning,
        )],
    );
    assert!(
        compact(&out.source).contains("push(None,1as::core::ffi::c_int)") && out.reverted == 0,
        "{}\n{}",
        out.artifacts.box_param_receipts,
        out.source
    );

    // Control: a non-zero literal is an address, not `None`.
    let address = NULL_ACTUAL.replace("::core::ptr::null_mut::<Node>()", "8 as *mut Node");
    assert_ne!(address, NULL_ACTUAL);
    let out = linked_list_with(
        "r697-null-actual-control",
        &address,
        &[(
            "main_0::a",
            crate::analyses::borrow_ownership::SlotKind::Owning,
        )],
    );
    assert!(
        out.artifacts
            .box_param_receipts
            .contains("push::head\theld\tbox-param-caller-retains:main_0:not-a-local"),
        "{}",
        out.artifacts.box_param_receipts
    );
}

/// **R697-3 (2)** — 020's `last(l)`, with the input's two other walls
/// factored out (the nested `push(push(..), 2)` is a local `a`, and the
/// recursive `drop` is a `free` of the head, whose tail C leaks). `l` is a
/// certified receiver of `push`, lent to `last`, whose formal the model calls
/// Ref and whose result it calls Ref too. `last` walks its formal down the
/// list and returns it: the model's Ref at both ends is its borrow verdict on
/// that returned pointer, so the call is a lend: `l` stays a `Box`, and
/// `last(&mut *l)`.
const RETURNED_LEND: &str = r#"
// w6a-r697-linked-list-frame
#[repr(C)]
pub struct Node {
    pub val: ::core::ffi::c_int,
    pub next: *mut Node,
}
#[no_mangle]
pub unsafe extern "C" fn push(mut head: *mut Node, mut val: ::core::ffi::c_int) -> *mut Node {
    let mut n = malloc(::core::mem::size_of::<Node>() as usize) as *mut Node;
    (*n).val = val;
    (*n).next = head;
    return n;
}
#[no_mangle]
pub unsafe extern "C" fn last(mut head: *mut Node) -> *mut Node {
    while !(*head).next.is_null() {
        head = (*head).next;
    }
    return head;
}
unsafe fn main_0() -> ::core::ffi::c_int {
    let mut a = push(::core::ptr::null_mut::<Node>(), 1 as ::core::ffi::c_int);
    let mut l = push(a, 2 as ::core::ffi::c_int);
    (*last(l)).val = 3 as ::core::ffi::c_int;
    let mut v = (*l).val;
    free(l as *mut ::core::ffi::c_void);
    return v;
}
"#;

#[test]
fn w6a_r697_a_box_lent_to_a_ref_formal_it_returns_is_a_lend() {
    let out = linked_list_with(
        "r697-returned-lend",
        RETURNED_LEND,
        &[(
            "node::n",
            crate::analyses::borrow_ownership::SlotKind::Owning,
        )],
    );
    let src = compact(&out.source);
    let context = format!(
        "{}\n{}\n{}\n{:#?}\nFIRST-FAILING-VERIFY\n{}",
        out.artifacts.box_param_receipts,
        out.artifacts.return_certificate_receipts,
        out.source,
        out.degradations,
        out.artifacts.first_failing_verify_tree
    );
    assert!(
        out.artifacts
            .return_certificate_receipts
            .contains("return-certificate callee=push ")
            && out
                .artifacts
                .return_certificate_receipts
                .contains("[main_0::a,main_0::l]"),
        "{context}"
    );
    assert!(
        src.contains("letmutl:Box<crate::Node>=push(Some(a),"),
        "{context}"
    );
    assert!(
        src.contains("fnlast<'a>(muthead:&'amutNode)->&'amutNode"),
        "{context}"
    );
    assert!(src.contains("last(&mut*l)"), "{context}");
    assert!(src.contains("drop(l);"), "{context}");
    assert!(!src.contains("as_mut())"), "{context}");
    assert_eq!(reason_of(&out.degradations, "main_0::l"), None, "{context}");
    assert_eq!(out.reverted, 0, "{context}");

    // Controls, one conjunct each. (a) The model does not call the formal
    // Ref, so the pointer `last` hands back is no borrow it verified. (b) The
    // formal is re-seated to ANOTHER pointer, not walked through itself.
    let out = linked_list_with(
        "r697-returned-lend-raw-formal",
        RETURNED_LEND,
        &[
            (
                "main_0::a",
                crate::analyses::borrow_ownership::SlotKind::Owning,
            ),
            (
                "last::head",
                crate::analyses::borrow_ownership::SlotKind::Raw,
            ),
        ],
    );
    assert!(
        out.artifacts.return_certificate_receipts.contains(
            "main_0::l\theld\treturn-certificate-receiver-use:call-argument-not-a-lend:last(l)"
        ),
        "{}\n{}",
        out.artifacts.return_certificate_receipts,
        out.source
    );
    // (b)
    let source = RETURNED_LEND
        .replace(
            "    (*last(l)).val = 3 as ::core::ffi::c_int;\n",
            "    (*pick(l, ::core::ptr::null_mut::<Node>())).val = 3 as ::core::ffi::c_int;\n",
        )
        .replace(
            "unsafe fn main_0()",
            "#[no_mangle]\npub unsafe extern \"C\" fn pick(mut head: *mut Node, mut other: *mut Node) -> *mut Node {\n    if (*head).val == 0 as ::core::ffi::c_int {\n        head = other;\n    }\n    return head;\n}\nunsafe fn main_0()",
        );
    assert!(source.contains("fn pick(") && source.contains("(*pick(l,"));
    let out = linked_list_with(
        "r697-returned-lend-other-reseat",
        &source,
        &[
            (
                "main_0::a",
                crate::analyses::borrow_ownership::SlotKind::Owning,
            ),
            (
                "pick::head",
                crate::analyses::borrow_ownership::SlotKind::Ref,
            ),
            (
                "pick::other",
                crate::analyses::borrow_ownership::SlotKind::Ref,
            ),
        ],
    );
    assert!(
        out.artifacts.return_certificate_receipts.contains(
            "main_0::l\theld\treturn-certificate-receiver-use:call-argument-not-a-lend:pick(l,"
        ),
        "{}\n{}",
        out.artifacts.return_certificate_receipts,
        out.source
    );
    // (c) 020's own input with `main`: in this harness the model calls
    // `last`'s formal Ref but its return Raw (the census model calls both
    // Ref), so the pointer `last` hands back is no borrow the model verified,
    // and the call is not a lend.
    let out = linked_list_with("r697-returned-lend-raw-return", LINKED_LIST_MAIN, &[]);
    assert!(
        out.artifacts.return_certificate_receipts.contains(
            "main_0::l\theld\treturn-certificate-receiver-use:call-argument-not-a-lend:last(l)"
        ),
        "{}\n{}",
        out.artifacts.return_certificate_receipts,
        out.source
    );
}
