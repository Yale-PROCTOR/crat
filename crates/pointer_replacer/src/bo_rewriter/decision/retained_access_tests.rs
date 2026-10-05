//! The retained-access check's witnesses (R812-1, era-5c 139): the eight's shapes stay
//! held, the clear shapes stay clear, and one fault per rule turns its witness RED.

use rustc_hash::FxHashMap;
use rustc_hir::{ItemKind, OwnerNode};
use rustc_span::def_id::DefId;

use super::retained_access::{
    AccessKind, HoldKind, Options, RetainedAccessCheck, Rule, Shape, Verdict, body_identity,
};
use crate::utils::rustc::RustProgram;

fn program_of<'tcx>(tcx: rustc_middle::ty::TyCtxt<'tcx>) -> RustProgram<'tcx> {
    let mut functions = Vec::new();
    let mut structs = Vec::new();
    for owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = owner.as_owner() else { continue };
        let OwnerNode::Item(item) = owner.node() else { continue };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        }
    }
    RustProgram {
        tcx,
        functions,
        structs,
    }
}

/// The verdicts by `fn::name` (the function's last path segment and the local's name),
/// with every retaining field raw unless `ref_fields` names it (`Struct.field`).
fn verdicts_with(code: &str, ref_fields: &[&str]) -> FxHashMap<String, Verdict> {
    verdicts_of(code, ref_fields, None)
}

/// The verdicts with `fault` removed from the check.
fn verdicts_faulted(code: &str, ref_fields: &[&str], fault: Rule) -> FxHashMap<String, Verdict> {
    verdicts_of(code, ref_fields, Some(fault))
}

fn verdicts_of(code: &str, ref_fields: &[&str], fault: Option<Rule>) -> FxHashMap<String, Verdict> {
    verdicts_opts(
        code,
        ref_fields,
        Options {
            fault,
            ..Options::default()
        },
    )
}

fn verdicts_opts(code: &str, ref_fields: &[&str], options: Options) -> FxHashMap<String, Verdict> {
    let mut out = FxHashMap::default();
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = program_of(tcx);
        let raw = |did: DefId, index: usize| {
            let adt = tcx.adt_def(did);
            let name = format!(
                "{}.{}",
                tcx.item_name(did),
                adt.all_fields().nth(index).expect("a field").name
            );
            !ref_fields.contains(&name.as_str())
        };
        let check = RetainedAccessCheck::compute_options(&program, &raw, options);
        for &f in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            check.assert_body(f, &body);
            assert_eq!(body_identity(&body), body_identity(&body));
            let fn_name = tcx.item_name(f.to_def_id());
            for info in &body.var_debug_info {
                let rustc_middle::mir::VarDebugInfoContents::Place(place) = info.value else {
                    continue;
                };
                if !place.projection.is_empty() {
                    continue;
                }
                let verdict = if place.local.as_usize() <= body.arg_count {
                    check.formal(f, place.local.as_usize())
                } else {
                    check.local(f, place.local)
                };
                if let Some(verdict) = verdict {
                    out.insert(format!("{fn_name}::{}", info.name), verdict.clone());
                }
            }
        }
    })
    .expect("compiles");
    out
}

fn verdicts(code: &str) -> FxHashMap<String, Verdict> {
    verdicts_with(code, &[])
}

fn of<'a>(verdicts: &'a FxHashMap<String, Verdict>, subject: &str) -> &'a Verdict {
    verdicts
        .get(subject)
        .unwrap_or_else(|| panic!("no subject {subject}: {verdicts:#?}"))
}

fn held_by(verdict: &Verdict, kind: HoldKind, access: AccessKind) -> bool {
    matches!(verdict, Verdict::Held(holds)
        if holds.iter().any(|hold| hold.kind == kind && hold.access == access))
}

fn writes(verdict: &Verdict) -> bool {
    held_by(verdict, HoldKind::Access, AccessKind::Write)
}

/// W1 (bzip2's shape): the init stores the stream into its state; a later entry
/// reaches the stream through the state while its own formal borrows it.
const W1_STREAM: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct bz_stream { pub avail_in: u32, pub state: *mut EState }
#[repr(C)] pub struct EState { pub strm: *mut bz_stream, pub mode: i32 }
pub unsafe fn init(strm: *mut bz_stream) -> i32 {
    let s = malloc(16) as *mut EState;
    (*s).strm = strm;
    (*strm).state = s;
    0
}
unsafe fn copy_input(s: *mut EState) { (*(*s).strm).avail_in -= 1; }
pub unsafe fn handle_compress(strm: *mut bz_stream) -> i32 {
    let s = (*strm).state;
    copy_input(s);
    (*strm).avail_in as i32
}
"#;

#[test]
fn e5c_hold_w1_the_stream_reached_through_its_state() {
    let v = verdicts(W1_STREAM);
    let strm = of(&v, "handle_compress::strm");
    assert!(writes(strm), "{strm:#?}");
    let Verdict::Held(holds) = strm else { unreachable!() };
    assert!(holds.iter().any(|h| h.shape == Shape::Cycle), "{holds:#?}");
}

/// W1b: the back-pointer reaches the state through a struct copied by value.
const W1B_COPY: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct bz_stream { pub avail_in: u32, pub state: *mut EState }
#[repr(C)] #[derive(Clone, Copy)] pub struct EState { pub strm: *mut bz_stream, pub mode: i32 }
pub unsafe fn init(strm: *mut bz_stream) -> i32 {
    let s = malloc(16) as *mut EState;
    let tmp = EState { strm, mode: 0 };
    *s = tmp;
    (*strm).state = s;
    0
}
unsafe fn copy_input(s: *mut EState) { let t = *s; (*t.strm).avail_in -= 1; }
pub unsafe fn handle_compress(strm: *mut bz_stream) -> i32 {
    let s = (*strm).state;
    copy_input(s);
    (*strm).avail_in as i32
}
"#;

#[test]
fn e5c_hold_w1b_a_struct_copy_carries_the_pointer() {
    assert!(writes(of(&verdicts(W1B_COPY), "handle_compress::strm")));
}

#[test]
fn e5c_hold_fault_copy_carry() {
    let v = verdicts_faulted(W1B_COPY, &[], Rule::CopyCarry);
    assert!(
        !writes(of(&v, "handle_compress::strm")),
        "the fault is caught"
    );
}

/// W2 (libtree's shape): the struct's own pointer into its buffer.
const W2_SELF: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct small_vec { pub p: *mut u64, pub n: usize, pub buf: [u64; 16] }
pub unsafe fn init(v: *mut small_vec) { (*v).p = (*v).buf.as_mut_ptr(); (*v).n = 0; }
pub unsafe fn append(v: *mut small_vec, x: u64) { *(*v).p.offset((*v).n as isize) = x; (*v).n += 1; }
"#;

#[test]
fn e5c_hold_w2_a_pointer_into_the_struct_itself() {
    let v = verdicts(W2_SELF);
    let append = of(&v, "append::v");
    let Verdict::Held(holds) = append else { panic!("{append:#?}") };
    let hold = holds
        .iter()
        .find(|h| h.access == AccessKind::Write && h.shape == Shape::SelfRef)
        .unwrap_or_else(|| panic!("{holds:#?}"));
    // The witness: `fn | Struct.field | file:line`.
    let parts: Vec<&str> = hold.witness.split(" | ").collect();
    assert_eq!(parts.len(), 3, "{}", hold.witness);
    assert!(parts[0].ends_with("append"), "{}", hold.witness);
    assert_eq!(parts[1], "small_vec.p");
    assert!(
        parts[2]
            .rsplit(':')
            .next()
            .unwrap()
            .parse::<usize>()
            .is_ok(),
        "{}",
        hold.witness
    );
    assert_eq!(hold.retaining_place, "small_vec.p");
    assert!(append.receipt().unwrap().starts_with("write:"));
}

/// The guard (132 §2): a write counts only through a raw retaining place. With the
/// model deciding `small_vec.p` a reference, W2's write is not a retained access.
#[test]
fn e5c_hold_the_guard_reads_the_model() {
    let v = verdicts_with(W2_SELF, &["small_vec.p"]);
    assert_eq!(of(&v, "append::v"), &Verdict::Clear);
}

#[test]
fn e5c_hold_fault_raw_guard() {
    let v = verdicts_faulted(W2_SELF, &["small_vec.p"], Rule::RawGuard);
    assert!(writes(of(&v, "append::v")), "the fault is caught");
}

/// C1 (libzahl's shape): the limbs are a separate allocation, never the struct. (With
/// libzahl's own `sign: i32`, an outside `u32` limb may be the sign: C11 §6.5p7's
/// signed/unsigned alias, era-5c 141; the fixture keeps the types apart.)
const C1_LIMBS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn realloc(_: *mut core::ffi::c_void, _: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct zahl { pub sign: i64, pub used: usize, pub alloced: usize, pub chars: *mut u32 }
pub unsafe fn zgrow(a: *mut zahl, n: usize) {
    (*a).chars = realloc((*a).chars as *mut core::ffi::c_void, (n * 4) as u64) as *mut u32;
    *(*a).chars.offset(0) = 0;
    (*a).alloced = n;
}
"#;

#[test]
fn e5c_hold_c1_the_limbs_are_not_the_struct() {
    assert!(!writes(of(&verdicts(C1_LIMBS), "zgrow::a")));
}

/// C2 (binn's shape): a header written as bytes through the item's buffer.
const C2_HEADER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct binn { pub header: i32, pub pbuf: *mut core::ffi::c_void, pub size: i32 }
pub unsafe fn binn_new(item: *mut binn) { (*item).pbuf = malloc(64); (*item).size = 0; }
pub unsafe fn binn_load(data: *mut core::ffi::c_void, item: *mut binn) { (*item).pbuf = data; }
pub unsafe fn binn_save_header(item: *mut binn) -> i32 {
    let p = (*item).pbuf as *mut u8;
    *p = 0xe0;
    (*item).size
}
"#;

#[test]
fn e5c_hold_c2_a_byte_buffer_is_not_the_item() {
    assert!(!writes(of(&verdicts(C2_HEADER), "binn_save_header::item")));
}

/// C2b (binn's allocator hook): every call through `malloc_fn` is a fresh allocation (P5).
const C2B_HOOK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; }
pub static mut malloc_fn: Option<unsafe extern "C" fn(u64) -> *mut core::ffi::c_void> = None;
unsafe fn check_alloc_functions() { if malloc_fn.is_none() { malloc_fn = Some(malloc); } }
unsafe fn binn_malloc(size: i32) -> *mut core::ffi::c_void {
    check_alloc_functions();
    malloc_fn.expect("non-null function pointer")(size as u64)
}
#[repr(C)] pub struct binn { pub header: i32, pub pbuf: *mut core::ffi::c_void, pub size: i32 }
unsafe fn binn_new() -> *mut binn {
    let item = binn_malloc(24) as *mut binn;
    (*item).pbuf = binn_malloc(64);
    binn_save_header(item);
    item
}
// The item stays inside the program (returned to an outside caller it would take the
// outside's stores, 3.4).
pub unsafe fn entry() -> i32 { (*binn_new()).size }
unsafe fn binn_save_header(item: *mut binn) -> i32 {
    let p = (*item).pbuf as *mut u8;
    *p = 0xe0;
    (*item).size
}
"#;

#[test]
fn e5c_hold_c2b_an_allocator_hook_allocates() {
    let v = verdicts(C2B_HOOK);
    let item = of(&v, "binn_save_header::item");
    assert!(!writes(item), "{item:#?}");
}

#[test]
fn e5c_hold_fault_allocator_hook() {
    let v = verdicts_faulted(C2B_HOOK, &[], Rule::AllocatorHook);
    assert!(
        writes(of(&v, "binn_save_header::item")),
        "the fault is caught"
    );
}

/// Brotli's decoder (the eight's two decoder rows; wave-6o 110a): the state's own
/// `symbol_lists` points into its array, and the bit reader's `next_in` into its buffer.
const BROTLI_STATE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct BitReader { pub next_in: *const u8, pub avail_in: usize }
#[repr(C)] pub struct State {
    pub br: BitReader,
    pub buffer: [u8; 8],
    pub symbol_lists: *mut u16,
    pub symbols_lists_array: [u16; 32],
    pub avail: u32,
}
unsafe fn init(s: *mut State) {
    (*s).symbol_lists = (*s).symbols_lists_array.as_mut_ptr().offset(16);
    (*s).br.next_in = (*s).buffer.as_mut_ptr();
}
unsafe fn read_symbol_code_lengths(s: *mut State, i: isize) { *(*s).symbol_lists.offset(i) = 0; }
unsafe fn pull_byte(s: *mut State) -> u8 {
    (*s).avail = 0;
    *(*s).br.next_in
}
pub unsafe fn decode(s: *mut State) -> u8 {
    init(s);
    read_symbol_code_lengths(s, 1);
    pull_byte(s)
}
"#;

#[test]
fn e5c_hold_brotli_the_decoder_state() {
    let v = verdicts(BROTLI_STATE);
    assert!(writes(of(&v, "read_symbol_code_lengths::s")), "{v:#?}");
    let pull = of(&v, "pull_byte::s");
    assert!(
        held_by(pull, HoldKind::Access, AccessKind::Read),
        "{pull:#?}"
    );
}

#[test]
fn e5c_hold_fault_mut_read() {
    let v = verdicts_faulted(BROTLI_STATE, &[], Rule::MutRead);
    assert_eq!(
        of(&v, "pull_byte::s"),
        &Verdict::Clear,
        "the fault is caught"
    );
}

/// A pointer loaded from memory an outside caller provides reaches the outside object
/// of its pointee type, even when the program never stores there.
const OUTSIDE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct A { pub px: *mut i32 }
pub unsafe fn g(a: *mut A, x: *mut i32) { let p = (*a).px; *p = 1; }
"#;

#[test]
fn e5c_hold_outside_memory_holds_the_outside_object() {
    assert!(writes(of(&verdicts(OUTSIDE), "g::x")));
}

#[test]
fn e5c_hold_fault_outside_load() {
    let v = verdicts_faulted(OUTSIDE, &[], Rule::OutsideLoad);
    assert!(!writes(of(&v, "g::x")), "the fault is caught");
}

/// The derived-store: a formal's value stored into memory, kept apart with its store.
const DERIVED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct G { pub px: *mut i32 }
pub unsafe fn keep(g: *mut G, x: *mut i32) { (*g).px = x; }
"#;

#[test]
fn e5c_hold_the_derived_store() {
    let v = verdicts(DERIVED);
    let x = of(&v, "keep::x");
    assert!(
        held_by(x, HoldKind::DerivedStore, AccessKind::Write),
        "{x:#?}"
    );
    let Verdict::Held(holds) = x else { unreachable!() };
    assert!(holds[0].witness.contains("| G.px |"), "{holds:#?}");
}

#[test]
fn e5c_hold_fault_derived_store() {
    let v = verdicts_faulted(DERIVED, &[], Rule::DerivedStore);
    assert_eq!(of(&v, "keep::x"), &Verdict::Clear, "the fault is caught");
}

/// A byte copy (a loop of `*d = *s` through byte pointers) carries the pointers the
/// source struct holds.
const BYTE_COPY: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct S { pub p: *mut i32 }
unsafe fn copy_bytes(d: *mut S, s: *mut S) {
    let dp = d as *mut u8;
    let sp = s as *const u8;
    let mut i = 0;
    while i < 8 { *dp.offset(i) = *sp.offset(i); i += 1; }
}
unsafe fn write_through(t: *mut S) { *(*t).p = 1; }
unsafe fn f(x: *mut i32, a: *mut S, b: *mut S) { copy_bytes(b, a); write_through(b); }
pub unsafe fn entry() {
    let mut v = 0i32;
    let mut a = S { p: &mut v };
    let mut b = S { p: core::ptr::null_mut() };
    f(&mut v, &mut a, &mut b);
}
"#;

#[test]
fn e5c_hold_a_byte_copy_carries_the_pointer() {
    assert!(writes(of(&verdicts(BYTE_COPY), "f::x")));
}

#[test]
fn e5c_hold_fault_byte_copy() {
    let v = verdicts_faulted(BYTE_COPY, &[], Rule::ByteCopy);
    assert!(!writes(of(&v, "f::x")), "the fault is caught");
}

/// lodepng's `info` (era-5c 138 §1): a pointer stored through `&mut h.f` (a cell) and
/// read as `h.f` (a field) is the same memory.
const CELL_FIELD: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct H { pub f: *mut i32 }
unsafe fn set(slot: *mut *mut i32, v: *mut i32) { *slot = v; }
unsafe fn poke(h: *mut H) { *(*h).f = 1; }
unsafe fn f(x: *mut i32, h: *mut H) { poke(h); }
pub unsafe fn entry() {
    let mut v = 0i32;
    let mut h = H { f: core::ptr::null_mut() };
    set(&mut h.f, &mut v);
    f(&mut v, &mut h);
}
"#;

#[test]
fn e5c_hold_a_cell_is_its_field() {
    assert!(writes(of(&verdicts(CELL_FIELD), "f::x")));
}

/// The cell is the struct's own address (its first member, cast): with members (item 4)
/// `&mut h.f` names the field itself, so the cell rule's witness is this one.
const CELL_FIELD_CAST: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct H { pub f: *mut i32 }
unsafe fn set(slot: *mut *mut i32, v: *mut i32) { *slot = v; }
unsafe fn poke(h: *mut H) { *(*h).f = 1; }
unsafe fn f(x: *mut i32, h: *mut H) { poke(h); }
pub unsafe fn entry() {
    let mut v = 0i32;
    let mut h = H { f: core::ptr::null_mut() };
    set(&raw mut h as *mut *mut i32, &mut v);
    f(&mut v, &mut h);
}
"#;

#[test]
fn e5c_hold_a_cell_is_its_field_through_the_struct_address() {
    assert!(writes(of(&verdicts(CELL_FIELD_CAST), "f::x")));
}

#[test]
fn e5c_hold_fault_cell_field() {
    let v = verdicts_faulted(CELL_FIELD_CAST, &[], Rule::CellField);
    assert!(!writes(of(&v, "f::x")), "the fault is caught");
}

/// A mixed object (cells of two pointer types): a cell read as a third type reads
/// everything it holds, and the value leaves the loading extent through a static.
const MIXED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
static mut G: *mut u32 = core::ptr::null_mut();
unsafe fn store_a(slot: *mut *mut i32, v: *mut i32) { *slot = v; }
unsafe fn store_b(slot: *mut *mut u8, w: *mut u8) { *slot = w; }
unsafe fn load(slot: *mut *mut u32) { G = *slot; }
unsafe fn peek(y: *mut i64, slot: *mut *mut u32) -> u32 { **slot }
unsafe fn poke() { *G = 1; }
unsafe fn f(x: *mut u32) { poke(); }
pub unsafe fn entry() {
    let mut v = 0i32;
    let mut w = 0u8;
    let mut z = 0i64;
    let mut cell: *mut i32 = core::ptr::null_mut();
    let slot = &mut cell as *mut *mut i32;
    store_a(slot, &mut v);
    store_b(slot as *mut *mut u8, &mut w);
    load(slot as *mut *mut u32);
    peek(&mut z, slot as *mut *mut u32);
    f(&mut v as *mut i32 as *mut u32);
}
"#;

#[test]
fn e5c_hold_a_mixed_cell_reads_everything() {
    assert!(writes(of(&verdicts(MIXED), "f::x")));
}

#[test]
fn e5c_hold_fault_mixed_union() {
    let v = verdicts_faulted(MIXED, &[], Rule::MixedUnion);
    assert!(!writes(of(&v, "f::x")), "the fault is caught");
}

#[test]
fn e5c_hold_unknown_is_held() {
    let v = verdicts(MIXED);
    let y = of(&v, "peek::y");
    assert_eq!(y, &Verdict::Unknown);
    assert!(y.withdraws());
}

#[test]
fn e5c_hold_fault_unknown() {
    let v = verdicts_faulted(MIXED, &[], Rule::Unknown);
    assert_eq!(of(&v, "peek::y"), &Verdict::Clear, "the fault is caught");
}

/// An integer made a pointer may be anything of its type.
const INT_PTR: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
unsafe fn f(x: *mut i32, a: usize) { let p = a as *mut i32; *p = 1; }
pub unsafe fn entry() { let mut v = 0i32; let a = &mut v as *mut i32 as usize; f(&mut v, a); }
"#;

#[test]
fn e5c_hold_an_integer_made_a_pointer() {
    // Anything exposed: `Top`, so `Unknown`.
    assert_eq!(of(&verdicts(INT_PTR), "f::x"), &Verdict::Unknown);
}

#[test]
fn e5c_hold_fault_integer_pointer() {
    let v = verdicts_faulted(INT_PTR, &[], Rule::TopFlows);
    assert!(!of(&v, "f::x").withdraws(), "the fault is caught");
}

/// The corpus driver (era-5c 139): `CRAT_E5C_SIDE_SOURCE` names a program's `lib.rs`,
/// `CRAT_E5C_FIELDS` the frame's field kinds (`path::fieldN<TAB>kind`), and the rows go
/// to `CRAT_E5C_SIDE_ROWS`: `fn  local  name  f|l  verdict  receipt`.
#[test]
#[ignore = "the retained-access check over one corpus program (era-5c 139)"]
fn e5c_hold_corpus_rows() {
    let path = std::env::var("CRAT_E5C_SIDE_SOURCE").expect("CRAT_E5C_SIDE_SOURCE");
    let out = std::env::var("CRAT_E5C_SIDE_ROWS").expect("CRAT_E5C_SIDE_ROWS");
    let kinds: FxHashMap<String, String> = std::env::var("CRAT_E5C_FIELDS")
        .ok()
        .map(|p| std::fs::read_to_string(p).expect("fields"))
        .unwrap_or_default()
        .lines()
        .filter_map(|l| l.split_once('\t'))
        .map(|(k, v)| (k.trim_end_matches("@d0").to_owned(), v.to_owned()))
        .collect();
    let mut rows = Vec::new();
    ::utils::compilation::run_compiler_on_path(std::path::Path::new(&path), |tcx| {
        let program = program_of(tcx);
        let raw = |did: DefId, index: usize| {
            kinds
                .get(&format!("{}::field{index}", tcx.def_path_str(did)))
                .is_none_or(|kind| kind == "raw")
        };
        let started = std::time::Instant::now();
        // `CRAT_E5C_HOLD_FAULT` names one rule to drop, for the price of each;
        // `CRAT_E5C_HOLD_BYTES=off` drops R1's premise.
        // CRAT_E5C_HOLD_FAULT=Rule[,Rule...]: the first is the fault; all are removed.
        let rules: [Rule; 45] = [
            Rule::OutsideLoad,
            Rule::AllocatorHook,
            Rule::CopyCarry,
            Rule::ByteCopy,
            Rule::CellField,
            Rule::MixedUnion,
            Rule::Unknown,
            Rule::TopFlows,
            Rule::RawGuard,
            Rule::MutRead,
            Rule::DerivedStore,
            Rule::LibraryMemory,
            Rule::WrapperEscape,
            Rule::WrapperContents,
            Rule::StaticInit,
            Rule::AddressTaken,
            Rule::UnionMembers,
            Rule::ArrayInit,
            Rule::ByValue,
            Rule::ForeignEffects,
            Rule::StatementLiveness,
            Rule::MustDerive,
            Rule::ReturnedAlias,
            Rule::OutsideCopy,
            Rule::TopStores,
            Rule::Signedness,
            Rule::ForeignMutability,
            Rule::JointTargets,
            Rule::FormatWrites,
            Rule::StrtokState,
            Rule::EscapingExtent,
            Rule::Members,
            Rule::MemberCast,
            Rule::ContainerOf,
            Rule::VoidCast,
            Rule::IntLocalMemory,
            Rule::CrossCopy,
            Rule::Containers,
            Rule::WideStores,
            Rule::Callbacks,
            Rule::ViewValues,
            Rule::RoundTrip,
            Rule::Escape,
            Rule::IncomingStores,
            Rule::AggregateTransfer,
        ];
        let named: Vec<Rule> = std::env::var("CRAT_E5C_HOLD_FAULT")
            .unwrap_or_default()
            .split(',')
            .filter(|name| !name.is_empty())
            .map(|name| {
                *rules
                    .iter()
                    .find(|rule| format!("{rule:?}") == name)
                    .expect("a rule")
            })
            .collect();
        let fault = named.first().copied();
        let faults = named
            .iter()
            .fold(0u64, |mask, &rule| mask | (1u64 << rule as u64));
        let options = Options {
            fault,
            outside_bytes_disjoint: std::env::var("CRAT_E5C_HOLD_BYTES").as_deref() != Ok("off"),
            program_bytes_disjoint: std::env::var("CRAT_E5C_HOLD_BYTES").as_deref() == Ok("wide"),
            by_types: std::env::var("CRAT_E5C_HOLD_MODE").as_deref() == Ok("types"),
            closed: std::env::var("CRAT_E5C_HOLD_WORLD").as_deref() == Ok("closed"),
            faults,
            close_n1: std::env::var("CRAT_E5C_HOLD_CLOSE").is_ok_and(|v| v.contains("n1")),
            close_n2: std::env::var("CRAT_E5C_HOLD_CLOSE").is_ok_and(|v| v.contains("n2")),
            evident: std::env::var("CRAT_E5C_HOLD_MODE").as_deref() == Ok("evident"),
        };
        let check = RetainedAccessCheck::compute_options(&program, &raw, options);
        eprintln!(
            "E5C_HOLD {path} compute {:.1} s",
            started.elapsed().as_secs_f64()
        );
        for (f, local) in check.container_of_sites() {
            eprintln!(
                "E5C_HOLD {path} container-of {} {local:?}",
                tcx.def_path_str(f.to_def_id())
            );
        }
        for ((f, local), verdict) in check.verdicts() {
            let body = tcx.mir_drops_elaborated_and_const_checked(*f).borrow();
            let name = body
                .var_debug_info
                .iter()
                .find_map(|info| match info.value {
                    rustc_middle::mir::VarDebugInfoContents::Place(place)
                        if place.local == *local && place.projection.is_empty() =>
                    {
                        Some(info.name.to_string())
                    }
                    _ => None,
                })
                .unwrap_or_else(|| format!("_{}", local.as_usize()));
            rows.push(format!(
                "{}\t{}\t{name}\t{}\t{}\t{}\t{}",
                tcx.def_path_str(f.to_def_id()),
                local.as_usize(),
                if local.as_usize() <= body.arg_count {
                    "f"
                } else {
                    "l"
                },
                match verdict {
                    Verdict::Clear => "clear",
                    Verdict::Held(_) => "held",
                    Verdict::Unknown => "unknown",
                },
                verdict.receipt().unwrap_or_default(),
                check.premise(*f, *local).unwrap_or_default()
            ));
        }
    })
    .expect("compiles");
    rows.sort();
    std::fs::write(&out, rows.join("\n") + "\n").expect("write rows");
}

// ---- The Codex review's findings (era-5c 139 §4): each a RED witness of a missed
// ---- conflict; ignored until its fix lands, run with `--ignored`.

/// R1: a byte pointer an outside caller provides may point into typed storage.
const R1_BYTE_ALIAS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct H { pub p: *mut u8 }
pub unsafe fn f(x: *mut u32, h: *mut H) -> u32 { let v = *x; *(*h).p = 0; v + *x }
"#;

/// R1b: an unknown call's result used without a cast is anything (`Top`).
const R1B_OPAQUE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn give(p: *mut i32); fn get() -> *mut i32; }
unsafe fn f(x: *mut i32) -> i32 { let p = get(); *p = 1; *x }
pub unsafe fn entry() { let mut v = 0; give(&mut v); f(&mut v); }
"#;

/// The library's memory (`errno`) is never a program object, even one handed out (`v`
/// escapes through `give`, so 2.3 alone would let an outside `int` reach it).
const LIBRARY: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn __errno_location() -> *mut i32; fn give(p: *mut i32); }
unsafe fn f(x: *mut i32) -> i32 { let p = __errno_location(); *p = 1; *x }
pub unsafe fn entry() { let mut v = 0; give(&mut v); f(&mut v); }
"#;

#[test]
fn e5c_hold_library_memory_is_not_the_program() {
    assert!(!held(LIBRARY, "f::x"));
}

#[test]
fn e5c_hold_fault_library_memory() {
    assert!(
        held_faulted(LIBRARY, "f::x", Rule::LibraryMemory),
        "the fault is caught"
    );
}

/// R2: an allocator wrapper that also stores the fresh pointer.
const R2_WRAPPER_ESCAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; }
static mut G: *mut i32 = core::ptr::null_mut();
unsafe fn make() -> *mut i32 { let p = malloc(4) as *mut i32; G = p; p }
unsafe fn f(x: *mut i32) -> i32 { *G = 1; *x }
pub unsafe fn entry() { let p = make(); f(p); }
"#;

/// R2b: a wrapper that initializes a pointer field of the fresh object.
const R2B_WRAPPER_FIELD: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct N { pub buf: *mut i32 }
unsafe fn make(v: *mut i32) -> *mut N { let n = malloc(8) as *mut N; (*n).buf = v; n }
unsafe fn f(x: *mut i32, n: *mut N) -> i32 { *(*n).buf = 1; *x }
pub unsafe fn entry() { let mut v = 0; let n = make(&mut v); f(&mut v, n); }
"#;

/// R3: a static initialized with another static's address.
const R3_STATIC_INIT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
static mut V: i32 = 0;
static mut G: *mut i32 = unsafe { &raw mut V };
unsafe fn f(x: *mut i32) -> i32 { *G = 1; *x }
pub unsafe fn entry() { f(&raw mut V); }
"#;

/// R4: a pointer local whose address is taken (an out-parameter).
const R4_ADDRESS_TAKEN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
unsafe fn f(x: *mut i32, pp: *mut *mut i32) -> i32 { **pp = 1; *x }
pub unsafe fn entry() { let mut v = 0; let mut slot: *mut i32 = &mut v; f(&mut v, &mut slot); }
"#;

/// R5: a union's members are one place.
const R5_UNION: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub union U { pub p: *mut i32, pub q: *mut i32 }
unsafe fn f(x: *mut i32, u: *mut U) -> i32 { *(*u).q = 1; *x }
pub unsafe fn entry() { let mut v = 0; let mut u = U { p: &mut v }; f(&mut v, &mut u); }
"#;

/// R6: an array initializer stores its pointers.
const R6_ARRAY_INIT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
unsafe fn f(x: *mut i32, a: *mut *mut i32) -> i32 { **a = 1; *x }
pub unsafe fn entry() { let mut v = 0; let mut a: [*mut i32; 1] = [&mut v]; f(&mut v, a.as_mut_ptr()); }
"#;

/// R7: a struct passed by value carries its pointers into the callee.
const R7_BY_VALUE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] #[derive(Clone, Copy)] pub struct S { pub p: *mut i32 }
unsafe fn f(x: *mut i32, s: S) -> i32 { *s.p = 1; *x }
pub unsafe fn entry() { let mut v = 0; let s = S { p: &mut v }; f(&mut v, s); }
"#;

/// R8: a byte copy through a wider integer temporary.
const R8_WIDE_TEMP: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct S { pub p: *mut i32 }
unsafe fn copy_bytes(d: *mut S, s: *mut S) {
    let dp = d as *mut u8;
    let sp = s as *const u8;
    let mut i = 0;
    while i < 8 { let t: u32 = *sp.offset(i) as u32; *dp.offset(i) = t as u8; i += 1; }
}
unsafe fn write_through(t: *mut S) { *(*t).p = 1; }
unsafe fn f(x: *mut i32, a: *mut S, b: *mut S) { copy_bytes(b, a); write_through(b); }
pub unsafe fn entry() {
    let mut v = 0i32;
    let mut a = S { p: &mut v };
    let mut b = S { p: core::ptr::null_mut() };
    f(&mut v, &mut a, &mut b);
}
"#;

/// R9: `memcpy` reads through its source, a read that conflicts a `&mut` subject.
const R9_FOREIGN_READ: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct H { pub p: *mut i32 }
unsafe fn f(x: *mut i32, h: *mut H) -> i32 {
    *x = 1;
    let mut t = 0i32;
    memcpy(&mut t as *mut i32 as *mut core::ffi::c_void, (*h).p as *const core::ffi::c_void, 4);
    *x
}
pub unsafe fn entry() { let mut v = 0; let mut h = H { p: &mut v }; f(&mut v, &mut h); }
"#;

/// R10: a local live only inside one block.
const R10_ONE_BLOCK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct H { pub p: *mut i32, pub q: *mut i32 }
unsafe fn f(h: *mut H) -> i32 { let p = (*h).p; let a = *p; *(*h).q = 1; let b = *p; a ^ b }
pub unsafe fn entry() { let mut v = 0; let mut h = H { p: &mut v, q: &mut v }; f(&mut h); }
"#;

/// R11: a local that only may derive from the subject is not the subject's.
const R11_MAY_DERIVE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct S { pub x: i32, pub saved: *mut i32 }
unsafe fn f(s: *mut S, b: bool) -> i32 {
    let p: *mut i32 = &raw mut (*s).x;
    let a = *p;
    let q = if b { p } else { (*s).saved };
    *q = 1;
    let c = *p;
    a ^ c
}
pub unsafe fn entry() { let mut s = S { x: 0, saved: core::ptr::null_mut() }; s.saved = &raw mut s.x; f(&mut s, false); }
"#;

/// R12: a pointer a callee returns derived from its argument extends the argument's extent.
const R12_RETURNED_ALIAS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct H { pub p: *mut i32, pub g: *mut i32 }
unsafe fn id(p: *mut i32) -> *mut i32 { p }
unsafe fn f(h: *mut H) -> i32 { let p = (*h).p; let q = id(p); let a = *q; *(*h).g = 1; let b = *q; a ^ b }
pub unsafe fn entry() { let mut v = 0; let mut h = H { p: &mut v, g: &mut v }; f(&mut h); }
"#;

fn held(code: &str, subject: &str) -> bool {
    of(&verdicts(code), subject).withdraws()
}

fn held_faulted(code: &str, subject: &str, rule: Rule) -> bool {
    of(&verdicts_faulted(code, &[], rule), subject).withdraws()
}

/// R1: kept as the premise (an outside byte object never meets a typed one), Clear;
/// dropped, held.
#[test]
fn e5c_hold_r1_the_byte_premise_both_ways() {
    assert!(!held(R1_BYTE_ALIAS, "f::x"), "under the premise");
    let v = verdicts_opts(
        R1_BYTE_ALIAS,
        &[],
        Options {
            outside_bytes_disjoint: false,
            ..Options::default()
        },
    );
    assert!(of(&v, "f::x").withdraws(), "without the premise");
}

macro_rules! witness {
    ($name:ident, $fault:ident, $code:expr, $subject:expr, $rule:expr) => {
        #[test]
        fn $name() {
            assert!(held($code, $subject), "{} is held", $subject);
        }
        #[test]
        fn $fault() {
            assert!(!held_faulted($code, $subject, $rule), "the fault is caught");
        }
    };
}

witness!(
    e5c_hold_r1b_opaque,
    e5c_hold_fault_r1b_opaque,
    R1B_OPAQUE,
    "f::x",
    Rule::TopFlows
);
witness!(
    e5c_hold_r2_wrapper_escape,
    e5c_hold_fault_r2_wrapper_escape,
    R2_WRAPPER_ESCAPE,
    "f::x",
    Rule::WrapperEscape
);
witness!(
    e5c_hold_r2b_wrapper_field,
    e5c_hold_fault_r2b_wrapper_field,
    R2B_WRAPPER_FIELD,
    "f::x",
    Rule::WrapperContents
);
witness!(
    e5c_hold_r3_static_init,
    e5c_hold_fault_r3_static_init,
    R3_STATIC_INIT,
    "f::x",
    Rule::StaticInit
);
witness!(
    e5c_hold_r4_address_taken,
    e5c_hold_fault_r4_address_taken,
    R4_ADDRESS_TAKEN,
    "f::x",
    Rule::AddressTaken
);
witness!(
    e5c_hold_r5_union,
    e5c_hold_fault_r5_union,
    R5_UNION,
    "f::x",
    Rule::UnionMembers
);
witness!(
    e5c_hold_r6_array_init,
    e5c_hold_fault_r6_array_init,
    R6_ARRAY_INIT,
    "f::x",
    Rule::ArrayInit
);
witness!(
    e5c_hold_r7_by_value,
    e5c_hold_fault_r7_by_value,
    R7_BY_VALUE,
    "f::x",
    Rule::ByValue
);
witness!(
    e5c_hold_r8_wide_temp,
    e5c_hold_fault_r8_wide_temp,
    R8_WIDE_TEMP,
    "f::x",
    Rule::ByteCopy
);
witness!(
    e5c_hold_r9_foreign_read,
    e5c_hold_fault_r9_foreign_read,
    R9_FOREIGN_READ,
    "f::x",
    Rule::ForeignEffects
);
witness!(
    e5c_hold_r10_one_block,
    e5c_hold_fault_r10_one_block,
    R10_ONE_BLOCK,
    "f::p",
    Rule::StatementLiveness
);
witness!(
    e5c_hold_r11_may_derive,
    e5c_hold_fault_r11_may_derive,
    R11_MAY_DERIVE,
    "f::p",
    Rule::MustDerive
);
witness!(
    e5c_hold_r12_returned_alias,
    e5c_hold_fault_r12_returned_alias,
    R12_RETURNED_ALIAS,
    "f::p",
    Rule::ReturnedAlias
);

/// brotli's `h#488`: a local stores a pointer derived from itself into memory.
const LOCAL_STORE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct A { pub symbol_lists: *mut u16, pub array: [u16; 32] }
#[repr(C)] pub struct S { pub arena: A }
pub unsafe fn f(s: *mut S) { let h: *mut A = &mut (*s).arena; (*h).symbol_lists = (*h).array.as_mut_ptr().offset(16); }
"#;

witness!(
    e5c_hold_a_local_derived_store,
    e5c_hold_fault_local_derived_store,
    LOCAL_STORE,
    "f::h",
    Rule::DerivedStore
);

/// An unlisted foreign call is `Top`: its effects are anything.
const UNLISTED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn mystery(p: *mut core::ffi::c_void); }
unsafe fn f(x: *mut i32, y: *mut i32) -> i32 { *x = 1; mystery(y as *mut core::ffi::c_void); *x }
pub unsafe fn entry() { let mut v = 0; let mut w = 0; f(&mut v, &mut w); }
"#;

#[test]
fn e5c_hold_an_unlisted_foreign_call_is_unknown() {
    assert_eq!(of(&verdicts(UNLISTED), "f::x"), &Verdict::Unknown);
}

#[test]
fn e5c_hold_fault_top_flows_unlisted() {
    assert!(
        !held_faulted(UNLISTED, "f::x", Rule::TopFlows),
        "the fault is caught"
    );
}

/// R13: two bodies of one shape have different identities.
#[test]
fn e5c_hold_r13_body_identity_is_the_body() {
    const TWO: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
pub unsafe fn a(p: *mut i32, q: *mut i32) { *p = 1; *q = 2; }
pub unsafe fn b(p: *mut i32, q: *mut i32) { *q = 1; *p = 2; }
"#;
    ::utils::compilation::run_compiler_on_str(TWO, |tcx| {
        let program = program_of(tcx);
        let ids: Vec<u64> = program
            .functions
            .iter()
            .map(|&f| body_identity(&tcx.mir_drops_elaborated_and_const_checked(f).borrow()))
            .collect();
        assert_eq!(ids.len(), 2);
        assert_ne!(ids[0], ids[1]);
    })
    .expect("compiles");
}

/// Inventory (era-5c 140): the foreign functions a program calls or takes by address,
/// with counts, to `CRAT_E5C_SIDE_ROWS`.
#[test]
#[ignore = "the foreign-call inventory (era-5c 140)"]
fn e5c_hold_foreign_inventory() {
    let path = std::env::var("CRAT_E5C_SIDE_SOURCE").expect("CRAT_E5C_SIDE_SOURCE");
    let out = std::env::var("CRAT_E5C_SIDE_ROWS").expect("CRAT_E5C_SIDE_ROWS");
    let mut counts: std::collections::BTreeMap<String, (usize, usize)> = Default::default();
    let mut rustlib: Vec<String> = Vec::new();
    ::utils::compilation::run_compiler_on_path(std::path::Path::new(&path), |tcx| {
        for f in program_of(tcx).functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            let mut note = |op: &rustc_middle::mir::Operand<'_>, called: bool| {
                if let Some(c) = op.constant()
                    && let rustc_middle::ty::TyKind::FnDef(d, _) = c.ty().kind()
                    && tcx.is_foreign_item(*d)
                {
                    let e = counts.entry(tcx.item_name(*d).to_string()).or_default();
                    if called { e.0 += 1 } else { e.1 += 1 }
                }
            };
            for data in body.basic_blocks.iter() {
                for st in &data.statements {
                    if let rustc_middle::mir::StatementKind::Assign(box (_, rv)) = &st.kind {
                        match rv {
                            rustc_middle::mir::Rvalue::Cast(_, op, _) => note(op, false),
                            rustc_middle::mir::Rvalue::Aggregate(_, ops) => {
                                ops.iter().for_each(|op| note(op, false))
                            }
                            _ => {}
                        }
                    }
                }
                if let rustc_middle::mir::TerminatorKind::Call { func, args, .. } =
                    &data.terminator().kind
                {
                    if let Some(c) = func.constant()
                        && let rustc_middle::ty::TyKind::FnDef(d, _) = c.ty().kind()
                        && !d.is_local()
                    {
                        rustlib.push(format!("rustlib:{}", tcx.def_path_str(*d)));
                    }
                    note(func, true);
                    args.iter().for_each(|a| note(&a.node, false));
                }
            }
        }
    })
    .expect("compiles");
    for name in rustlib {
        counts.entry(name).or_default().0 += 1;
    }
    let rows: Vec<String> = counts
        .iter()
        .map(|(k, (c, t))| format!("{k}\t{c}\t{t}"))
        .collect();
    std::fs::write(&out, rows.join("\n") + "\n").expect("write");
}

// ---- Codex round 2 (era-5c 140 §6): each a RED witness of a missed conflict, ignored until
// ---- its fix lands.

/// 2.1: a struct copied out of outside memory keeps the outside's pointers.
const Q1_OUTSIDE_COPY: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] #[derive(Clone, Copy)] pub struct S { pub q: *mut i32 }
pub unsafe fn f(p: *mut i32, s: *const S) -> i32 { let t = *s; *t.q = 1; *p }
"#;

/// 2.2: a store through an integer-made address reaches a static.
const Q2_TOP_STORE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
static mut G: *mut i32 = core::ptr::null_mut();
unsafe fn init(v: *mut i32) { let u = &raw mut G as usize; *(u as *mut *mut i32) = v; }
unsafe fn f(p: *mut i32) -> i32 { *G = 1; *p }
pub unsafe fn entry() { let mut x = 0; init(&mut x); f(&mut x); }
"#;

/// 2.2's fault witness: the integer address comes from the outside, so no program
/// object is exposed by the cast (with `&raw mut G as usize`, 3.4 covers the case too).
const Q2_TOP_STORE_OUTSIDE_ADDRESS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
static mut G: *mut i32 = core::ptr::null_mut();
unsafe fn init(v: *mut i32, a: usize) { *(a as *mut *mut i32) = v; }
unsafe fn f(p: *mut i32) -> i32 { *G = 1; *p }
pub unsafe fn entry(a: usize) { let mut x = 0; init(&mut x, a); f(&mut x); }
"#;

/// 2.4: corresponding signed and unsigned types alias.
const Q4_SIGNEDNESS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct S { pub q: *mut u32 }
pub unsafe fn f(p: *mut i32, s: *mut S) -> i32 { *(*s).q = 1; *p }
"#;

/// 2.5: a callee that may return its argument or a retained pointer.
const Q5_MAY_RETURN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
static mut X: i32 = 0;
static mut G: *mut i32 = unsafe { &raw mut X };
unsafe fn pick(a: *mut i32, b: i32) -> *mut i32 { if b != 0 { a } else { G } }
unsafe fn f(b: i32) -> i32 { let p: *mut i32 = &raw mut X; let r = *p; let q = pick(p, b); *q = 1; r ^ *p }
pub unsafe fn entry() { f(0); }
"#;

/// 2.6: `memset` makes a local mutable; a retained read then conflicts.
const Q6_FOREIGN_MUT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
extern "C" { fn memset(d: *mut core::ffi::c_void, c: i32, n: u64) -> *mut core::ffi::c_void; }
static mut X: u8 = 1;
static mut G: *mut u8 = unsafe { &raw mut X };
unsafe fn f() -> i32 { let p: *mut u8 = &raw mut X; memset(p as *mut core::ffi::c_void, 0, 1); let r = *G as i32; r + *p as i32 }
pub unsafe fn entry() { f(); }
"#;

/// 2.7: a function pointer that may be a program function or a C library one.
const Q7_MIXED_TARGETS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
extern "C" { fn strcpy(d: *mut i8, s: *const i8) -> *mut i8; }
static mut BUF: [i8; 8] = [0; 8];
static mut G: *mut i8 = unsafe { &raw mut BUF as *mut i8 };
unsafe extern "C" fn noop(d: *mut i8, _s: *const i8) -> *mut i8 { d }
static mut FP: Option<unsafe extern "C" fn(*mut i8, *const i8) -> *mut i8> = None;
unsafe fn f(p: *const i8) -> i32 { (FP.unwrap())(G, b"x\0".as_ptr() as *const i8); *p as i32 }
pub unsafe fn entry(c: i32) { FP = if c != 0 { Some(strcpy) } else { Some(noop) }; f(&raw mut BUF as *const i8); }
"#;

/// 2.8: `printf`'s `%n` writes through a vararg.
const Q8_PRINTF_N: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
extern "C" { fn printf(f: *const i8, ...) -> i32; }
static mut X: i32 = 0;
static mut G: *mut i32 = unsafe { &raw mut X };
unsafe fn f(p: *const i32) -> i32 { printf(b"%n\0".as_ptr() as *const i8, G); *p }
pub unsafe fn entry() { f(&raw mut X); }
"#;

/// 2.9: `strtok(NULL, …)` writes the buffer an earlier call remembered.
const Q9_STRTOK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn strtok(s: *mut i8, d: *const i8) -> *mut i8; }
unsafe fn f(p: *const i8) -> i32 { strtok(core::ptr::null_mut(), b",\0".as_ptr() as *const i8); *p as i32 }
pub unsafe fn entry() { let mut b: [i8; 6] = [97, 44, 98, 44, 99, 0]; strtok(b.as_mut_ptr(), b",\0".as_ptr() as *const i8); f(b.as_ptr().offset(3)); }
"#;

/// 2.10: a nested union: one member's struct field read through the other's.
const Q10_NESTED_UNION: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
#[repr(C)] #[derive(Clone, Copy)] pub struct A { pub p: *mut i32 }
#[repr(C)] #[derive(Clone, Copy)] pub struct B { pub q: *mut i32 }
#[repr(C)] pub union U { pub a: A, pub b: B }
static mut X: i32 = 0;
static mut G: *mut i32 = unsafe { &raw mut X };
unsafe fn f(p: *mut i32) -> i32 { let u = U { a: A { p: G } }; *u.b.q = 1; *p }
pub unsafe fn entry() { f(&raw mut X); }
"#;

/// 2.11: a pointer copied bytewise through an integer field.
const Q11_INT_FIELD: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
#[repr(C)] pub struct Spill { pub b: u64 }
static mut X: i32 = 0;
static mut G: *mut i32 = unsafe { &raw mut X };
unsafe fn f(p: *mut i32) -> i32 {
    let mut src: *mut i32 = G;
    let mut dst: *mut i32 = core::ptr::null_mut();
    let mut spill = Spill { b: 0 };
    let s = &raw mut src as *mut u8;
    let d = &raw mut dst as *mut u8;
    let mut i = 0;
    while i < 8 { spill.b = *s.offset(i) as u64; *d.offset(i) = spill.b as u8; i += 1; }
    *dst = 1;
    *p
}
pub unsafe fn entry() { f(&raw mut X); }
"#;

/// 2.12: a pointer carried inside an aggregate extends the local's extent.
const Q12_CARRIED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
#[repr(C)] #[derive(Clone, Copy)] pub struct S { pub q: *mut i32 }
static mut X: i32 = 0;
static mut G: *mut i32 = unsafe { &raw mut X };
unsafe fn f(c: i32) -> i32 { let p: *mut i32 = &raw mut X; let r = *p; let s = S { q: p }; if c != 0 { *G = 1; } r ^ *s.q }
pub unsafe fn entry() { f(1); }
"#;

/// 2.3: an outside byte pointer to the program's own global (R1's narrower sentence).
const Q3_OWN_GLOBAL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
#[no_mangle] pub static mut X: i32 = 0;
pub unsafe fn entry(slot: *mut *mut u8) -> i32 { let p: *mut i32 = &raw mut X; let r = *p; **slot = 1; r ^ *p }
"#;

witness!(
    e5c_hold_r2_1_outside_copy,
    e5c_hold_fault_r2_1_outside_copy,
    Q1_OUTSIDE_COPY,
    "f::p",
    Rule::OutsideCopy
);
witness!(
    e5c_hold_r2_2_top_store,
    e5c_hold_fault_r2_2_top_store,
    Q2_TOP_STORE_OUTSIDE_ADDRESS,
    "f::p",
    Rule::TopStores
);
witness!(
    e5c_hold_r2_4_signedness,
    e5c_hold_fault_r2_4_signedness,
    Q4_SIGNEDNESS,
    "f::p",
    Rule::Signedness
);
witness!(
    e5c_hold_r2_5_may_return,
    e5c_hold_fault_r2_5_may_return,
    Q5_MAY_RETURN,
    "f::p",
    Rule::MustDerive
);
witness!(
    e5c_hold_r2_6_foreign_mut,
    e5c_hold_fault_r2_6_foreign_mut,
    Q6_FOREIGN_MUT,
    "f::p",
    Rule::ForeignMutability
);
witness!(
    e5c_hold_r2_7_mixed_targets,
    e5c_hold_fault_r2_7_mixed_targets,
    Q7_MIXED_TARGETS,
    "f::p",
    Rule::JointTargets
);
witness!(
    e5c_hold_r2_8_printf_n,
    e5c_hold_fault_r2_8_printf_n,
    Q8_PRINTF_N,
    "f::p",
    Rule::FormatWrites
);
witness!(
    e5c_hold_r2_9_strtok,
    e5c_hold_fault_r2_9_strtok,
    Q9_STRTOK,
    "f::p",
    Rule::StrtokState
);
witness!(
    e5c_hold_r2_10_nested_union,
    e5c_hold_fault_r2_10_nested_union,
    Q10_NESTED_UNION,
    "f::p",
    Rule::UnionMembers
);
witness!(
    e5c_hold_r2_11_int_field,
    e5c_hold_fault_r2_11_int_field,
    Q11_INT_FIELD,
    "f::p",
    Rule::ByteCopy
);
witness!(
    e5c_hold_r2_12_carried,
    e5c_hold_fault_r2_12_carried,
    Q12_CARRIED,
    "f::p",
    Rule::EscapingExtent
);

/// A literal format without `%n` reads its varargs only.
const PRINTF_PLAIN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
extern "C" { fn printf(f: *const i8, ...) -> i32; }
static mut X: i32 = 0;
static mut G: *mut i32 = unsafe { &raw mut X };
unsafe fn f(p: *const i32) -> i32 { printf(b"%d\0".as_ptr() as *const i8, *G); *p }
pub unsafe fn entry() { f(&raw mut X); }
"#;

#[test]
fn e5c_hold_a_plain_format_only_reads() {
    assert!(!held(PRINTF_PLAIN, "f::p"));
}

#[test]
fn e5c_hold_red2_3_own_global() {
    assert!(held(Q3_OWN_GLOBAL, "entry::p"));
}

#[test]
fn e5c_hold_fault_escape() {
    assert!(
        !held_faulted(Q3_OWN_GLOBAL, "entry::p", Rule::Escape),
        "the fault is caught"
    );
}

/// 2.3's other side: a stack object the program never hands out is not what an outside
/// pointer reaches, whatever its type; handed to a foreign call, it is.
const ESCAPE_LOCAL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn keep(p: *mut i32); }
pub unsafe fn kept(slot: *mut *mut i32) -> i32 {
    let mut x = 0;
    let p: *mut i32 = &raw mut x;
    keep(p);
    let r = *p;
    **slot = 1;
    r ^ *p
}
pub unsafe fn private(slot: *mut *mut i32) -> i32 {
    let mut x = 0;
    let p: *mut i32 = &raw mut x;
    let r = *p;
    **slot = 1;
    r ^ *p
}
"#;

#[test]
fn e5c_hold_escape_a_handed_local_meets_the_outside() {
    assert!(held(ESCAPE_LOCAL, "kept::p"));
}

#[test]
fn e5c_hold_escape_a_private_local_does_not() {
    assert_eq!(of(&verdicts(ESCAPE_LOCAL), "private::p"), &Verdict::Clear);
}

// ---- Item 4 (relay 175): members. The address of a struct field names the member; two
// ---- members of one object are disjoint unless one contains the other.

/// Brotli's decoder: `br` is a member of the state; the state's own pointer into its
/// symbol array writes another member.
const MEMBERS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct BitReader { pub next_in: *const u8, pub avail_in: usize }
#[repr(C)] pub struct State {
    pub br: BitReader,
    pub buffer: [u8; 8],
    pub symbol_lists: *mut u16,
    pub symbols_lists_array: [u16; 32],
}
unsafe fn init(s: *mut State) {
    (*s).symbol_lists = (*s).symbols_lists_array.as_mut_ptr().offset(16);
    (*s).br.next_in = (*s).buffer.as_mut_ptr();
}
unsafe fn step(br: *mut BitReader, s: *mut State) -> usize {
    let a = (*br).avail_in;
    *(*s).symbol_lists = 0;
    a ^ (*br).avail_in
}
unsafe fn whole(s: *mut State) -> u16 {
    let a = (*s).symbols_lists_array[16];
    *(*s).symbol_lists = 1;
    a ^ (*s).symbols_lists_array[16]
}
unsafe fn first(p: *mut State) -> u16 {
    let a = (*p).symbols_lists_array[16];
    *(*p).symbol_lists = 1;
    a ^ (*p).symbols_lists_array[16]
}
pub unsafe fn decode(s: *mut State) -> usize {
    init(s);
    let br: *mut BitReader = &raw mut (*s).br;
    let r = step(br, s);
    whole(s);
    first(br as *mut State);
    r
}
"#;

#[test]
fn e5c_hold_members_a_member_is_not_its_sibling() {
    let v = verdicts(MEMBERS);
    assert_eq!(of(&v, "step::br"), &Verdict::Clear, "{v:#?}");
}

#[test]
fn e5c_hold_members_the_whole_object_holds() {
    let v = verdicts(MEMBERS);
    assert!(writes(of(&v, "whole::s")), "{v:#?}");
}

#[test]
fn e5c_hold_members_a_first_member_cast_is_the_container() {
    let v = verdicts(MEMBERS);
    assert!(writes(of(&v, "first::p")), "{v:#?}");
}

#[test]
fn e5c_hold_fault_members() {
    assert!(
        held_faulted(MEMBERS, "step::br", Rule::Members),
        "the fault is caught"
    );
}

#[test]
fn e5c_hold_fault_member_cast() {
    let v = verdicts_faulted(MEMBERS, &[], Rule::MemberCast);
    assert_eq!(of(&v, "first::p"), &Verdict::Clear, "the fault is caught");
}

/// Container-of: a member's address moved back through a byte pointer reaches the
/// container, so its sibling `key`; a constant offset inside the member stays in it.
const CONTAINER_OF: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct Link { pub next: *mut Link }
#[repr(C)] pub struct Node { pub key: i32, pub pad: i32, pub link: Link }
#[repr(C)] pub struct H { pub head: *mut Link }
unsafe fn back(k: *mut i32, h: *mut H) -> i32 {
    let a = *k;
    let c = ((*h).head as *mut u8).offset(-8) as *mut i32;
    *c = 1;
    a ^ *k
}
unsafe fn ahead(k: *mut i32, h: *mut H) -> i32 {
    let a = *k;
    let c = ((*h).head as *mut u8).offset(4) as *mut i32;
    *c = 1;
    a ^ *k
}
unsafe fn past(k: *mut i32, h: *mut H) -> i32 {
    let a = *k;
    let c = ((*h).head as *mut u8).offset(4).offset(4) as *mut i32;
    *c = 1;
    a ^ *k
}
pub unsafe fn entry() {
    let mut n = Node { key: 0, pad: 0, link: Link { next: core::ptr::null_mut() } };
    let mut h = H { head: &raw mut n.link };
    back(&raw mut n.key, &mut h);
    ahead(&raw mut n.key, &mut h);
    past(&raw mut n.key, &mut h);
}
"#;

#[test]
fn e5c_hold_members_container_of() {
    let v = verdicts(CONTAINER_OF);
    assert!(writes(of(&v, "back::k")), "{v:#?}");
    assert!(
        writes(of(&v, "past::k")),
        "a moved view moved again: {v:#?}"
    );
}

#[test]
fn e5c_hold_members_a_forward_byte_offset_stays_in_the_member() {
    let v = verdicts(CONTAINER_OF);
    assert_eq!(of(&v, "ahead::k"), &Verdict::Clear, "{v:#?}");
}

#[test]
fn e5c_hold_fault_container_of() {
    let v = verdicts_faulted(CONTAINER_OF, &[], Rule::ContainerOf);
    assert_eq!(of(&v, "back::k"), &Verdict::Clear, "the fault is caught");
}

/// A member reached again through a cast to its container's type (json.h's shape) does
/// not nest: without the bound the fixpoint made a member of a member forever.
const MEMBER_CAST_CYCLE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct B { pub a: *mut A, pub y: i32 }
#[repr(C)] pub struct A { pub b: B, pub x: i32 }
unsafe fn walk(mut p: *mut A, n: i32) -> i32 {
    let mut i = 0;
    while i < n { p = &raw mut (*p).b as *mut A; i += 1; }
    (*p).x
}
pub unsafe fn entry() -> i32 {
    let mut a = A { b: B { a: core::ptr::null_mut(), y: 0 }, x: 0 };
    walk(&mut a, 3)
}
"#;

#[test]
fn e5c_hold_members_a_cast_cycle_terminates() {
    let v = verdicts(MEMBER_CAST_CYCLE);
    assert!(v.contains_key("walk::p"), "{v:#?}");
}

// ---- Codex round 3 (era-5c 141 §3): each a RED witness of a missed conflict, ignored until
// ---- its fix lands.

/// 3.1: a first-member cast recovers the intermediate container `o.i`, not only `o`.
const T1_INTERMEDIATE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct I { pub x: i32, pub y: i32 }
#[repr(C)] pub struct O { pub tag: i32, pub i: I }
#[repr(C)] pub struct H { pub q: *mut i32 }
unsafe fn g(p: *mut i32, h: *mut H) -> i32 { *(*h).q = 1; *p }
pub unsafe fn f() -> i32 {
    let mut o = O { tag: 0, i: I { x: 0, y: 0 } };
    let i = &raw mut o.i.x as *mut I;
    let mut h = H { q: &raw mut (*i).y };
    let p: *mut i32 = &raw mut o.i.y;
    g(p, &mut h)
}
"#;

/// 3.2: a path truncated at a union (or an index) must not later split into disjoint paths.
const T2_TRUNCATED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] #[derive(Clone, Copy)] pub struct L { pub x: i32 }
#[repr(C)] #[derive(Clone, Copy)] pub struct N { pub l: L }
#[repr(C)] pub union U { pub n: N }
#[repr(C)] pub struct H { pub q: *mut i32 }
unsafe fn g(p: *mut i32, h: *mut H) -> i32 { *(*h).q = 1; *p }
pub unsafe fn f() -> i32 {
    let mut u = U { n: N { l: L { x: 0 } } };
    let n: *mut N = &raw mut u.n;
    let l: *mut L = &raw mut u.n.l;
    let mut h = H { q: &raw mut (*l).x };
    let p: *mut i32 = &raw mut (*n).l.x;
    g(p, &mut h)
}
"#;

/// 3.3: memcpy between two pointer fields of one object.
const T3_FIELD_COPY: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct H { pub a: *mut i32, pub b: *mut i32 }
unsafe fn g(p: *mut i32, h: *mut H) -> i32 { *(*h).b = 1; *p }
pub unsafe fn f() -> i32 {
    let mut x = 0;
    let mut h = H { a: &raw mut x, b: core::ptr::null_mut() };
    memcpy(&raw mut h.b as *mut core::ffi::c_void, &raw mut h.a as *const core::ffi::c_void, 8);
    g(&raw mut x, &mut h)
}
"#;

/// 3.4: storage the program hands out is written by the outside.
const T4_PUBLISHED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
static mut SAVED: *mut i32 = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn slot() -> *mut *mut i32 { &raw mut SAVED }
#[no_mangle] pub unsafe extern "C" fn use_(p: *mut i32) -> i32 { *SAVED = 1; *p }
"#;

/// 3.5: a store through an integer-made address into an address-taken pointer local,
/// before the subject's extent.
const T5_TOP_LOCAL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[inline(never)] fn cut() {}
pub unsafe fn f() -> i32 {
    let mut x = 0;
    let mut q: *mut i32 = core::ptr::null_mut();
    *((&raw mut q as usize) as *mut *mut i32) = &raw mut x;
    cut();
    let p: *mut i32 = &raw mut x;
    let r = *p;
    *q = 1;
    r ^ *p
}
"#;

/// 3.6: pointer bytes memcpy'd into an integer, the integer copied, copied back.
const T6_INT_COPY: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void; }
pub unsafe fn f() -> i32 {
    let mut x = 0;
    let mut src: *mut i32 = &raw mut x;
    let mut q: *mut i32 = core::ptr::null_mut();
    let mut bits: u64 = 0;
    memcpy(&raw mut bits as *mut core::ffi::c_void, &raw mut src as *const core::ffi::c_void, 8);
    let mut copy: u64 = bits;
    memcpy(&raw mut q as *mut core::ffi::c_void, &raw mut copy as *const core::ffi::c_void, 8);
    let p: *mut i32 = &raw mut x;
    let r = *p;
    *q = 1;
    r ^ *p
}
"#;

/// 3.7: a format literal read from an offset (`"%%n" + 1` is `%n`).
const T7_FORMAT_OFFSET: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn printf(f: *const i8, ...) -> i32; }
#[repr(C)] pub struct H { pub q: *mut i32 }
unsafe fn g(p: *const i32, h: *mut H) -> i32 { printf((b"%%n\0".as_ptr() as *const i8).offset(1), (*h).q); *p }
pub unsafe fn f() -> i32 { let mut x = 0; let mut h = H { q: &raw mut x }; g(&raw mut x, &mut h) }
"#;

/// 3.8: a pointer returned inside an aggregate extends the caller local's extent.
const T8_AGGREGATE_RETURN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] #[derive(Clone, Copy)] pub struct H { pub q: *mut i32 }
#[inline(never)] unsafe fn pack(v: *mut i32) -> H { H { q: v } }
pub unsafe fn f() -> i32 {
    let mut x = 0;
    let raw = H { q: &raw mut x };
    let p: *mut i32 = &raw mut x;
    let out = pack(p);
    *raw.q = 1;
    *out.q
}
"#;

#[test]
fn e5c_hold_red3_1_intermediate_container() {
    assert!(held(T1_INTERMEDIATE, "g::p"));
}
#[test]
fn e5c_hold_red3_2_truncated_path() {
    assert!(held(T2_TRUNCATED, "g::p"));
}
#[test]
fn e5c_hold_red3_3_field_copy() {
    assert!(held(T3_FIELD_COPY, "g::p"));
}
#[test]
fn e5c_hold_red3_4_published_storage() {
    assert!(held(T4_PUBLISHED, "use_::p"));
}
#[test]
fn e5c_hold_red3_5_top_store_local() {
    assert!(held(T5_TOP_LOCAL, "f::p"));
}
#[test]
fn e5c_hold_red3_6_int_copy() {
    assert!(held(T6_INT_COPY, "f::p"));
}
#[test]
fn e5c_hold_red3_7_format_offset() {
    assert!(held(T7_FORMAT_OFFSET, "g::p"));
}
#[test]
fn e5c_hold_red3_8_aggregate_return() {
    assert!(held(T8_AGGREGATE_RETURN, "f::p"));
}

#[test]
fn e5c_hold_fault_round3() {
    // Each round-3 rule's fault: the witness clears without it.
    assert!(
        !held_faulted(T4_PUBLISHED, "use_::p", Rule::IncomingStores),
        "3.4"
    );
    assert!(
        !held_faulted(T8_AGGREGATE_RETURN, "f::p", Rule::AggregateTransfer),
        "3.8"
    );
    assert!(
        !held_faulted(T3_FIELD_COPY, "g::p", Rule::Members),
        "3.3 rides Members"
    );
    assert!(!held_faulted(T5_TOP_LOCAL, "f::p", Rule::TopStores), "3.5");
    assert!(!held_faulted(T6_INT_COPY, "f::p", Rule::ByteCopy), "3.6");
}

#[test]
fn e5c_hold_r2_2_top_store_own_address() {
    assert!(held(Q2_TOP_STORE, "f::p"));
}

/// The wider R1 sentence, a measurement only: under it 2.3's byte pointer to the
/// program's own global is premised away.
#[test]
fn e5c_hold_r1_wide_premises_away_2_3() {
    let v = verdicts_opts(
        Q3_OWN_GLOBAL,
        &[],
        Options {
            program_bytes_disjoint: true,
            ..Options::default()
        },
    );
    assert!(!of(&v, "entry::p").withdraws(), "{v:#?}");
}

// ---- The stand-in round-4 review (era-5c 141 §4; Codex was out of quota): each a RED
// ---- witness, ignored until its fix lands.

/// H1: a member against an outside object of the container's type.
const H1_MEMBER_CONTAINER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct S { pub x: i32, pub y: i32 }
#[repr(C)] pub struct H { pub s: *mut S }
extern "C" { fn give(p: *mut S); }
pub unsafe fn f(h: *mut H) -> i32 {
    let mut s = S { x: 0, y: 0 };
    give(&mut s);
    let p: *mut i32 = &raw mut s.x;
    let r = *p;
    *(*h).s = S { x: 1, y: 1 };
    r ^ *p
}
"#;

/// H2: memcpy between objects of two struct types.
const H2_CROSS_COPY: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct A { pub p: *mut i32 }
#[repr(C)] pub struct B { pub q: *mut i32 }
pub unsafe fn f() -> i32 {
    let mut x = 0;
    let mut a = A { p: &raw mut x };
    let mut b = B { q: core::ptr::null_mut() };
    memcpy(&raw mut b as *mut core::ffi::c_void, &raw mut a as *const core::ffi::c_void, 8);
    let p: *mut i32 = &raw mut x;
    let r = *p;
    *b.q = 1;
    r ^ *p
}
"#;

/// H3: a member's byte view stored, then moved back after the load.
const H3_STORED_VIEW: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct Node { pub key: i32, pub pad: i32, pub link: *mut Node }
#[repr(C)] pub struct H { pub head: *mut u8 }
unsafe fn back(k: *mut i32, h: *mut H) -> i32 { let a = *k; *((*h).head.offset(-8) as *mut i32) = 1; a ^ *k }
pub unsafe fn entry() {
    let mut n = Node { key: 0, pad: 0, link: core::ptr::null_mut() };
    let mut h = H { head: &raw mut n.link as *mut u8 };
    back(&raw mut n.key, &mut h);
}
"#;

/// H4: a callback the program also calls itself, handed to an unlisted function.
const H4_CALLED_CALLBACK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
extern "C" { fn run(f: Option<unsafe extern "C" fn(*mut i32) -> i32>, a: *mut i32) -> i32; }
static mut SHARED: i32 = 0;
static mut G: *mut i32 = core::ptr::null_mut();
unsafe extern "C" fn work(p: *mut i32) -> i32 { let r = *p; *G = 1; r ^ *p }
pub unsafe fn entry() -> i32 {
    G = &raw mut SHARED;
    let mut own = 0;
    work(&raw mut own);
    run(Some(work), &raw mut SHARED)
}
"#;

/// H6: a formal stored inside an aggregate, and the one store contract (`strtoul`).
const H6_AGGREGATE_STORE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct G { pub px: *mut i32 }
pub unsafe fn keep(g: *mut G, x: *mut i32) { *g = G { px: x }; }
"#;
const H6_STRTOUL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn strtoul(s: *const i8, e: *mut *mut i8, b: i32) -> u64; }
pub unsafe fn parse(s: *const i8, end: *mut *mut i8) -> u64 { strtoul(s, end, 10) }
"#;

/// H7: pointer bytes memcpy'd into a field, read as an integer, copied back.
const H7_FIELD_BYTES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" { fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct Spill { pub bits: u64 }
pub unsafe fn f() -> i32 {
    let mut x = 0;
    let mut src: *mut i32 = &raw mut x;
    let mut q: *mut i32 = core::ptr::null_mut();
    let mut s = Spill { bits: 0 };
    memcpy(&raw mut s.bits as *mut core::ffi::c_void, &raw mut src as *const core::ffi::c_void, 8);
    let mut c: u64 = s.bits;
    memcpy(&raw mut q as *mut core::ffi::c_void, &raw mut c as *const core::ffi::c_void, 8);
    let p: *mut i32 = &raw mut x;
    let r = *p;
    *q = 1;
    r ^ *p
}
"#;

#[test]
fn e5c_hold_red4_h1_member_container() {
    assert!(held(H1_MEMBER_CONTAINER, "f::p"));
}
#[test]
fn e5c_hold_fault_containers() {
    assert!(
        !held_faulted(H1_MEMBER_CONTAINER, "f::p", Rule::Containers),
        "the fault is caught"
    );
}
#[test]
fn e5c_hold_red4_h2_cross_copy() {
    assert!(held(H2_CROSS_COPY, "f::p"));
}
#[test]
fn e5c_hold_fault_cross_copy() {
    assert!(
        !held_faulted(H2_CROSS_COPY, "f::p", Rule::CrossCopy),
        "the fault is caught"
    );
}
#[test]
fn e5c_hold_red4_h3_stored_view() {
    assert!(held(H3_STORED_VIEW, "back::k"));
}
#[test]
fn e5c_hold_fault_view_values() {
    assert!(
        !held_faulted(H3_STORED_VIEW, "back::k", Rule::ViewValues),
        "H3"
    );
}
#[test]
fn e5c_hold_red4_h4_called_callback() {
    assert!(held(H4_CALLED_CALLBACK, "work::p"));
}
#[test]
fn e5c_hold_fault_callbacks() {
    assert!(
        !held_faulted(H4_CALLED_CALLBACK, "work::p", Rule::Callbacks),
        "H4"
    );
}
#[test]
fn e5c_hold_red4_h6_aggregate_store() {
    assert!(held(H6_AGGREGATE_STORE, "keep::x"));
}
#[test]
fn e5c_hold_red4_h6_strtoul() {
    assert!(held(H6_STRTOUL, "parse::s"));
}
#[test]
fn e5c_hold_red4_h7_field_bytes() {
    assert!(held(H7_FIELD_BYTES, "f::p"));
}
#[test]
fn e5c_hold_fault_int_local_memory() {
    assert!(
        !held_faulted(H7_FIELD_BYTES, "f::p", Rule::IntLocalMemory),
        "H7"
    );
    assert!(
        !held_faulted(T6_INT_COPY, "f::p", Rule::IntLocalMemory),
        "3.6"
    );
}

/// The void cast (relay 176): a member's address through `void *` back to its own type is
/// the member, so a retained write to a sibling member does not reach it; cast to the
/// container's type it is the whole object.
const VOID_CAST: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct I { pub x: i32 }
#[repr(C)] pub struct O { pub i: I, pub y: i32, pub py: *mut i32 }
unsafe fn own(p: *mut I, o: *mut O) -> i32 { let a = (*p).x; *(*o).py = 1; a ^ (*p).x }
unsafe fn whole(q: *mut O, o: *mut O) -> i32 { let a = (*q).y; *(*o).py = 1; a ^ (*q).y }
pub unsafe fn entry() {
    let mut o = O { i: I { x: 0 }, y: 0, py: core::ptr::null_mut() };
    o.py = &raw mut o.y;
    let v = &raw mut o.i as *mut core::ffi::c_void;
    own(v as *mut I, &mut o);
    whole(v as *mut O, &mut o);
}
"#;

#[test]
fn e5c_hold_void_cast_keeps_the_member() {
    let v = verdicts(VOID_CAST);
    assert_eq!(of(&v, "own::p"), &Verdict::Clear, "{v:#?}");
    assert!(writes(of(&v, "whole::q")), "{v:#?}");
}

#[test]
fn e5c_hold_fault_void_cast() {
    assert!(
        held_faulted(VOID_CAST, "own::p", Rule::VoidCast),
        "the fault is caught"
    );
}

/// H6 (c): a formal handed to a callee that stores it.
const H6_CALLEE_STORE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct G { pub px: *mut i32 }
unsafe fn keep(g: *mut G, x: *mut i32) { (*g).px = x; }
pub unsafe fn pass(g: *mut G, y: *mut i32) { keep(g, y); }
"#;

#[test]
fn e5c_hold_h6_callee_store() {
    assert!(held(H6_CALLEE_STORE, "pass::y"));
}

#[test]
fn e5c_hold_fault_wide_stores() {
    assert!(
        !held_faulted(H6_AGGREGATE_STORE, "keep::x", Rule::WideStores),
        "(a)"
    );
    assert!(
        !held_faulted(H6_STRTOUL, "parse::s", Rule::WideStores),
        "(b)"
    );
    assert!(
        !held_faulted(H6_CALLEE_STORE, "pass::y", Rule::WideStores),
        "(c)"
    );
}

/// H5: glob's error callback passed as c2rust does, `Some(err)` through a local.
const H5_GLOB_SOME: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
#[repr(C)] pub struct glob_t { pub gl_pathc: u64, pub gl_pathv: *mut *mut i8, pub gl_offs: u64 }
extern "C" {
    fn glob(p: *const i8, flags: i32, errfunc: Option<unsafe extern "C" fn(*const i8, i32) -> i32>, g: *mut glob_t) -> i32;
}
static mut G: *mut i32 = core::ptr::null_mut();
unsafe extern "C" fn err(_: *const i8, _: i32) -> i32 { *G = 1; 0 }
pub unsafe fn f() -> i32 {
    let mut x = 0;
    G = &raw mut x;
    let mut g = glob_t { gl_pathc: 0, gl_pathv: core::ptr::null_mut(), gl_offs: 0 };
    let p: *mut i32 = &raw mut x;
    let r = *p;
    let cb: Option<unsafe extern "C" fn(*const i8, i32) -> i32> = Some(err);
    glob(b"*\0".as_ptr() as *const i8, 0, cb, &mut g);
    r ^ *p
}
"#;

#[test]
fn e5c_hold_h5_glob_some() {
    assert!(held(H5_GLOB_SOME, "f::p"));
}

#[test]
fn e5c_hold_fault_callbacks_h5() {
    assert!(!held_faulted(H5_GLOB_SOME, "f::p", Rule::Callbacks), "H5");
}

/// P8's receipt (relay 176): a subject Clear only under the premise carries it; a subject
/// clear without the premise does not.
fn premises(code: &str) -> FxHashMap<String, Option<&'static str>> {
    let mut out = FxHashMap::default();
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = program_of(tcx);
        let check =
            RetainedAccessCheck::compute_options(&program, &|_, _| true, Options::default());
        for &f in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            let fn_name = tcx.item_name(f.to_def_id());
            for info in &body.var_debug_info {
                let rustc_middle::mir::VarDebugInfoContents::Place(place) = info.value else {
                    continue;
                };
                if place.projection.is_empty() {
                    out.insert(
                        format!("{fn_name}::{}", info.name),
                        check.premise(f, place.local),
                    );
                }
            }
        }
    })
    .expect("compiles");
    out
}

#[test]
fn e5c_hold_p8_receipt() {
    assert_eq!(
        premises(R1_BYTE_ALIAS)["f::x"],
        Some("premise=outside-byte-view")
    );
    assert_eq!(premises(MEMBERS)["step::br"], None);
}

/// M1: a pointer printed with `%p` and read back with `sscanf` in the same run.
const M1_ROUND_TRIP: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" {
    fn sprintf(s: *mut i8, f: *const i8, ...) -> i32;
    fn sscanf(s: *const i8, f: *const i8, ...) -> i32;
}
pub unsafe fn f() -> i32 {
    let mut x = 0;
    let mut buf: [i8; 32] = [0; 32];
    let mut q: *mut i32 = core::ptr::null_mut();
    sprintf(buf.as_mut_ptr(), b"%p\0".as_ptr() as *const i8, &raw mut x);
    sscanf(buf.as_ptr(), b"%p\0".as_ptr() as *const i8, &raw mut q);
    let p: *mut i32 = &raw mut x;
    let r = *p;
    *q = 1;
    r ^ *p
}
"#;

/// M2: a handler registered with the library runs at `exit`.
const M2_ATEXIT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
extern "C" { fn atexit(f: Option<unsafe extern "C" fn()>) -> i32; fn exit(c: i32) -> !; }
static mut G: *mut i32 = core::ptr::null_mut();
unsafe extern "C" fn bye() { *G = 1; }
unsafe fn f(p: *mut i32) { let _ = *p; exit(0); }
pub unsafe fn entry() { let mut x = 0; G = &raw mut x; atexit(Some(bye)); f(&raw mut x); }
"#;

#[test]
fn e5c_hold_m1_round_trip() {
    assert!(held(M1_ROUND_TRIP, "f::p"));
    assert!(
        !held_faulted(M1_ROUND_TRIP, "f::p", Rule::RoundTrip),
        "the fault is caught"
    );
}

#[test]
fn e5c_hold_m2_atexit() {
    assert!(held(M2_ATEXIT, "f::p"));
}

/// §3 (ii) of 142a, the measurement mode: by types, brotli's `br` meets the state's
/// `u16` write only if the types may alias; they do not, so it stays Clear; the whole
/// state holds.
#[test]
fn e5c_hold_by_types_mode() {
    let v = verdicts_opts(
        MEMBERS,
        &[],
        Options {
            by_types: true,
            ..Options::default()
        },
    );
    assert_eq!(of(&v, "step::br"), &Verdict::Clear, "{v:#?}");
    assert!(writes(of(&v, "whole::s")), "{v:#?}");
}

// ---- Round 5 (stand-in, era-5c 142a §3): the two new classes as RED witnesses, ignored.

/// N1: direct self-recursion -- a nested frame's write in a branch where the outer local
/// is dead.
const N1_SELF_RECURSION: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct H { pub q: *mut i32, pub x: i32 }
unsafe fn walk(h: *mut H, n: i32) -> i32 {
    if n == 0 { *(*h).q = 1; return 0; }
    let p: *mut i32 = &raw mut (*h).x;
    let r = *p;
    walk(h, n - 1);
    r ^ *p
}
pub unsafe fn entry() -> i32 { let mut h = H { q: core::ptr::null_mut(), x: 0 }; h.q = &raw mut h.x; walk(&mut h, 1) }
"#;

/// N2: glob writes library pointers into the program's `glob_t`.
const N2_GLOB_WRITEBACK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct glob_t { pub gl_pathc: u64, pub gl_pathv: *mut *mut i8, pub gl_offs: u64 }
extern "C" {
    fn glob(p: *const i8, flags: i32, errfunc: Option<unsafe extern "C" fn(*const i8, i32) -> i32>, g: *mut glob_t) -> i32;
}
pub unsafe fn f() -> i32 {
    let mut g = glob_t { gl_pathc: 0, gl_pathv: core::ptr::null_mut(), gl_offs: 0 };
    if glob(b"*\0".as_ptr() as *const i8, 0, None, &mut g) != 0 || g.gl_pathc == 0 { return 0; }
    let p: *mut *mut i8 = g.gl_pathv;
    let a = *p;
    *g.gl_pathv = core::ptr::null_mut();
    (a == *p) as i32
}
"#;

#[test]
#[ignore = "RED: stand-in round 5, N1 (era-5c 142a §3)"]
fn e5c_hold_red5_n1_self_recursion() {
    assert!(held(N1_SELF_RECURSION, "walk::p"));
}

#[test]
#[ignore = "RED: stand-in round 5, N2 (era-5c 142a §3)"]
fn e5c_hold_red5_n2_glob_writeback() {
    assert!(held(N2_GLOB_WRITEBACK, "f::p"));
}

/// R816-1, the closed world: an entry's two arguments are distinct objects, but the
/// program's own aliasing through memory reached from one argument still holds.
const CLOSED_WORLD: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct H { pub p: *mut i32 }
pub unsafe fn two(x: *mut i32, h: *mut H) -> i32 { let a = *x; *(*h).p = 1; a ^ *x }
pub unsafe fn own(h: *mut H) -> i32 { let x: *mut i32 = (*h).p; let a = *x; *(*h).p = 1; a ^ *x }
"#;

#[test]
fn e5c_hold_closed_world() {
    let v = verdicts_opts(
        CLOSED_WORLD,
        &[],
        Options {
            closed: true,
            ..Options::default()
        },
    );
    assert_eq!(of(&v, "two::x"), &Verdict::Clear, "{v:#?}");
    assert!(writes(of(&v, "own::x")), "{v:#?}");
    let open = verdicts(CLOSED_WORLD);
    assert!(
        writes(of(&open, "two::x")),
        "the open world holds it: {open:#?}"
    );
}

/// Relay 179: what N1 and N2 cost to close under (T). N2 is held by (T) as it is (an
/// access counts by its type with no object known); N1 needs its extent closure.
#[test]
fn e5c_hold_n1_n2_under_types() {
    let types = Options {
        by_types: true,
        closed: true,
        ..Options::default()
    };
    let n2 = verdicts_opts(N2_GLOB_WRITEBACK, &[], types);
    assert!(of(&n2, "f::p").withdraws(), "N2 under (T): {n2:#?}");
    let n1 = verdicts_opts(N1_SELF_RECURSION, &[], types);
    assert_eq!(
        of(&n1, "walk::p"),
        &Verdict::Clear,
        "N1 under (T) without its closure"
    );
    let closed_n1 = verdicts_opts(
        N1_SELF_RECURSION,
        &[],
        Options {
            close_n1: true,
            ..types
        },
    );
    assert!(
        of(&closed_n1, "walk::p").withdraws(),
        "N1 under (T) with its closure"
    );
    let closed_n2 = verdicts_opts(
        N2_GLOB_WRITEBACK,
        &[],
        Options {
            close_n2: true,
            ..Options::default()
        },
    );
    assert!(
        of(&closed_n2, "f::p").withdraws(),
        "N2 under (P) with its closure"
    );
}

// ---- The check of record (R826-1, relay 182): (E) in the closed world, M1 off. Each
// ---- evident shape holds, with its census receipt; what is not evident is P9's.

fn of_record(code: &str) -> FxHashMap<String, Verdict> {
    verdicts_opts(code, &[], Options::of_record())
}

#[test]
#[ignore = "era-5c 145 H3: both W1 entries are uncalled, so in the closed world the client's object is two fresh objects; the user's answer to H3 decides"]
fn e5c_evident_record_holds_the_cycle() {
    let v = of_record(W1_STREAM);
    let receipt = of(&v, "handle_compress::strm").evident_receipt();
    assert!(
        receipt
            .as_deref()
            .is_some_and(|r| r.starts_with("evident:cycle:")),
        "{receipt:?}"
    );
}

#[test]
#[ignore = "era-5c 145 H3: as above, for W2's init and append"]
fn e5c_evident_record_holds_the_self_reference() {
    let v = of_record(W2_SELF);
    let receipt = of(&v, "append::v").evident_receipt();
    assert!(
        receipt
            .as_deref()
            .is_some_and(|r| r.starts_with("evident:self-reference:small_vec.p")),
        "{receipt:?}"
    );
}

#[test]
fn e5c_evident_record_holds_the_derived_store() {
    let v = of_record(DERIVED);
    let receipt = of(&v, "keep::x").evident_receipt();
    assert!(
        receipt
            .as_deref()
            .is_some_and(|r| r.starts_with("evident:derived-store:")),
        "{receipt:?}"
    );
}

/// What is not an evident shape is not held: P9 stands for it.
#[test]
fn e5c_evident_record_leaves_the_rest_to_p9() {
    let v = of_record(CLOSED_WORLD);
    assert_eq!(of(&v, "own::x"), &Verdict::Clear, "{v:#?}");
    assert_eq!(of(&v, "two::x"), &Verdict::Clear, "{v:#?}");
}

// ---- The review of (E)'s rules (era-5c 145, the stand-in, R820-2): missed holds inside
// ---- the evident shapes, as RED witnesses under the mode of record, ignored until fixed.

/// H1: `Top` in the subject erases a self-reference hold (Unknown is dropped by (E)).
const EH1_TOP_SUBJECT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct small_vec { pub p: *mut u64, pub n: usize, pub buf: [u64; 16] }
unsafe fn init(v: *mut small_vec) { (*v).p = (*v).buf.as_mut_ptr(); }
unsafe fn f(x: *mut u64, v: *mut small_vec) -> u64 { let a = *x; *(*v).p = 1; a ^ *x }
pub unsafe fn entry() -> u64 {
    let mut v = small_vec { p: core::ptr::null_mut(), n: 0, buf: [0; 16] };
    init(&mut v);
    let x = (v.buf.as_mut_ptr() as usize) as *mut u64;
    f(x, &mut v)
}
"#;

/// H2: E1 for a local -- a callee stores it.
const EH2_LOCAL_CALLEE_STORE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct L { pub head: *mut i32 }
unsafe fn push(l: *mut L, x: *mut i32) { (*l).head = x; }
unsafe fn bump(l: *mut L) { *(*l).head += 1; }
pub unsafe fn f(l: *mut L) -> i32 {
    let mut v = 0;
    let p: *mut i32 = &mut v as *mut i32;
    push(l, p);
    let a = *p;
    bump(l);
    a ^ *p
}
"#;

/// H4: a stack struct's self store (no dereference on the left).
const EH4_STACK_SELF: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] pub struct H { pub q: *mut i32, pub x: i32 }
unsafe fn f(p: *mut i32, h: *mut H) -> i32 { let a = *p; *(*h).q = 1; a ^ *p }
pub unsafe fn entry() -> i32 {
    let mut h = H { q: core::ptr::null_mut(), x: 0 };
    h.q = &mut h.x as *mut i32;
    f(&mut h.x as *mut i32, &mut h as *mut H)
}
"#;

/// H5 (round 5's F2): a formal carried in an aggregate to a callee that stores it.
const EH5_AGGREGATE_TO_CALLEE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
#[repr(C)] #[derive(Clone, Copy)] pub struct S { pub p: *mut i32 }
#[repr(C)] pub struct G { pub px: *mut i32 }
unsafe fn put(g: *mut G, s: S) { (*g).px = s.p; }
pub unsafe fn keep(g: *mut G, x: *mut i32) { put(g, S { p: x }); }
"#;

#[test]
fn e5c_evident_red_h1_top_subject() {
    assert!(of_record(EH1_TOP_SUBJECT)["f::x"].withdraws());
}
#[test]
fn e5c_evident_red_h2_local_callee_store() {
    assert!(of_record(EH2_LOCAL_CALLEE_STORE)["f::p"].withdraws());
}
#[test]
fn e5c_evident_red_h4_stack_self() {
    assert!(of_record(EH4_STACK_SELF)["f::p"].withdraws());
}
#[test]
fn e5c_evident_red_h5_aggregate_to_callee() {
    assert!(of_record(EH5_AGGREGATE_TO_CALLEE)["keep::x"].withdraws());
}
#[test]
fn e5c_evident_red_n1_self_recursion() {
    assert!(of_record(N1_SELF_RECURSION)["walk::p"].withdraws());
}

/// Each fix's fault (era-5c 145): the witness clears without it.
#[test]
fn e5c_evident_faults() {
    let faulted = |code: &str, subject: &str, rule: Rule| {
        verdicts_opts(
            code,
            &[],
            Options {
                fault: Some(rule),
                ..Options::of_record()
            },
        )[subject]
            .withdraws()
    };
    assert!(
        !faulted(EH1_TOP_SUBJECT, "f::x", Rule::EvidentUnknown),
        "H1"
    );
    assert!(
        !faulted(EH2_LOCAL_CALLEE_STORE, "f::p", Rule::LocalWideStores),
        "H2"
    );
    assert!(!faulted(EH4_STACK_SELF, "f::p", Rule::SelfStores), "H4");
    assert!(
        !faulted(EH5_AGGREGATE_TO_CALLEE, "keep::x", Rule::WideStores),
        "H5"
    );
    assert!(
        !verdicts_opts(
            N1_SELF_RECURSION,
            &[],
            Options {
                close_n1: false,
                ..Options::of_record()
            }
        )["walk::p"]
            .withdraws(),
        "N1"
    );
}

// ---- The review of (E), round 2: Codex (2026-10-05, at 5bb6cc7d1). Variants of round 1's
// ---- classes the fixes do not cover, as RED witnesses under the mode of record.

const CX_AGG: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
#[repr(C)] struct A { q: *mut i32 }
static mut G: *mut i32 = 0 as *mut i32;
unsafe fn keep(q: *mut i32) { G = q; }
pub unsafe fn f(p: *mut i32) {
    let a = A { q: p }; let q = a.q;
    keep(q); *G = 1; *p = 2;
}
"#;

const CX_REC: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
#[repr(C)] struct H { x: i32, q: *mut i32 }
static mut G: *mut i32 = 0 as *mut i32;
unsafe fn rec(n: u32) {
    let p = G; *p = 1;
    if n > 0 { rec(n - 1); }
    *p = 2;
}
pub unsafe fn run() {
    let mut h = H { x: 0, q: 0 as *mut i32 };
    h.q = &raw mut h.x; G = h.q; rec(1);
}
"#;

const CX_TOP: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
#[repr(C)] struct H { x: i32, q: *mut i32 }
unsafe fn f(p: *mut H) {
    let bits = (*p).q as usize;
    let r = bits as *mut i32;
    *r = 1; (*p).x = 2;
}
pub unsafe fn run() {
    let mut h = H { x: 0, q: 0 as *mut i32 };
    h.q = &raw mut h.x; f(&raw mut h);
}
"#;

const CX_SLOT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
#[repr(C)] struct H { x: i32, q: *mut i32 }
unsafe fn f(p: *mut H) {
    let q = (*p).q; *q = 1; (*p).x = 2;
}
pub unsafe fn run() {
    let mut h = H { x: 0, q: 0 as *mut i32 };
    let slot = &raw mut h.q;
    *slot = &raw mut h.x;
    f(&raw mut h);
}
"#;

const CX_RAW: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, static_mut_refs)]
#[repr(C)] struct H { x: i32, q: *mut i32 }
pub unsafe fn f(p: *mut H, g: *mut H) {
    (*g).q = &raw mut (*p).x;
    *(*g).q = 1;
    (*p).x = 2;
}
"#;

#[test]
#[ignore = "RED: era-5c 145a, Codex round 2, AGG"]
fn e5c_evident_red_cx_agg() {
    assert!(of_record(CX_AGG)["f::p"].withdraws());
}
#[test]
#[ignore = "RED: era-5c 145a, Codex round 2, REC"]
fn e5c_evident_red_cx_rec() {
    assert!(of_record(CX_REC)["rec::p"].withdraws());
}
#[test]
#[ignore = "RED: era-5c 145a, Codex round 2, TOP"]
fn e5c_evident_red_cx_top() {
    assert!(of_record(CX_TOP)["f::p"].withdraws());
}
#[test]
#[ignore = "RED: era-5c 145a, Codex round 2, SLOT"]
fn e5c_evident_red_cx_slot() {
    assert!(of_record(CX_SLOT)["f::p"].withdraws());
}
#[test]
#[ignore = "RED: era-5c 145a, Codex round 2, RAW"]
fn e5c_evident_red_cx_raw() {
    assert!(of_record(CX_RAW)["f::p"].withdraws());
}
