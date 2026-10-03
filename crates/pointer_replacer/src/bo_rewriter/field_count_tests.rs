//! **R763-2 — wave-4 build 2: `len-field-count`.** A pointer field whose
//! element count is a sibling field, proven from every write of the pair.
//!
//! `W4FC-1` / `W4FC-2` are the RED witnesses: genann's shape (the offset
//! witness, at the declaration planner) and ht's (the allocation, at the
//! seam's raw-argument arm). Each emitted `FALLBACK_SLICE_EXTENT` at
//! `d5d115ddb`.

const PRE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments)]\n\
extern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void; }\n";

fn emitted(src: &str) -> String {
    match super::rewrite_m1(src) {
        super::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("fixture must survive production verify: {other:?}"),
    }
}

fn flat(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// genann's shape: `weight` points into the struct's own allocation and the
/// initializer computes `output = weight.offset(total)` — the offset witness.
const GENANN: &str = "pub struct Ann { pub total: i32, pub weight: *mut f64, pub output: *mut f64 }\n\
pub unsafe fn init(n: i32) -> *mut Ann {\n\
    let ret = malloc(core::mem::size_of::<Ann>() + core::mem::size_of::<f64>() * (2 * n as usize)) as *mut Ann;\n\
    (*ret).total = n;\n\
    let ref mut fresh0 = (*ret).weight;\n\
    *fresh0 = (ret as *mut u8).offset(core::mem::size_of::<Ann>() as isize) as *mut f64;\n\
    let ref mut fresh1 = (*ret).output;\n\
    *fresh1 = ((*ret).weight).offset((*ret).total as isize);\n\
    ret\n\
}\n\
pub unsafe fn run(ann: *const Ann) -> f64 {\n\
    let mut w: *const f64 = (*ann).weight;\n\
    let mut s = 0.0; let mut i: i32 = 0;\n\
    while i < (*ann).total { s += *w.offset(i as isize); i += 1; }\n\
    s\n\
}\n";

/// ht's shape: `entries` is `calloc(capacity, ..)` in `create` and the
/// expansion, and `set` passes the field beside its count.
const HT: &str = "pub struct Entry { pub key: *const i8, pub value: *mut core::ffi::c_void }\n\
pub struct Ht { pub entries: *mut Entry, pub capacity: usize, pub length: usize }\n\
pub unsafe fn create() -> *mut Ht {\n\
    let table = malloc(core::mem::size_of::<Ht>()) as *mut Ht;\n\
    (*table).length = 0;\n\
    (*table).capacity = 16;\n\
    let ref mut fresh0 = (*table).entries;\n\
    *fresh0 = calloc((*table).capacity, core::mem::size_of::<Entry>()) as *mut Entry;\n\
    table\n\
}\n\
unsafe fn set_entry(entries: *mut Entry, capacity: usize, h: usize) {\n\
    let mut index = h & capacity.wrapping_sub(1);\n\
    while !((*entries.offset(index as isize)).key).is_null() {\n\
        index = index.wrapping_add(1);\n\
        if index >= capacity { index = 0; }\n\
    }\n\
    (*entries.offset(index as isize)).value = 0 as *mut core::ffi::c_void;\n\
}\n\
pub unsafe fn expand(table: *mut Ht) {\n\
    let new_capacity = ((*table).capacity).wrapping_mul(2);\n\
    let new_entries = calloc(new_capacity, core::mem::size_of::<Entry>()) as *mut Entry;\n\
    let ref mut fresh4 = (*table).entries;\n\
    *fresh4 = new_entries;\n\
    (*table).capacity = new_capacity;\n\
}\n\
pub unsafe fn set(table: *mut Ht, h: usize, k: isize) {\n\
    set_entry((*table).entries, (*table).capacity, h)\n\
}\n";

/// **W4FC-1 — the offset witness, at the declaration planner.** `run`'s `w`
/// is read under a loop on `(*ann).total` (a field, so no callee bound), and
/// the pair `weight`/`total` is established by `init`'s offset witness.
#[test]
fn w4fc_1_an_offset_witness_sizes_a_field_by_its_sibling() {
    let out = flat(&emitted(&format!("{PRE}{GENANN}")));
    assert!(
        out.contains("from_raw_parts((*ann).weight, ((*ann).total) as usize)"),
        "{out}"
    );
}

/// **W4FC-2 — the allocation, at the seam.** `entries` is allocated with
/// `capacity` elements wherever it is written, so `set`'s raw argument takes
/// `(*table).capacity`.
#[test]
fn w4fc_2_an_allocation_sizes_a_field_passed_beside_its_count() {
    let out = flat(&emitted(&format!("{PRE}{HT}")));
    assert!(
        out.contains("from_raw_parts_mut((*table).entries, ((*table).capacity) as usize)"),
        "{out}"
    );
}
