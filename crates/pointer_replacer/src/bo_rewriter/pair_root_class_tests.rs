//! wave-6p R619-4 (1): every pair certificate is receipted with the root class
//! of each side — `entry` (a pointer parameter of the calling function, or a
//! place inside its pointee), `internal` (storage the program made) or `other`
//! (no known root) — lower argument index first, so a `type-rule` certificate
//! reads as entry / entry, entry / internal or internal / internal.

use super::decision::pair_disjointness::PairDisjointnessIndex;

fn family(src: &str, caller: &str, callee: &str, left: usize, right: usize) -> &'static str {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = PairDisjointnessIndex::derive(&program, &mut_facts, None);
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        out = Some(index.certificate_family_recorded(
            function(caller),
            function(callee),
            left,
            right,
        ));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

/// `bs` is stored only by `malloc`, so `(*q).bs` is an admitted field's block;
/// `ext()` is foreign, so its result has no known root.
const SIDES: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, static_mut_refs)]
extern "C" {
    fn malloc(n: libc::c_ulong) -> *mut libc::c_void;
    fn ext() -> *mut B;
}
#[repr(C)]
pub struct A { pub x: i32 }
#[repr(C)]
pub struct B { pub y: i64 }
#[repr(C)]
pub struct Q { pub bs: *mut B }
pub static mut GA: A = A { x: 0 };
pub unsafe fn InitQ(mut q: *mut Q) {
    (*q).bs = malloc(8) as *mut B;
}
pub unsafe fn Put(mut a: *mut A, mut b: *mut B) {
    (*a).x = 1;
    (*b).y = 2;
}
pub unsafe fn EntryInternal(mut p: *mut A, mut q: *mut Q) {
    Put(p, (*q).bs);
}
pub unsafe fn EntryEntry(mut p: *mut A, mut r: *mut B) {
    Put(p, r);
}
pub unsafe fn InternalInternal(mut q: *mut Q) {
    Put(&mut GA, (*q).bs);
}
pub unsafe fn EntryOther(mut p: *mut A) {
    let mut u = ext();
    Put(p, u);
}
"#;

#[test]
fn w6p_r619_the_receipt_names_each_sides_root_class() {
    for (caller, roots) in [
        ("EntryInternal", "entry/internal"),
        ("EntryEntry", "entry/entry"),
        ("InternalInternal", "internal/internal"),
        ("EntryOther", "entry/other"),
    ] {
        assert_eq!(
            family(SIDES, caller, "Put", 0, 1),
            format!("pair-disjointness-certificate:roots={roots}"),
            "{caller}"
        );
    }
}

#[test]
fn w6p_r619_the_roots_are_in_argument_index_order() {
    assert_eq!(
        family(SIDES, "EntryInternal", "Put", 1, 0),
        "pair-disjointness-certificate:roots=entry/internal",
        "the receipt's pair is canonical, lower argument first, and so are its roots"
    );
}
