//! wave-6p R583-5 (G3): the fresh-field admission reads EVERY body the program
//! owns, not only its functions.
//!
//! R479-4a admits a pointer field when every store into it is null or a
//! directly called allocator, and a struct literal counts as a store of each
//! field it names. The scan walked `program.functions` only, so a literal in a
//! `static` or `const` initializer was never read. A self-referential static —
//! the sentinel list head, `Node { next: &raw mut SENTINEL }` — then puts the
//! base object into its own field, and the rule certifies `n` beside
//! `(*n).next` distinct when both name `SENTINEL`.

use super::decision::pair_disjointness::{CertificateKind, PairDisjointnessIndex, Unproved};

fn verdict(
    src: &str,
    caller: &str,
    callee: &str,
    left: usize,
    right: usize,
) -> Result<CertificateKind, Unproved> {
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
        out = Some(index.certify_recorded(function(caller), function(callee), left, right));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

/// The program's only FUNCTION store into `next` is `malloc`, which alone
/// would admit the field. `Use2` takes two formals of one type, so the type
/// rule refuses `same-type` and the root rule is the one under test.
const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, static_mut_refs)]
extern "C" { fn malloc(n: libc::c_ulong) -> *mut libc::c_void; }
#[repr(C)]
pub struct Node { pub next: *mut Node, pub v: i32 }
pub unsafe fn Grow(mut n: *mut Node) {
    (*n).next = malloc(16) as *mut Node;
}
pub unsafe fn Use2(mut a: *mut Node, mut b: *mut Node) {
    (*a).v = 1;
    (*b).v = 2;
}
pub unsafe fn Walk(mut n: *mut Node) {
    Use2(n, (*n).next);
}
"#;

/// W1: the sentinel. `SENTINEL.next` IS `SENTINEL`.
const SELF_REFERENTIAL_STATIC: &str = r#"
pub static mut SENTINEL: Node = Node { next: &raw mut SENTINEL, v: 0 };
"#;

/// W2: a `const` initializer is a body the scan never read either; an address
/// made from an integer is no allocation.
const CONST_WITH_A_FORGED_POINTER: &str = r#"
pub const FORGED: Node = Node { next: 16 as *mut Node, v: 0 };
"#;

/// C1: a static literal whose pointer field is null stores nothing that
/// breaks the claim, so the field stays admitted.
const STATIC_WITH_A_NULL_FIELD: &str = r#"
pub static mut EMPTY: Node = Node { next: 0 as *mut Node, v: 0 };
"#;

fn source(extra: &str) -> String {
    format!("{PRELUDE}{extra}")
}

#[test]
fn w6p_a_self_referential_static_literal_refuses_the_field() {
    let verdict = verdict(&source(SELF_REFERENTIAL_STATIC), "Walk", "Use2", 0, 1);
    assert!(
        verdict.is_err(),
        "`SENTINEL.next` is `SENTINEL`, so `n` and `(*n).next` may be one object: got {verdict:?}"
    );
}

#[test]
fn w6p_a_const_literal_with_a_forged_pointer_refuses_the_field() {
    let verdict = verdict(&source(CONST_WITH_A_FORGED_POINTER), "Walk", "Use2", 0, 1);
    assert!(
        verdict.is_err(),
        "a const initializer stores an address no allocator returned: got {verdict:?}"
    );
}

#[test]
fn w6p_a_null_field_in_a_static_literal_keeps_the_admission() {
    assert_eq!(
        verdict(&source(STATIC_WITH_A_NULL_FIELD), "Walk", "Use2", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "a null store keeps `next` holding null or a block `malloc` returned"
    );
}
