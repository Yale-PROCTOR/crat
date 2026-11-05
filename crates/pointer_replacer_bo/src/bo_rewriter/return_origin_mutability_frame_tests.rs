//! **R586-2 (main 118) — the sole-origin mutability rule, read on avl's own frame.**
//!
//! The corpus hold is gate 2 of avl's `minValueNode` wall
//! (`dropped-site:seam-shared-to-mut`), and only the L01⁹ model reaches it:
//! `node` decides `ref`, the return keeps the exported `*mut`. A fixture stops at
//! gate 1 (`escapes-via-return`), so the witness reads avl's substrate under the
//! frame's accepted model through the census's one-iteration instrument, with no
//! solve. Run by hand, never by the suite: `CRAT_R586_PROGRAM=<…/rs-crown-derived/
//! avl/lib.rs>` with the L01⁹ frame's env (`l01p9-extra-env.sh`) on a head
//! carrying the L01⁹ analyses.

/// The rule's shape in a one-file crate: an exported function that reads
/// through its one formal and returns it.
const R586_SHAPE: &str = r#"
#[repr(C)]
pub struct Node {
    pub key: i32,
}
#[no_mangle]
pub unsafe extern "C" fn first(mut node: *mut Node) -> *mut Node {
    let _k = (*node).key;
    return node;
}
"#;

/// An in-program caller whose argument is only read: it decides shared.
const R586_CALLER: &str = r#"
pub unsafe fn peek(mut n: *mut Node) -> i32 {
    let mut m = first(n);
    return (*m).key;
}
"#;

/// Two formals, one returned: `a` is the sole origin, `b` is only read.
const R586_TWO_FORMALS: &str = r#"
#[repr(C)]
pub struct Node {
    pub key: i32,
}
#[no_mangle]
pub unsafe extern "C" fn pick(mut a: *mut Node, mut b: *mut Node) -> *mut Node {
    let _k = (*a).key + (*b).key;
    return a;
}
"#;

/// The fixture's receipts, under the crate-wide frame lock (no model override
/// may leak in from a concurrent test).
fn fixture(src: &str) -> super::plan::class_split::fixture::Receipts {
    let _frame = super::test_model_override::frame_lock();
    super::plan::class_split::fixture::run(src)
}

fn exclusion<'a>(receipts: &'a super::plan::class_split::fixture::Receipts, key: &str) -> &'a str {
    super::plan::class_split::fixture::column(&receipts.subjects, key, "exclusion")
}

/// **R586-2 witness (the shape).** The exported formal that is the sole origin
/// of the mutable scalar return is decided mutable: the function delivers
/// `&'a mut Node -> &'a mut Node`. RED without the rule: `first::node#1` is
/// held on the return seam (`dropped-site:seam-shared-to-mut`).
#[test]
fn r586_2_an_exported_sole_origin_formal_takes_the_return_mutability() {
    let out = fixture(R586_SHAPE);
    assert_eq!(exclusion(&out, "first::node#1"), "-", "{}", out.subjects);
    assert!(
        super::wave6a_allocation_tests::compact(out.tree())
            .contains("fnfirst<'a>(mutnode:&'amutNode)->&'amutNode{"),
        "{}",
        out.tree()
    );
}

/// **R586-2 control.** An in-program caller passing a shared argument into the
/// upgraded formal meets the existing call-site shared-to-mut gate (`peek` →
/// `first`, argument 0): the callee's signature class holds and the caller with
/// it, so nothing hands a shared reference to a `&mut` formal. Both functions
/// stay raw.
#[test]
fn r586_2_a_caller_holding_a_shared_argument_keeps_its_hold() {
    let out = fixture(&format!("{R586_SHAPE}{R586_CALLER}"));
    assert!(
        exclusion(&out, "first::node#1").contains("seam-shared-to-mut"),
        "{}",
        out.subjects
    );
    assert!(
        exclusion(&out, "peek::n#1").contains("dependency-class-held"),
        "{}",
        out.subjects
    );
    let tree = super::wave6a_allocation_tests::compact(out.tree());
    assert!(
        tree.contains("fnfirst(mutnode:*mutNode)->*mutNode{")
            && tree.contains("fnpeek(mutn:*mutNode)->i32{"),
        "{}",
        out.tree()
    );
}

/// **R586-2 witness (the sole-subject guard).** `pick` returns its origin `a`
/// but also reads a second pointer formal `b`, which C may pass aliased with `a`
/// (`pick(p, p)`): `a` stays shared and `pick` holds on the return seam, as
/// before the rule. The fault (the guard removed) upgrades `a` and delivers
/// `pick<'a>(a: &'a mut Node, b: &Node)`, a `&mut` beside a possibly aliased `&`.
#[test]
fn r586_2_a_second_pointer_subject_keeps_the_rule_out() {
    let out = fixture(R586_TWO_FORMALS);
    assert!(
        exclusion(&out, "pick::a#1").contains("seam-shared-to-mut"),
        "{}",
        out.subjects
    );
    assert!(
        super::wave6a_allocation_tests::compact(out.tree())
            .contains("fnpick(muta:*mutNode,mutb:*mutNode)->*mutNode{"),
        "{}",
        out.tree()
    );
}

/// The static-read residual's shape (R590-2): `first` reads another `Node`
/// through a static pointer while `node` lives. As `&mut`, `node` would assert
/// uniqueness over a pointee the static may alias; a foreign read pops it
/// (Stacked Borrows). The body is not closed, so the rule stays out.
const R590_STATIC_READ: &str = r#"
#[repr(C)]
pub struct Node {
    pub key: i32,
}
pub static mut ROOT: *mut Node = 0 as *mut Node;
#[no_mangle]
pub unsafe extern "C" fn first(mut node: *mut Node) -> *mut Node {
    let _k = (*ROOT).key + (*node).key;
    return node;
}
"#;

/// The same read one call away: a program callee that reads the static.
const R590_CALLEE_READ: &str = r#"
#[repr(C)]
pub struct Node {
    pub key: i32,
}
pub static mut ROOT: *mut Node = 0 as *mut Node;
pub unsafe fn root_key() -> i32 {
    return (*ROOT).key;
}
#[no_mangle]
pub unsafe extern "C" fn first(mut node: *mut Node) -> *mut Node {
    let _k = root_key() + (*node).key;
    return node;
}
"#;

/// **R590-2 witness (the closed body).** A static read during the formal's span
/// keeps the rule out: `first` stays raw, held on the return seam as before.
#[test]
fn r590_2_a_static_read_keeps_the_rule_out() {
    let out = fixture(R590_STATIC_READ);
    assert!(
        exclusion(&out, "first::node#1").contains("seam-shared-to-mut"),
        "{}",
        out.subjects
    );
    assert!(
        super::wave6a_allocation_tests::compact(out.tree())
            .contains("fnfirst(mutnode:*mutNode)->*mutNode{"),
        "{}",
        out.tree()
    );
}

/// **R590-2 witness (the closed body, one call away).** A call to a program
/// function keeps the rule out: the callee may reach the pointee through a
/// pointer the rule cannot see.
#[test]
fn r590_2_a_program_callee_keeps_the_rule_out() {
    let out = fixture(R590_CALLEE_READ);
    assert!(
        exclusion(&out, "first::node#1").contains("seam-shared-to-mut"),
        "{}",
        out.subjects
    );
    assert!(
        super::wave6a_allocation_tests::compact(out.tree())
            .contains("fnfirst(mutnode:*mutNode)->*mutNode{"),
        "{}",
        out.tree()
    );
}
