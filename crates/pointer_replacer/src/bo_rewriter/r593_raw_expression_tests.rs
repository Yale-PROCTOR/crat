//! **R593-2 — a raw-expression argument into a reverted callee's raw input.**
//!
//! When a callee's class reverts and its caller's does not, the caller renders
//! each argument in its current form into the callee's input form (`Raw`). A
//! `RawExpr` argument was refused unless it was `local_array.as_ptr()`
//! (`raw-expression-not-proven-stable`), and the refusal makes the caller an
//! owner of the input-reversion closure. brotli's five owners at batch 41 and
//! 42′ + 43 are this refusal (main 120). (a1): a raw expression over a root that
//! stays raw renders unchanged. (a2): a field read through a thin converted `ref`
//! whose field no transaction delivers reads the same raw pointer.

/// `first` holds on the return seam (its read-only formal decides shared under a
/// `*mut` return), so its class reverts and its callers' arguments must take its
/// raw input form.
const SHAPES: &str = r#"
#[repr(C)]
pub struct Node {
    pub key: i32,
    pub child: *mut Node,
}
#[no_mangle]
pub unsafe extern "C" fn first(mut node: *mut Node) -> *mut Node {
    let _k = (*node).key;
    return node;
}
pub unsafe fn caller(mut base: *mut Node, mut out: *mut i32) {
    let _b = (*base.offset(-1)).key;
    *out = 1;
    first(base.offset(1));
}
pub unsafe fn field_caller(mut s: *mut Node, mut out: *mut i32) {
    let _k = (*s).key;
    *out = 1;
    first((*s).child);
}
pub unsafe fn ctrl_caller(mut s: *mut Node, mut out: *mut i32) {
    let _k = (*s).key;
    *out = 1;
    first((*s).child.offset(0));
}
"#;

fn run() -> super::wave6a_allocation_tests::Emitted {
    let _frame = super::test_model_override::frame_lock();
    super::wave6a_allocation_tests::emitted("r593-raw-expression", SHAPES)
}

/// The final-reverts row of one function, if it reverted.
fn reverted<'a>(
    out: &'a super::wave6a_allocation_tests::Emitted,
    function: &str,
) -> Option<&'a str> {
    out.artifacts
        .final_reverts
        .lines()
        .find(|line| line.split('\t').nth(1) == Some(function))
}

/// **(a1) witness.** `caller` passes `base.offset(1)` with `base` degraded
/// (`slice-neg-or-unknown-offset`): the expression renders unchanged, so `caller`
/// is no owner and keeps `out: &mut i32`. RED before: `caller` is
/// `closure:partition` on `callee-parameter-input-raw-expression-not-proven-stable`.
#[test]
fn r593_a1_a_raw_rooted_expression_renders_unchanged() {
    let out = run();
    assert_eq!(
        reverted(&out, "caller"),
        None,
        "{}",
        out.artifacts.final_reverts
    );
    assert!(
        super::wave6a_allocation_tests::compact(&out.source)
            .contains("fncaller(mutbase:*mutNode,mutout:&muti32){"),
        "{}",
        out.source
    );
}

/// **(a1) control.** A raw expression over a CONVERTED root that is not a plain
/// field read (`(*s).child.offset(0)`, `s` a `ref`) keeps the refusal: `ctrl_caller`
/// stays an owner of the closure and reverts.
#[test]
fn r593_a1_a_converted_root_keeps_the_refusal() {
    let out = run();
    let row = reverted(&out, "ctrl_caller").unwrap_or_default();
    assert!(
        row.contains("callee-parameter-input-raw-expression-not-proven-stable"),
        "{}",
        out.artifacts.final_reverts
    );
}

/// **(a2) witness.** `field_caller` passes `(*s).child` with `s` a thin `ref`
/// and `child` delivered by no field transaction: the read is the same raw
/// pointer, so `field_caller` keeps `s` and `out`. RED before: the same
/// `not-proven-stable` owner row as `caller`.
#[test]
fn r593_a2_a_field_read_through_a_ref_reads_raw() {
    let out = run();
    assert_eq!(
        reverted(&out, "field_caller"),
        None,
        "{}",
        out.artifacts.final_reverts
    );
    assert!(
        super::wave6a_allocation_tests::compact(&out.source)
            .contains("fnfield_caller(muts:&Node,mutout:&muti32){"),
        "{}",
        out.source
    );
}

/// A field the field-reference transaction delivers (`Holder.node`, stored by
/// the c2rust `let ref mut fresh = (*h).node; *fresh = n;` idiom, wave-6f's H35
/// shape), read through a thin `ref` into the held `first`.
const DELIVERED_FIELD: &str = r#"
#[repr(C)]
pub struct Node {
    pub key: i32,
    pub child: *mut Node,
}
#[repr(C)]
pub struct Holder {
    pub fresh: i32,
    pub node: *mut Node,
}
#[no_mangle]
pub unsafe extern "C" fn first(mut node: *mut Node) -> *mut Node {
    let _k = (*node).key;
    return node;
}
pub unsafe extern "C" fn init_holder(mut h: *mut Holder, mut n: *mut Node) {
    let ref mut fresh1 = (*h).node;
    *fresh1 = n;
}
pub unsafe fn held_field_caller(mut h: *mut Holder, mut out: *mut i32) {
    let _k = (*h).fresh;
    *out = 1;
    first((*h).node);
}
"#;

/// **(a2) control.** The field read `(*h).node` goes through a thin `ref`, but
/// `Holder.node` is delivered by a field transaction (`applied`, `ref-shared`), so
/// its text no longer reads a raw pointer: `held_field_caller` keeps the refusal
/// and stays an owner.
#[test]
fn r593_a2_a_delivered_field_keeps_the_refusal() {
    let _frame = super::test_model_override::frame_lock();
    let out = super::wave6a_allocation_tests::emitted("r593-delivered-field", DELIVERED_FIELD);
    assert!(
        out.artifacts
            .field_transactions
            .lines()
            .any(|line| line.starts_with("Holder\tnode\tapplied\tref-shared\t")),
        "{}",
        out.artifacts.field_transactions
    );
    let row = reverted(&out, "held_field_caller").unwrap_or_default();
    assert!(
        row.contains("callee-parameter-input-raw-expression-not-proven-stable"),
        "{}",
        out.artifacts.final_reverts
    );
}
