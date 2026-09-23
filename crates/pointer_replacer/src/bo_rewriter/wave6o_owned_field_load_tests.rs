//! **R538-3(i) (relay 081): the Option value edit defers to an applied OWNED
//! field transaction at a load it would otherwise render.**
//!
//! bst's `minValueNode` walks `node = (*node).left;` with `node` an optional
//! Ref local. The Option family rendered the right-hand side as a raw-field
//! adapter, `((*node.unwrap()).left as *const node).as_ref()`, while the owned
//! field transaction wraps the same load as `.as_deref()`: two renderings of one
//! node, the graft floor holds, and the transaction withdraws with its
//! dependent owners (wave-6f 064). Deferred, the base's own edit applies on
//! its own span and the load takes the transaction's wrap:
//! `(*node.unwrap()).left.as_deref()`.
use super::{A5Mode, RewriteOutcome, WholeProgramAttestation};

/// A reduction of the corpus bst: owned children built by `newNode` /
/// `insert`, and a walker whose local is decided an optional Ref.
const WALKER: &str = r#"
// wave6o-owned-field-walker
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(_: u64) -> *mut ::std::ffi::c_void;
    fn free(_: *mut ::std::ffi::c_void);
}
pub struct node {
    pub key: i32,
    pub left: *mut node,
    pub right: *mut node,
}
#[no_mangle]
pub unsafe extern "C" fn newNode(mut item: i32) -> *mut node {
    let mut temp = malloc(::std::mem::size_of::<node>() as u64) as *mut node;
    (*temp).key = item;
    (*temp).left = 0 as *mut node;
    (*temp).right = 0 as *mut node;
    return temp;
}
#[no_mangle]
pub unsafe extern "C" fn insert(mut node: *mut node, mut key: i32) -> *mut node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key {
        (*node).left = insert((*node).left, key);
    } else { (*node).right = insert((*node).right, key); }
    return node;
}
#[no_mangle]
pub unsafe extern "C" fn leftmostKey(mut node: *mut node) -> i32 {
    while !node.is_null() && !((*node).left).is_null() {
        node = (*node).left;
    }
    if node.is_null() { return -1; }
    return (*node).key;
}
"#;

/// era-5c's bst frame restricted to this reduction: both children Owning, the
/// builders Owning, the walker's local a Ref. `owned` = false leaves the fields
/// Raw — no field transaction exists, which is the control.
fn frame(owned: bool) {
    use crate::analyses::borrow_ownership::SlotKind;
    let field = if owned {
        SlotKind::Owning
    } else {
        SlotKind::Raw
    };
    super::test_model_override::set(
        "wave6o-owned-field-walker",
        vec![("node".to_owned(), 1, field), ("node".to_owned(), 2, field)],
        vec![
            ("insert::node".to_owned(), SlotKind::Owning),
            ("newNode::temp".to_owned(), SlotKind::Owning),
            ("leftmostKey::node".to_owned(), SlotKind::Ref),
        ],
    );
}

fn emitted(name: &str, source: &str) -> RewriteOutcome {
    let dir = std::env::temp_dir().join(format!("crat-wave6o-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, source).unwrap();
    let outcome = super::rewrite_m1_path_a5_injected(
        &root,
        A5Mode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        &|_| {},
    );
    std::fs::remove_dir_all(dir).unwrap();
    outcome
}

/// `(source, emitted, reverted)` under the frame; panics on a degraded program
/// with its reason (the base's outcome for the witness: the graft floor held
/// the transaction and every class was reverted).
fn walker(owned: bool) -> (String, usize, usize) {
    let _frame = super::test_model_override::frame_lock();
    frame(owned);
    let outcome = emitted(if owned { "owned-walker" } else { "raw-walker" }, WALKER);
    super::test_model_override::clear();
    match outcome {
        RewriteOutcome::Emitted {
            source,
            emitted_count,
            reverted_count,
            ..
        } => (source, emitted_count, reverted_count),
        RewriteOutcome::Degraded { reason, .. } => panic!("degraded: {reason}"),
    }
}

/// The witness. Owned children: the walker's traversal composes the base's
/// own edit with the transaction's wrap, the fields stay `Option<Box<node>>`,
/// and nothing is reverted. RED on the base: `recovery-degraded` — the two
/// renderings of `(*node).left` meet at one node, the graft floor holds the
/// field wrap, and the withdrawal takes every dependent class with it.
#[test]
fn wave6o_an_owned_field_load_defers_to_the_transaction() {
    let (source, emitted, reverted) = walker(true);
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    // **R541-2: a dichotomy on wave-6a's re-seat (`95f485540`), as wave-6f
    // restated theirs (R217-2).** `insert` consumes and returns its node; the
    // re-seat makes that formal an owner (`Option<Box<node>>`) and its class
    // delivers too. The walker's composition below is the same on both
    // frames; the branch is decided by `insert`'s formal, and each branch pins
    // its count with no revert.
    let reseated = flat.contains("fn insert(mut node: Option<Box<node>>, mut key: i32)");
    assert!(
        reseated || flat.contains("fn insert(mut node: *mut node, mut key: i32)"),
        "insert's formal is either raw or the re-seated owner:\n{source}"
    );
    assert_eq!(
        (emitted, reverted),
        (if reseated { 2 } else { 1 }, 0),
        "{source}"
    );
    for needle in [
        "pub left: Option<Box<node>>,",
        "pub right: Option<Box<node>>,",
        "pub unsafe extern \"C\" fn leftmostKey(mut node: Option<&node>) -> i32 {",
        "node = (*node.unwrap()).left.as_deref();",
    ] {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }
    assert!(!flat.contains("left as *const"), "{source}");
}

/// Control: with Raw children there is no field transaction, so the Option
/// value keeps its own raw-field adapter at the same node — the deferral is
/// keyed on an applied owned transaction, not on the shape of the load.
#[test]
fn wave6o_a_raw_field_load_keeps_the_option_adapter() {
    let (source, _, _) = walker(false);
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("pub left: *mut node,"), "{source}");
    assert!(
        flat.contains("node = ((*node.unwrap()).left as *const crate::node).as_ref();"),
        "{source}"
    );
}
